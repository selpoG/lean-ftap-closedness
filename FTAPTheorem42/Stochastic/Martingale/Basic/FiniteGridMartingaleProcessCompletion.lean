/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcess
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Memin.SummableL2Limit
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Process.UniformLimits

/-!
# Completing finite-grid martingale integral processes

The predictable energy measure first completes the terminal finite-grid
integral in `L²`.  This module performs the corresponding process-level
completion.  Simple predictable approximants are integrated by the concrete
finite-grid martingale process.  A subsequence with summable terminal `L²`
steps has summable Doob envelopes, hence converges uniformly outside one null
set.  Its regularized limit is a right-continuous true martingale, constant
after the final grid time, with terminal value equal to the already completed
terminal operator.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ChronologicalGrid

/-- A terminal-`L²` Cauchy sequence of pathwise right-continuous
martingales, all stopped at the same deterministic horizon, has a
right-continuous martingale process limit with the Hilbert-space terminal
limit.  This is the analytic completion theorem used below for the concrete
finite-grid integrals. -/
theorem exists_rightContinuous_martingale_of_terminalLp_cauchy
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    (hUsual : Filtration.UsualConditions μ ℱ)
    (X : ℕ → Process Ω) (T : ℝ≥0)
    (hX : ∀ n, Martingale (X n) ℱ μ)
    (hXRight : ∀ n ω t,
      ContinuousWithinAt (X n · ω) (Set.Ici t) t)
    (hXConstant : ∀ n t, T ≤ t → X n t = X n T)
    (hTerminal : ∀ n, MemLp (X n T) (2 : ℝ≥0∞) μ)
    (hTerminalCauchy : CauchySeq (fun n =>
      (hTerminal n).toLp (X n T))) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      ∃ Y : Process Ω,
        Martingale Y ℱ μ ∧
          (∀ ω t, ContinuousWithinAt (Y · ω) (Set.Ici t) t) ∧
          (∀ t, T ≤ t → Y t =ᵐ[μ] Y T) ∧
          (∀ᵐ ω ∂μ, TendstoUniformly
            (fun n t => X (cutoff n) t ω) (fun t => Y t ω) atTop) ∧
          ∃ hYTerminal : MemLp (Y T) (2 : ℝ≥0∞) μ,
            hYTerminal.toLp (Y T) =
              limUnder atTop (fun n => (hTerminal n).toLp (X n T)) := by
  let F : ℕ → Lp ℝ (2 : ℝ≥0∞) μ := fun n =>
    (hTerminal n).toLp (X n T)
  obtain ⟨cutoff, hCutoff, hDistanceSummable⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq F hTerminalCauchy
  let Z : ℕ → Process Ω := fun n => X (cutoff n)
  let D : ℕ → Process Ω := fun n => Z (n + 1) - Z n
  let E : ℕ → Ω → ℝ := fun n =>
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope (D n) T
  have hD : ∀ n, Martingale (D n) ℱ μ := fun n =>
    (hX (cutoff (n + 1))).sub (hX (cutoff n))
  have hDRight : ∀ n ω t,
      ContinuousWithinAt (D n · ω) (Set.Ici t) t := by
    intro n ω t
    exact (hXRight (cutoff (n + 1)) ω t).sub
      (hXRight (cutoff n) ω t)
  have hDTerminal : ∀ n, MemLp (D n T) (2 : ℝ≥0∞) μ := fun n =>
    (hTerminal (cutoff (n + 1))).sub (hTerminal (cutoff n))
  have hEMemLp : ∀ n, MemLp (E n) (2 : ℝ≥0∞) μ := fun n =>
    FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      (hD n) T (hDTerminal n)
  have hTerminalDistance : ∀ n,
      eLpNorm (D n T) (2 : ℝ≥0∞) μ =
        ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) := by
    intro n
    calc
      eLpNorm (D n T) (2 : ℝ≥0∞) μ =
          edist (F (cutoff (n + 1))) (F (cutoff n)) := by
        dsimp only [D, Z, F]
        exact (Lp.edist_toLp_toLp
          (X (cutoff (n + 1)) T) (X (cutoff n) T)
          (hTerminal (cutoff (n + 1)))
          (hTerminal (cutoff n))).symm
      _ = ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) :=
        Lp.edist_dist _ _
  have hENorm : ∀ n,
      eLpNorm (E n) (2 : ℝ≥0∞) μ ≤
        2 * ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) := by
    intro n
    exact (FactorialChronologicalGrid.Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
        (hD n) T (hDTerminal n)).trans_eq
          (congrArg (fun x : ℝ≥0∞ => 2 * x) (hTerminalDistance n))
  have hETsum : (∑' n, eLpNorm (E n) (2 : ℝ≥0∞) μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)
        hDistanceSummable.tsum_ofReal_ne_top)
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hENorm
  have hESummable : ∀ᵐ ω ∂μ, Summable (fun n => ‖E n ω‖) :=
    summable_norm_of_tsum_eLpNorm_ne_top (p := (2 : ℝ≥0∞))
      (by norm_num) hETsum
  have hEDominates : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      dist (Z n t ω) (Z (n + 1) t ω) ≤ ‖E n ω‖ := by
    intro n
    have hUntil :=
      FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
          (hD n) T (hDTerminal n) (hDRight n)
    filter_upwards [hUntil] with ω hUntilω
    intro t
    by_cases ht : t ≤ T
    · calc
        dist (Z n t ω) (Z (n + 1) t ω) = ‖D n t ω‖ := by
          simp only [D, Z, Pi.sub_apply, Real.norm_eq_abs,
            Real.dist_eq, abs_sub_comm]
        _ ≤ E n ω := hUntilω t ht
        _ = ‖E n ω‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact Real.sqrt_nonneg _
    · have hTt : T ≤ t := le_of_not_ge ht
      change dist (X (cutoff n) t ω) (X (cutoff (n + 1)) t ω) ≤
        ‖E n ω‖
      rw [hXConstant (cutoff n) t hTt,
        hXConstant (cutoff (n + 1)) t hTt]
      calc
        dist (X (cutoff n) T ω) (X (cutoff (n + 1)) T ω) =
            ‖D n T ω‖ := by
          simp only [D, Z, Pi.sub_apply, Real.norm_eq_abs,
            Real.dist_eq, abs_sub_comm]
        _ ≤ E n ω := hUntilω T le_rfl
        _ = ‖E n ω‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact Real.sqrt_nonneg _
  have hEDominatesAll : ∀ᵐ ω ∂μ, ∀ n t,
      dist (Z n t ω) (Z (n + 1) t ω) ≤ ‖E n ω‖ := by
    rw [ae_all_iff]
    exact hEDominates
  let raw : Process Ω := fun t ω =>
    limUnder atTop (fun n => Z n t ω)
  have hRawLimit : ∀ᵐ ω ∂μ, ∀ t,
      Tendsto (fun n => Z n t ω) atTop (𝓝 (raw t ω)) := by
    filter_upwards [hESummable, hEDominatesAll] with ω hSum hDom
    intro t
    have hDistance : Summable (fun n =>
        dist (Z n t ω) (Z (n + 1) t ω)) :=
      Summable.of_nonneg_of_le (fun _ => dist_nonneg)
        (fun n => hDom n t) hSum
    exact (cauchySeq_of_summable_dist hDistance).tendsto_limUnder
  have hRawUniform : ∀ᵐ ω ∂μ,
      TendstoUniformly (fun n t => Z n t ω)
        (fun t => raw t ω) atTop := by
    filter_upwards [hESummable, hEDominatesAll, hRawLimit]
        with ω hSum hDom hLimit
    exact tendstoUniformly_of_eventually_dist_step_le_of_summable
      (fun n t => Z n t ω) (fun t => raw t ω)
      (fun n => ‖E n ω‖) hSum (fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall hDom) hLimit
  have hRawRight : ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (raw · ω) (Set.Ici t) t := by
    filter_upwards [hRawUniform] with ω hUniform
    exact rightContinuous_of_tendstoUniformly
      (fun n t => Z n t ω) (fun t => raw t ω) hUniform
      (fun n => hXRight (cutoff n) ω)
  have hRawAdapted : StronglyAdapted ℱ raw := by
    intro t
    change StronglyMeasurable[ℱ t]
      (fun ω => limUnder atTop (fun n => Z n t ω))
    exact @StronglyMeasurable.limUnder
      ℕ Ω ℝ (ℱ t) _ _ atTop _
      (fun n ω => Z n t ω) _ _
      (fun n => (hX (cutoff n)).stronglyMeasurable t)
  obtain ⟨B, hTerminalBound⟩ :=
    MeminL2.exists_eLpNorm_two_bound_of_cauchy
      (fun n => X n T) hTerminal hTerminalCauchy
  have hZBound : ∀ n t,
      eLpNorm (Z n t) (2 : ℝ≥0∞) μ ≤ B := by
    intro n t
    change eLpNorm (X (cutoff n) t) (2 : ℝ≥0∞) μ ≤ B
    by_cases ht : t ≤ T
    · exact (MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
          (hX (cutoff n)) ht (hTerminal (cutoff n))).2.trans
            (hTerminalBound (cutoff n))
    · rw [hXConstant (cutoff n) t (le_of_not_ge ht)]
      exact hTerminalBound (cutoff n)
  have hRawMartingale : Martingale raw ℱ μ :=
    Martingale.of_ae_tendsto_of_eLpNorm_two_le Z raw
      (fun n => hX (cutoff n)) hRawAdapted
      (fun t => hRawLimit.mono fun _ hω => hω t) B hZBound
  have hSelectedTerminalCauchy : CauchySeq (fun n =>
      (hTerminal (cutoff n)).toLp (X (cutoff n) T)) := by
    simpa only [F, Function.comp_def] using
      hTerminalCauchy.comp_tendsto hCutoff.tendsto_atTop
  have hSelectedTerminalLimit : ∀ᵐ ω ∂μ,
      Tendsto (fun n => X (cutoff n) T ω) atTop (𝓝 (raw T ω)) := by
    simpa only [Z] using hRawLimit.mono fun _ hω => hω T
  obtain ⟨hRawTerminal, hRawTerminalNorm⟩ :=
    MeminL2.memLp_two_of_cauchy_of_ae_tendsto
      (fun n => X (cutoff n) T)
      (fun n => hTerminal (cutoff n)) hSelectedTerminalCauchy
      (raw T) hSelectedTerminalLimit
  have hRawTerminalLp : Tendsto (fun n =>
      (hTerminal (cutoff n)).toLp (X (cutoff n) T)) atTop
      (𝓝 (hRawTerminal.toLp (raw T))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => X (cutoff n) T)
      (fun n => hTerminal (cutoff n)) (raw T) hRawTerminal).mpr
        hRawTerminalNorm
  have hHilbertTerminalLp : Tendsto (fun n =>
      (hTerminal (cutoff n)).toLp (X (cutoff n) T)) atTop
      (𝓝 (limUnder atTop (fun n => (hTerminal n).toLp (X n T)))) := by
    exact hTerminalCauchy.tendsto_limUnder.comp hCutoff.tendsto_atTop
  have hRawTerminalEq : hRawTerminal.toLp (raw T) =
      limUnder atTop (fun n => (hTerminal n).toLp (X n T)) :=
    tendsto_nhds_unique hRawTerminalLp hHilbertTerminalLp
  obtain ⟨Y, hYAdapted, hYRight, hYRaw⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_version
      hUsual hRawAdapted hRawRight
  have hYMartingale : Martingale Y ℱ μ :=
    hRawMartingale.congr hYAdapted
      (fun t => (hYRaw.eventuallyEq_at t).symm)
  have hYConstant : ∀ t, T ≤ t → Y t =ᵐ[μ] Y T := by
    intro t ht
    filter_upwards [hYRaw.eventuallyEq_at t,
      hYRaw.eventuallyEq_at T] with ω hYt hYT
    rw [hYt, hYT]
    simp only [raw]
    apply congrArg (limUnder atTop)
    funext n
    exact congrFun (hXConstant (cutoff n) t ht) ω
  have hYTerminal : MemLp (Y T) (2 : ℝ≥0∞) μ :=
    hRawTerminal.ae_eq (hYRaw.eventuallyEq_at T).symm
  have hYTerminalToLp : hYTerminal.toLp (Y T) =
      hRawTerminal.toLp (raw T) :=
    MemLp.toLp_congr hYTerminal hRawTerminal
      (hYRaw.eventuallyEq_at T)
  have hYUniform : ∀ᵐ ω ∂μ,
      TendstoUniformly (fun n t => X (cutoff n) t ω)
        (fun t => Y t ω) atTop := by
    filter_upwards [hRawUniform, hYRaw] with ω hUniform hEq
    have hPathEq : (fun t => Y t ω) = fun t => raw t ω := by
      funext t
      exact hEq t
    rw [hPathEq]
    simpa only [Z] using hUniform
  exact ⟨cutoff, hCutoff, Y, hYMartingale, hYRight, hYConstant,
    hYUniform, hYTerminal, hYTerminalToLp.trans hRawTerminalEq⟩

/-- If the approximating martingales also have left limits, the terminal
`L²` completion admits a version whose every path is right-continuous and
has left limits.  The same selected subsequence converges uniformly outside
one null set. -/
theorem exists_cadlag_martingale_of_terminalLp_cauchy
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    (hUsual : Filtration.UsualConditions μ ℱ)
    (X : ℕ → Process Ω) (T : ℝ≥0)
    (hX : ∀ n, Martingale (X n) ℱ μ)
    (hXRight : ∀ n ω t,
      ContinuousWithinAt (X n · ω) (Set.Ici t) t)
    (hXLeft : ∀ n, ProcessHasLeftLimits (X n))
    (hXConstant : ∀ n t, T ≤ t → X n t = X n T)
    (hTerminal : ∀ n, MemLp (X n T) (2 : ℝ≥0∞) μ)
    (hTerminalCauchy : CauchySeq (fun n =>
      (hTerminal n).toLp (X n T))) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      ∃ Y : Process Ω,
        Martingale Y ℱ μ ∧
          (∀ ω t, ContinuousWithinAt (Y · ω) (Set.Ici t) t) ∧
          ProcessHasLeftLimits Y ∧
          (∀ t, T ≤ t → Y t =ᵐ[μ] Y T) ∧
          (∀ᵐ ω ∂μ, TendstoUniformly
            (fun n t => X (cutoff n) t ω) (fun t => Y t ω) atTop) ∧
          ∃ hYTerminal : MemLp (Y T) (2 : ℝ≥0∞) μ,
            hYTerminal.toLp (Y T) =
              limUnder atTop (fun n => (hTerminal n).toLp (X n T)) := by
  obtain ⟨cutoff, hCutoff, Y, hYMartingale, hYRight,
      hYConstant, hYUniform, hYTerminal, hYTerminalEq⟩ :=
    exists_rightContinuous_martingale_of_terminalLp_cauchy
      hUsual X T hX hXRight hXConstant hTerminal hTerminalCauchy
  have hYRegular : ∀ᵐ ω ∂μ,
      (∀ t, ContinuousWithinAt (Y · ω) (Set.Ici t) t) ∧
        ∀ t, Tendsto (fun s => Y s ω) (𝓝[<] t)
          (𝓝 (Function.leftLim (fun s => Y s ω) t)) := by
    filter_upwards [hYUniform] with ω hUniform
    refine ⟨hYRight ω, ?_⟩
    exact leftLimits_of_tendstoUniformly
      (fun n t => X (cutoff n) t ω) (fun t => Y t ω)
      hUniform (fun n => hXLeft (cutoff n) ω)
  obtain ⟨Y', hY'Adapted, hY'Right, hY'Left, hY'Y⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
        hUsual hYMartingale.stronglyAdapted hYRegular
  have hY'Martingale : Martingale Y' ℱ μ :=
    hYMartingale.congr hY'Adapted
      (fun t => (hY'Y.eventuallyEq_at t).symm)
  have hY'Constant : ∀ t, T ≤ t → Y' t =ᵐ[μ] Y' T := by
    intro t ht
    filter_upwards [hY'Y.eventuallyEq_at t,
      hY'Y.eventuallyEq_at T, hYConstant t ht] with ω hY't hY'T hYT
    exact hY't.trans (hYT.trans hY'T.symm)
  have hY'Uniform : ∀ᵐ ω ∂μ,
      TendstoUniformly (fun n t => X (cutoff n) t ω)
        (fun t => Y' t ω) atTop := by
    filter_upwards [hYUniform, hY'Y] with ω hUniform hEq
    have hPathEq : (fun t => Y' t ω) = fun t => Y t ω := by
      funext t
      exact hEq t
    rw [hPathEq]
    exact hUniform
  have hY'Terminal : MemLp (Y' T) (2 : ℝ≥0∞) μ :=
    hYTerminal.ae_eq (hY'Y.eventuallyEq_at T).symm
  have hY'TerminalEq : hY'Terminal.toLp (Y' T) =
      hYTerminal.toLp (Y T) :=
    MemLp.toLp_congr hY'Terminal hYTerminal
      (hY'Y.eventuallyEq_at T)
  exact ⟨cutoff, hCutoff, Y', hY'Martingale, hY'Right, hY'Left,
    hY'Constant, hY'Uniform, hY'Terminal,
    hY'TerminalEq.trans hYTerminalEq⟩

end ChronologicalGrid

end FTAPTheorem42
