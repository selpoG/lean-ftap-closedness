/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessFastSubsequence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Adapted local uniform limits of elementary-test Cauchy subsequences -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The fast subsequence has an adapted limit on one common full-measure
set, uniformly on every finite time interval. No limit is an input. -/
theorem ElementaryEmeryCauchy.exists_adapted_locallyUniform_limit
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0) :
    ∃ (f : Nat → Nat) (Y : Process Ω), StrictMono f ∧ StronglyAdapted F Y ∧
      ∀ᵐ w ∂μ, ∀ T : NNReal,
        TendstoUniformlyOn (fun k t => X (f k) t w) (Y · w) atTop (Iic T) := by
  obtain ⟨f, hf, hFast⟩ := h.exists_fast_subsequence hX hXR hInitial
  let Y : Process Ω := fun t w => limUnder atTop (fun k => X (f k) t w)
  refine ⟨f, Y, hf, ?_, ?_⟩
  · intro t
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun k => (hX (f k)).stronglyAdapted t)
  · filter_upwards [hFast] with w hw
    have hC (T : NNReal) : UniformCauchySeqOn
        (fun k t => X (f k) t w) atTop (Iic T) := by
      apply uniformCauchySeqOn_of_eventually_dist_step_le_of_summable
        _ _ (fun k => ((1 : Real) / 2) ^ (k + 1))
      · simpa [pow_succ, mul_comm] using
          (summable_geometric_two.mul_left ((1 : Real) / 2))
      · intro k
        positivity
      · filter_upwards [hw, eventually_ge_atTop (Nat.ceil T)] with k hk hTk
        intro t ht
        have hT : T ≤ ((k + 1 : Nat) : NNReal) :=
          (Nat.le_ceil T).trans (by exact_mod_cast hTk.trans (Nat.le_succ k))
        simpa only [Real.dist_eq, abs_sub_comm] using hk t (ht.trans hT)
    intro T
    exact (hC T).tendstoUniformlyOn_of_tendsto fun t ht =>
      ((hC T).cauchySeq ht).tendsto_limUnder

/-- Under the usual conditions, regularize the constructed adapted limit
on one time-zero null set while preserving local uniform convergence. -/
theorem ElementaryEmeryCauchy.exists_cadlag_locallyUniform_limit
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hUsual : Filtration.UsualConditions μ F)
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hXL : ∀ n, ProcessHasLeftLimits (X n))
    (hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0) :
    ∃ (f : Nat → Nat) (Y : Process Ω), StrictMono f ∧ StronglyAdapted F Y ∧
      (∀ w t, ContinuousWithinAt (Y · w) (Ici t) t) ∧ ProcessHasLeftLimits Y ∧
      Y 0 =ᵐ[μ] X 0 0 ∧
      ∀ᵐ w ∂μ, ∀ T : NNReal,
        TendstoUniformlyOn (fun k t => X (f k) t w) (Y · w) atTop (Iic T) := by
  obtain ⟨f, Z, hf, hZ, hU⟩ := h.exists_adapted_locallyUniform_limit hX hXR hInitial
  have hReg : ∀ᵐ w ∂μ, (∀ t, ContinuousWithinAt (Z · w) (Ici t) t) ∧
      ∀ t, Tendsto (Z · w) (𝓝[<] t) (𝓝 (Function.leftLim (Z · w) t)) := by
    filter_upwards [hU] with w hw
    exact cadlag_of_locallyUniform_limit (fun n t => X (f n) t w) (Z · w) hw
      (fun n => hXR (f n) w) (fun n => hXL (f n) w)
  obtain ⟨Y, hY, hYR, hYL, hYZ⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hZ hReg
  have hUY : ∀ᵐ w ∂μ, ∀ T : NNReal,
      TendstoUniformlyOn (fun k t => X (f k) t w) (Y · w) atTop (Iic T) := by
    filter_upwards [hU, hYZ] with w hw heq
    simpa only [show (Y · w) = (Z · w) from funext heq] using hw
  refine ⟨f, Y, hf, hY, hYR, hYL, ?_, hUY⟩
  have h0 : ∀ᵐ w ∂μ, ∀ n, X n 0 w = X 0 0 w := ae_all_iff.mpr hInitial
  filter_upwards [hUY, h0] with w hw h0w
  have hLim := (hw 0).tendsto_at (show (0 : NNReal) ∈ Iic (0 : NNReal) by simp)
  have hConst : Tendsto (fun k => X (f k) 0 w) atTop (𝓝 (X 0 0 w)) := by
    simpa only [h0w] using (tendsto_const_nhds : Tendsto
      (fun _ : Nat => X 0 0 w) atTop (𝓝 (X 0 0 w)))
  exact tendsto_nhds_unique hLim hConst

/-- Independent construction of a regular elementary-test limit. The
original sequence converges uniformly over the test class; neither a
good-integrator assumption nor fixed-source integral closedness is used. -/
theorem ElementaryEmeryCauchy.exists_cadlag_limit
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hUsual : Filtration.UsualConditions μ F)
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hXL : ∀ n, ProcessHasLeftLimits (X n))
    (hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0) :
    ∃ Y : Process Ω, IsStronglyProgressive F Y ∧
      (∀ w t, ContinuousWithinAt (Y · w) (Ici t) t) ∧ ProcessHasLeftLimits Y ∧
      Y 0 =ᵐ[μ] X 0 0 ∧ ElementaryEmeryConverges μ F X Y ∧
      ∀ T : NNReal, TendstoInMeasure μ
        (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t w => X n t w - Y t w) T) atTop (fun _ => (0 : Real)) := by
  obtain ⟨f, Y, hf, hY, hYR, hYL, hY0, hU⟩ :=
    h.exists_cadlag_locallyUniform_limit hUsual hX hXR hXL hInitial
  have hYP := StronglyAdapted.isStronglyProgressive_of_rightContinuous hY hYR
  have hSub : ∀ T : NNReal, TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X (f n) t w - Y t w) T) atTop (fun _ => (0 : Real)) := by
    intro T
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
        ((hX (f n)).stronglyAdapted.sub hY) T).mono (F.le T) |>.aestronglyMeasurable
    · filter_upwards [hU] with w hw
      open FactorialChronologicalGrid in
      exact cappedFiniteHorizonAbsoluteEnvelope_tendsto_zero_of_tendstoUniformlyOn
        (fun n => X (f n)) Y T w (hw T)
  have hConv := h.converges_of_subsequence_ucp hX hYP hXR hYR f hf.tendsto_atTop hSub
  exact ⟨Y, hYP, hYR, hYL, hY0, hConv,
    hConv.ucp hX hYP (fun n => (hInitial n).trans hY0.symm)⟩

/-! ## Good-integrator stability under uniform elementary-test convergence -/

omit [MeasurableSpace Ω] in
private theorem capped_value_le_envelope (X : Process Ω) (T : NNReal)
    (hR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t) (w : Ω) :
    min |X T w| 1 ≤ FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T w := by
  have h := FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
    (fun t w => |X t w|) T (fun w t => (hR w t).abs) w le_rfl
  have hCap := ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by finiteness) (min_le_right
      (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope (fun t w => |X t w|) T w) 1))
    (min_le_min h (le_rfl : (1 : ENNReal) ≤ 1))
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_min,
    ENNReal.toReal_ofReal (le_min (abs_nonneg _) zero_le_one)] at hCap
  simpa only [ENNReal.ofReal_one,
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope] using hCap

/-- For each probability tolerance, fix one approximating good integrator
before sending the small elementary integrand to zero. Uniformity over tests
controls the error without any bound on their lengths or coefficient sums. -/
theorem ElementaryEmeryConverges.isSemimartingale
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hGI : ∀ n, IsSemimartingale (X n) F μ) : IsSemimartingale Y F μ := by
  refine ⟨fun J T => ((PredictableElementaryStrategy.stronglyAdapted_gain Y hY J T).mono
    (F.le T)).aestronglyMeasurable, ?_⟩
  intro J hJ T
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le (measureReal_nonneg)
  · intro δ hδ
    let a : Real := min (ε / 2) 1
    have ha : 0 < a := lt_min (half_pos hε) zero_lt_one
    obtain ⟨m, hm⟩ := (h T (a * (δ / 4)) (mul_pos ha (by positivity))).exists
    have hFixed := (tendstoInMeasure_iff_measureReal_norm.mp ((hGI m).2 J hJ T))
      (ε / 2) (half_pos hε)
    simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hFixed
    filter_upwards [hJ 1 zero_lt_one, hFixed.eventually (Iio_mem_nhds (half_pos hδ))]
      with k hk hSmall
    let B : BoundedPredictableElementaryMultiplier (Ω := Ω) F := ⟨J k, hk⟩
    let E : Ω → Real := elementaryEmeryTestError (X m) Y B T
    have hEi : Integrable E μ := elementaryEmeryTestError_integrable (hX m) hY B T
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun w => (elementaryEmeryTestError_bounds (X m) Y B T w).1) hEi a
    have hError : μ.real {w | a ≤ E w} ≤ δ / 4 :=
      (mul_le_mul_iff_right₀ ha).mp (hMarkov.trans (hm B))
    have hSubset : {w | ε ≤ |ElementaryStrategy.gain Y (J k).toElementary T w|} ⊆
        {w | ε / 2 ≤ |ElementaryStrategy.gain (X m) (J k).toElementary T w|} ∪
          {w | a ≤ E w} := by
      intro w hw
      change ε ≤ |ElementaryStrategy.gain Y (J k).toElementary T w| at hw
      by_contra hn
      have hNot := not_or.mp hn
      have hBase : |ElementaryStrategy.gain (X m) (J k).toElementary T w| < ε / 2 :=
        lt_of_not_ge hNot.1
      have hErr : E w < a := lt_of_not_ge hNot.2
      have hCap : min |ElementaryStrategy.gain (X m) (J k).toElementary T w -
          ElementaryStrategy.gain Y (J k).toElementary T w| 1 ≤ E w :=
        capped_value_le_envelope _ T
          (fun w t => (PredictableElementaryStrategy.rightContinuous_gain _ (hXR m) (J k) w t).sub
            (PredictableElementaryStrategy.rightContinuous_gain _ hYR (J k) w t)) w
      have hDiff : |ElementaryStrategy.gain (X m) (J k).toElementary T w -
          ElementaryStrategy.gain Y (J k).toElementary T w| < ε / 2 := by
        by_contra hd
        exact (not_lt_of_ge ((min_le_min (le_of_not_gt hd) le_rfl).trans hCap)) hErr
      have hTri := abs_add_le
        (ElementaryStrategy.gain (X m) (J k).toElementary T w)
        (ElementaryStrategy.gain Y (J k).toElementary T w -
          ElementaryStrategy.gain (X m) (J k).toElementary T w)
      rw [add_sub_cancel, abs_sub_comm] at hTri
      linarith
    have hBound := (measureReal_mono (μ := μ) hSubset).trans (measureReal_union_le _ _)
    exact hBound.trans_lt (by linarith)

end FTAPTheorem42
