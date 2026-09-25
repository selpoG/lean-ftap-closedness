/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Foundations.Envelope
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.DS.Lemma49.StoppedTailMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Foundations.CadlagEnvelope
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Maximal passage-prefix approximation for Lemma 4.11

The real factorial envelope uses `ENNReal.toReal`; consequently it sends an
infinite extended envelope to zero.  This file introduces a capped measurable
gauge which still detects that case.  The gauge supports a three-error
approximation argument combining an actual passage prefix, the full process,
and the post-passage tail.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FactorialChronologicalGrid

omit [MeasurableSpace Ω] in
/-- Every sampled value is bounded by its extended factorial envelope. -/
theorem ofReal_natSample_le_eFactorialRunningMaxEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (r k : ℕ)
    (hk : k ≤ r * r.factorial) (ω : Ω) :
    ENNReal.ofReal
        (f ((stoppedGrid T r).sampledTime k) ω) ≤
      eFactorialRunningMaxEnvelope f T ω := by
  calc
    ENNReal.ofReal (f ((stoppedGrid T r).sampledTime k) ω) ≤
        ENNReal.ofReal
          (factorialRunningMax f T r ω) := by
      apply ENNReal.ofReal_le_ofReal
      exact Finset.le_sup' (fun j =>
        (stoppedGrid T r).natSample f j ω)
        (Finset.mem_range.2 (Nat.lt_succ_iff.2 hk))
    _ ≤ eFactorialRunningMaxEnvelope f T ω :=
      le_iSup (fun q => ENNReal.ofReal
        (factorialRunningMax f T q ω)) r

omit [MeasurableSpace Ω] in
/-- A pointwise compact-horizon bound controls the extended factorial
envelope. -/
theorem eFactorialRunningMaxEnvelope_abs_le_of_bound
    (X : Process Ω) (T : ℝ≥0) {G : ℝ} {ω : Ω}
    (hbound : ∀ t, t ≤ T → |X t ω| ≤ G) :
    eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω ≤
      ENNReal.ofReal G := by
  apply iSup_le
  intro r
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (r * r.factorial + 1))
    Finset.nonempty_range_add_one
    (fun j => (stoppedGrid T r).natSample
      (fun t ω => |X t ω|) j ω)
  rw [show factorialRunningMax (fun t ω => |X t ω|) T r ω =
      (stoppedGrid T r).natSample
        (fun t ω => |X t ω|) k ω by exact hkEq]
  apply hbound
  simp only [ChronologicalGrid.sampledTime, stoppedGrid_time]
  exact min_le_right _ _

omit [MeasurableSpace Ω] in
/-- If the squared factorial envelope is finite, every finite-grid maximum
is bounded by the real square-root envelope. -/
theorem factorialRunningMax_abs_le_finiteHorizonAbsoluteEnvelope_of_ne_top
    (X : Process Ω) (T : ℝ≥0) (ω : Ω)
    (hFinite : eFactorialRunningMaxSqEnvelope
      (fun t ω => |X t ω|) T ω ≠ ∞) (r : ℕ) :
    factorialRunningMax (fun t ω => |X t ω|) T r ω ≤
      finiteHorizonAbsoluteEnvelope X T ω := by
  apply Real.le_sqrt_of_sq_le
  have hENN : ENNReal.ofReal
      ((factorialRunningMax (fun t ω => |X t ω|) T r ω) ^ 2) ≤
      eFactorialRunningMaxSqEnvelope
        (fun t ω => |X t ω|) T ω :=
    le_iSup (fun q => ENNReal.ofReal
      ((factorialRunningMax (fun t ω => |X t ω|) T q ω) ^ 2)) r
  have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    hFinite).2 hENN
  simpa only [finiteHorizonAbsoluteEnvelope,
    ENNReal.toReal_ofReal (sq_nonneg _)] using hReal

omit [MeasurableSpace Ω] in
/-- On the finite-envelope event, the capped extended envelope is bounded by
the ordinary real factorial envelope. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_le_of_sq_ne_top
    (X : Process Ω) (T : ℝ≥0) (ω : Ω)
    (hFinite : eFactorialRunningMaxSqEnvelope
      (fun t ω => |X t ω|) T ω ≠ ∞) :
    cappedFiniteHorizonAbsoluteEnvelope X T ω ≤
      finiteHorizonAbsoluteEnvelope X T ω := by
  let E := eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω
  have hELe : E ≤ ENNReal.ofReal
      (finiteHorizonAbsoluteEnvelope X T ω) := by
    apply iSup_le
    intro r
    exact ENNReal.ofReal_le_ofReal
      (factorialRunningMax_abs_le_finiteHorizonAbsoluteEnvelope_of_ne_top
        X T ω hFinite r)
  have hENeTop : E ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hELe
  have hMinLe : min E 1 ≤ E := min_le_left _ _
  unfold cappedFiniteHorizonAbsoluteEnvelope
  calc
    (min E 1).toReal ≤ E.toReal :=
      ENNReal.toReal_mono hENeTop hMinLe
    _ ≤ (ENNReal.ofReal
        (finiteHorizonAbsoluteEnvelope X T ω)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hELe
    _ = finiteHorizonAbsoluteEnvelope X T ω := by
      rw [ENNReal.toReal_ofReal]
      exact Real.sqrt_nonneg _

omit [MeasurableSpace Ω] in
/-- Below level one, a strict capped-gauge bound is a strict bound for the
underlying extended envelope. -/
theorem eFactorialRunningMaxEnvelope_abs_lt_of_capped_lt
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hCapped : cappedFiniteHorizonAbsoluteEnvelope X T ω < a) :
    eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω <
      ENNReal.ofReal a := by
  let E := eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω
  have hMinNeTop : min E 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hMinLt : min E 1 < ENNReal.ofReal a := by
    apply (ENNReal.toReal_lt_toReal hMinNeTop ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal ha0, E,
      cappedFiniteHorizonAbsoluteEnvelope] using hCapped
  rcases min_lt_iff.mp hMinLt with hE | hOne
  · exact hE
  · have hOfReal : ENNReal.ofReal a < 1 := by
      simpa only [← ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).mpr ha1
    exact (hOne.trans hOfReal).false.elim

omit [MeasurableSpace Ω] in
/-- A capped-gauge bound below one bounds the ordinary real square-root
envelope as well. -/
theorem finiteHorizonAbsoluteEnvelope_le_of_capped_le
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hCapped : cappedFiniteHorizonAbsoluteEnvelope X T ω ≤ a) :
    finiteHorizonAbsoluteEnvelope X T ω ≤ a := by
  let E := eFactorialRunningMaxEnvelope (fun t ω => |X t ω|) T ω
  have hMinNeTop : min E 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hMinLe : min E 1 ≤ ENNReal.ofReal a := by
    apply (ENNReal.toReal_le_toReal hMinNeTop ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal ha0, E,
      cappedFiniteHorizonAbsoluteEnvelope] using hCapped
  have hOfRealLtOne : ENNReal.ofReal a < 1 := by
    simpa only [← ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).mpr ha1
  have hELe : E ≤ ENNReal.ofReal a := by
    by_contra hNot
    have haE : ENNReal.ofReal a < E := lt_of_not_ge hNot
    have hLower : ENNReal.ofReal a < min E 1 := by
      rw [lt_min_iff]
      exact ⟨haE, hOfRealLtOne⟩
    exact (not_lt_of_ge hMinLe) hLower
  have hGridBound : ∀ r,
      factorialRunningMax (fun t ω => |X t ω|) T r ω ≤ a := by
    intro r
    have hOfReal : ENNReal.ofReal
        (factorialRunningMax (fun t ω => |X t ω|) T r ω) ≤
        ENNReal.ofReal a :=
      (le_iSup (fun q => ENNReal.ofReal
        (factorialRunningMax (fun t ω => |X t ω|) T q ω)) r).trans hELe
    exact (ENNReal.ofReal_le_ofReal_iff ha0).mp hOfReal
  have hSq : eFactorialRunningMaxSqEnvelope
      (fun t ω => |X t ω|) T ω ≤ ENNReal.ofReal (a ^ 2) := by
    apply iSup_le
    intro r
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀
      (finiteRunningMax_nonneg _ _
        ((stoppedGrid T r).natSample_nonneg
          (fun _ _ => abs_nonneg _)) ω) ha0).2 (hGridBound r)
  have hSqFinite : eFactorialRunningMaxSqEnvelope
      (fun t ω => |X t ω|) T ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSq
  have hReal := (ENNReal.toReal_le_toReal hSqFinite
    ENNReal.ofReal_ne_top).2 hSq
  apply Real.sqrt_le_iff.mpr
  exact ⟨ha0, by
    simpa only [finiteHorizonAbsoluteEnvelope,
      ENNReal.toReal_ofReal (sq_nonneg a)] using hReal⟩

omit [MeasurableSpace Ω] in
/-- Three nonnegative pointwise summands give a three-term extended-envelope
bound. -/
theorem eFactorialRunningMaxEnvelope_le_add_three_of_pointwise
    (f g h k : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hg : 0 ≤ g) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hpoint : ∀ t, f t ω ≤ g t ω + h t ω + k t ω) :
    eFactorialRunningMaxEnvelope f T ω ≤
      eFactorialRunningMaxEnvelope g T ω +
        eFactorialRunningMaxEnvelope h T ω +
          eFactorialRunningMaxEnvelope k T ω := by
  apply iSup_le
  intro r
  obtain ⟨j, hj, hjEq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (r * r.factorial + 1))
    Finset.nonempty_range_add_one
    (fun i => (stoppedGrid T r).natSample f i ω)
  have hjN : j ≤ r * r.factorial :=
    Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  rw [show factorialRunningMax f T r ω =
      (stoppedGrid T r).natSample f j ω by exact hjEq]
  calc
    ENNReal.ofReal ((stoppedGrid T r).natSample f j ω) ≤
        ENNReal.ofReal
          ((stoppedGrid T r).natSample g j ω +
            (stoppedGrid T r).natSample h j ω +
              (stoppedGrid T r).natSample k j ω) :=
      ENNReal.ofReal_le_ofReal
        (hpoint ((stoppedGrid T r).sampledTime j))
    _ = ENNReal.ofReal ((stoppedGrid T r).natSample g j ω) +
          ENNReal.ofReal ((stoppedGrid T r).natSample h j ω) +
            ENNReal.ofReal ((stoppedGrid T r).natSample k j ω) := by
      simp only [ChronologicalGrid.natSample]
      rw [ENNReal.ofReal_add (add_nonneg (hg _ _) (hh _ _)) (hk _ _),
        ENNReal.ofReal_add (hg _ _) (hh _ _)]
    _ ≤ eFactorialRunningMaxEnvelope g T ω +
          eFactorialRunningMaxEnvelope h T ω +
            eFactorialRunningMaxEnvelope k T ω := by
      gcongr
      · exact ofReal_natSample_le_eFactorialRunningMaxEnvelope
          g T r j hjN ω
      · exact ofReal_natSample_le_eFactorialRunningMaxEnvelope
          h T r j hjN ω
      · exact ofReal_natSample_le_eFactorialRunningMaxEnvelope
          k T r j hjN ω

omit [MeasurableSpace Ω] in
/-- Uniform pathwise convergence makes the capped factorial envelopes of the
errors converge to zero at each sample point. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_tendsto_zero_of_tendstoUniformlyOn
    (X : ℕ → Process Ω) (Y : Process Ω) (T : ℝ≥0) (ω : Ω)
    (hUniform : TendstoUniformlyOn
      (fun n t => X n t ω) (fun t => Y t ω) atTop (Set.Iic T)) :
    Tendsto (fun n => cappedFiniteHorizonAbsoluteEnvelope
      (fun t ω => X n t ω - Y t ω) T ω) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.mp hUniform) (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  have hBound : ∀ t, t ≤ T → |X n t ω - Y t ω| ≤ ε / 2 := by
    intro t htT
    have ht := hN n hn t htT
    rw [Real.dist_eq, abs_sub_comm] at ht
    exact ht.le
  have hExtended := eFactorialRunningMaxEnvelope_abs_le_of_bound
    (fun t ω => X n t ω - Y t ω) T hBound
  have hMinLe : min
      (eFactorialRunningMaxEnvelope
        (fun t ω => |X n t ω - Y t ω|) T ω) 1 ≤
      ENNReal.ofReal (ε / 2) :=
    (min_le_left _ _).trans hExtended
  have hCappedLe : cappedFiniteHorizonAbsoluteEnvelope
      (fun t ω => X n t ω - Y t ω) T ω ≤ ε / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hMinLe
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (cappedFiniteHorizonAbsoluteEnvelope_nonneg
      (fun t ω => X n t ω - Y t ω) T ω)]
  exact hCappedLe.trans_lt (half_lt_self hε)

omit [MeasurableSpace Ω] in
/-- Global uniform convergence is a special case of convergence on the
finite horizon used by the envelope. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_tendsto_zero_of_tendstoUniformly
    (X : ℕ → Process Ω) (Y : Process Ω) (T : ℝ≥0) (ω : Ω)
    (hUniform : TendstoUniformly
      (fun n t => X n t ω) (fun t => Y t ω) atTop) :
    Tendsto (fun n => cappedFiniteHorizonAbsoluteEnvelope
      (fun t ω => X n t ω - Y t ω) T ω) atTop (𝓝 0) :=
  cappedFiniteHorizonAbsoluteEnvelope_tendsto_zero_of_tendstoUniformlyOn
    X Y T ω hUniform.tendstoUniformlyOn

/-- Almost-everywhere uniform convergence of adapted processes implies
convergence in measure of the capped compact-horizon factorial envelopes. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_uniformAE
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Process Ω} {Y : Process Ω}
    (hX : ∀ n, StronglyAdapted ℱ (X n)) (hY : StronglyAdapted ℱ Y)
    (hUniform : ∀ᵐ ω ∂μ, TendstoUniformly
      (fun n t => X n t ω) (fun t => Y t ω) atTop)
    (T : ℝ≥0) :
    TendstoInMeasure μ
      (fun n => cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X n t ω - Y t ω) T)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hDifference : StronglyAdapted ℱ
        (fun t ω => X n t ω - Y t ω) := by
      intro t
      exact (hX n t).sub (hY t)
    exact (stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      hDifference T).mono (ℱ.le T) |>.aestronglyMeasurable
  · filter_upwards [hUniform] with ω hω
    exact cappedFiniteHorizonAbsoluteEnvelope_tendsto_zero_of_tendstoUniformly
      X Y T ω hω

/-- Convergence in measure of the capped extended gauge implies convergence
in measure of the ordinary real factorial envelope. -/
theorem finiteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_capped
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Process Ω} (T : ℝ≥0)
    (hCapped : TendstoInMeasure μ
      (fun n => cappedFiniteHorizonAbsoluteEnvelope (X n) T)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n => finiteHorizonAbsoluteEnvelope (X n) T)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hCapped ⊢
  intro ε hε
  let a : ℝ := min (ε / 2) (1 / 2)
  have ha0 : 0 < a := lt_min (half_pos hε) (by norm_num)
  have ha1 : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have haε : a < ε :=
    (min_le_left _ _).trans_lt (half_lt_self hε)
  have hUpper := hCapped a ha0
  apply squeeze_zero'
      (f := fun n => μ.real {ω | ε ≤ dist
        (finiteHorizonAbsoluteEnvelope (X n) T ω) 0})
      (g := fun n => μ.real {ω | a ≤ dist
        (cappedFiniteHorizonAbsoluteEnvelope (X n) T ω) 0})
  · exact Filter.Eventually.of_forall fun _ => measureReal_nonneg
  · exact Filter.Eventually.of_forall fun n => by
      have hSubset : {ω | ε ≤ dist
          (finiteHorizonAbsoluteEnvelope (X n) T ω) 0} ⊆
          {ω | a ≤ dist
            (cappedFiniteHorizonAbsoluteEnvelope (X n) T ω) 0} := by
        intro ω hω
        change ε ≤ dist
          (finiteHorizonAbsoluteEnvelope (X n) T ω) 0 at hω
        change a ≤ dist
          (cappedFiniteHorizonAbsoluteEnvelope (X n) T ω) 0
        simp only [Real.dist_eq, sub_zero] at hω ⊢
        have hEnvelopeNonnegative : 0 ≤
            finiteHorizonAbsoluteEnvelope (X n) T ω := by
          unfold finiteHorizonAbsoluteEnvelope
          exact Real.sqrt_nonneg _
        rw [abs_of_nonneg hEnvelopeNonnegative] at hω
        rw [abs_of_nonneg
          (cappedFiniteHorizonAbsoluteEnvelope_nonneg (X n) T ω)]
        apply le_of_not_gt
        intro hNot
        have hEnvelopeLe := finiteHorizonAbsoluteEnvelope_le_of_capped_le
          (X n) T ω ha0.le ha1 hNot.le
        linarith
      exact ENNReal.toReal_mono (by finiteness) (measure_mono hSubset)
  · exact hUpper

end FactorialChronologicalGrid

end FTAPTheorem42
