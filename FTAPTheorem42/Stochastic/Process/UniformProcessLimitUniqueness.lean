/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma411.MaximalApproximation
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import FTAPTheorem42.Foundations.ProcessIndistinguishable

/-!
# Uniqueness of compact-uniform process limits

If two right-continuous processes are compact-uniform limits in probability
of the same process sequence, then they are indistinguishable.  The compact
uniform gauge is the measurable capped factorial-grid envelope, so the result
does not require measurability of an uncountable path supremum.

This is the uniqueness bridge needed after a Mémín graph-closure theorem:
Emery convergence supplies compact-uniform convergence in probability, while
the component construction supplies the canonical candidate limit.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ProcessIndistinguishable

/-- Two right-continuous processes which are pointwise limits in measure of
the same process sequence on one countable right-dense skeleton are
indistinguishable. -/
theorem of_common_tendstoInMeasure_on_rightDense
    {μ : Measure Ω} (Z : ℕ → Process Ω) (X Y : Process Ω)
    (skeleton : ℕ → ℝ≥0)
    (hRightDense : ∀ t,
      t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hYRight : ∀ ω t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    (hZX : ∀ k, TendstoInMeasure μ
      (fun n => Z n (skeleton k)) atTop (X (skeleton k)))
    (hZY : ∀ k, TendstoInMeasure μ
      (fun n => Z n (skeleton k)) atTop (Y (skeleton k))) :
    ProcessIndistinguishable μ X Y := by
  apply ProcessIndistinguishable.of_ae_eq_on_rightDense
    X Y skeleton hRightDense
    (Filter.Eventually.of_forall hXRight)
    (Filter.Eventually.of_forall hYRight)
  intro k
  exact tendstoInMeasure_ae_unique (hZX k) (hZY k)

/-- Nonnegative real time has a canonical countable right-dense skeleton,
so fixed-time convergence in measure on all times determines a unique
right-continuous process limit. -/
theorem of_common_tendstoInMeasure_nnreal
    {μ : Measure Ω} (Z : ℕ → Process Ω) (X Y : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hYRight : ∀ ω t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    (hZX : ∀ t, TendstoInMeasure μ
      (fun n => Z n t) atTop (X t))
    (hZY : ∀ t, TendstoInMeasure μ
      (fun n => Z n t) atTop (Y t)) :
    ProcessIndistinguishable μ X Y := by
  exact of_common_tendstoInMeasure_on_rightDense Z X Y
    NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense hXRight hYRight
    (fun k => hZX _) (fun k => hZY _)

end ProcessIndistinguishable

namespace FactorialChronologicalGrid

omit [MeasurableSpace Ω] in
/-- The capped factorial envelope satisfies the triangle inequality needed
to compare two limits through one common approximating process. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
    (X Y Z : Process Ω) (T : ℝ≥0) (ω : Ω) :
    cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X t ω - Y t ω) T ω ≤
      cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => Z t ω - X t ω) T ω +
        cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => Z t ω - Y t ω) T ω := by
  let E : (Process Ω) → ℝ≥0∞ := fun W =>
    eFactorialRunningMaxEnvelope (fun t ω => |W t ω|) T ω
  have hEnvelope : E (fun t ω => X t ω - Y t ω) ≤
      E (fun t ω => Z t ω - X t ω) +
        E (fun t ω => Z t ω - Y t ω) := by
    have h := eFactorialRunningMaxEnvelope_le_add_three_of_pointwise
      (fun t ω => |X t ω - Y t ω|)
      (fun t ω => |Z t ω - X t ω|)
      (fun t ω => |Z t ω - Y t ω|)
      (fun _ _ => (0 : ℝ)) T ω
      (fun _ _ => abs_nonneg _)
      (fun _ _ => abs_nonneg _)
      (fun _ _ => le_rfl)
      (fun t => by
        have hAdd : X t ω - Y t ω =
            -(Z t ω - X t ω) + (Z t ω - Y t ω) := by ring
        rw [hAdd]
        simpa only [abs_neg, add_zero] using
          abs_add_le (-(Z t ω - X t ω)) (Z t ω - Y t ω))
    have hZero : eFactorialRunningMaxEnvelope
        (fun _ _ => (0 : ℝ)) T ω = 0 := by
      simp [eFactorialRunningMaxEnvelope, factorialRunningMax,
        finiteRunningMax, ChronologicalGrid.natSample]
    simpa only [E, hZero, add_zero] using h
  let A := E (fun t ω => Z t ω - X t ω)
  let B := E (fun t ω => Z t ω - Y t ω)
  have hMinAdd : min (A + B) 1 ≤ min A 1 + min B 1 := by
    by_cases hA : A ≤ 1
    · rw [min_eq_left hA]
      by_cases hB : B ≤ 1
      · rw [min_eq_left hB]
        exact min_le_left _ _
      · rw [min_eq_right (le_of_not_ge hB)]
        exact (min_le_right _ _).trans (le_add_of_nonneg_left bot_le)
    · rw [min_eq_right (le_of_not_ge hA)]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right bot_le)
  have hMin : min (E (fun t ω => X t ω - Y t ω)) 1 ≤
      min A 1 + min B 1 :=
    (min_le_min hEnvelope le_rfl).trans hMinAdd
  unfold cappedFiniteHorizonAbsoluteEnvelope
  change (min (E (fun t ω => X t ω - Y t ω)) 1).toReal ≤
    (min A 1).toReal + (min B 1).toReal
  have hAFinite : min A 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hBFinite : min B 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  rw [← ENNReal.toReal_add hAFinite hBFinite]
  exact ENNReal.toReal_mono (by finiteness) hMin

/-- Vanishing capped envelopes on every positive integer horizon force a
right-continuous process to vanish at every time. -/
theorem eq_zero_of_cappedFiniteHorizonAbsoluteEnvelope_ae_eq_zero
    {μ : Measure Ω}
    (X : Process Ω)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hZero : ∀ r : ℕ,
      cappedFiniteHorizonAbsoluteEnvelope X
        ((r + 1 : ℕ) : ℝ≥0) =ᵐ[μ] 0) :
    ProcessIndistinguishable μ X (fun _ _ => 0) := by
  have hZeroAll : ∀ᵐ ω ∂μ, ∀ r : ℕ,
      cappedFiniteHorizonAbsoluteEnvelope X
        ((r + 1 : ℕ) : ℝ≥0) ω = 0 := by
    rw [ae_all_iff]
    exact hZero
  filter_upwards [hZeroAll] with ω hω
  intro t
  have hApproxZero : ∀ᶠ r in atTop, X (approx r t) ω = 0 := by
    filter_upwards [eventually_ge_atTop (Nat.ceil t)] with r hr
    let kFin := approxIndex t hr
    let k := kFin.1
    have hk : k ≤ r * r.factorial :=
      Nat.le_of_lt_succ kFin.2
    have hkIndex :
        (stoppedGrid ((r + 1 : ℕ) : ℝ≥0) r).natIndex k = kFin := by
      ext
      simp [ChronologicalGrid.natIndex, k, min_eq_left hk]
    have hApproxLe : approx r t ≤ (r : ℝ≥0) := by
      rw [approx, div_le_iff₀ (by positivity)]
      change (k : ℝ≥0) ≤ (r : ℝ≥0) * (r.factorial : ℝ≥0)
      exact_mod_cast hk
    let E := eFactorialRunningMaxEnvelope
      (fun t ω => |X t ω|) ((r + 1 : ℕ) : ℝ≥0) ω
    have hMinZero : min E 1 = 0 := by
      have hToReal : (min E 1).toReal = 0 := by
        simpa only [cappedFiniteHorizonAbsoluteEnvelope, E] using hω r
      have hFinite : min E 1 ≠ ∞ :=
        ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
      exact ((ENNReal.toReal_eq_zero_iff _).mp hToReal).resolve_right hFinite
    have hEZero : E = 0 := by
      by_contra hE
      have hEPos : 0 < E := bot_lt_iff_ne_bot.2 hE
      have hMinPos : 0 < min E 1 := lt_min hEPos (by norm_num)
      exact (ne_of_gt hMinPos) hMinZero
    have hSample := ofReal_natSample_le_eFactorialRunningMaxEnvelope
      (fun t ω => |X t ω|) ((r + 1 : ℕ) : ℝ≥0) r k hk ω
    have hStoppedTime :
        (stoppedGrid ((r + 1 : ℕ) : ℝ≥0) r).sampledTime k =
          approx r t := by
      simp only [ChronologicalGrid.sampledTime, hkIndex, stoppedGrid_time]
      rw [show (grid r).time kFin = approx r t by
        simpa only [kFin] using grid_time_approxIndex t hr]
      rw [min_eq_left]
      have hrSucc : (r : ℝ≥0) ≤ ((r + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast Nat.le_succ r
      exact hApproxLe.trans hrSucc
    rw [hStoppedTime] at hSample
    change ENNReal.ofReal |X (approx r t) ω| ≤ E at hSample
    rw [hEZero] at hSample
    have hAbs : |X (approx r t) ω| = 0 := by
      have hOfReal : ENNReal.ofReal |X (approx r t) ω| = 0 :=
        le_antisymm hSample bot_le
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hOfReal) (abs_nonneg _)
    exact abs_eq_zero.mp hAbs
  have hApproxTendsto : Tendsto (fun r => X (approx r t) ω) atTop
      (𝓝 (X t ω)) :=
    (hRight ω t).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_approx t,
          Filter.Eventually.of_forall fun r => le_approx r t⟩)
  have hZeroTendsto : Tendsto (fun r => X (approx r t) ω) atTop
      (𝓝 0) := tendsto_const_nhds.congr'
        (hApproxZero.mono fun r hr => hr.symm)
  exact tendsto_nhds_unique hApproxTendsto hZeroTendsto

/-- Two right-continuous compact-uniform limits in probability of the same
process sequence are indistinguishable. -/
theorem processIndistinguishable_of_common_cappedFiniteHorizon_limit
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (Z : ℕ → Process Ω) (X Y : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hYRight : ∀ ω t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    (hZX : ∀ r : ℕ, TendstoInMeasure μ
      (fun n => cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => Z n t ω - X t ω) ((r + 1 : ℕ) : ℝ≥0))
      atTop (fun _ => 0))
    (hZY : ∀ r : ℕ, TendstoInMeasure μ
      (fun n => cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => Z n t ω - Y t ω) ((r + 1 : ℕ) : ℝ≥0))
      atTop (fun _ => 0)) :
    ProcessIndistinguishable μ X Y := by
  have hEnvelopeZero : ∀ r : ℕ,
      cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X t ω - Y t ω) ((r + 1 : ℕ) : ℝ≥0) =ᵐ[μ] 0 := by
    intro r
    have hSum : TendstoInMeasure μ
        (fun n ω =>
          cappedFiniteHorizonAbsoluteEnvelope
              (fun t ω => Z n t ω - X t ω)
                ((r + 1 : ℕ) : ℝ≥0) ω +
            cappedFiniteHorizonAbsoluteEnvelope
              (fun t ω => Z n t ω - Y t ω)
                ((r + 1 : ℕ) : ℝ≥0) ω)
        atTop (fun _ => 0) := by
      simpa only [zero_add] using tendstoInMeasure_add (hZX r) (hZY r)
    obtain ⟨ns, hns, hSumAE⟩ := hSum.exists_seq_tendsto_ae'
    filter_upwards [hSumAE] with ω hω
    have hTargetNonneg : 0 ≤ cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X t ω - Y t ω) ((r + 1 : ℕ) : ℝ≥0) ω :=
      cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _
    apply le_antisymm _ hTargetNonneg
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hω ε hε
    have hNear := hN N le_rfl
    have hSumNonneg : 0 ≤
        cappedFiniteHorizonAbsoluteEnvelope
            (fun t ω => Z (ns N) t ω - X t ω)
              ((r + 1 : ℕ) : ℝ≥0) ω +
          cappedFiniteHorizonAbsoluteEnvelope
            (fun t ω => Z (ns N) t ω - Y t ω)
              ((r + 1 : ℕ) : ℝ≥0) ω :=
      add_nonneg
        (cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)
        (cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hSumNonneg] at hNear
    simpa only [zero_add] using
      (cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
        X Y (Z (ns N)) ((r + 1 : ℕ) : ℝ≥0) ω).trans hNear.le
  have hDifference :=
    eq_zero_of_cappedFiniteHorizonAbsoluteEnvelope_ae_eq_zero
      (μ := μ) (fun t ω => X t ω - Y t ω)
      (fun ω t => (hXRight ω t).sub (hYRight ω t)) hEnvelopeZero
  filter_upwards [hDifference] with ω hω
  intro t
  exact sub_eq_zero.mp (hω t)

end FactorialChronologicalGrid

end FTAPTheorem42
