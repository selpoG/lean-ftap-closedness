/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import FTAPTheorem42.Stochastic.Martingale.Basic.CountableRangeStoppedMartingale
import Mathlib.Probability.Process.Stopping

/-!
# Countable-range right approximations of finite stopping times

Rounding a finite stopping time upward to the factorial grid produces a
countable-range stopping time.  The approximations lie above the original
time and converge to it pointwise, so right-continuous processes sampled at
them converge to the value at the original stopping time.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StoppingTimeRightApproximation

/-- Round a finite random time upward to the level-`r` factorial grid. -/
noncomputable def approx (r : ℕ) (τ : Ω → ℝ≥0) : Ω → ℝ≥0 :=
  fun ω => FactorialChronologicalGrid.approx r (τ ω)

omit [MeasurableSpace Ω] in
theorem le_approx (r : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) :
    τ ω ≤ approx r τ ω :=
  FactorialChronologicalGrid.le_approx r (τ ω)

omit [MeasurableSpace Ω] in
theorem tendsto_approx (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun r => approx r τ ω) atTop (𝓝 (τ ω)) :=
  FactorialChronologicalGrid.tendsto_approx (τ ω)

omit [MeasurableSpace Ω] in
/-- Factorial rounding overshoots its target by at most one. -/
theorem approx_le_add_one (r : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) :
    approx r τ ω ≤ τ ω + 1 := by
  unfold approx FactorialChronologicalGrid.approx
  rw [div_le_iff₀ (by positivity)]
  have hceil :
      (Nat.ceil (τ ω * (r.factorial : ℝ≥0)) : ℝ≥0) ≤
        τ ω * (r.factorial : ℝ≥0) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    (Nat.ceil (τ ω * (r.factorial : ℝ≥0)) : ℝ≥0)
        ≤ τ ω * (r.factorial : ℝ≥0) + 1 := hceil
    _ ≤ τ ω * (r.factorial : ℝ≥0) +
        1 * (r.factorial : ℝ≥0) := by
      have hf : (1 : ℝ≥0) ≤ 1 * (r.factorial : ℝ≥0) := by
        simpa only [one_mul] using
          (show (1 : ℝ≥0) ≤ (r.factorial : ℝ≥0) by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r))
      simpa only [add_comm] using
        add_le_add_left hf (τ ω * (r.factorial : ℝ≥0))
    _ = (τ ω + 1) * (r.factorial : ℝ≥0) := by rw [add_mul]

omit [MeasurableSpace Ω] in
/-- A deterministic upper bound for the original time gives a uniform upper
bound for all right approximations. -/
theorem approx_le_add_one_of_le
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (r : ℕ) (ω : Ω) :
    approx r τ ω ≤ T + 1 :=
  (approx_le_add_one r τ ω).trans (add_le_add (hτT ω) le_rfl)

omit [MeasurableSpace Ω] in
theorem countable_range (r : ℕ) (τ : Ω → ℝ≥0) :
    (Set.range (approx r τ)).Countable := by
  apply Set.Countable.mono ?_
    (Set.countable_range fun k : ℕ =>
      (k : ℝ≥0) / (r.factorial : ℝ≥0))
  rintro _ ⟨ω, rfl⟩
  exact ⟨Nat.ceil (τ ω * (r.factorial : ℝ≥0)), rfl⟩

/-- Upward factorial rounding preserves the stopping-time property. -/
theorem isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (r : ℕ) :
    IsStoppingTime ℱ (fun ω => (approx r τ ω : WithTop ℝ≥0)) := by
  intro i
  let q : ℕ → ℝ≥0 := fun k =>
    (k : ℝ≥0) / (r.factorial : ℝ≥0)
  have hevent :
      {ω | (approx r τ ω : WithTop ℝ≥0) ≤ i} =
        ⋃ k : ℕ, if q k ≤ i then
        {ω | (τ ω : WithTop ℝ≥0) ≤ q k} else ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro happrox
      let k := Nat.ceil (τ ω * (r.factorial : ℝ≥0))
      refine ⟨k, ?_⟩
      have hqi : q k ≤ i := by
        exact_mod_cast happrox
      simp only [hqi, ↓reduceIte, Set.mem_ofPred_eq]
      exact_mod_cast le_approx r τ ω
    · rintro ⟨k, hk⟩
      by_cases hki : q k ≤ i
      · simp only [hki, ↓reduceIte, Set.mem_ofPred_eq] at hk
        have hceil : Nat.ceil (τ ω * (r.factorial : ℝ≥0)) ≤ k := by
          apply Nat.ceil_le.mpr
          have hk' : τ ω ≤ q k := WithTop.coe_le_coe.mp hk
          change τ ω ≤ (k : ℝ≥0) / (r.factorial : ℝ≥0) at hk'
          rw [le_div_iff₀ (by positivity)] at hk'
          exact_mod_cast hk'
        have hrounded : approx r τ ω ≤ q k := by
          unfold approx FactorialChronologicalGrid.approx q
          exact div_le_div_of_nonneg_right (by exact_mod_cast hceil)
            (by positivity)
        exact_mod_cast hrounded.trans hki
      · rw [ite_eq_right hki] at hk
        simp only [Set.mem_empty_iff_false] at hk
  rw [hevent]
  apply MeasurableSet.iUnion
  intro k
  by_cases hki : q k ≤ i
  · rw [ite_eq_left hki]
    exact ℱ.mono hki _ (hτ (q k))
  · rw [ite_eq_right hki]
    exact @MeasurableSet.empty Ω (ℱ i)

omit [MeasurableSpace Ω] in
/-- Right continuity turns the pointwise time approximation into convergence
of sampled process values. -/
theorem tendsto_sample
    (X : ℝ≥0 → Ω → ℝ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun r => X (approx r τ ω) ω) atTop (𝓝 (X (τ ω) ω)) := by
  apply (hXRight ω (τ ω)).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_approx τ ω,
    Filter.Eventually.of_forall fun r => le_approx r τ ω⟩

/-- A strongly adapted right-continuous process sampled at an arbitrary
bounded finite stopping time is strongly measurable at the deterministic
upper-bound sigma algebra. -/
theorem stronglyMeasurable_sample_of_boundedStoppingTime_filtration
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    StronglyMeasurable[ℱ T] (fun ω => X (τ ω) ω) := by
  let ρ : ℕ → Ω → ℝ≥0 := fun r ω => min (approx r τ ω) T
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun r ω => X (ρ r ω) ω)
    (g := fun ω => X (τ ω) ω) ?_ ?_
  · intro r
    have hρ : IsStoppingTime ℱ (fun ω => (ρ r ω : WithTop ℝ≥0)) := by
      simpa [ρ, WithTop.coe_min] using
        (isStoppingTime hτ r).min (isStoppingTime_const ℱ T)
    have hρEq : MeasureTheory.stoppedValue X
        (fun ω => (ρ r ω : WithTop ℝ≥0)) =
          fun ω => X (ρ r ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [← hρEq]
    exact FTAPTheorem42.StronglyAdapted.stronglyMeasurable_stoppedValue_of_countableRange_filtration
        hX hρ
        (by
          apply Set.Countable.mono ?_
            ((countable_range r τ).image
              (fun t : ℝ≥0 => ((min t T : ℝ≥0) : WithTop ℝ≥0)))
          rintro _ ⟨ω, rfl⟩
          exact ⟨approx r τ ω, ⟨ω, rfl⟩, by rfl⟩)
        (fun ω => WithTop.coe_le_coe.mpr (min_le_right _ _))
  · rw [tendsto_pi_nhds]
    intro ω
    apply (hXRight ω (τ ω)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hTend := (tendsto_approx τ ω).min
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => T) atTop (𝓝 T))
      simpa [ρ, min_eq_left (hτT ω)] using hTend
    · exact Filter.Eventually.of_forall fun r =>
        le_min (le_approx r τ ω) (hτT ω)

/-- Ambient measurable form of
`stronglyMeasurable_sample_of_boundedStoppingTime_filtration`. -/
theorem stronglyMeasurable_sample_of_boundedStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    StronglyMeasurable (fun ω => X (τ ω) ω) :=
  (stronglyMeasurable_sample_of_boundedStoppingTime_filtration
    hX hτ hτT hXRight).mono (ℱ.le T)

end StoppingTimeRightApproximation

end FTAPTheorem42
