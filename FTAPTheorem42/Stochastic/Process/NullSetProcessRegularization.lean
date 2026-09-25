/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Foundations.UsualConditions

/-!
# Regularizing processes on one null set

Under the usual conditions, a null set belongs to the time-zero sigma
algebra.  A process can therefore be replaced by zero on that set without
losing adaptedness or predictability.  This module records the resulting
all-path regular versions needed after the component-limit extraction in
Lemma 4.11.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*}

namespace ProcessNullSetRegularization

/-- Replace a real-valued process by zero on a set of sample points. -/
noncomputable def zeroOn (bad : Set Ω) (X : Process Ω) : Process Ω :=
  by
    classical
    exact fun t ω => if ω ∈ bad then 0 else X t ω

@[simp]
theorem zeroOn_apply_of_mem (bad : Set Ω) (X : Process Ω)
    {t : ℝ≥0} {ω : Ω} (hω : ω ∈ bad) :
    zeroOn bad X t ω = 0 := by
  simp [zeroOn, hω]

@[simp]
theorem zeroOn_apply_of_notMem (bad : Set Ω) (X : Process Ω)
    {t : ℝ≥0} {ω : Ω} (hω : ω ∉ bad) :
    zeroOn bad X t ω = X t ω := by
  simp [zeroOn, hω]

/-- A time-zero event, repeated at every time, is predictable. -/
theorem measurableSet_predictable_univ_prod
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {B : Set Ω} (hB : MeasurableSet[ℱ 0] B) :
    MeasurableSet[ℱ.predictable] (Set.univ ×ˢ B) := by
  have hUnion : (Set.univ : Set ℝ≥0) ×ˢ B =
      ({0} ×ˢ B) ∪ (Set.Ioi 0 ×ˢ B) := by
    ext p
    rcases p with ⟨t, ω⟩
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · intro hω
      by_cases ht : t = 0
      · exact Or.inl ⟨ht, hω⟩
      · exact Or.inr ⟨pos_of_ne_zero ht, hω⟩
    · rintro (⟨_, hω⟩ | ⟨_, hω⟩) <;> exact hω
  rw [hUnion]
  exact (measurableSet_predictable_singleton_bot_prod hB).union
    (measurableSet_predictable_Ioi_prod hB)

/-- Zeroing a process on a time-zero event preserves strong adaptedness. -/
theorem stronglyAdapted_zeroOn
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {bad : Set Ω} (hbad : MeasurableSet[ℱ 0] bad)
    {X : Process Ω} (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ (zeroOn bad X) := by
  classical
  intro t
  change StronglyMeasurable[ℱ t]
    (fun ω => if ω ∈ bad then 0 else X t ω)
  exact StronglyMeasurable.ite
    (ℱ.mono bot_le bad hbad) stronglyMeasurable_const (hX t)

/-- Zeroing a process on a time-zero event preserves predictability. -/
theorem isStronglyPredictable_zeroOn
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {bad : Set Ω} (hbad : MeasurableSet[ℱ 0] bad)
    {X : Process Ω} (hX : IsStronglyPredictable ℱ X) :
    IsStronglyPredictable ℱ (zeroOn bad X) := by
  classical
  change StronglyMeasurable[ℱ.predictable]
    (fun p : ℝ≥0 × Ω => if p.2 ∈ bad then 0 else X p.1 p.2)
  have hCylinder : MeasurableSet[ℱ.predictable]
      {p : ℝ≥0 × Ω | p.2 ∈ bad} := by
    rw [show {p : ℝ≥0 × Ω | p.2 ∈ bad} = Set.univ ×ˢ bad by
      ext p
      simp]
    exact measurableSet_predictable_univ_prod hbad
  exact StronglyMeasurable.ite
    hCylinder stronglyMeasurable_const hX

/-- Zeroing on a null set produces an indistinguishable process. -/
theorem zeroOn_indistinguishable
    [MeasurableSpace Ω]
    {μ : Measure Ω} {bad : Set Ω} (hbad : μ bad = 0)
    (X : Process Ω) :
    ProcessIndistinguishable μ (zeroOn bad X) X := by
  have hNotMem : ∀ᵐ ω ∂μ, ω ∉ bad := by
    rw [ae_iff]
    rw [show {ω | ¬ω ∉ bad} = bad by ext ω; simp]
    exact hbad
  filter_upwards [hNotMem] with ω hω
  intro t
  exact zeroOn_apply_of_notMem bad X hω

/-- Right continuity is made pathwise by zeroing the exceptional set. -/
theorem zeroOn_isRightContinuous
    {bad : Set Ω} {X : Process Ω}
    (hX : ∀ ω, ω ∉ bad → ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    ∀ ω t, ContinuousWithinAt
      (fun u => zeroOn bad X u ω) (Set.Ici t) t := by
  intro ω t
  by_cases hω : ω ∈ bad
  · have hZero : (fun u => zeroOn bad X u ω) = fun _ => 0 := by
      funext u
      exact zeroOn_apply_of_mem bad X hω
    rw [hZero]
    exact continuousWithinAt_const
  · have hEq : (fun u => zeroOn bad X u ω) = fun u => X u ω := by
      funext u
      exact zeroOn_apply_of_notMem bad X hω
    rw [hEq]
    exact hX ω hω t

/-- Left limits are made pathwise by zeroing the exceptional set. -/
theorem zeroOn_hasLeftLimits
    {bad : Set Ω} {X : Process Ω}
    (hX : ∀ ω, ω ∉ bad →
      ∀ t, Tendsto (fun s => X s ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => X s ω) t))) :
    ProcessHasLeftLimits (zeroOn bad X) := by
  intro ω t
  by_cases hω : ω ∈ bad
  · have hZero : (fun u => zeroOn bad X u ω) = fun _ => 0 := by
      funext u
      exact zeroOn_apply_of_mem bad X hω
    rw [hZero]
    exact tendsto_leftLim_of_tendsto
      (f := fun _ : ℝ≥0 => (0 : ℝ)) (a := t)
      ⟨0, tendsto_const_nhds⟩
  · have hEq : (fun u => zeroOn bad X u ω) = fun u => X u ω := by
      funext u
      exact zeroOn_apply_of_notMem bad X hω
    rw [hEq]
    exact hX ω hω t

/-- Bounded variation is made pathwise by zeroing the exceptional set. -/
theorem zeroOn_isBoundedVariation
    {bad : Set Ω} {X : Process Ω}
    (hX : ∀ ω, ω ∉ bad →
      BoundedVariationOn (X · ω) Set.univ) :
    ∀ ω, BoundedVariationOn
      (fun u => zeroOn bad X u ω) Set.univ := by
  intro ω
  by_cases hω : ω ∈ bad
  · have hZero : (fun u => zeroOn bad X u ω) = fun _ => 0 := by
      funext u
      exact zeroOn_apply_of_mem bad X hω
    rw [hZero]
    change eVariationOn (fun _ : ℝ≥0 => (0 : ℝ)) Set.univ ≠ ∞
    rw [eVariationOn.constant_on (by simp)]
    exact ENNReal.zero_ne_top
  · have hEq : (fun u => zeroOn bad X u ω) = fun u => X u ω := by
      funext u
      exact zeroOn_apply_of_notMem bad X hω
    rw [hEq]
    exact hX ω hω

/-- Local bounded variation is made pathwise by zeroing the exceptional set. -/
theorem zeroOn_isLocallyBoundedVariation
    {bad : Set Ω} {X : Process Ω}
    (hX : ∀ ω, ω ∉ bad →
      LocallyBoundedVariationOn (X · ω) Set.univ) :
    ∀ ω, LocallyBoundedVariationOn
      (fun u => zeroOn bad X u ω) Set.univ := by
  intro ω
  by_cases hω : ω ∈ bad
  · have hZero : (fun u => zeroOn bad X u ω) =
        fun _ => (0 : ℝ) := by
      funext u
      exact zeroOn_apply_of_mem bad X hω
    rw [hZero]
    have hZeroVariation : BoundedVariationOn
        (fun _ : ℝ≥0 => (0 : ℝ)) Set.univ := by
      change eVariationOn (fun _ : ℝ≥0 => (0 : ℝ)) Set.univ ≠ ∞
      rw [eVariationOn.constant_on (by simp)]
      exact ENNReal.zero_ne_top
    exact hZeroVariation.locallyBoundedVariationOn
  · have hEq : (fun u => zeroOn bad X u ω) = fun u => X u ω := by
      funext u
      exact zeroOn_apply_of_notMem bad X hω
    rw [hEq]
    exact hX ω hω

/-- An adapted process with almost surely right-continuous paths has an
indistinguishable adapted version whose every path is right-continuous. -/
theorem exists_stronglyAdapted_rightContinuous_version
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} (hUsual : Filtration.UsualConditions μ ℱ)
    {X : Process Ω} (hAdapted : StronglyAdapted ℱ X)
    (hRight : ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    ∃ X' : Process Ω,
      StronglyAdapted ℱ X' ∧
        (∀ ω t, ContinuousWithinAt (X' · ω) (Set.Ici t) t) ∧
        ProcessIndistinguishable μ X' X := by
  let bad : Set Ω := {ω | ¬∀ t,
    ContinuousWithinAt (X · ω) (Set.Ici t) t}
  have hbadNull : μ bad = 0 := by
    simpa only [bad] using ae_iff.mp hRight
  have hbadMeasurable : MeasurableSet[ℱ 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hRightOff : ∀ ω, ω ∉ bad → ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t := by
    intro ω hω
    simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
  exact ⟨zeroOn bad X,
    stronglyAdapted_zeroOn hbadMeasurable hAdapted,
    zeroOn_isRightContinuous hRightOff,
    zeroOn_indistinguishable hbadNull X⟩

/-- An adapted process with almost surely right-continuous paths and left
limits has an indistinguishable adapted version with both properties on
every path. -/
theorem exists_stronglyAdapted_rightContinuous_leftLimits_version
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} (hUsual : Filtration.UsualConditions μ ℱ)
    {X : Process Ω} (hAdapted : StronglyAdapted ℱ X)
    (hRegular : ∀ᵐ ω ∂μ,
      (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
        ∀ t, Tendsto (fun s => X s ω) (𝓝[<] t)
          (𝓝 (Function.leftLim (fun s => X s ω) t))) :
    ∃ X' : Process Ω,
      StronglyAdapted ℱ X' ∧
        (∀ ω t, ContinuousWithinAt (X' · ω) (Set.Ici t) t) ∧
        ProcessHasLeftLimits X' ∧
        ProcessIndistinguishable μ X' X := by
  let bad : Set Ω := {ω |
    ¬((∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
      ∀ t, Tendsto (fun s => X s ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => X s ω) t)))}
  have hbadNull : μ bad = 0 := by
    simpa only [bad] using ae_iff.mp hRegular
  have hbadMeasurable : MeasurableSet[ℱ 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hRightOff : ∀ ω, ω ∉ bad → ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t := by
    intro ω hω
    have hReg :
        (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
          ∀ t, Tendsto (fun s => X s ω) (𝓝[<] t)
            (𝓝 (Function.leftLim (fun s => X s ω) t)) := by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hReg.1
  refine ⟨zeroOn bad X,
    stronglyAdapted_zeroOn hbadMeasurable hAdapted,
    zeroOn_isRightContinuous hRightOff, ?_,
    zeroOn_indistinguishable hbadNull X⟩
  apply zeroOn_hasLeftLimits
  intro ω hω t
  have hReg :
      (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
        ∀ t, Tendsto (fun s => X s ω) (𝓝[<] t)
          (𝓝 (Function.leftLim (fun s => X s ω) t)) := by
    simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
  exact hReg.2 t

/-- A predictable process with almost surely right-continuous bounded-
variation paths has an indistinguishable predictable version with those
properties on every path. -/
theorem exists_predictable_rightContinuous_boundedVariation_version
    [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} (hUsual : Filtration.UsualConditions μ ℱ)
    {X : Process Ω} (hPredictable : IsStronglyPredictable ℱ X)
    (hRegular : ∀ᵐ ω ∂μ,
      (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
        BoundedVariationOn (X · ω) Set.univ) :
    ∃ X' : Process Ω,
      IsStronglyPredictable ℱ X' ∧
        (∀ ω t, ContinuousWithinAt (X' · ω) (Set.Ici t) t) ∧
        (∀ ω, BoundedVariationOn (X' · ω) Set.univ) ∧
        ProcessIndistinguishable μ X' X := by
  let bad : Set Ω := {ω |
    ¬((∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
      BoundedVariationOn (X · ω) Set.univ)}
  have hbadNull : μ bad = 0 := by
    simpa only [bad] using ae_iff.mp hRegular
  have hbadMeasurable : MeasurableSet[ℱ 0] bad :=
    hUsual.containsNullSetsAtZero bad hbadNull
  have hRightOff : ∀ ω, ω ∉ bad → ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t := by
    intro ω hω
    have hRegularω :
        (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
          BoundedVariationOn (X · ω) Set.univ := by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hRegularω.1
  have hVariationOff : ∀ ω, ω ∉ bad →
      BoundedVariationOn (X · ω) Set.univ := by
    intro ω hω
    have hRegularω :
        (∀ t, ContinuousWithinAt (X · ω) (Set.Ici t) t) ∧
          BoundedVariationOn (X · ω) Set.univ := by
      simpa only [bad, Set.mem_ofPred_eq, not_not] using hω
    exact hRegularω.2
  exact ⟨zeroOn bad X,
    isStronglyPredictable_zeroOn hbadMeasurable hPredictable,
    zeroOn_isRightContinuous hRightOff,
    zeroOn_isBoundedVariation hVariationOff,
    zeroOn_indistinguishable hbadNull X⟩

end ProcessNullSetRegularization

end FTAPTheorem42
