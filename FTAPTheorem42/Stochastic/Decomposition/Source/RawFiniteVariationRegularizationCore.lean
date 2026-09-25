/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure
import FTAPTheorem42.Foundations.Variation

/-!
# Source-independent regularization and Jordan path core

This module contains the pathwise cumulative variation, signed-measure bridge,
and zero-normalized Jordan helpers shared by bounded-source and envelope
regularization endpoints.  Process-specific null-set and integrability
certificates remain in their respective modules.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Cumulative variation and zero-normalized Jordan paths -/

noncomputable def commonStopJordanPositive
    (A : Process Omega) : Process Omega :=
  fun t omega =>
    (localVariation A t omega + A t omega) / 2

noncomputable def commonStopJordanNegative
    (A : Process Omega) : Process Omega :=
  fun t omega =>
    (localVariation A t omega - A t omega) / 2

omit [MeasurableSpace Omega] in
@[simp]
theorem commonStopCumulativeVariation_apply
    (A : Process Omega) (t : NNReal) (omega : Omega) :
    localVariation A t omega =
      variationOnFromTo (fun s => A s omega) Set.univ 0 t :=
  rfl

omit [MeasurableSpace Omega] in
@[simp]
theorem commonStopJordanPositive_apply
    (A : Process Omega) (t : NNReal) (omega : Omega) :
    commonStopJordanPositive A t omega =
      (localVariation A t omega + A t omega) / 2 :=
  rfl

omit [MeasurableSpace Omega] in
@[simp]
theorem commonStopJordanNegative_apply
    (A : Process Omega) (t : NNReal) (omega : Omega) :
    commonStopJordanNegative A t omega =
      (localVariation A t omega - A t omega) / 2 :=
  rfl

/-! The cumulative variation is explicitly identified with the Jordan total
variation of the signed Stieltjes measure. -/

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_eq_totalVariation
    {A : Process Omega}
    {hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ}
    {hRight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t}
    (t : NNReal) (omega : Omega) :
    localVariation A t omega =
      (FiniteVariationPath.signedMeasure (hA omega)).totalVariation.real
        (Ioc 0 t) := by
  calc
    localVariation A t omega =
        variationOnFromTo (fun s => A s omega) Set.univ 0 t := rfl
    _ = (FiniteVariationPath.signedMeasure (hA omega)).totalVariation.real
        (Ioc 0 t) :=
      FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
        (hA omega) (hRight omega) bot_le

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_eq_variation
    {A : Process Omega}
    {hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ}
    {hRight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t}
    (t : NNReal) (omega : Omega) :
    localVariation A t omega =
      (FiniteVariationPath.signedMeasure (hA omega)).variation.real
        (Ioc 0 t) := by
  calc
    localVariation A t omega =
        (FiniteVariationPath.signedMeasure (hA omega)).totalVariation.real
          (Ioc 0 t) :=
      commonStopCumulativeVariation_eq_totalVariation
        (hRight := hRight) t omega
    _ = (FiniteVariationPath.signedMeasure (hA omega)).variation.real
        (Ioc 0 t) := by
      rw [signedMeasure_totalVariation_eq_variation]

/-! ## Pathwise variation facts used by both endpoints -/

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_monotone
    {A : Process Omega}
    (hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega, Monotone (localVariation A · omega) := by
  intro omega
  rw [← monotoneOn_univ]
  exact variationOnFromTo.monotoneOn
    (hA omega).locallyBoundedVariationOn (Set.mem_univ 0)

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_zero
    (A : Process Omega) :
    localVariation A 0 = 0 := by
  funext omega
  simp [localVariation, variationOnFromTo.self]

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_rightContinuous
    {A : Process Omega}
    (hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hRight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t) :
    ∀ omega t,
      ContinuousWithinAt (localVariation A · omega) (Ici t) t := by
  intro omega t
  change ContinuousWithinAt
    (variationOnFromTo (fun s => A s omega) Set.univ 0)
    (Ici t) t
  exact (hA omega).continuousWithinAt_variationOnFromTo_Ici (hRight omega t)

omit [MeasurableSpace Omega] in
theorem commonStopCumulativeVariation_constant_after
    {A : Process Omega} {T : NNReal}
    (hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hConstant : ∀ omega t, T ≤ t → A t omega = A T omega) :
    ∀ omega t, T ≤ t →
      localVariation A t omega =
        localVariation A T omega := by
  intro omega t htt
  let f : NNReal → Real := fun s => A s omega
  have hLoc : LocallyBoundedVariationOn f Set.univ :=
    (hA omega).locallyBoundedVariationOn
  have hZeroVar : variationOnFromTo f Set.univ T t = 0 := by
    apply (variationOnFromTo.eq_zero_iff_of_le hLoc
      (Set.mem_univ T) (Set.mem_univ t) htt).2
    intro x hx y hy
    have hxT : T ≤ x := hx.2.1
    have hyT : T ≤ y := hy.2.1
    change edist (A x omega) (A y omega) = 0
    rw [hConstant omega x hxT, hConstant omega y hyT]
    simp
  have hAdd := variationOnFromTo.add hLoc
    (Set.mem_univ 0) (Set.mem_univ T) (Set.mem_univ t)
  dsimp [localVariation, f]
  rw [← hAdd, hZeroVar, add_zero]

omit [MeasurableSpace Omega] in
theorem commonStopJordanPositive_monotone
    {A : Process Omega}
    (hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega, Monotone (commonStopJordanPositive A · omega) := by
  intro omega s t hst
  have h := (variationOnFromTo.add_self_monotoneOn
    (hA omega).locallyBoundedVariationOn (Set.mem_univ 0))
    (Set.mem_univ s) (Set.mem_univ t) hst
  change
    (variationOnFromTo (fun s => A s omega) Set.univ 0 s + A s omega) ≤
      variationOnFromTo (fun s => A s omega) Set.univ 0 t + A t omega at h
  dsimp [commonStopJordanPositive, localVariation]
  linarith

omit [MeasurableSpace Omega] in
theorem commonStopJordanNegative_monotone
    {A : Process Omega}
    (hA : ∀ omega, BoundedVariationOn (A · omega) Set.univ) :
    ∀ omega, Monotone (commonStopJordanNegative A · omega) := by
  intro omega s t hst
  have h := (variationOnFromTo.sub_self_monotoneOn
    (hA omega).locallyBoundedVariationOn (Set.mem_univ 0))
    (Set.mem_univ s) (Set.mem_univ t) hst
  change
    (variationOnFromTo (fun s => A s omega) Set.univ 0 s - A s omega) ≤
      variationOnFromTo (fun s => A s omega) Set.univ 0 t - A t omega at h
  dsimp [commonStopJordanNegative, localVariation]
  linarith

omit [MeasurableSpace Omega] in
theorem commonStopJordanPositive_zero
    {A : Process Omega} (hAZero : A 0 = 0) :
    commonStopJordanPositive A 0 = 0 := by
  funext omega
  simp [commonStopJordanPositive, localVariation,
    variationOnFromTo.self, hAZero]

omit [MeasurableSpace Omega] in
theorem commonStopJordanNegative_zero
    {A : Process Omega} (hAZero : A 0 = 0) :
    commonStopJordanNegative A 0 = 0 := by
  funext omega
  simp [commonStopJordanNegative, localVariation,
    variationOnFromTo.self, hAZero]
end HorizonFactorialGrid

end FTAPTheorem42
