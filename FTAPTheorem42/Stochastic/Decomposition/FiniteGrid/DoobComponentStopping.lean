/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobDoubleStopping

/-!
# Variation stopping of both finite-grid Doob components

The predictable gate stays open while the already accumulated variation of
the discrete Doob predictable part is below a fixed level. Integrating this
gate against the source and both Doob components gives an exact stopped
decomposition. The predictable component has deterministically bounded
variation, while the martingale component remains a true martingale.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The predictable gate which stays open until the accumulated discrete
Doob variation reaches `a`. -/
noncomputable def doobVariationGate
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  fun n omega =>
    if G.doobPredictableVariation S F mu n omega < a then 1 else 0

/-- The variation gate is adapted to the sampled filtration. -/
theorem stronglyAdapted_doobVariationGate
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsFiniteMeasure mu] (a : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobVariationGate S F mu a) := by
  intro n
  let B : Set Omega :=
    {omega | G.doobPredictableVariation S F mu n omega < a}
  have hB : MeasurableSet[G.sampledFiltration F n] B := by
    change MeasurableSet[G.sampledFiltration F n]
      ((G.doobPredictableVariation S F mu n) ⁻¹' Iio a)
    exact (G.stronglyAdapted_doobPredictableVariation S F mu n).measurable
      measurableSet_Iio
  change StronglyMeasurable[G.sampledFiltration F n]
    (B.piecewise (fun _ => (1 : Real)) 0)
  exact StronglyMeasurable.piecewise hB stronglyMeasurable_const
    stronglyMeasurable_zero

/-- The variation gate has absolute value at most one. -/
theorem abs_doobVariationGate_le_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) (omega : Omega) :
    |G.doobVariationGate S F mu a n omega| ≤ 1 := by
  unfold doobVariationGate
  split_ifs <;> norm_num

/-- Discrete predictable variation increases with the grid index. -/
theorem monotone_doobPredictableVariation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    Monotone (G.doobPredictableVariation S F mu) := by
  apply monotone_nat_of_le_succ
  intro n omega
  unfold doobPredictableVariation
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (abs_nonneg _)

/-- The source stopped when its discrete predictable variation reaches
`a`. -/
noncomputable def doobVariationStoppedSourcePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  discretePredictableIntegral (G.doobVariationGate S F mu a) (G.natSample S)

/-- The predictable Doob component stopped by the same variation gate. -/
noncomputable def doobVariationStoppedPredictablePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  discretePredictableIntegral
    (G.doobVariationGate S F mu a) (G.doobPredictablePart S F mu)

/-- The martingale Doob component stopped by the same variation gate. -/
noncomputable def doobVariationStoppedMartingalePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  discretePredictableIntegral
    (G.doobVariationGate S F mu a) (G.doobMartingalePart S F mu)

/-- Variation stopping preserves the discrete Doob decomposition exactly. -/
theorem doobVariationStoppedSourcePart_eq_add
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) :
    G.doobVariationStoppedSourcePart S F mu a n =
      G.doobVariationStoppedMartingalePart S F mu a n +
        G.doobVariationStoppedPredictablePart S F mu a n := by
  funext omega
  unfold doobVariationStoppedSourcePart doobVariationStoppedMartingalePart
    doobVariationStoppedPredictablePart discretePredictableIntegral
    doobMartingalePart martingalePart doobPredictablePart
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The stopped predictable component has exactly the stopped accumulated
variation. -/
theorem sum_abs_doobVariationStoppedPredictablePart_increment
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) (omega : Omega) :
    ∑ k ∈ Finset.range n,
        |G.doobVariationStoppedPredictablePart S F mu a (k + 1) omega -
          G.doobVariationStoppedPredictablePart S F mu a k omega| =
      G.doobVariationStoppedAccumulation S F mu a n omega := by
  unfold doobVariationStoppedPredictablePart doobVariationStoppedAccumulation
  apply Finset.sum_congr rfl
  intro k _hk
  have hIncrement := congrFun (discretePredictableIntegral_succ_sub
    (G.doobVariationGate S F mu a) (G.doobPredictablePart S F mu) k) omega
  simp only [Pi.sub_apply, Pi.mul_apply] at hIncrement
  rw [hIncrement]
  unfold doobVariationGate doobPredictableIncrement
  by_cases h : G.doobPredictableVariation S F mu k omega < a
  · simp [h]
  · simp [h]

/-- The stopped predictable component has uniformly bounded discrete total
variation at every grid index. -/
theorem ae_sum_abs_doobVariationStoppedPredictablePart_increment_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a) :
    ∀ᵐ omega ∂mu, ∀ n,
      ∑ k ∈ Finset.range n,
          |G.doobVariationStoppedPredictablePart S F mu a (k + 1) omega -
            G.doobVariationStoppedPredictablePart S F mu a k omega| ≤
        a + 2 * max source.bound 0 := by
  filter_upwards [G.ae_doobVariationStoppedAccumulation_le source ha] with
      omega homega
  intro n
  rw [G.sum_abs_doobVariationStoppedPredictablePart_increment S F mu a]
  exact homega n

/-- Before the variation threshold is reached, the stopped source integral
is the full source increment. -/
theorem doobVariationStoppedSourcePart_eq_of_variation_lt
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) {n : Nat} {omega : Omega}
    (hVariation : G.doobPredictableVariation S F mu n omega < a) :
    G.doobVariationStoppedSourcePart S F mu a n omega =
      G.natSample S n omega - G.natSample S 0 omega := by
  induction n with
  | zero =>
      simp [doobVariationStoppedSourcePart]
  | succ n ih =>
      have hVariationPrevious :
          G.doobPredictableVariation S F mu n omega < a := by
        apply lt_of_le_of_lt _ hVariation
        unfold doobPredictableVariation
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (abs_nonneg _)
      have hIncrement := congrFun (discretePredictableIntegral_succ
        (G.doobVariationGate S F mu a) (G.natSample S) n) omega
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] at hIncrement
      rw [show G.doobVariationStoppedSourcePart S F mu a (n + 1) omega =
          G.doobVariationStoppedSourcePart S F mu a n omega +
            G.doobVariationGate S F mu a n omega *
              (G.natSample S (n + 1) omega - G.natSample S n omega) by
        exact hIncrement]
      rw [ih hVariationPrevious]
      simp only [doobVariationGate, ite_eq_left hVariationPrevious, one_mul]
      ring

/-- At every grid index the stopped source integral is one source increment
from time zero, evaluated at some earlier grid index. -/
theorem exists_doobVariationStoppedSourcePart_eq
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) (omega : Omega) :
    ∃ k ≤ n,
      G.doobVariationStoppedSourcePart S F mu a n omega =
        G.natSample S k omega - G.natSample S 0 omega := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      simp [doobVariationStoppedSourcePart]
  | succ n ih =>
      by_cases hVariation :
          G.doobPredictableVariation S F mu n omega < a
      · refine ⟨n + 1, le_rfl, ?_⟩
        have hIncrement := congrFun (discretePredictableIntegral_succ
          (G.doobVariationGate S F mu a) (G.natSample S) n) omega
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] at hIncrement
        rw [show G.doobVariationStoppedSourcePart S F mu a (n + 1) omega =
            G.doobVariationStoppedSourcePart S F mu a n omega +
              G.doobVariationGate S F mu a n omega *
                (G.natSample S (n + 1) omega - G.natSample S n omega) by
          exact hIncrement]
        rw [G.doobVariationStoppedSourcePart_eq_of_variation_lt
          S F mu a hVariation]
        simp only [doobVariationGate, ite_eq_left hVariation, one_mul]
        ring
      · obtain ⟨k, hk, hEq⟩ := ih
        refine ⟨k, hk.trans (Nat.le_succ n), ?_⟩
        have hIncrement := congrFun (discretePredictableIntegral_succ
          (G.doobVariationGate S F mu a) (G.natSample S) n) omega
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] at hIncrement
        rw [show G.doobVariationStoppedSourcePart S F mu a (n + 1) omega =
            G.doobVariationStoppedSourcePart S F mu a n omega +
              G.doobVariationGate S F mu a n omega *
                (G.natSample S (n + 1) omega - G.natSample S n omega) by
          exact hIncrement]
        simp only [doobVariationGate, ite_eq_right hVariation, zero_mul, add_zero]
        exact hEq

/-- A bounded source gives a deterministic pathwise bound for its
variation-stopped discrete integral. -/
theorem ae_abs_doobVariationStoppedSourcePart_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real) :
    ∀ᵐ omega ∂mu, ∀ n,
      |G.doobVariationStoppedSourcePart S F mu a n omega| ≤
        2 * max source.bound 0 := by
  filter_upwards [source.uniformBound] with omega homega
  intro n
  obtain ⟨k, _hk, hEq⟩ :=
    G.exists_doobVariationStoppedSourcePart_eq S F mu a n omega
  rw [hEq]
  calc
    |G.natSample S k omega - G.natSample S 0 omega| ≤
        |G.natSample S k omega| + |G.natSample S 0 omega| := abs_sub _ _
    _ ≤ max source.bound 0 + max source.bound 0 := by
      apply add_le_add
      · exact (homega (G.sampledTime k)).trans (le_max_left _ _)
      · exact (homega (G.sampledTime 0)).trans (le_max_left _ _)
    _ = 2 * max source.bound 0 := by ring

/-- The stopped predictable component is bounded in absolute value by its
accumulated variation. -/
theorem abs_doobVariationStoppedPredictablePart_le_accumulation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) (omega : Omega) :
    |G.doobVariationStoppedPredictablePart S F mu a n omega| ≤
      G.doobVariationStoppedAccumulation S F mu a n omega := by
  let A : Nat → Real := fun k =>
    G.doobVariationStoppedPredictablePart S F mu a k omega
  have hZero : A 0 = 0 := by
    simp [A, doobVariationStoppedPredictablePart]
  calc
    |A n| = |∑ k ∈ Finset.range n, (A (k + 1) - A k)| := by
      rw [Finset.sum_range_sub, hZero, sub_zero]
    _ ≤ ∑ k ∈ Finset.range n, |A (k + 1) - A k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = G.doobVariationStoppedAccumulation S F mu a n omega :=
      G.sum_abs_doobVariationStoppedPredictablePart_increment S F mu a n omega

/-- The stopped predictable component is uniformly bounded at every grid
index. -/
theorem ae_abs_doobVariationStoppedPredictablePart_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a) :
    ∀ᵐ omega ∂mu, ∀ n,
      |G.doobVariationStoppedPredictablePart S F mu a n omega| ≤
        a + 2 * max source.bound 0 := by
  filter_upwards [G.ae_doobVariationStoppedAccumulation_le source ha] with
      omega homega
  intro n
  exact (G.abs_doobVariationStoppedPredictablePart_le_accumulation
    S F mu a n omega).trans (homega n)

/-- The stopped predictable component is adapted to the sampled
filtration. -/
theorem stronglyAdapted_doobVariationStoppedPredictablePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (_source : BoundedSemimartingaleSource S F mu) (a : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobVariationStoppedPredictablePart S F mu a) :=
  DiscretePredictableIntegral.stronglyAdapted_of_stronglyAdapted
    (G.stronglyAdapted_doobVariationGate S F mu a)
    stronglyAdapted_predictablePart'

/-- The stopped martingale component is still a true martingale. -/
theorem martingale_doobVariationStoppedMartingalePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real) :
    Martingale
      (G.doobVariationStoppedMartingalePart S F mu a)
      (G.sampledFiltration F) mu := by
  apply DiscretePredictableIntegral.isMartingale
    (C := fun _ => 1)
    (G.martingale_martingalePart_natSample_boundedSemimartingaleSource source)
    (G.memLp_two_doobMartingalePart source)
    (G.stronglyAdapted_doobVariationGate S F mu a)
  intro n
  exact ae_of_all mu fun omega =>
    G.abs_doobVariationGate_le_one S F mu a n omega

/-- The stopped martingale component is uniformly bounded at every grid
index. -/
theorem ae_abs_doobVariationStoppedMartingalePart_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a) :
    ∀ᵐ omega ∂mu, ∀ n,
      |G.doobVariationStoppedMartingalePart S F mu a n omega| ≤
        a + 4 * max source.bound 0 := by
  filter_upwards [G.ae_abs_doobVariationStoppedSourcePart_le source a,
      G.ae_abs_doobVariationStoppedPredictablePart_le source ha] with
      omega hSource hPredictable
  intro n
  have hDecomposition := congrFun
    (G.doobVariationStoppedSourcePart_eq_add S F mu a n) omega
  simp only [Pi.add_apply] at hDecomposition
  have hEq :
      G.doobVariationStoppedMartingalePart S F mu a n omega =
        G.doobVariationStoppedSourcePart S F mu a n omega -
          G.doobVariationStoppedPredictablePart S F mu a n omega := by
    linarith
  rw [hEq]
  calc
    |G.doobVariationStoppedSourcePart S F mu a n omega -
        G.doobVariationStoppedPredictablePart S F mu a n omega| ≤
      |G.doobVariationStoppedSourcePart S F mu a n omega| +
        |G.doobVariationStoppedPredictablePart S F mu a n omega| :=
      abs_sub _ _
    _ ≤ 2 * max source.bound 0 +
        (a + 2 * max source.bound 0) :=
      add_le_add (hSource n) (hPredictable n)
    _ = a + 4 * max source.bound 0 := by ring

/-- Every fixed-time value of the variation-stopped predictable component
belongs to `L²`, with a bound independent of the grid size. -/
theorem memLp_two_doobVariationStoppedPredictablePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a)
    (n : Nat) :
    MemLp (G.doobVariationStoppedPredictablePart S F mu a n)
      (2 : ENNReal) mu := by
  apply MemLp.of_bound
    ((G.stronglyAdapted_doobVariationStoppedPredictablePart source a n).mono
      ((G.sampledFiltration F).le n)).aestronglyMeasurable
    (a + 2 * max source.bound 0)
  filter_upwards [G.ae_abs_doobVariationStoppedPredictablePart_le source ha] with
      omega homega
  simpa only [Real.norm_eq_abs] using homega n

/-- Every fixed-time value of the variation-stopped martingale component
belongs to `L²`, with a bound independent of the grid size. -/
theorem memLp_two_doobVariationStoppedMartingalePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a)
    (n : Nat) :
    MemLp (G.doobVariationStoppedMartingalePart S F mu a n)
      (2 : ENNReal) mu := by
  apply MemLp.of_bound
    ((G.martingale_doobVariationStoppedMartingalePart source a).stronglyMeasurable n
      |>.mono ((G.sampledFiltration F).le n)).aestronglyMeasurable
    (a + 4 * max source.bound 0)
  filter_upwards [G.ae_abs_doobVariationStoppedMartingalePart_le source ha] with
      omega homega
  simpa only [Real.norm_eq_abs] using homega n

end ChronologicalGrid

end FTAPTheorem42
