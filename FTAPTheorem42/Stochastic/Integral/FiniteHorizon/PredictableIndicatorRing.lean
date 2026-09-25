/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct
import Mathlib.MeasureTheory.Measure.AddContent

/-!
# A finite-horizon ring of elementary predictable indicators

For a deterministic horizon `T`, this module records predictable sets whose
intersection with `(0,T] x Omega` is represented by a bounded predictable
elementary integrand.  Products of elementary integrands make these sets a
ring.  The ring contains every generator of the predictable sigma algebra:
time-zero generators have empty positive-horizon section, while
`(s,infinity) x A` is represented on the horizon by one deterministic
buy-and-hold block.

This is the set-theoretic domain on which the finite-horizon martingale
energy content is constructed.  No stochastic-integral existence or energy
measure is assumed here.
-/

open MeasureTheory Set
open scoped NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

namespace FiniteHorizonPredictableIndicatorRing

attribute [local instance] Classical.propDecidable

/-- The strictly positive deterministic horizon on the predictable product
space. -/
def horizonCarrier (T : NNReal) : Set (NNReal × Omega) :=
  Ioc 0 T ×ˢ (Set.univ : Set Omega)

/-- The positive deterministic horizon carrier is predictable. -/
theorem measurableSet_horizonCarrier (T : NNReal) :
    MeasurableSet[F.predictable] (horizonCarrier (Omega := Omega) T) :=
  measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ

/-- The real indicator process of a set in the predictable product space. -/
noncomputable def indicatorProcess (s : Set (NNReal × Omega)) : Process Omega :=
  fun t omega => if (t, omega) ∈ s then 1 else 0

/-- A bounded elementary representation of the indicator of the positive
finite-horizon part of a predictable set. -/
structure BoundedIndicatorRepresentation
    (T : NNReal) (s : Set (NNReal × Omega)) where
  strategy : PredictableElementaryStrategy F
  bound : NNReal
  coefficientAbsSum_le : ∀ omega,
    strategy.coefficientAbsSum omega ≤ (bound : Real)
  integrand_eq : strategy.integrand = indicatorProcess (s ∩ horizonCarrier T)

namespace BoundedIndicatorRepresentation

/-- The empty set has the empty elementary representation. -/
noncomputable def empty (T : NNReal) :
    BoundedIndicatorRepresentation (F := F) T ∅ where
  strategy := []
  bound := 0
  coefficientAbsSum_le := by simp [PredictableElementaryStrategy.coefficientAbsSum]
  integrand_eq := by
    funext t omega
    simp [PredictableElementaryStrategy.integrand, indicatorProcess]

/-- The elementary block whose integrand is the positive horizon indicator. -/
noncomputable def horizonBlock (T : NNReal) :
    PredictableElementaryInterval F where
  interval :=
    { coefficient := fun _ => 1
      startTime := fun _ => 0
      stopTime := fun _ => T
      start_le_stop := fun _ => bot_le }
  startStopping := isStoppingTime_const F 0
  stopStopping := isStoppingTime_const F T
  coefficient_measurable := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurable_const

/-- The whole predictable product space is represented on `(0,T]` by one
deterministic block. -/
noncomputable def univ (T : NNReal) :
    BoundedIndicatorRepresentation (F := F) T Set.univ where
  strategy := [horizonBlock T]
  bound := 1
  coefficientAbsSum_le := by simp [horizonBlock, PredictableElementaryStrategy.coefficientAbsSum]
  integrand_eq := by
    funext t omega
    simp only [PredictableElementaryStrategy.integrand, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      PredictableElementaryInterval.integrand, horizonBlock]
    simp [indicatorProcess, horizonCarrier]

/-- Union of represented sets, realized by `f + g - f*g`. -/
noncomputable def union
    {T : NNReal} {s u : Set (NNReal × Omega)}
    (hs : BoundedIndicatorRepresentation (F := F) T s)
    (hu : BoundedIndicatorRepresentation (F := F) T u) :
    BoundedIndicatorRepresentation (F := F) T (s ∪ u) where
  strategy :=
    (hs.strategy ++ hu.strategy) ++
      (hs.strategy.mul hu.strategy).neg
  bound := hs.bound + hu.bound + hs.bound * hu.bound
  coefficientAbsSum_le := by
    intro omega
    rw [PredictableElementaryStrategy.coefficientAbsSum_append,
      PredictableElementaryStrategy.coefficientAbsSum_append,
      PredictableElementaryStrategy.coefficientAbsSum_neg,
      PredictableElementaryStrategy.coefficientAbsSum_mul]
    have huNonneg := hu.strategy.coefficientAbsSum_nonneg omega
    have hMul := mul_le_mul (hs.coefficientAbsSum_le omega)
      (hu.coefficientAbsSum_le omega) huNonneg (by positivity)
    calc
      hs.strategy.coefficientAbsSum omega +
            hu.strategy.coefficientAbsSum omega +
          hs.strategy.coefficientAbsSum omega *
            hu.strategy.coefficientAbsSum omega ≤
        (hs.bound : Real) + (hu.bound : Real) +
          (hs.bound : Real) * (hu.bound : Real) :=
        add_le_add
          (add_le_add (hs.coefficientAbsSum_le omega)
            (hu.coefficientAbsSum_le omega)) hMul
      _ = ((hs.bound + hu.bound + hs.bound * hu.bound : NNReal) : Real) := by
        norm_cast
  integrand_eq := by
    rw [PredictableElementaryStrategy.append_integrand,
      PredictableElementaryStrategy.append_integrand,
      PredictableElementaryStrategy.neg_integrand,
      PredictableElementaryStrategy.mul_integrand,
      hs.integrand_eq, hu.integrand_eq]
    funext t omega
    simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
    by_cases hst : (t, omega) ∈ s ∩ horizonCarrier T
    · have hUnion : (t, omega) ∈ (s ∪ u) ∩ horizonCarrier T :=
        ⟨Or.inl hst.1, hst.2⟩
      by_cases hut : (t, omega) ∈ u ∩ horizonCarrier T
      · simp [indicatorProcess, hst, hut, hUnion]
      · simp [indicatorProcess, hst, hut, hUnion]
    · by_cases hut : (t, omega) ∈ u ∩ horizonCarrier T
      · have hUnion : (t, omega) ∈ (s ∪ u) ∩ horizonCarrier T :=
          ⟨Or.inr hut.1, hut.2⟩
        simp [indicatorProcess, hst, hut, hUnion]
      · have hNotUnion : (t, omega) ∉ (s ∪ u) ∩ horizonCarrier T := by
          rintro ⟨hsu, hQ⟩
          rcases hsu with hsMem | huMem
          · exact hst ⟨hsMem, hQ⟩
          · exact hut ⟨huMem, hQ⟩
        simp [indicatorProcess, hst, hut, hNotUnion]

/-- Relative complement of represented sets, realized by `f - f*g`. -/
noncomputable def sdiff
    {T : NNReal} {s u : Set (NNReal × Omega)}
    (hs : BoundedIndicatorRepresentation (F := F) T s)
    (hu : BoundedIndicatorRepresentation (F := F) T u) :
    BoundedIndicatorRepresentation (F := F) T (s \ u) where
  strategy := hs.strategy ++ (hs.strategy.mul hu.strategy).neg
  bound := hs.bound + hs.bound * hu.bound
  coefficientAbsSum_le := by
    intro omega
    rw [PredictableElementaryStrategy.coefficientAbsSum_append,
      PredictableElementaryStrategy.coefficientAbsSum_neg,
      PredictableElementaryStrategy.coefficientAbsSum_mul]
    have hMul := mul_le_mul (hs.coefficientAbsSum_le omega)
      (hu.coefficientAbsSum_le omega)
      (hu.strategy.coefficientAbsSum_nonneg omega) (by positivity)
    calc
      hs.strategy.coefficientAbsSum omega +
          hs.strategy.coefficientAbsSum omega *
            hu.strategy.coefficientAbsSum omega ≤
        (hs.bound : Real) + (hs.bound : Real) * (hu.bound : Real) :=
        add_le_add (hs.coefficientAbsSum_le omega) hMul
      _ = ((hs.bound + hs.bound * hu.bound : NNReal) : Real) := by
        norm_cast
  integrand_eq := by
    rw [PredictableElementaryStrategy.append_integrand,
      PredictableElementaryStrategy.neg_integrand,
      PredictableElementaryStrategy.mul_integrand,
      hs.integrand_eq, hu.integrand_eq]
    funext t omega
    simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
    by_cases hst : (t, omega) ∈ s ∩ horizonCarrier T
    · by_cases hut : (t, omega) ∈ u ∩ horizonCarrier T
      · have hNotDiff : (t, omega) ∉ (s \ u) ∩ horizonCarrier T := by
          intro hDiff
          exact hDiff.1.2 hut.1
        simp [indicatorProcess, hst, hut, hNotDiff]
      · have hDiff : (t, omega) ∈ (s \ u) ∩ horizonCarrier T := by
          refine ⟨⟨hst.1, ?_⟩, hst.2⟩
          intro huMem
          exact hut ⟨huMem, hst.2⟩
        simp [indicatorProcess, hst, hut, hDiff]
    · have hNotDiff : (t, omega) ∉ (s \ u) ∩ horizonCarrier T := by
        intro hDiff
        exact hst ⟨hDiff.1.1, hDiff.2⟩
      by_cases hut : (t, omega) ∈ u ∩ horizonCarrier T <;>
        simp [indicatorProcess, hst, hut, hNotDiff]

/-- One deterministic predictable generator, clipped to the horizon, has a
single-block elementary representation. -/
noncomputable def generator
    (T i : NNReal) (A : Set Omega) (hA : MeasurableSet[F i] A) :
    BoundedIndicatorRepresentation (F := F) T (Ioi i ×ˢ A) := by
  let coefficient : Omega → Real := fun omega => if omega ∈ A then 1 else 0
  let B : PredictableElementaryInterval F :=
    { interval :=
        { coefficient := coefficient
          startTime := fun _ => i
          stopTime := fun _ => max i T
          start_le_stop := fun _ => le_max_left _ _ }
      startStopping := isStoppingTime_const F i
      stopStopping := isStoppingTime_const F (max i T)
      coefficient_measurable := by
        rw [IsStoppingTime.measurableSpace_const]
        change Measurable[F i]
          (fun omega => if omega ∈ A then (1 : Real) else 0)
        exact Measurable.ite hA measurable_const measurable_const }
  refine
    { strategy := [B]
      bound := 1
      coefficientAbsSum_le := ?_
      integrand_eq := ?_ }
  · intro omega
    simp only [PredictableElementaryStrategy.coefficientAbsSum, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, B, coefficient]
    split_ifs <;> simp
  · funext t omega
    simp only [PredictableElementaryStrategy.integrand, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      PredictableElementaryInterval.integrand, B, coefficient]
    by_cases hiT : i ≤ T
    · rw [max_eq_right hiT]
      by_cases hAomega : omega ∈ A
      · by_cases hActive : i < t ∧ t ≤ T
        · have htPos : 0 < t := bot_le.trans_lt hActive.1
          simp [indicatorProcess, horizonCarrier, hAomega, hActive, htPos]
        · have hNotRight : ¬(i < t ∧ 0 < t ∧ t ≤ T) := fun h =>
            hActive ⟨h.1, h.2.2⟩
          simp [indicatorProcess, horizonCarrier, hAomega, hActive, hNotRight]
      · simp [indicatorProcess, horizonCarrier, hAomega]
    · have hTi : T ≤ i := le_of_not_ge hiT
      rw [max_eq_left hTi]
      have hNotLeft : ¬(i < t ∧ t ≤ i) := fun h =>
        (not_lt_of_ge h.2) h.1
      have hNotRight : ¬(i < t ∧ 0 < t ∧ t ≤ T) := fun h =>
        (not_lt_of_ge (h.2.2.trans hTi)) h.1
      by_cases hAomega : omega ∈ A <;>
        simp [indicatorProcess, horizonCarrier, hAomega, hNotLeft, hNotRight]

end BoundedIndicatorRepresentation

/-- The predictable sets whose positive finite-horizon parts have bounded
elementary indicator representations. -/
def sets (T : NNReal) : Set (Set (NNReal × Omega)) :=
  {s | MeasurableSet[F.predictable] s /\
    Nonempty (BoundedIndicatorRepresentation (F := F) T s)}

/-- The elementary predictable indicator sets form a ring. -/
theorem isSetRing_sets (T : NNReal) : IsSetRing (sets (F := F) T) where
  empty_mem := by
    refine ⟨?_, ⟨BoundedIndicatorRepresentation.empty (F := F) T⟩⟩
    exact @MeasurableSet.empty _ F.predictable
  union_mem := by
    rintro s u ⟨hsMeas, ⟨hs⟩⟩ ⟨huMeas, ⟨hu⟩⟩
    exact ⟨hsMeas.union huMeas,
      ⟨BoundedIndicatorRepresentation.union hs hu⟩⟩
  sdiff_mem := by
    rintro s u ⟨hsMeas, ⟨hs⟩⟩ ⟨huMeas, ⟨hu⟩⟩
    exact ⟨hsMeas.diff huMeas,
      ⟨BoundedIndicatorRepresentation.sdiff hs hu⟩⟩

/-- Every time-zero predictable generator belongs to the ring because its
intersection with the positive horizon is empty. -/
theorem singleton_zero_prod_mem_sets
    (T : NNReal) {A : Set Omega} (hA : MeasurableSet[F 0] A) :
    ({0} ×ˢ A : Set (NNReal × Omega)) ∈ sets (F := F) T := by
  refine ⟨measurableSet_predictable_singleton_bot_prod hA, ?_⟩
  let hEmpty := BoundedIndicatorRepresentation.empty (F := F) T
  refine ⟨{ hEmpty with integrand_eq := ?_ }⟩
  have hInter :
      ({0} ×ˢ A : Set (NNReal × Omega)) ∩ horizonCarrier T = ∅ := by
    ext p
    simp only [horizonCarrier, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_Ioc, Set.mem_univ, and_true,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hpZero, -⟩, hpPos, -⟩
    rw [hpZero] at hpPos
    exact (lt_irrefl 0 hpPos).elim
  simpa [hInter] using hEmpty.integrand_eq

/-- Every positive-time generator of the predictable sigma algebra belongs
to the elementary indicator ring. -/
theorem Ioi_prod_mem_sets
    (T i : NNReal) {A : Set Omega} (hA : MeasurableSet[F i] A) :
    (Ioi i ×ˢ A : Set (NNReal × Omega)) ∈ sets (F := F) T :=
  ⟨measurableSet_predictable_Ioi_prod hA,
    ⟨BoundedIndicatorRepresentation.generator T i A hA⟩⟩

/-- The elementary indicator ring generates exactly the predictable sigma
algebra. -/
theorem generateFrom_sets (T : NNReal) :
    MeasurableSpace.generateFrom (sets (F := F) T) = F.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  · unfold Filtration.predictable
    apply MeasurableSpace.generateFrom_mono
    rintro s (hs | hs)
    · obtain ⟨A, hA, rfl⟩ := hs
      exact singleton_zero_prod_mem_sets T hA
    · obtain ⟨i, A, hA, rfl⟩ := hs
      exact Ioi_prod_mem_sets T i hA

end FiniteHorizonPredictableIndicatorRing

end FTAPTheorem42
