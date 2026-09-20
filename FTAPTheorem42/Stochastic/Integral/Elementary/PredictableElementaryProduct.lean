/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand

/-!
# Absolute coefficient sums of predictable elementary strategies

The pathwise sum of the absolute block coefficients is the deterministic
bookkeeping quantity used to control elementary gains.  It is defined here,
before any particular approximation construction, so density theorems can
retain this stronger bound rather than only a bound on the summed integrand.
-/

namespace FTAPTheorem42

open MeasureTheory
open scoped NNReal

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryStrategy

/-- Pathwise sum of the absolute block coefficients of an elementary
strategy.  Unlike the value of the summed integrand, this controls the
telescoping representation block by block. -/
noncomputable def coefficientAbsSum
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (omega : Omega) : Real :=
  (H.map fun B => |B.interval.coefficient omega|).sum

theorem coefficientAbsSum_nonneg
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (omega : Omega) :
    0 ≤ H.coefficientAbsSum omega := by
  induction H with
  | nil => simp [coefficientAbsSum]
  | cons B H ih => exact add_nonneg (abs_nonneg _) ih

/-- Positive scalar multiplication scales the coefficient sum by that scalar. -/
theorem coefficientAbsSum_posSMul
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (c : ℝ) (hc : 0 < c)
    (H : PredictableElementaryStrategy F) (omega : Omega) :
    coefficientAbsSum (H.posSMul c hc) omega =
      c * coefficientAbsSum H omega := by
  induction H with
  | nil =>
      simp [PredictableElementaryStrategy.posSMul,
        PredictableElementaryStrategy.coefficientAbsSum]
  | cons B H ih =>
      change |c * B.interval.coefficient omega| +
          coefficientAbsSum (PredictableElementaryStrategy.posSMul c hc H) omega =
        c * (|B.interval.coefficient omega| + coefficientAbsSum H omega)
      rw [ih, abs_mul, abs_of_pos hc]
      ring

/-- The absolute value of an elementary integrand is bounded by the sum of
the absolute block coefficients on the same path. -/
theorem abs_integrand_le_coefficientAbsSum
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (t : NNReal) (omega : Omega) :
    |H.integrand t omega| ≤ H.coefficientAbsSum omega := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.integrand, coefficientAbsSum]
  | cons B H ih =>
      change |B.integrand t omega +
          PredictableElementaryStrategy.integrand H t omega| ≤
        |B.interval.coefficient omega| + coefficientAbsSum H omega
      calc
        |B.integrand t omega +
            PredictableElementaryStrategy.integrand H t omega| ≤
            |B.integrand t omega| +
              |PredictableElementaryStrategy.integrand H t omega| :=
          abs_add_le _ _
        _ ≤ |B.interval.coefficient omega| +
            coefficientAbsSum H omega := by
          apply add_le_add _ ih
          rw [PredictableElementaryInterval.integrand]
          split_ifs <;> simp

end PredictableElementaryStrategy

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Products of predictable elementary integrands

The intersection of two predictable elementary stochastic intervals is
again represented by a predictable elementary interval.  Distributing this
construction over finite lists realizes the pointwise product of two
elementary integrands.  The blockwise coefficient bound is multiplicative;
this is the closure needed to build an algebra of elementary predictable
indicator sets for the finite-horizon martingale energy content.
-/

open MeasureTheory
open scoped NNReal

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

namespace PredictableElementaryInterval

/-- A predictable block representing the pointwise product of two block
integrands.  The upper endpoint is raised to the new lower endpoint when the
two active intervals do not overlap. -/
noncomputable def mul
    (B C : PredictableElementaryInterval F) :
    PredictableElementaryInterval F := by
  let start : Omega -> NNReal := fun omega =>
    max (B.interval.startTime omega) (C.interval.startTime omega)
  let rawStop : Omega -> NNReal := fun omega =>
    min (B.interval.stopTime omega) (C.interval.stopTime omega)
  let stop : Omega -> NNReal := fun omega => max (start omega) (rawStop omega)
  let hStart : IsStoppingTime F (fun omega => (start omega : WithTop NNReal)) := by
    simpa only [start, WithTop.coe_max] using B.startStopping.max C.startStopping
  let hRawStop : IsStoppingTime F
      (fun omega => (rawStop omega : WithTop NNReal)) := by
    simpa only [rawStop, WithTop.coe_min] using B.stopStopping.min C.stopStopping
  let hStop : IsStoppingTime F (fun omega => (stop omega : WithTop NNReal)) := by
    simpa only [stop, WithTop.coe_max] using hStart.max hRawStop
  refine
    { interval :=
        { coefficient := fun omega =>
            B.interval.coefficient omega * C.interval.coefficient omega
          startTime := start
          stopTime := stop
          start_le_stop := fun omega => le_max_left _ _ }
      startStopping := hStart
      stopStopping := hStop
      coefficient_measurable := ?_ }
  have hBLe :
      (fun omega => (B.interval.startTime omega : WithTop NNReal)) <=
        fun omega => (start omega : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr (le_max_left _ _)
  have hCLe :
      (fun omega => (C.interval.startTime omega : WithTop NNReal)) <=
        fun omega => (start omega : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr (le_max_right _ _)
  exact
    (B.coefficient_measurable.mono
      (B.startStopping.measurableSpace_mono hStart hBLe) le_rfl).mul
      (C.coefficient_measurable.mono
        (C.startStopping.measurableSpace_mono hStart hCLe) le_rfl)

/-- The block product represents the pointwise product of the two original
block integrands. -/
theorem mul_integrand
    (B C : PredictableElementaryInterval F) :
    (B.mul C).integrand = B.integrand * C.integrand := by
  funext t omega
  simp only [PredictableElementaryInterval.integrand, mul, Pi.mul_apply]
  by_cases hB : B.interval.startTime omega < t /\
      t <= B.interval.stopTime omega
  · by_cases hC : C.interval.startTime omega < t /\
        t <= C.interval.stopTime omega
    · have hStart :
          max (B.interval.startTime omega) (C.interval.startTime omega) < t :=
        max_lt hB.1 hC.1
      have hStop : t <= max
          (max (B.interval.startTime omega) (C.interval.startTime omega))
          (min (B.interval.stopTime omega) (C.interval.stopTime omega)) := by
        exact le_max_of_le_right (le_min hB.2 hC.2)
      simp [hB, hC, hStart, hStop]
    · have hProduct :
          B.interval.coefficient omega *
              (if C.interval.startTime omega < t /\
                  t <= C.interval.stopTime omega then
                C.interval.coefficient omega else 0) = 0 := by
        rw [ite_eq_right hC, mul_zero]
      rw [ite_eq_left hB, hProduct]
      apply ite_eq_right
      intro hActive
      apply hC
      constructor
      · exact (le_max_right _ _).trans_lt hActive.1
      · have hRaw :
            t <= min (B.interval.stopTime omega)
              (C.interval.stopTime omega) := by
          by_cases hOrder :
              max (B.interval.startTime omega) (C.interval.startTime omega) <=
                min (B.interval.stopTime omega) (C.interval.stopTime omega)
          · simpa [max_eq_right hOrder] using hActive.2
          · have hEq : max
                (max (B.interval.startTime omega) (C.interval.startTime omega))
                (min (B.interval.stopTime omega) (C.interval.stopTime omega)) =
                max (B.interval.startTime omega) (C.interval.startTime omega) :=
              max_eq_left (le_of_not_ge hOrder)
            have hLe := hActive.2
            rw [hEq] at hLe
            exact False.elim ((not_lt_of_ge hLe) hActive.1)
        exact hRaw.trans (min_le_right _ _)
  · rw [ite_eq_right hB, zero_mul]
    apply ite_eq_right
    intro hActive
    apply hB
    constructor
    · exact (le_max_left _ _).trans_lt hActive.1
    · have hRaw :
          t <= min (B.interval.stopTime omega)
            (C.interval.stopTime omega) := by
        by_cases hOrder :
            max (B.interval.startTime omega) (C.interval.startTime omega) <=
              min (B.interval.stopTime omega) (C.interval.stopTime omega)
        · simpa [max_eq_right hOrder] using hActive.2
        · have hEq : max
              (max (B.interval.startTime omega) (C.interval.startTime omega))
              (min (B.interval.stopTime omega) (C.interval.stopTime omega)) =
              max (B.interval.startTime omega) (C.interval.startTime omega) :=
            max_eq_left (le_of_not_ge hOrder)
          have hLe := hActive.2
          rw [hEq] at hLe
          exact False.elim ((not_lt_of_ge hLe) hActive.1)
      exact hRaw.trans (min_le_left _ _)

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

/-- Appending elementary blocks adds their represented integrands. -/
theorem append_integrand
    (H K : PredictableElementaryStrategy F) :
    (H ++ K).integrand = H.integrand + K.integrand := by
  funext t omega
  simp [PredictableElementaryStrategy.integrand]

/-- Negating all block coefficients negates the represented integrand. -/
theorem neg_integrand
    (H : PredictableElementaryStrategy F) :
    H.neg.integrand = -H.integrand := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.neg,
      PredictableElementaryStrategy.integrand]
  | cons B H ih =>
      funext t omega
      simp only [PredictableElementaryStrategy.neg, List.map_cons,
        PredictableElementaryStrategy.integrand, List.sum_cons,
        Pi.add_apply, Pi.neg_apply]
      have hBlock : B.neg.integrand t omega = -B.integrand t omega := by
        simp only [PredictableElementaryInterval.integrand,
          PredictableElementaryInterval.neg, ElementaryInterval.neg,
          ElementaryInterval.mulCoefficient]
        by_cases h :
            B.interval.startTime omega < t ∧
              t ≤ B.interval.stopTime omega <;> simp [h]
      have ihRaw :
          ((H.map PredictableElementaryInterval.neg).map
              PredictableElementaryInterval.integrand).sum t omega =
            -((H.map PredictableElementaryInterval.integrand).sum t omega) := by
        simpa only [PredictableElementaryStrategy.neg,
          PredictableElementaryStrategy.integrand, Pi.neg_apply] using
          congrFun (congrFun ih t) omega
      rw [hBlock, ihRaw]
      ring

/-- Absolute coefficient sums add under list append. -/
theorem coefficientAbsSum_append
    (H K : PredictableElementaryStrategy F) (omega : Omega) :
    (H ++ K).coefficientAbsSum omega =
      H.coefficientAbsSum omega + K.coefficientAbsSum omega := by
  simp [coefficientAbsSum]

/-- Negating all blocks preserves the absolute coefficient sum. -/
theorem coefficientAbsSum_neg
    (H : PredictableElementaryStrategy F) (omega : Omega) :
    H.neg.coefficientAbsSum omega = H.coefficientAbsSum omega := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.neg, coefficientAbsSum]
  | cons B H ih =>
      have ihRaw :
          ((H.map PredictableElementaryInterval.neg).map fun C =>
              |C.interval.coefficient omega|).sum =
            (H.map fun C => |C.interval.coefficient omega|).sum := by
        simpa only [PredictableElementaryStrategy.neg, coefficientAbsSum] using ih
      simp only [PredictableElementaryStrategy.neg, List.map_cons]
      unfold PredictableElementaryStrategy.coefficientAbsSum
      simp only [List.map_cons, List.sum_cons]
      rw [ihRaw]
      simp [PredictableElementaryInterval.neg, ElementaryInterval.neg,
        ElementaryInterval.mulCoefficient]

/-- Distribute block intersection over two finite elementary strategies. -/
noncomputable def mul
    (H K : PredictableElementaryStrategy F) : PredictableElementaryStrategy F :=
  H.flatMap fun B => K.map B.mul

private theorem map_mul_integrand_sum
    (B : PredictableElementaryInterval F)
    (K : PredictableElementaryStrategy F) (t : NNReal) (omega : Omega) :
    ((K.map B.mul).map PredictableElementaryInterval.integrand).sum t omega =
      B.integrand t omega *
        PredictableElementaryStrategy.integrand K t omega := by
  induction K with
  | nil => simp [PredictableElementaryStrategy.integrand]
  | cons C K ih =>
      simp only [List.map_cons, List.sum_cons,
        PredictableElementaryInterval.mul_integrand, Pi.add_apply,
        Pi.mul_apply, PredictableElementaryStrategy.integrand]
      change
        ((K.map B.mul).map PredictableElementaryInterval.integrand).sum t omega =
          B.integrand t omega *
            ((K.map PredictableElementaryInterval.integrand).sum t omega) at ih
      rw [ih]
      ring

private theorem map_mul_coefficientAbsSum
    (B : PredictableElementaryInterval F)
    (K : PredictableElementaryStrategy F) (omega : Omega) :
    ((K.map B.mul).map fun C => |C.interval.coefficient omega|).sum =
      |B.interval.coefficient omega| *
        PredictableElementaryStrategy.coefficientAbsSum K omega := by
  induction K with
  | nil => simp [PredictableElementaryStrategy.coefficientAbsSum]
  | cons C K ih =>
      change
        |B.interval.coefficient omega * C.interval.coefficient omega| +
            ((K.map B.mul).map fun D =>
              |D.interval.coefficient omega|).sum =
          |B.interval.coefficient omega| *
            (|C.interval.coefficient omega| +
              PredictableElementaryStrategy.coefficientAbsSum K omega)
      rw [abs_mul, ih]
      ring

/-- The distributed product strategy represents the pointwise product of
the summed elementary integrands. -/
theorem mul_integrand
    (H K : PredictableElementaryStrategy F) :
    (H.mul K).integrand = H.integrand * K.integrand := by
  induction H with
  | nil => simp [mul, PredictableElementaryStrategy.integrand]
  | cons B H ih =>
      funext t omega
      have ihApply :
          ((PredictableElementaryStrategy.mul H K).map
              PredictableElementaryInterval.integrand).sum t omega =
            PredictableElementaryStrategy.integrand H t omega *
              PredictableElementaryStrategy.integrand K t omega := by
        exact congrFun (congrFun ih t) omega
      have ihRaw :
          ((H.flatMap fun B => K.map B.mul).map
              PredictableElementaryInterval.integrand).sum t omega =
            PredictableElementaryStrategy.integrand H t omega *
              PredictableElementaryStrategy.integrand K t omega := by
        simpa only [mul] using ihApply
      simp only [mul, List.flatMap_cons,
        PredictableElementaryStrategy.integrand, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons, Pi.add_apply,
        Pi.mul_apply]
      rw [map_mul_integrand_sum, ihRaw]
      unfold PredictableElementaryStrategy.integrand
      ring

/-- The absolute block-coefficient sum of the distributed product is the
product of the two original sums. -/
theorem coefficientAbsSum_mul
    (H K : PredictableElementaryStrategy F) (omega : Omega) :
    (H.mul K).coefficientAbsSum omega =
      H.coefficientAbsSum omega * K.coefficientAbsSum omega := by
  induction H with
  | nil => simp [mul, coefficientAbsSum]
  | cons B H ih =>
      have ihApply :
          ((PredictableElementaryStrategy.mul H K).map fun C =>
              |C.interval.coefficient omega|).sum =
            PredictableElementaryStrategy.coefficientAbsSum H omega *
              PredictableElementaryStrategy.coefficientAbsSum K omega := ih
      have ihRaw :
          ((H.flatMap fun B => K.map B.mul).map fun C =>
              |C.interval.coefficient omega|).sum =
            PredictableElementaryStrategy.coefficientAbsSum H omega *
              PredictableElementaryStrategy.coefficientAbsSum K omega := by
        simpa only [mul] using ihApply
      simp only [mul, List.flatMap_cons, coefficientAbsSum,
        List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [map_mul_coefficientAbsSum, ihRaw]
      unfold PredictableElementaryStrategy.coefficientAbsSum
      ring

end PredictableElementaryStrategy

end FTAPTheorem42
