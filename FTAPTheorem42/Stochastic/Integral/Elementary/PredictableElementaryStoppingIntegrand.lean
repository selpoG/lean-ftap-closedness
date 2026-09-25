/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct

/-!
# Integrands of stopped predictable elementary strategies

The algebraic stopping operation on a predictable elementary strategy is the
original strategy minus its post-stopping tail.  This module records the
corresponding pointwise restriction of its integrand and a coefficient bound
which is uniform in the stopping time.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

namespace PredictableElementaryInterval

attribute [local instance] Classical.propDecidable

/-- The post-stopping tail of one elementary block is its original integrand
on the strict post-stopping interval. -/
theorem after_integrand_apply
    (B : PredictableElementaryInterval F)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (t : NNReal) (omega : Omega) :
    (B.after tau hTau).integrand t omega =
      if tau omega < t then B.integrand t omega else 0 := by
  unfold PredictableElementaryInterval.integrand
  by_cases hNew : (B.after tau hTau).interval.startTime omega < t ∧
      t <= (B.after tau hTau).interval.stopTime omega
  · rw [ite_eq_left hNew]
    have hNew' : max (B.interval.startTime omega) (tau omega) < t ∧
        t <= max (B.interval.stopTime omega) (tau omega) := by
      simpa only [after, ElementaryInterval.after] using hNew
    have hTauT : tau omega < t := (le_max_right _ _).trans_lt hNew'.1
    have hStart : B.interval.startTime omega < t :=
      (le_max_left _ _).trans_lt hNew'.1
    have hStop : t <= B.interval.stopTime omega := by
      by_cases hOrder : tau omega <= B.interval.stopTime omega
      · simpa [max_eq_left hOrder] using hNew'.2
      · have hReverse : B.interval.stopTime omega <= tau omega :=
          le_of_not_ge hOrder
        rw [max_eq_right hReverse] at hNew'
        exact False.elim ((not_le_of_gt hTauT) hNew'.2)
    rw [ite_eq_left hTauT, ite_eq_left ⟨hStart, hStop⟩]
    rfl
  · rw [ite_eq_right hNew]
    by_cases hTauT : tau omega < t
    · rw [ite_eq_left hTauT]
      apply Eq.symm
      apply ite_eq_right
      rintro hActive
      apply hNew
      have hStart : max (B.interval.startTime omega) (tau omega) < t :=
        max_lt hActive.1 hTauT
      have hStop : t <= max (B.interval.stopTime omega) (tau omega) :=
        hActive.2.trans (le_max_left _ _)
      simpa only [after, ElementaryInterval.after] using And.intro hStart hStop
    · rw [ite_eq_right hTauT]

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

attribute [local instance] Classical.propDecidable

/-- Retaining the post-stopping tail preserves the sum of absolute block
coefficients. -/
theorem coefficientAbsSum_after
    (H : PredictableElementaryStrategy F)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (omega : Omega) :
    (PredictableElementaryStrategy.after H tau hTau).coefficientAbsSum omega =
      PredictableElementaryStrategy.coefficientAbsSum H omega := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      simp only [after, List.map_cons]
      change |(B.after tau hTau).interval.coefficient omega| +
        coefficientAbsSum (H.map fun B => B.after tau hTau) omega =
          |B.interval.coefficient omega| + coefficientAbsSum H omega
      have ih' :
          coefficientAbsSum (H.map fun B => B.after tau hTau) omega =
            coefficientAbsSum H omega := by
        simpa only [after] using ih
      rw [ih']
      rfl

/-- The integrand of the retained post-stopping tail. -/
theorem after_integrand_apply
    (H : PredictableElementaryStrategy F)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (t : NNReal) (omega : Omega) :
    (PredictableElementaryStrategy.after H tau hTau).integrand t omega =
      if tau omega < t then
        PredictableElementaryStrategy.integrand H t omega else 0 := by
  induction H with
  | nil => simp [after, PredictableElementaryStrategy.integrand]
  | cons B H ih =>
      change (B.after tau hTau).integrand t omega +
          (PredictableElementaryStrategy.after H tau hTau).integrand t omega =
        if tau omega < t then
          B.integrand t omega +
            PredictableElementaryStrategy.integrand H t omega else 0
      rw [PredictableElementaryInterval.after_integrand_apply, ih]
      split_ifs <;> ring

/-- Algebraic stopping increases the elementary coefficient bound by at
most a factor of two. -/
theorem coefficientAbsSum_stopAt
    (H : PredictableElementaryStrategy F)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (omega : Omega) :
    (PredictableElementaryStrategy.stopAt H tau hTau).coefficientAbsSum omega =
      2 * PredictableElementaryStrategy.coefficientAbsSum H omega := by
  rw [stopAt, coefficientAbsSum_append, coefficientAbsSum_neg,
    coefficientAbsSum_after]
  ring

/-- The integrand of the algebraically stopped elementary strategy is the
predictable restriction to `(0,tau]`. -/
theorem stopAt_integrand_apply
    (H : PredictableElementaryStrategy F)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (t : NNReal) (omega : Omega) :
    (PredictableElementaryStrategy.stopAt H tau hTau).integrand t omega =
      if 0 < t ∧ t <= tau omega then
        PredictableElementaryStrategy.integrand H t omega else 0 := by
  rw [stopAt, append_integrand, neg_integrand]
  change PredictableElementaryStrategy.integrand H t omega -
      (PredictableElementaryStrategy.after H tau hTau).integrand t omega = _
  rw [after_integrand_apply]
  by_cases hPos : 0 < t
  · by_cases hLe : t <= tau omega
    · simp [hPos, hLe, not_lt.mpr hLe]
    · have hLt : tau omega < t := lt_of_not_ge hLe
      simp [hPos, hLe, hLt]
  · have htZero : t = 0 := le_antisymm (not_lt.mp hPos) bot_le
    subst t
    have hHZero : PredictableElementaryStrategy.integrand H 0 omega = 0 := by
      induction H with
      | nil => rfl
      | cons B H ih =>
          simp only [PredictableElementaryStrategy.integrand, List.map_cons,
            List.sum_cons, Pi.add_apply, PredictableElementaryInterval.integrand]
          have hNot : ¬B.interval.startTime omega < 0 := not_lt.mpr bot_le
          change (if B.interval.startTime omega < 0 ∧
              0 <= B.interval.stopTime omega then
                B.interval.coefficient omega else 0) +
              PredictableElementaryStrategy.integrand H 0 omega = 0
          rw [ite_eq_right (fun h => hNot h.1), ih, zero_add]
    simp [hHZero]

end PredictableElementaryStrategy

end FTAPTheorem42
