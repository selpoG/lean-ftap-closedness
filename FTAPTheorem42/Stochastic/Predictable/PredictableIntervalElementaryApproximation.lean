/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalAlgebraDensity
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Elementary approximation of foretold stochastic intervals

The predictable interval algebra uses half-open intervals `[R,S)`, while an
actual elementary buy-and-hold block has integrand `1_(tau,sigma]`.  If
`R_n ↑ R` and `S_n ↑ S` are foretelling sequences, the actual blocks
`(R_n,S_n]` eventually agree pointwise with `[R,S)` away from time zero.

This module makes that endpoint conversion concrete.  It also records the
necessary time-zero qualification: no elementary block is active at time
zero, so approximation in a control measure is asserted only when that
measure gives the time-zero slice mass zero.
-/

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal symmDiff

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega)}

namespace StoppingTimeForetelling

/-- Every member of a foretelling sequence is finite, even when the target
time is infinite. -/
theorem time_ne_top
    {tau : Omega → WithTop ℝ≥0}
    (a : StoppingTimeForetelling F tau) (n : ℕ) (omega : Omega) :
    a.time n omega ≠ ⊤ := by
  by_cases hzero : tau omega = 0
  · have htime : a.time n omega = 0 :=
      bot_unique ((a.le n omega).trans_eq hzero)
    rw [htime]
    exact WithTop.zero_ne_top
  · exact ne_top_of_lt (a.lt_of_ne_zero n omega hzero)

/-- The finite stopping time represented by one member of a foretelling
sequence. -/
noncomputable def finiteTime
    {tau : Omega → WithTop ℝ≥0}
    (a : StoppingTimeForetelling F tau) (n : ℕ) : Omega → ℝ≥0 :=
  fun omega => (a.time n omega).untop (a.time_ne_top n omega)

@[simp]
theorem coe_finiteTime
    {tau : Omega → WithTop ℝ≥0}
    (a : StoppingTimeForetelling F tau) (n : ℕ) (omega : Omega) :
    (a.finiteTime n omega : WithTop ℝ≥0) = a.time n omega :=
  WithTop.coe_untop _ (a.time_ne_top n omega)

/-- A finite foretelling approximant remains a stopping time after removing
the `WithTop` wrapper. -/
theorem finiteTime_isStoppingTime
    {tau : Omega → WithTop ℝ≥0}
    (a : StoppingTimeForetelling F tau) (n : ℕ) :
    IsStoppingTime F (fun omega =>
      (a.finiteTime n omega : WithTop ℝ≥0)) := by
  simpa only [a.coe_finiteTime] using a.isStoppingTime n

end StoppingTimeForetelling

namespace PredictableIntervalAlgebra.Interval

attribute [local instance] Classical.propDecidable

/-- The active set of the `n`-th actual elementary approximation of a
foretold interval.  The maximum makes the endpoints ordered even when the
raw interval is empty on part of the sample space. -/
def elementaryApproximationCarrier
    (I : PredictableIntervalAlgebra.Interval F) (n : ℕ) :
    Set (ℝ≥0 × Omega) :=
  {p | I.left_foretelling.finiteTime n p.2 < p.1 ∧
    p.1 ≤ max (I.left_foretelling.finiteTime n p.2)
      (I.right_foretelling.finiteTime n p.2)}

private theorem approximating_left_lt
    (I : PredictableIntervalAlgebra.Interval F)
    {t : ℝ≥0} (ht : t ≠ 0) (omega : Omega)
    (hleft : I.left omega ≤ (t : WithTop ℝ≥0)) (n : ℕ) :
    I.left_foretelling.finiteTime n omega < t := by
  apply WithTop.coe_lt_coe.mp
  rw [I.left_foretelling.coe_finiteTime]
  by_cases hzero : I.left omega = 0
  · have htime : I.left_foretelling.time n omega = 0 :=
      bot_unique ((I.left_foretelling.le n omega).trans_eq hzero)
    rw [htime]
    exact WithTop.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  · exact (I.left_foretelling.lt_of_ne_zero n omega hzero).trans_le hleft

private theorem approximating_time_lt
    {tau : Omega → WithTop ℝ≥0}
    (a : StoppingTimeForetelling F tau)
    {t : ℝ≥0} (ht : t ≠ 0) (omega : Omega)
    (htau : tau omega ≤ (t : WithTop ℝ≥0)) (n : ℕ) :
    a.finiteTime n omega < t := by
  apply WithTop.coe_lt_coe.mp
  rw [a.coe_finiteTime]
  by_cases hzero : tau omega = 0
  · have htime : a.time n omega = 0 :=
      bot_unique ((a.le n omega).trans_eq hzero)
    rw [htime]
    exact WithTop.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  · exact (a.lt_of_ne_zero n omega hzero).trans_le htau

/-- Away from time zero, the elementary approximating carriers eventually
agree pointwise with their foretold interval. -/
theorem eventually_mem_elementaryApproximationCarrier_iff
    (I : PredictableIntervalAlgebra.Interval F)
    {t : ℝ≥0} (ht : t ≠ 0) (omega : Omega) :
    ∀ᶠ n in atTop,
      (t, omega) ∈ I.elementaryApproximationCarrier n ↔
        (t, omega) ∈ I.carrier := by
  rw [I.mem_carrier_iff]
  by_cases htarget :
      I.left omega ≤ (t : WithTop ℝ≥0) ∧
        (t : WithTop ℝ≥0) < I.right omega
  · have hRightEventually : ∀ᶠ n in atTop,
        (t : WithTop ℝ≥0) < I.right_foretelling.time n omega :=
      (I.right_foretelling.tendsto omega).eventually
        (Ioi_mem_nhds htarget.2)
    filter_upwards [hRightEventually] with n hright
    change
      (I.left_foretelling.finiteTime n omega < t ∧
          t ≤ max (I.left_foretelling.finiteTime n omega)
            (I.right_foretelling.finiteTime n omega)) ↔ _
    constructor
    · intro _
      exact htarget
    · intro _
      refine ⟨approximating_left_lt I ht omega htarget.1 n, ?_⟩
      apply WithTop.coe_le_coe.mp
      rw [WithTop.coe_max, I.right_foretelling.coe_finiteTime]
      exact hright.le.trans (le_max_right _ _)
  · by_cases hleft : (t : WithTop ℝ≥0) < I.left omega
    · have hLeftEventually : ∀ᶠ n in atTop,
          (t : WithTop ℝ≥0) < I.left_foretelling.time n omega :=
        (I.left_foretelling.tendsto omega).eventually
          (Ioi_mem_nhds hleft)
      filter_upwards [hLeftEventually] with n hleftApprox
      change
        (I.left_foretelling.finiteTime n omega < t ∧
            t ≤ max (I.left_foretelling.finiteTime n omega)
              (I.right_foretelling.finiteTime n omega)) ↔ _
      constructor
      · intro hactive
        have hactiveLeft :
            (I.left_foretelling.time n omega) <
              (t : WithTop ℝ≥0) := by
          rw [← I.left_foretelling.coe_finiteTime]
          exact WithTop.coe_lt_coe.mpr hactive.1
        exact (lt_asymm hleftApprox hactiveLeft).elim
      · intro hcarrier
        exact (htarget hcarrier).elim
    · have hleftLe : I.left omega ≤ (t : WithTop ℝ≥0) :=
        le_of_not_gt hleft
      have hright : I.right omega ≤ (t : WithTop ℝ≥0) := by
        exact le_of_not_gt fun hright => htarget ⟨hleftLe, hright⟩
      apply Eventually.of_forall
      intro n
      change
        (I.left_foretelling.finiteTime n omega < t ∧
            t ≤ max (I.left_foretelling.finiteTime n omega)
              (I.right_foretelling.finiteTime n omega)) ↔ _
      constructor
      · intro hactive
        have hLeftApprox := approximating_left_lt I ht omega hleftLe n
        have hRightApprox := approximating_time_lt
          I.right_foretelling ht omega hright n
        exact ((not_le_of_gt (max_lt hLeftApprox hRightApprox)) hactive.2).elim
      · intro hcarrier
        exact (htarget hcarrier).elim

/-- The only endpoint obstruction to elementary approximation is the
time-zero slice. -/
def timeZeroSlice : Set (ℝ≥0 × Omega) :=
  ({0} : Set ℝ≥0) ×ˢ (Set.univ : Set Omega)

/-- The time-zero slice is a predictable set. -/
theorem measurableSet_timeZeroSlice :
    MeasurableSet[F.predictable]
      (timeZeroSlice : Set (ℝ≥0 × Omega)) := by
  unfold timeZeroSlice
  exact measurableSet_predictable_singleton_bot_prod MeasurableSet.univ

omit [MeasurableSpace Omega] in
theorem mem_timeZeroSlice_iff (p : ℝ≥0 × Omega) :
    p ∈ timeZeroSlice ↔ p.1 = 0 := by
  simp [timeZeroSlice]

end PredictableIntervalAlgebra.Interval

end FTAPTheorem42
