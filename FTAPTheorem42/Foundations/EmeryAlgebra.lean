/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Emery

/-! # Elementary gain identities for the capped test error -/

namespace FTAPTheorem42
open MeasureTheory Set
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}

theorem elementaryEmeryTestError_sub_zero (X Y : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    elementaryEmeryTestError (X - Y) 0 J T = elementaryEmeryTestError X Y J T := by
  unfold elementaryEmeryTestError
  congr 1
  have hZeroGain : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  simp only [hZeroGain, Pi.zero_apply, sub_zero]
  funext t ω
  have hSub (H : ElementaryStrategy Ω NNReal) :
      ElementaryStrategy.gain (X - Y) H t ω =
        ElementaryStrategy.gain X H t ω - ElementaryStrategy.gain Y H t ω := by
    induction H with
    | nil => simp [ElementaryStrategy.gain]
    | cons B H ih =>
      change B.gain (X - Y) t ω + ElementaryStrategy.gain (X - Y) H t ω =
        (B.gain X t ω + ElementaryStrategy.gain X H t ω) -
          (B.gain Y t ω + ElementaryStrategy.gain Y H t ω)
      rw [ih]
      simp only [ElementaryInterval.gain, Pi.sub_apply]
      ring
  exact hSub J.strategy.toElementary

theorem elementaryEmeryTestError_zero_horizon (X Y : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (ω : Ω) :
    elementaryEmeryTestError X Y J 0 ω = 0 := by
  rw [elementaryEmeryTestError_congr_upto (X' := fun _ => X 0) (Y' := fun _ => Y 0)
    J 0 ω (fun t ht => by rw [le_antisymm ht bot_le])
    (fun t ht => by rw [le_antisymm ht bot_le])]
  have hConst (f : Ω → Real) :
      ElementaryStrategy.gain (fun _ => f) J.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  simp only [elementaryEmeryTestError, hConst, Pi.zero_apply, sub_self]
  simp [FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope,
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope,
    FactorialChronologicalGrid.factorialRunningMax,
    finiteRunningMax, ChronologicalGrid.natSample]

end FTAPTheorem42
