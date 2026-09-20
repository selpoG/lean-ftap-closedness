import FTAPTheorem42.Stochastic.Decomposition.Source.CenteredSpecialDecompositionUniqueness

/-! # Normalized passage decompositions of general good integrators -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal

namespace FTAPTheorem42

open FiniteLargeJumpProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F] {X : Process Ω}

/-- The previously constructed source decompositions are centered and
restopped at their own finite passage time, supplying global FV and exact
zero initial values for both components. -/
noncomputable def goodIntegratorCenteredPassageDecomposition
    (hUsual : Filtration.UsualConditions μ F) (hX : IsSemimartingale X F μ)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    (c : Real) (hc : 0 < c) (n : Nat) :
    CenteredGlobalSpecialDecomposition
      (stoppedProcess (globalSmallJumpResidual X c)
        (fun w => (cadlagAbsolutePassageLocalizerFinite
          (globalSmallJumpResidual X c) n w : WithTop NNReal))) F μ := by
  let := hUsual.rightContinuous
  let Y := globalSmallJumpResidual X c
  let D := Classical.choice
    (exists_goodIntegratorSmallJumpPassage_decomposition
      hUsual hX hAdapted hRight hLeft hZero c hc n)
  have hY0 : Y 0 = 0 := by
    funext w
    change X 0 w - globalProcess X c 0 w = 0
    rw [hZero, globalProcess_zero hRight hLeft hc]
    exact sub_self _
  have hS0 : (stoppedProcess Y (cadlagAbsolutePassageLocalizer Y n)) 0 = 0 := by
    funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ _ from bot_le)]
    exact congrFun hY0 w
  have hLoc : IsLocalizingSequence F (cadlagAbsolutePassageLocalizer Y) μ :=
    cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (hAdapted.sub (globalProcess_stronglyAdapted hAdapted hRight hLeft hc))
      (fun w t => (hRight w t).sub (globalProcess_rightContinuous hRight hLeft hc w t))
      (hLeft.sub (globalProcess_hasLeftLimits hRight hLeft hc))
  have hτ : IsStoppingTime F
      (fun w => (cadlagAbsolutePassageLocalizerFinite Y n w : WithTop NNReal)) := by
    simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using hLoc.isStoppingTime n
  have E := D.centeredStopped hS0 (cadlagAbsolutePassageLocalizerFinite Y n) hτ
  simpa only [Y, coe_cadlagAbsolutePassageLocalizerFinite, stoppedProcess_stoppedProcess,
    inf_idem] using E

/-- The constructed coordinates, rather than unspecified candidate
decompositions, satisfy the common-stop compatibility needed for gluing. -/
theorem goodIntegratorCenteredPassageDecomposition_overlap
    (hUsual : Filtration.UsualConditions μ F) (hX : IsSemimartingale X F μ)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    (c : Real) (hc : 0 < c) :
    let D := goodIntegratorCenteredPassageDecomposition hUsual hX hAdapted hRight hLeft hZero c hc
    let τ := cadlagAbsolutePassageLocalizer (globalSmallJumpResidual X c)
    ∀ n m, ProcessIndistinguishable μ
        (stoppedProcess (D n).N (min (τ n) (τ m)))
        (stoppedProcess (D m).N (min (τ n) (τ m))) ∧
      ProcessIndistinguishable μ
        (stoppedProcess (D n).A (min (τ n) (τ m)))
        (stoppedProcess (D m).A (min (τ n) (τ m))) := by
  let := hUsual.rightContinuous
  let Y := globalSmallJumpResidual X c
  have hLoc : IsLocalizingSequence F (cadlagAbsolutePassageLocalizer Y) μ :=
    cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (hAdapted.sub (globalProcess_stronglyAdapted hAdapted hRight hLeft hc))
      (fun w t => (hRight w t).sub (globalProcess_rightContinuous hRight hLeft hc w t))
      (hLeft.sub (globalProcess_hasLeftLimits hRight hLeft hc))
  have hτ n : IsStoppingTime F
      (fun w => (cadlagAbsolutePassageLocalizerFinite Y n w : WithTop NNReal)) := by
    simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using hLoc.isStoppingTime n
  intro D τ n m
  have h := CenteredGlobalSpecialDecomposition.overlap hUsual
      (cadlagAbsolutePassageLocalizerFinite Y n) (cadlagAbsolutePassageLocalizerFinite Y m)
      (hτ n) (hτ m) (D n) (D m)
  have hρ : (fun w => min (cadlagAbsolutePassageLocalizerFinite Y n w : WithTop NNReal)
      (cadlagAbsolutePassageLocalizerFinite Y m w)) = min (τ n) (τ m) := by
    funext w
    simp only [coe_cadlagAbsolutePassageLocalizerFinite, Pi.inf_apply]
    rfl
  dsimp only at h
  rw [hρ] at h
  exact h

end FTAPTheorem42
