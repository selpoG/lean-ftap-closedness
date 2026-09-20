/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.StoppedGoodIntegrator
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSpecialDecomposition
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.GlobalLargeJumpProcess

/-! # Bounded-jump good integrators supply bounded stopped decomposition sources -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] {X : Process Ω}

/-- The jump bound controls the overshoot at the closed passage time.
All source fields, including the elementary good-integrator property,
are supplied before applying the existing bounded-source decomposition. -/
noncomputable def goodIntegratorPassageSource
    (hUsual : Filtration.UsualConditions mu F) (hX : IsSemimartingale X F mu)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    (c : Real) (hc : 0 ≤ c) (hJump : ∀ᵐ w ∂mu, ∀ t, |processLeftJump X t w| ≤ c)
    (n : Nat) : BoundedSemimartingaleSource
      (stoppedProcess X (cadlagAbsolutePassageLocalizer X n)) F mu := by
  let := hUsual.rightContinuous
  have hLocal : IsLocalizingSequence F (cadlagAbsolutePassageLocalizer X) mu :=
    cadlagAbsolutePassageLocalizer_isLocalizingSequence hAdapted hRight hLeft
  have hτ : IsStoppingTime F (fun w =>
      (cadlagAbsolutePassageLocalizerFinite X n w : WithTop NNReal)) := by
    simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using hLocal.isStoppingTime n
  refine {
    usualConditions := hUsual
    stronglyAdapted :=
      RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        hAdapted (hLocal.isStoppingTime n) hRight
    rightContinuous := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hRight
    hasLeftLimits := hLeft.stoppedProcess _
    bound := cadlagPassageLevel n + c
    uniformBound := ?_
    isSemimartingale := ?_ }
  · filter_upwards [hJump] with w hw
    apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting X hLeft
      (cadlagPassageLevel n) c hc w
      (by simpa only [hZero, Pi.zero_apply, abs_zero] using cadlagPassageLevel_nonnegative n)
      (cadlagAbsolutePassageLocalizer X n) (min_le_left _ _) hw
  · simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using
      hX.stoppedProcess_coe (cadlagAbsolutePassageLocalizerFinite X n) hτ

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Large-jump removal supplies bounded-jump good-integrator sources -/

open Filter MeasureTheory Set Topology
open scoped NNReal

open FiniteLargeJumpProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {X : Process Ω}

/-- The all-time adapted FV jump sum can be subtracted without a
compensator. This supplies the good-integrator property of the residual. -/
theorem globalSmallJumpResidual_isSemimartingale [F.IsRightContinuous]
    (hX : IsSemimartingale X F μ) (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) {c : Real} (hc : 0 < c) :
    IsSemimartingale (globalSmallJumpResidual X c) F μ :=
  hX.sub (isSemimartingale_of_locallyBoundedVariation (globalProcess X c)
    (globalProcess_stronglyAdapted hAdapted hRight hLeft hc)
    (globalProcess_rightContinuous hRight hLeft hc)
    (globalProcess_locallyBoundedVariation hRight hLeft hc))

/-- Every regular zero-initial good integrator now supplies the bounded
closed-stop source after removal of its large jumps, with no residual
good-integrator or jump-bound premise left to supply. -/
noncomputable def goodIntegratorSmallJumpPassageSource
    (hUsual : Filtration.UsualConditions μ F) (hX : IsSemimartingale X F μ)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    (c : Real) (hc : 0 < c) (n : Nat) : BoundedSemimartingaleSource
      (stoppedProcess (globalSmallJumpResidual X c)
        (cadlagAbsolutePassageLocalizer (globalSmallJumpResidual X c) n)) F μ := by
  let := hUsual.rightContinuous
  apply goodIntegratorPassageSource hUsual
    (globalSmallJumpResidual_isSemimartingale hX hAdapted hRight hLeft hc)
    (hAdapted.sub (globalProcess_stronglyAdapted hAdapted hRight hLeft hc))
    (fun w t => (hRight w t).sub (globalProcess_rightContinuous hRight hLeft hc w t))
    (hLeft.sub (globalProcess_hasLeftLimits hRight hLeft hc))
    ?_ c hc.le
    (Eventually.of_forall fun w t => globalSmallJumpResidual_jump_le hRight hLeft hc t w) n
  funext w
  change X 0 w - globalProcess X c 0 w = 0
  rw [hZero, globalProcess_zero hRight hLeft hc]
  exact sub_self _

/-- Consume the constructed source in the existing rich bounded-source
decomposition theorem. Centered overlap and unstopped gluing remain separate. -/
theorem exists_goodIntegratorSmallJumpPassage_decomposition
    (hUsual : Filtration.UsualConditions μ F) (hX : IsSemimartingale X F μ)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0)
    (c : Real) (hc : 0 < c) (n : Nat) :
    Nonempty (HorizonFactorialGrid.BoundedSemimartingaleGlobalSpecialDecompositionData
      (goodIntegratorSmallJumpPassageSource hUsual hX hAdapted hRight hLeft hZero c hc n)) :=
  HorizonFactorialGrid.exists_boundedSemimartingaleSource_globalSpecialDecompositionData _

end FTAPTheorem42
