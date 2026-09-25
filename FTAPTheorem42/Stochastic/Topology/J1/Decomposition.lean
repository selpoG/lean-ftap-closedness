/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GoodIntegratorCenteredPassage
import FTAPTheorem42.Stochastic.Topology.J1.GeneralGoodIntegrator
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessLocalLimit

/-! # An adapted-FV decomposition of a regular good integrator

Remove large jumps, glue the normalized special decompositions of the
bounded-jump residual, and return the adapted jump sum to the FV component.
No special decomposition of the original good integrator is asserted.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal

open FiniteLargeJumpProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F] {X : Process Ω}

theorem exists_j1Decomposition_of_goodIntegrator_cadlag_zero
    (hUsual : Filtration.UsualConditions μ F) (hX : IsSemimartingale X F μ)
    (hAdapted : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hZero : X 0 = 0) :
    Nonempty (J1Decomposition X F μ) := by
  let := hUsual.rightContinuous
  let J := globalProcess X 1
  let Y := globalSmallJumpResidual X 1
  have hJA : StronglyAdapted F J := globalProcess_stronglyAdapted hAdapted hRight hLeft zero_lt_one
  have hJR := globalProcess_rightContinuous hRight hLeft zero_lt_one (c := 1)
  have hJL := globalProcess_hasLeftLimits hRight hLeft zero_lt_one (c := 1)
  have hJV := globalProcess_locallyBoundedVariation hRight hLeft zero_lt_one (c := 1)
  have hJ0 : J 0 = 0 := globalProcess_zero hRight hLeft zero_lt_one
  let τ := cadlagAbsolutePassageLocalizer Y
  have hτ : IsLocalizingSequence F τ μ :=
    cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (hAdapted.sub hJA) (fun w t => (hRight w t).sub (hJR w t)) (hLeft.sub hJL)
  let D := goodIntegratorCenteredPassageDecomposition
    hUsual hX hAdapted hRight hLeft hZero 1 zero_lt_one
  have hOverlap := goodIntegratorCenteredPassageDecomposition_overlap
    hUsual hX hAdapted hRight hLeft hZero 1 zero_lt_one
  obtain ⟨M, hMA, hMM, hMR, hML, hMS⟩ :=
    CompatibleLocalMartingaleGluing.exists_cadlag_of_localMartingale hUsual hτ
      (fun n => (D n).localMartingale) (fun n => (D n).zeroN)
      (fun n => (D n).rightN) (fun n => (D n).leftN) (fun n m => (hOverlap n m).1)
  obtain ⟨A, hAP, hAR, hAV, hAS⟩ :=
    CompatibleLocalFiniteVariationGluing.exists_predictable_rightContinuous_locallyBoundedVariation
      hUsual hτ (fun n => (D n).predictableA) (fun n => (D n).rightA)
      (fun n => (D n).boundedVariationA) (fun n m => (hOverlap n m).2)
  have hY : ProcessIndistinguishable μ Y (fun t w => M t w + A t w) := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hτ
    intro n
    have hd := (D n).decomposition.stoppedProcess (τ n)
    have hTimes : (fun w => (cadlagAbsolutePassageLocalizerFinite Y n w : WithTop NNReal)) =
        τ n := by funext w; exact coe_cadlagAbsolutePassageLocalizerFinite Y n w
    change ProcessIndistinguishable μ
      (stoppedProcess (stoppedProcess Y _) (τ n)) _ at hd
    have hRestop : stoppedProcess
        (stoppedProcess Y (fun w => (cadlagAbsolutePassageLocalizerFinite Y n w : WithTop NNReal)))
        (τ n) = stoppedProcess Y (τ n) := by
      rw [hTimes, stoppedProcess_stoppedProcess_of_le_right (fun _ => le_rfl)]
    rw [hRestop] at hd
    filter_upwards [hd, hMS n, hAS n] with w hw hm ha
    intro t
    have hd := hw t
    have hm := hm t
    have ha := ha t
    dsimp only [stoppedProcess] at hd hm ha ⊢
    linarith
  have hAL : ProcessHasLeftLimits A :=
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      hAV
  let AC : Process Ω := fun t w => A t w - A 0 w
  have hACP : IsStronglyPredictable F AC :=
    hAP.sub (IsStronglyPredictable.timeConstant_initial hAP)
  have hACV : ∀ w, LocallyBoundedVariationOn (AC · w) univ := fun w =>
    SpecialSemimartingaleDecomposition.locallyBoundedVariationOn_sub_initial (hAV w)
  refine ⟨{
    N := fun t w => M t w - M 0 w
    A := fun t w => AC t w + J t w
    localMartingale := hMM.centered
    adaptedN := hMA.sub (fun t => (hMA 0).mono (F.mono bot_le))
    rightN := fun w t => (hMR w t).sub continuousWithinAt_const
    leftN := hML.sub (.timeConstant (M 0))
    zeroN := by funext w; exact sub_self _
    adaptedA := hACP.stronglyAdapted.add hJA
    rightA := fun w t => ((hAR w t).sub continuousWithinAt_const).add (hJR w t)
    leftA := (hAL.sub (.timeConstant (A 0))).add hJL
    variationA := fun w a b ha hb => boundedVariationOn_add (hACV w a b ha hb) (hJV w a b ha hb)
    zeroA := ?_
    decomposition := ?_ }⟩
  · filter_upwards [hY] with w hw
    intro t
    have ht := hw t
    have hz := hw 0
    change X t w - J t w = M t w + A t w at ht
    change X 0 w - J 0 w = M 0 w + A 0 w at hz
    rw [hZero, hJ0] at hz
    dsimp only [AC]
    change (0 : Real) - 0 = M 0 w + A 0 w at hz
    linarith
  · funext w
    change (A 0 w - A 0 w) + J 0 w = 0
    rw [sub_self, hJ0]
    exact zero_add _

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Returning elementary-test Cauchy limits to the decomposition domain -/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- A regular zero-initial good-integrator Cauchy sequence has a regular
zero-initial limit in the same adapted-FV decomposition domain. All limit,
good-integrator and decomposition witnesses are generated internally. -/
theorem ElementaryEmeryCauchy.exists_j1_limit
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hUsual : Filtration.UsualConditions μ F)
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hXL : ∀ n, ProcessHasLeftLimits (X n))
    (hZero : ∀ n, X n 0 = 0)
    (hGI : ∀ n, IsSemimartingale (X n) F μ) :
    ∃ Z : Process Ω, IsStronglyProgressive F Z ∧
      (∀ w t, ContinuousWithinAt (Z · w) (Ici t) t) ∧ ProcessHasLeftLimits Z ∧
      Z 0 = 0 ∧ Nonempty (J1Decomposition Z F μ) ∧ ElementaryEmeryConverges μ F X Z := by
  have hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0 := fun n =>
    Eventually.of_forall fun w => by rw [hZero n, hZero 0]
  obtain ⟨Y, hYP, hYR, hYL, _, hConv, _⟩ :=
    h.exists_cadlag_limit hUsual hX hXR hXL hInitial
  let Z : Process Ω := fun t w => Y t w - Y 0 w
  have hZR : ∀ w t, ContinuousWithinAt (Z · w) (Ici t) t :=
    fun w t => (hYR w t).sub continuousWithinAt_const
  have hZL : ProcessHasLeftLimits Z := hYL.sub (.timeConstant (Y 0))
  have hZA : StronglyAdapted F Z := fun t =>
    (hYP.stronglyAdapted t).sub ((hYP.stronglyAdapted 0).mono (F.mono bot_le))
  have hZP := StronglyAdapted.isStronglyProgressive_of_rightContinuous hZA hZR
  have hZ0 : Z 0 = 0 := funext fun w => sub_self _
  have hGain (J : PredictableElementaryStrategy F) (t : NNReal) (w : Ω) :
      ElementaryStrategy.gain Z J.toElementary t w =
        ElementaryStrategy.gain Y J.toElementary t w := by
    simp only [Z, ElementaryStrategy.gain, ElementaryInterval.gain, sub_sub_sub_cancel_right]
  have hConvZ : ElementaryEmeryConverges μ F X Z := by
    intro T ε hε
    simpa only [hGain] using hConv T ε hε
  have hGIZ := hConvZ.isSemimartingale hX hZP hXR hZR hGI
  exact ⟨Z, hZP, hZR, hZL, hZ0,
    exists_j1Decomposition_of_goodIntegrator_cadlag_zero hUsual hGIZ hZA hZR hZL hZ0,
    hConvZ⟩

end FTAPTheorem42
