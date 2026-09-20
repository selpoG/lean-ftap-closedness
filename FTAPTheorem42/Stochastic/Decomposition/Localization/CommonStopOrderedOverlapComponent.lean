/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRestoppedComponent
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale

/-!
# Source-independent ordered overlap of re-stopped components

This module contains the part of the common-stop overlap argument which is
independent of the bounded or square-integrable producer.  Two completed
component packages are compared after the same stopping time.  The difference
of their finite-variation coordinates is a predictable finite-variation local
martingale, so source-free rigidity identifies both coordinates.  A separate
minimum-stop bridge transports this identity to two coordinates of one
localizing schedule.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open PredictableFiniteVariationLocalMartingale

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Stopping bridges -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem stoppedProcess_indistinguishable_of_ae_eq
    {u : Process Ω} {σ τ : Ω → WithTop NNReal}
    (hστ : ∀ᵐ ω ∂mu, σ ω = τ ω) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess u σ)
      (MeasureTheory.stoppedProcess u τ) := by
  filter_upwards [hστ] with ω hω
  intro t
  simp only [MeasureTheory.stoppedProcess]
  rw [hω]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem stoppedProcess_stoppedProcess_indistinguishable_of_ae_le
    {u : Process Ω} {σ τ : Ω → WithTop NNReal}
    (hστ : ∀ᵐ ω ∂mu, σ ω ≤ τ ω) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess u τ) σ)
      (MeasureTheory.stoppedProcess u σ) := by
  filter_upwards [hστ] with ω hω
  intro t
  rw [MeasureTheory.stoppedProcess_stoppedProcess]
  change u (min (t : WithTop NNReal) (min (σ ω) (τ ω))).untopA ω =
    u (min (t : WithTop NNReal) (σ ω)).untopA ω
  rw [min_eq_left hω]

/-! ## One ordered pair at one common stop -/

/-- The source-independent ordered overlap certificate.  The two
`restopped` fields are completed component certificates at the same `rho`;
the remaining fields are exactly the rigidity certificate used by downstream
gluing consumers. -/
structure CommonStopUncenteredRestoppedOrderedOverlapComponentData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alphaN alphaM : Ω → WithTop NNReal}
    (hAlphaN : IsStoppingTime F alphaN)
    {MsourceN ApN MsourceM ApM : Process Ω}
    (hViewN : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlphaN MsourceN ApN)
    (hAlphaM : IsStoppingTime F alphaM)
    (hViewM : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlphaM MsourceM ApM)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeN : ∀ omega, rho omega ≤ alphaN omega)
    (hRhoLeM : ∀ omega, rho omega ≤ alphaM omega)
    (MρN AρN MρM AρM : Process Ω) where
  restoppedN : CommonStopUncenteredRestoppedComponentData
    hAlphaN hViewN rho hRho hRhoLeN MρN AρN
  restoppedM : CommonStopUncenteredRestoppedComponentData
    hAlphaM hViewM rho hRho hRhoLeM MρM AρM
  finiteVariationDifference : Process Ω
  finiteVariationDifference_eq :
    finiteVariationDifference = (fun t omega => AρM t omega - AρN t omega)
  finiteVariationDifference_isLocalMartingale :
    LocalMartingale finiteVariationDifference F mu
  finiteVariationDifference_isStronglyPredictable :
    IsStronglyPredictable F finiteVariationDifference
  finiteVariationDifference_rightContinuous : ∀ omega t,
    ContinuousWithinAt (finiteVariationDifference · omega) (Ici t) t
  finiteVariationDifference_boundedVariation : ∀ omega,
    BoundedVariationOn (finiteVariationDifference · omega) Set.univ
  finiteVariationDifference_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (finiteVariationDifference · omega) Set.univ
  finiteVariationDifference_zero : finiteVariationDifference 0 = 0
  finiteVariationDifference_indistinguishable_oppositeMartingale :
    ProcessIndistinguishable mu finiteVariationDifference
      (fun t omega => MρN t omega - MρM t omega)
  finiteVariationDifference_indistinguishable_zero :
    ProcessIndistinguishable mu finiteVariationDifference (fun _ _ => 0)
  finiteVariation_overlap_at_rho :
    ProcessIndistinguishable mu AρN AρM
  martingale_overlap_at_rho :
    ProcessIndistinguishable mu MρN MρM

theorem exists_commonStopUncenteredRestoppedOrderedOverlapComponentData
    {S : Process Ω}
    (hUsual : Filtration.UsualConditions mu F)
    {alphaN alphaM : Ω → WithTop NNReal}
    (hAlphaN : IsStoppingTime F alphaN)
    {MsourceN ApN MsourceM ApM : Process Ω}
    (hViewN : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlphaN MsourceN ApN)
    (hAlphaM : IsStoppingTime F alphaM)
    (hViewM : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hAlphaM MsourceM ApM)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeN : ∀ omega, rho omega ≤ alphaN omega)
    (hRhoLeM : ∀ omega, rho omega ≤ alphaM omega)
    (MρN AρN MρM AρM : Process Ω)
    (hRestoppedN : CommonStopUncenteredRestoppedComponentData
      hAlphaN hViewN rho hRho hRhoLeN MρN AρN)
    (hRestoppedM : CommonStopUncenteredRestoppedComponentData
      hAlphaM hViewM rho hRho hRhoLeM MρM AρM) :
    Nonempty (CommonStopUncenteredRestoppedOrderedOverlapComponentData
      hAlphaN hViewN hAlphaM hViewM rho hRho hRhoLeN hRhoLeM MρN AρN MρM AρM) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  let ADiff : Process Ω := fun t omega =>
    AρM t omega - AρN t omega
  have hSum : ProcessIndistinguishable mu
      (fun t omega => MρN t omega + AρN t omega)
      (fun t omega => MρM t omega + AρM t omega) :=
    hRestoppedN.source_indistinguishable.symm.trans
      hRestoppedM.source_indistinguishable
  have hADiffOpposite : ProcessIndistinguishable mu ADiff
      (fun t omega => MρN t omega - MρM t omega) := by
    filter_upwards [hSum] with omega hOmega
    intro t
    dsimp [ADiff]
    linarith [hOmega t]
  have hADiffPredictable : IsStronglyPredictable F ADiff := by
    unfold IsStronglyPredictable
    dsimp [ADiff]
    exact hRestoppedM.Aρ_isStronglyPredictable.sub
      hRestoppedN.Aρ_isStronglyPredictable
  have hADiffRight : ∀ omega t,
      ContinuousWithinAt (ADiff · omega) (Ici t) t := by
    intro omega t
    dsimp [ADiff]
    exact (hRestoppedM.Aρ_rightContinuous omega t).sub
      (hRestoppedN.Aρ_rightContinuous omega t)
  have hADiffVariation : ∀ omega,
      BoundedVariationOn (ADiff · omega) Set.univ := by
    intro omega
    simpa only [ADiff, sub_eq_add_neg] using
      boundedVariationOn_add
        (hRestoppedM.Aρ_boundedVariation omega)
        (boundedVariationOn_neg
          (hRestoppedN.Aρ_boundedVariation omega))
  have hADiffLocalVariation : ∀ omega,
      LocallyBoundedVariationOn (ADiff · omega) Set.univ := by
    intro omega
    exact (hADiffVariation omega).locallyBoundedVariationOn
  have hADiffZero : ADiff 0 = 0 := by
    funext omega
    dsimp [ADiff]
    rw [congrFun hRestoppedM.Aρ_zero omega,
      congrFun hRestoppedN.Aρ_zero omega]
    ring
  have hMartingaleDifference : Martingale
      (fun t omega => MρN t omega - MρM t omega) F mu :=
    hRestoppedN.Mρ_martingale.sub hRestoppedM.Mρ_martingale
  have hADiffMartingale : Martingale ADiff F mu := by
    apply hMartingaleDifference.congr hADiffPredictable.stronglyAdapted
    intro t
    exact (hADiffOpposite.eventuallyEq_at t).symm
  have hADiffLocalMartingale : LocalMartingale ADiff F mu :=
    ProbabilityTheory.Locally.of_prop hADiffMartingale
  have hADiffZeroIndistinguishable :
      ProcessIndistinguishable mu ADiff (fun _ _ => 0) :=
    indistinguishable_zero_of_predictableFiniteVariationLocalMartingale
      hUsual ADiff hADiffLocalMartingale hADiffPredictable hADiffRight
      hADiffVariation hADiffZero
  have hFiniteVariationOverlap : ProcessIndistinguishable mu AρN AρM := by
    filter_upwards [hADiffZeroIndistinguishable] with omega hOmega
    intro t
    have h := hOmega t
    dsimp [ADiff] at h
    linarith
  have hMartingaleDifferenceZero : ProcessIndistinguishable mu
      (fun t omega => MρN t omega - MρM t omega)
      (fun _ _ => 0) :=
    hADiffOpposite.symm.trans hADiffZeroIndistinguishable
  have hMartingaleOverlap : ProcessIndistinguishable mu MρN MρM := by
    filter_upwards [hMartingaleDifferenceZero] with omega hOmega
    intro t
    exact sub_eq_zero.mp (hOmega t)
  exact ⟨{
    restoppedN := hRestoppedN
    restoppedM := hRestoppedM
    finiteVariationDifference := ADiff
    finiteVariationDifference_eq := by rfl
    finiteVariationDifference_isLocalMartingale := hADiffLocalMartingale
    finiteVariationDifference_isStronglyPredictable := hADiffPredictable
    finiteVariationDifference_rightContinuous := hADiffRight
    finiteVariationDifference_boundedVariation := hADiffVariation
    finiteVariationDifference_locallyBoundedVariation := hADiffLocalVariation
    finiteVariationDifference_zero := hADiffZero
    finiteVariationDifference_indistinguishable_oppositeMartingale :=
      hADiffOpposite
    finiteVariationDifference_indistinguishable_zero :=
      hADiffZeroIndistinguishable
    finiteVariation_overlap_at_rho := hFiniteVariationOverlap
    martingale_overlap_at_rho := hMartingaleOverlap }⟩

/-! ## Transport to a minimum of two localizers -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem stoppedProcess_stoppedProcess_indistinguishable_of_stopped_overlap_of_ae_le
    {u v X Y : Process Ω} {rhoN rhoM : Ω → WithTop NNReal}
    (hX : ProcessIndistinguishable mu X
      (MeasureTheory.stoppedProcess u rhoN))
    (hY : ProcessIndistinguishable mu Y
      (MeasureTheory.stoppedProcess v rhoM))
    (hOverlap : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess u rhoN)
      (MeasureTheory.stoppedProcess v rhoN))
    (hRhoLe : ∀ᵐ omega ∂mu, rhoN omega ≤ rhoM omega) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess X (min rhoN rhoM))
      (MeasureTheory.stoppedProcess Y (min rhoN rhoM)) := by
  have hMin : ∀ᵐ omega ∂mu,
      min (rhoN omega) (rhoM omega) = rhoN omega := by
    filter_upwards [hRhoLe] with omega hOmega
    exact min_eq_left hOmega
  have hLeft : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess X (min rhoN rhoM))
      (MeasureTheory.stoppedProcess u rhoN) := by
    have hXStop := hX.stoppedProcess (min rhoN rhoM)
    have hNested :=
      stoppedProcess_stoppedProcess_indistinguishable_of_ae_le
        (mu := mu) (u := u) (σ := min rhoN rhoM) (τ := rhoN)
        (Filter.Eventually.of_forall fun omega => min_le_left _ _)
    have hMinEq := stoppedProcess_indistinguishable_of_ae_eq
      (u := u) hMin
    exact hXStop.trans (hNested.trans hMinEq)
  have hRight : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Y (min rhoN rhoM))
      (MeasureTheory.stoppedProcess v rhoN) := by
    have hYStop := hY.stoppedProcess (min rhoN rhoM)
    have hNested :=
      stoppedProcess_stoppedProcess_indistinguishable_of_ae_le
        (mu := mu) (u := v) (σ := min rhoN rhoM) (τ := rhoM)
        (Filter.Eventually.of_forall fun omega => min_le_right _ _)
    have hMinEq := stoppedProcess_indistinguishable_of_ae_eq
      (u := v) hMin
    exact hYStop.trans (hNested.trans hMinEq)
  exact hLeft.trans (hOverlap.trans hRight.symm)

end HorizonFactorialGrid

end FTAPTheorem42
