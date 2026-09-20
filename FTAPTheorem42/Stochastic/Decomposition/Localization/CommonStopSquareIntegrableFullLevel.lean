/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticVertical
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopSquareIntegrableUncenteredFixedStopDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRestoppedComponent

/-!
# A full square-integrable one-horizon common-stop level

This module is the vertical envelope producer.  The conditional-expectation
envelope, common gate, stopped-row controls, analytic rows, regularized raw
finite variation, Jordan projections, and uncentered fixed-stop consumer are
called in one dependent chain.  In particular, the returned decomposition and
the stopping time are attached to the same rows and coefficients; no bounded
source wrapper is introduced.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The dependent one-horizon certificate -/

/-- All witnesses produced by the envelope route at one finite horizon.

The `envelope`, `feasibility`, `control`, `analyticData`, `regularized`, and
`fixedStop` fields are dependent on one another.  Thus the `alpha`, selection,
rows, convex coefficients, and all fixed-stop components in this certificate
come from one invocation of the vertical producer.
-/
structure SquareIntegrableCommonStopAnalyticRegularizedLevelData
    {S : Process Ω}
    (T : NNReal) (eta : Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    where
  source_semimartingale : IsSemimartingale S F mu
  Z : Process Ω
  Γ : Ω → Real
  envelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ
  a : Real
  u : ∀ n, TailConvexWeights n
  selection : Nat → Nat
  alphaSeq : Nat → Ω → WithTop NNReal
  alpha : Ω → WithTop NNReal
  R : Ω → Real
  feasibility : EnvelopeDominatedCommonStoppedRowsFeasibilityEndpoint
    (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R
    hUsual hSAdapted hξ hSBound
  C : Ω → Real
  control : EnvelopeStoppedRowsInverseResidualControlData
    (S := S) (F := F) (mu := mu) ξ hξ T Z Γ envelope eta u selection a
    alphaSeq alpha R hUsual hSAdapted hSRight hSBound C
  N : Nat → Process Ω
  B : Nat → Process Ω
  analyticData : CommonStoppedRowsUniformAnalyticData
    (S := S) T alpha
    control.nativeResidualControl.nativeControl.feasibility.commonGate.alpha_stopping
    selection N B (envelopeInverseResidualControl C Γ)
    (ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu)) hUsual
  v : ∀ n, TailConvexWeights n
  Zlp : Lp Real 2 mu
  Nbar : Nat → Process Ω
  Bbar : Nat → Process Ω
  Xbar : Nat → Process Ω
  M : Process Ω
  cutoff : Nat → Nat
  nested : CommonStoppedRowsUniformAnalyticNestedGridVariationData analyticData v Zlp
    Nbar Bbar Xbar M cutoff
  A : Process Ω
  bad : Set Ω
  Atilde : Process Ω
  Aplus : Process Ω
  Aminus : Process Ω
  cumulativeVariation : Process Ω
  regularized : CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
    nested A bad Atilde Aplus Aminus cumulativeVariation
structure SquareIntegrableCommonStopUncenteredFixedStopLevelData
    {S : Process Ω}
    (T : NNReal) (eta : Real)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    where
  analytic : SquareIntegrableCommonStopAnalyticRegularizedLevelData
    (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound
  pkg : SquareIntegrablePredictableCompensatorJordanPackage
    (F := F) (mu := mu) analytic.Aplus analytic.Aminus T
  pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData pkg
  Ap : Process Ω
  signed : SquareIntegrablePredictableCompensatorJordanSignedProjectionData
    analytic.nested analytic.bad analytic.Atilde analytic.Aplus analytic.Aminus
      analytic.cumulativeVariation analytic.regularized pair Ap
  Mfixed : Process Ω
  centered : SquareIntegrableCommonStopFixedStopSpecialDecompositionData
    analytic.nested analytic.bad analytic.Atilde analytic.Aplus analytic.Aminus
      analytic.cumulativeVariation analytic.regularized pair signed Mfixed
  Msource : Process Ω
  uncentered : SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
    analytic.nested analytic.bad analytic.Atilde analytic.Aplus analytic.Aminus
      analytic.cumulativeVariation analytic.regularized pair signed centered Msource
  fixedStopDecomposition : Nonempty (SpecialSemimartingaleDecomposition
    (MeasureTheory.stoppedProcess S analytic.alpha) F mu)
  alpha_stopping : IsStoppingTime F analytic.alpha
  alpha_le_horizon : ∀ omega, analytic.alpha omega ≤ (T : WithTop NNReal)
  alpha_bad_event_measure : mu {omega |
      analytic.alpha omega < (T : WithTop NNReal)} ≤ ENNReal.ofReal (4 * eta)
  Msource_martingale : Martingale Msource F mu
  Ap_isStronglyPredictable : IsStronglyPredictable F Ap
  stopped_source_indistinguishable : ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess S analytic.alpha)
    (fun t omega => Msource t omega + Ap t omega)

/-! ## One dependent producer -/

theorem exists_squareIntegrableCommonStopUncenteredFixedStopLevelData
    {S : Process Ω}
    (T : NNReal) {eta : Real} (heta : 0 < eta)
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    Nonempty (SquareIntegrableCommonStopUncenteredFixedStopLevelData
      (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound) := by
  obtain ⟨Z, Γ, hEnvelope⟩ :=
    exists_cadlag_condExpEnvelopeData_of_memLp_two hUsual ξ hξ T
  obtain ⟨a, u, selection, alphaSeq, alpha, R, hFeas⟩ :=
    exists_commonGateStoppedRows_of_memLp_two_envelope
      hUsual hS hSAdapted ξ hξ hSBound T heta
  obtain ⟨C, hNative⟩ :=
    exists_envelopeStoppedRowsNativeUniformControlData
      hUsual hSAdapted ξ hξ hSBound T Z Γ hEnvelope u selection a alphaSeq alpha R
      hFeas (le_of_lt hFeas.commonGate.a_pos)
  have hInverse :=
    exists_envelopeStoppedRowsInverseMartingaleControlData
      ξ hξ T Z Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSBound C
      hNative
  have hNativeResidual :=
    exists_envelopeStoppedRowsNativeResidualControlData
      ξ hξ T Z Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
      hSBound C hNative
  have hControl :=
    exists_envelopeStoppedRowsInverseResidualControlData
      ξ hξ T Z Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
      hSBound C hNativeResidual hInverse
  obtain ⟨N, B, analyticData, v, Zlp, Nbar, Bbar, Xbar, M, cutoff, nested, A,
      bad, Atilde, Aplus, Aminus, cumulativeVariation, regularized⟩ :=
    exists_envelope_commonStoppedRows_uniformAnalytic_regularizedRawFiniteVariation
      ξ hξ T Z Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
      hSLeft hSBound C hControl
  obtain ⟨pkg, pair, Ap, signed, Mfixed, centered, Msource, uncentered,
      fixedStopDecomposition⟩ :=
   exists_squareIntegrableCommonStopUncenteredFixedStopSpecialDecomposition_of_commonStopRegularized
      (F := F) (mu := mu) nested bad Atilde Aplus Aminus cumulativeVariation regularized
      hSAdapted ξ hξ hSBound
  let analytic : SquareIntegrableCommonStopAnalyticRegularizedLevelData
      (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound := {
    source_semimartingale := hS
    Z := Z
    Γ := Γ
    envelope := hEnvelope
    a := a
    u := u
    selection := selection
    alphaSeq := alphaSeq
    alpha := alpha
    R := R
    feasibility := hControl.nativeResidualControl.nativeControl.feasibility
    C := C
    control := hControl
    N := N
    B := B
    analyticData := analyticData
    v := v
    Zlp := Zlp
    Nbar := Nbar
    Bbar := Bbar
    Xbar := Xbar
    M := M
    cutoff := cutoff
    nested := nested
    A := A
    bad := bad
    Atilde := Atilde
    Aplus := Aplus
    Aminus := Aminus
    cumulativeVariation := cumulativeVariation
    regularized := regularized }
  let hGate := hControl.nativeResidualControl.nativeControl.feasibility.commonGate
  have hLevel : SquareIntegrableCommonStopUncenteredFixedStopLevelData
      (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound := {
    analytic := analytic
    pkg := pkg
    pair := pair
    Ap := Ap
    signed := signed
    Mfixed := Mfixed
    centered := centered
    Msource := Msource
    uncentered := uncentered
    fixedStopDecomposition := fixedStopDecomposition
    alpha_stopping := hGate.alpha_stopping
    alpha_le_horizon := by
      intro omega
      exact (hGate.alpha_le_alphaSeq 0 omega).trans (hGate.alphaSeq_le_T 0 omega)
    alpha_bad_event_measure :=
      hGate.alpha_measure
    Msource_martingale := uncentered.Msource_martingale
    Ap_isStronglyPredictable := centered.Ap_isStronglyPredictable
    stopped_source_indistinguishable := uncentered.source_indistinguishable }
  exact ⟨hLevel⟩

/-!
## Re-stopping the square-integrable common-stop level

The square-integrable adapter exposes only the component fields required by
the source-independent re-stopping consumer.  The one-horizon level, its
stopping time, and its martingale/finite-variation components are retained;
no upstream rows or convex coefficients are selected again.
-/

/-! ## The square-integrable component adapter -/

/-- Extract the minimal source-independent component view from an `L²` level. -/
theorem SquareIntegrableCommonStopUncenteredFixedStopLevelData.toComponentView
    {S : Process Ω}
    {T : NNReal} {eta : Real}
    {ξ : Ω → Real} {hξ : MemLp ξ (2 : ENNReal) mu}
    {hUsual : Filtration.UsualConditions mu F}
    {hSAdapted : StronglyAdapted F S}
    {hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t}
    {hSLeft : ProcessHasLeftLimits S}
    {hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖}
    (hLevel : SquareIntegrableCommonStopUncenteredFixedStopLevelData
      (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound) :
    CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) hLevel.alpha_stopping
      hLevel.Msource hLevel.Ap := {
  Msource_martingale := hLevel.Msource_martingale
  Msource_stronglyAdapted := hLevel.uncentered.Msource_stronglyAdapted
  Msource_rightContinuous := hLevel.uncentered.Msource_rightContinuous
  Msource_leftLimits := hLevel.uncentered.Msource_leftLimits
  Msource_initial := hLevel.uncentered.Msource_initial
  Ap_isStronglyPredictable := hLevel.Ap_isStronglyPredictable
  Ap_isStronglyAdapted := hLevel.centered.Ap_isStronglyAdapted
  Ap_rightContinuous := hLevel.centered.Ap_rightContinuous
  Ap_leftLimits := hLevel.centered.Ap_leftLimits
  Ap_boundedVariation := hLevel.centered.Ap_boundedVariation
  Ap_locallyBoundedVariation := hLevel.centered.Ap_locallyBoundedVariation
  Ap_zero := hLevel.centered.Ap_zero
  source_indistinguishable := hLevel.stopped_source_indistinguishable }

/-! ## The square-integrable adapter -/

/-- Re-stop an `L²` fixed-stop level through the common component core. -/
theorem exists_squareIntegrableCommonStopUncenteredRestoppedComponentData
    {S : Process Ω}
    {T : NNReal} {eta : Real}
    {ξ : Ω → Real} {hξ : MemLp ξ (2 : ENNReal) mu}
    {hUsual : Filtration.UsualConditions mu F}
    {hSAdapted : StronglyAdapted F S}
    {hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t}
    {hSLeft : ProcessHasLeftLimits S}
    {hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖}
    (hLevel : SquareIntegrableCommonStopUncenteredFixedStopLevelData
      (F := F) (mu := mu) T eta ξ hξ hUsual hSAdapted hSRight hSLeft hSBound)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ hLevel.analytic.alpha omega) :
    ∃ Mρ Aρ : Process Ω,
      ∃ _hRestopped : CommonStopUncenteredRestoppedComponentData
        hLevel.alpha_stopping hLevel.toComponentView rho hRho hRhoLeAlpha Mρ Aρ,
        Nonempty (SpecialSemimartingaleDecomposition
          (MeasureTheory.stoppedProcess S rho) F mu) := by
  exact exists_commonStopUncenteredRestoppedComponentData
    (S := S) (F := F) (mu := mu) hLevel.alpha_stopping
      hLevel.toComponentView rho hRho hRhoLeAlpha

end HorizonFactorialGrid

end FTAPTheorem42
