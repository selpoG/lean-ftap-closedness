/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticProducers
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticNestedGridVariation
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticRawFiniteVariation
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticRegularization

/-!
# Vertical consumption of the common-stop analytic interface

The envelope route is now consumed through one source-independent chain:
native/inverse row control, analytic terminal-tail convexification, the
càdlàg martingale limit, and nested-grid residual variation.  All witnesses
are returned by one theorem; no coefficient family or stopping time is
selected again at this layer.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

theorem exists_envelope_commonStoppedRows_uniformAnalytic_nestedGridVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z₀ : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z₀ Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (hControl : EnvelopeStoppedRowsInverseResidualControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z₀ Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C) :
    ∃ (N B : Nat → Process Omega)
      (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha
        hControl.nativeResidualControl.nativeControl.feasibility.commonGate.alpha_stopping
        selection N B (envelopeInverseResidualControl C Γ)
        (ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu)) hUsual)
      (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
      (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
      (cutoff : Nat → Nat),
      CommonStoppedRowsUniformAnalyticNestedGridVariationData data v Z Nbar Bbar Xbar
        M cutoff := by
  obtain ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, hTail⟩ :=
    exists_envelope_commonStoppedRows_uniformAnalytic_terminalTailConvexification
      ξ hξ T Z₀ Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
        hSBound C hControl
  obtain ⟨M, cutoff, hCadlag⟩ := hTail.exists_cadlagMartingaleLimit
  exact ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, M, cutoff,
    commonStoppedRowsUniformAnalytic_nestedGridVariation data hCadlag⟩

theorem exists_envelope_commonStoppedRows_uniformAnalytic_rawFiniteVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z₀ : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z₀ Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (hControl : EnvelopeStoppedRowsInverseResidualControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z₀ Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C) :
    ∃ (N B : Nat → Process Omega)
      (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha
        hControl.nativeResidualControl.nativeControl.feasibility.commonGate.alpha_stopping
        selection N B (envelopeInverseResidualControl C Γ)
        (ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu)) hUsual)
      (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
      (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
      (cutoff : Nat → Nat)
      (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData data v Z Nbar Bbar
        Xbar M cutoff),
      ∃ A : Process Omega,
        CommonStoppedRowsUniformAnalyticRawFiniteVariationData hNested A := by
  obtain ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, M, cutoff, hNested⟩ :=
    exists_envelope_commonStoppedRows_uniformAnalytic_nestedGridVariation
      ξ hξ T Z₀ Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
        hSBound C hControl
  obtain ⟨A, hA⟩ := commonStoppedRowsUniformAnalytic_rawFiniteVariation
    hSAdapted hSRight hSLeft hNested
  exact ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, M, cutoff, hNested, A, hA⟩

theorem exists_envelope_commonStoppedRows_uniformAnalytic_regularizedRawFiniteVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z₀ : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z₀ Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (hControl : EnvelopeStoppedRowsInverseResidualControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z₀ Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C) :
    ∃ (N B : Nat → Process Omega)
      (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha
        hControl.nativeResidualControl.nativeControl.feasibility.commonGate.alpha_stopping
        selection N B (envelopeInverseResidualControl C Γ)
        (ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu)) hUsual)
      (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
      (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
      (cutoff : Nat → Nat)
      (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData data v Z Nbar Bbar
        Xbar M cutoff),
      ∃ A : Process Omega, ∃ (bad : Set Omega)
        (Atilde Aplus Aminus cumulativeVariation : Process Omega),
        CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
          hNested A bad Atilde Aplus Aminus cumulativeVariation := by
  obtain ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, M, cutoff, hNested, A, hA⟩ :=
    exists_envelope_commonStoppedRows_uniformAnalytic_rawFiniteVariation
      ξ hξ T Z₀ Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
        hSLeft hSBound C hControl
  obtain ⟨bad, Atilde, Aplus, Aminus, cumulativeVariation, hReg⟩ :=
    commonStoppedRowsUniformAnalytic_regularizeRawFiniteVariation hNested hA
  exact ⟨N, B, data, v, Z, Nbar, Bbar, Xbar, M, cutoff, hNested, A,
    bad, Atilde, Aplus, Aminus, cumulativeVariation, hReg⟩

end HorizonFactorialGrid

end FTAPTheorem42
