/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalytic
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopConvexification
import FTAPTheorem42.Stochastic.Decomposition.Source.EnvelopeInverseResidualControl

/-!
# Producers for the common stopped-row analytic interface

This adapter attaches the source-independent certificate to the already
constructed bounded and envelope witnesses.  It does not select new rows or
stopping times.  The generic terminal tail consumer is called directly from
the envelope route below; the bounded route remains available through the
same interface.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Envelope producer -/

theorem exists_commonStoppedRowsUniformAnalyticData_of_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (hControl : EnvelopeStoppedRowsInverseResidualControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C) :
    ∃ (N B : Nat → Process Omega),
      CommonStoppedRowsUniformAnalyticData (S := S) T alpha
        hControl.nativeResidualControl.nativeControl.feasibility.commonGate.alpha_stopping
        selection N B (envelopeInverseResidualControl C Γ)
        (ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu)) hUsual := by
  let hGate := hControl.nativeResidualControl.nativeControl.feasibility.commonGate
  let N : Nat → Process Omega := fun k =>
    MeasureTheory.stoppedProcess
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
        (hGate.alphaSeq_stopping k)) alpha
  let B : Nat → Process Omega := fun k =>
    MeasureTheory.stoppedProcess
      (envelopeRowInverseResidualGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
        (hGate.alphaSeq_stopping k)) alpha
  have hAlphaLeT : ∀ omega, alpha omega ≤ (T : WithTop NNReal) := by
    intro omega
    exact (hGate.alpha_le_alphaSeq 0 omega).trans (hGate.alphaSeq_le_T 0 omega)
  have hCmem : MemLp C (2 : ENNReal) mu :=
    hControl.nativeResidualControl.nativeControl.control_memLp
  have hRhsTop : 2 * eLpNorm C (2 : ENNReal) mu ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hCmem.eLpNorm_ne_top
  have hLnonneg : 0 ≤ ENNReal.toReal (2 * eLpNorm C (2 : ENNReal) mu) :=
    ENNReal.toReal_nonneg
  refine ⟨N, B, ?_⟩
  refine
    { alpha_le_horizon := hAlphaLeT
      selection_strictMono := hGate.selection_strictMono
      martingale := ?_
      martingale_zero := ?_
      martingale_rightContinuous := ?_
      terminal_memLp := ?_
      terminal_bound_nonneg := hLnonneg
      terminal_norm_le := ?_
      residual_memLp := hControl.control_memLp
      residual_integrable := hControl.control_integrable
      residual_nonneg := hControl.control_nonneg
      residual_baseGridVariation := ?_
      residual_horizon_sup := ?_
      stoppedSource_eq_martingale_add_residual := ?_ }
  · intro k
    simpa [N] using
      (hControl.nativeResidualControl.nativeControl.feasibility.rowData k).stopped_martingale
  · intro k
    funext omega
    unfold N
    rw [MeasureTheory.stoppedProcess_eq_of_le (by exact bot_le)]
    unfold envelopeRowInverseMartingaleGain
    exact martingaleIntegralProcess_at_zero
      (grid T (rowCommonLevel u (selection k)))
      (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u (selection k) a T (alphaSeq k))
      (envelopeNativeMartingaleConvexRow u (selection k) hUsual hSAdapted
        ξ hξ hSBound a T) omega
  · intro k omega t
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
          (hGate.alphaSeq_stopping k))
      (envelopeRowInverseMartingaleGain_rightContinuous
        (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
        a T (alphaSeq k) (hGate.alphaSeq_stopping k)) omega t
  · intro k
    simpa [N] using
      (hControl.nativeResidualControl.nativeControl.feasibility.rowData k).stopped_terminal_memLp
  · intro k
    have hNorm := hControl.inverseMartingaleControl.stoppedInverseTerminal_eLpNorm_le k
    rw [MeasureTheory.Lp.norm_toLp]
    change (eLpNorm
      (MeasureTheory.stoppedProcess
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
            (hGate.alphaSeq_stopping k)) alpha T)
        (2 : ENNReal) mu).toReal ≤
      (2 * eLpNorm C (2 : ENNReal) mu).toReal
    exact (ENNReal.toReal_le_toReal
      (hControl.inverseMartingaleControl.stoppedInverseTerminal_memLp k).eLpNorm_ne_top
      hRhsTop).mpr hNorm
  · intro k
    filter_upwards [hControl.stoppedInverseResidual_baseGridVariation k] with omega hOmega
    simpa [B, envelopeStoppedInverseResidualRow, envelopeInverseResidualRow] using hOmega
  · intro k
    filter_upwards [hControl.stoppedInverseResidual_horizon_bound k] with omega hOmega
    intro t ht
    simpa [B, envelopeStoppedInverseResidualRow, envelopeInverseResidualRow] using hOmega t ht
  · intro k t omega
    have hRowData := hControl.nativeResidualControl.nativeControl.feasibility.rowData k
    have h := hRowData.stoppedSource_eq_martingale_add_residual t omega
    simpa [N, B, envelopeStoppedInverseResidualRow, envelopeInverseResidualRow] using h

/-! ## Direct envelope consumer of the generic tail theorem -/

theorem exists_envelope_commonStoppedRows_uniformAnalytic_terminalTailConvexification
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
      (Nbar Bbar Xbar : Nat → Process Omega),
      CommonStoppedRowsUniformAnalyticTailConvexificationData data v Z Nbar Bbar Xbar := by
  obtain ⟨N, B, hData⟩ := exists_commonStoppedRowsUniformAnalyticData_of_envelope
    ξ hξ T Z₀ Γ hEnvelope u selection a alphaSeq alpha R hUsual hSAdapted hSRight
      hSBound C hControl
  obtain ⟨v, Z, Nbar, Bbar, Xbar, hTail⟩ :=
    hData.exists_terminalTailConvexification
  exact ⟨N, B, hData, v, Z, Nbar, Bbar, Xbar, hTail⟩

end HorizonFactorialGrid

end FTAPTheorem42
