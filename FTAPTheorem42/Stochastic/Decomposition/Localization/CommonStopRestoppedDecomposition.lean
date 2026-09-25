/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppedProcess
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopUncenteredFixedStopDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRestoppedComponent

/-!
# Re-stopping a common-stop fixed-stop decomposition

The common-stop fixed-stop construction is completed before it is used by the
global exhaustion.  If a later stopping time `rho` is bounded by its chosen
common stop `alpha`, the already completed decomposition can be stopped once
more.  This module records that data-level operation.  In particular, it does
not exchange stopping with any of the convexification used to construct the
fixed-stop package.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The re-stopped data certificate -/

structure CommonStopUncenteredRestoppedSpecialDecompositionData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Ω → WithTop NNReal}
    {alpha : Ω → WithTop NNReal} {R : Ω → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {M Atilde Aplus Aminus cumulativeVariation : Process Ω}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω}
    {cutoff : Nat → Nat} {A : Process Ω} {bad : Set Ω}
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation)
    (pair : CommonStopJordanDualProjectionPairData
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg)
    {Ap : Process Ω}
    (hSigned : CommonStopJordanSignedProjectionData
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap)
    {Mfixed : Process Ω}
    (hCentered : CommonStopFixedStopSpecialDecompositionData
      endpoint hReg pair hSigned Mfixed)
    {Msource : Process Ω}
    (hData : CommonStopUncenteredFixedStopSpecialDecompositionData
      endpoint hReg pair hSigned hCentered Msource)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ alpha omega)
    (Mρ Aρ : Process Ω) : Prop where
  /-- The two component processes are exactly the stopped fixed-stop ones. -/
  Mρ_eq_stopped : Mρ = MeasureTheory.stoppedProcess Msource rho
  Aρ_eq_stopped : Aρ = MeasureTheory.stoppedProcess Ap rho
  /-- The source double-stop identity used to identify the re-stopped source. -/
  source_doubleStop_eq :
    MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess S alpha) rho =
      MeasureTheory.stoppedProcess S rho
  source_doubleStop_indistinguishable :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess S alpha) rho)
      (MeasureTheory.stoppedProcess S rho)
  /-- The stopped martingale coordinate remains a true martingale. -/
  Mρ_martingale : Martingale Mρ F mu
  Mρ_stronglyAdapted : StronglyAdapted F Mρ
  Mρ_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Mρ · omega) (Ici t) t
  Mρ_leftLimits : ProcessHasLeftLimits Mρ
  /-- Stopping at time zero does not change the source's initial value. -/
  Mρ_initial : Mρ 0 =ᵐ[mu] S 0
  /-- The finite-variation coordinate retains all regularity needed below. -/
  Aρ_isStronglyPredictable : IsStronglyPredictable F Aρ
  Aρ_isStronglyAdapted : StronglyAdapted F Aρ
  Aρ_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Aρ · omega) (Ici t) t
  Aρ_leftLimits : ProcessHasLeftLimits Aρ
  Aρ_boundedVariation : ∀ omega,
    BoundedVariationOn (Aρ · omega) Set.univ
  Aρ_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (Aρ · omega) Set.univ
  Aρ_zero : Aρ 0 = 0
  /-- The already completed source decomposition, stopped at `rho`. -/
  source_indistinguishable : ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess S rho)
    (fun t omega => Mρ t omega + Aρ t omega)

/-! ## Re-stopping the completed package -/

theorem exists_commonStopUncenteredRestoppedSpecialDecompositionData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Ω → WithTop NNReal}
    {alpha : Ω → WithTop NNReal} {R : Ω → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    {M Atilde Aplus Aminus cumulativeVariation : Process Ω}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω}
    {cutoff : Nat → Nat} {A : Process Ω} {bad : Set Ω}
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation)
    (pair : CommonStopJordanDualProjectionPairData
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg)
    {Ap : Process Ω}
    (hSigned : CommonStopJordanSignedProjectionData
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap)
    {Mfixed : Process Ω}
    (hCentered : CommonStopFixedStopSpecialDecompositionData
      endpoint hReg pair hSigned Mfixed)
    {Msource : Process Ω}
    (hData : CommonStopUncenteredFixedStopSpecialDecompositionData
      endpoint hReg pair hSigned hCentered Msource)
    (rho : Ω → WithTop NNReal)
    (hRho : IsStoppingTime F rho)
    (hRhoLeAlpha : ∀ omega, rho omega ≤ alpha omega) :
    ∃ Mρ Aρ : Process Ω,
      ∃ _hRestopped : CommonStopUncenteredRestoppedSpecialDecompositionData
        endpoint hReg pair hSigned hCentered hData rho hRho hRhoLeAlpha Mρ Aρ,
        Nonempty (SpecialSemimartingaleDecomposition
          (MeasureTheory.stoppedProcess S rho) F mu) := by
  let hView : CommonStopUncenteredFixedStopComponentView
      (S := S) (F := F) (mu := mu) endpoint.alpha_stopping Msource Ap := {
    Msource_martingale := hData.Msource_martingale
    Msource_stronglyAdapted := hData.Msource_stronglyAdapted
    Msource_rightContinuous := hData.Msource_rightContinuous
    Msource_leftLimits := hData.Msource_leftLimits
    Msource_initial := hData.Msource_initial
    Ap_isStronglyPredictable := hCentered.Ap_isStronglyPredictable
    Ap_isStronglyAdapted := hCentered.Ap_isStronglyAdapted
    Ap_rightContinuous := hCentered.Ap_rightContinuous
    Ap_leftLimits := hCentered.Ap_leftLimits
    Ap_boundedVariation := hCentered.Ap_boundedVariation
    Ap_locallyBoundedVariation := hCentered.Ap_locallyBoundedVariation
    Ap_zero := hCentered.Ap_zero
    source_indistinguishable := hData.source_indistinguishable }
  obtain ⟨Mρ, Aρ, hCore, hDecomposition⟩ :=
    exists_commonStopUncenteredRestoppedComponentData
      (S := S) (F := F) (mu := mu) endpoint.alpha_stopping hView rho hRho
      hRhoLeAlpha
  let hRestopped : CommonStopUncenteredRestoppedSpecialDecompositionData
      endpoint hReg pair hSigned hCentered hData rho hRho hRhoLeAlpha Mρ Aρ := {
    Mρ_eq_stopped := hCore.Mρ_eq_stopped
    Aρ_eq_stopped := hCore.Aρ_eq_stopped
    source_doubleStop_eq := hCore.source_doubleStop_eq
    source_doubleStop_indistinguishable := hCore.source_doubleStop_indistinguishable
    Mρ_martingale := hCore.Mρ_martingale
    Mρ_stronglyAdapted := hCore.Mρ_stronglyAdapted
    Mρ_rightContinuous := hCore.Mρ_rightContinuous
    Mρ_leftLimits := hCore.Mρ_leftLimits
    Mρ_initial := hCore.Mρ_initial
    Aρ_isStronglyPredictable := hCore.Aρ_isStronglyPredictable
    Aρ_isStronglyAdapted := hCore.Aρ_isStronglyAdapted
    Aρ_rightContinuous := hCore.Aρ_rightContinuous
    Aρ_leftLimits := hCore.Aρ_leftLimits
    Aρ_boundedVariation := hCore.Aρ_boundedVariation
    Aρ_locallyBoundedVariation := hCore.Aρ_locallyBoundedVariation
    Aρ_zero := hCore.Aρ_zero
    source_indistinguishable := hCore.source_indistinguishable }
  exact ⟨Mρ, Aρ, hRestopped, hDecomposition⟩

end HorizonFactorialGrid

end FTAPTheorem42
