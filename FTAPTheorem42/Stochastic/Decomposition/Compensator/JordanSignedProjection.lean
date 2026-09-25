/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.JordanDualProjection
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.DualProjection

/-!
# The signed projection of the common-stop Jordan residual

The two nonnegative Jordan components of the regularized common-stop residual
have independent completed predictable projections.  This module takes their
difference.  It records the pathwise regularity of that signed process and
identifies the remaining finite-variation residual with the difference of the
two component martingales.

No fixed-stop martingale component is formed here.  The next consumer may use
the residual martingale in this certificate together with the common-stop
martingale already present in the raw decomposition.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Signed projection certificate -/

structure CommonStopJordanSignedProjectionData
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
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
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
    (Ap : Process Ω) : Prop where
  Ap_eq_def : Ap = fun t omega => pair.plus.Vp t omega - pair.minus.Vp t omega
  Ap_isStronglyPredictable : IsStronglyPredictable F Ap
  Ap_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Ap · omega) (Ici t) t
  Ap_leftLimits : ProcessHasLeftLimits Ap
  Ap_boundedVariation : ∀ omega,
    BoundedVariationOn (Ap · omega) Set.univ
  Ap_zero : Ap 0 = 0
  Ap_constant_after : ∀ omega t, T ≤ t →
    Ap t omega = Ap T omega
  residual_stronglyAdapted : StronglyAdapted F
    (fun t omega => Atilde t omega - Ap t omega)
  residual_martingale : Martingale
    (fun t omega => Atilde t omega - Ap t omega) F mu
  residual_indistinguishable_jordan : ProcessIndistinguishable mu
    (fun t omega => Atilde t omega - Ap t omega)
    (fun t omega =>
      (Aplus t omega - pair.plus.Vp t omega) -
        (Aminus t omega - pair.minus.Vp t omega))
  signed_decomposition : ProcessIndistinguishable mu Atilde
    (fun t omega => Ap t omega +
      ((Aplus t omega - pair.plus.Vp t omega) -
        (Aminus t omega - pair.minus.Vp t omega)))

/-! ## Construction from the two component certificates -/

theorem exists_commonStopJordanSignedProjection_of_pair
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
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation)
    (pair : CommonStopJordanDualProjectionPairData
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg) :
    ∃ Ap : Process Ω,
      CommonStopJordanSignedProjectionData
        endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap := by
  obtain ⟨Ap, hCore⟩ := exists_predictableSignedProjectionCore
    (F := F) (mu := mu) (Atilde := Atilde) (Aplus := Aplus)
    (Aminus := Aminus) (VpPlus := pair.plus.Vp) (VpMinus := pair.minus.Vp)
    (T := T) hReg.Atilde_stronglyAdapted
    pair.plus.projection.predictable_version.Vp_isStronglyPredictable
    pair.minus.projection.predictable_version.Vp_isStronglyPredictable
    pair.plus.projection.predictable_version.Vp_rightContinuous
    pair.minus.projection.predictable_version.Vp_rightContinuous
    pair.plus.projection.predictable_version.Vp_leftLimits
    pair.minus.projection.predictable_version.Vp_leftLimits
    pair.plus.projection.predictable_version.Vp_nonnegative
    pair.minus.projection.predictable_version.Vp_nonnegative
    pair.plus.projection.predictable_version.Vp_monotone
    pair.minus.projection.predictable_version.Vp_monotone
    pair.plus.projection.predictable_version.Vp_zero
    pair.minus.projection.predictable_version.Vp_zero
    pair.plus.projection.predictable_version.Vp_constant_after
    pair.minus.projection.predictable_version.Vp_constant_after
    pair.plus.projection.residual_martingale
    pair.minus.projection.residual_martingale
    hReg.jordan_decomposition
  refine ⟨Ap, {
    Ap_eq_def := hCore.Ap_eq_def
    Ap_isStronglyPredictable := hCore.Ap_isStronglyPredictable
    Ap_rightContinuous := hCore.Ap_rightContinuous
    Ap_leftLimits := hCore.Ap_leftLimits
    Ap_boundedVariation := hCore.Ap_boundedVariation
    Ap_zero := hCore.Ap_zero
    Ap_constant_after := hCore.Ap_constant_after
    residual_stronglyAdapted := hCore.residual_stronglyAdapted
    residual_martingale := hCore.residual_martingale
    residual_indistinguishable_jordan := hCore.residual_indistinguishable_jordan
    signed_decomposition := hCore.signed_decomposition }⟩

/-! ## Direct consumer for the common-stop Jordan pair producer -/

theorem exists_commonStopJordanSignedProjection_of_commonStopRegularized
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
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ pair : CommonStopJordanDualProjectionPairData
        endpoint bad Atilde Aplus Aminus cumulativeVariation hReg,
      ∃ Ap : Process Ω,
        CommonStopJordanSignedProjectionData
          endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap := by
  obtain ⟨pair⟩ := exists_commonStopJordanDualProjectionPair
    (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨Ap, hSigned⟩ := exists_commonStopJordanSignedProjection_of_pair
    (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair
  exact ⟨pair, Ap, hSigned⟩

end HorizonFactorialGrid

end FTAPTheorem42
