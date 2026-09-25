/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.JordanSignedProjection
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopFixedStopDecompositionCore

/-!
# A fixed-stop special decomposition from the signed projection

The common-stop construction first decomposes the centered stopped source as
`M + Atilde`.  The signed dual projection writes the residual `Atilde - Ap`
as a true martingale.  Moving that residual into the martingale coordinate
therefore gives

```text
Mfixed = M + (Atilde - Ap),       X^alpha = Mfixed + Ap.
```

All identities in this module are process identities up to
indistinguishability.  In particular, the fixed-stop package does not replace
the raw or regularized process decomposition by a collection of fixed-time
almost-everywhere equalities.
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

/-! ## Fixed-stop package -/

structure CommonStopFixedStopSpecialDecompositionData
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
    (Mfixed : Process Ω) : Prop where
  Mfixed_eq_def : Mfixed = fun t omega =>
    M t omega + (Atilde t omega - Ap t omega)
  Mfixed_martingale : Martingale Mfixed F mu
  Mfixed_stronglyAdapted : StronglyAdapted F Mfixed
  Mfixed_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Mfixed · omega) (Ici t) t
  Mfixed_leftLimits : ProcessHasLeftLimits Mfixed
  Mfixed_zero : Mfixed 0 =ᵐ[mu] 0
  Mfixed_constant_after : ∀ t, T ≤ t → Mfixed t =ᵐ[mu] Mfixed T
  Ap_isStronglyPredictable : IsStronglyPredictable F Ap
  Ap_isStronglyAdapted : StronglyAdapted F Ap
  Ap_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Ap · omega) (Ici t) t
  Ap_leftLimits : ProcessHasLeftLimits Ap
  Ap_boundedVariation : ∀ omega,
    BoundedVariationOn (Ap · omega) Set.univ
  Ap_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (Ap · omega) Set.univ
  Ap_zero : Ap 0 = 0
  Ap_constant_after : ∀ omega t, T ≤ t →
    Ap t omega = Ap T omega
  signedResidual_martingale : Martingale
    (fun t omega => Atilde t omega - Ap t omega) F mu
  signedResidual_indistinguishable_jordan : ProcessIndistinguishable mu
    (fun t omega => Atilde t omega - Ap t omega)
    (fun t omega =>
      (Aplus t omega - pair.plus.Vp t omega) -
        (Aminus t omega - pair.minus.Vp t omega))
  raw_regularized_source_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => M t omega + Atilde t omega)
  signed_source_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => M t omega +
      (Ap t omega +
        ((Aplus t omega - pair.plus.Vp t omega) -
          (Aminus t omega - pair.minus.Vp t omega))))
  centeredSource_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => Mfixed t omega + Ap t omega)

/-! ## Construction from the signed projection -/

theorem exists_commonStopFixedStopSpecialDecomposition_of_signed
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
      endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap) :
    ∃ Mfixed : Process Ω,
      CommonStopFixedStopSpecialDecompositionData
        endpoint hReg pair hSigned Mfixed := by
  let Mfixed : Process Ω := fun t omega =>
    M t omega + (Atilde t omega - Ap t omega)
  have hM : Martingale M F mu := hReg.raw.nestedGrid.cadlag.M_martingale
  have hMfixed : Martingale Mfixed F mu := by
    dsimp [Mfixed]
    exact hM.add hSigned.residual_martingale
  have hMfixedAdapted : StronglyAdapted F Mfixed := hMfixed.stronglyAdapted
  have hResidualRight : ∀ omega t,
      ContinuousWithinAt
        ((fun s omega => Atilde s omega - Ap s omega) · omega) (Ici t) t := by
    intro omega t
    exact (hReg.Atilde_rightContinuous omega t).sub
      (hSigned.Ap_rightContinuous omega t)
  have hMfixedRight : ∀ omega t,
      ContinuousWithinAt (Mfixed · omega) (Ici t) t := by
    intro omega t
    dsimp [Mfixed]
    exact (hReg.raw.nestedGrid.cadlag.M_rightContinuous omega t).add
      (hResidualRight omega t)
  have hResidualLeft : ProcessHasLeftLimits
      (fun t omega => Atilde t omega - Ap t omega) :=
    hReg.Atilde_hasLeftLimits.sub hSigned.Ap_leftLimits
  have hMfixedLeft : ProcessHasLeftLimits Mfixed := by
    dsimp [Mfixed]
    exact hReg.raw.nestedGrid.cadlag.M_leftLimits.add hResidualLeft
  have hMfixedZero : Mfixed 0 =ᵐ[mu] 0 := by
    filter_upwards [hReg.raw.nestedGrid.cadlag.M_zero] with omega hMzero
    dsimp [Mfixed]
    rw [hMzero, congrFun hReg.Atilde_zero omega,
      congrFun hSigned.Ap_zero omega]
    simp
  have hMfixedConstant : ∀ t, T ≤ t → Mfixed t =ᵐ[mu] Mfixed T := by
    intro t ht
    filter_upwards [hReg.raw.nestedGrid.cadlag.M_constant_after t ht] with omega hM
    dsimp [Mfixed]
    rw [hM, hReg.Atilde_constant_after omega t ht,
      hSigned.Ap_constant_after omega t ht]
  have hApLocal : ∀ omega,
      LocallyBoundedVariationOn (Ap · omega) Set.univ := by
    intro omega
    exact hSigned.Ap_boundedVariation omega |>.locallyBoundedVariationOn
  have hRawSource : ProcessIndistinguishable mu
      (commonStopCenteredStoppedSource S alpha)
      (fun t omega => M t omega + Atilde t omega) := by
    change ProcessIndistinguishable mu
      (fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega)
      (fun t omega => M t omega + Atilde t omega)
    exact hReg.stoppedSource_indistinguishable
  have hSignedSource : ProcessIndistinguishable mu
      (commonStopCenteredStoppedSource S alpha)
      (fun t omega => M t omega +
        (Ap t omega +
          ((Aplus t omega - pair.plus.Vp t omega) -
            (Aminus t omega - pair.minus.Vp t omega)))) := by
    have hAdd := ProcessIndistinguishable.add
      (ProcessIndistinguishable.refl mu (fun t omega => M t omega))
      hSigned.signed_decomposition
    exact hRawSource.trans hAdd
  have hResidualJordan : ProcessIndistinguishable mu
      (fun t omega => Atilde t omega - Ap t omega)
      (fun t omega =>
        (Aplus t omega - pair.plus.Vp t omega) -
          (Aminus t omega - pair.minus.Vp t omega)) :=
    hSigned.residual_indistinguishable_jordan
  have hSignedToFixed : ProcessIndistinguishable mu
      (fun t omega => M t omega +
        (Ap t omega +
          ((Aplus t omega - pair.plus.Vp t omega) -
            (Aminus t omega - pair.minus.Vp t omega))))
      (fun t omega => Mfixed t omega + Ap t omega) := by
    have hAddResidual := ProcessIndistinguishable.add
      (ProcessIndistinguishable.refl mu (fun t omega => M t omega))
      (ProcessIndistinguishable.add
        (ProcessIndistinguishable.refl mu (fun t omega => Ap t omega))
        hResidualJordan.symm)
    have hAlgebra : ProcessIndistinguishable mu
        (fun t omega => M t omega +
          (Ap t omega + (Atilde t omega - Ap t omega)))
        (fun t omega => Mfixed t omega + Ap t omega) := by
      filter_upwards [] with omega
      intro t
      dsimp [Mfixed]
      ring
    exact hAddResidual.trans hAlgebra
  have hCenteredSource : ProcessIndistinguishable mu
      (commonStopCenteredStoppedSource S alpha)
      (fun t omega => Mfixed t omega + Ap t omega) :=
    hSignedSource.trans hSignedToFixed
  refine ⟨Mfixed, {
    Mfixed_eq_def := by rfl
    Mfixed_martingale := hMfixed
    Mfixed_stronglyAdapted := hMfixedAdapted
    Mfixed_rightContinuous := hMfixedRight
    Mfixed_leftLimits := hMfixedLeft
    Mfixed_zero := hMfixedZero
    Mfixed_constant_after := hMfixedConstant
    Ap_isStronglyPredictable := hSigned.Ap_isStronglyPredictable
    Ap_isStronglyAdapted := hSigned.Ap_isStronglyPredictable.stronglyAdapted
    Ap_rightContinuous := hSigned.Ap_rightContinuous
    Ap_leftLimits := hSigned.Ap_leftLimits
    Ap_boundedVariation := hSigned.Ap_boundedVariation
    Ap_locallyBoundedVariation := hApLocal
    Ap_zero := hSigned.Ap_zero
    Ap_constant_after := hSigned.Ap_constant_after
    signedResidual_martingale := hSigned.residual_martingale
    signedResidual_indistinguishable_jordan := hResidualJordan
    raw_regularized_source_indistinguishable := hRawSource
    signed_source_indistinguishable := hSignedSource
    centeredSource_indistinguishable := hCenteredSource }⟩

end HorizonFactorialGrid

end FTAPTheorem42
