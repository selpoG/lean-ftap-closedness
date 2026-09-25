/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore

/-!
# Source-independent centered fixed-stop algebra

This module contains the part of the fixed-stop construction which only uses
process algebra.  In particular, it does not refer to a bounded source or to
the construction of the predictable projections.  The bounded and the
square-integrable routes provide the hypotheses below and retain their own
data certificates.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The centered source -/

/-- The stopped source with its time-zero value removed. -/
noncomputable def commonStopCenteredStoppedSource
    (S : Process Ω) (alpha : Ω → WithTop NNReal) : Process Ω :=
  fun t omega => MeasureTheory.stoppedProcess S alpha t omega - S 0 omega

/-! ## A common certificate for the centered algebra -/

omit [SigmaFiniteFiltration mu F] in
structure PredictableCenteredFixedStopCoreData
    {S : Process Ω} {alpha : Ω → WithTop NNReal}
    {M Atilde Aplus Aminus VpPlus VpMinus Ap : Process Ω}
    {T : NNReal} (Mfixed : Process Ω) : Prop where
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
      (Aplus t omega - VpPlus t omega) -
        (Aminus t omega - VpMinus t omega))
  raw_regularized_source_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => M t omega + Atilde t omega)
  signed_source_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => M t omega +
      (Ap t omega +
        ((Aplus t omega - VpPlus t omega) -
          (Aminus t omega - VpMinus t omega))))
  centeredSource_indistinguishable : ProcessIndistinguishable mu
    (commonStopCenteredStoppedSource S alpha)
    (fun t omega => Mfixed t omega + Ap t omega)

/-! ## Construction from component identities -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem exists_predictableCenteredFixedStopCore
    {S : Process Ω} {alpha : Ω → WithTop NNReal}
    {M Atilde Aplus Aminus VpPlus VpMinus Ap : Process Ω}
    {T : NNReal}
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMZero : M 0 =ᵐ[mu] 0)
    (hMConstantAfter : ∀ t, T ≤ t → M t =ᵐ[mu] M T)
    (hAtildeRight : ∀ omega t,
      ContinuousWithinAt (Atilde · omega) (Ici t) t)
    (hAtildeLeft : ProcessHasLeftLimits Atilde)
    (hAtildeZero : Atilde 0 = 0)
    (hAtildeConstantAfter : ∀ omega t, T ≤ t →
      Atilde t omega = Atilde T omega)
    (hApPredictable : IsStronglyPredictable F Ap)
    (hApRight : ∀ omega t,
      ContinuousWithinAt (Ap · omega) (Ici t) t)
    (hApLeft : ProcessHasLeftLimits Ap)
    (hApBoundedVariation : ∀ omega,
      BoundedVariationOn (Ap · omega) Set.univ)
    (hApZero : Ap 0 = 0)
    (hApConstantAfter : ∀ omega t, T ≤ t →
      Ap t omega = Ap T omega)
    (hSignedResidualMartingale : Martingale
      (fun t omega => Atilde t omega - Ap t omega) F mu)
    (hSignedResidualIndistinguishableJordan : ProcessIndistinguishable mu
      (fun t omega => Atilde t omega - Ap t omega)
      (fun t omega =>
        (Aplus t omega - VpPlus t omega) -
          (Aminus t omega - VpMinus t omega)))
    (hRawSourceIndistinguishable : ProcessIndistinguishable mu
      (commonStopCenteredStoppedSource S alpha)
      (fun t omega => M t omega + Atilde t omega))
    (hSignedSourceIndistinguishable : ProcessIndistinguishable mu
      (commonStopCenteredStoppedSource S alpha)
      (fun t omega => M t omega +
        (Ap t omega +
          ((Aplus t omega - VpPlus t omega) -
            (Aminus t omega - VpMinus t omega))))) :
    ∃ Mfixed : Process Ω,
      PredictableCenteredFixedStopCoreData
        (F := F) (mu := mu) (S := S) (alpha := alpha)
        (M := M) (Atilde := Atilde) (Aplus := Aplus)
        (Aminus := Aminus) (VpPlus := VpPlus) (VpMinus := VpMinus)
        (Ap := Ap) (T := T) Mfixed := by
  let Mfixed : Process Ω := fun t omega =>
    M t omega + (Atilde t omega - Ap t omega)
  have hMfixed : Martingale Mfixed F mu := by
    dsimp [Mfixed]
    exact hM.add hSignedResidualMartingale
  have hMfixedAdapted : StronglyAdapted F Mfixed := hMfixed.stronglyAdapted
  have hResidualRight : ∀ omega t,
      ContinuousWithinAt
        ((fun s omega => Atilde s omega - Ap s omega) · omega)
        (Ici t) t := by
    intro omega t
    exact (hAtildeRight omega t).sub (hApRight omega t)
  have hMfixedRight : ∀ omega t,
      ContinuousWithinAt (Mfixed · omega) (Ici t) t := by
    intro omega t
    dsimp [Mfixed]
    exact (hMRight omega t).add (hResidualRight omega t)
  have hResidualLeft : ProcessHasLeftLimits
      (fun t omega => Atilde t omega - Ap t omega) :=
    hAtildeLeft.sub hApLeft
  have hMfixedLeft : ProcessHasLeftLimits Mfixed := by
    dsimp [Mfixed]
    exact hMLeft.add hResidualLeft
  have hMfixedZero : Mfixed 0 =ᵐ[mu] 0 := by
    filter_upwards [hMZero] with omega hMzero
    dsimp [Mfixed]
    rw [hMzero, congrFun hAtildeZero omega,
      congrFun hApZero omega]
    simp
  have hMfixedConstant : ∀ t, T ≤ t → Mfixed t =ᵐ[mu] Mfixed T := by
    intro t ht
    filter_upwards [hMConstantAfter t ht] with omega hM
    dsimp [Mfixed]
    rw [hM, hAtildeConstantAfter omega t ht,
      hApConstantAfter omega t ht]
  have hApAdapted : StronglyAdapted F Ap := hApPredictable.stronglyAdapted
  have hApLocal : ∀ omega,
      LocallyBoundedVariationOn (Ap · omega) Set.univ := by
    intro omega
    exact hApBoundedVariation omega |>.locallyBoundedVariationOn
  have hResidualJordan := hSignedResidualIndistinguishableJordan
  have hSignedToFixed : ProcessIndistinguishable mu
      (fun t omega => M t omega +
        (Ap t omega +
          ((Aplus t omega - VpPlus t omega) -
            (Aminus t omega - VpMinus t omega))))
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
    hSignedSourceIndistinguishable.trans hSignedToFixed
  exact ⟨Mfixed, {
    Mfixed_eq_def := by rfl
    Mfixed_martingale := hMfixed
    Mfixed_stronglyAdapted := hMfixedAdapted
    Mfixed_rightContinuous := hMfixedRight
    Mfixed_leftLimits := hMfixedLeft
    Mfixed_zero := hMfixedZero
    Mfixed_constant_after := hMfixedConstant
    Ap_isStronglyPredictable := hApPredictable
    Ap_isStronglyAdapted := hApAdapted
    Ap_rightContinuous := hApRight
    Ap_leftLimits := hApLeft
    Ap_boundedVariation := hApBoundedVariation
    Ap_locallyBoundedVariation := hApLocal
    Ap_zero := hApZero
    Ap_constant_after := hApConstantAfter
    signedResidual_martingale := hSignedResidualMartingale
    signedResidual_indistinguishable_jordan := hResidualJordan
    raw_regularized_source_indistinguishable := hRawSourceIndistinguishable
    signed_source_indistinguishable := hSignedSourceIndistinguishable
    centeredSource_indistinguishable := hCenteredSource }⟩

end HorizonFactorialGrid

end FTAPTheorem42
