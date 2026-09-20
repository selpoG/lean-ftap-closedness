/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopFixedStopDecompositionCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.JordanSignedProjection
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy

/-!
# The square-integrable common-stop fixed-stop decomposition

This is the random-envelope consumer of the signed predictable projection.  It
uses the same stopped rows, regularized residual, Jordan projection pair, and
signed certificate throughout.  The construction itself is source-independent
apart from the data indices; in particular no deterministic source bound is
introduced.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The centered fixed-stop package -/

structure SquareIntegrableCommonStopFixedStopSpecialDecompositionData
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Ω → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Ω}
    {Vbound : Ω → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B Vbound L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω} {cutoff : Nat → Nat}
    {A : Process Ω}
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff)
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
      hNested A bad Atilde Aplus Aminus cumulativeVariation)
    {pkg : SquareIntegrablePredictableCompensatorJordanPackage
      (F := F) (mu := mu) Aplus Aminus T}
    (pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData pkg)
    {Ap : Process Ω}
    (hSigned : SquareIntegrablePredictableCompensatorJordanSignedProjectionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap)
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

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableCommonStopFixedStopSpecialDecomposition_of_signed
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Ω → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Ω}
    {Vbound : Ω → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B Vbound L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω} {cutoff : Nat → Nat}
    {A : Process Ω}
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff)
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
      hNested A bad Atilde Aplus Aminus cumulativeVariation)
    {pkg : SquareIntegrablePredictableCompensatorJordanPackage
      (F := F) (mu := mu) Aplus Aminus T}
    (pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData pkg)
    {Ap : Process Ω}
    (hSigned : SquareIntegrablePredictableCompensatorJordanSignedProjectionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap) :
    ∃ Mfixed : Process Ω,
      SquareIntegrableCommonStopFixedStopSpecialDecompositionData
        hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned Mfixed := by
  let Mfixed : Process Ω := fun t omega =>
    M t omega + (Atilde t omega - Ap t omega)
  have hCore : ∃ Mfixed : Process Ω,
      PredictableCenteredFixedStopCoreData
        (F := F) (mu := mu) (S := S) (alpha := alpha)
        (M := M) (Atilde := Atilde) (Aplus := Aplus)
        (Aminus := Aminus) (VpPlus := pair.plus.Vp)
        (VpMinus := pair.minus.Vp) (Ap := Ap) (T := T) Mfixed := by
    apply exists_predictableCenteredFixedStopCore
    · exact hNested.cadlag.M_martingale
    · exact hNested.cadlag.M_rightContinuous
    · exact hNested.cadlag.M_leftLimits
    · exact hNested.cadlag.M_zero
    · exact hNested.cadlag.M_constant_after
    · exact hReg.Atilde_rightContinuous
    · exact hReg.Atilde_hasLeftLimits
    · exact hReg.Atilde_zero
    · exact hReg.Atilde_constant_after
    · exact hSigned.Ap_isStronglyPredictable
    · exact hSigned.Ap_rightContinuous
    · exact hSigned.Ap_leftLimits
    · exact hSigned.Ap_boundedVariation
    · exact hSigned.Ap_zero
    · exact hSigned.Ap_constant_after
    · exact hSigned.residual_martingale
    · exact hSigned.residual_indistinguishable_jordan
    · exact hReg.stoppedSource_indistinguishable
    · have hAdd := ProcessIndistinguishable.add
        (ProcessIndistinguishable.refl mu (fun t omega => M t omega))
        hSigned.signed_decomposition
      exact hReg.stoppedSource_indistinguishable.trans hAdd
  obtain ⟨Mfixed, hCore⟩ := hCore
  refine ⟨Mfixed, ?_⟩
  refine {
    Mfixed_eq_def := ?_
    Mfixed_martingale := hCore.Mfixed_martingale
    Mfixed_stronglyAdapted := hCore.Mfixed_stronglyAdapted
    Mfixed_rightContinuous := hCore.Mfixed_rightContinuous
    Mfixed_leftLimits := hCore.Mfixed_leftLimits
    Mfixed_zero := hCore.Mfixed_zero
    Mfixed_constant_after := hCore.Mfixed_constant_after
    Ap_isStronglyPredictable := hCore.Ap_isStronglyPredictable
    Ap_isStronglyAdapted := hCore.Ap_isStronglyAdapted
    Ap_rightContinuous := hCore.Ap_rightContinuous
    Ap_leftLimits := hCore.Ap_leftLimits
    Ap_boundedVariation := hCore.Ap_boundedVariation
    Ap_locallyBoundedVariation := ?_
    Ap_zero := hCore.Ap_zero
    Ap_constant_after := hCore.Ap_constant_after
    signedResidual_martingale := hCore.signedResidual_martingale
    signedResidual_indistinguishable_jordan :=
      hCore.signedResidual_indistinguishable_jordan
    raw_regularized_source_indistinguishable :=
      hCore.raw_regularized_source_indistinguishable
    signed_source_indistinguishable := hCore.signed_source_indistinguishable
    centeredSource_indistinguishable := hCore.centeredSource_indistinguishable }
  · exact hCore.Mfixed_eq_def
  · intro omega
    exact hCore.Ap_boundedVariation omega |>.locallyBoundedVariationOn

end HorizonFactorialGrid

end FTAPTheorem42
