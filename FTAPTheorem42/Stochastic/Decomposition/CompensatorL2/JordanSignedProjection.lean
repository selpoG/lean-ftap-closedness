/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.DualProjection
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore

/-!
# The square-integrable Jordan projection pair

The square-integrable Jordan package has already fixed the two component
packages.  This module applies the completed one-component projection to
each package without changing its rows, weights, cutoff, or candidate.  The
two components are independent, so their weights and cutoffs need not agree.

Only the two completed component certificates are recorded here.  In
particular, no signed projection or fixed-stop decomposition is introduced.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The two completed component certificates -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorJordanDualProjectionComponentData
    {V : Process Ω} {T : NNReal}
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T) : Type _ where
  badPred : Set Ω
  Vp : Process Ω
  projection : SquareIntegrablePredictableCompensatorDualProjectionData
    pkg badPred Vp

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
    {VPlus VMinus : Process Ω} {T : NNReal}
    (pkg : SquareIntegrablePredictableCompensatorJordanPackage
      (F := F) (mu := mu) VPlus VMinus T) : Type _ where
  plus : SquareIntegrablePredictableCompensatorJordanDualProjectionComponentData
    pkg.plus
  minus : SquareIntegrablePredictableCompensatorJordanDualProjectionComponentData
    pkg.minus

/-! ## Pair construction from one fixed Jordan package -/

namespace SquareIntegrablePredictableCompensatorJordanPackage

variable {VPlus VMinus : Process Ω} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
theorem dualProjection
    (pkg : SquareIntegrablePredictableCompensatorJordanPackage
      (F := F) (mu := mu) VPlus VMinus T)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty
      (SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
        pkg) := by
  obtain ⟨badPlus, VpPlus, hPlus⟩ := pkg.plus.dualProjection hUsual
  obtain ⟨badMinus, VpMinus, hMinus⟩ := pkg.minus.dualProjection hUsual
  exact ⟨{
    plus := {
      badPred := badPlus
      Vp := VpPlus
      projection := hPlus }
    minus := {
      badPred := badMinus
      Vp := VpMinus
      projection := hMinus } }⟩

end SquareIntegrablePredictableCompensatorJordanPackage

/-!
## The square-integrable signed projection

The two component certificates from the square-integrable Jordan projection
package are consumed without changing their rows, weights, cutoffs, or
candidates.  The source-independent signed-projection core supplies the
pathwise algebra and the residual martingale; this module only supplies the
regularized square-integrable Jordan data and the two fixed component
certificates.
-/

/-! ## Signed projection certificate -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorJordanSignedProjectionData
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
    (pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
      pkg)
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

/-! ## Construction from the two fixed component certificates -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableJordanSignedProjection_of_pair
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
    (pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
      pkg) :
    ∃ Ap : Process Ω,
      SquareIntegrablePredictableCompensatorJordanSignedProjectionData
        hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap := by
  obtain ⟨Ap, hCore⟩ := exists_predictableSignedProjectionCore
    (F := F) (mu := mu) (Atilde := Atilde) (Aplus := Aplus)
    (Aminus := Aminus) (VpPlus := pair.plus.Vp) (VpMinus := pair.minus.Vp)
    (T := T) hReg.Atilde_stronglyAdapted
    pair.plus.projection.projection_ready.predictable_version.Vp_isStronglyPredictable
    pair.minus.projection.projection_ready.predictable_version.Vp_isStronglyPredictable
    pair.plus.projection.projection_ready.predictable_version.Vp_rightContinuous
    pair.minus.projection.projection_ready.predictable_version.Vp_rightContinuous
    pair.plus.projection.projection_ready.predictable_version.Vp_leftLimits
    pair.minus.projection.projection_ready.predictable_version.Vp_leftLimits
    pair.plus.projection.projection_ready.predictable_version.Vp_nonnegative
    pair.minus.projection.projection_ready.predictable_version.Vp_nonnegative
    pair.plus.projection.projection_ready.predictable_version.Vp_monotone
    pair.minus.projection.projection_ready.predictable_version.Vp_monotone
    pair.plus.projection.projection_ready.predictable_version.Vp_zero
    pair.minus.projection.projection_ready.predictable_version.Vp_zero
    pair.plus.projection.projection_ready.predictable_version.Vp_constant_after
    pair.minus.projection.projection_ready.predictable_version.Vp_constant_after
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

end HorizonFactorialGrid

end FTAPTheorem42
