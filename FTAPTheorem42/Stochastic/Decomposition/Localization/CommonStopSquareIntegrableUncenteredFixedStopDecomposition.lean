/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopSquareIntegrableFixedStopDecomposition

/-!
# The square-integrable uncentered common-stop decomposition

The analytic rows decompose the source after subtracting its initial value.
This module adds that initial value back.  Its integrability is obtained from
the same random `L²` envelope used for the source, not from a deterministic
bound.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The uncentered package -/

structure SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
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
    {Mfixed : Process Ω}
    (hCentered : SquareIntegrableCommonStopFixedStopSpecialDecompositionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned Mfixed)
    (Msource : Process Ω) : Prop where
  Msource_eq_def : Msource = fun t omega => Mfixed t omega + S 0 omega
  Msource_martingale : Martingale Msource F mu
  Msource_stronglyAdapted : StronglyAdapted F Msource
  Msource_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Msource · omega) (Ici t) t
  Msource_leftLimits : ProcessHasLeftLimits Msource
  Msource_initial : Msource 0 =ᵐ[mu] S 0
  Msource_constant_after : ∀ t, T ≤ t → Msource t =ᵐ[mu] Msource T
  source_indistinguishable : ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess S alpha)
    (fun t omega => Msource t omega + Ap t omega)

namespace SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData

/-- Convert an uncentered square-integrable fixed-stop package to the standard
special-semimartingale decomposition record. -/
def toSpecialSemimartingaleDecomposition
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
    {Mfixed : Process Ω}
    (hCentered : SquareIntegrableCommonStopFixedStopSpecialDecompositionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned Mfixed)
    {Msource : Process Ω}
    (hData : SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned hCentered Msource) :
    SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S alpha) F mu := by
  let D : SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S alpha) F mu := {
    martingalePart := Msource
    finiteVariationPart := Ap
    martingalePart_isLocalMartingale :=
      ProbabilityTheory.Locally.of_prop hData.Msource_martingale
    finiteVariationPart_isPredictable := hCentered.Ap_isStronglyPredictable
    finiteVariationPart_isLocallyBoundedVariation :=
      fun omega => hCentered.Ap_locallyBoundedVariation omega
    decomposition := hData.source_indistinguishable }
  exact D

end SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData

/-! ## The envelope-derived initial-value lemmas -/

theorem squareIntegrableSource_initial_integrable
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    Integrable (S 0) mu := by
  have hξNorm : MemLp (fun omega => ‖ξ omega‖) (2 : ENNReal) mu := hξ.norm
  apply Integrable.mono' (hξNorm.integrable (by norm_num))
    ((hSAdapted 0).mono (F.le 0)).aestronglyMeasurable
  filter_upwards [hSBound] with omega hBound
  simpa only [Real.norm_eq_abs] using hBound 0

theorem squareIntegrableSource_initial_constant_martingale
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    Martingale (fun _ omega => S 0 omega) F mu := by
  have hS0F0 : StronglyMeasurable[F 0] (S 0) := hSAdapted 0
  have hS0Fbot : StronglyMeasurable[F ⊥] (S 0) := by
    simpa using hS0F0
  exact martingale_const_fun F mu hS0Fbot
    (squareIntegrableSource_initial_integrable hSAdapted ξ hξ hSBound)

/-! ## Construction from the centered package -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableCommonStopUncenteredFixedStopSpecialDecomposition_of_centered
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
    {Mfixed : Process Ω}
    (hCentered : SquareIntegrableCommonStopFixedStopSpecialDecompositionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned Mfixed)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    ∃ Msource : Process Ω,
      SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
        hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned hCentered Msource ∧
      Nonempty (SpecialSemimartingaleDecomposition
        (MeasureTheory.stoppedProcess S alpha) F mu) := by
  let Msource : Process Ω := fun t omega => Mfixed t omega + S 0 omega
  have hInitialMartingale : Martingale (fun _ omega => S 0 omega) F mu :=
    squareIntegrableSource_initial_constant_martingale hSAdapted ξ hξ hSBound
  have hMsource : Martingale Msource F mu := by
    dsimp [Msource]
    exact hCentered.Mfixed_martingale.add hInitialMartingale
  have hMsourceAdapted : StronglyAdapted F Msource := hMsource.stronglyAdapted
  have hMsourceRight : ∀ omega t,
      ContinuousWithinAt (Msource · omega) (Ici t) t := by
    intro omega t
    dsimp [Msource]
    exact hCentered.Mfixed_rightContinuous omega t |>.add continuousWithinAt_const
  have hMsourceLeft : ProcessHasLeftLimits Msource := by
    have hInitialLeft : ProcessHasLeftLimits (fun _ omega => S 0 omega) := by
      intro omega t
      apply tendsto_leftLim_of_tendsto
      exact ⟨S 0 omega, tendsto_const_nhds⟩
    dsimp [Msource]
    exact hCentered.Mfixed_leftLimits.add hInitialLeft
  have hMsourceInitial : Msource 0 =ᵐ[mu] S 0 := by
    filter_upwards [hCentered.Mfixed_zero] with omega hMzero
    dsimp [Msource]
    rw [hMzero]
    simp
  have hMsourceConstant : ∀ t, T ≤ t → Msource t =ᵐ[mu] Msource T := by
    intro t ht
    filter_upwards [hCentered.Mfixed_constant_after t ht] with omega hMfixed
    dsimp [Msource]
    rw [hMfixed]
  have hSource : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess S alpha)
      (fun t omega => Msource t omega + Ap t omega) := by
    have hLeft : ProcessIndistinguishable mu
        (fun t omega => commonStopCenteredStoppedSource S alpha t omega + S 0 omega)
        (MeasureTheory.stoppedProcess S alpha) := by
      filter_upwards [] with omega
      intro t
      dsimp [commonStopCenteredStoppedSource]
      ring
    have hRight : ProcessIndistinguishable mu
        (fun t omega => (Mfixed t omega + Ap t omega) + S 0 omega)
        (fun t omega => Msource t omega + Ap t omega) := by
      filter_upwards [] with omega
      intro t
      dsimp [Msource]
      ring
    have hAdd := ProcessIndistinguishable.add
      hCentered.centeredSource_indistinguishable
      (ProcessIndistinguishable.refl mu (fun _ omega => S 0 omega))
    exact hLeft.symm.trans (hAdd.trans hRight)
  let hData : SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned hCentered Msource := {
    Msource_eq_def := by rfl
    Msource_martingale := hMsource
    Msource_stronglyAdapted := hMsourceAdapted
    Msource_rightContinuous := hMsourceRight
    Msource_leftLimits := hMsourceLeft
    Msource_initial := hMsourceInitial
    Msource_constant_after := hMsourceConstant
    source_indistinguishable := hSource }
  exact ⟨Msource, hData, ⟨hData.toSpecialSemimartingaleDecomposition
    hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned hCentered⟩⟩

/-! ## Direct endpoint from regularized raw data -/

omit [SigmaFiniteFiltration mu F] in
theorem
exists_squareIntegrableCommonStopUncenteredFixedStopSpecialDecomposition_of_commonStopRegularized
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
    (hSAdapted : StronglyAdapted F S)
    (ξ : Ω → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖) :
    ∃ pkg : SquareIntegrablePredictableCompensatorJordanPackage
        (F := F) (mu := mu) Aplus Aminus T,
      ∃ pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData pkg,
        ∃ Ap : Process Ω,
          ∃ hSigned : SquareIntegrablePredictableCompensatorJordanSignedProjectionData
            hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap,
            ∃ Mfixed : Process Ω,
              ∃ hCentered : SquareIntegrableCommonStopFixedStopSpecialDecompositionData
                hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned Mfixed,
                ∃ Msource : Process Ω,
                  ∃ _hData :
                    SquareIntegrableCommonStopUncenteredFixedStopSpecialDecompositionData
                      hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned
                        hCentered Msource,
                    Nonempty (SpecialSemimartingaleDecomposition
                      (MeasureTheory.stoppedProcess S alpha) F mu) := by
  obtain ⟨pkg⟩ :=
    exists_squareIntegrablePredictableCompensatorJordanPackage_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨pair⟩ := pkg.dualProjection hUsual
  obtain ⟨Ap, hSigned⟩ :=
    exists_squareIntegrableJordanSignedProjection_of_pair
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair
  obtain ⟨Mfixed, hCentered⟩ :=
    exists_squareIntegrableCommonStopFixedStopSpecialDecomposition_of_signed
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned
  obtain ⟨Msource, hData, ⟨D⟩⟩ :=
    exists_squareIntegrableCommonStopUncenteredFixedStopSpecialDecomposition_of_centered
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg pair hSigned
        hCentered hSAdapted ξ hξ hSBound
  exact ⟨pkg, pair, Ap, hSigned, Mfixed, hCentered, Msource, hData, ⟨D⟩⟩

end HorizonFactorialGrid

end FTAPTheorem42
