/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopFixedStopDecomposition
import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy

/-!
# The uncentered common-stop fixed-stop decomposition

The common-stop construction naturally produces the centered source
`stoppedProcess S alpha - S 0`.  This module puts back the time-zero value.
The martingale coordinate is therefore

```text
Msource = Mfixed + (fun _ omega => S 0 omega),
```

and is not asserted to start from zero.  The initial value is only identified
with `S 0` almost everywhere.  The integrability and measurability of this
constant process are obtained from the concrete bounded-source hypotheses.
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

/-! ## The uncentered package -/

/-- The data obtained by adding the integrable time-zero value of the source
to a centered common-stop fixed-stop decomposition. -/
structure CommonStopUncenteredFixedStopSpecialDecompositionData
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

namespace CommonStopUncenteredFixedStopSpecialDecompositionData

/-- Convert the uncentered package to the existing special-semimartingale
decomposition record. -/
def toSpecialSemimartingaleDecomposition
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
      endpoint hReg pair hSigned hCentered Msource) :
    SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S alpha) F mu := by
  let D : SpecialSemimartingaleDecomposition
      (MeasureTheory.stoppedProcess S alpha) F mu := {
    martingalePart := Msource
    finiteVariationPart := Ap
    martingalePart_isLocalMartingale :=
      ProbabilityTheory.Locally.of_prop hData.Msource_martingale
    finiteVariationPart_isPredictable :=
      hCentered.Ap_isStronglyPredictable
    finiteVariationPart_isLocallyBoundedVariation :=
      hCentered.Ap_locallyBoundedVariation
    decomposition := hData.source_indistinguishable }
  exact D

end CommonStopUncenteredFixedStopSpecialDecompositionData

/-! ## Adding the source's initial value -/

theorem source_initial_integrable
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) :
    Integrable (S 0) mu := by
  refine Integrable.of_bound (μ := mu)
    ((source.stronglyAdapted 0).mono (F.le 0)).aestronglyMeasurable
    (max source.bound 0) ?_
  filter_upwards [source.uniformBound] with omega hBound
  rw [Real.norm_eq_abs]
  exact (hBound 0).trans (le_max_left _ _)

theorem source_initial_constant_martingale
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (source : BoundedSemimartingaleSource S F mu) :
    Martingale (fun _ omega => S 0 omega) F mu := by
  have hS0F0 : StronglyMeasurable[F 0] (S 0) := source.stronglyAdapted 0
  have hS0Fbot : StronglyMeasurable[F ⊥] (S 0) := by
    simpa using hS0F0
  exact martingale_const_fun F mu
    hS0Fbot
    (source_initial_integrable source)

/-! ## Construction from the centered package -/

theorem exists_commonStopUncenteredFixedStopSpecialDecomposition_of_centered
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
      endpoint hReg pair hSigned Mfixed) :
    ∃ Msource : Process Ω,
      ∃ _hData : CommonStopUncenteredFixedStopSpecialDecompositionData
        endpoint hReg pair hSigned hCentered Msource,
        Nonempty (SpecialSemimartingaleDecomposition
          (MeasureTheory.stoppedProcess S alpha) F mu) := by
  let Msource : Process Ω := fun t omega => Mfixed t omega + S 0 omega
  have hInitialMartingale : Martingale (fun _ omega => S 0 omega) F mu :=
    source_initial_constant_martingale source
  have hMsource : Martingale Msource F mu := by
    dsimp [Msource]
    exact hCentered.Mfixed_martingale.add hInitialMartingale
  have hMsourceAdapted : StronglyAdapted F Msource := hMsource.stronglyAdapted
  have hMsourceRight : ∀ omega t,
      ContinuousWithinAt (Msource · omega) (Ici t) t := by
    intro omega t
    dsimp [Msource]
    exact hCentered.Mfixed_rightContinuous omega t |>.add
      continuousWithinAt_const
  have hMsourceLeft : ProcessHasLeftLimits Msource := by
    dsimp [Msource]
    exact hCentered.Mfixed_leftLimits.add
      (ProcessHasLeftLimits.timeConstant (S 0))
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
        (fun t omega =>
          commonStopCenteredStoppedSource S alpha t omega + S 0 omega)
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
  let hData : CommonStopUncenteredFixedStopSpecialDecompositionData
      endpoint hReg pair hSigned hCentered Msource := {
    Msource_eq_def := by rfl
    Msource_martingale := hMsource
    Msource_stronglyAdapted := hMsourceAdapted
    Msource_rightContinuous := hMsourceRight
    Msource_leftLimits := hMsourceLeft
    Msource_initial := hMsourceInitial
    Msource_constant_after := hMsourceConstant
    source_indistinguishable := hSource }
  exact ⟨Msource, hData, ⟨hData.toSpecialSemimartingaleDecomposition
    endpoint hReg pair hSigned hCentered⟩⟩

/-! ## Direct consumer for the regularized common-stop producer -/

theorem exists_commonStopUncenteredFixedStopSpecialDecomposition_of_commonStopRegularized
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
      endpoint bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ pair : CommonStopJordanDualProjectionPairData
        endpoint bad Atilde Aplus Aminus cumulativeVariation hReg,
      ∃ Ap : Process Ω,
        ∃ hSigned : CommonStopJordanSignedProjectionData
          endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap,
          ∃ Mfixed : Process Ω,
            ∃ hCentered : CommonStopFixedStopSpecialDecompositionData
              endpoint hReg pair hSigned Mfixed,
              ∃ Msource : Process Ω,
                ∃ _hData : CommonStopUncenteredFixedStopSpecialDecompositionData
                  endpoint hReg pair hSigned hCentered Msource,
                  Nonempty (SpecialSemimartingaleDecomposition
                    (MeasureTheory.stoppedProcess S alpha) F mu) := by
  obtain ⟨pair, Ap, hSigned⟩ :=
    exists_commonStopJordanSignedProjection_of_commonStopRegularized
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨Mfixed, hCentered⟩ :=
    exists_commonStopFixedStopSpecialDecomposition_of_signed
      (F := F) (mu := mu) endpoint hReg pair hSigned
  obtain ⟨Msource, hData, ⟨D⟩⟩ :=
    exists_commonStopUncenteredFixedStopSpecialDecomposition_of_centered
      (F := F) (mu := mu) endpoint hReg pair hSigned hCentered
  exact ⟨pair, Ap, hSigned, Mfixed, hCentered, Msource, hData, ⟨D⟩⟩

end HorizonFactorialGrid

end FTAPTheorem42
