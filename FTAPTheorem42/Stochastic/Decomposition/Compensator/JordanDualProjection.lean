/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.DualProjection

/-!
# Dual projections of the two Jordan components

The common-stop finite-variation residual has two nonnegative Jordan
components.  The finite-grid compensator construction is applied to those
components independently.  This module packages the two resulting complete
dual-projection certificates without identifying either their convex weights
or their diagonal subsequences.

No signed projection or fixed-stop special decomposition is formed here.  The
next consumer may therefore use both component certificates, including their
separate residual martingales and pathwise regularity data, before taking a
difference.
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

/-! ## One complete component certificate -/

structure CommonStopJordanDualProjectionComponentData
    {V : Process Ω} {T C : NNReal}
    (hV : BoundedIncreasingProcessData (F := F) V T C) : Type _ where
  hRows : FactorialGridPredictableCompensatorRowsData
    (F := F) (mu := mu) hV
  hControl : FactorialGridPredictableCompensatorRowControlData
    (F := F) (mu := mu) hV hRows
  hResidual : ∀ r,
    FactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows r
  w : ∀ n, TailConvexWeights n
  y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
    (2 : ENNReal)
  hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
    hV hRows hControl hResidual w y
  Z : Lp Real 2 mu
  M : Process Ω
  Pcad : Process Ω
  hCad : FactorialGridPredictableCompensatorCadlagCandidateData
    hV hRows hControl hResidual hCommon Z M Pcad
  bad : Set Ω
  Preg : Process Ω
  hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
    hCad bad Preg
  component : FactorialGridPredictableCompensatorCommonAEJordanComponentData
    hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg
  badPred : Set Ω
  Vp : Process Ω
  projection :
    FactorialGridPredictableCompensatorDualProjectionData
      (Ppred := predictableCompensatorLimsup w component.cutoff V F mu T C)
      (Vp := Vp)
      component.common_subsequence hCad bad Preg hReg badPred

/-! ## Pair certificate over one regularized common-stop decomposition -/

structure CommonStopJordanDualProjectionPairData
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
      endpoint bad Atilde Aplus Aminus cumulativeVariation) : Type _ where
  hPlus : BoundedIncreasingProcessData (F := F) Aplus T
    (commonStoppedRowsResidualVariationBound a source.bound).toNNReal
  plus : CommonStopJordanDualProjectionComponentData (F := F) (mu := mu) hPlus
  hMinus : BoundedIncreasingProcessData (F := F) Aminus T
    (commonStoppedRowsResidualVariationBound a source.bound).toNNReal
  minus : CommonStopJordanDualProjectionComponentData (F := F) (mu := mu) hMinus

/-! ## Direct producer -/

theorem exists_commonStopJordanDualProjectionPair
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
    Nonempty (CommonStopJordanDualProjectionPairData
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus cumulativeVariation hReg) := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
      badPlus, PregPlus, hRegPlus,
      hPlusComponent, hMinus, hRowsMinus, hControlMinus, hResidualMinus,
      wMinus, yMinus, hCommonMinus, ZMinus, MMinus, PcadMinus, hCadMinus,
      badMinus, PregMinus, hRegMinus, hMinusComponent⟩ :=
    exists_commonAEJordanComponents_of_commonStopJordanComponents
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus
        cumulativeVariation hReg
  let componentPlus := Classical.choice hPlusComponent
  let componentMinus := Classical.choice hMinusComponent
  obtain ⟨badPredPlus, VpPlus, hProjectionPlus⟩ :=
    exists_dualPredictableProjection_of_commonAEJordanComponent
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus
      wPlus yPlus hCommonPlus (Z := ZPlus) (M := MPlus) (Pcad := PcadPlus)
      hCadPlus badPlus PregPlus
      hRegPlus componentPlus hUsual
  obtain ⟨badPredMinus, VpMinus, hProjectionMinus⟩ :=
    exists_dualPredictableProjection_of_commonAEJordanComponent
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus
      wMinus yMinus hCommonMinus (Z := ZMinus) (M := MMinus) (Pcad := PcadMinus)
      hCadMinus badMinus PregMinus
      hRegMinus componentMinus hUsual
  exact ⟨{
    hPlus := hPlus
    plus := {
      hRows := hRowsPlus
      hControl := hControlPlus
      hResidual := hResidualPlus
      w := wPlus
      y := yPlus
      hCommon := hCommonPlus
      Z := ZPlus
      M := MPlus
      Pcad := PcadPlus
      hCad := hCadPlus
      bad := badPlus
      Preg := PregPlus
      hReg := hRegPlus
      component := componentPlus
      badPred := badPredPlus
      Vp := VpPlus
      projection := hProjectionPlus }
    hMinus := hMinus
    minus := {
      hRows := hRowsMinus
      hControl := hControlMinus
      hResidual := hResidualMinus
      w := wMinus
      y := yMinus
      hCommon := hCommonMinus
      Z := ZMinus
      M := MMinus
      Pcad := PcadMinus
      hCad := hCadMinus
      bad := badMinus
      Preg := PregMinus
      hReg := hRegMinus
      component := componentMinus
      badPred := badPredMinus
      Vp := VpMinus
      projection := hProjectionMinus }}⟩

end HorizonFactorialGrid

end FTAPTheorem42
