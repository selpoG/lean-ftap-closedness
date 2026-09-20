/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalExhaustion
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopUncenteredFixedStopDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRestoppedDecomposition

/-!
# The full fixed-stop family used by the global exhaustion

The common-stop exhaustion must retain the stopping time selected by the same
finite-horizon construction that produced its decomposition.  This module
packages one complete uncentered fixed-stop producer output at every level,
then applies the Borel--Cantelli/tail-infimum construction to that exact
family.  Re-stopping is performed only after the family has been selected.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## One complete producer output -/

/-- All dependent witnesses returned by the full common-stop producer at one
finite horizon.  In particular, `alpha`, `hReg`, and `hData` belong to one
and the same producer invocation. -/
structure CommonStopUncenteredFixedStopLevelData
    {S : Process Ω}
    (T : NNReal) (eta : Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) where
  a : Real
  u : ∀ n, TailConvexWeights n
  selection : Nat → Nat
  alphaSeq : Nat → Ω → WithTop NNReal
  alpha : Ω → WithTop NNReal
  R : Ω → Real
  endpoint : CommonStoppedRowsEndpoint
    (S := S) (F := F) (mu := mu) (eta := eta)
    u selection a T alphaSeq alpha R hUsual source
  v : ∀ n, TailConvexWeights n
  Z : Lp Real 2 mu
  Nbar : Nat → Process Ω
  Bbar : Nat → Process Ω
  Xbar : Nat → Process Ω
  M : Process Ω
  cutoff : Nat → Nat
  A : Process Ω
  bad : Set Ω
  Atilde : Process Ω
  Aplus : Process Ω
  Aminus : Process Ω
  cumulativeVariation : Process Ω
  hReg : CommonStopRegularizedRawDecompositionData
    (S := S) (F := F) (mu := mu) (eta := eta)
    (u := u) (selection := selection) (a := a) (T := T)
    (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
    (hUsual := hUsual) (source := source)
    (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
    (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
    endpoint bad Atilde Aplus Aminus cumulativeVariation
  pair : CommonStopJordanDualProjectionPairData
    endpoint bad Atilde Aplus Aminus cumulativeVariation hReg
  Ap : Process Ω
  hSigned : CommonStopJordanSignedProjectionData
    endpoint bad Atilde Aplus Aminus cumulativeVariation hReg pair Ap
  Mfixed : Process Ω
  hCentered : CommonStopFixedStopSpecialDecompositionData
    endpoint hReg pair hSigned Mfixed
  Msource : Process Ω
  hData : CommonStopUncenteredFixedStopSpecialDecompositionData
    endpoint hReg pair hSigned hCentered Msource

namespace CommonStopUncenteredFixedStopLevelData

/-- The producer output can be assembled once from the regularized raw
decomposition and its direct uncentered fixed-stop consumer. -/
theorem nonemptyData
    {S : Process Ω}
    (T : NNReal) {eta : Real} (heta : 0 < eta)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) :
    Nonempty (CommonStopUncenteredFixedStopLevelData T eta hUsual source) := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
      Nbar, Bbar, Xbar, M, cutoff, A, bad, Atilde, Aplus, Aminus,
      cumulativeVariation, hReg⟩ :=
    exists_commonStop_regularizedRawDecomposition hUsual
      source.isSemimartingale source T heta
  obtain ⟨pair, Ap, hSigned, Mfixed, hCentered, Msource, hData,
      _hDecomposition⟩ :=
    exists_commonStopUncenteredFixedStopSpecialDecomposition_of_commonStopRegularized
      (F := F) (mu := mu) endpoint hReg
  exact ⟨{
    a := a
    u := u
    selection := selection
    alphaSeq := alphaSeq
    alpha := alpha
    R := R
    endpoint := endpoint
    v := v
    Z := Z
    Nbar := Nbar
    Bbar := Bbar
    Xbar := Xbar
    M := M
    cutoff := cutoff
    A := A
    bad := bad
    Atilde := Atilde
    Aplus := Aplus
    Aminus := Aminus
    cumulativeVariation := cumulativeVariation
    hReg := hReg
    pair := pair
    Ap := Ap
    hSigned := hSigned
    Mfixed := Mfixed
    hCentered := hCentered
    Msource := Msource
    hData := hData }⟩

end CommonStopUncenteredFixedStopLevelData

/-! ## The exact family and its direct tail-infimum consumer -/

/-- A level-indexed family of complete producer outputs. -/
structure CommonStopUncenteredFixedStopFamily
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) where
  level : ∀ m, CommonStopUncenteredFixedStopLevelData
    (T m) (eta m) hUsual source

theorem exists_commonStopUncenteredFixedStopFamily
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (heta : ∀ m, 0 < eta m) :
    Nonempty (CommonStopUncenteredFixedStopFamily T eta hUsual source) := by
  let level : ∀ m, CommonStopUncenteredFixedStopLevelData
      (T m) (eta m) hUsual source := fun m =>
    Classical.choice
      (CommonStopUncenteredFixedStopLevelData.nonemptyData
        (T m) (heta m) hUsual source)
  exact ⟨{ level := level }⟩

/-- The exact full fixed-stop family, its tail-infimum localizer, and the
re-stopped decomposition at each localizing time.  The re-stopped package at
index `n` is obtained from the stored level-`n` uncentered package, so no
second producer invocation and no exchange of stopping with convexification
is involved. -/
structure CommonStopUncenteredFixedStopExhaustionData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal) where
  isLocalizingSequence : ProbabilityTheory.IsLocalizingSequence F tau mu
  alpha_stopping : ∀ n, IsStoppingTime F ((family.level n).alpha)
  alpha_le_horizon : ∀ n ω, (family.level n).alpha ω ≤ (T n : WithTop NNReal)
  alpha_bad_measure : ∀ n,
    mu {ω | (family.level n).alpha ω < (T n : WithTop NNReal)} ≤
      ENNReal.ofReal (4 * eta n)
  tau_le_alpha : ∀ n ω, tau n ω ≤ (family.level n).alpha ω
  tau_le_horizon : ∀ n ω, tau n ω ≤ (T n : WithTop NNReal)
  tau_le_all_alpha : ∀ n m ω, n ≤ m → tau n ω ≤ (family.level m).alpha ω
  Mρ : ∀ _n, Process Ω
  Aρ : ∀ _n, Process Ω
  restopped : ∀ n,
    CommonStopUncenteredRestoppedSpecialDecompositionData
      (family.level n).endpoint
      (family.level n).hReg
      (family.level n).pair
      (family.level n).hSigned
      (family.level n).hCentered
      (family.level n).hData
      (tau n)
      ((isLocalizingSequence.isStoppingTime n))
      (tau_le_alpha n)
      (Mρ n) (Aρ n)

/-! The stopped martingale and finite-variation coordinates remain explicit
fields so subsequent overlap consumers can use their stronger certificates. -/

theorem exists_commonStopUncenteredFixedStopExhaustion
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hT : Tendsto (fun n => (T n : WithTop NNReal)) atTop (𝓝 ⊤))
    (heta : ∀ m, 0 < eta m)
    (hEta : (∑' m, ENNReal.ofReal (4 * eta m)) ≠ ⊤)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) :
    ∃ family : CommonStopUncenteredFixedStopFamily T eta hUsual source,
      ∃ tau : Nat → Ω → WithTop NNReal,
        Nonempty (CommonStopUncenteredFixedStopExhaustionData
          T eta hUsual source family tau) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨family⟩ :=
    exists_commonStopUncenteredFixedStopFamily T eta hUsual source heta
  let alpha : Nat → Ω → WithTop NNReal := fun m ω =>
    (family.level m).alpha ω
  let boundedFamily : BoundedStoppingTimeFamily (F := F) (mu := mu)
      T alpha := {
    horizon_tendsto := hT
    isStoppingTime := fun m => (family.level m).endpoint.alpha_stopping
    le_horizon := fun m ω =>
      ((family.level m).endpoint.alpha_le_alphaSeq m ω).trans
        ((family.level m).endpoint.alphaSeq_le_T m ω)
    bad_measure_sum := by
      apply ne_top_of_le_ne_top hEta
      exact ENNReal.tsum_le_tsum (fun m => by
        simpa only [alpha] using (family.level m).endpoint.alpha_measure) }
  have hAlphaStopping : ∀ n, IsStoppingTime F ((family.level n).alpha) := by
    intro n
    exact (family.level n).endpoint.alpha_stopping
  have hAlphaLeHorizon : ∀ n ω,
      (family.level n).alpha ω ≤ (T n : WithTop NNReal) := by
    intro n ω
    exact (boundedFamily.le_horizon n ω)
  have hAlphaMeasure : ∀ n,
      mu {ω | (family.level n).alpha ω < (T n : WithTop NNReal)} ≤
        ENNReal.ofReal (4 * eta n) := by
    intro n
    exact (family.level n).endpoint.alpha_measure
  obtain ⟨tau, hTau, hTauAlpha, hTauHorizon, hTauAll⟩ :=
    boundedFamily.exists_tailInf_localizingSequence
  have hTauAlpha' : ∀ n ω, tau n ω ≤ (family.level n).alpha ω := by
    intro n ω
    simpa only [alpha] using hTauAlpha n ω
  have hTauAll' : ∀ n m ω, n ≤ m →
      tau n ω ≤ (family.level m).alpha ω := by
    intro n m ω hnm
    simpa only [alpha] using hTauAll n m ω hnm
  let hStop : ∀ n, IsStoppingTime F (tau n) :=
    fun n => hTau.isStoppingTime n
  choose Mρ Aρ hRestopped _hRestoppedDecomposition using fun n =>
    exists_commonStopUncenteredRestoppedSpecialDecompositionData
      (F := F) (mu := mu)
      (family.level n).endpoint
      (family.level n).hReg
      (family.level n).pair
      (family.level n).hSigned
      (family.level n).hCentered
      (family.level n).hData
      (tau n) (hStop n) (hTauAlpha' n)
  let data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau := {
    isLocalizingSequence := hTau
    alpha_stopping := hAlphaStopping
    alpha_le_horizon := hAlphaLeHorizon
    alpha_bad_measure := hAlphaMeasure
    tau_le_alpha := hTauAlpha'
    tau_le_horizon := hTauHorizon
    tau_le_all_alpha := hTauAll'
    Mρ := Mρ
    Aρ := Aρ
    restopped := hRestopped }
  exact ⟨family, tau, ⟨data⟩⟩

end HorizonFactorialGrid

end FTAPTheorem42
