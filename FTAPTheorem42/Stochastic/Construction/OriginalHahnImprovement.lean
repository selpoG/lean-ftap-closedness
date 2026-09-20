/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.RealizedPairHahnAdmissibility
import FTAPTheorem42.Interface.HahnData

/-! # Hahn improvement data and orientation in the original market

Extract the numerical data and terminal claims from an admissible actual
strategy, then orient a finite-variation event toward one of the two improvements.
-/

/-! ## Construction from an admissible strategy -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Extract the numerical data and terminal claims of the same actual
witness. No new component decomposition is chosen. -/
theorem originalHahnImprovement_of_admissibleControl
    (source : BoundedSemimartingaleSource S F μ)
    (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (T : NNReal) (hT : 0 < T) (b δ : Real)
    (hControl : OriginalPairHahnAdmissibleControl source hUsual R V D E hDP hEP T hT b δ) :
    Nonempty (OriginalHahnImprovement source Q V.gain (D.N - E.N) (D.A - E.A) T b δ) := by
  let _ := hUsual.rightContinuous
  let hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  let W := R.sub hS V
  let B := R.subDecomposition hS V D E
  have hBP : IsStronglyPredictable F B.A := hDP.add hEP.neg
  let G := W.componentSource source.rightContinuous B hBP
  let hGL := W.componentSource_martingalePart_hasLeftLimits source.rightContinuous B hBP
  obtain ⟨L, hL, _hGraph, hInc, _hTest, hCap, hBad, _hLower, _hTerminal, hPasted⟩ := hControl
  change L.val = G at hL
  let X := actualHahnOfDeterministicStop hGL L T hT
  have hLL : ProcessHasLeftLimits L.val.stochasticIntegral := by
    rw [hL]
    exact W.gain_hasLeftLimits
  obtain ⟨_hXL, hX0, hN0, _hJump⟩ := actualHahnOfDeterministicStop_semantics hGL L hLL T hT
  refine ⟨{
    gain := X.val.stochasticIntegral
    martingale := X.val.martingalePart
    finiteVariation := X.val.finiteVariationPart
    martingale_adapted := X.val.martingalePart_isStronglyAdapted
    martingale_right := X.val.martingalePart_isRightContinuous
    finiteVariation_adapted := X.val.finiteVariationPart_isPredictable.stronglyAdapted
    decomposition := X.val.integral_decomposition
    finiteVariation_zero := ?_
    increment := hInc
    martingale_bound := hCap
    downside_probability := hBad
    terminal_mem := fun U hU => (hPasted U hU).2.2 }⟩
  filter_upwards [hX0, hN0, X.val.integral_decomposition] with ω hx hn hd
  have h0 := hd 0
  change X.val.stochasticIntegral 0 ω = 0 at hx
  change X.val.martingalePart 0 ω = 0 at hn
  change X.val.finiteVariationPart 0 ω = 0
  linarith

end FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Variation bounds and orientation -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket.OriginalHahnImprovement

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F]
  {source : BoundedSemimartingaleSource S F μ}
  {Y Y' M M' A A' : Process Ω} {T : NNReal} {b b' δ δ' : Real}

omit [IsProbabilityMeasure Q] in
/-- Two opposite actual Hahn constructions control the same original
variation. Their auxiliary sources and martingale parts may differ. -/
theorem variation_le
    (P : OriginalHahnImprovement source Q Y M A T b δ)
    (R : OriginalHahnImprovement source Q Y' M' A' T b' δ')
    (hOpp : A' = -A)
    (hA : ∀ ω, LocallyBoundedVariationOn (A · ω) univ)
    (hAR : ∀ ω t, ContinuousWithinAt (A · ω) (Ici t) t) :
    ∀ᵐ ω ∂Q, finiteHorizonPathVariation A hA T ω ≤
      P.finiteVariation T ω + R.finiteVariation T ω := by
  filter_upwards [P.increment, R.increment, P.finiteVariation_zero,
    R.finiteVariation_zero] with ω hp hr hp0 hr0
  have hpMono : Monotone (P.finiteVariation · ω) := fun a c hac => sub_nonneg.mp (hp a c hac).1
  have hrMono : Monotone (R.finiteVariation · ω) := fun a c hac => sub_nonneg.mp (hr a c hac).1
  have h := finiteHorizonPathVariation_le_of_two_monotone_controls A hA hAR
    (P.finiteVariation · ω) (R.finiteVariation · ω) T ω hpMono hrMono
    (fun a c hac hc => by
      simpa only [min_eq_left hc, min_eq_left (hac.trans hc)] using (hp a c hac).2)
    (fun a c hac hc => by
      have h := (hr a c hac).2
      rw [congrFun (congrFun hOpp (min c T)) ω,
        congrFun (congrFun hOpp (min a T)) ω] at h
      simp only [Pi.neg_apply, min_eq_left hc, min_eq_left (hac.trans hc)] at h
      linarith)
  simpa only [hp0, hr0, Pi.zero_apply, sub_zero] using h

/-- A positive-probability variation event gives one of the two actual
improvements a positive-probability event at half the level and mass. -/
theorem exists_orientation
    (P : OriginalHahnImprovement source Q Y M A T b δ)
    (R : OriginalHahnImprovement source Q Y' M' A' T b' δ')
    (hOpp : A' = -A)
    (hA : ∀ ω, LocallyBoundedVariationOn (A · ω) univ)
    (hAR : ∀ ω t, ContinuousWithinAt (A · ω) (Ici t) t)
    {α : Real} (hMass : α < Q.real {ω | α < finiteHorizonPathVariation A hA T ω}) :
    α / 2 < Q.real {ω | α / 2 < P.finiteVariation T ω} ∨
      α / 2 < Q.real {ω | α / 2 < R.finiteVariation T ω} := by
  have hSubset : ∀ᵐ ω ∂Q,
      ω ∈ {ω | α < finiteHorizonPathVariation A hA T ω} →
      ω ∈ {ω | α / 2 < P.finiteVariation T ω} ∪
        {ω | α / 2 < R.finiteVariation T ω} := by
    filter_upwards [P.variation_le R hOpp hA hAR] with ω hω hBig
    change α / 2 < P.finiteVariation T ω ∨ α / 2 < R.finiteVariation T ω
    by_contra h
    push Not at h
    change α < finiteHorizonPathVariation A hA T ω at hBig
    linarith
  have hBound := (ENNReal.toReal_mono (measure_ne_top Q _)
    (measure_mono_ae hSubset)).trans (measureReal_union_le _ _)
  change Q.real {ω | α < finiteHorizonPathVariation A hA T ω} ≤
    Q.real {ω | α / 2 < P.finiteVariation T ω} +
      Q.real {ω | α / 2 < R.finiteVariation T ω} at hBound
  by_cases hp : α / 2 < Q.real {ω | α / 2 < P.finiteVariation T ω}
  · exact Or.inl hp
  · exact Or.inr (by linarith [le_of_not_gt hp])

end FTAPTheorem42.BoundedSourceIntegralMarket.OriginalHahnImprovement

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Generate both original-market Hahn improvements and orient variation events -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Apply the actual construction in both directions. This consumes the
finite-horizon variation comparison with no common auxiliary source assumption. -/
theorem original_pair_hahn_orientedImprovement
    (source : BoundedSemimartingaleSource S F μ)
    (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (T : NNReal) (hT : 0 < T) (b δ : Real)
    (hForward : OriginalPairHahnAdmissibleControl source hUsual R V D E hDP hEP T hT b δ)
    (hReverse : OriginalPairHahnAdmissibleControl source hUsual V R E D hEP hDP T hT b δ) :
    OriginalPairHahnOrientedImprovement source R.gain V.gain D E T b δ := by
  obtain ⟨P⟩ := originalHahnImprovement_of_admissibleControl source hUsual
    R V D E hDP hEP T hT b δ hForward
  obtain ⟨P'⟩ := originalHahnImprovement_of_admissibleControl source hUsual
    V R E D hEP hDP T hT b δ hReverse
  refine ⟨P, P', fun α hMass => ?_⟩
  have hOpp : E.A - D.A = -(D.A - E.A) := (neg_sub D.A E.A).symm
  exact P.exists_orientation P' hOpp
    (fun ω a c ha hc => by
          simpa only [Pi.sub_apply, sub_eq_add_neg] using
            boundedVariationOn_add (D.variationA ω a c ha hc)
              (boundedVariationOn_neg (E.variationA ω a c ha hc)))
    (fun ω t => (D.rightA ω t).sub (E.rightA ω t)) hMass

end FTAPTheorem42.BoundedSourceIntegralMarket
