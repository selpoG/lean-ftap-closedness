/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.CompletedRowBridge
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.ControlConvergence
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessCauchy
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessFastSubsequence
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessLocalization

/-! # Unit-bounded elementary approximation of completed integrals

The same elementary approximants satisfy both coefficient controls and the
pointwise unit bound. Thus an estimate uniform over elementary tests can be
passed to a completed integral without a presentation-dependent constant.
-/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open PredictableUnitBoundedElementaryDensity BoundedMartingaleQuadraticEnergy.Data

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : SIntegrableStrategy D}
  {T : NNReal} {E : SIntegrableFiniteVariationBridge G}

/-- A completed coefficient with a unit-bounded represented integrand is
approximated by actual unit elementary tests in the process Émery topology. -/
theorem exists_unitElementarySequence_gain_martingale_emery
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart T)
    (hM : Martingale G.martingalePart F μ) (hMT : MemLp (G.martingalePart T) 2 μ)
    (K : FiniteHorizonM2ACoefficient E Q) (hK : ∀ t ω, |K.integrand t ω| ≤ 1) :
    ∃ J : Nat → BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      ElementaryEmeryConverges μ F
        (fun n => (J n).strategy.finiteHorizonGain G.stochasticIntegral T)
        (finiteHorizonCompletedM2AGain hUsual T Q E hM hMT K) ∧
      ElementaryEmeryConverges μ F
        (fun n => (J n).strategy.finiteHorizonGain G.martingalePart T)
        (finiteHorizonCompletedMartingalePart hUsual T Q hM hMT K) := by
  let _ := Q.predictableEnergyMeasure_isFinite
  let L : FiniteHorizonM2ACoefficient E Q := {
    coefficient := Function.uncurry K.integrand
    coefficient_isStronglyMeasurable := K.integrand_isStronglyPredictable
    coefficient_memLp_variation := K.integrand_memLp_variation
    coefficient_memLp_energy := K.integrand_memLp_energy }
  have hOff : ∀ p, p ∉ FiniteHorizonPredictableIndicatorRing.horizonCarrier
      (Omega := Ω) T → K.integrand p.1 p.2 = 0 :=
    horizonRestrictedTest_zero_off_horizon (Function.curry K.coefficient)
      K.coefficient_isStronglyMeasurable
  let ε : Nat → ENNReal := fun n => ((n + 1 : Nat) : ENNReal)⁻¹
  have hε n : ε n ≠ 0 := ENNReal.inv_ne_zero.mpr (by finiteness)
  have hRows n :=
    exists_boundedPredictableElementaryMultiplier_unit_approximation_with_coefficientBound
      T Q.predictableEnergyMeasure (canonicalVariationMeasure E)
      K.integrand K.integrand_isStronglyPredictable hK hOff (hε n)
  choose J hJq hJv _hJO C hC using hRows
  have hεLim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hqLim : Tendsto (fun n => eLpNorm
      (L.coefficient - Function.uncurry (J n).strategy.integrand) 2
      Q.predictableEnergyMeasure) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεLim
      (fun _ => zero_le)
    intro n
    dsimp only
    rw [eLpNorm_sub_comm (μ := Q.predictableEnergyMeasure)]
    exact hJq n
  have hvLim : Tendsto (fun n => eLpNorm
      (L.coefficient - Function.uncurry (J n).strategy.integrand) 1
      (canonicalVariationMeasure E)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεLim
      (fun _ => zero_le)
    intro n
    dsimp only
    rw [eLpNorm_sub_comm (μ := canonicalVariationMeasure E)]
    exact hJv n
  have hConv := finiteHorizonElementaryGain_emery_of_controls hUsual Q hM hMT
    (fun n => (J n).strategy) C hC L hvLim hqLim
  have hLK : L.integrand = K.integrand := by
    funext t ω
    change (finiteHorizonPredictableStrip T).indicator
      ((finiteHorizonPredictableStrip T).indicator K.coefficient) (t, ω) =
        (finiteHorizonPredictableStrip T).indicator K.coefficient (t, ω)
    rw [Set.indicator_indicator, Set.inter_self]
  have hMConv := finiteHorizonElementaryMartingale_emery_of_controls hUsual Q hM hMT
    (fun n => (J n).strategy) C hC L hqLim
  have hMEq := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hM G.martingalePart_isRightContinuous hMT
    (Function.uncurry L.integrand) L.integrand_isStronglyPredictable L.integrand_memLp_energy
    (Function.uncurry K.integrand) K.integrand_isStronglyPredictable K.integrand_memLp_energy
    (Eventually.of_forall fun p => congrFun (congrFun hLK p.1) p.2)
  exact ⟨J, hConv.congr_limit
    (finiteHorizonCompletedM2AGain_indistinguishable_of_integrand_eq
      hUsual E Q hM hMT L K hLK), hMConv.congr_limit hMEq⟩

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42

/-! ## Completed martingale bounds on a test horizon independent of completion -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Completing an elementary integral on `U` does not enlarge a test error
on `T`, regardless of the order of the two horizons. -/
theorem integral_elementaryEmeryTestError_finiteHorizonGain_le
    (S : Process Ω) (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (H J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (U T : NNReal) :
    (∫ ω, elementaryEmeryTestError (H.strategy.finiteHorizonGain S U) 0 J T ω ∂μ) ≤
      ∫ ω, elementaryEmeryTestError S 0 (J.mul H) T ω ∂μ := by
  let X := ElementaryStrategy.gain S H.strategy.toElementary
  have hXR := H.strategy.rightContinuous_gain S hSR
  have hXP := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (H.strategy.stronglyAdapted_gain S hS) hXR
  have hStop := integral_elementaryEmeryTestError_finiteStopped_le (μ := μ) X 0 hXP
    (show IsStronglyProgressive F (0 : Process Ω) from fun _ => stronglyMeasurable_zero)
    hXR (fun _ _ => continuousWithinAt_const) (fun _ => U) (isStoppingTime_const F U) J T
  have hZeroStop : stoppedProcess (0 : Process Ω) (fun _ : Ω => (U : WithTop NNReal)) = 0 := by
    funext t ω
    rfl
  rw [hZeroStop] at hStop
  have hAssoc : ElementaryStrategy.gain X J.strategy.toElementary =
      ElementaryStrategy.gain S (J.mul H).strategy.toElementary :=
    PredictableElementaryEmery.elementaryGain_source_mul S J.strategy H.strategy
  have hZero (K : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
      ElementaryStrategy.gain (0 : Process Ω) K.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  have hEq : elementaryEmeryTestError X 0 J T =
      elementaryEmeryTestError S 0 (J.mul H) T := by
    simp only [elementaryEmeryTestError, hAssoc, hZero, Pi.zero_apply, sub_zero]
  rw [hEq] at hStop
  exact hStop

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Ω} [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {G : SIntegrableStrategy D}
  {U : NNReal} {E : SIntegrableFiniteVariationBridge G}

/-- A unit completed martingale integral preserves the source's bound on
any fixed test horizon. Its completion horizon can vary independently. -/
theorem finiteHorizonCompletedMartingalePart_testError_bound_on_horizon
    (hUsual : Filtration.UsualConditions μ F)
    (Q : BoundedMartingaleQuadraticKernel.Data F μ G.martingalePart U)
    (hM : Martingale G.martingalePart F μ) (hMU : MemLp (G.martingalePart U) 2 μ)
    (K : FiniteHorizonM2ACoefficient E Q) (hK : ∀ t ω, |K.integrand t ω| ≤ 1)
    (T : NNReal) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂μ) ≤ b) :
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError
        (finiteHorizonCompletedMartingalePart hUsual U Q hM hMU K) 0 J T ω ∂μ) ≤ b := by
  obtain ⟨A, _, hA⟩ := exists_unitElementarySequence_gain_martingale_emery hUsual Q hM hMU K hK
  have hSP : IsStronglyProgressive F G.martingalePart :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      G.martingalePart_isStronglyAdapted G.martingalePart_isRightContinuous
  have hAP n : IsStronglyProgressive F
      ((A n).strategy.finiteHorizonGain G.martingalePart U) := by
    have hAR := (A n).strategy.rightContinuous_gain G.martingalePart
      G.martingalePart_isRightContinuous
    apply StronglyAdapted.isStronglyProgressive_of_rightContinuous
    · exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        ((A n).strategy.stronglyAdapted_gain G.martingalePart hSP)
        (isStoppingTime_const F U) hAR
    · exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _ hAR
  have hVP : IsStronglyProgressive F
      (finiteHorizonCompletedMartingalePart hUsual U Q hM hMU K) :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (finiteHorizonMartingaleIntegralProcess_isMartingale hUsual Q hM
        G.martingalePart_isRightContinuous hMU (Function.uncurry K.integrand)
        K.integrand_isStronglyPredictable K.integrand_memLp_energy).stronglyAdapted
      (finiteHorizonMartingaleIntegralProcess_rightContinuous hUsual Q hM
        G.martingalePart_isRightContinuous hMU (Function.uncurry K.integrand)
        K.integrand_isStronglyPredictable K.integrand_memLp_energy)
  apply hA.testError_bound hAP hVP T b
  intro n J
  exact (integral_elementaryEmeryTestError_finiteHorizonGain_le (μ := μ)
    G.martingalePart hSP G.martingalePart_isRightContinuous (A n) J U T).trans
      (hBound (J.mul (A n)))

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
