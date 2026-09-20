/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.General.TruncatedIntegralGraph
import FTAPTheorem42.Stochastic.Integral.Local.Construction.UnitSourceRealization
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualRestrictionCadlag
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-! # Bounded global certificates in the truncation graph

Predictable restriction constructs every bounded coefficient truncation.
Beyond a deterministic index the coefficients agree with the original, so
fixed-source uniqueness identifies the gains. The regular limit is obtained
from completed càdlàg coordinates. Coordinate restriction and gluing construct the local
approximants without an input stopping or predictable restriction calculus.
-/

namespace FTAPTheorem42.LocalCompletedM2A

open Filter MeasureTheory Set Topology
open FTAPTheorem42.SpecialSemimartingaleDecomposition
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ F] {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

/-- Self-refinement and the existing coordinate gluing supply a regular
version of a global graph gain, without a restriction calculus. -/
theorem GraphWitness.exists_cadlagGain
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {H : SIntegrableStrategy D} (w : GraphWitness G H) :
    ∃ X : Process Ω, StronglyAdapted F X ∧
      (∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) ∧
      ProcessHasLeftLimits X ∧ ProcessIndistinguishable μ X H.stochasticIntegral := by
  let rep := w.selfPairRepresentation
  let schedule := pairCommonSchedule w.schedule w.schedule
  let c := fun n => (rep.coefficient n).restrictPredictable univ MeasurableSet.univ
  have hc n : (c n).coefficient = Function.uncurry H.integrand := by
    change univ.indicator (rep.coefficient n).coefficient = _
    simpa only [Set.indicator_univ] using rep.coefficient_eq n
  obtain ⟨V, hVI, hVG, hVM, hVA⟩ :=
    exists_completedM2AGainStrategy_with_integrand schedule c hc
  obtain ⟨M, hMA, hML, hMR, hMLeft, hMS⟩ :=
    rep.exists_restrictedCadlagMartingalePart
      (w.selfPairSchedule_sourceLeft hGLeft) univ MeasurableSet.univ
  have hMV : ProcessIndistinguishable μ M V.martingalePart := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
      schedule.isLocalizingSequence
    intro n
    exact (hMS n).trans ((completedMartingaleCadlagCoordinate_indistinguishable
      schedule (w.selfPairSchedule_sourceLeft hGLeft) c n).trans (hVM n).symm)
  have hVH : ProcessIndistinguishable μ V.stochasticIntegral H.stochasticIntegral := by
    exact stochasticIntegral_indistinguishable_of_integrand_eq_of_actualLocal
      ⟨V, fun T hT => deterministicallyStoppedGraphWitness_isRealized
        schedule c hc V hVI hVG T hT⟩ w.toActualLocal hVI
  refine ⟨fun t ω => M t ω + V.finiteVariationPart t ω,
    hMA.add V.finiteVariationPart_isPredictable.stronglyAdapted,
    fun ω t => (hMR ω t).add (V.finiteVariationPart_isRightContinuous ω t),
    hMLeft.add ?_, ?_⟩
  · exact finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      V.finiteVariationPart_isLocallyBoundedVariation
  · exact (hMV.add (.refl μ _)).trans (V.integral_decomposition.symm.trans hVH)

end FTAPTheorem42.LocalCompletedM2A

namespace FTAPTheorem42.LocalCompletedM2A

/-! ## Bounded predictable coefficients in the general integral graph

The finite variation control and quadratic energy measures are finite, so
every bounded predictable coefficient belongs to both completed spaces.
Gluing their integrals supplies actual local graphs and a regular gain.
Fixed-source uniqueness then includes every bounded local certificate in the
truncation graph, without an additional stopping or restriction calculus.
-/

open Filter MeasureTheory Set Topology
open FTAPTheorem42.SpecialSemimartingaleDecomposition
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

/-- Boundedness supplies both integrability obligations on every coordinate. -/
noncomputable def boundedPredictableCoefficient
    (schedule : LocalCompletedM2ASchedule G)
    (H : Process Ω) (hH : IsStronglyPredictable F H)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) (n : Nat) :
    FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n) where
  coefficient := Function.uncurry H
  coefficient_isStronglyMeasurable := hH
  coefficient_memLp_variation := MemLp.of_bound hH.aestronglyMeasurable b
    (Eventually.of_forall fun p => hBound p.1 p.2)
  coefficient_memLp_energy := by
    let _ := (schedule.quadraticKernel n).predictableEnergyMeasure_isFinite
    exact MemLp.of_bound hH.aestronglyMeasurable b
      (Eventually.of_forall fun p => hBound p.1 p.2)

/-- The existing completed gluing actually constructs the bounded graph. -/
theorem exists_boundedPredictable_actualLocal
    (schedule : LocalCompletedM2ASchedule G)
    (H : Process Ω) (hH : IsStronglyPredictable F H)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ∃ R : ActualLocallySIntegrableStrategy (realizationModel G),
      R.val.integrand = H ∧
      ∀ n, ProcessIndistinguishable μ
        (stoppedProcess R.val.stochasticIntegral (schedule.localizer n))
        (finiteHorizonCompletedM2AGain schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n)
          (boundedPredictableCoefficient schedule H hH b hBound n)) := by
  obtain ⟨R, hR, hGain, -⟩ := exists_actualLocal_of_commonSchedule schedule
    (boundedPredictableCoefficient schedule H hH b hBound) (fun _ => rfl)
  exact ⟨R, hR, hGain⟩

/-- Càdlàg completed coordinates provide a regular version of the same gain.
The coefficient need not be bounded when its completed coordinates are supplied. -/
theorem CommonScheduleIntegralGraphData.exists_cadlagGain
    {H X : Process Ω} (data : CommonScheduleIntegralGraphData G H X)
    (hLeft : ∀ n, ProcessHasLeftLimits (data.schedule.sourcePrefix n).martingalePart) :
    ∃ Y : Process Ω, StronglyAdapted F Y ∧
      (∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t) ∧
      ProcessHasLeftLimits Y ∧ Y 0 =ᵐ[μ] 0 ∧ ProcessIndistinguishable μ Y X := by
  obtain ⟨R, hR, hGain, hM, hA⟩ := exists_actualLocal_of_commonSchedule
    data.schedule data.coefficient data.coefficient_eq
  obtain ⟨M, hMA, _hML, hMR, hMLft, hMS⟩ := exists_completedCadlagMartingalePart
    data.schedule hLeft data.coefficient data.coefficient_eq
  have hMR' : ProcessIndistinguishable μ M R.val.martingalePart := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
      data.schedule.isLocalizingSequence
    intro n
    exact (hMS n).trans ((completedMartingaleCadlagCoordinate_indistinguishable
      data.schedule hLeft data.coefficient n).trans (hM n).symm)
  have hRX : ProcessIndistinguishable μ R.val.stochasticIntegral X := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
      data.schedule.isLocalizingSequence
    intro n
    exact (hGain n).trans (data.stoppedGain_eq n).symm
  let Y : Process Ω := fun t ω => M t ω + R.val.finiteVariationPart t ω
  have hYR : ProcessIndistinguishable μ Y R.val.stochasticIntegral :=
    (hMR'.add (.refl μ _)).trans R.val.integral_decomposition.symm
  refine ⟨Y, hMA.add R.val.finiteVariationPart_isPredictable.stronglyAdapted,
    fun ω t => (hMR ω t).add (R.val.finiteVariationPart_isRightContinuous ω t),
    hMLft.add (finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      R.val.finiteVariationPart_isLocallyBoundedVariation), ?_, hYR.trans hRX⟩
  have hZero := actual_stochasticIntegral_zero (R.deterministicallyStopped 1 zero_lt_one)
  change R.val.stochasticIntegral (min 0 1) =ᵐ[μ] 0 at hZero
  exact (hYR.eventuallyEq_at 0).trans (by simpa only [min_eq_left zero_le_one] using hZero)

/-- Every bounded predictable coefficient has a truncation graph, constructed
from the original source schedule and with a regular zero-initial gain. -/
theorem exists_boundedPredictable_truncatedGraph
    (schedule : LocalCompletedM2ASchedule G)
    (hLeft : ∀ n, ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (H : Process Ω) (hH : IsStronglyPredictable F H)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ∃ X : Process Ω, IsIntegralGraph G H X ∧ IsTruncatedIntegralGraph G H X := by
  classical
  obtain ⟨R, hR, hGain⟩ := exists_boundedPredictable_actualLocal schedule H hH b hBound
  let data : CommonScheduleIntegralGraphData G H R.val.stochasticIntegral := {
    schedule := schedule
    coefficient := boundedPredictableCoefficient schedule H hH b hBound
    coefficient_eq := fun _ => rfl
    stoppedGain_eq := hGain }
  obtain ⟨Y, hYA, hYR, hYL, hY0, hY⟩ := data.exists_cadlagGain hLeft
  have hCut n : IsStronglyPredictable F (integralCoefficientTruncation H n) :=
    PredictableProcess.isStronglyPredictable_restrict
      (hH.norm.measurableSet_le stronglyMeasurable_const) hH
  have hRows n := exists_boundedPredictable_actualLocal schedule
    (integralCoefficientTruncation H n) (hCut n) ((n : Real) + 1)
    (integralCoefficientTruncation_abs_le H n)
  choose A hAI hAG using hRows
  have hEventually : ∀ᶠ n : Nat in atTop,
      ProcessIndistinguishable μ Y (A n).val.stochasticIntegral := by
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop N] with n hn
    apply hY.trans
    apply stochasticIntegral_indistinguishable_of_integrand_eq_of_actualLocal R (A n)
    rw [hR, hAI]
    funext t ω
    apply (ite_eq_left _).symm
    exact (hBound t ω).trans (hN.le.trans
      ((Nat.cast_le.mpr hn).trans (le_add_of_nonneg_right zero_le_one)))
  refine ⟨R.val.stochasticIntegral, ⟨⟨R, hR, .refl μ _⟩⟩, ⟨{
    integrand_predictable := hH
    approximant := A
    approximant_integrand := hAI
    regularGain := Y
    regularGain_adapted := hYA
    regularGain_right := hYR
    regularGain_left := hYL
    regularGain_zero := hY0
    gain_indistinguishable := hY
    convergence := (ElementaryEmeryConverges.refl Y).congr_sequence_eventually hEventually }⟩⟩

end FTAPTheorem42.LocalCompletedM2A
