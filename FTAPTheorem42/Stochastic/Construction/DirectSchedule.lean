/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.ActualVanishingRisk
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageLimitRealization
import FTAPTheorem42.Stochastic.Market.Source.TiltedRegularizedSourceData
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.Process.Stopping
import FTAPTheorem42.Foundations.ChronologicalGridOrientation
import FTAPTheorem42.Stochastic.Market.Transfer.EquivalentMeasure
import FTAPTheorem42.Stochastic.Process.CadlagPathBoundedness
import FTAPTheorem42.Stochastic.Integral.Localization.DirectPassageM2A
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2AApproximation
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Integral.General.BoundedPredictableIntegralGraph

/-! # The regularized centered unit source, independent of integration calculus -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Choose the already constructed global special decomposition. -/
noncomputable def sourceData (source : BoundedSemimartingaleSource S F μ) :
    TiltedRegularizedSourceData source :=
  ⟨Classical.choice
    (HorizonFactorialGrid.exists_boundedSemimartingaleSource_globalSpecialDecompositionData
      source)⟩

variable [SigmaFiniteFiltration μ F]

noncomputable abbrev unitSource (source : BoundedSemimartingaleSource S F μ) :=
  (sourceData source).centeredUnitLocallySIntegrableStrategy

theorem unitSource_integrand (source : BoundedSemimartingaleSource S F μ) :
    (unitSource source).integrand = PredictableProcess.unit :=
  (sourceData source).centeredUnitLocallySIntegrableStrategy_integrand

theorem unitSource_zero (source : BoundedSemimartingaleSource S F μ) :
    (unitSource source).stochasticIntegral 0 =ᵐ[μ] 0 := by
  exact Filter.Eventually.of_forall fun ω => by
    change S 0 ω - S 0 ω = 0
    exact sub_self _

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Direct elementary coordinates of the original bounded source

The finite-horizon elementary carrier of each stopped unit coordinate is
constructed from the source decomposition. The exhaustive schedule below
identifies these coordinates with the global local-completed graph.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

noncomputable def directUnitHorizon (source : BoundedSemimartingaleSource S F μ) (n : Nat) :=
  (unitSource source).deterministicallyStopped (cadlagPassageHorizon n) (cadlagPassageHorizon_pos n)

theorem directUnitHorizon_martingale_zero (source : BoundedSemimartingaleSource S F μ) (n : Nat) :
    (directUnitHorizon source n).martingalePart 0 = 0 := by
  funext ω
  change (sourceData source).regularizedDecomposition.martingalePart (min 0 _) ω -
    (sourceData source).regularizedDecomposition.martingalePart 0 ω = 0
  rw [min_eq_left (show (0 : NNReal) ≤ cadlagPassageHorizon n from bot_le), sub_self]

noncomputable def directUnitPassage (source : BoundedSemimartingaleSource S F μ) (n : Nat) :=
  let := source.usualConditions.rightContinuous
  (directUnitHorizon source n).directPassage (directUnitHorizon_martingale_zero source n) n

theorem directUnitPassage_martingale_l2 (source : BoundedSemimartingaleSource S F μ) (n : Nat) :
    Martingale (directUnitPassage source n).martingalePart F μ ∧
      MemLp ((directUnitPassage source n).martingalePart (cadlagPassageHorizon n)) 2 μ := by
  let := source.usualConditions.rightContinuous
  apply (directUnitHorizon source n).directPassage_martingale_l2
    (directUnitHorizon_martingale_zero source n) _ source.usualConditions
    (fun _ => 2 * source.bound) (memLp_const _) _ n
  · have h := (sourceData source).regularizedDecomposition_spec.2.2.2.2.1
    exact (h.sub (.timeConstant _)).deterministicallyStopped _
  · filter_upwards [source.uniformBound] with ω hω
    intro t
    change |S (min t (cadlagPassageHorizon n)) ω - S 0 ω| ≤ 2 * source.bound
    calc
      _ ≤ |S (min t (cadlagPassageHorizon n)) ω| + |S 0 ω| := abs_sub _ _
      _ ≤ source.bound + source.bound := add_le_add (hω _) (hω _)
      _ = _ := by ring

theorem directUnitPassage_gain (source : BoundedSemimartingaleSource S F μ) (n : Nat) :
    (directUnitPassage source n).stochasticIntegral =
      stoppedProcess (fun t ω => S (min t (cadlagPassageHorizon n)) ω - S 0 ω)
        (fun ω => (cadlagAbsolutePassageLocalizerFinite
          (directUnitHorizon source n).martingalePart n ω : WithTop NNReal)) := rfl

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## A direct exhaustive completed schedule for the original centered unit source -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

theorem directUnitPassage_localizer_eq (source : BoundedSemimartingaleSource S F μ) (n : Nat) :
    (fun ω => (cadlagAbsolutePassageLocalizerFinite
      (directUnitHorizon source n).martingalePart n ω : WithTop NNReal)) =
      cadlagAbsolutePassageLocalizer (unitSource source).martingalePart n := by
  funext ω
  rw [coe_cadlagAbsolutePassageLocalizerFinite]
  exact min_absoluteStrictHittingAfter_deterministicallyStopped
    (unitSource source).martingalePart (cadlagPassageLevel n) (cadlagPassageHorizon n) ω

/-- All coordinate inputs and component identities are produced directly;
no raw restriction or stopping calculus is assumed. -/
noncomputable def directSchedule (source : BoundedSemimartingaleSource S F μ) :
    LocalCompletedM2ASchedule (unitSource source) := by
  let := source.usualConditions.rightContinuous
  refine {
    usualConditions := source.usualConditions
    localizer := cadlagAbsolutePassageLocalizer (unitSource source).martingalePart
    isLocalizingSequence := cadlagAbsolutePassageLocalizer_isLocalizingSequence
      (unitSource source).martingalePart_isStronglyAdapted
      (unitSource source).martingalePart_isRightContinuous ?_
    horizon := cadlagPassageHorizon
    horizon_pos := cadlagPassageHorizon_pos
    localizer_le_horizon := fun _ _ => min_le_right _ _
    sourcePrefix := directUnitPassage source
    sourcePrefix_stochasticIntegral := ?_
    sourcePrefix_martingalePart := ?_
    sourcePrefix_finiteVariationPart := ?_
    martingale := fun n => (directUnitPassage_martingale_l2 source n).1
    terminal_memLp := fun n => (directUnitPassage_martingale_l2 source n).2
    variationBridge := fun n => ofCumulativeVariationNormalized
      (directUnitPassage source n).finiteVariationPart_isRightContinuous
    quadraticKernel := fun n => Classical.choice
      (SquareIntegrableMartingaleQuadraticKernel.exists_data source.usualConditions
        (directUnitPassage_martingale_l2 source n).1
        (directUnitPassage source n).martingalePart_isRightContinuous
        (cadlagPassageHorizon n) (directUnitPassage_martingale_l2 source n).2) }
  · exact ((sourceData source).regularizedDecomposition_spec.2.2.2.2.1).sub (.timeConstant _)
  all_goals
    intro n
    dsimp only [directUnitPassage, SIntegrableStrategy.directPassage,
      LocallySIntegrableStrategy.finiteClosedStop,
      LocallySIntegrableStrategy.finiteClosedStopOfRightContinuous, SIntegrableStrategy.toLocally]
    rw [directUnitPassage_localizer_eq]
    exact ProcessIndistinguishable.refl μ _

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## General bounded predictable integrands of the original bounded price

The source supplies its own completed schedule. Bounded predictable
integrands therefore generate actual local and truncation graphs without a
calculus hypothesis. Existing bounded integral graphs retain their stored gain.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- The common schedule can be produced directly for a bounded existing
graph; the arbitrary-coefficient common schedule obligation is separate. -/
theorem exists_commonSchedule_of_bounded
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (h : IsIntegralGraph (unitSource source) H X)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    Nonempty (CommonScheduleIntegralGraphData (unitSource source) H X) := by
  have hH : IsStronglyPredictable F H :=
    h.representative_integrand ▸ h.representative.val.integrand_isPredictable
  obtain ⟨R, hR, hGain⟩ := exists_boundedPredictable_actualLocal
    (directSchedule source) H hH b hBound
  have hRX : ProcessIndistinguishable μ R.val.stochasticIntegral X :=
    IsIntegralGraph.gain_indistinguishable ⟨⟨R, hR, .refl μ _⟩⟩ h
  exact ⟨{
    schedule := directSchedule source
    coefficient := boundedPredictableCoefficient (directSchedule source) H hH b hBound
    coefficient_eq := fun _ => rfl
    stoppedGain_eq := fun n =>
      (hRX.symm.stoppedProcess ((directSchedule source).localizer n)).trans (hGain n) }⟩

/-- The original bounded source constructs both graphs for every bounded
predictable coefficient, without supplying an integral as an input. -/
theorem bounded_predictable_exists_integralGraph
    (source : BoundedSemimartingaleSource S F μ)
    (H : Process Ω) (hH : IsStronglyPredictable F H)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    ∃ X : Process Ω, IsIntegralGraph (unitSource source) H X ∧
      IsTruncatedIntegralGraph (unitSource source) H X := by
  let base := directSchedule source
  apply exists_boundedPredictable_truncatedGraph (pairCommonSchedule base base) _ H hH b hBound
  intro n
  exact pairScheduleSourcePrefix_martingalePart_hasLeftLimits
    (((sourceData source).regularizedDecomposition_spec.2.2.2.2.1).sub (.timeConstant _))
    base base n

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Original-price semantics for the direct elementary completed coordinates -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

theorem directUnitPassage_elementaryGain_eq
    (source : BoundedSemimartingaleSource S F μ) (n : Nat)
    (K : PredictableElementaryStrategy F) :
    K.finiteHorizonGain (directUnitPassage source n).stochasticIntegral (cadlagPassageHorizon n) =
      stoppedProcess (ElementaryStrategy.gain S K.toElementary)
        ((directSchedule source).localizer n) := by
  rw [directUnitPassage_gain]
  change stoppedProcess (ElementaryStrategy.gain
    (stoppedProcess (stoppedProcess (fun t ω => S t ω - S 0 ω)
      (fun _ => (cadlagPassageHorizon n : WithTop NNReal)))
      (fun ω => (cadlagAbsolutePassageLocalizerFinite
        (directUnitHorizon source n).martingalePart n ω : WithTop NNReal))) K.toElementary)
    (fun _ => (cadlagPassageHorizon n : WithTop NNReal)) = _
  rw [ElementaryStrategy.gain_finiteStoppedProcess,
    ElementaryStrategy.gain_finiteStoppedProcess, ElementaryStrategy.gain_sub_initial]
  change _ = stoppedProcess (ElementaryStrategy.gain S K.toElementary)
    (cadlagAbsolutePassageLocalizer (unitSource source).martingalePart n)
  rw [← directUnitPassage_localizer_eq source n]
  funext t ω
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  congr 1
  have hτ := cadlagAbsolutePassageLocalizerFinite_le_horizon
    (directUnitHorizon source n).martingalePart n ω
  simp only [min_assoc, min_eq_left hτ, min_eq_right hτ]

/-- Completed coordinates on the same source schedule represent the stopped
elementary gain of the original price, with the original coefficient. -/
theorem directSchedule_completedGain_elementary
    (source : BoundedSemimartingaleSource S F μ) (n : Nat)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B) :
    let C := directSchedule source
    ProcessIndistinguishable μ
      (finiteHorizonCompletedM2AGain C.usualConditions (C.horizon n) (C.quadraticKernel n)
        (C.variationBridge n) (C.martingale n) (C.terminal_memLp n)
        (finiteHorizonM2ACoefficientOfElementary
          (C.variationBridge n) (C.quadraticKernel n) K B hB))
      (stoppedProcess (ElementaryStrategy.gain S K.toElementary) (C.localizer n)) := by
  have h := finiteHorizonCompletedM2AGain_indistinguishable_elementary
    (directSchedule source).usualConditions ((directSchedule source).variationBridge n)
    ((directSchedule source).quadraticKernel n) ((directSchedule source).martingale n)
    ((directSchedule source).terminal_memLp n) K B hB
  exact h.trans (Eventually.of_forall fun ω t =>
    congrFun (congrFun (directUnitPassage_elementaryGain_eq source n K) t) ω)

/-- The original elementary pair has completed semantics on an exhaustive
source schedule. All inputs are generated without the general calculus. -/
noncomputable def directElementaryCommonSchedule
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B) :
    CommonScheduleIntegralGraphData (unitSource source) K.integrand
      (ElementaryStrategy.gain S K.toElementary) where
  schedule := directSchedule source
  coefficient := fun n => finiteHorizonM2ACoefficientOfElementary
    ((directSchedule source).variationBridge n) ((directSchedule source).quadraticKernel n) K B hB
  coefficient_eq := fun _ => rfl
  stoppedGain_eq := fun n => (directSchedule_completedGain_elementary source n K B hB).symm

end FTAPTheorem42.BoundedSourceIntegralMarket
