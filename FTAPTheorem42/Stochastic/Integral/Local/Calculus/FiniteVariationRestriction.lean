/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARestriction
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationStoppedStieltjes
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.FiniteVariationCoordinateAgreement
import FTAPTheorem42.Stochastic.Integral.Local.Construction.MartingaleGluing
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge

/-!
# Global finite-variation part of an intrinsic predictable restriction

The finite-variation component is the direct bounded predictable Stieltjes
integral of the indicator. Its increments identify each schedule stop with
the restricted completed `A1` coordinate. No raw restriction calculus is
required to assemble the intrinsic graph.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The predictable indicator integral against the finite-variation part,
constructed from its normalized Stieltjes bridge. -/
noncomputable def restrictedFiniteVariationPart
    (B : Set (NNReal × Omega)) (_hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) : Process Omega :=
  finiteVariationIntegralProcess
    (ofCumulativeVariationNormalized H.finiteVariationPart_isRightContinuous)
    (PredictableProcess.indicator B)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
@[simp]
theorem restrictedFiniteVariationPart_zero
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) :
    restrictedFiniteVariationPart B hB H 0 = 0 := by
  funext omega
  simp [restrictedFiniteVariationPart, finiteVariationIntegralProcess,
    pathVariationMeasureUpTo]

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- Bounded predictable Stieltjes integration preserves predictability. -/
theorem restrictedFiniteVariationPart_isStronglyPredictable
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) :
    IsStronglyPredictable F (restrictedFiniteVariationPart B hB H) :=
  finiteVariationIntegralProcess_isStronglyPredictable _
    (PredictableProcess.isStronglyPredictable_indicator hB)
    (PredictableProcess.abs_indicator_le_one B)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- The direct indicator integral is right-continuous on every path. -/
theorem restrictedFiniteVariationPart_isRightContinuous
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt
      (restrictedFiniteVariationPart B hB H · omega) (Ici t) t :=
  finiteVariationIntegralProcess_rightContinuous _
    (PredictableProcess.isStronglyPredictable_indicator hB)
    (PredictableProcess.abs_indicator_le_one B) omega t

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- Restriction retains global bounded variation on every path. -/
theorem restrictedFiniteVariationPart_isBoundedVariation
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) (omega : Omega) :
    BoundedVariationOn
      (fun t => restrictedFiniteVariationPart B hB H t omega) Set.univ :=
  finiteVariationIntegralProcess_isBoundedVariation _
    (PredictableProcess.isStronglyPredictable_indicator hB)
    (PredictableProcess.abs_indicator_le_one B) omega

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- The direct integral has the restricted signed-measure increments. -/
theorem restrictedFiniteVariationPart_increment
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (H : SIntegrableStrategy D) :
    ∀ᵐ omega ∂mu, ∀ a b : NNReal, a ≤ b →
      restrictedFiniteVariationPart B hB H b omega -
          restrictedFiniteVariationPart B hB H a omega =
        FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation omega)
          (PredictableFiniteVariationRestriction.timeSection B omega ∩ Ioc a b) := by
  let E := ofCumulativeVariationNormalized H.finiteVariationPart_isRightContinuous
  filter_upwards [signedMeasure_finiteVariationPart_eq_withDensity_ae E] with omega hDensity
  intro a b hab
  let A := PredictableFiniteVariationRestriction.timeSection B omega
  have hA : MeasurableSet A :=
    SIntegrablePathwiseRestrictionCalculus.measurableSet_timeSection B hB omega
  have hEq : (fun t => finiteVariationIntegralDensity E
      (PredictableProcess.indicator B) (t, omega)) =
      A.indicator (fun t => jumpCorrectedCanonicalVariationDensity E (t, omega)) := by
    funext t
    by_cases ht : (t, omega) ∈ B
    · simp [finiteVariationIntegralDensity, ht, A,
        PredictableFiniteVariationRestriction.timeSection]
    · simp [finiteVariationIntegralDensity, ht, A,
        PredictableFiniteVariationRestriction.timeSection]
  change finiteVariationIntegralProcess E _ b omega -
    finiteVariationIntegralProcess E _ a omega = _
  rw [finiteVariationIntegralProcess_sub E
    (PredictableProcess.isStronglyPredictable_indicator hB)
    (PredictableProcess.abs_indicator_le_one B) omega hab, hEq,
    setIntegral_indicator hA, inter_comm (Ioc a b) A]
  conv_rhs => rw [hDensity,
    withDensityᵥ_apply (integrable_jumpCorrectedCanonicalVariationDensity_section E omega)
      (hA.inter measurableSet_Ioc)]

/-- At every coordinate of an intrinsic graph, the centered global
finite-variation restriction agrees with the completed restricted `A1`
coordinate. The direct Stieltjes increment identity and the original
coordinate density determine this equality. -/
theorem actual_restrictedFiniteVariationPart_stopped_eq_completed
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (n : Nat) :
    let witness := actualGraphWitness H
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (restrictedFiniteVariationPart B hB H.val)
        (witness.schedule.localizer n))
      (finiteHorizonCompletedFiniteVariationPart
        witness.schedule.usualConditions (witness.schedule.horizon n)
        (witness.schedule.quadraticKernel n)
        (witness.schedule.variationBridge n)
        ((witness.coefficient n).restrictPredictable B hB)) := by
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  let tau := schedule.localizer n
  let T := schedule.horizon n
  let c := witness.coefficient n
  let E := schedule.variationBridge n
  have hRestriction :=
    restrictedFiniteVariationPart_increment B hB H.val
  have hDensity := actualCoordinate_finiteVariationPathDensity H n
  have hCoefficientIntegrable : ∀ᵐ omega ∂mu, Integrable
      (fun u => c.integrand u omega)
      (FiniteVariationPath.signedMeasure
        ((schedule.sourcePrefix n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation :=
    integrable_section_ae_of_memLp_one_canonicalVariation
      E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  have hCompleted :=
    finiteHorizonCompletedFiniteVariationPart_restrictPredictable
      schedule.usualConditions (schedule.quadraticKernel n) E B hB c
  filter_upwards [hRestriction, hDensity, hCoefficientIntegrable, hCompleted]
      with omega hRestrictionOmega hDensityOmega hIntegrableOmega
        hCompletedOmega
  intro t
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau omega
  let u := RightContinuousStoppedMartingale.boundedTime t tau omega
  let timeSet := PredictableFiniteVariationRestriction.timeSection B omega
  let nu := (FiniteVariationPath.signedMeasure
    ((schedule.sourcePrefix n
      ).finiteVariationPart_isBoundedVariation omega)).totalVariation
  let g := fun s => finiteVariationIntegralDensity E c.integrand (s, omega)
  let stoppedPath := FiniteVariationStoppedPath.stopAt
    (fun s => H.val.finiteVariationPart s omega) sigma
  let hStoppedPath := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (H.val.finiteVariationPart_isBoundedVariation omega) sigma
  have hTauT : tau omega <= (T : WithTop NNReal) :=
    schedule.localizer_le_horizon n omega
  have hu : u = min t sigma := by
    apply WithTop.coe_eq_coe.mp
    rw [RightContinuousStoppedMartingale.coe_boundedTime,
      WithTop.coe_min,
      RightContinuousStoppedMartingale.coe_boundedTime,
      min_eq_right hTauT]
  have hTimeSet : MeasurableSet timeSet :=
    SIntegrablePathwiseRestrictionCalculus.measurableSet_timeSection
      B hB omega
  have hSet : timeSet ∩ Ioc 0 u =
      (timeSet ∩ Ioc 0 t) ∩ Ioc 0 sigma := by
    ext s
    simp only [mem_inter_iff, mem_Ioc]
    rw [hu]
    constructor
    · rintro ⟨hs, h0s, hsMin⟩
      exact ⟨⟨hs, h0s, hsMin.trans (min_le_left t sigma)⟩,
        h0s, hsMin.trans (min_le_right t sigma)⟩
    · rintro ⟨⟨hs, h0s, hst⟩, -, hsSigma⟩
      exact ⟨hs, h0s, le_min hst hsSigma⟩
  have hGIntegrable : Integrable g nu :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E c.integrand_isStronglyPredictable omega hIntegrableOmega
  have hRestrictedDensity :
      (fun s => finiteVariationIntegralDensity E
        (PredictableProcess.restrict B c.integrand) (s, omega)) =
        timeSet.indicator g := by
    funext s
    by_cases hs : (s, omega) ∈ B
    · rw [Set.indicator_of_mem]
      · simp [finiteVariationIntegralDensity,
          PredictableProcess.restrict, hs, g]
      · exact hs
    · rw [Set.indicator_of_notMem]
      · simp [finiteVariationIntegralDensity,
          PredictableProcess.restrict, hs]
      · exact hs
  have hIntegral : finiteVariationIntegralProcess E
      (PredictableProcess.restrict B c.integrand) t omega =
        FiniteVariationPath.signedMeasure hStoppedPath
          (timeSet ∩ Ioc 0 t) := by
    rw [finiteVariationIntegralProcess, pathVariationMeasureUpTo,
      hRestrictedDensity]
    change (∫ s in Ioc 0 t, timeSet.indicator g s ∂nu) = _
    rw [MeasureTheory.setIntegral_indicator hTimeSet,
      inter_comm (Ioc 0 t) timeSet]
    have hApply := congrArg
      (fun m : SignedMeasure NNReal => m (timeSet ∩ Ioc 0 t))
      hDensityOmega
    rw [withDensityᵥ_apply hGIntegrable
      (hTimeSet.inter measurableSet_Ioc)] at hApply
    exact hApply
  have hStoppedMeasure :
      FiniteVariationPath.signedMeasure hStoppedPath =
        (FiniteVariationPath.signedMeasure
          (H.val.finiteVariationPart_isBoundedVariation omega)).restrict
            (Ioc 0 sigma) :=
    FiniteVariationStoppedPath.signedMeasure_stopAt_eq_restrict_Ioc
      (fun s => H.val.finiteVariationPart s omega)
      (H.val.finiteVariationPart_isBoundedVariation omega)
      (H.val.finiteVariationPart_isRightContinuous omega) sigma
  have hRawIncrement : restrictedFiniteVariationPart B hB H.val u omega -
      restrictedFiniteVariationPart B hB H.val 0 omega =
        FiniteVariationPath.signedMeasure
          (H.val.finiteVariationPart_isBoundedVariation omega)
          (timeSet ∩ Ioc 0 u) := by
    simpa only [timeSet] using hRestrictionOmega 0 u bot_le
  have hSample : MeasureTheory.stoppedProcess
      (restrictedFiniteVariationPart B hB H.val) tau t omega =
        restrictedFiniteVariationPart B hB H.val u omega -
          restrictedFiniteVariationPart B hB H.val 0 omega := by
    rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
    simp only [restrictedFiniteVariationPart_zero, Pi.zero_apply, sub_zero]
    rfl
  rw [hSample, hRawIncrement, hCompletedOmega t, hIntegral,
    hStoppedMeasure, VectorMeasure.restrict_apply _ measurableSet_Ioc
      (hTimeSet.inter measurableSet_Ioc), hSet]

/-- The global local martingale obtained by gluing the predictably
restricted completed martingale coordinates of an intrinsic graph. -/
noncomputable def restrictedMartingalePart
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    Process Omega :=
  Classical.choose
    ((actualGraphWitness H).exists_restrictedMartingalePart B hB)

omit [F.IsRightContinuous] in
/-- The glued restricted martingale has the required global regularity and
the prescribed completed coordinate stops. -/
theorem restrictedMartingalePart_spec
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    StronglyAdapted F (restrictedMartingalePart  H B hB) /\
      LocalMartingale (restrictedMartingalePart  H B hB) F mu /\
      (forall omega t, ContinuousWithinAt
        (restrictedMartingalePart  H B hB · omega) (Ici t) t) /\
      forall n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess (restrictedMartingalePart  H B hB)
          ((actualGraphWitness H).schedule.localizer n))
        (completedMartingaleCoordinate (actualGraphWitness H).schedule
          (fun k => ((actualGraphWitness H).coefficient k
            ).restrictPredictable B hB) n) :=
  Classical.choose_spec
    ((actualGraphWitness H).exists_restrictedMartingalePart B hB)

/-- The raw strategy assembled directly from the two intrinsic restricted
components.  In particular, its gain is not taken from the underdetermined
raw restriction interface. -/
noncomputable def restrictPredictableStrategy
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    SIntegrableStrategy D := by
  let M := restrictedMartingalePart  H B hB
  let A := restrictedFiniteVariationPart B hB H.val
  have hM := restrictedMartingalePart_spec  H B hB
  have hAPredictable :=
    restrictedFiniteVariationPart_isStronglyPredictable B hB H.val
  exact {
    integrand := PredictableProcess.restrict B H.val.integrand
    stochasticIntegral := fun t omega => M t omega + A t omega
    martingalePart := M
    finiteVariationPart := A
    finiteVariationMeasure := H.val.finiteVariationMeasure.restrict B
    integrand_isPredictable :=
      PredictableProcess.isStronglyPredictable_restrict hB
        H.val.integrand_isPredictable
    stochasticIntegral_isStronglyAdapted :=
      hM.1.add hAPredictable.stronglyAdapted
    stochasticIntegral_isRightContinuous := fun omega t =>
      (hM.2.2.1 omega t).add
        (restrictedFiniteVariationPart_isRightContinuous B hB H.val
          omega t)
    martingalePart_isLocalMartingale := hM.2.1
    martingalePart_isStronglyAdapted := hM.1
    martingalePart_isRightContinuous := hM.2.2.1
    finiteVariationPart_isPredictable := hAPredictable
    finiteVariationPart_isRightContinuous :=
      restrictedFiniteVariationPart_isRightContinuous B hB H.val
    finiteVariationPart_isBoundedVariation :=
      restrictedFiniteVariationPart_isBoundedVariation B hB H.val
    integral_decomposition := ProcessIndistinguishable.refl mu _
    source_decomposition := H.val.source_decomposition }

/-- The actual-first restricted strategy is represented on the original
exhaustive schedule by the indicator-restricted coefficients. -/
noncomputable def restrictPredictableStrategy_graphWitness
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    GraphWitness G (restrictPredictableStrategy H B hB) := by
  let witness := actualGraphWitness H
  refine {
    schedule := witness.schedule
    coefficient := fun n => (witness.coefficient n).restrictPredictable B hB
    coefficient_eq := fun n => ?_
    stoppedGain_eq := fun n => ?_ }
  · rw [FiniteHorizonM2ACoefficient.restrictPredictable_coefficient,
      witness.coefficient_eq n]
    rfl
  · have hM := (restrictedMartingalePart_spec  H B hB).2.2.2 n
    have hA := actual_restrictedFiniteVariationPart_stopped_eq_completed H B hB n
    have hSum := hM.add hA
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (fun t omega => restrictedMartingalePart  H B hB t omega +
          restrictedFiniteVariationPart B hB H.val t omega)
        (witness.schedule.localizer n))
      (fun t omega =>
        finiteHorizonCompletedMartingalePart witness.schedule.usualConditions
            (witness.schedule.horizon n)
            (witness.schedule.quadraticKernel n)
            (witness.schedule.martingale n)
            (witness.schedule.terminal_memLp n)
            ((witness.coefficient n).restrictPredictable B hB) t omega +
          finiteHorizonCompletedFiniteVariationPart
            witness.schedule.usualConditions (witness.schedule.horizon n)
            (witness.schedule.quadraticKernel n)
            (witness.schedule.variationBridge n)
            ((witness.coefficient n).restrictPredictable B hB) t omega)
    have hStopAdd : ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (fun t omega => restrictedMartingalePart  H B hB t omega +
            restrictedFiniteVariationPart B hB H.val t omega)
          (witness.schedule.localizer n))
        (fun t omega =>
          MeasureTheory.stoppedProcess (restrictedMartingalePart  H B hB)
              (witness.schedule.localizer n) t omega +
            MeasureTheory.stoppedProcess
              (restrictedFiniteVariationPart B hB H.val)
              (witness.schedule.localizer n) t omega) := by
      filter_upwards with omega
      intro t
      rfl
    exact hStopAdd.trans hSum

/-- Predictable restriction constructed intrinsically in the local
completed carrier. -/
noncomputable def actualRestrictPredictable
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ActualSIntegrableStrategy (realizationModel G) :=
  ⟨restrictPredictableStrategy H B hB,
    ⟨restrictPredictableStrategy_graphWitness H B hB⟩⟩

end LocalCompletedM2A

end FTAPTheorem42
