/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualRestrictionSemantics
import FTAPTheorem42.Stochastic.Integral.Local.Construction.MartingaleCadlagGluing
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairRefinement

/-!
# Càdlàg intrinsic predictable restrictions

An arbitrary intrinsic graph witness need not store left limits for the raw
representatives of its finite-horizon source.  Refining that witness with
itself rebuilds each source prefix through the concrete stopping calculus.
Thus left limits of the common local source pass to every refined prefix.
The càdlàg completed coordinates can then be glued, producing an actual-first
predictable restriction whose martingale component and gain have left
limits on every path.
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

omit [F.IsRightContinuous] in
/-- The source prefix rebuilt on a pair-refined schedule inherits left
limits from the common local source. -/
theorem pairScheduleSourcePrefix_martingalePart_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessHasLeftLimits
      (pairScheduleSourcePrefix left right n).martingalePart := by
  let T := pairScheduleHorizon left right n
  have hDeterministic : ProcessHasLeftLimits
      (G.deterministicallyStopped T
        (pairScheduleHorizon_pos left right n)).martingalePart := by
    intro omega t
    change Tendsto (fun s => G.martingalePart (min s T) omega)
      (nhdsWithin t (Iio t))
      (nhds (Function.leftLim
        (fun s => G.martingalePart (min s T) omega) t))
    simpa only [stoppedProcess_const_apply] using
      (hGLeft.stoppedProcess
        (fun _ : Omega => (T : WithTop NNReal)) omega t)
  exact hDeterministic.stoppedProcess
    (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal))

/-- Refine one graph witness with itself.  The localizer is unchanged, but
the source prefixes are rebuilt through the concrete stopping calculus. -/
noncomputable def GraphWitness.selfPairRepresentation
    {H : SIntegrableStrategy D} (witness : GraphWitness G H) :
    ScheduleGraphRepresentation
      (pairCommonSchedule witness.schedule witness.schedule) H :=
  witness.toScheduleGraphRepresentation.pairRefineLeft

omit [F.IsRightContinuous] in
/-- The self-refined schedule has source martingales with left limits. -/
theorem GraphWitness.selfPairSchedule_sourceLeft
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    {H : SIntegrableStrategy D} (witness : GraphWitness G H) :
    forall n, ProcessHasLeftLimits
      ((pairCommonSchedule witness.schedule witness.schedule
        ).sourcePrefix n).martingalePart := by
  intro n
  exact pairScheduleSourcePrefix_martingalePart_hasLeftLimits hGLeft witness.schedule
    witness.schedule n

/-- The global càdlàg martingale obtained from the self-refined restricted
coordinates. -/
noncomputable def restrictedCadlagMartingalePart
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    Process Omega :=
  let witness := actualGraphWitness H
  let representation := witness.selfPairRepresentation
  Classical.choose
    (representation.exists_restrictedCadlagMartingalePart
      (witness.selfPairSchedule_sourceLeft hGLeft) B hB)

omit [F.IsRightContinuous] in
/-- The self-refined càdlàg martingale has the expected regularity and
completed coordinate stops. -/
theorem restrictedCadlagMartingalePart_spec
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    let witness := actualGraphWitness H
    let schedule := pairCommonSchedule
      witness.schedule witness.schedule
    let representation := witness.selfPairRepresentation
    StronglyAdapted F (restrictedCadlagMartingalePart  hGLeft H B hB) /\
      LocalMartingale (restrictedCadlagMartingalePart  hGLeft H B hB) F mu /\
      (forall omega t, ContinuousWithinAt
        (restrictedCadlagMartingalePart  hGLeft H B hB · omega)
          (Ici t) t) /\
      ProcessHasLeftLimits
        (restrictedCadlagMartingalePart  hGLeft H B hB) /\
      forall n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (restrictedCadlagMartingalePart  hGLeft H B hB)
          (schedule.localizer n))
        (completedMartingaleCadlagCoordinate schedule
          (witness.selfPairSchedule_sourceLeft hGLeft)
          (fun k => (representation.coefficient k
            ).restrictPredictable B hB) n) := by
  let witness := actualGraphWitness H
  let representation := witness.selfPairRepresentation
  exact Classical.choose_spec
    (representation.exists_restrictedCadlagMartingalePart
      (witness.selfPairSchedule_sourceLeft hGLeft) B hB)

omit [F.IsRightContinuous] in
/-- The càdlàg glued martingale is a version of the previously constructed
right-continuous intrinsic restriction martingale. -/
theorem restrictedCadlagMartingalePart_indistinguishable
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ProcessIndistinguishable mu
      (restrictedCadlagMartingalePart  hGLeft H B hB)
      (restrictedMartingalePart  H B hB) := by
  let witness := actualGraphWitness H
  let oldSchedule := witness.schedule
  let pairSchedule := pairCommonSchedule oldSchedule oldSchedule
  let representation := witness.selfPairRepresentation
  let oldCoefficient := fun n =>
    (witness.coefficient n).restrictPredictable B hB
  let pairCoefficient := fun n =>
    (representation.coefficient n).restrictPredictable B hB
  let transportedCoefficient := fun n =>
    pairScheduleCoefficientLeft oldSchedule oldSchedule n
      (oldCoefficient n)
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
    oldSchedule.isLocalizingSequence
  intro n
  have hNew :=
    (restrictedCadlagMartingalePart_spec  hGLeft H B hB).2.2.2.2 n
  have hPairLocalizer : pairSchedule.localizer n =
      oldSchedule.localizer n := by
    funext omega
    exact min_self _
  have hNew' : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (restrictedCadlagMartingalePart  hGLeft H B hB)
        (oldSchedule.localizer n))
      (completedMartingaleCadlagCoordinate pairSchedule
        (witness.selfPairSchedule_sourceLeft hGLeft)
        pairCoefficient n) := by
    change ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (restrictedCadlagMartingalePart  hGLeft H B hB)
        (pairSchedule.localizer n))
      (completedMartingaleCadlagCoordinate pairSchedule
        (witness.selfPairSchedule_sourceLeft hGLeft)
        pairCoefficient n) at hNew
    rwa [hPairLocalizer] at hNew
  have hCadlag := completedMartingaleCadlagCoordinate_indistinguishable
    pairSchedule (witness.selfPairSchedule_sourceLeft hGLeft)
      pairCoefficient n
  have hCoefficientEq : (pairCoefficient n).coefficient =
      (transportedCoefficient n).coefficient := by
    funext point
    change B.indicator (witness.coefficient n).coefficient point =
      B.indicator (witness.coefficient n).coefficient point
    rfl
  have hCoefficient :=
    completedMartingalePart_indistinguishable_of_coefficient_eq
      pairSchedule.usualConditions (pairSchedule.quadraticKernel n)
      (pairSchedule.variationBridge n) (pairSchedule.martingale n)
      (pairSchedule.terminal_memLp n) (pairCoefficient n)
      (transportedCoefficient n) hCoefficientEq
  have hTransport := pairScheduleCompletedMartingalePart_left oldSchedule oldSchedule n
    (oldCoefficient n)
  have hOldStopped := completedMartingaleCoordinate_indistinguishable_stopped
    oldSchedule oldCoefficient n
  have hOld := (restrictedMartingalePart_spec  H B hB).2.2.2 n
  change ProcessIndistinguishable mu
    (completedMartingaleCoordinate pairSchedule transportedCoefficient n)
    (MeasureTheory.stoppedProcess
      (completedMartingaleCoordinate oldSchedule oldCoefficient n)
      (pairScheduleLocalizer oldSchedule oldSchedule n)) at hTransport
  rw [show pairScheduleLocalizer oldSchedule oldSchedule n =
      oldSchedule.localizer n by
    funext omega
    exact min_self _] at hTransport
  exact hNew'.trans <| hCadlag.trans <| hCoefficient.trans <|
    hTransport.trans <| hOldStopped.symm.trans hOld.symm

/-- The intrinsic predictable restriction using the càdlàg glued
martingale representative. -/
noncomputable def restrictPredictableCadlagStrategy
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    SIntegrableStrategy D := by
  let M := restrictedCadlagMartingalePart  hGLeft H B hB
  let A := restrictedFiniteVariationPart B hB H.val
  have hM := restrictedCadlagMartingalePart_spec  hGLeft H B hB
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

/-- Replacing the intrinsic restricted martingale by its càdlàg version
does not change the realized gain graph. -/
theorem restrictPredictableCadlagStrategy_gain_indistinguishable
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ProcessIndistinguishable mu
      (actualRestrictPredictable H B hB).val.stochasticIntegral
      (restrictPredictableCadlagStrategy hGLeft H B hB
        ).stochasticIntegral := by
  have hM := restrictedCadlagMartingalePart_indistinguishable hGLeft H B hB
  change ProcessIndistinguishable mu
    (fun t omega => restrictedMartingalePart  H B hB t omega +
      restrictedFiniteVariationPart B hB H.val t omega)
    (fun t omega => restrictedCadlagMartingalePart  hGLeft H B hB t omega +
      restrictedFiniteVariationPart B hB H.val t omega)
  exact hM.symm.add (ProcessIndistinguishable.refl mu _)

/-- The càdlàg representative is an actual graph in the same intrinsic
carrier. -/
noncomputable def actualRestrictPredictableCadlag
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ActualSIntegrableStrategy (realizationModel G) :=
  (actualRestrictPredictable H B hB).congr
    (restrictPredictableCadlagStrategy hGLeft H B hB) rfl
      (restrictPredictableCadlagStrategy_gain_indistinguishable hGLeft H B hB)

/-- The martingale coordinate of the actual-first càdlàg restriction has
left limits on every path. -/
theorem actualRestrictPredictableCadlag_martingalePart_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ProcessHasLeftLimits
      (actualRestrictPredictableCadlag hGLeft H B hB
        ).val.martingalePart :=
  (restrictedCadlagMartingalePart_spec  hGLeft H B hB).2.2.2.1

/-- The gain of the actual-first càdlàg restriction has left limits on
every path. -/
theorem actualRestrictPredictableCadlag_stochasticIntegral_hasLeftLimits
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ProcessHasLeftLimits
      (actualRestrictPredictableCadlag hGLeft H B hB
        ).val.stochasticIntegral :=
  (actualRestrictPredictableCadlag_martingalePart_hasLeftLimits hGLeft H B hB).add
      (actualRestrictPredictableCadlag hGLeft H B hB
        ).val.finiteVariationPart_hasLeftLimits

/-- The càdlàg actual-first predictable restriction starts from zero. -/
theorem actualRestrictPredictableCadlag_stochasticIntegral_zero
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    (actualRestrictPredictableCadlag hGLeft H B hB
      ).val.stochasticIntegral 0 =ᵐ[mu] 0 := by
  filter_upwards [
    actualRestrictPredictable_stochasticIntegral_zero H B hB,
    (restrictPredictableCadlagStrategy_gain_indistinguishable hGLeft H B hB).eventuallyEq_at 0]
      with omega hOldZero hGain
  exact hGain.symm.trans hOldZero

/-- The càdlàg representative preserves the intrinsic finite-variation
increment identity. -/
theorem actualRestrictPredictableCadlag_finiteVariationPart_increment
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ∀ᵐ omega ∂mu, forall a b : NNReal, a <= b ->
      (actualRestrictPredictableCadlag hGLeft H B hB
          ).val.finiteVariationPart b omega -
          (actualRestrictPredictableCadlag hGLeft H B hB
            ).val.finiteVariationPart a omega =
        FiniteVariationPath.signedMeasure
          (H.val.finiteVariationPart_isBoundedVariation omega)
          (PredictableFiniteVariationRestriction.timeSection B omega ∩
            Ioc a b) := by
  simpa only [actualRestrictPredictableCadlag, actualRestrictPredictable,
    ActualSIntegrableStrategy.congr, restrictPredictableCadlagStrategy,
    restrictPredictableStrategy] using
    actualRestrictPredictable_finiteVariationPart_increment H B hB

/-- The càdlàg representative satisfies the second-moment increment
estimate used by the Lemma 4.7 Hahn consumer. -/
theorem actualRestrictPredictableCadlag_stopped_martingale_increment_l2
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hM : Martingale H.val.martingalePart F mu)
    (hMIncrement : MemLp
      (fun omega => H.val.martingalePart (tau omega) omega -
        H.val.martingalePart 0 omega) (2 : ENNReal) mu) :
    let R := actualRestrictPredictableCadlag hGLeft H B hB
    let Y := MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (tau omega : WithTop NNReal))
    Martingale Y F mu /\
      MemLp (fun omega => Y T omega - Y 0 omega) (2 : ENNReal) mu /\
      (∫ omega, ‖Y T omega - Y 0 omega‖ ^ 2 ∂mu) <=
        ∫ omega, ‖H.val.martingalePart (tau omega) omega -
          H.val.martingalePart 0 omega‖ ^ 2 ∂mu := by
  let Rold := actualRestrictPredictable H B hB
  let R := actualRestrictPredictableCadlag hGLeft H B hB
  let tauTop : Omega -> WithTop NNReal := fun omega => tau omega
  let Yold := MeasureTheory.stoppedProcess Rold.val.martingalePart tauTop
  let Y := MeasureTheory.stoppedProcess R.val.martingalePart tauTop
  change Martingale Y F mu /\
    MemLp (fun omega => Y T omega - Y 0 omega) (2 : ENNReal) mu /\ _
  have hCore := actualRestrictPredictable_stopped_martingale_increment_l2 H B hB tau hTau T hTauT
    hM hMIncrement
  change Martingale Yold F mu /\
    MemLp (fun omega => Yold T omega - Yold 0 omega)
      (2 : ENNReal) mu /\ _ at hCore
  have hStopped : ProcessIndistinguishable mu Y Yold :=
    (restrictedCadlagMartingalePart_indistinguishable hGLeft H B hB).stoppedProcess tauTop
  have hYAdapted : StronglyAdapted F Y :=
    FTAPTheorem42.RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      R.val.martingalePart_isStronglyAdapted hTau
        R.val.martingalePart_isRightContinuous
  have hYMartingale : Martingale Y F mu :=
    hCore.1.congr hYAdapted fun t =>
      (hStopped.eventuallyEq_at t).symm
  have hIncrement : (fun omega => Y T omega - Y 0 omega) =ᵐ[mu]
      fun omega => Yold T omega - Yold 0 omega :=
    (hStopped.eventuallyEq_at T).sub (hStopped.eventuallyEq_at 0)
  have hIntegrand : (fun omega => ‖Y T omega - Y 0 omega‖ ^ 2) =ᵐ[mu]
      fun omega => ‖Yold T omega - Yold 0 omega‖ ^ 2 := by
    filter_upwards [hIncrement] with omega hOmega
    rw [hOmega]
  exact ⟨hYMartingale, (memLp_congr_ae hIncrement).mpr hCore.2.1,
    (le_of_eq (integral_congr_ae hIntegrand)).trans hCore.2.2⟩

/-- The càdlàg intrinsic restriction uses the zero-based completed
martingale coordinate. -/
theorem actualRestrictPredictableCadlag_martingalePart_zero
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    (actualRestrictPredictableCadlag hGLeft H B hB
      ).val.martingalePart 0 =ᵐ[mu] 0 := by
  filter_upwards [
    (restrictedCadlagMartingalePart_indistinguishable hGLeft H B hB).eventuallyEq_at 0,
    restrictedMartingalePart_zero  H B hB]
      with omega hCadlag hZero
  exact hCadlag.trans hZero

end LocalCompletedM2A

end FTAPTheorem42
