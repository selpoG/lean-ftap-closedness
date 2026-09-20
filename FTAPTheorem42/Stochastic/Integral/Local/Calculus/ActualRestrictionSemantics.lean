/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralStopping
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.FiniteVariationRestriction
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit

/-!
# Analytic semantics of intrinsic predictable restrictions

The local-completed carrier constructs predictable restriction by restricting
each completed coordinate and then gluing.  This file records the analytic
properties of that actual-first output which are consumed by Lemmas 4.7--4.11.
It does not identify the output with the underdetermined raw restriction
record.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

omit [F.IsRightContinuous] in
/-- The global martingale component selected by the intrinsic restriction
starts from zero almost surely. -/
theorem restrictedMartingalePart_zero
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    restrictedMartingalePart  H B hB 0 =ᵐ[mu] 0 := by
  let witness := actualGraphWitness H
  have hCoordinate :=
    (restrictedMartingalePart_spec  H B hB).2.2.2 0
  have hAtZero := hCoordinate.eventuallyEq_at 0
  have hCompletedZero :=
    finiteHorizonMartingaleIntegralProcess_zero
      witness.schedule.usualConditions
      (witness.schedule.quadraticKernel 0)
      (witness.schedule.martingale 0)
      (witness.schedule.sourcePrefix 0).martingalePart_isRightContinuous
      (witness.schedule.terminal_memLp 0)
      (Function.uncurry
        ((witness.coefficient 0).restrictPredictable B hB).integrand)
      ((witness.coefficient 0).restrictPredictable B hB
        ).integrand_isStronglyPredictable
      ((witness.coefficient 0).restrictPredictable B hB
        ).integrand_memLp_energy
  filter_upwards [hAtZero, hCompletedZero] with omega hRestricted hZero
  rw [MeasureTheory.stoppedProcess_eq_of_le bot_le] at hRestricted
  exact hRestricted.trans hZero

/-- The intrinsic restricted gain starts from zero. -/
theorem actualRestrictPredictable_stochasticIntegral_zero
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    (actualRestrictPredictable H B hB).val.stochasticIntegral 0 =ᵐ[mu] 0 :=
  actual_stochasticIntegral_zero (actualRestrictPredictable H B hB)

/-- The assembled finite-variation component has the direct Stieltjes
increments of the predictable restriction. -/
theorem actualRestrictPredictable_finiteVariationPart_increment
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ∀ᵐ omega ∂mu, forall a b : NNReal, a <= b ->
      (actualRestrictPredictable H B hB).val.finiteVariationPart b omega -
          (actualRestrictPredictable H B hB).val.finiteVariationPart a omega =
        FiniteVariationPath.signedMeasure
          (H.val.finiteVariationPart_isBoundedVariation omega)
          (PredictableFiniteVariationRestriction.timeSection B omega ∩
            Ioc a b) :=
  restrictedFiniteVariationPart_increment B hB H.val

/-- The finite stopping time obtained by intersecting a bounded stopping
time with one coordinate of an intrinsic schedule. -/
noncomputable def restrictionCoordinateStop
    (schedule : LocalCompletedM2ASchedule G)
    (tau : Omega -> NNReal) (n : Nat) : Omega -> NNReal :=
  RightContinuousStoppedMartingale.boundedTime (schedule.horizon n)
    (fun omega => min (tau omega : WithTop NNReal)
      (schedule.localizer n omega))

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
@[simp]
theorem coe_restrictionCoordinateStop
    (schedule : LocalCompletedM2ASchedule G)
    (tau : Omega -> NNReal) (n : Nat) (omega : Omega) :
    (restrictionCoordinateStop schedule tau n omega : WithTop NNReal) =
      min (tau omega : WithTop NNReal) (schedule.localizer n omega) := by
  rw [restrictionCoordinateStop,
    RightContinuousStoppedMartingale.coe_boundedTime, min_eq_right]
  exact (min_le_right _ _).trans (schedule.localizer_le_horizon n omega)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem restrictionCoordinateStop_isStoppingTime
    (schedule : LocalCompletedM2ASchedule G)
    {tau : Omega -> NNReal}
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (n : Nat) : IsStoppingTime F (fun omega =>
      (restrictionCoordinateStop schedule tau n omega : WithTop NNReal)) := by
  unfold restrictionCoordinateStop
  exact RightContinuousStoppedMartingale.boundedTime_isStoppingTime
    (hTau.min (schedule.isLocalizingSequence.isStoppingTime n))
    (schedule.horizon n)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem restrictionCoordinateStop_le_tau
    (schedule : LocalCompletedM2ASchedule G)
    (tau : Omega -> NNReal) (n : Nat) (omega : Omega) :
    restrictionCoordinateStop schedule tau n omega <= tau omega := by
  apply WithTop.coe_le_coe.mp
  rw [coe_restrictionCoordinateStop]
  exact min_le_left _ _

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem restrictionCoordinateStop_le_horizon
    (schedule : LocalCompletedM2ASchedule G)
    (tau : Omega -> NNReal) (n : Nat) (omega : Omega) :
    restrictionCoordinateStop schedule tau n omega <= schedule.horizon n :=
  RightContinuousStoppedMartingale.boundedTime_le _ _ _

/-- Intersecting a bounded stopping time with one coordinate of the
intrinsic restriction schedule gives a true martingale. -/
theorem actualRestrictPredictable_coordinate_martingale
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (n : Nat) :
    let R := actualRestrictPredictable H B hB
    let rho := restrictionCoordinateStop
      (actualGraphWitness H).schedule tau n
    Martingale (MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (rho omega : WithTop NNReal))) F mu := by
  let R := actualRestrictPredictable H B hB
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  let rho := restrictionCoordinateStop schedule tau n
  have hRho : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal)) :=
    restrictionCoordinateStop_isStoppingTime schedule hTau n
  have hRhoSigma : forall omega,
      (rho omega : WithTop NNReal) <= schedule.localizer n omega := by
    intro omega
    dsimp only [rho]
    rw [coe_restrictionCoordinateStop]
    exact min_le_right _ _
  let cB := (witness.coefficient n).restrictPredictable B hB
  let completed := finiteHorizonCompletedMartingalePart
    schedule.usualConditions (schedule.horizon n)
      (schedule.quadraticKernel n) (schedule.martingale n)
        (schedule.terminal_memLp n) cB
  have hCoordinate :=
    (restrictedMartingalePart_spec  H B hB).2.2.2 n
  have hStopped := hCoordinate.stoppedProcess
    (fun omega => (rho omega : WithTop NNReal))
  rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
    hRhoSigma] at hStopped
  have hCompletedMartingale : Martingale completed F mu := by
    exact finiteHorizonMartingaleIntegralProcess_isMartingale
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) (Function.uncurry cB.integrand)
      cB.integrand_isStronglyPredictable cB.integrand_memLp_energy
  have hCompletedRight : forall omega t,
      ContinuousWithinAt (completed · omega) (Ici t) t := by
    exact finiteHorizonMartingaleIntegralProcess_rightContinuous
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) (Function.uncurry cB.integrand)
      cB.integrand_isStronglyPredictable cB.integrand_memLp_energy
  have hStoppedCompleted : Martingale
      (MeasureTheory.stoppedProcess completed
        (fun omega => (rho omega : WithTop NNReal))) F mu :=
    FTAPTheorem42.RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hCompletedMartingale hRho hCompletedRight
  have hTargetAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess R.val.martingalePart
        (fun omega => (rho omega : WithTop NNReal))) :=
    FTAPTheorem42.RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        R.val.martingalePart_isStronglyAdapted hRho
          R.val.martingalePart_isRightContinuous
  exact hStoppedCompleted.congr hTargetAdapted fun t =>
    (hStopped.eventuallyEq_at t).symm

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- Restriction by two predictable sets commutes at the coefficient level. -/
theorem FiniteHorizonM2ACoefficient.restrictPredictable_comm
    {P : SIntegrableStrategy D} {T : NNReal}
    {E : SIntegrableFiniteVariationBridge P}
    {Q : BoundedMartingaleQuadraticKernel.Data F mu P.martingalePart T}
    (K : FiniteHorizonM2ACoefficient E Q)
    (A B : Set (NNReal × Omega))
    (hA : MeasurableSet[F.predictable] A)
    (hB : MeasurableSet[F.predictable] B) :
    ((K.restrictPredictable A hA).restrictPredictable B hB).coefficient =
      ((K.restrictPredictable B hB).restrictPredictable A hA).coefficient := by
  funext point
  by_cases hPointA : point ∈ A <;>
    by_cases hPointB : point ∈ B <;>
      simp [FiniteHorizonM2ACoefficient.restrictPredictable_coefficient,
        hPointA, hPointB]

/-- At one schedule coordinate, stopping the intrinsic restricted
martingale at `tau` contracts its terminal `L2` norm by the centered
original martingale sampled at `tau`. -/
theorem actualRestrictPredictable_coordinate_eLpNorm_le
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hM : Martingale H.val.martingalePart F mu)
    (hMIncrement : MemLp
      (fun omega => H.val.martingalePart (tau omega) omega -
        H.val.martingalePart 0 omega) (2 : ENNReal) mu)
    (n : Nat) :
    let R := actualRestrictPredictable H B hB
    let rho := restrictionCoordinateStop
      (actualGraphWitness H).schedule tau n
    eLpNorm (fun omega => R.val.martingalePart (rho omega) omega)
        (2 : ENNReal) mu <=
      eLpNorm (fun omega => H.val.martingalePart (tau omega) omega -
        H.val.martingalePart 0 omega) (2 : ENNReal) mu := by
  classical
  let R := actualRestrictPredictable H B hB
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  let U := schedule.horizon n
  let sigma := schedule.localizer n
  let rho := restrictionCoordinateStop schedule tau n
  let hRho : IsStoppingTime F (fun omega => (rho omega : WithTop NNReal)) :=
    restrictionCoordinateStop_isStoppingTime schedule hTau n
  let I := stochasticIntervalIocZero rho
  let hI : MeasurableSet[F.predictable] I :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hRho
  let c := witness.coefficient n
  let cB := c.restrictPredictable B hB
  let cI := c.restrictPredictable I hI
  let cBI := cB.restrictPredictable I hI
  let cIB := cI.restrictPredictable B hB
  let completed := fun K : FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n) =>
    finiteHorizonCompletedMartingalePart schedule.usualConditions U
      (schedule.quadraticKernel n) (schedule.martingale n)
      (schedule.terminal_memLp n) K
  have hRhoSigma : forall omega,
      (rho omega : WithTop NNReal) <= sigma omega := by
    intro omega
    dsimp only [rho, sigma]
    rw [coe_restrictionCoordinateStop]
    exact min_le_right _ _
  have hRestrictedCoordinate : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess R.val.martingalePart
        (fun omega => (rho omega : WithTop NNReal)))
      (completed cBI) := by
    have hSpec := (restrictedMartingalePart_spec  H B hB).2.2.2 n
    have hStopped := hSpec.stoppedProcess
      (fun omega => (rho omega : WithTop NNReal))
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      hRhoSigma] at hStopped
    have hLocality :=
      finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) rho hRho
        (restrictionCoordinateStop_le_horizon schedule tau n)
        (Function.uncurry cB.integrand)
        cB.integrand_isStronglyPredictable cB.integrand_memLp_energy
    have hIntegrand : Function.uncurry cBI.integrand =
        I.indicator (Function.uncurry cB.integrand) := by
      dsimp only [cBI]
      rw [FiniteHorizonM2ACoefficient.restrictPredictable_integrand]
      rfl
    have hCongruence :=
      finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n)
        (Function.uncurry cBI.integrand)
        cBI.integrand_isStronglyPredictable cBI.integrand_memLp_energy
        (I.indicator (Function.uncurry cB.integrand))
        (cB.integrand_isStronglyPredictable.indicator hI)
        (cB.integrand_memLp_energy.indicator hI)
        (Filter.Eventually.of_forall fun point => congrFun hIntegrand point)
    exact hStopped.trans (hLocality.symm.trans hCongruence.symm)
  have hOriginalCoordinate : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.val.centeredMartingalePart
        (fun omega => (rho omega : WithTop NNReal)))
      (completed cI) := by
    have hSemantics := witness.toScheduleGraphRepresentation
      |>.coordinate_martingaleSemantics n
    let hEnergy := Classical.choose hSemantics
    have hProcess := Classical.choose_spec hSemantics
    have hStopped := hProcess.stoppedProcess
      (fun omega => (rho omega : WithTop NNReal))
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      hRhoSigma] at hStopped
    have hLocality :=
      finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) rho hRho
        (restrictionCoordinateStop_le_horizon schedule tau n)
        (Function.uncurry H.val.integrand)
        H.val.integrand_isPredictable hEnergy
    have hRaw : Function.uncurry c.integrand
        =ᵐ[(schedule.quadraticKernel n).predictableEnergyMeasure]
          Function.uncurry H.val.integrand := by
      have hc := finiteHorizonCoefficient_ae_eq
        (schedule.quadraticKernel n) c.coefficient
      exact hc.trans (Filter.Eventually.of_forall fun point =>
        congrFun (witness.coefficient_eq n) point)
    have hRawI : Function.uncurry cI.integrand
        =ᵐ[(schedule.quadraticKernel n).predictableEnergyMeasure]
          I.indicator (Function.uncurry H.val.integrand) := by
      have hIntegrand : Function.uncurry cI.integrand =
          I.indicator (Function.uncurry c.integrand) := by
        dsimp only [cI]
        rw [FiniteHorizonM2ACoefficient.restrictPredictable_integrand]
        rfl
      filter_upwards [hRaw] with point hPoint
      rw [congrFun hIntegrand point]
      by_cases hPointI : point ∈ I <;> simp [hPointI, hPoint]
    have hCongruence :=
      finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n)
        (Function.uncurry cI.integrand)
        cI.integrand_isStronglyPredictable cI.integrand_memLp_energy
        (I.indicator (Function.uncurry H.val.integrand))
        (H.val.integrand_isPredictable.indicator hI)
        (hEnergy.indicator hI) hRawI
    exact hStopped.trans (hLocality.symm.trans hCongruence.symm)
  have hCommute : ProcessIndistinguishable mu (completed cBI)
      (completed cIB) :=
    completedMartingalePart_indistinguishable_of_coefficient_eq
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.variationBridge n) (schedule.martingale n)
      (schedule.terminal_memLp n) cBI cIB
      (FiniteHorizonM2ACoefficient.restrictPredictable_comm
        c B I hB hI)
  have hContraction : eLpNorm (completed cIB U) (2 : ENNReal) mu <=
      eLpNorm (completed cI U) (2 : ENNReal) mu :=
    finiteHorizonCompletedMartingalePart_restrictPredictable_eLpNorm_le
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n) (schedule.terminal_memLp n) B hB cI
  have hRhoU : forall omega, rho omega <= U :=
    restrictionCoordinateStop_le_horizon schedule tau n
  have hRestrictedSample :
      (fun omega => R.val.martingalePart (rho omega) omega) =ᵐ[mu]
        completed cBI U := by
    filter_upwards [hRestrictedCoordinate.eventuallyEq_at U]
      with omega hOmega
    simpa only [MeasureTheory.stoppedProcess,
      min_eq_right (WithTop.coe_le_coe.mpr (hRhoU omega)),
      WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe] using hOmega
  have hOriginalSample :
      (fun omega => H.val.martingalePart (rho omega) omega -
        H.val.martingalePart 0 omega) =ᵐ[mu] completed cI U := by
    filter_upwards [hOriginalCoordinate.eventuallyEq_at U]
      with omega hOmega
    simpa only [SIntegrableStrategy.centeredMartingalePart,
      MeasureTheory.stoppedProcess,
      min_eq_right (WithTop.coe_le_coe.mpr (hRhoU omega)),
      WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe] using hOmega
  have hCoordinateBound :
      eLpNorm (fun omega => R.val.martingalePart (rho omega) omega)
          (2 : ENNReal) mu <=
        eLpNorm (fun omega => H.val.martingalePart (rho omega) omega -
          H.val.martingalePart 0 omega) (2 : ENNReal) mu := by
    calc
      eLpNorm (fun omega => R.val.martingalePart (rho omega) omega)
          (2 : ENNReal) mu = eLpNorm (completed cBI U)
          (2 : ENNReal) mu := eLpNorm_congr_ae hRestrictedSample
      _ = eLpNorm (completed cIB U) (2 : ENNReal) mu :=
        eLpNorm_congr_ae (hCommute.eventuallyEq_at U)
      _ <= eLpNorm (completed cI U) (2 : ENNReal) mu := hContraction
      _ = eLpNorm (fun omega => H.val.martingalePart (rho omega) omega -
          H.val.martingalePart 0 omega) (2 : ENNReal) mu :=
        (eLpNorm_congr_ae hOriginalSample).symm
  exact hCoordinateBound.trans
    (FTAPTheorem42.Martingale.centered_sample_memLp_two_and_eLpNorm_le
      hM
      H.val.martingalePart_isRightContinuous hRho hTau
      (restrictionCoordinateStop_le_tau schedule tau n) hTauT
      hMIncrement).2

/-- The intrinsic predictable restriction, stopped at a bounded stopping
time, has a true square-integrable martingale component.  Its terminal
`L2` norm contracts the centered stopped martingale of the input. -/
theorem actualRestrictPredictable_stopped_martingale_l2
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hM : Martingale H.val.martingalePart F mu)
    (hMIncrement : MemLp
      (fun omega => H.val.martingalePart (tau omega) omega -
        H.val.martingalePart 0 omega) (2 : ENNReal) mu) :
    let R := actualRestrictPredictable H B hB
    let Y := MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (tau omega : WithTop NNReal))
    Martingale Y F mu /\ MemLp (Y T) (2 : ENNReal) mu /\
      eLpNorm (Y T) (2 : ENNReal) mu <=
        eLpNorm (fun omega => H.val.martingalePart (tau omega) omega -
          H.val.martingalePart 0 omega) (2 : ENNReal) mu := by
  classical
  let R := actualRestrictPredictable H B hB
  let schedule := (actualGraphWitness H).schedule
  let rho : Nat -> Omega -> NNReal := fun n =>
    restrictionCoordinateStop schedule tau n
  let X : Nat -> Process Omega := fun n =>
    MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (rho n omega : WithTop NNReal))
  let Y : Process Omega := MeasureTheory.stoppedProcess
    R.val.martingalePart (fun omega => (tau omega : WithTop NNReal))
  let B0 : ENNReal := eLpNorm
    (fun omega => H.val.martingalePart (tau omega) omega -
      H.val.martingalePart 0 omega) (2 : ENNReal) mu
  change Martingale Y F mu /\ MemLp (Y T) (2 : ENNReal) mu /\
    eLpNorm (Y T) (2 : ENNReal) mu <= B0
  have hB0Top : B0 ≠ ⊤ := hMIncrement.eLpNorm_ne_top
  let bound : NNReal := B0.toNNReal
  have hBoundCoe : (bound : ENNReal) = B0 := ENNReal.coe_toNNReal hB0Top
  have hXMartingale : forall n, Martingale (X n) F mu := by
    intro n
    simpa only [X, rho, R, schedule] using
      actualRestrictPredictable_coordinate_martingale H B hB tau hTau n
  have hYAdapted : StronglyAdapted F Y := by
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      R.val.martingalePart_isStronglyAdapted hTau
        R.val.martingalePart_isRightContinuous
  have hLimit : ∀ t, ∀ᵐ omega ∂mu,
      Tendsto (fun n => X n t omega) atTop (nhds (Y t omega)) := by
    intro t
    filter_upwards [schedule.isLocalizingSequence.tendsto_top]
      with omega hTop
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    have hEventually : ∀ᶠ n in atTop,
        (tau omega : WithTop NNReal) <= schedule.localizer n omega :=
      (hTop (tau omega)).mono fun _ hn => hn.le
    apply tendsto_const_nhds.congr'
    filter_upwards [hEventually] with n hn
    have hRho : (rho n omega : WithTop NNReal) =
        (tau omega : WithTop NNReal) := by
      dsimp only [rho]
      rw [coe_restrictionCoordinateStop, min_eq_left hn]
    dsimp only [X, Y]
    simp only [MeasureTheory.stoppedProcess, hRho]
  have hRhoT : forall n omega, rho n omega <= T := by
    intro n omega
    exact (restrictionCoordinateStop_le_tau schedule tau n omega).trans
      (hTauT omega)
  have hXTerminalEq : forall n, X n T =
      fun omega => R.val.martingalePart (rho n omega) omega := by
    intro n
    funext omega
    dsimp only [X]
    simp only [MeasureTheory.stoppedProcess,
      min_eq_right (WithTop.coe_le_coe.mpr (hRhoT n omega)),
      WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  have hXTerminalNorm : forall n,
      eLpNorm (X n T) (2 : ENNReal) mu <= (bound : ENNReal) := by
    intro n
    rw [hXTerminalEq n, hBoundCoe]
    exact actualRestrictPredictable_coordinate_eLpNorm_le H B hB tau hTau T hTauT hM hMIncrement n
  have hXTerminalMem : forall n, MemLp (X n T) (2 : ENNReal) mu := by
    intro n
    exact (hXTerminalNorm n).trans_lt ENNReal.coe_lt_top
  have hXNorm : forall n t,
      eLpNorm (X n t) (2 : ENNReal) mu <= bound := by
    intro n t
    by_cases ht : t <= T
    · exact
        (FTAPTheorem42.MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
            (hXMartingale n) ht (hXTerminalMem n)).2.trans
              (hXTerminalNorm n)
    · have hTt : T <= t := le_of_not_ge ht
      have hEq : X n t = X n T := by
        funext omega
        dsimp only [X]
        simp only [MeasureTheory.stoppedProcess,
          min_eq_right
            (WithTop.coe_le_coe.mpr ((hRhoT n omega).trans hTt)),
          min_eq_right (WithTop.coe_le_coe.mpr (hRhoT n omega))]
      rw [hEq]
      exact hXTerminalNorm n
  have hYMartingale : Martingale Y F mu :=
    Martingale.of_ae_tendsto_of_eLpNorm_two_le X Y hXMartingale
      hYAdapted hLimit bound hXNorm
  have hYNormBound : eLpNorm (Y T) (2 : ENNReal) mu <=
      (bound : ENNReal) := by
    exact Lp.eLpNorm_le_of_ae_tendsto
      (Filter.Eventually.of_forall fun n => hXNorm n T)
      (fun n => (((hXMartingale n).stronglyMeasurable T).mono
        (F.le T)).aestronglyMeasurable)
      ((hYAdapted T).mono (F.le T)).aestronglyMeasurable (hLimit T)
  have hYTerminalMem : MemLp (Y T) (2 : ENNReal) mu := by
    exact hYNormBound.trans_lt ENNReal.coe_lt_top
  refine ⟨hYMartingale, hYTerminalMem, ?_⟩
  rw [hBoundCoe] at hYNormBound
  exact hYNormBound

/-- The same intrinsic stopped restriction satisfies the second-moment
inequality used by the Lemma 4.7 Hahn consumer. -/
theorem actualRestrictPredictable_stopped_martingale_increment_l2
    (H : ActualSIntegrableStrategy (realizationModel G))
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (T : NNReal) (hTauT : forall omega, tau omega <= T)
    (hM : Martingale H.val.martingalePart F mu)
    (hMIncrement : MemLp
      (fun omega => H.val.martingalePart (tau omega) omega -
        H.val.martingalePart 0 omega) (2 : ENNReal) mu) :
    let R := actualRestrictPredictable H B hB
    let Y := MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (tau omega : WithTop NNReal))
    Martingale Y F mu /\
      MemLp (fun omega => Y T omega - Y 0 omega) (2 : ENNReal) mu /\
      (∫ omega, ‖Y T omega - Y 0 omega‖ ^ 2 ∂mu) <=
        ∫ omega, ‖H.val.martingalePart (tau omega) omega -
          H.val.martingalePart 0 omega‖ ^ 2 ∂mu := by
  let R := actualRestrictPredictable H B hB
  let Y := MeasureTheory.stoppedProcess R.val.martingalePart
    (fun omega => (tau omega : WithTop NNReal))
  change Martingale Y F mu /\
    MemLp (fun omega => Y T omega - Y 0 omega) (2 : ENNReal) mu /\ _
  have hCore := actualRestrictPredictable_stopped_martingale_l2 H B hB tau hTau T hTauT hM
    hMIncrement
  change Martingale Y F mu /\ MemLp (Y T) (2 : ENNReal) mu /\ _ at hCore
  have hYZero : Y 0 =ᵐ[mu] 0 := by
    filter_upwards [restrictedMartingalePart_zero  H B hB]
      with omega hZero
    change MeasureTheory.stoppedProcess R.val.martingalePart
      (fun omega => (tau omega : WithTop NNReal)) 0 omega = 0
    rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
    exact hZero
  have hIncrementEq : (fun omega => Y T omega - Y 0 omega) =ᵐ[mu]
      Y T := by
    filter_upwards [hYZero] with omega hZero
    change Y 0 omega = 0 at hZero
    rw [hZero, sub_zero]
  have hIncrementMem : MemLp (fun omega => Y T omega - Y 0 omega)
      (2 : ENNReal) mu :=
    (memLp_congr_ae hIncrementEq).2 hCore.2.1
  have hIncrementNorm : eLpNorm
      (fun omega => Y T omega - Y 0 omega) (2 : ENNReal) mu <=
        eLpNorm (fun omega => H.val.martingalePart (tau omega) omega -
          H.val.martingalePart 0 omega) (2 : ENNReal) mu :=
    (le_of_eq (eLpNorm_congr_ae hIncrementEq)).trans hCore.2.2
  exact ⟨hCore.1, hIncrementMem,
    integral_norm_sq_le_of_eLpNorm_two_le hIncrementMem hMIncrement
      hIncrementNorm⟩

end LocalCompletedM2A

end FTAPTheorem42
