/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairFiniteVariation
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticEnergyUniqueness
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticProcessLimit

/-!
# Martingale-energy transport to a pairwise common schedule

The predictable energy measure of the pair-refined source is the restriction
of either old schedule's energy measure to the pair stopping interval.  Thus
both old coefficients remain energy-`L2`, and their completed martingale
integrals agree with the corresponding old integrals stopped at the pair
localizer.  Together with the common finite-variation bridge, this gives two
genuine coefficients on one pair-refined `M2 + A1` source.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge
open BoundedMartingaleQuadraticEnergy.Data
open BoundedMartingaleQuadraticKernel.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The quadratic kernel of the source prefix on the pair-refined schedule. -/
noncomputable def pairScheduleQuadraticKernel
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    BoundedMartingaleQuadraticKernel.Data F mu
      (pairScheduleSourcePrefix left right n).martingalePart
        (pairScheduleHorizon left right n) :=
  Classical.choice <| SquareIntegrableMartingaleQuadraticKernel.exists_data
    left.usualConditions
    (pairScheduleSourcePrefix_martingale left right n)
    (pairScheduleSourcePrefix left right n).martingalePart_isRightContinuous
    (pairScheduleHorizon left right n)
    (pairScheduleSourcePrefix_terminal_memLp left right n)

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleFiniteLocalizer_le_scheduleHorizon
    (left right schedule : LocalCompletedM2ASchedule G) (n : Nat)
    (hPairLe : forall omega,
      pairScheduleLocalizer left right n omega <= schedule.localizer n omega)
    (omega : Omega) :
    pairScheduleFiniteLocalizer left right n omega <= schedule.horizon n := by
  apply WithTop.coe_le_coe.mp
  rw [coe_pairScheduleFiniteLocalizer]
  exact (hPairLe omega).trans (schedule.localizer_le_horizon n omega)

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleFiniteLocalizer_le_pairHorizon
    (left right : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    pairScheduleFiniteLocalizer left right n omega <=
      pairScheduleHorizon left right n :=
  RightContinuousStoppedMartingale.boundedTime_le
    (pairScheduleHorizon left right n) (pairScheduleLocalizer left right n)
      omega

private theorem pairScheduleCoefficient_memLp_two_of_schedule
    (left right schedule : LocalCompletedM2ASchedule G) (n : Nat)
    (hPairLe : forall omega,
      pairScheduleLocalizer left right n omega <= schedule.localizer n omega)
    (hSource : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess (schedule.sourcePrefix n).martingalePart
        (pairScheduleLocalizer left right n)))
    (c : FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n)) :
    MemLp c.coefficient (2 : ENNReal)
      (pairScheduleQuadraticKernel left right n).predictableEnergyMeasure := by
  let tau := pairScheduleFiniteLocalizer left right n
  have hStopped : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess (schedule.sourcePrefix n).martingalePart
        (fun omega => (tau omega : WithTop NNReal))) := by
    simpa only [tau, coe_pairScheduleFiniteLocalizer] using hSource
  exact BoundedMartingaleQuadraticKernel.Data.memLp_two_stoppedProcess_of_restrict
    (schedule.quadraticKernel n) (schedule.martingale n)
    (schedule.sourcePrefix n).martingalePart_isRightContinuous
    (schedule.terminal_memLp n) tau
    (pairScheduleFiniteLocalizer_isStoppingTime left right n)
    (pairScheduleFiniteLocalizer_le_scheduleHorizon left right schedule n
      hPairLe)
    (pairScheduleFiniteLocalizer_le_pairHorizon left right n)
    (pairScheduleSourcePrefix left right n).martingalePart hStopped
    (pairScheduleSourcePrefix_martingale left right n)
    (pairScheduleSourcePrefix left right n).martingalePart_isRightContinuous
    (pairScheduleSourcePrefix_terminal_memLp left right n)
    (pairScheduleQuadraticKernel left right n) c.coefficient_memLp_energy

/-- A left-schedule coefficient remains energy-`L2` on the pair schedule. -/
theorem pairScheduleCoefficient_memLp_two_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (left.variationBridge n) (left.quadraticKernel n)) :
    MemLp c.coefficient (2 : ENNReal)
      (pairScheduleQuadraticKernel left right n).predictableEnergyMeasure :=
  pairScheduleCoefficient_memLp_two_of_schedule left right left n
    (pairScheduleLocalizer_le_left left right n)
    (pairScheduleSourcePrefix_martingalePart_left left right n) c

/-- A right-schedule coefficient remains energy-`L2` on the pair schedule. -/
theorem pairScheduleCoefficient_memLp_two_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (right.variationBridge n) (right.quadraticKernel n)) :
    MemLp c.coefficient (2 : ENNReal)
      (pairScheduleQuadraticKernel left right n).predictableEnergyMeasure :=
  pairScheduleCoefficient_memLp_two_of_schedule left right right n
    (pairScheduleLocalizer_le_right left right n)
    (pairScheduleSourcePrefix_martingalePart_right left right n) c

/-- A left coefficient, now carrying both integrability witnesses on the
pair-refined source. -/
noncomputable def pairScheduleCoefficientLeft
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (left.variationBridge n) (left.quadraticKernel n)) :
    FiniteHorizonM2ACoefficient
      (pairScheduleFiniteVariationBridge left right n)
      (pairScheduleQuadraticKernel left right n) where
  coefficient := c.coefficient
  coefficient_isStronglyMeasurable := c.coefficient_isStronglyMeasurable
  coefficient_memLp_variation := by
    exact memLp_one_commonRefinement_of_left
      (left.variationBridge n) (right.variationBridge n)
      (pairScheduleSourcePrefix_pathVariation_le_left left right n)
      (fun t omega => c.coefficient (t, omega))
      c.coefficient_isStronglyMeasurable c.coefficient_memLp_variation
  coefficient_memLp_energy :=
    pairScheduleCoefficient_memLp_two_left left right n c

/-- A right coefficient, now carrying both integrability witnesses on the
pair-refined source. -/
noncomputable def pairScheduleCoefficientRight
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (right.variationBridge n) (right.quadraticKernel n)) :
    FiniteHorizonM2ACoefficient
      (pairScheduleFiniteVariationBridge left right n)
      (pairScheduleQuadraticKernel left right n) where
  coefficient := c.coefficient
  coefficient_isStronglyMeasurable := c.coefficient_isStronglyMeasurable
  coefficient_memLp_variation := by
    exact memLp_one_commonRefinement_of_right
      (left.variationBridge n) (right.variationBridge n)
      (pairScheduleSourcePrefix_pathVariation_le_right left right n)
      (fun t omega => c.coefficient (t, omega))
      c.coefficient_isStronglyMeasurable c.coefficient_memLp_variation
  coefficient_memLp_energy :=
    pairScheduleCoefficient_memLp_two_right left right n c

private theorem pairScheduleCompletedMartingalePart_of_schedule
    (left right schedule : LocalCompletedM2ASchedule G) (n : Nat)
    (hPairLe : forall omega,
      pairScheduleLocalizer left right n omega <= schedule.localizer n omega)
    (hSource : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess (schedule.sourcePrefix n).martingalePart
        (pairScheduleLocalizer left right n)))
    (c : FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (pc : FiniteHorizonM2ACoefficient
      (pairScheduleFiniteVariationBridge left right n)
      (pairScheduleQuadraticKernel left right n))
    (hpc : pc.coefficient = c.coefficient) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n) pc)
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedMartingalePart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.martingale n) (schedule.terminal_memLp n) c)
        (pairScheduleLocalizer left right n)) := by
  let tau := pairScheduleFiniteLocalizer left right n
  let N := (pairScheduleSourcePrefix left right n).martingalePart
  let Qnew := pairScheduleQuadraticKernel left right n
  have hStopped : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess (schedule.sourcePrefix n).martingalePart
        (fun omega => (tau omega : WithTop NNReal))) := by
    simpa only [N, tau, coe_pairScheduleFiniteLocalizer] using hSource
  have hPcRaw : Function.uncurry pc.integrand
      =ᵐ[Qnew.predictableEnergyMeasure] c.coefficient :=
    (finiteHorizonCoefficient_ae_eq Qnew pc.coefficient).trans
      (Filter.Eventually.of_forall fun point => congrFun hpc point)
  let hRawNew : MemLp c.coefficient (2 : ENNReal)
      Qnew.predictableEnergyMeasure :=
    (memLp_congr_ae hPcRaw).mp pc.integrand_memLp_energy
  have hNewCongr : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right n) Qnew
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n) pc)
      (finiteHorizonMartingaleIntegralProcess left.usualConditions Qnew
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix left right n
          ).martingalePart_isRightContinuous
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        c.coefficient c.coefficient_isStronglyMeasurable hRawNew) :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
        left.usualConditions Qnew
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix left right n
          ).martingalePart_isRightContinuous
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        (Function.uncurry pc.integrand) pc.integrand_isStronglyPredictable
        pc.integrand_memLp_energy c.coefficient
        c.coefficient_isStronglyMeasurable hRawNew hPcRaw
  have hTransport := finiteHorizonMartingaleIntegralProcess_stoppedProcess
      left.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) tau
      (pairScheduleFiniteLocalizer_isStoppingTime left right n)
      (pairScheduleFiniteLocalizer_le_scheduleHorizon left right schedule n
        hPairLe)
      (pairScheduleFiniteLocalizer_le_pairHorizon left right n) N hStopped
      (pairScheduleSourcePrefix_martingale left right n)
      (pairScheduleSourcePrefix left right n
        ).martingalePart_isRightContinuous
      (pairScheduleSourcePrefix_terminal_memLp left right n) Qnew
      c.coefficient c.coefficient_isStronglyMeasurable
      c.coefficient_memLp_energy
  have hStopOld :=
    finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) tau
      (pairScheduleFiniteLocalizer_isStoppingTime left right n)
      (pairScheduleFiniteLocalizer_le_scheduleHorizon left right schedule n
        hPairLe)
      c.coefficient c.coefficient_isStronglyMeasurable
      c.coefficient_memLp_energy
  have hOldRaw := finiteHorizonCoefficient_ae_eq
    (schedule.quadraticKernel n) c.coefficient
  have hOldCongr : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.martingale n) (schedule.terminal_memLp n) c)
      (finiteHorizonMartingaleIntegralProcess schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) c.coefficient
        c.coefficient_isStronglyMeasurable c.coefficient_memLp_energy) :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) (Function.uncurry c.integrand)
        c.integrand_isStronglyPredictable c.integrand_memLp_energy
        c.coefficient c.coefficient_isStronglyMeasurable
        c.coefficient_memLp_energy hOldRaw
  have hOldStopped :=
    hOldCongr.symm.stoppedProcess
      (fun omega => (tau omega : WithTop NNReal))
  simpa only [tau, coe_pairScheduleFiniteLocalizer] using
    hNewCongr.trans (hTransport.trans (hStopOld.trans hOldStopped))

/-- The pair-refined completed martingale integral of a left coefficient is
the old left integral stopped at the common localizer. -/
theorem pairScheduleCompletedMartingalePart_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (left.variationBridge n) (left.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        (pairScheduleCoefficientLeft left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedMartingalePart left.usualConditions
          (left.horizon n) (left.quadraticKernel n) (left.martingale n)
          (left.terminal_memLp n) c) (pairScheduleLocalizer left right n)) :=
  pairScheduleCompletedMartingalePart_of_schedule left right left n
    (pairScheduleLocalizer_le_left left right n)
    (pairScheduleSourcePrefix_martingalePart_left left right n) c
    (pairScheduleCoefficientLeft left right n c) rfl

/-- The pair-refined completed martingale integral of a right coefficient is
the old right integral stopped at the common localizer. -/
theorem pairScheduleCompletedMartingalePart_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (right.variationBridge n) (right.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        (pairScheduleCoefficientRight left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedMartingalePart right.usualConditions
          (right.horizon n) (right.quadraticKernel n) (right.martingale n)
          (right.terminal_memLp n) c) (pairScheduleLocalizer left right n)) :=
  pairScheduleCompletedMartingalePart_of_schedule left right right n
    (pairScheduleLocalizer_le_right left right n)
    (pairScheduleSourcePrefix_martingalePart_right left right n) c
    (pairScheduleCoefficientRight left right n c) rfl

end LocalCompletedM2A

end FTAPTheorem42
