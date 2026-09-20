/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageFiniteVariation
import FTAPTheorem42.Stochastic.Integral.Local.Construction.FiniteVariationStieltjesCalculus

/-!
# Realization of the Mémín limit on intrinsic joint passages

The actual joint-passage convexifications select one predictable integrand
which is square-integrable for every joint martingale energy control.  The
range finite-variation bridge places the same representative in every
variation `L¹` space.  This module combines the two completed component
identities into an exhaustive graph witness for the raw component-sum limit.

The generic endpoint keeps the actual source representative and its
Stieltjes calculus explicit. For a zero-based unit source, the intrinsic
carrier constructs both from the completed base schedule, yielding a final
endpoint with no supplied stopping or restriction calculus. An arbitrary
raw locally integrable source is not identified with the unit market graph.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
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

/-- The raw limit graph using exactly the predictable representative selected
from the actual intrinsic joint-passage convexifications. -/
noncomputable def intrinsicJointPassageLimitStrategyCandidate
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat) :
    SIntegrableStrategy D where
  integrand := fun t omega =>
    intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)
  stochasticIntegral := fun t omega =>
    data.martingaleLimit t omega + data.finiteVariationLimit t omega
  martingalePart := data.martingaleLimit
  finiteVariationPart := data.finiteVariationLimit
  finiteVariationMeasure := 0
  integrand_isPredictable :=
    intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff
  stochasticIntegral_isStronglyAdapted :=
    data.martingaleLimit_stronglyAdapted.add
      data.finiteVariationLimit_isStronglyPredictable.stronglyAdapted
  stochasticIntegral_isRightContinuous := fun omega t =>
    (data.martingaleLimit_rightContinuous omega t).add
      (data.finiteVariationLimit_rightContinuous omega t)
  martingalePart_isLocalMartingale := data.martingaleLimit_localMartingale
  martingalePart_isStronglyAdapted := data.martingaleLimit_stronglyAdapted
  martingalePart_isRightContinuous := data.martingaleLimit_rightContinuous
  finiteVariationPart_isPredictable :=
    data.finiteVariationLimit_isStronglyPredictable
  finiteVariationPart_isRightContinuous :=
    data.finiteVariationLimit_rightContinuous
  finiteVariationPart_isBoundedVariation :=
    data.finiteVariationLimit_boundedVariation
  integral_decomposition := ProcessIndistinguishable.refl mu _
  source_decomposition := D.decomposition

/-- The completed martingale component of the selected exact coefficient is
the intrinsic joint stop of the existing martingale component limit. -/
theorem intrinsicJointPassageSelectedM2ACoefficient_martingalePart
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (hEnergy : forall n, MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageSchedule base data).quadraticKernel n
        ).predictableEnergyMeasure)
    (hMartingale : forall n, ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        (intrinsicJointPassageSchedule base data).usualConditions
        ((intrinsicJointPassageSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageSchedule base data).martingale n)
        ((intrinsicJointPassageSchedule base data).sourcePrefix n
          ).martingalePart_isRightContinuous
        ((intrinsicJointPassageSchedule base data).terminal_memLp n)
        (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy n))
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          ((intrinsicJointPassageSchedule base data).localizer n))
        (fun _ => ((intrinsicJointPassageSchedule base data).horizon n :
          WithTop NNReal))))
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess data.martingaleLimit
        ((intrinsicJointPassageRangeSchedule base data).localizer n))
      (finiteHorizonCompletedMartingalePart
        (intrinsicJointPassageRangeSchedule base data).usualConditions
        ((intrinsicJointPassageRangeSchedule base data).horizon n)
        ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageRangeSchedule base data).martingale n)
        ((intrinsicJointPassageRangeSchedule base data).terminal_memLp n)
        (intrinsicJointPassageSelectedM2ACoefficient base Gactual hGactual
          Cfv data w cutoff hCutoff n (hEnergy n))) := by
  let target := intrinsicJointPassageRangeSchedule base data
  let selected := intrinsicJointPassageSelectedIntegrand data w cutoff
  let c := intrinsicJointPassageSelectedM2ACoefficient
    base Gactual hGactual Cfv data w cutoff hCutoff n (hEnergy n)
  have hRestricted : Function.uncurry c.integrand =ᵐ[
      (target.quadraticKernel n).predictableEnergyMeasure] selected := by
    exact finiteHorizonCoefficient_ae_eq
      (target.quadraticKernel n) c.coefficient
  have hCongr : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart target.usualConditions
        (target.horizon n) (target.quadraticKernel n)
          (target.martingale n) (target.terminal_memLp n) c)
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (target.quadraticKernel n) (target.martingale n)
        (target.sourcePrefix n).martingalePart_isRightContinuous
        (target.terminal_memLp n) selected
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy
          n)) := by
    exact finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      target.usualConditions (target.quadraticKernel n)
      (target.martingale n)
      (target.sourcePrefix n).martingalePart_isRightContinuous
      (target.terminal_memLp n) (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy
      selected
      (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy n)
        hRestricted
  have hIdentified : ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (target.quadraticKernel n) (target.martingale n)
        (target.sourcePrefix n).martingalePart_isRightContinuous
        (target.terminal_memLp n) selected
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy n))
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          (target.localizer n))
        (fun _ => (target.horizon n : WithTop NNReal))) := by
    exact hMartingale n
  have hCollapse : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess data.martingaleLimit
        (target.localizer n))
      (fun _ => (target.horizon n : WithTop NNReal)) =
      MeasureTheory.stoppedProcess data.martingaleLimit
        (target.localizer n) := by
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_left]
    exact target.localizer_le_horizon n
  rw [hCollapse] at hIdentified
  exact (hCongr.trans hIdentified).symm

/-- At one intrinsic joint coordinate, the selected coefficient realizes the
stopped component-sum gain in the concrete completed `M² + A¹` graph. -/
theorem intrinsicJointPassageLimitStrategyCandidate_oneCoordinate
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (hEnergy : forall n, MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageSchedule base data).quadraticKernel n
        ).predictableEnergyMeasure)
    (hMartingale : forall n, ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        (intrinsicJointPassageSchedule base data).usualConditions
        ((intrinsicJointPassageSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageSchedule base data).martingale n)
        ((intrinsicJointPassageSchedule base data).sourcePrefix n
          ).martingalePart_isRightContinuous
        ((intrinsicJointPassageSchedule base data).terminal_memLp n)
        (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy n))
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          ((intrinsicJointPassageSchedule base data).localizer n))
        (fun _ => ((intrinsicJointPassageSchedule base data).horizon n :
          WithTop NNReal))))
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (intrinsicJointPassageLimitStrategyCandidate data w cutoff
          ).stochasticIntegral
        ((intrinsicJointPassageRangeSchedule base data).localizer n))
      (finiteHorizonCompletedM2AGain
        (intrinsicJointPassageRangeSchedule base data).usualConditions
        ((intrinsicJointPassageRangeSchedule base data).horizon n)
        ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageRangeSchedule base data).variationBridge n)
        ((intrinsicJointPassageRangeSchedule base data).martingale n)
        ((intrinsicJointPassageRangeSchedule base data).terminal_memLp n)
        (intrinsicJointPassageSelectedM2ACoefficient base Gactual hGactual
          Cfv data w cutoff hCutoff n (hEnergy n))) := by
  let target := intrinsicJointPassageRangeSchedule base data
  let c := intrinsicJointPassageSelectedM2ACoefficient
    base Gactual hGactual Cfv data w cutoff hCutoff n (hEnergy n)
  have hM := intrinsicJointPassageSelectedM2ACoefficient_martingalePart
    base Gactual hGactual Cfv data w cutoff hCutoff hEnergy hMartingale n
  have hA :=
    intrinsicJointPassageSelectedM2ACoefficient_finiteVariationPart
      base Gactual hGactual Cfv data w cutoff hCutoff n (hEnergy n)
  have hAStop : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess data.finiteVariationLimit
        (target.localizer n))
      (finiteHorizonCompletedFiniteVariationPart target.usualConditions
        (target.horizon n) (target.quadraticKernel n)
          (target.variationBridge n) c) := by
    filter_upwards [hA] with omega hOmega
    intro t
    rw [<- hOmega t]
    simp only [MeasureTheory.stoppedProcess,
      FiniteVariationStoppedPath.stopAt]
    rw [show target.localizer n omega =
        (intrinsicJointPassageFiniteLocalizer base data n omega :
          WithTop NNReal) by
      exact (coe_intrinsicJointPassageFiniteLocalizer
        base data n omega).symm]
    rw [<- WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  filter_upwards [hM, hAStop] with omega hMOmega hAOmega
  intro t
  change data.martingaleLimit
        ((min (t : WithTop NNReal) (target.localizer n omega)).untopA) omega +
      data.finiteVariationLimit
        ((min (t : WithTop NNReal) (target.localizer n omega)).untopA) omega =
    finiteHorizonCompletedMartingalePart target.usualConditions
        (target.horizon n) (target.quadraticKernel n)
          (target.martingale n) (target.terminal_memLp n) c t omega +
      finiteHorizonCompletedFiniteVariationPart target.usualConditions
        (target.horizon n) (target.quadraticKernel n)
          (target.variationBridge n) c t omega
  have hm := hMOmega t
  change data.martingaleLimit
      ((min (t : WithTop NNReal) (target.localizer n omega)).untopA) omega =
    finiteHorizonCompletedMartingalePart target.usualConditions
      (target.horizon n) (target.quadraticKernel n)
        (target.martingale n) (target.terminal_memLp n) c t omega at hm
  have ha := hAOmega t
  change data.finiteVariationLimit
      ((min (t : WithTop NNReal) (target.localizer n omega)).untopA) omega =
    finiteHorizonCompletedFiniteVariationPart target.usualConditions
      (target.horizon n) (target.quadraticKernel n)
        (target.variationBridge n) c t omega at ha
  rw [hm, ha]

/-- The selected martingale identities and the range-controlled
finite-variation identities form one exhaustive graph witness for the raw
component-sum limit. -/
noncomputable def intrinsicJointPassageLimitStrategyCandidate_graphWitness
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (hEnergy : forall n, MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageSchedule base data).quadraticKernel n
        ).predictableEnergyMeasure)
    (hMartingale : forall n, ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        (intrinsicJointPassageSchedule base data).usualConditions
        ((intrinsicJointPassageSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageSchedule base data).martingale n)
        ((intrinsicJointPassageSchedule base data).sourcePrefix n
          ).martingalePart_isRightContinuous
        ((intrinsicJointPassageSchedule base data).terminal_memLp n)
        (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy n))
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          ((intrinsicJointPassageSchedule base data).localizer n))
        (fun _ => ((intrinsicJointPassageSchedule base data).horizon n :
          WithTop NNReal)))) :
    GraphWitness G
      (intrinsicJointPassageLimitStrategyCandidate data w cutoff) where
  schedule := intrinsicJointPassageRangeSchedule base data
  coefficient := fun n =>
    intrinsicJointPassageSelectedM2ACoefficient
      base Gactual hGactual Cfv data w cutoff hCutoff n (hEnergy n)
  coefficient_eq := fun _ => rfl
  stoppedGain_eq := fun n =>
    intrinsicJointPassageLimitStrategyCandidate_oneCoordinate
      base Gactual hGactual Cfv data w cutoff hCutoff
        hEnergy hMartingale n

/-- The completed martingale construction and the finite-variation range
control therefore produce an actual intrinsic local-completed graph for the
Mémín component-sum limit. -/
theorem exists_intrinsicJointPassageLimitStrategyCandidate_isRealized
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat),
      StrictMono cutoff ∧
        (realizationModel G).IsRealized
          (intrinsicJointPassageLimitStrategyCandidate data w cutoff) := by
  obtain ⟨w, cutoff, hEnergy, hCutoff, hMartingale⟩ :=
    exists_intrinsicJointPassage_selectedMartingaleIntegral base data
  refine ⟨w, cutoff, hCutoff, ?_⟩
  exact ⟨intrinsicJointPassageLimitStrategyCandidate_graphWitness
    base Gactual hGactual Cfv data w cutoff hCutoff
      hEnergy hMartingale⟩

/-- For a zero-based unit-integrand source, the supplied completed schedule
itself provides the actual local source required by the Mémín limit theorem.
This form takes the finite-variation Stieltjes calculus as an input.
The intrinsic theorem below constructs that calculus from the same schedule. -/
theorem
    exists_intrinsicJointPassageLimitStrategyCandidate_isRealized_of_unitSource
    (base : LocalCompletedM2ASchedule G)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hZero : G.stochasticIntegral 0 =ᵐ[mu] 0)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) (actualUnitSource base hUnit hZero))
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat),
      StrictMono cutoff ∧
        (realizationModel G).IsRealized
          (intrinsicJointPassageLimitStrategyCandidate data w cutoff) := by
  exact exists_intrinsicJointPassageLimitStrategyCandidate_isRealized
    base (actualUnitSource base hUnit hZero) rfl Cfv data

/-- On the intrinsic local-completed carrier, a zero-based unit source
supplies both source actuality and the finite-variation Stieltjes semantics.
The joint passages and Stieltjes semantics are constructed directly,
so no stopping or restriction calculus is an additional input. -/
theorem
    exists_intrinsicJointPassageLimitStrategyCandidate_isRealized_intrinsic
    (base : LocalCompletedM2ASchedule G)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hZero : G.stochasticIntegral 0 =ᵐ[mu] 0)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat),
      StrictMono cutoff ∧
        (realizationModel G).IsRealized
          (intrinsicJointPassageLimitStrategyCandidate data w cutoff) := by
  exact
    exists_intrinsicJointPassageLimitStrategyCandidate_isRealized_of_unitSource
      base hUnit hZero
        (finiteVariationStieltjesCalculus base hUnit hZero) data

end LocalCompletedM2A

end FTAPTheorem42
