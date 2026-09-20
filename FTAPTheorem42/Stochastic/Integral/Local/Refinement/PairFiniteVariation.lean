/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Localization.CommonRefinementFiniteVariationBridge
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedFiniteVariationStopping
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessGeneralMeasure
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairScheduleSource
import FTAPTheorem42.Stochastic.FiniteVariation.VariationDirection

/-!
# Finite-variation transport to a pairwise common schedule

The source prefix of the pairwise minimum schedule is, outside one null set,
the further stop of either old source prefix.  Hence its path variation is
dominated by both old path variations.  A single common-refinement bridge
therefore carries the variation-`L1` half of coefficients represented on
either old schedule.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

omit [MeasurableSpace Omega] [SigmaFiniteFiltration mu F] in
/-- The intrinsic Jordan direction is insensitive to the proof term used
for an unchanged path.  Keeping this small congruence separate prevents the
dependent proof arguments of the surrounding strategy structures from being
unfolded by `subst`. -/
private theorem variationDirection_eq_of_path_eq
    {A B : NNReal -> Real} (hA : BoundedVariationOn A Set.univ)
    (hB : BoundedVariationOn B Set.univ) (hAB : A = B) :
    FiniteVariationPath.variationDirection hA =
      FiniteVariationPath.variationDirection hB := by
  subst B
  rfl

omit [SigmaFiniteFiltration mu F] in
/-- Raw cumulative finite-variation integration is local in its source
path.  If the new source is the old source stopped at `tau`, coefficients
which agree up to `tau` produce the stopped old integral. -/
theorem finiteVariationIntegralProcess_eq_stopped_of_path
    {H L : SIntegrableStrategy D}
    (Eold : SIntegrableFiniteVariationBridge H)
    (Enew : SIntegrableFiniteVariationBridge L)
    (tau : Omega -> WithTop NNReal) (T : NNReal)
    (hTauT : forall omega, tau omega <= (T : WithTop NNReal))
    (hPath : ProcessIndistinguishable mu L.finiteVariationPart
      (MeasureTheory.stoppedProcess H.finiteVariationPart tau))
    (Kold Knew : Process Omega)
    (hCoefficient : forall omega u,
      u <= RightContinuousStoppedMartingale.boundedTime T tau omega ->
        Knew u omega = Kold u omega) :
    ProcessIndistinguishable mu
      (finiteVariationIntegralProcess Enew Knew)
      (MeasureTheory.stoppedProcess
        (finiteVariationIntegralProcess Eold Kold) tau) := by
  filter_upwards [hPath,
      Enew.jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection,
      Eold.jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection]
      with omega hPathOmega hNewDensity hOldDensity
  intro t
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau omega
  let oldPath := fun u => H.finiteVariationPart u omega
  let newPath := fun u => L.finiteVariationPart u omega
  let hOld := H.finiteVariationPart_isBoundedVariation omega
  let hNew := L.finiteVariationPart_isBoundedVariation omega
  let hStopped := FiniteVariationStoppedPath.boundedVariationOn_stopAt hOld sigma
  have hStoppedPath :
      (fun u => MeasureTheory.stoppedProcess H.finiteVariationPart tau u omega) =
        FiniteVariationStoppedPath.stopAt oldPath sigma := by
    exact RightContinuousStoppedMartingale.stoppedProcess_path_eq_stopAt_boundedTime
      H.finiteVariationPart tau T hTauT omega
  have hNewPath : newPath = FiniteVariationStoppedPath.stopAt oldPath sigma :=
    (funext hPathOmega).trans hStoppedPath
  have hSigned : FiniteVariationPath.signedMeasure hNew =
      FiniteVariationPath.signedMeasure hStopped :=
    FiniteVariationPath.signedMeasure_eq_of_eq hNew hStopped hNewPath
  have hVariation :
      (FiniteVariationPath.signedMeasure hNew).totalVariation =
        (FiniteVariationPath.signedMeasure hOld).totalVariation.restrict
          (Ioc 0 sigma) := by
    rw [congrArg SignedMeasure.totalVariation hSigned]
    exact FiniteVariationStoppedPath.totalVariation_stopAt_eq_restrict_Ioc
      oldPath hOld (H.finiteVariationPart_isRightContinuous omega) sigma
  have hDirection : FiniteVariationPath.variationDirection hNew =
      FiniteVariationPath.variationDirection hStopped := by
    exact variationDirection_eq_of_path_eq hNew hStopped hNewPath
  have hStoppedDirection :=
    FiniteVariationStoppedPath.variationDirection_stopAt_ae_eq
      oldPath hOld (H.finiteVariationPart_isRightContinuous omega) sigma
  have hStoppedDirectionNew :
      FiniteVariationPath.variationDirection hStopped =ᵐ[
        (FiniteVariationPath.signedMeasure hNew).totalVariation]
        FiniteVariationPath.variationDirection hOld := by
    rw [hSigned]
    exact hStoppedDirection
  let target :=
    (FiniteVariationPath.signedMeasure hOld).totalVariation.restrict
      (Ioc 0 (min t sigma))
  have hSet : Ioc (0 : NNReal) t ∩ Ioc 0 sigma = Ioc 0 (min t sigma) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨h0u, hut⟩, ⟨_, huSigma⟩⟩
      exact ⟨h0u, le_min hut huSigma⟩
    · rintro ⟨h0u, hu⟩
      exact ⟨⟨h0u, hu.trans (min_le_left t sigma)⟩,
        ⟨h0u, hu.trans (min_le_right t sigma)⟩⟩
  have hUpTo : pathVariationMeasureUpTo Enew t omega = target := by
    unfold pathVariationMeasureUpTo target
    rw [hVariation, Measure.restrict_restrict measurableSet_Ioc, hSet]
  have hTargetLeNew : target <=
      (FiniteVariationPath.signedMeasure hNew).totalVariation := by
    rw [hVariation]
    exact Measure.restrict_mono_set _
      (Ioc_subset_Ioc_right (min_le_right t sigma))
  have hTargetLeOld : target <=
      (FiniteVariationPath.signedMeasure hOld).totalVariation :=
    Measure.restrict_le_self
  have hTargetMem : ∀ᵐ u ∂target, u ∈ Ioc 0 (min t sigma) :=
    ae_restrict_mem measurableSet_Ioc
  have hIntegrand :
      (fun u => finiteVariationIntegralDensity Enew Knew (u, omega)) =ᵐ[target]
        fun u => finiteVariationIntegralDensity Eold Kold (u, omega) := by
    filter_upwards [ae_mono hTargetLeNew hNewDensity,
        ae_mono hTargetLeOld hOldDensity,
        ae_mono hTargetLeNew hStoppedDirectionNew, hTargetMem]
        with u hNewD hOldD hStopD hu
    unfold finiteVariationIntegralDensity
    rw [hNewD, hDirection, hStopD, hOldD,
      hCoefficient omega u (hu.2.trans (min_le_right t sigma))]
  rw [finiteVariationIntegralProcess, hUpTo]
  have hStoppedRaw := RightContinuousStoppedMartingale.stoppedProcess_path_eq_stopAt_boundedTime
    (finiteVariationIntegralProcess Eold Kold) tau T hTauT omega
  rw [congrFun hStoppedRaw t]
  unfold FiniteVariationStoppedPath.stopAt
  change (∫ u, finiteVariationIntegralDensity Enew Knew (u, omega) ∂target) =
    ∫ u, finiteVariationIntegralDensity Eold Kold (u, omega) ∂target
  exact integral_congr_ae hIntegrand

omit [MeasurableSpace Omega] [SigmaFiniteFiltration mu F] in
/-- Two deterministic horizon restrictions of the same raw coefficient
agree at every time lying below both horizons. -/
private theorem finiteHorizonCoefficient_eq_of_le
    (f : NNReal × Omega -> Real) (U V u : NNReal) (omega : Omega)
    (huU : u <= U) (huV : u <= V) :
    finiteHorizonCoefficient U f u omega =
      finiteHorizonCoefficient V f u omega := by
  unfold finiteHorizonCoefficient
  by_cases hPos : 0 < u
  · rw [PredictableProcess.restrict_apply_of_mem,
      PredictableProcess.restrict_apply_of_mem]
    · exact (mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => V) u omega).2 ⟨hPos, huV⟩
    · exact (mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => U) u omega).2 ⟨hPos, huU⟩
  · have hZero : u = 0 := le_antisymm (not_lt.mp hPos) bot_le
    subst u
    rw [PredictableProcess.restrict_apply_of_notMem,
      PredictableProcess.restrict_apply_of_notMem]
    · exact fun h => (mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => V) 0 omega).1 h |>.1.false
    · exact fun h => (mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => U) 0 omega).1 h |>.1.false

/-- The refined source path variation is dominated by the left source
prefix path variation. -/
theorem pairScheduleSourcePrefix_pathVariation_le_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((pairScheduleSourcePrefix left right n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        ((left.sourcePrefix n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  have hIndistinguishable :=
    pairScheduleSourcePrefix_finiteVariationPart_left left right n
  filter_upwards [hIndistinguishable] with omega hOmega
  let sigma := RightContinuousStoppedMartingale.boundedTime (left.horizon n)
    (pairScheduleLocalizer left right n) omega
  have hPath :
      (fun t => (pairScheduleSourcePrefix left right n
        ).finiteVariationPart t omega) =
      FiniteVariationStoppedPath.stopAt
        (fun t => (left.sourcePrefix n).finiteVariationPart t omega) sigma := by
    exact funext hOmega |>.trans
      (RightContinuousStoppedMartingale.stoppedProcess_path_eq_stopAt_boundedTime
        (left.sourcePrefix n).finiteVariationPart
        (pairScheduleLocalizer left right n) (left.horizon n)
        (fun sample =>
          (pairScheduleLocalizer_le_left left right n sample).trans
            (left.localizer_le_horizon n sample)) omega)
  let hStopped := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    ((left.sourcePrefix n).finiteVariationPart_isBoundedVariation omega) sigma
  have hMeasure := FiniteVariationPath.signedMeasure_eq_of_eq
    ((pairScheduleSourcePrefix left right n
      ).finiteVariationPart_isBoundedVariation omega) hStopped hPath
  rw [hMeasure]
  exact stoppedPath_totalVariation_le
    (fun t => (left.sourcePrefix n).finiteVariationPart t omega)
    ((left.sourcePrefix n).finiteVariationPart_isBoundedVariation omega)
    (fun t => (left.sourcePrefix n).finiteVariationPart_isRightContinuous
      omega t) sigma

/-- The refined source path variation is dominated by the right source
prefix path variation. -/
theorem pairScheduleSourcePrefix_pathVariation_le_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((pairScheduleSourcePrefix left right n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        ((right.sourcePrefix n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  have hIndistinguishable :=
    pairScheduleSourcePrefix_finiteVariationPart_right left right n
  filter_upwards [hIndistinguishable] with omega hOmega
  let sigma := RightContinuousStoppedMartingale.boundedTime (right.horizon n)
    (pairScheduleLocalizer left right n) omega
  have hPath :
      (fun t => (pairScheduleSourcePrefix left right n
        ).finiteVariationPart t omega) =
      FiniteVariationStoppedPath.stopAt
        (fun t => (right.sourcePrefix n).finiteVariationPart t omega) sigma := by
    exact funext hOmega |>.trans
      (RightContinuousStoppedMartingale.stoppedProcess_path_eq_stopAt_boundedTime
        (right.sourcePrefix n).finiteVariationPart
        (pairScheduleLocalizer left right n) (right.horizon n)
        (fun sample =>
          (pairScheduleLocalizer_le_right left right n sample).trans
            (right.localizer_le_horizon n sample)) omega)
  let hStopped := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    ((right.sourcePrefix n).finiteVariationPart_isBoundedVariation omega) sigma
  have hMeasure := FiniteVariationPath.signedMeasure_eq_of_eq
    ((pairScheduleSourcePrefix left right n
      ).finiteVariationPart_isBoundedVariation omega) hStopped hPath
  rw [hMeasure]
  exact stoppedPath_totalVariation_le
    (fun t => (right.sourcePrefix n).finiteVariationPart t omega)
    ((right.sourcePrefix n).finiteVariationPart_isBoundedVariation omega)
    (fun t => (right.sourcePrefix n).finiteVariationPart_isRightContinuous
      omega t) sigma

/-- The common finite-variation bridge attached to the pair-refined source
prefix. -/
noncomputable def pairScheduleFiniteVariationBridge
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    SIntegrableFiniteVariationBridge
      (pairScheduleSourcePrefix left right n) :=
  commonRefinementFiniteVariationBridge
    (left.variationBridge n) (right.variationBridge n)
      (pairScheduleSourcePrefix left right n)

/-- The completed finite-variation process of a coefficient transported to
the pair schedule is the old completed process stopped at the common
localizer.  The target quadratic kernel is arbitrary: only the common raw
coefficient and the two variation bridges enter this statement. -/
theorem pairScheduleCompletedFiniteVariationPart_of_schedule
    (left right schedule : LocalCompletedM2ASchedule G) (n : Nat)
    (hPairLe : forall omega,
      pairScheduleLocalizer left right n omega <= schedule.localizer n omega)
    (hSource : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (schedule.sourcePrefix n).finiteVariationPart
        (pairScheduleLocalizer left right n)))
    (c : FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {Qnew : BoundedMartingaleQuadraticKernel.Data F mu
      (pairScheduleSourcePrefix left right n).martingalePart
        (pairScheduleHorizon left right n)}
    (pc : FiniteHorizonM2ACoefficient
      (pairScheduleFiniteVariationBridge left right n) Qnew)
    (hpc : pc.coefficient = c.coefficient) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart left.usualConditions
        (pairScheduleHorizon left right n) Qnew
        (pairScheduleFiniteVariationBridge left right n) pc)
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) c)
        (pairScheduleLocalizer left right n)) := by
  let tau := pairScheduleLocalizer left right n
  let T := min (schedule.horizon n) (pairScheduleHorizon left right n)
  have hTauT : forall omega, tau omega <= (T : WithTop NNReal) := by
    intro omega
    rw [WithTop.coe_min]
    exact le_min
      ((hPairLe omega).trans (schedule.localizer_le_horizon n omega))
      (pairScheduleLocalizer_le_horizon left right n omega)
  have hCoefficient : forall omega u,
      u <= RightContinuousStoppedMartingale.boundedTime T tau omega ->
        pc.integrand u omega = c.integrand u omega := by
    intro omega u hu
    have huT : u <= T := hu.trans
      (RightContinuousStoppedMartingale.boundedTime_le T tau omega)
    have huSchedule : u <= schedule.horizon n :=
      huT.trans (min_le_left _ _)
    have huPair : u <= pairScheduleHorizon left right n :=
      huT.trans (min_le_right _ _)
    change finiteHorizonCoefficient (pairScheduleHorizon left right n)
        pc.coefficient u omega =
      finiteHorizonCoefficient (schedule.horizon n) c.coefficient u omega
    rw [hpc]
    exact finiteHorizonCoefficient_eq_of_le c.coefficient
      (pairScheduleHorizon left right n) (schedule.horizon n) u omega
      huPair huSchedule
  have hNew := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    left.usualConditions (pairScheduleFiniteVariationBridge left right n)
      Qnew pc
  have hRaw := finiteVariationIntegralProcess_eq_stopped_of_path
    (schedule.variationBridge n)
    (pairScheduleFiniteVariationBridge left right n) tau T hTauT
      hSource c.integrand pc.integrand hCoefficient
  have hOld := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    schedule.usualConditions (schedule.variationBridge n)
      (schedule.quadraticKernel n) c
  exact hNew.trans <| hRaw.trans <| hOld.symm.stoppedProcess tau

end LocalCompletedM2A
end FTAPTheorem42
