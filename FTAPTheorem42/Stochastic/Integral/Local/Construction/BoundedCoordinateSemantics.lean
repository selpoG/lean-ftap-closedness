/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.FiniteVariationCoordinateAgreement
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairRefinement
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Memin.SummableL2Limit

/-!
# Extending local completed semantics to a bounded M² coordinate

An intrinsic graph may use a localization schedule unrelated to a second
finite-horizon source coordinate.  If the graph's centered output becomes a
true square-integrable martingale on that second coordinate, its intrinsic
local representations can be intersected with the coordinate and then sent
to the limit.  Exact energy isometries identify the resulting limit with the
raw predictable integrand.

This is the semantic bridge needed for the common Mémin joint passages.  It
does not assume membership in a fixed-passage carrier or a countable common
schedule.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open BoundedMartingaleQuadraticKernel.Data
open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- Reindex an exhaustive completed schedule along a monotone cofinal map. -/
noncomputable def LocalCompletedM2ASchedule.reindex
    (schedule : LocalCompletedM2ASchedule G)
    (index : Nat -> Nat) (hIndexMono : Monotone index)
    (hIndexTop : Tendsto index atTop atTop) :
    LocalCompletedM2ASchedule G where
  usualConditions := schedule.usualConditions
  localizer := fun n => schedule.localizer (index n)
  isLocalizingSequence := {
    isStoppingTime := fun n =>
      schedule.isLocalizingSequence.isStoppingTime (index n)
    mono := by
      filter_upwards [schedule.isLocalizingSequence.mono] with omega hOmega
      intro n m hnm
      exact hOmega (hIndexMono hnm)
    tendsto_top := by
      filter_upwards [schedule.isLocalizingSequence.tendsto_top]
        with omega hOmega
      exact hOmega.comp hIndexTop }
  horizon := fun n => schedule.horizon (index n)
  horizon_pos := fun n => schedule.horizon_pos (index n)
  localizer_le_horizon := fun n =>
    schedule.localizer_le_horizon (index n)
  sourcePrefix := fun n => schedule.sourcePrefix (index n)
  sourcePrefix_stochasticIntegral := fun n =>
    schedule.sourcePrefix_stochasticIntegral (index n)
  sourcePrefix_martingalePart := fun n =>
    schedule.sourcePrefix_martingalePart (index n)
  sourcePrefix_finiteVariationPart := fun n =>
    schedule.sourcePrefix_finiteVariationPart (index n)
  martingale := fun n => schedule.martingale (index n)
  terminal_memLp := fun n => schedule.terminal_memLp (index n)
  variationBridge := fun n => schedule.variationBridge (index n)
  quadraticKernel := fun n => schedule.quadraticKernel (index n)

/-- Cofinal tail reindexing of a schedule. -/
def tailScheduleIndex (r k : Nat) : Nat :=
  r + k

theorem tailScheduleIndex_monotone (r : Nat) :
    Monotone (tailScheduleIndex r) := by
  intro k l hkl
  exact Nat.add_le_add_left hkl r

theorem tailScheduleIndex_tendsto_atTop (r : Nat) :
    Tendsto (tailScheduleIndex r) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun k hk => hk.trans (Nat.le_add_left k r)⟩

@[simp]
theorem tailScheduleIndex_zero (r : Nat) : tailScheduleIndex r 0 = r :=
  Nat.add_zero r

/-- The cofinal tail of a completed schedule starting at coordinate `r`. -/
noncomputable def LocalCompletedM2ASchedule.tailFrom
    (schedule : LocalCompletedM2ASchedule G) (r : Nat) :
    LocalCompletedM2ASchedule G :=
  schedule.reindex (tailScheduleIndex r)
    (tailScheduleIndex_monotone r)
    (tailScheduleIndex_tendsto_atTop r)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
@[simp]
theorem LocalCompletedM2ASchedule.tailFrom_localizer_zero
    (schedule : LocalCompletedM2ASchedule G) (r : Nat) :
    (schedule.tailFrom r).localizer 0 = schedule.localizer r := by
  simp [LocalCompletedM2ASchedule.tailFrom,
    LocalCompletedM2ASchedule.reindex]

/-- Reindex a graph representation along a cofinal schedule tail. -/
noncomputable def ScheduleGraphRepresentation.tailFrom
    {schedule : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation schedule H) (r : Nat) :
    ScheduleGraphRepresentation (schedule.tailFrom r) H where
  coefficient := fun n => representation.coefficient (tailScheduleIndex r n)
  coefficient_eq := fun n => representation.coefficient_eq
    (tailScheduleIndex r n)
  stoppedGain_eq := fun n => representation.stoppedGain_eq
    (tailScheduleIndex r n)

/-- The finite representative of a schedule localizer at one coordinate. -/
noncomputable def scheduleFiniteLocalizer
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) : Omega -> NNReal :=
  RightContinuousStoppedMartingale.boundedTime
    (schedule.horizon n) (schedule.localizer n)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
@[simp]
theorem coe_scheduleFiniteLocalizer
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    (scheduleFiniteLocalizer schedule n omega : WithTop NNReal) =
      schedule.localizer n omega := by
  rw [scheduleFiniteLocalizer,
    RightContinuousStoppedMartingale.coe_boundedTime,
    min_eq_right (schedule.localizer_le_horizon n omega)]

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem scheduleFiniteLocalizer_isStoppingTime
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) :
    IsStoppingTime F (fun omega =>
      (scheduleFiniteLocalizer schedule n omega : WithTop NNReal)) := by
  simpa only [coe_scheduleFiniteLocalizer] using
    schedule.isLocalizingSequence.isStoppingTime n

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem scheduleFiniteLocalizer_le_horizon
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    scheduleFiniteLocalizer schedule n omega <= schedule.horizon n :=
  RightContinuousStoppedMartingale.boundedTime_le
    (schedule.horizon n) (schedule.localizer n) omega

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- A schedule source prefix is already stopped at its own localizer. -/
theorem sourcePrefix_martingalePart_indistinguishable_stopped
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (schedule.sourcePrefix n).martingalePart
      (MeasureTheory.stoppedProcess
        (schedule.sourcePrefix n).martingalePart (schedule.localizer n)) := by
  let tau := schedule.localizer n
  have hSource := schedule.sourcePrefix_martingalePart n
  have hStopped := hSource.stoppedProcess tau
  rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
    (fun _ => le_rfl)] at hStopped
  exact hSource.trans hStopped.symm

omit [F.IsRightContinuous] in
/-- Consequently, a schedule energy measure is supported on its own
positive stochastic interval. -/
theorem schedule_predictableEnergyMeasure_eq_restrict
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) :
    (schedule.quadraticKernel n).predictableEnergyMeasure =
      (schedule.quadraticKernel n).predictableEnergyMeasure.restrict
        (stochasticIntervalIocZero
          (scheduleFiniteLocalizer schedule n)) := by
  let tau := scheduleFiniteLocalizer schedule n
  have hStopped : ProcessIndistinguishable mu
      (schedule.sourcePrefix n).martingalePart
      (MeasureTheory.stoppedProcess
        (schedule.sourcePrefix n).martingalePart
          (fun omega => (tau omega : WithTop NNReal))) := by
    simpa only [tau, coe_scheduleFiniteLocalizer] using
      sourcePrefix_martingalePart_indistinguishable_stopped schedule n
  exact predictableEnergyMeasure_stoppedProcess_eq_restrict
    (schedule.quadraticKernel n) (schedule.martingale n)
    (schedule.sourcePrefix n).martingalePart_isRightContinuous
    (schedule.terminal_memLp n) tau
    (scheduleFiniteLocalizer_isStoppingTime schedule n)
    (scheduleFiniteLocalizer_le_horizon schedule n)
    (scheduleFiniteLocalizer_le_horizon schedule n)
    (schedule.sourcePrefix n).martingalePart hStopped
    (schedule.martingale n)
    (schedule.sourcePrefix n).martingalePart_isRightContinuous
    (schedule.terminal_memLp n) (schedule.quadraticKernel n)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- Base-measure almost-everywhere properties lift through the integrated
quadratic kernel.  Completeness at time zero makes the exceptional cylinder
predictable. -/
theorem predictableEnergyMeasure_ae_snd
    (hUsual : Filtration.UsualConditions mu F)
    {M : Process Omega} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    {P : Omega -> Prop} (hP : ∀ᵐ omega ∂mu, P omega) :
    ∀ᵐ point ∂Q.predictableEnergyMeasure, P point.2 := by
  have hBad : mu {omega | ¬ P omega} = 0 := ae_iff.mp hP
  have hBadMeas : MeasurableSet[F 0] {omega | ¬ P omega} :=
    hUsual.measurableSet_of_null bot_le hBad
  have hCylinder : MeasurableSet[F.predictable]
      (Set.univ ×ˢ {omega | ¬ P omega}) :=
    ProcessNullSetRegularization.measurableSet_predictable_univ_prod hBadMeas
  rw [ae_iff]
  change Q.predictableEnergyMeasure {point | ¬ P point.2} = 0
  rw [show {point : NNReal × Omega | ¬ P point.2} =
      Set.univ ×ˢ {omega | ¬ P omega} by
    ext point
    simp]
  rw [Q.predictableEnergyMeasure_apply hCylinder]
  calc
    (∫⁻ omega,
        IncreasingProcessStieltjesKernel.pathMeasure Q.variation
          Q.variation_monotone Q.variation_rightContinuous omega
            ((fun t => (t, omega)) ⁻¹' (Set.univ ×ˢ {omega | ¬ P omega}))
        ∂mu) = ∫⁻ _omega, 0 ∂mu := by
          apply lintegral_congr_ae
          filter_upwards [hP] with omega hOmega
          simp [hOmega]
    _ = 0 := lintegral_zero

omit [F.IsRightContinuous] in
/-- Almost every point of a schedule energy measure lies before the
schedule's own finite localizer. -/
theorem schedule_ae_mem_stochasticInterval
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) :
    ∀ᵐ point ∂(schedule.quadraticKernel n).predictableEnergyMeasure,
      point ∈ stochasticIntervalIocZero
        (scheduleFiniteLocalizer schedule n) := by
  rw [schedule_predictableEnergyMeasure_eq_restrict schedule n]
  exact ae_restrict_mem
    (IsStoppingTime.measurableSet_stochasticIntervalIocZero
      (scheduleFiniteLocalizer_isStoppingTime schedule n))

omit [F.IsRightContinuous] in
/-- The pair-refined energy measure is the left schedule's energy measure
restricted to the common stochastic interval. -/
theorem pairSchedule_predictableEnergyMeasure_eq_restrict_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    (pairScheduleQuadraticKernel left right n).predictableEnergyMeasure =
      (left.quadraticKernel n).predictableEnergyMeasure.restrict
        (stochasticIntervalIocZero
          (pairScheduleFiniteLocalizer left right n)) := by
  let tau := pairScheduleFiniteLocalizer left right n
  have hStopped : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess
        (left.sourcePrefix n).martingalePart
          (fun omega => (tau omega : WithTop NNReal))) := by
    simpa only [tau, coe_pairScheduleFiniteLocalizer] using
      pairScheduleSourcePrefix_martingalePart_left left right n
  exact predictableEnergyMeasure_stoppedProcess_eq_restrict
    (left.quadraticKernel n) (left.martingale n)
    (left.sourcePrefix n).martingalePart_isRightContinuous
    (left.terminal_memLp n) tau
    (pairScheduleFiniteLocalizer_isStoppingTime left right n)
    (pairScheduleFiniteLocalizer_le_scheduleHorizon
      left right left n (pairScheduleLocalizer_le_left left right n))
    (pairScheduleFiniteLocalizer_le_pairHorizon left right n)
    (pairScheduleSourcePrefix left right n).martingalePart hStopped
    (pairScheduleSourcePrefix_martingale left right n)
    (pairScheduleSourcePrefix left right n).martingalePart_isRightContinuous
    (pairScheduleSourcePrefix_terminal_memLp left right n)
    (pairScheduleQuadraticKernel left right n)

omit [F.IsRightContinuous] in
@[simp]
theorem pairCommonSchedule_quadraticKernel
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    (pairCommonSchedule left right).quadraticKernel n =
      pairScheduleQuadraticKernel left right n :=
  rfl

omit [F.IsRightContinuous] in
/-- A coefficient which is square-integrable for the pair source is the
indicator restriction of a coefficient in the left energy space, and the
two completed martingale integrals agree. -/
theorem pairScheduleMartingaleIntegral_eq_leftRestricted
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hfPair : MemLp f (2 : ENNReal)
      (pairScheduleQuadraticKernel left right n
        ).predictableEnergyMeasure) :
    exists hRestricted : MemLp
        ((stochasticIntervalIocZero
          (pairScheduleFiniteLocalizer left right n)).indicator f)
        (2 : ENNReal) (left.quadraticKernel n).predictableEnergyMeasure,
      ProcessIndistinguishable mu
        (finiteHorizonMartingaleIntegralProcess left.usualConditions
          (pairScheduleQuadraticKernel left right n)
          (pairScheduleSourcePrefix_martingale left right n)
          (pairScheduleSourcePrefix left right n
            ).martingalePart_isRightContinuous
          (pairScheduleSourcePrefix_terminal_memLp left right n)
          f hfMeas hfPair)
        (finiteHorizonMartingaleIntegralProcess left.usualConditions
          (left.quadraticKernel n) (left.martingale n)
          (left.sourcePrefix n).martingalePart_isRightContinuous
          (left.terminal_memLp n)
          ((stochasticIntervalIocZero
            (pairScheduleFiniteLocalizer left right n)).indicator f)
          (hfMeas.indicator
            (IsStoppingTime.measurableSet_stochasticIntervalIocZero
              (pairScheduleFiniteLocalizer_isStoppingTime left right n)))
          hRestricted) := by
  let tau := pairScheduleFiniteLocalizer left right n
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero
      (pairScheduleFiniteLocalizer_isStoppingTime left right n)
  let g := B.indicator f
  let hgMeas : StronglyMeasurable[F.predictable] g := hfMeas.indicator hB
  have hMeasure :=
    pairSchedule_predictableEnergyMeasure_eq_restrict_left left right n
  let hg : MemLp g (2 : ENNReal)
      (left.quadraticKernel n).predictableEnergyMeasure := by
    rw [memLp_indicator_iff_restrict hB]
    rw [← hMeasure]
    exact hfPair
  refine ⟨hg, ?_⟩
  have hSupport : ∀ᵐ point ∂(pairScheduleQuadraticKernel left right n
      ).predictableEnergyMeasure, point ∈ B := by
    rw [hMeasure]
    exact ae_restrict_mem hB
  have hGF : g =ᵐ[(pairScheduleQuadraticKernel left right n
      ).predictableEnergyMeasure] f := by
    filter_upwards [hSupport] with point hPoint
    simp only [g, Set.indicator_of_mem hPoint]
  let hgPair : MemLp g (2 : ENNReal)
      (pairScheduleQuadraticKernel left right n
        ).predictableEnergyMeasure :=
    (memLp_congr_ae hGF).mpr hfPair
  have hCongr : ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess left.usualConditions
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix left right n
          ).martingalePart_isRightContinuous
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        f hfMeas hfPair)
      (finiteHorizonMartingaleIntegralProcess left.usualConditions
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix left right n
          ).martingalePart_isRightContinuous
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        g hgMeas hgPair) :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      left.usualConditions (pairScheduleQuadraticKernel left right n)
      (pairScheduleSourcePrefix_martingale left right n)
      (pairScheduleSourcePrefix left right n
        ).martingalePart_isRightContinuous
      (pairScheduleSourcePrefix_terminal_memLp left right n)
      f hfMeas hfPair g hgMeas hgPair hGF.symm
  have hStopped : ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess
        (left.sourcePrefix n).martingalePart
          (fun omega => (tau omega : WithTop NNReal))) := by
    simpa only [tau, coe_pairScheduleFiniteLocalizer] using
      pairScheduleSourcePrefix_martingalePart_left left right n
  have hTransport := finiteHorizonMartingaleIntegralProcess_stoppedProcess
    left.usualConditions (left.quadraticKernel n) (left.martingale n)
    (left.sourcePrefix n).martingalePart_isRightContinuous
    (left.terminal_memLp n) tau
    (pairScheduleFiniteLocalizer_isStoppingTime left right n)
    (pairScheduleFiniteLocalizer_le_scheduleHorizon
      left right left n (pairScheduleLocalizer_le_left left right n))
    (pairScheduleFiniteLocalizer_le_pairHorizon left right n)
    (pairScheduleSourcePrefix left right n).martingalePart hStopped
    (pairScheduleSourcePrefix_martingale left right n)
    (pairScheduleSourcePrefix left right n).martingalePart_isRightContinuous
    (pairScheduleSourcePrefix_terminal_memLp left right n)
    (pairScheduleQuadraticKernel left right n) g hgMeas hg
  have hIdempotent : B.indicator g = g := by
    funext point
    by_cases hPoint : point ∈ B <;> simp [g, hPoint]
  have hIdempotentProcess : ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess left.usualConditions
        (left.quadraticKernel n) (left.martingale n)
        (left.sourcePrefix n).martingalePart_isRightContinuous
        (left.terminal_memLp n) (B.indicator g)
        (hgMeas.indicator hB) (hg.indicator hB))
      (finiteHorizonMartingaleIntegralProcess left.usualConditions
        (left.quadraticKernel n) (left.martingale n)
        (left.sourcePrefix n).martingalePart_isRightContinuous
        (left.terminal_memLp n) g hgMeas hg) :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      left.usualConditions (left.quadraticKernel n) (left.martingale n)
      (left.sourcePrefix n).martingalePart_isRightContinuous
      (left.terminal_memLp n) (B.indicator g) (hgMeas.indicator hB)
      (hg.indicator hB) g hgMeas hg
      (Filter.Eventually.of_forall fun point => congrFun hIdempotent point)
  simpa only [tau, B, g, hgMeas, hg, hB, hgPair] using
    hCongr.trans (hTransport.trans hIdempotentProcess)

/-- A graph representation on a prescribed schedule identifies its stopped
centered martingale coordinate with the completed martingale integral of the
raw predictable integrand.  This is the fixed-witness form of
`actualCoordinate_martingaleSemantics`. -/
theorem ScheduleGraphRepresentation.coordinate_martingaleSemantics
    {schedule : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation schedule H)
    (n : Nat) :
    exists hEnergy : MemLp (Function.uncurry H.integrand) (2 : ENNReal)
        (schedule.quadraticKernel n).predictableEnergyMeasure,
      ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.centeredMartingalePart
          (schedule.localizer n))
        (finiteHorizonMartingaleIntegralProcess
          schedule.usualConditions (schedule.quadraticKernel n)
          (schedule.martingale n)
          (schedule.sourcePrefix n).martingalePart_isRightContinuous
          (schedule.terminal_memLp n) (Function.uncurry H.integrand)
          H.integrand_isPredictable hEnergy) := by
  let tau := schedule.localizer n
  let T := schedule.horizon n
  let P := schedule.sourcePrefix n
  let c := representation.coefficient n
  have hRaw : Function.uncurry c.integrand
      =ᵐ[(schedule.quadraticKernel n).predictableEnergyMeasure]
        Function.uncurry H.integrand :=
    (finiteHorizonCoefficient_ae_eq
      (schedule.quadraticKernel n) c.coefficient).trans
        (Filter.Eventually.of_forall fun point =>
          congrFun (representation.coefficient_eq n) point)
  let hEnergy : MemLp (Function.uncurry H.integrand) (2 : ENNReal)
      (schedule.quadraticKernel n).predictableEnergyMeasure :=
    (memLp_congr_ae hRaw).mp c.integrand_memLp_energy
  refine ⟨hEnergy, ?_⟩
  let hTau : IsStoppingTime F tau :=
    schedule.isLocalizingSequence.isStoppingTime n
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau
  have hSigma : (fun omega => (sigma omega : WithTop NNReal)) = tau := by
    funext omega
    exact (RightContinuousStoppedMartingale.coe_boundedTime T tau omega).trans
      (min_eq_right (schedule.localizer_le_horizon n omega))
  have hStopping : IsStoppingTime F (fun omega => (sigma omega : WithTop NNReal)) := by
    rw [hSigma]
    exact hTau
  let K := H.toLocally.finiteClosedStopOfRightContinuous sigma hStopping
  let V := finiteHorizonCompletedM2AStrategy schedule.usualConditions T
    (schedule.quadraticKernel n) (schedule.variationBridge n)
      (schedule.martingale n) (schedule.terminal_memLp n) c
  have hGain : ProcessIndistinguishable mu K.stochasticIntegral
      V.stochasticIntegral :=
    by
      change ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.stochasticIntegral
          (fun omega => (sigma omega : WithTop NNReal))) V.stochasticIntegral
      rw [hSigma]
      exact representation.stoppedGain_eq n
  have hCentered : ProcessIndistinguishable mu K.centeredMartingalePart
      V.centeredMartingalePart :=
    K.centeredMartingalePart_indistinguishable_of_gain
      schedule.usualConditions V hGain
  have hKStopped : ProcessIndistinguishable mu K.centeredMartingalePart
      (MeasureTheory.stoppedProcess H.centeredMartingalePart tau) := by
    have hMStop : ProcessIndistinguishable mu K.martingalePart
        (MeasureTheory.stoppedProcess H.martingalePart tau) := by
      change ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.martingalePart
          (fun omega => (sigma omega : WithTop NNReal))) _
      rw [hSigma]
      exact ProcessIndistinguishable.refl mu _
    filter_upwards [hMStop] with omega hMStopOmega
    intro t
    change K.martingalePart t omega - K.martingalePart 0 omega = _
    rw [hMStopOmega t, hMStopOmega 0]
    simp [MeasureTheory.stoppedProcess,
      SIntegrableStrategy.centeredMartingalePart]
  have hCanonical : ProcessIndistinguishable mu V.centeredMartingalePart
      (finiteHorizonCompletedMartingalePart schedule.usualConditions T
        (schedule.quadraticKernel n) (schedule.martingale n)
          (schedule.terminal_memLp n) c) :=
    finiteHorizonCompletedM2AStrategy_centeredMartingalePart
      schedule.usualConditions T (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) c
  have hCompleted : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart schedule.usualConditions T
        (schedule.quadraticKernel n) (schedule.martingale n)
          (schedule.terminal_memLp n) c)
      (finiteHorizonMartingaleIntegralProcess schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.martingale n)
          P.martingalePart_isRightContinuous (schedule.terminal_memLp n)
            (Function.uncurry H.integrand) H.integrand_isPredictable
              hEnergy) :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.martingale n) P.martingalePart_isRightContinuous
          (schedule.terminal_memLp n) (Function.uncurry c.integrand)
            c.integrand_isStronglyPredictable c.integrand_memLp_energy
          (Function.uncurry H.integrand) H.integrand_isPredictable
            hEnergy hRaw
  exact hKStopped.symm.trans (hCentered.trans (hCanonical.trans hCompleted))

omit [F.IsRightContinuous] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
/-- The intrinsic centered coordinate has right-continuous paths. -/
theorem actualLocalL2CoordinateProcess_rightContinuous
    {R : SIntegrableRealizationModel D}
    (tau : Omega -> WithTop NNReal) (T : NNReal)
    (H : ActualSIntegrableStrategy R) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt
      (actualLocalL2CoordinateProcess tau T H · omega) (Set.Ici t) t := by
  have hCenteredRight : forall omega s,
      ContinuousWithinAt (H.val.centeredMartingalePart · omega)
        (Set.Ici s) s := by
    intro sample s
    exact (H.val.martingalePart_isRightContinuous sample s).sub
      continuousWithinAt_const
  have hFirstRight : forall sample s, ContinuousWithinAt
      (MeasureTheory.stoppedProcess H.val.centeredMartingalePart tau · sample)
        (Set.Ici s) s :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      H.val.centeredMartingalePart hCenteredRight
  exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
    (MeasureTheory.stoppedProcess H.val.centeredMartingalePart tau)
      hFirstRight omega t

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
/-- Intersecting a target coordinate with an intrinsic witness coordinate
is the same as stopping the target coordinate once more. -/
theorem actualLocalL2CoordinateProcess_pair_eq_stopped_target
    {R : SIntegrableRealizationModel D}
    (target own : LocalCompletedM2ASchedule G) (n : Nat)
    (H : ActualSIntegrableStrategy R) :
    actualLocalL2CoordinateProcess
        (pairScheduleLocalizer target own n) (target.horizon n) H =
      MeasureTheory.stoppedProcess
        (actualLocalL2CoordinateProcess
          (target.localizer n) (target.horizon n) H)
        (own.localizer n) := by
  have hPairLeT : forall omega,
      pairScheduleLocalizer target own n omega <=
        (target.horizon n : WithTop NNReal) := by
    intro omega
    exact (pairScheduleLocalizer_le_left
      target own n omega).trans (target.localizer_le_horizon n omega)
  have hTargetLeT : forall omega,
      target.localizer n omega <= (target.horizon n : WithTop NNReal) :=
    target.localizer_le_horizon n
  rw [actualLocalL2CoordinateProcess,
    MeasureTheory.stoppedProcess_stoppedProcess_of_le_left hPairLeT,
    actualLocalL2CoordinateProcess,
    MeasureTheory.stoppedProcess_stoppedProcess_of_le_left hTargetLeT,
    MeasureTheory.stoppedProcess_stoppedProcess']
  congr 1
  funext omega
  simp only [pairScheduleLocalizer]
  exact min_comm _ _

end LocalCompletedM2A

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Fixed-horizon samples along an exhaustive localizer converge pointwise
almost everywhere to the terminal value. -/
theorem stoppedProcess_localizer_tendsto_ae
    {X : Process Omega} {T : NNReal}
    {localizer : Nat -> Omega -> WithTop NNReal}
    (hLocalizer : ProbabilityTheory.IsLocalizingSequence F localizer mu) :
    ∀ᵐ omega ∂mu, Tendsto (fun n =>
      MeasureTheory.stoppedProcess X (localizer n) T omega)
        atTop (nhds (X T omega)) := by
  filter_upwards [hLocalizer.tendsto_top] with omega hTop
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  have hEventually : ∀ᶠ n in atTop,
      (T : WithTop NNReal) <= localizer n omega :=
    (hTop T).mono fun _ hn => hn.le
  apply tendsto_const_nhds.congr'
  filter_upwards [hEventually] with n hn
  exact (MeasureTheory.stoppedProcess_eq_of_le hn).symm

omit [SigmaFiniteFiltration mu F] in
/-- The continuous-time martingale envelope dominates every fixed-horizon
stopped sample error. -/
theorem Martingale.stoppedProcess_localizer_error_le_envelope
    {X : Process Omega} {T : NNReal}
    (hX : Martingale X F mu)
    (hXRight : forall omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hXT : MemLp (X T) (2 : ENNReal) mu)
    (localizer : Nat -> Omega -> WithTop NNReal) (n : Nat) :
    ∀ᵐ omega ∂mu,
      ‖MeasureTheory.stoppedProcess X (localizer n) T omega - X T omega‖ <=
        ‖(2 : Real) •
          FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T omega‖ := by
  filter_upwards [
    FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hX T hXT hXRight] with omega hEnvelopeOmega
  have hTime :
      (min (T : WithTop NNReal) (localizer n omega)).untopA <= T :=
    WithTop.untopA_le (min_le_left _ _)
  calc
    ‖MeasureTheory.stoppedProcess X (localizer n) T omega - X T omega‖ <=
        ‖MeasureTheory.stoppedProcess X (localizer n) T omega‖ +
          ‖X T omega‖ := norm_sub_le _ _
    _ <= FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T omega +
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T omega :=
      add_le_add (hEnvelopeOmega _ hTime) (hEnvelopeOmega T le_rfl)
    _ = ‖(2 : Real) •
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T omega‖ := by
      simp only [norm_smul, Real.norm_ofNat]
      have hNonnegative : 0 <=
          FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T omega :=
        Real.sqrt_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hNonnegative]
      ring

omit [SigmaFiniteFiltration mu F] in
/-- Stopping a finite-horizon `M²` martingale along an exhaustive
localizer converges back to its deterministic terminal value in `L²`. -/
theorem Martingale.tendsto_eLpNorm_two_stoppedProcess_localizer
    {X : Process Omega} {T : NNReal}
    (hX : Martingale X F mu)
    (hXRight : forall omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t)
    (hXT : MemLp (X T) (2 : ENNReal) mu)
    {localizer : Nat -> Omega -> WithTop NNReal}
    (hLocalizer : ProbabilityTheory.IsLocalizingSequence
      F localizer mu) :
    Tendsto (fun n => eLpNorm (fun omega =>
      MeasureTheory.stoppedProcess X (localizer n) T omega - X T omega)
        (2 : ENNReal) mu) atTop (nhds 0) := by
  have hSampleMeas : forall n, AEStronglyMeasurable
      (MeasureTheory.stoppedProcess X (localizer n) T) mu := by
    intro n
    have hStoppedAdapted : StronglyAdapted F
        (MeasureTheory.stoppedProcess X (localizer n)) :=
      RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        hX.stronglyAdapted (hLocalizer.isStoppingTime n) hXRight
    exact ((hStoppedAdapted T).mono (F.le T)).aestronglyMeasurable
  have hTerminalMeas : AEStronglyMeasurable (X T) mu :=
    ((hX.stronglyMeasurable T).mono (F.le T)).aestronglyMeasurable
  have hBoundMem : MemLp ((2 : Real) •
      FactorialChronologicalGrid.martingaleAbsoluteEnvelope X T)
      (2 : ENNReal) mu :=
    (FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hX T hXT).const_smul (2 : Real)
  exact tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    hSampleMeas hTerminalMeas hBoundMem
      (fun n => Martingale.stoppedProcess_localizer_error_le_envelope
        hX hXRight hXT localizer n)
      (stoppedProcess_localizer_tendsto_ae hLocalizer)

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open BoundedMartingaleQuadraticKernel.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- An intrinsic graph whose centered output is `M²` on a bounded source
coordinate has the raw predictable integrand in that coordinate's energy
space, and its centered output is exactly the completed martingale
integral.  The proof intersects the coordinate with the graph's own
exhaustive schedule and removes that second localization in `L²`. -/
theorem actual_boundedCoordinate_martingaleSemantics
    (target : LocalCompletedM2ASchedule G) (r : Nat)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hMartingale : Martingale
      (actualLocalL2CoordinateProcess
        (target.localizer r) (target.horizon r) H) F mu)
    (hTerminal : MemLp
      (actualLocalL2CoordinateProcess
        (target.localizer r) (target.horizon r) H (target.horizon r))
      (2 : ENNReal) mu) :
    exists hEnergy : MemLp (Function.uncurry H.val.integrand) (2 : ENNReal)
        (target.quadraticKernel r).predictableEnergyMeasure,
      ProcessIndistinguishable mu
        (actualLocalL2CoordinateProcess
          (target.localizer r) (target.horizon r) H)
        (finiteHorizonMartingaleIntegralProcess target.usualConditions
          (target.quadraticKernel r) (target.martingale r)
          (target.sourcePrefix r).martingalePart_isRightContinuous
          (target.terminal_memLp r) (Function.uncurry H.val.integrand)
          H.val.integrand_isPredictable hEnergy) := by
  classical
  let _ : MeasurableSpace (NNReal × Omega) := F.predictable
  let witness := actualGraphWitness H
  let f : NNReal × Omega -> Real := Function.uncurry H.val.integrand
  let X : Process Omega := actualLocalL2CoordinateProcess
    (target.localizer r) (target.horizon r) H
  let left : LocalCompletedM2ASchedule G := target.tailFrom r
  let right (n : Nat) : LocalCompletedM2ASchedule G :=
    witness.schedule.tailFrom n
  let rightRepresentation (n : Nat) : ScheduleGraphRepresentation
      (right n) H.val := witness.toScheduleGraphRepresentation.tailFrom n
  let pairRepresentation (n : Nat) : ScheduleGraphRepresentation
      (pairCommonSchedule left (right n)) H.val :=
    (rightRepresentation n).pairRefineRight (left := left)
  have hPairSemantics (n : Nat) :=
    (pairRepresentation n).coordinate_martingaleSemantics  0
  let hPairEnergy (n : Nat) := Classical.choose (hPairSemantics n)
  have hPairProcess (n : Nat) := Classical.choose_spec (hPairSemantics n)
  have hPairEnergyRaw (n : Nat) : MemLp f (2 : ENNReal)
      (pairScheduleQuadraticKernel left (right n) 0
        ).predictableEnergyMeasure := by
    have h := hPairEnergy n
    rw [pairCommonSchedule_quadraticKernel] at h
    change MemLp f (2 : ENNReal)
      (pairScheduleQuadraticKernel left (right n) 0
        ).predictableEnergyMeasure at h
    exact h
  let hRestricted (n : Nat) := Classical.choose
    (pairScheduleMartingaleIntegral_eq_leftRestricted
      left (right n) 0 f H.val.integrand_isPredictable
        (hPairEnergyRaw n))
  have hPairToLeft (n : Nat) := Classical.choose_spec
    (pairScheduleMartingaleIntegral_eq_leftRestricted
      left (right n) 0 f H.val.integrand_isPredictable
        (hPairEnergyRaw n))
  let B (n : Nat) := stochasticIntervalIocZero
    (pairScheduleFiniteLocalizer left (right n) 0)
  let truncated (n : Nat) : NNReal × Omega -> Real := (B n).indicator f
  have hTruncatedMem (n : Nat) : MemLp (truncated n) (2 : ENNReal)
      (target.quadraticKernel r).predictableEnergyMeasure := by
    simpa [truncated, B, left, f,
      LocalCompletedM2ASchedule.tailFrom,
      LocalCompletedM2ASchedule.reindex, tailScheduleIndex] using
        hRestricted n
  have hPairProcessRaw (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.val.centeredMartingalePart
        (pairScheduleLocalizer left (right n) 0))
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (pairScheduleQuadraticKernel left (right n) 0)
        (pairScheduleSourcePrefix_martingale left (right n) 0)
        (pairScheduleSourcePrefix left (right n) 0
          ).martingalePart_isRightContinuous
        (pairScheduleSourcePrefix_terminal_memLp left (right n) 0)
        f H.val.integrand_isPredictable (hPairEnergyRaw n)) := by
    exact hPairProcess n
  have hSampleProcess (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess X (witness.schedule.localizer n))
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (target.quadraticKernel r) (target.martingale r)
        (target.sourcePrefix r).martingalePart_isRightContinuous
        (target.terminal_memLp r) (truncated n)
        (H.val.integrand_isPredictable.indicator
          (pairScheduleFiniteLocalizer_isStoppingTime
            left (right n) 0
            |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
        (hTruncatedMem n)) := by
    have hCoordinate := actualLocalL2CoordinateProcess_pair_eq_stopped_target
      left (right n) 0 H
    have hPairLeT : forall omega,
        pairScheduleLocalizer left (right n) 0 omega <=
          (target.horizon r : WithTop NNReal) := by
      intro omega
      exact (pairScheduleLocalizer_le_left
        left (right n) 0 omega).trans (by
          simpa only [left,
            LocalCompletedM2ASchedule.tailFrom_localizer_zero] using
              target.localizer_le_horizon r omega)
    have hPairRaw : MeasureTheory.stoppedProcess
        H.val.centeredMartingalePart
          (pairScheduleLocalizer left (right n) 0) =
        MeasureTheory.stoppedProcess X (witness.schedule.localizer n) := by
      have hSingle : actualLocalL2CoordinateProcess
          (pairScheduleLocalizer left (right n) 0)
            (target.horizon r) H =
          MeasureTheory.stoppedProcess H.val.centeredMartingalePart
            (pairScheduleLocalizer left (right n) 0) :=
        MeasureTheory.stoppedProcess_stoppedProcess_of_le_left hPairLeT
      simpa [X, left, right,
        LocalCompletedM2ASchedule.tailFrom,
        LocalCompletedM2ASchedule.reindex, tailScheduleIndex] using
          hSingle.symm.trans hCoordinate
    rw [← hPairRaw]
    have hLeft : ProcessIndistinguishable mu
        (finiteHorizonMartingaleIntegralProcess target.usualConditions
          (pairScheduleQuadraticKernel left (right n) 0)
          (pairScheduleSourcePrefix_martingale left (right n) 0)
          (pairScheduleSourcePrefix left (right n) 0
            ).martingalePart_isRightContinuous
          (pairScheduleSourcePrefix_terminal_memLp left (right n) 0)
          f H.val.integrand_isPredictable (hPairEnergyRaw n))
        (finiteHorizonMartingaleIntegralProcess target.usualConditions
          (target.quadraticKernel r) (target.martingale r)
          (target.sourcePrefix r).martingalePart_isRightContinuous
          (target.terminal_memLp r) (truncated n)
          (H.val.integrand_isPredictable.indicator
            (pairScheduleFiniteLocalizer_isStoppingTime
              left (right n) 0
              |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
          (hTruncatedMem n)) := by
      convert hPairToLeft n using 1
      all_goals
        simp [truncated, B, left, right, f,
          LocalCompletedM2ASchedule.tailFrom,
          LocalCompletedM2ASchedule.reindex, tailScheduleIndex]
    exact (hPairProcessRaw n).trans hLeft
  have hTruncatedTendsto : ∀ᵐ point ∂
      (target.quadraticKernel r).predictableEnergyMeasure,
      Tendsto (fun n => truncated n point) atTop (nhds (f point)) := by
    have hTargetSupport := schedule_ae_mem_stochasticInterval target r
    have hOwnTop := predictableEnergyMeasure_ae_snd target.usualConditions
      (target.quadraticKernel r) witness.schedule.isLocalizingSequence.tendsto_top
    filter_upwards [hTargetSupport, hOwnTop] with point hTarget hTop
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    rcases (mem_stochasticIntervalIocZero_iff
      (scheduleFiniteLocalizer target r) point.1 point.2).mp hTarget with
      ⟨hTimePos, hTimeTargetFinite⟩
    have hTimeTarget : (point.1 : WithTop NNReal) <=
        target.localizer r point.2 := by
      rw [← coe_scheduleFiniteLocalizer target r]
      exact WithTop.coe_le_coe.mpr hTimeTargetFinite
    have hEventuallyOwn : ∀ᶠ n in atTop,
        (point.1 : WithTop NNReal) <= witness.schedule.localizer n point.2 :=
      (hTop point.1).mono fun _ hlt => hlt.le
    apply tendsto_const_nhds.congr'
    filter_upwards [hEventuallyOwn] with n hTimeOwn
    have hTimePairTop : (point.1 : WithTop NNReal) <=
        pairScheduleLocalizer left (right n) 0 point.2 := by
      rw [pairScheduleLocalizer]
      apply le_min
      · simpa only [left,
          LocalCompletedM2ASchedule.tailFrom_localizer_zero] using
            hTimeTarget
      · simpa only [right,
          LocalCompletedM2ASchedule.tailFrom_localizer_zero] using hTimeOwn
    have hTimePair : point.1 <=
        pairScheduleFiniteLocalizer left (right n) 0 point.2 := by
      apply WithTop.coe_le_coe.mp
      rw [coe_pairScheduleFiniteLocalizer]
      exact hTimePairTop
    have hPointB : point ∈ B n :=
      (mem_stochasticIntervalIocZero_iff
        (pairScheduleFiniteLocalizer left (right n) 0)
          point.1 point.2).2 ⟨hTimePos, hTimePair⟩
    exact (Set.indicator_of_mem hPointB f).symm
  have hXRight : forall omega t,
      ContinuousWithinAt (X · omega) (Set.Ici t) t := by
    simpa only [X] using
      actualLocalL2CoordinateProcess_rightContinuous
        (target.localizer r) (target.horizon r) H
  have hStoppedNorm : Tendsto (fun n => eLpNorm (fun omega =>
      MeasureTheory.stoppedProcess X (witness.schedule.localizer n)
          (target.horizon r) omega - X (target.horizon r) omega)
        (2 : ENNReal) mu) atTop (nhds 0) :=
    Martingale.tendsto_eLpNorm_two_stoppedProcess_localizer
      (by simpa only [X] using hMartingale) hXRight
      (by simpa only [X] using hTerminal)
      witness.schedule.isLocalizingSequence
  let integralProcess (n : Nat) : Process Omega :=
    finiteHorizonMartingaleIntegralProcess target.usualConditions
      (target.quadraticKernel r) (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) (truncated n)
      (H.val.integrand_isPredictable.indicator
        (pairScheduleFiniteLocalizer_isStoppingTime left (right n) 0
          |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
      (hTruncatedMem n)
  let hIntegralTerminal (n : Nat) : MemLp
      (integralProcess n (target.horizon r)) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      target.usualConditions (target.quadraticKernel r)
      (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) (truncated n)
      (H.val.integrand_isPredictable.indicator
        (pairScheduleFiniteLocalizer_isStoppingTime left (right n) 0
          |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
      (hTruncatedMem n)
  let sample (n : Nat) : Omega -> Real := fun omega =>
    MeasureTheory.stoppedProcess X (witness.schedule.localizer n)
      (target.horizon r) omega
  let hSampleMem (n : Nat) : MemLp (sample n) (2 : ENNReal) mu :=
    (hIntegralTerminal n).ae_eq
      ((hSampleProcess n).eventuallyEq_at (target.horizon r)).symm
  have hSampleLpTendsto : Tendsto (fun n =>
      (hSampleMem n).toLp (sample n)) atTop
      (nhds (hTerminal.toLp
        (actualLocalL2CoordinateProcess
          (target.localizer r) (target.horizon r) H (target.horizon r)))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' sample hSampleMem
      (X (target.horizon r)) (by simpa only [X] using hTerminal)).mpr
    change Tendsto (fun n => eLpNorm (fun omega =>
      sample n omega - X (target.horizon r) omega)
        (2 : ENNReal) mu) atTop (nhds 0)
    simpa only [sample] using hStoppedNorm
  have hIntegralTerminalLpTendsto : Tendsto (fun n =>
      (hIntegralTerminal n).toLp
        (integralProcess n (target.horizon r))) atTop
      (nhds (hTerminal.toLp
        (actualLocalL2CoordinateProcess
          (target.localizer r) (target.horizon r) H (target.horizon r)))) := by
    apply hSampleLpTendsto.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply MemLp.toLp_congr
      exact (hSampleProcess n).eventuallyEq_at (target.horizon r)
  have hIntegralTerminalCauchy : CauchySeq (fun n =>
      (hIntegralTerminal n).toLp
        (integralProcess n (target.horizon r))) :=
    hIntegralTerminalLpTendsto.cauchySeq
  have hIntegrandCauchy : CauchySeq (fun n =>
      (hTruncatedMem n).toLp (truncated n)) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hEpsilon
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp
      hIntegralTerminalCauchy) epsilon hEpsilon
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist ((hTruncatedMem m).toLp (truncated m))
          ((hTruncatedMem n).toLp (truncated n)) =
          dist
            (finiteHorizonMartingaleTerminalIntegralLp
              (target.quadraticKernel r) (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) (truncated m)
              (H.val.integrand_isPredictable.indicator
                (pairScheduleFiniteLocalizer_isStoppingTime left (right m) 0
                  |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
              (hTruncatedMem m))
            (finiteHorizonMartingaleTerminalIntegralLp
              (target.quadraticKernel r) (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) (truncated n)
              (H.val.integrand_isPredictable.indicator
                (pairScheduleFiniteLocalizer_isStoppingTime left (right n) 0
                  |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
              (hTruncatedMem n)) :=
        (dist_finiteHorizonMartingaleTerminalIntegralLp_eq
          (target.quadraticKernel r) (target.martingale r)
          (target.sourcePrefix r).martingalePart_isRightContinuous
          (target.terminal_memLp r) (truncated m)
          (H.val.integrand_isPredictable.indicator
            (pairScheduleFiniteLocalizer_isStoppingTime left (right m) 0
              |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
          (hTruncatedMem m) (truncated n)
          (H.val.integrand_isPredictable.indicator
            (pairScheduleFiniteLocalizer_isStoppingTime left (right n) 0
              |> IsStoppingTime.measurableSet_stochasticIntervalIocZero))
          (hTruncatedMem n)).symm
      _ = dist
          ((hIntegralTerminal m).toLp
            (integralProcess m (target.horizon r)))
          ((hIntegralTerminal n).toLp
            (integralProcess n (target.horizon r))) := by
        rw [finiteHorizonMartingaleIntegralProcess_terminal_toLp,
          finiteHorizonMartingaleIntegralProcess_terminal_toLp]
      _ < epsilon := hN m hm n hn
  obtain ⟨hEnergy, hTruncatedNorm⟩ :=
    MeminL2.memLp_two_of_cauchy_of_ae_tendsto truncated hTruncatedMem
      hIntegrandCauchy f hTruncatedTendsto
  refine ⟨hEnergy, ?_⟩
  let fullIntegral : Process Omega :=
    finiteHorizonMartingaleIntegralProcess target.usualConditions
      (target.quadraticKernel r) (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) f H.val.integrand_isPredictable hEnergy
  let hFullTerminal : MemLp (fullIntegral (target.horizon r))
      (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      target.usualConditions (target.quadraticKernel r)
      (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) f H.val.integrand_isPredictable hEnergy
  have hIntegrandLpTendsto : Tendsto (fun n =>
      (hTruncatedMem n).toLp (truncated n)) atTop
      (nhds (hEnergy.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' truncated hTruncatedMem
      f hEnergy).mpr hTruncatedNorm
  have hTerminalToFull : Tendsto (fun n =>
      (hIntegralTerminal n).toLp
        (integralProcess n (target.horizon r))) atTop
      (nhds (hFullTerminal.toLp
        (fullIntegral (target.horizon r)))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hIntegrandLpTendsto
    exact hDistance.congr' (Filter.Eventually.of_forall fun n => by
      calc
        dist ((hTruncatedMem n).toLp (truncated n))
            (hEnergy.toLp f) =
          dist ((hIntegralTerminal n).toLp
            (integralProcess n (target.horizon r)))
            (hFullTerminal.toLp (fullIntegral (target.horizon r))) := by
          symm
          calc
            dist ((hIntegralTerminal n).toLp
                (integralProcess n (target.horizon r)))
                (hFullTerminal.toLp (fullIntegral (target.horizon r))) =
              dist
                (finiteHorizonMartingaleTerminalIntegralLp
                  (target.quadraticKernel r) (target.martingale r)
                  (target.sourcePrefix r).martingalePart_isRightContinuous
                  (target.terminal_memLp r) (truncated n)
                  (H.val.integrand_isPredictable.indicator
                    (pairScheduleFiniteLocalizer_isStoppingTime
                      left (right n) 0 |>
                        IsStoppingTime.measurableSet_stochasticIntervalIocZero))
                  (hTruncatedMem n))
                (finiteHorizonMartingaleTerminalIntegralLp
                  (target.quadraticKernel r) (target.martingale r)
                  (target.sourcePrefix r).martingalePart_isRightContinuous
                  (target.terminal_memLp r) f H.val.integrand_isPredictable
                  hEnergy) := by
                    have hTruncatedTerminal :=
                      finiteHorizonMartingaleIntegralProcess_terminal_toLp
                        target.usualConditions (target.quadraticKernel r)
                        (target.martingale r)
                        (target.sourcePrefix r
                          ).martingalePart_isRightContinuous
                        (target.terminal_memLp r) (truncated n)
                        (H.val.integrand_isPredictable.indicator
                          (pairScheduleFiniteLocalizer_isStoppingTime
                            left (right n) 0 |>
                              IsStoppingTime.measurableSet_stochasticIntervalIocZero))
                        (hTruncatedMem n)
                    have hFullTerminalEq :=
                      finiteHorizonMartingaleIntegralProcess_terminal_toLp
                        target.usualConditions (target.quadraticKernel r)
                        (target.martingale r)
                        (target.sourcePrefix r
                          ).martingalePart_isRightContinuous
                        (target.terminal_memLp r) f
                        H.val.integrand_isPredictable hEnergy
                    simpa only [integralProcess, hIntegralTerminal,
                      fullIntegral, hFullTerminal] using
                        congrArg₂ dist hTruncatedTerminal hFullTerminalEq
            _ = dist ((hTruncatedMem n).toLp (truncated n))
                (hEnergy.toLp f) :=
              dist_finiteHorizonMartingaleTerminalIntegralLp_eq
                (target.quadraticKernel r) (target.martingale r)
                (target.sourcePrefix r).martingalePart_isRightContinuous
                (target.terminal_memLp r) (truncated n)
                (H.val.integrand_isPredictable.indicator
                  (pairScheduleFiniteLocalizer_isStoppingTime
                    left (right n) 0 |>
                      IsStoppingTime.measurableSet_stochasticIntervalIocZero))
                (hTruncatedMem n) f H.val.integrand_isPredictable hEnergy)
  have hTerminalLp : hFullTerminal.toLp
      (fullIntegral (target.horizon r)) =
      hTerminal.toLp
        (actualLocalL2CoordinateProcess
          (target.localizer r) (target.horizon r) H (target.horizon r)) :=
    tendsto_nhds_unique hTerminalToFull hIntegralTerminalLpTendsto
  have hTerminalAE : fullIntegral (target.horizon r) =ᵐ[mu]
      X (target.horizon r) := by
    simpa only [X] using
      (MemLp.toLp_eq_toLp_iff hFullTerminal hTerminal).mp hTerminalLp
  have hFullMartingale : Martingale fullIntegral F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      target.usualConditions (target.quadraticKernel r)
      (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) f H.val.integrand_isPredictable hEnergy
  have hEqAt : forall t, X t =ᵐ[mu] fullIntegral t := by
    intro t
    by_cases ht : t <= target.horizon r
    · exact (hMartingale.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE.symm).trans
          (hFullMartingale.condExp_ae_eq ht))
    · have hTt : target.horizon r <= t := le_of_not_ge ht
      have hXConstant : X t = X (target.horizon r) := by
        funext omega
        simp only [X, actualLocalL2CoordinateProcess,
          stoppedProcess_const_apply]
        rw [min_eq_right hTt, min_self]
      have hFullConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          target.usualConditions (target.quadraticKernel r)
          (target.martingale r)
          (target.sourcePrefix r).martingalePart_isRightContinuous
          (target.terminal_memLp r) f H.val.integrand_isPredictable
          hEnergy t hTt
      have hXConstantAE : X t =ᵐ[mu] X (target.horizon r) :=
        Filter.Eventually.of_forall fun omega => congrFun hXConstant omega
      exact hXConstantAE.trans
        (hTerminalAE.symm.trans hFullConstant.symm)
  have hFullRight : forall omega t,
      ContinuousWithinAt (fullIntegral · omega) (Set.Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      target.usualConditions (target.quadraticKernel r)
      (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) f H.val.integrand_isPredictable hEnergy
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    X fullIntegral NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hXRight)
    (Filter.Eventually.of_forall hFullRight)
    (fun n => hEqAt _)

end LocalCompletedM2A

end FTAPTheorem42
