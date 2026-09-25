/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStoppingCalculus

/-!
# A common source schedule below two local-completed schedules

Two intrinsic graph witnesses may choose different exhaustive schedules.
This module constructs the source part of a left-biased pointwise-minimum
refinement.  At coordinate `n`, the refined stopping time is the minimum of
the two old localizers, while the deterministic horizon is retained from the
left schedule.  Keeping that horizon unchanged lets the left quadratic
kernel be restricted without a separate horizon-change theorem.  The refined
time is nevertheless below both old horizons.  The raw stopping calculus
constructs the corresponding source prefix.  Its three components agree both
with the newly stopped source and with either old source prefix stopped once
more.

The source martingale is a true `M²` martingale.  This is derived from either
old source schedule by optional stopping; it is not stored as a new
assumption.  The finite-variation bridge and quadratic kernel are deliberately
not chosen here.  `PairCommonSourceScheduleSkeleton.toLocalCompletedM2ASchedule`
lists precisely those two remaining producers.
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

/-- Coordinatewise minimum of the two exhaustive stopping schedules. -/
def pairScheduleLocalizer
    (left right : LocalCompletedM2ASchedule G) :
    Nat -> Omega -> WithTop NNReal :=
  fun n omega => min (left.localizer n omega) (right.localizer n omega)

/-- The left schedule's deterministic horizon, retained by the refinement. -/
def pairScheduleHorizon
    (left _right : LocalCompletedM2ASchedule G) : Nat -> NNReal :=
  left.horizon

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleLocalizer_le_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    pairScheduleLocalizer left right n omega <= left.localizer n omega :=
  min_le_left _ _

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleLocalizer_le_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    pairScheduleLocalizer left right n omega <= right.localizer n omega :=
  min_le_right _ _

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleHorizon_le_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    pairScheduleHorizon left right n <= left.horizon n :=
  le_rfl

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleHorizon_pos
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    0 < pairScheduleHorizon left right n :=
  left.horizon_pos n

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleLocalizer_le_horizon
    (left right : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    pairScheduleLocalizer left right n omega <=
      (pairScheduleHorizon left right n : WithTop NNReal) := by
  exact (pairScheduleLocalizer_le_left left right n omega).trans
    (left.localizer_le_horizon n omega)

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleLocalizer_isLocalizingSequence
    (left right : LocalCompletedM2ASchedule G) :
    ProbabilityTheory.IsLocalizingSequence F
      (pairScheduleLocalizer left right) mu := by
  refine {
    isStoppingTime := fun n =>
      (left.isLocalizingSequence.isStoppingTime n).min
        (right.isLocalizingSequence.isStoppingTime n)
    mono := ?_
    tendsto_top := ?_ }
  · filter_upwards [left.isLocalizingSequence.tendsto_top,
      right.isLocalizingSequence.tendsto_top] with omega hLeft hRight
    simpa only [pairScheduleLocalizer, min_self] using hLeft.min hRight
  · filter_upwards [left.isLocalizingSequence.mono,
      right.isLocalizingSequence.mono] with omega hLeft hRight
    intro n m hnm
    exact min_le_min (hLeft hnm) (hRight hnm)

/-- The finite stopping time represented by the pair localizer. -/
noncomputable def pairScheduleFiniteLocalizer
    (left right : LocalCompletedM2ASchedule G) (n : Nat) : Omega -> NNReal :=
  RightContinuousStoppedMartingale.boundedTime
    (pairScheduleHorizon left right n) (pairScheduleLocalizer left right n)

omit [SigmaFiniteFiltration mu F] in
@[simp]
theorem coe_pairScheduleFiniteLocalizer
    (left right : LocalCompletedM2ASchedule G) (n : Nat) (omega : Omega) :
    (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal) =
      pairScheduleLocalizer left right n omega := by
  rw [pairScheduleFiniteLocalizer,
    RightContinuousStoppedMartingale.coe_boundedTime,
    min_eq_right (pairScheduleLocalizer_le_horizon left right n omega)]

omit [SigmaFiniteFiltration mu F] in
theorem pairScheduleFiniteLocalizer_isStoppingTime
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    IsStoppingTime F (fun omega =>
      (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal)) := by
  simpa only [coe_pairScheduleFiniteLocalizer] using
    (pairScheduleLocalizer_isLocalizingSequence left right
      |>.isStoppingTime n)

/-- The raw source prefix is constructed by direct finite stopping. -/
noncomputable def pairScheduleSourcePrefix
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    SIntegrableStrategy D :=
  (G.deterministicallyStopped (pairScheduleHorizon left right n)
    (pairScheduleHorizon_pos left right n)).toLocally.finiteClosedStopOfRightContinuous
      (pairScheduleFiniteLocalizer left right n)
      (pairScheduleFiniteLocalizer_isStoppingTime left right n)

theorem pairScheduleSourcePrefix_stochasticIntegral
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).stochasticIntegral
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (pairScheduleHorizon left right n)
          (pairScheduleHorizon_pos left right n)).stochasticIntegral
        (pairScheduleLocalizer left right n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).stochasticIntegral
      (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal))) _
  rw [show (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal)) =
    pairScheduleLocalizer left right n from funext (coe_pairScheduleFiniteLocalizer left right n)]
  exact ProcessIndistinguishable.refl mu _

theorem pairScheduleSourcePrefix_martingalePart
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (pairScheduleHorizon left right n)
          (pairScheduleHorizon_pos left right n)).martingalePart
        (pairScheduleLocalizer left right n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).martingalePart
      (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal))) _
  rw [show (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal)) =
    pairScheduleLocalizer left right n from funext (coe_pairScheduleFiniteLocalizer left right n)]
  exact ProcessIndistinguishable.refl mu _

theorem pairScheduleSourcePrefix_finiteVariationPart
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (pairScheduleHorizon left right n)
          (pairScheduleHorizon_pos left right n)).finiteVariationPart
        (pairScheduleLocalizer left right n)) := by
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).finiteVariationPart
      (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal))) _
  rw [show (fun omega => (pairScheduleFiniteLocalizer left right n omega : WithTop NNReal)) =
    pairScheduleLocalizer left right n from funext (coe_pairScheduleFiniteLocalizer left right n)]
  exact ProcessIndistinguishable.refl mu _

omit [SigmaFiniteFiltration mu F] in
/-- Re-stopping either old source component at the pair localizer gives the
same stopped raw source component. -/
private theorem stopped_oldSourceComponent_eq
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (schedule : LocalCompletedM2ASchedule G)
    (hPairLe : forall omega,
      pairScheduleLocalizer left right n omega <= schedule.localizer n omega)
    (X : Process Omega) :
    MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess
          (fun t omega => X (min t (schedule.horizon n)) omega)
          (schedule.localizer n))
        (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess X
        (pairScheduleLocalizer left right n) := by
  rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right]
  · exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right fun omega =>
        (hPairLe omega).trans (schedule.localizer_le_horizon n omega)
  · exact hPairLe

theorem pairScheduleSourcePrefix_martingalePart_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess (left.sourcePrefix n).martingalePart
        (pairScheduleLocalizer left right n)) := by
  have hNew := pairScheduleSourcePrefix_martingalePart left right n
  have hOld := (left.sourcePrefix_martingalePart n).stoppedProcess
    (pairScheduleLocalizer left right n)
  have hNewTarget : MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).martingalePart
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.martingalePart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (fun t omega => G.martingalePart
        (min t (pairScheduleHorizon left right n)) omega)
      (pairScheduleLocalizer left right n) = _
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_horizon left right n)
  have hOldTarget : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (left.horizon n)
          (left.horizon_pos n)).martingalePart (left.localizer n))
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.martingalePart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (fun t omega => G.martingalePart (min t (left.horizon n)) omega)
        (left.localizer n)) (pairScheduleLocalizer left right n) = _
    exact stopped_oldSourceComponent_eq left right n left
      (pairScheduleLocalizer_le_left left right n) G.martingalePart
  rw [hNewTarget] at hNew
  rw [hOldTarget] at hOld
  exact hNew.trans hOld.symm

theorem pairScheduleSourcePrefix_martingalePart_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).martingalePart
      (MeasureTheory.stoppedProcess (right.sourcePrefix n).martingalePart
        (pairScheduleLocalizer left right n)) := by
  have hNew := pairScheduleSourcePrefix_martingalePart left right n
  have hOld := (right.sourcePrefix_martingalePart n).stoppedProcess
    (pairScheduleLocalizer left right n)
  have hNewTarget : MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).martingalePart
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.martingalePart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (fun t omega => G.martingalePart
        (min t (pairScheduleHorizon left right n)) omega)
      (pairScheduleLocalizer left right n) = _
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_horizon left right n)
  have hOldTarget : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (right.horizon n)
          (right.horizon_pos n)).martingalePart (right.localizer n))
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.martingalePart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (fun t omega => G.martingalePart (min t (right.horizon n)) omega)
        (right.localizer n)) (pairScheduleLocalizer left right n) = _
    exact stopped_oldSourceComponent_eq left right n right
      (pairScheduleLocalizer_le_right left right n) G.martingalePart
  rw [hNewTarget] at hNew
  rw [hOldTarget] at hOld
  exact hNew.trans hOld.symm

theorem pairScheduleSourcePrefix_finiteVariationPart_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (left.sourcePrefix n).finiteVariationPart
        (pairScheduleLocalizer left right n)) := by
  have hNew := pairScheduleSourcePrefix_finiteVariationPart left right n
  have hOld := (left.sourcePrefix_finiteVariationPart n).stoppedProcess
    (pairScheduleLocalizer left right n)
  have hNewTarget : MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).finiteVariationPart
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.finiteVariationPart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (fun t omega => G.finiteVariationPart
        (min t (pairScheduleHorizon left right n)) omega)
      (pairScheduleLocalizer left right n) = _
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_horizon left right n)
  have hOldTarget : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (left.horizon n)
          (left.horizon_pos n)).finiteVariationPart (left.localizer n))
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.finiteVariationPart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (fun t omega => G.finiteVariationPart (min t (left.horizon n)) omega)
        (left.localizer n)) (pairScheduleLocalizer left right n) = _
    exact stopped_oldSourceComponent_eq left right n left
      (pairScheduleLocalizer_le_left left right n) G.finiteVariationPart
  rw [hNewTarget] at hNew
  rw [hOldTarget] at hOld
  exact hNew.trans hOld.symm

theorem pairScheduleSourcePrefix_finiteVariationPart_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (pairScheduleSourcePrefix left right n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (right.sourcePrefix n).finiteVariationPart
        (pairScheduleLocalizer left right n)) := by
  have hNew := pairScheduleSourcePrefix_finiteVariationPart left right n
  have hOld := (right.sourcePrefix_finiteVariationPart n).stoppedProcess
    (pairScheduleLocalizer left right n)
  have hNewTarget : MeasureTheory.stoppedProcess
      (G.deterministicallyStopped (pairScheduleHorizon left right n)
        (pairScheduleHorizon_pos left right n)).finiteVariationPart
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.finiteVariationPart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (fun t omega => G.finiteVariationPart
        (min t (pairScheduleHorizon left right n)) omega)
      (pairScheduleLocalizer left right n) = _
    exact MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_horizon left right n)
  have hOldTarget : MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (right.horizon n)
          (right.horizon_pos n)).finiteVariationPart (right.localizer n))
      (pairScheduleLocalizer left right n) =
      MeasureTheory.stoppedProcess G.finiteVariationPart
        (pairScheduleLocalizer left right n) := by
    change MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess
        (fun t omega => G.finiteVariationPart (min t (right.horizon n)) omega)
        (right.localizer n)) (pairScheduleLocalizer left right n) = _
    exact stopped_oldSourceComponent_eq left right n right
      (pairScheduleLocalizer_le_right left right n) G.finiteVariationPart
  rw [hNewTarget] at hNew
  rw [hOldTarget] at hOld
  exact hNew.trans hOld.symm

/-- The pair-refined source martingale is true; it is the further stop of
the left schedule's true martingale source prefix. -/
theorem pairScheduleSourcePrefix_martingale
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    Martingale (pairScheduleSourcePrefix left right n).martingalePart F mu := by
  let rho := pairScheduleLocalizer left right n
  let P := pairScheduleSourcePrefix left right n
  have hStopped : Martingale
      (MeasureTheory.stoppedProcess (left.sourcePrefix n).martingalePart rho)
      F mu :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (left.martingale n)
      ((pairScheduleLocalizer_isLocalizingSequence left right).isStoppingTime n)
      (left.sourcePrefix n).martingalePart_isRightContinuous
  apply hStopped.congr P.martingalePart_isStronglyAdapted
  intro t
  exact (pairScheduleSourcePrefix_martingalePart_left left right n
    |>.eventuallyEq_at t).symm

omit [SigmaFiniteFiltration mu F] in
/-- An old source prefix is constant after its own deterministic horizon. -/
private theorem sourcePrefix_martingalePart_constantAfter
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) (t : NNReal)
    (hTt : schedule.horizon n <= t) :
    (schedule.sourcePrefix n).martingalePart t =ᵐ[mu]
      (schedule.sourcePrefix n).martingalePart (schedule.horizon n) := by
  filter_upwards [schedule.sourcePrefix_martingalePart n]
      with omega hComponent
  rw [hComponent t, hComponent (schedule.horizon n)]
  have hTauT := schedule.localizer_le_horizon n omega
  have hTauT' : schedule.localizer n omega <= (t : WithTop NNReal) :=
    hTauT.trans (WithTop.coe_le_coe.mpr hTt)
  rw [MeasureTheory.stoppedProcess_eq_of_ge hTauT',
    MeasureTheory.stoppedProcess_eq_of_ge hTauT]

/-- The terminal value of the pair-refined source martingale is in `L²`.
The proof samples the left old source prefix at the bounded pair localizer
and uses its stored `L²` terminal together with its constancy after the old
horizon. -/
theorem pairScheduleSourcePrefix_terminal_memLp
    (left right : LocalCompletedM2ASchedule G) (n : Nat) :
    MemLp ((pairScheduleSourcePrefix left right n).martingalePart
      (pairScheduleHorizon left right n)) (2 : ENNReal) mu := by
  let rho := pairScheduleLocalizer left right n
  let U := pairScheduleHorizon left right n
  let T := left.horizon n
  let M := (left.sourcePrefix n).martingalePart
  let sigma : Omega -> NNReal := fun omega =>
    RightContinuousStoppedMartingale.boundedTime U rho omega
  have hRho : IsStoppingTime F rho :=
    (pairScheduleLocalizer_isLocalizingSequence left right).isStoppingTime n
  have hSigma : IsStoppingTime F
      (fun omega => (sigma omega : WithTop NNReal)) :=
    RightContinuousStoppedMartingale.boundedTime_isStoppingTime hRho U
  have hSigmaT : forall omega, sigma omega <= T := fun omega =>
    (RightContinuousStoppedMartingale.boundedTime_le U rho omega).trans
      (pairScheduleHorizon_le_left left right n)
  have hConstant : M (T + 1) =ᵐ[mu] M T := by
    exact sourcePrefix_martingalePart_constantAfter left n (T + 1)
      (le_add_right (le_refl T))
  have hLater : MemLp (M (T + 1)) (2 : ENNReal) mu :=
    (memLp_congr_ae hConstant).mpr (left.terminal_memLp n)
  have hConditional : MemLp
      (mu[M (T + 1) | hSigma.measurableSpace]) (2 : ENNReal) mu :=
    hLater.condExp (by norm_num)
  have hOptional : (fun omega => M (sigma omega) omega) =ᵐ[mu]
      mu[M (T + 1) | hSigma.measurableSpace] :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      (left.martingale n) hSigma hSigmaT
        (left.sourcePrefix n).martingalePart_isRightContinuous
  have hSample : MemLp (fun omega => M (sigma omega) omega)
      (2 : ENNReal) mu :=
    (memLp_congr_ae hOptional).mpr hConditional
  have hStopped : MemLp
      (MeasureTheory.stoppedProcess M rho U) (2 : ENNReal) mu := by
    apply (memLp_congr_ae ?_).mpr hSample
    exact Filter.Eventually.of_forall fun omega => by rfl
  exact (memLp_congr_ae
    (pairScheduleSourcePrefix_martingalePart_left left right n
      |>.eventuallyEq_at U)).mpr hStopped

/-- The source-only part of a pairwise common refinement.  No finite-
variation bridge or martingale quadratic kernel is hidden in this object. -/
structure PairCommonSourceScheduleSkeleton
    (left right : LocalCompletedM2ASchedule G) where
  sourcePrefix : Nat -> SIntegrableStrategy D
  sourcePrefix_eq : forall n,
    sourcePrefix n = pairScheduleSourcePrefix left right n
  martingale : forall n, Martingale (sourcePrefix n).martingalePart F mu
  terminal_memLp : forall n,
    MemLp ((sourcePrefix n).martingalePart
      (pairScheduleHorizon left right n)) (2 : ENNReal) mu

/-- The minimum construction supplies the source-only skeleton without any
new semantic assumption. -/
noncomputable def pairCommonSourceScheduleSkeleton
    (left right : LocalCompletedM2ASchedule G) :
    PairCommonSourceScheduleSkeleton left right where
  sourcePrefix := pairScheduleSourcePrefix left right
  sourcePrefix_eq := fun _ => rfl
  martingale := pairScheduleSourcePrefix_martingale left right
  terminal_memLp := pairScheduleSourcePrefix_terminal_memLp left right

/-- Once the independently constructed finite-variation bridges and
quadratic kernels for the refined source prefixes are supplied, the skeleton
is an ordinary local-completed schedule and can be consumed by the existing
common-schedule addition theorem. -/
noncomputable def PairCommonSourceScheduleSkeleton.toLocalCompletedM2ASchedule
    {left right : LocalCompletedM2ASchedule G}
    (skeleton : PairCommonSourceScheduleSkeleton left right)
    (variationBridge : forall n,
      SIntegrableFiniteVariationBridge (skeleton.sourcePrefix n))
    (quadraticKernel : forall n,
      BoundedMartingaleQuadraticKernel.Data F mu
        (skeleton.sourcePrefix n).martingalePart
          (pairScheduleHorizon left right n)) :
    LocalCompletedM2ASchedule G where
  usualConditions := left.usualConditions
  localizer := pairScheduleLocalizer left right
  isLocalizingSequence := pairScheduleLocalizer_isLocalizingSequence left right
  horizon := pairScheduleHorizon left right
  horizon_pos := pairScheduleHorizon_pos left right
  localizer_le_horizon := pairScheduleLocalizer_le_horizon left right
  sourcePrefix := skeleton.sourcePrefix
  sourcePrefix_stochasticIntegral := fun n => by
    rw [skeleton.sourcePrefix_eq n]
    exact pairScheduleSourcePrefix_stochasticIntegral left right n
  sourcePrefix_martingalePart := fun n => by
    rw [skeleton.sourcePrefix_eq n]
    exact pairScheduleSourcePrefix_martingalePart left right n
  sourcePrefix_finiteVariationPart := fun n => by
    rw [skeleton.sourcePrefix_eq n]
    exact pairScheduleSourcePrefix_finiteVariationPart left right n
  martingale := skeleton.martingale
  terminal_memLp := skeleton.terminal_memLp
  variationBridge := variationBridge
  quadraticKernel := quadraticKernel

end LocalCompletedM2A

end FTAPTheorem42
