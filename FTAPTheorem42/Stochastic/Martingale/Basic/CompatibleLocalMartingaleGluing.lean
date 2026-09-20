/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Martingale.Basic
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Martingale.Basic.ZeroInitialLocalMartingaleStopping

/-!
# Martingale restriction by an initial event

An event measurable at the bottom of a filtration can be used as a bounded
initial multiplier of a martingale.  This is the small measure-theoretic
primitive needed when a localizing time is allowed to equal the bottom time:
the defining indicator in `ProbabilityTheory.Locally` must be retained while
two local martingales are synchronized.
-/

namespace MeasureTheory

open MeasureTheory Set

variable {Ω ι E : Type*} [MeasurableSpace Ω]
  [Preorder ι] [OrderBot ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}

theorem Martingale.indicator_of_measurableSet_bot
    {f : ι → Ω → E} (hf : Martingale f ℱ μ)
    {s : Set Ω} (hs : MeasurableSet[ℱ ⊥] s) :
    Martingale (fun i ω => s.indicator (f i) ω) ℱ μ := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact (hf.stronglyAdapted i).indicator
      ((ℱ.mono bot_le) s hs)
  · have hs_i : MeasurableSet[ℱ i] s := (ℱ.mono bot_le) s hs
    have hindicator :
        μ[s.indicator (f j) | ℱ i] =ᵐ[μ]
          s.indicator (μ[f j | ℱ i]) :=
      condExp_indicator (hf.integrable j) hs_i
    filter_upwards [hindicator, hf.condExp_ae_eq hij] with ω hindicator hmart
    rw [hindicator]
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact hmart
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]

end MeasureTheory

namespace FTAPTheorem42

/-!
## Gluing compatible local martingales

A local stochastic integral is first constructed on a sequence of bounded
source coordinates.  This section glues such coordinate processes without
assuming that a global raw process already exists.

The compatibility hypothesis is symmetric: two coordinate processes agree
after stopping both of them at the minimum of their localizing times.  Along
an almost surely increasing exhaustive schedule, their pointwise values are
therefore eventually constant.  The pointwise `limUnder` is strongly
adapted, is almost surely càdlàg, and has the prescribed stopped processes.
Usual conditions then give an everywhere càdlàg version, and optional
stopping proves that this version is a local martingale.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace CompatibleLocalMartingaleGluing

open FTAPTheorem42.ProcessNullSetRegularization

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-- The raw pointwise limit of a compatible family of local coordinates. -/
noncomputable def rawLimit (X : Nat -> Process Omega) : Process Omega :=
  fun t omega => limUnder atTop (fun n => X n t omega)

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
/-- Once one coordinate localizer dominates a deterministic time, all later
coordinate values at that time agree with the selected coordinate. -/
theorem rawLimit_eq_of_le
    {tau : Nat -> Omega -> WithTop NNReal}
    {X : Nat -> Process Omega}
    {omega : Omega}
    (hMono : Monotone (tau · omega))
    {n : Nat}
    (hCompat : forall m t,
      MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)) t omega =
        MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)) t omega)
    {t : NNReal} (ht : (t : WithTop NNReal) <= tau n omega) :
    rawLimit X t omega = X n t omega := by
  have hEventually : ∀ᶠ m in atTop, X m t omega = X n t omega := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hTau : tau n omega <= tau m omega := hMono hnm
    have hEq := hCompat m t
    have htMin : (t : WithTop NNReal) <=
        min (tau n) (tau m) omega := by
      rw [Pi.inf_apply, min_eq_left hTau]
      exact ht
    rw [MeasureTheory.stoppedProcess_eq_of_le htMin,
      MeasureTheory.stoppedProcess_eq_of_le htMin] at hEq
    exact hEq.symm
  have hTendsto : Tendsto (fun m => X m t omega) atTop
      (nhds (X n t omega)) :=
    tendsto_const_nhds.congr'
      (hEventually.mono fun _ hm => hm.symm)
  exact hTendsto.limUnder_eq

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The raw limit stopped at one schedule coordinate is the corresponding
coordinate process stopped at the same time. -/
theorem rawLimit_stoppedProcess
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat -> Process Omega}
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m))))
    (n : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (rawLimit X) (tau n))
      (MeasureTheory.stoppedProcess (X n) (tau n)) := by
  have hCompatAll : ∀ᵐ omega ∂mu, forall m t,
      MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)) t omega =
        MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)) t omega := by
    rw [ae_all_iff]
    exact fun m => hCompat n m
  filter_upwards [hTau.mono, hCompatAll] with omega hMono hCompatOmega
  intro t
  let u : NNReal :=
    (min (t : WithTop NNReal) (tau n omega)).untopA
  have hu : (u : WithTop NNReal) <= tau n omega := by
    dsimp only [u]
    have hNe : min (t : WithTop NNReal) (tau n omega) ≠
        (⊤ : WithTop NNReal) :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    rw [WithTop.untopA_eq_untop hNe, WithTop.coe_untop _ hNe]
    exact min_le_right _ _
  change rawLimit X u omega = X n u omega
  exact rawLimit_eq_of_le hMono hCompatOmega hu

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The raw compatible limit is strongly adapted. -/
theorem rawLimit_stronglyAdapted
    {X : Nat -> Process Omega}
    (hX : forall n, Martingale (X n) F mu) :
    StronglyAdapted F (rawLimit X) := by
  intro t
  exact @MeasureTheory.StronglyMeasurable.limUnder
    Nat Omega Real (F t) _ _ atTop _
    (fun n omega => X n t omega) _ _
    (fun n => (hX n).stronglyAdapted t)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Off one null set, the raw compatible limit inherits right continuity and
left limits from its local coordinates. -/
theorem rawLimit_regular_ae
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat -> Process Omega}
    (hXRight : forall n omega t,
      ContinuousWithinAt (X n · omega) (Ici t) t)
    (hXLeft : forall n, ProcessHasLeftLimits (X n))
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)))) :
    ∀ᵐ omega ∂mu,
      (forall t, ContinuousWithinAt (rawLimit X · omega) (Ici t) t) /\
        forall t, Tendsto (fun s => rawLimit X s omega) (nhdsWithin t (Iio t))
          (nhds (Function.leftLim (rawLimit X · omega) t)) := by
  have hCompatAll : ∀ᵐ omega ∂mu, forall n m t,
      MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)) t omega =
        MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)) t omega := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    exact hCompat n
  filter_upwards [hTau.mono, hTau.tendsto_top, hCompatAll]
      with omega hMono hTop hCompatOmega
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  have hLocalEq (t : NNReal) : exists n,
      forall s, s < t + 1 -> rawLimit X s omega = X n s omega := by
    obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
    refine ⟨n, fun s hs => ?_⟩
    apply rawLimit_eq_of_le hMono (fun m u => hCompatOmega n m u)
    exact (WithTop.coe_le_coe.mpr hs.le).trans hn.le
  constructor
  · intro t
    obtain ⟨n, hn⟩ := hLocalEq t
    have hNear : ∀ᶠ s in nhdsWithin t (Ici t), s < t + 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds (by exact lt_add_one t))
    have hEq : (rawLimit X · omega) =ᶠ[nhdsWithin t (Ici t)]
        (X n · omega) := by
      filter_upwards [hNear] with s hs
      exact hn s hs
    have hAt : rawLimit X t omega = X n t omega :=
      hn t (lt_add_one t)
    exact (hXRight n omega t).congr_of_eventuallyEq hEq hAt
  · intro t
    obtain ⟨n, hn⟩ := hLocalEq t
    have hNear : ∀ᶠ s in nhdsWithin t (Iio t), s < t + 1 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hs.trans (lt_add_one t)
    have hEq : (fun s => rawLimit X s omega) =ᶠ[nhdsWithin t (Iio t)]
        (X n · omega) := by
      filter_upwards [hNear] with s hs
      exact hn s hs
    have hTendsto : Tendsto (fun s => rawLimit X s omega)
        (nhdsWithin t (Iio t))
        (nhds (Function.leftLim (X n · omega) t)) :=
      (hXLeft n omega t).congr' hEq.symm
    exact tendsto_leftLim_of_tendsto ⟨_, hTendsto⟩

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Off one null set, the raw compatible limit inherits right continuity
from its local coordinates. -/
theorem rawLimit_rightContinuous_ae
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat -> Process Omega}
    (hXRight : forall n omega t,
      ContinuousWithinAt (X n · omega) (Ici t) t)
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)))) :
    ∀ᵐ omega ∂mu, forall t,
      ContinuousWithinAt (rawLimit X · omega) (Ici t) t := by
  have hCompatAll : ∀ᵐ omega ∂mu, forall n m t,
      MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)) t omega =
        MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)) t omega := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    exact hCompat n
  filter_upwards [hTau.mono, hTau.tendsto_top, hCompatAll]
      with omega hMono hTop hCompatOmega
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  intro t
  obtain ⟨n, hn⟩ := (hTop (t + 1)).exists
  have hLocalEq : forall s, s < t + 1 ->
      rawLimit X s omega = X n s omega := by
    intro s hs
    apply rawLimit_eq_of_le hMono (fun m u => hCompatOmega n m u)
    exact (WithTop.coe_le_coe.mpr hs.le).trans hn.le
  have hNear : ∀ᶠ s in nhdsWithin t (Ici t), s < t + 1 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (by exact lt_add_one t))
  have hEq : (rawLimit X · omega) =ᶠ[nhdsWithin t (Ici t)]
      (X n · omega) := by
    filter_upwards [hNear] with s hs
    exact hLocalEq s hs
  have hAt : rawLimit X t omega = X n t omega :=
    hLocalEq t (lt_add_one t)
  exact (hXRight n omega t).congr_of_eventuallyEq hEq hAt

/-- Compatible right-continuous true-martingale coordinates glue to one
right-continuous local martingale.  No left-limit hypothesis is needed. -/
theorem exists_rightContinuous_localMartingale
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat -> Process Omega}
    (hX : forall n, Martingale (X n) F mu)
    (hXRight : forall n omega t,
      ContinuousWithinAt (X n · omega) (Ici t) t)
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)))) :
    exists Y : Process Omega,
      StronglyAdapted F Y /\
        LocalMartingale Y F mu /\
        (forall omega t, ContinuousWithinAt (Y · omega) (Ici t) t) /\
        forall n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess Y (tau n))
          (MeasureTheory.stoppedProcess (X n) (tau n)) := by
  let raw := rawLimit X
  have hRawAdapted : StronglyAdapted F raw :=
    rawLimit_stronglyAdapted hX
  have hRawRight : ∀ᵐ omega ∂mu,
      forall t, ContinuousWithinAt (raw · omega) (Ici t) t := by
    exact rawLimit_rightContinuous_ae hTau hXRight hCompat
  obtain ⟨Y, hYAdapted, hYRight, hYRaw⟩ :=
    exists_stronglyAdapted_rightContinuous_version
      hUsual hRawAdapted hRawRight
  have hYStopped (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Y (tau n))
      (MeasureTheory.stoppedProcess (X n) (tau n)) :=
    (hYRaw.stoppedProcess (tau n)).trans
      (rawLimit_stoppedProcess hTau hCompat n)
  have hYLocal : LocalMartingale Y F mu := by
    refine ⟨tau, hTau, fun n => ?_⟩
    let B : Set Omega := {omega | (⊥ : WithTop NNReal) < tau n omega}
    have hB : MeasurableSet[F 0] B := by
      have hEq : B = {omega | tau n omega <= (0 : NNReal)}ᶜ := by
        ext omega
        simp only [B, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
        rw [show (⊥ : WithTop NNReal) =
          ((0 : NNReal) : WithTop NNReal) by rfl]
      rw [hEq]
      exact (hTau.isStoppingTime n).measurableSet_le 0 |>.compl
    have hXStopped : Martingale
        (MeasureTheory.stoppedProcess (X n) (tau n)) F mu :=
      RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        (hX n) (hTau.isStoppingTime n) (hXRight n)
    have hIndicator : Martingale
        (fun t omega => B.indicator
          (MeasureTheory.stoppedProcess (X n) (tau n) t) omega) F mu :=
      hXStopped.indicator_of_measurableSet_bot hB
    have hTargetAdapted : StronglyAdapted F
        (MeasureTheory.stoppedProcess
          (fun t => B.indicator (Y t)) (tau n)) := by
      rw [MeasureTheory.stoppedProcess_indicator_comm']
      intro t
      exact
        (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
          hYAdapted
          (hTau.isStoppingTime n) hYRight t).indicator
            ((F.mono bot_le) B hB)
    apply hIndicator.congr hTargetAdapted
    intro t
    have hStoppedAt := (hYStopped n).eventuallyEq_at t
    filter_upwards [hStoppedAt] with omega homega
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    change B.indicator
        (MeasureTheory.stoppedProcess (X n) (tau n) t) omega =
      B.indicator (MeasureTheory.stoppedProcess Y (tau n) t) omega
    by_cases hOmega : omega ∈ B
    · simp only [Set.indicator_of_mem hOmega]
      exact homega.symm
    · simp only [Set.indicator_of_notMem hOmega]
  exact ⟨Y, hYAdapted, hYLocal, hYRight, hYStopped⟩

/-- Compatible càdlàg true-martingale coordinates glue to one càdlàg local
martingale.  Its stop at every schedule coordinate is indistinguishable from
the corresponding coordinate process stopped at the same time. -/
theorem exists_cadlag_localMartingale
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Nat -> Omega -> WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat -> Process Omega}
    (hX : forall n, Martingale (X n) F mu)
    (hXRight : forall n omega t,
      ContinuousWithinAt (X n · omega) (Ici t) t)
    (hXLeft : forall n, ProcessHasLeftLimits (X n))
    (hCompat : forall n m, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess (X n) (min (tau n) (tau m)))
      (MeasureTheory.stoppedProcess (X m) (min (tau n) (tau m)))) :
    exists Y : Process Omega,
      StronglyAdapted F Y /\
        LocalMartingale Y F mu /\
        (forall omega t, ContinuousWithinAt (Y · omega) (Ici t) t) /\
        ProcessHasLeftLimits Y /\
        forall n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess Y (tau n))
          (MeasureTheory.stoppedProcess (X n) (tau n)) := by
  let raw := rawLimit X
  have hRawAdapted : StronglyAdapted F raw :=
    rawLimit_stronglyAdapted hX
  have hRawRegular : ∀ᵐ omega ∂mu,
      (forall t, ContinuousWithinAt (raw · omega) (Ici t) t) /\
        forall t, Tendsto (fun s => raw s omega) (nhdsWithin t (Iio t))
          (nhds (Function.leftLim (raw · omega) t)) := by
    exact rawLimit_regular_ae hTau hXRight hXLeft hCompat
  obtain ⟨Y, hYAdapted, hYRight, hYLeft, hYRaw⟩ :=
    exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hRawAdapted hRawRegular
  have hYStopped (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess Y (tau n))
      (MeasureTheory.stoppedProcess (X n) (tau n)) :=
    (hYRaw.stoppedProcess (tau n)).trans
      (rawLimit_stoppedProcess hTau hCompat n)
  have hYLocal : LocalMartingale Y F mu := by
    refine ⟨tau, hTau, fun n => ?_⟩
    let B : Set Omega := {omega | (⊥ : WithTop NNReal) < tau n omega}
    have hB : MeasurableSet[F 0] B := by
      have hEq : B = {omega | tau n omega <= (0 : NNReal)}ᶜ := by
        ext omega
        simp only [B, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
        rw [show (⊥ : WithTop NNReal) = ((0 : NNReal) : WithTop NNReal) by rfl]
      rw [hEq]
      exact (hTau.isStoppingTime n).measurableSet_le 0 |>.compl
    have hXStopped : Martingale
        (MeasureTheory.stoppedProcess (X n) (tau n)) F mu :=
      RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        (hX n) (hTau.isStoppingTime n) (hXRight n)
    have hIndicator : Martingale
        (fun t omega => B.indicator
          (MeasureTheory.stoppedProcess (X n) (tau n) t) omega) F mu :=
      hXStopped.indicator_of_measurableSet_bot hB
    have hTargetAdapted : StronglyAdapted F
        (MeasureTheory.stoppedProcess
          (fun t => B.indicator (Y t)) (tau n)) := by
      rw [MeasureTheory.stoppedProcess_indicator_comm']
      intro t
      exact (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
          hYAdapted
          (hTau.isStoppingTime n) hYRight t).indicator
            ((F.mono bot_le) B hB)
    apply hIndicator.congr hTargetAdapted
    intro t
    have hStoppedAt := (hYStopped n).eventuallyEq_at t
    filter_upwards [hStoppedAt] with omega homega
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    change B.indicator
        (MeasureTheory.stoppedProcess (X n) (tau n) t) omega =
      B.indicator (MeasureTheory.stoppedProcess Y (tau n) t) omega
    by_cases hOmega : omega ∈ B
    · simp only [Set.indicator_of_mem hOmega]
      exact homega.symm
    · simp only [Set.indicator_of_notMem hOmega]
  exact ⟨Y, hYAdapted, hYLocal, hYRight, hYLeft, hYStopped⟩

end CompatibleLocalMartingaleGluing

end FTAPTheorem42

namespace FTAPTheorem42.CompatibleLocalMartingaleGluing

/-!
## Refining compatible local-martingale coordinates

Extraction followed by tail infima produces an exhaustive common schedule
below the coordinate martingale localizers. The existing true-martingale
gluing theorem then retains agreement at the original outer stops.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

/-- Glue zero-initial local martingales without assuming a common
true-martingale schedule. Agreement is at the original outer stops. -/
theorem exists_cadlag_of_localMartingale
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Nat → Ω → WithTop NNReal}
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    {X : Nat → Process Ω}
    (hX : ∀ n, LocalMartingale (X n) F mu)
    (hXZero : ∀ n, X n 0 = 0)
    (hXRight : ∀ n omega t, ContinuousWithinAt (X n · omega) (Ici t) t)
    (hXLeft : ∀ n, ProcessHasLeftLimits (X n))
    (hCompat : ∀ n m, ProcessIndistinguishable mu
      (stoppedProcess (X n) (min (tau n) (tau m)))
      (stoppedProcess (X m) (min (tau n) (tau m)))) :
    ∃ Y : Process Ω, StronglyAdapted F Y ∧ LocalMartingale Y F mu ∧
      (∀ omega t, ContinuousWithinAt (Y · omega) (Ici t) t) ∧
      ProcessHasLeftLimits Y ∧ ∀ n, ProcessIndistinguishable mu
        (stoppedProcess Y (tau n)) (stoppedProcess (X n) (tau n)) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨k, _, hPre⟩ := hTau.isPrelocalizingSequence_inf_extraction
    (fun n => (hX n).isLocalizingSequence_localSeq)
  let rho : Nat → Ω → WithTop NNReal := fun n omega =>
    ⨅ j ≥ n, min (tau j omega) ((hX j).localSeq (k j) omega)
  have hRho : ProbabilityTheory.IsLocalizingSequence F rho mu :=
    hPre.isLocalizingSequence_biInf
  have hLe : ∀ n omega,
      rho n omega ≤ min (tau n omega) ((hX n).localSeq (k n) omega) := by
    intro n omega
    exact (iInf_le _ n).trans (iInf_le _ le_rfl)
  have hOuter : ∀ n, rho n ≤ tau n := fun n omega => (hLe n omega).trans (min_le_left _ _)
  have hInner : ∀ n, rho n ≤ (hX n).localSeq (k n) :=
    fun n omega => (hLe n omega).trans (min_le_right _ _)
  let Z : Nat → Process Ω := fun n => stoppedProcess (X n) (rho n)
  have hZ : ∀ n, Martingale (Z n) F mu := by
    intro n
    have h := RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      ((hX n).closed_localSeq_of_zero (hXZero n) (k n)) (hRho.isStoppingTime n)
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous (X n) (hXRight n))
    rw [stoppedProcess_stoppedProcess_of_le_right (hInner n)] at h
    exact h
  have hRaw : ∀ n, ProcessIndistinguishable mu
      (stoppedProcess (rawLimit X) (rho n)) (Z n) := by
    intro n
    have h := (rawLimit_stoppedProcess hTau hCompat n).stoppedProcess (rho n)
    simpa only [stoppedProcess_stoppedProcess_of_le_right (hOuter n)] using h
  have hZCompat : ∀ n m, ProcessIndistinguishable mu
      (stoppedProcess (Z n) (min (rho n) (rho m)))
      (stoppedProcess (Z m) (min (rho n) (rho m))) := by
    intro n m
    have hn := (hRaw n).stoppedProcess (min (rho n) (rho m))
    have hm := (hRaw m).stoppedProcess (min (rho n) (rho m))
    rw [stoppedProcess_stoppedProcess_of_le_right (fun _ => min_le_left _ _)] at hn
    rw [stoppedProcess_stoppedProcess_of_le_right (fun _ => min_le_right _ _)] at hm
    exact hn.symm.trans hm
  obtain ⟨Y, hYA, hYM, hYR, hYL, hYS⟩ := exists_cadlag_localMartingale
    hUsual hRho hZ
    (fun n => RightContinuousStoppedMartingale.stoppedProcess_rightContinuous (X n) (hXRight n))
    (fun n => (hXLeft n).stoppedProcess (rho n)) hZCompat
  have hYRaw : ProcessIndistinguishable mu Y (rawLimit X) := by
    apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hRho
    intro n
    have h := hYS n
    have hSelf : stoppedProcess (Z n) (rho n) = Z n :=
      stoppedProcess_stoppedProcess_of_le_right le_rfl
    rw [hSelf] at h
    exact h.trans (hRaw n).symm
  exact ⟨Y, hYA, hYM, hYR, hYL, fun n =>
    (hYRaw.stoppedProcess (tau n)).trans (rawLimit_stoppedProcess hTau hCompat n)⟩

end FTAPTheorem42.CompatibleLocalMartingaleGluing
