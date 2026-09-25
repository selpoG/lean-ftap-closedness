/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationFiltrationLimit
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetelling

/-!
# Predictable jumps of local martingales at announced times

This module localizes a local martingale before an announced finite stopping
time.  The event on which the announcing graph precedes a localizer belongs
to the sigma algebra immediately before the graph.  On that event the
localized and original left jumps agree, which permits the true-martingale
conditional jump identity to be applied without assuming global
integrability of the original local-martingale jump.
-/

open Filter MeasureTheory Set Topology
open scoped MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StoppingTimeAnnouncement

/-- The event that an announced finite stopping time occurs before another
stopping time is measurable immediately before the announced graph. -/
theorem measurableSet_le_stoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → ℝ≥0} (a : StoppingTimeAnnouncement ℱ τ)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) :
    MeasurableSet[predictableGraphMeasurableSpace ℱ τ]
      {ω | (τ ω : WithTop ℝ≥0) ≤ ρ ω} := by
  have hset : {ω | (τ ω : WithTop ℝ≥0) ≤ ρ ω} =
      ⋂ n, {ω | (a.time n ω : WithTop ℝ≥0) < ρ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hτρ n
      exact (WithTop.coe_lt_coe.mpr (a.lt n ω)).trans_le hτρ
    · intro hσρ
      by_contra hτρ
      have hρτ : ρ ω < (τ ω : WithTop ℝ≥0) := lt_of_not_ge hτρ
      have htend : Tendsto (fun n => (a.time n ω : WithTop ℝ≥0)) atTop
          (nhds (τ ω : WithTop ℝ≥0)) :=
        WithTop.continuous_coe.continuousAt.tendsto.comp (a.tendsto ω)
      obtain ⟨n, hn⟩ := (htend.eventually (Ioi_mem_nhds hρτ)).exists
      exact (not_lt_of_ge (hσρ n).le) hn
  rw [hset]
  apply MeasurableSet.iInter
  intro n
  apply IsStoppingTime.measurableSpace_le_predictableGraphMeasurableSpace_of_lt
    (a.isStoppingTime n) (a.lt n)
  have hle := hρ.measurableSet_stopping_time_le (a.isStoppingTime n)
  simpa only [Set.compl_ofPred, Set.mem_ofPred_eq, not_le] using hle.compl

end StoppingTimeAnnouncement

/-- The process used by mathlib's local-property interface at one localizer. -/
noncomputable def localizingStoppedProcess
    (X : Process Ω) (ρ : Ω → WithTop ℝ≥0) : Process Ω :=
  MeasureTheory.stoppedProcess
    (fun t => {ω | (⊥ : WithTop ℝ≥0) < ρ ω}.indicator (X t)) ρ

omit [MeasurableSpace Ω] in
/-- Localizer stopping preserves pathwise left limits. -/
theorem ProcessHasLeftLimits.localizingStoppedProcess
    {X : Process Ω} (hX : ProcessHasLeftLimits X)
    (ρ : Ω → WithTop ℝ≥0) :
    ProcessHasLeftLimits (localizingStoppedProcess X ρ) := by
  exact (hX.indicator {ω | (⊥ : WithTop ℝ≥0) < ρ ω}).stoppedProcess ρ

omit [MeasurableSpace Ω] in
/-- Localizer stopping preserves pathwise right continuity. -/
theorem localizingStoppedProcess_rightContinuous
    (X : Process Ω) (ρ : Ω → WithTop ℝ≥0)
    (hX : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    ∀ ω t, ContinuousWithinAt
      (localizingStoppedProcess X ρ · ω) (Set.Ici t) t := by
  apply RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
  exact RightContinuousStoppedMartingale.indicator_rightContinuous
    X {ω | (⊥ : WithTop ℝ≥0) < ρ ω} hX

omit [MeasurableSpace Ω] in
/-- Before a positive graph time lying below a localizer, the localized path
has the same left jump as the original path. -/
theorem processLeftJump_localizingStoppedProcess_eq_of_le_of_pos
    (X : Process Ω) (hX : ProcessHasLeftLimits X)
    {ρ : Ω → WithTop ℝ≥0} {τ : ℝ≥0} {ω : Ω}
    (hτ : 0 < τ) (hτρ : (τ : WithTop ℝ≥0) ≤ ρ ω) :
    processLeftJump (localizingStoppedProcess X ρ) τ ω =
      processLeftJump X τ ω := by
  have hbotτ : (⊥ : WithTop ℝ≥0) < (τ : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.mpr hτ
  have hbotρ : (⊥ : WithTop ℝ≥0) < ρ ω := hbotτ.trans_le hτρ
  have hωmem : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < ρ ω} := hbotρ
  let : NeBot (nhdsWithin τ (Set.Iio τ)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
  have heq : Filter.EventuallyEq (nhdsWithin τ (Set.Iio τ))
      (fun s => localizingStoppedProcess X ρ s ω) (fun s => X s ω) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [localizingStoppedProcess,
      MeasureTheory.stoppedProcess_eq_of_le
        ((WithTop.coe_le_coe.mpr hs.le).trans hτρ),
      Set.indicator_of_mem hωmem]
  have hlim : Tendsto (fun s => localizingStoppedProcess X ρ s ω)
      (nhdsWithin τ (Set.Iio τ))
      (nhds (Function.leftLim (fun s => X s ω) τ)) :=
    (hX ω τ).congr' heq.symm
  have hleft : Function.leftLim
      (fun s => localizingStoppedProcess X ρ s ω) τ =
        Function.leftLim (fun s => X s ω) τ :=
    leftLim_eq_of_tendsto hlim
  unfold processLeftJump
  rw [hleft, localizingStoppedProcess,
    MeasureTheory.stoppedProcess_eq_of_le hτρ,
    Set.indicator_of_mem hωmem]

namespace LocalMartingale

variable
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {M : Process Ω}

/-- At one localizer, the original local-martingale jump restricted to the
event that the announced graph precedes the localizer is integrable and has
conditional mean zero immediately before the graph. -/
theorem sampledLeftJump_on_localizer
    (hM : LocalMartingale M ℱ μ)
    {τ : Ω → ℝ≥0} (a : StoppingTimeAnnouncement ℱ τ)
    (T : ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M) (k : ℕ) :
    let B := {ω | (τ ω : WithTop ℝ≥0) ≤ hM.localSeq k ω}
    Integrable (B.indicator
        (fun ω => processLeftJump M (τ ω) ω)) μ ∧
      μ[B.indicator (fun ω => processLeftJump M (τ ω) ω) |
          predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ] fun _ => 0 := by
  dsimp only
  let ρ : Ω → WithTop ℝ≥0 := hM.localSeq k
  let L : Process Ω := localizingStoppedProcess M ρ
  let B : Set Ω := {ω | (τ ω : WithTop ℝ≥0) ≤ ρ ω}
  have hρ : IsStoppingTime ℱ ρ :=
    hM.isLocalizingSequence_localSeq.isStoppingTime k
  have hL : Martingale L ℱ μ := by
    simpa only [L, ρ, localizingStoppedProcess] using
      hM.stoppedProcess_localSeq k
  have hLRight : ∀ ω t,
      ContinuousWithinAt (L · ω) (Set.Ici t) t := by
    simpa only [L] using
      localizingStoppedProcess_rightContinuous M ρ hMRight
  have hLLeft : ProcessHasLeftLimits L := by
    simpa only [L] using hMLeft.localizingStoppedProcess ρ
  have hB : MeasurableSet[predictableGraphMeasurableSpace ℱ τ] B := by
    simpa only [B, ρ] using a.measurableSet_le_stoppingTime hρ
  have hm : predictableGraphMeasurableSpace ℱ τ ≤
      (inferInstance : MeasurableSpace Ω) :=
    IsStoppingTime.predictableGraphMeasurableSpace_le hτ
  have hLValueInt : Integrable (fun ω => L (τ ω) ω) μ :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hL hτ hτT hLRight
  have hLLeftInt : Integrable
      (fun ω => Function.leftLim (L · ω) (τ ω)) μ :=
    FTAPTheorem42.Martingale.integrable_sampledLeftLim_of_stoppingTimeAnnouncement
      hL a T hτT hLRight hLLeft
  have hLJumpInt : Integrable
      (fun ω => processLeftJump L (τ ω) ω) μ := by
    change Integrable
      ((fun ω => L (τ ω) ω) -
        fun ω => Function.leftLim (L · ω) (τ ω)) μ
    exact hLValueInt.sub hLLeftInt
  have hJumpEq : B.indicator
      (fun ω => processLeftJump M (τ ω) ω) =
        B.indicator (fun ω => processLeftJump L (τ ω) ω) := by
    funext ω
    by_cases hω : ω ∈ B
    · have hτpos : 0 < τ ω :=
        (bot_le : 0 ≤ a.time 0 ω).trans_lt (a.lt 0 ω)
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact (processLeftJump_localizingStoppedProcess_eq_of_le_of_pos
        M hMLeft hτpos hω).symm
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hRestrictedInt : Integrable
      (B.indicator (fun ω => processLeftJump M (τ ω) ω)) μ := by
    rw [hJumpEq]
    exact hLJumpInt.indicator (hm _ hB)
  refine ⟨hRestrictedInt, ?_⟩
  have hcondL :
      μ[(fun ω => processLeftJump L (τ ω) ω) |
          predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ] fun _ => 0 := by
    apply FTAPTheorem42.Martingale.condExp_sampledLeftJump_ae_eq_zero_of_stoppingTimeAnnouncement
      hL a T hτ hτT hLRight hLLeft
    exact IsStronglyPredictable.stronglyMeasurable_sampledGraph
      (ProcessHasLeftLimits.stronglyPredictable_leftLim
        hLLeft hL.stronglyAdapted) τ
  rw [hJumpEq]
  refine (condExp_indicator hLJumpInt hB).trans ?_
  filter_upwards [hcondL] with ω hω
  by_cases hωB : ω ∈ B
  · rw [Set.indicator_of_mem hωB]
    exact hω
  · rw [Set.indicator_of_notMem hωB]

/-- An announced graph turns a local-martingale decomposition and an
integrable jump envelope into the predictable finite-variation jump bound.
No global integrability of the original local-martingale jump is assumed. -/
theorem finiteVariationLeftJump_ae_le_condExp_of_announcement
    {X A : Process Ω} (hM : LocalMartingale M ℱ μ)
    {τ : Ω → ℝ≥0} (a : StoppingTimeAnnouncement ℱ τ)
    (T : ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hAmeas : StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
      (fun ω => processLeftJump A (τ ω) ω))
    (J : Ω → ℝ) (hJInt : Integrable J μ)
    (hdecomp :
      (fun ω => processLeftJump X (τ ω) ω) =ᵐ[μ]
        fun ω => processLeftJump M (τ ω) ω +
          processLeftJump A (τ ω) ω)
    (hXJ : (fun ω => |processLeftJump X (τ ω) ω|) ≤ᵐ[μ] J) :
    (fun ω => |processLeftJump A (τ ω) ω|) ≤ᵐ[μ]
      μ[J | predictableGraphMeasurableSpace ℱ τ] := by
  let Xτ : Ω → ℝ := fun ω => processLeftJump X (τ ω) ω
  let Mτ : Ω → ℝ := fun ω => processLeftJump M (τ ω) ω
  let Aτ : Ω → ℝ := fun ω => processLeftJump A (τ ω) ω
  let B : ℕ → Set Ω :=
    fun k => {ω | (τ ω : WithTop ℝ≥0) ≤ hM.localSeq k ω}
  have hm : predictableGraphMeasurableSpace ℱ τ ≤
      (inferInstance : MeasurableSpace Ω) :=
    IsStoppingTime.predictableGraphMeasurableSpace_le hτ
  let : SigmaFinite (μ.trim hm) := by infer_instance
  have hB : ∀ k,
      MeasurableSet[predictableGraphMeasurableSpace ℱ τ] (B k) := by
    intro k
    exact a.measurableSet_le_stoppingTime
      (hM.isLocalizingSequence_localSeq.isStoppingTime k)
  have hlocal : ∀ k, ∀ᵐ ω ∂μ, ω ∈ B k →
      |Aτ ω| ≤ μ[J | predictableGraphMeasurableSpace ℱ τ] ω := by
    intro k
    have hMkData := hM.sampledLeftJump_on_localizer
      a T hτ hτT hMRight hMLeft k
    have hMkInt : Integrable ((B k).indicator Mτ) μ := by
      simpa only [B, Mτ] using hMkData.1
    have hcondMk :
        μ[(B k).indicator Mτ | predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ]
          fun _ => 0 := by
      simpa only [B, Mτ] using hMkData.2
    have hAkMeas : StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
        ((B k).indicator Aτ) :=
      hAmeas.indicator (hB k)
    have hJkInt : Integrable ((B k).indicator J) μ :=
      hJInt.indicator (hm _ (hB k))
    have hAkInt : Integrable ((B k).indicator Aτ) μ := by
      apply (hJkInt.add hMkInt.norm).mono'
        (hAkMeas.mono hm).aestronglyMeasurable
      filter_upwards [hdecomp, hXJ] with ω hdecompω hXJω
      change ‖(B k).indicator Aτ ω‖ ≤
        (B k).indicator J ω + ‖(B k).indicator Mτ ω‖
      by_cases hω : ω ∈ B k
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem hω]
        have hAeq : Aτ ω = Xτ ω - Mτ ω := by
          dsimp only [Xτ, Mτ, Aτ]
          linarith
        rw [hAeq]
        calc
          ‖Xτ ω - Mτ ω‖ ≤ ‖Xτ ω‖ + ‖Mτ ω‖ :=
            norm_sub_le _ _
          _ ≤ J ω + ‖Mτ ω‖ := by
            exact add_le_add
              (by simpa only [Xτ, Real.norm_eq_abs] using hXJω) le_rfl
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Set.indicator_of_notMem hω, norm_zero, zero_add]
    have hdecompK : (B k).indicator Xτ =ᵐ[μ]
        fun ω => (B k).indicator Mτ ω + (B k).indicator Aτ ω := by
      filter_upwards [hdecomp] with ω hdecompω
      by_cases hω : ω ∈ B k
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem hω]
        exact hdecompω
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Set.indicator_of_notMem hω, zero_add]
    have hXJK : (fun ω => |(B k).indicator Xτ ω|) ≤ᵐ[μ]
        (B k).indicator J := by
      filter_upwards [hXJ] with ω hXJω
      by_cases hω : ω ∈ B k
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        exact hXJω
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          abs_zero]
    have hbound := abs_le_condExp_of_add_decomposition_of_abs_le
      (m0 := inferInstance) (μ := μ)
      (predictableGraphMeasurableSpace ℱ τ) hm
      hMkInt hAkInt hJkInt hAkMeas hdecompK hcondMk hXJK
    have hcondJ := condExp_indicator hJInt (hB k)
    filter_upwards [hbound, hcondJ] with ω hboundω hcondJω
    intro hω
    rw [hcondJω, Set.indicator_of_mem hω,
      Set.indicator_of_mem hω] at hboundω
    exact hboundω
  have hlocalAll : ∀ᵐ ω ∂μ, ∀ k, ω ∈ B k →
      |Aτ ω| ≤ μ[J | predictableGraphMeasurableSpace ℱ τ] ω :=
    ae_all_iff.2 hlocal
  have htop := hM.isLocalizingSequence_localSeq.tendsto_top
  have hfinal : (fun ω => |Aτ ω|) ≤ᵐ[μ]
      μ[J | predictableGraphMeasurableSpace ℱ τ] := by
    filter_upwards [hlocalAll, htop] with ω hlocalω htopω
    have hevent : ∀ᶠ k in atTop,
        (τ ω : WithTop ℝ≥0) < hM.localSeq k ω :=
      htopω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top (τ ω)))
    obtain ⟨k, hk⟩ := hevent.exists
    exact hlocalω k hk.le
  simpa only [Aτ] using hfinal

end LocalMartingale

end FTAPTheorem42
