/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Process.CadlagLargeJumpStopping
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Chronological enumeration of stochastic large jumps

The preceding two modules contain the pathwise finite large-jump core and a
debut for the first jump.  This module iterates that construction.  The
iterator uses `⊤` as its empty sentinel; in particular, the deterministic
horizon is never used as a fake empty value.

Only the chronological time enumeration is constructed here.  The finite
sum process is deliberately left to the consumer which needs it.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CadlagLargeJumpEnumeration

variable
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

open CadlagLargeJumpStopping

/-! ## Deterministic post-stopping tails -/

/-- The process which is zero through `q` and is translated by `X q` after
`q`.  This deterministic operation lets the debut theorem observe jumps
strictly after a previously selected time. -/
noncomputable def postProcess (X : Process Ω) (q : ℝ≥0) : Process Ω :=
  fun t ω => if t ≤ q then 0 else X t ω - X q ω

omit [MeasurableSpace Ω] in
@[simp] theorem postProcess_eq_zero_of_le
    (X : Process Ω) (q t : ℝ≥0) (ω : Ω) (ht : t ≤ q) :
    postProcess X q t ω = 0 := by
  simp [postProcess, ht]

omit [MeasurableSpace Ω] in
@[simp] theorem postProcess_eq_sub_of_gt
    (X : Process Ω) (q t : ℝ≥0) (ω : Ω) (hqt : q < t) :
    postProcess X q t ω = X t ω - X q ω := by
  simp [postProcess, not_le_of_gt hqt]

theorem postProcess_stronglyAdapted
    (hX : StronglyAdapted ℱ X) (q : ℝ≥0) :
    StronglyAdapted ℱ (postProcess X q) := by
  intro t
  by_cases ht : t ≤ q
  · change StronglyMeasurable[ℱ t]
      (fun ω => if t ≤ q then 0 else X t ω - X q ω)
    simp only [ite_eq_left ht]
    exact stronglyMeasurable_const
  · have hq : StronglyMeasurable[ℱ t] (X q) :=
      (hX q).mono (ℱ.mono (le_of_not_ge ht))
    change StronglyMeasurable[ℱ t]
      (fun ω => if t ≤ q then 0 else X t ω - X q ω)
    simp only [ite_eq_right ht]
    exact (hX t).sub hq

omit [MeasurableSpace Ω] in
theorem postProcess_rightContinuous
    {X : Process Ω}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (q : ℝ≥0) :
    ∀ ω t, ContinuousWithinAt ((postProcess X q) · ω) (Ici t) t := by
  intro ω t
  by_cases ht : t < q
  · have hzero : (postProcess X q · ω) =ᶠ[𝓝[Ici t] t]
        (fun _ : ℝ≥0 => (0 : ℝ)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht)] with s hs
      exact postProcess_eq_zero_of_le X q s ω hs
    exact continuousWithinAt_const.congr_of_eventuallyEq hzero
      (postProcess_eq_zero_of_le X q t ω ht.le)
  · by_cases htq : t = q
    · subst t
      have hconst : ContinuousWithinAt (fun _ : ℝ≥0 => X q ω)
          (Ici q) q := continuousWithinAt_const
      apply (hRight ω q).sub hconst |>.congr
      · intro s hs
        change q ≤ s at hs
        rcases hs.eq_or_lt with rfl | hsq
        · simp [postProcess]
        · simp [postProcess, not_le_of_gt hsq]
      · simp [postProcess]
    · have hqt : q < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm htq)
      have hconst : ContinuousWithinAt (fun _ : ℝ≥0 => X q ω)
          (Ici t) t := continuousWithinAt_const
      apply (hRight ω t).sub hconst |>.congr
      · intro s hs
        have hqs : q < s := hqt.trans_le hs
        simp [postProcess, not_le_of_gt hqs]
      · simp [postProcess, not_le_of_gt hqt]

omit [MeasurableSpace Ω] in
theorem postProcess_leftLimits
    {X : Process Ω}
    (hLeft : ProcessHasLeftLimits X) (q : ℝ≥0) :
    ProcessHasLeftLimits (postProcess X q) := by
  intro ω t
  by_cases ht : t ≤ q
  · have hzero : (postProcess X q · ω) =ᶠ[𝓝[<] t]
        (fun _ : ℝ≥0 => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact postProcess_eq_zero_of_le X q s ω (hs.le.trans ht)
    exact tendsto_leftLim_of_tendsto ⟨0,
      tendsto_const_nhds.congr' hzero.symm⟩
  · have hqt : q < t := lt_of_not_ge ht
    have heq : (postProcess X q · ω) =ᶠ[𝓝[<] t]
        (fun s => X s ω - X q ω) := by
      filter_upwards [Ioc_mem_nhdsLT hqt] with s hs
      exact postProcess_eq_sub_of_gt X q s ω hs.1
    exact tendsto_leftLim_of_tendsto ⟨
      Function.leftLim (fun s => X s ω) t - X q ω,
      (hLeft ω t).sub tendsto_const_nhds |>.congr' heq.symm⟩

omit [MeasurableSpace Ω] in
theorem postProcess_leftJump_eq_of_gt
    {X : Process Ω} (hLeft : ProcessHasLeftLimits X)
    (q t : ℝ≥0) (ω : Ω) (hqt : q < t) :
    processLeftJump (postProcess X q) t ω = processLeftJump X t ω := by
  let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨q, hqt⟩
  have hlimX := hLeft ω t
  have heq : Function.leftLim (fun s => postProcess X q s ω) t =
      Function.leftLim (fun s => X s ω) t - X q ω := by
    have hevent : (postProcess X q · ω) =ᶠ[𝓝[<] t]
        (fun s => X s ω - X q ω) := by
      filter_upwards [Ioc_mem_nhdsLT hqt] with s hs
      exact postProcess_eq_sub_of_gt X q s ω hs.1
    apply leftLim_eq_of_tendsto
    exact (hlimX.sub tendsto_const_nhds).congr' hevent.symm
  simp only [processLeftJump, postProcess_eq_sub_of_gt X q t ω hqt, heq]
  ring

omit [MeasurableSpace Ω] in
theorem postProcess_leftJump_eq_zero_of_le
    {X : Process Ω} (_hLeft : ProcessHasLeftLimits X)
    (q t : ℝ≥0) (ω : Ω) (ht : t ≤ q) :
    processLeftJump (postProcess X q) t ω = 0 := by
  have hzero : (postProcess X q · ω) =ᶠ[𝓝[<] t]
      (fun _ : ℝ≥0 => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact postProcess_eq_zero_of_le X q s ω (hs.le.trans ht)
  simp only [processLeftJump, postProcess_eq_zero_of_le X q t ω ht]
  have hlim : Function.leftLim (fun s => postProcess X q s ω) t = 0 := by
    by_cases ht0 : t = 0
    · subst t
      simpa using (leftLim_eq_of_isBot
        (f := fun s : ℝ≥0 => postProcess X q s ω) isBot_bot)
    · let : NeBot (𝓝[<] t) :=
        nhdsLT_neBot_of_exists_lt ⟨0, (pos_iff_ne_zero).2 ht0⟩
      exact leftLim_eq_of_tendsto (tendsto_const_nhds.congr' hzero.symm)
  rw [hlim, sub_self]

omit [MeasurableSpace Ω] in
theorem postProcess_largeJumpTimeSet_mem_iff
    {X : Process Ω} (hLeft : ProcessHasLeftLimits X)
    {q T t : ℝ≥0} {c : ℝ}
    (hc : 0 < c) (ω : Ω) :
    t ∈ largeJumpTimeSet (fun s => postProcess X q s ω) c T ↔
      t ∈ largeJumpTimeSet (fun s => X s ω) c T ∧ q < t := by
  constructor
  · intro ht
    have htq : q < t := by
      by_contra hnot
      have hle : t ≤ q := le_of_not_gt hnot
      have hzero : c < |processLeftJump (postProcess X q) t ω| := by
        have hjump := ht.2
        change c < |cadlagLeftJump (fun s => postProcess X q s ω) t| at hjump
        simpa only [processLeftJump, cadlagLeftJump] using hjump
      rw [postProcess_leftJump_eq_zero_of_le hLeft q t ω hle] at hzero
      exact (not_lt_of_ge (le_of_lt hc)) (by simpa [abs_zero] using hzero)
    refine ⟨?_, htq⟩
    refine ⟨ht.1, ?_⟩
    have hjump := ht.2
    change c < |processLeftJump (postProcess X q) t ω| at hjump
    rw [postProcess_leftJump_eq_of_gt hLeft q t ω htq] at hjump
    change c < |cadlagLeftJump (fun s => X s ω) t|
    simpa only [processLeftJump, cadlagLeftJump] using hjump
  · rintro ⟨ht, htq⟩
    refine ⟨ht.1, ?_⟩
    change c < |cadlagLeftJump (fun s => postProcess X q s ω) t|
    change c < |processLeftJump (postProcess X q) t ω|
    rw [postProcess_leftJump_eq_of_gt hLeft q t ω htq]
    have hjump := ht.2
    change c < |cadlagLeftJump (fun s => X s ω) t| at hjump
    simpa only [processLeftJump, cadlagLeftJump] using hjump

/-! ## The top-valued successor -/

omit [MeasurableSpace Ω] in
/-- The jump times of `X` strictly after a possibly infinite time `σ`. -/
def largeJumpTimeSetAfter
    (X : Process Ω) (c : ℝ) (T : ℝ≥0)
    (σ : Ω → WithTop ℝ≥0) (ω : Ω) : Set ℝ≥0 :=
  {t | t ∈ largeJumpTimeSet (fun s => X s ω) c T ∧ σ ω < (t : WithTop ℝ≥0)}

omit [MeasurableSpace Ω] in
theorem finite_largeJumpTimeSetAfter
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0} (ω : Ω)
    (hX : (largeJumpTimeSet (fun s => X s ω) c T).Finite) :
    (largeJumpTimeSetAfter X c T σ ω).Finite := by
  apply hX.subset
  intro t ht
  exact ht.1

omit [MeasurableSpace Ω] in
/-- The first retained jump after `σ`; the empty value is `⊤`. -/
noncomputable def nextLargeJumpTime
    (X : Process Ω) (c : ℝ) (T : ℝ≥0)
    (σ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  by
    classical
    exact fun ω => if h : (largeJumpTimeSetAfter X c T σ ω).Nonempty then
      ((sInf (largeJumpTimeSetAfter X c T σ ω) : ℝ≥0) : WithTop ℝ≥0)
    else ⊤

omit [MeasurableSpace Ω] in
theorem nextLargeJumpTime_eq_sInf_of_nonempty
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (σ : Ω → WithTop ℝ≥0) (ω : Ω)
    (hJ : (largeJumpTimeSetAfter X c T σ ω).Nonempty) :
    nextLargeJumpTime X c T σ ω =
      ((sInf (largeJumpTimeSetAfter X c T σ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  unfold nextLargeJumpTime
  rw [dite_eq_left hJ]

omit [MeasurableSpace Ω] in
theorem nextLargeJumpTime_eq_top_of_empty
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (σ : Ω → WithTop ℝ≥0) (ω : Ω)
    (hJ : ¬(largeJumpTimeSetAfter X c T σ ω).Nonempty) :
    nextLargeJumpTime X c T σ ω = ⊤ := by
  unfold nextLargeJumpTime
  rw [dite_eq_right hJ]

omit [MeasurableSpace Ω] in
theorem nextLargeJumpTime_le_of_mem
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (σ : Ω → WithTop ℝ≥0) (ω : Ω)
    {t : ℝ≥0} (ht : t ∈ largeJumpTimeSetAfter X c T σ ω) :
    nextLargeJumpTime X c T σ ω ≤ (t : WithTop ℝ≥0) := by
  by_cases hJ : (largeJumpTimeSetAfter X c T σ ω).Nonempty
  · rw [nextLargeJumpTime_eq_sInf_of_nonempty X c T σ ω hJ]
    exact WithTop.coe_le_coe.mpr (csInf_le' ht)
  · exact False.elim (hJ ⟨t, ht⟩)

omit [MeasurableSpace Ω] in
theorem nextLargeJumpTime_lt_iff
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (ω : Ω) (t : ℝ≥0) (_htt : t ≤ T) :
    nextLargeJumpTime X c T σ ω < (t : WithTop ℝ≥0) ↔
      ∃ s, s ∈ largeJumpTimeSet (fun u => X u ω) c T ∧
        σ ω < (s : WithTop ℝ≥0) ∧ s < t := by
  let J := largeJumpTimeSetAfter X c T σ ω
  have hJfinite : J.Finite := finite_largeJumpTimeSetAfter ω
    (finite_largeJumpTimeSet (fun s => hRight ω s) (fun s => hLeft ω s) hc T)
  have hmemJ : ∀ {s : ℝ≥0}, s ∈ J ↔
      s ∈ largeJumpTimeSet (fun u => X u ω) c T ∧ σ ω < (s : WithTop ℝ≥0) := Iff.rfl
  by_cases hJne : J.Nonempty
  · rw [nextLargeJumpTime_eq_sInf_of_nonempty X c T σ ω hJne]
    rw [WithTop.coe_lt_coe]
    constructor
    · intro hlt
      have hsc : sInf J ∈ J := hJne.csInf_mem hJfinite
      exact ⟨sInf J, (hmemJ.mp hsc).1, (hmemJ.mp hsc).2, hlt⟩
    · rintro ⟨s, hs, hσs, hst⟩
      have hsJ : s ∈ J := hmemJ.mpr ⟨hs, hσs⟩
      exact (csInf_le' hsJ).trans_lt hst
  · rw [nextLargeJumpTime_eq_top_of_empty X c T σ ω hJne]
    constructor
    · intro hlt
      exact ((not_lt_of_ge (le_top : (↑t : WithTop ℝ≥0) ≤ ⊤)) hlt).elim
    · rintro ⟨s, hs, hσs, hst⟩
      exact (hJne ⟨s, hmemJ.mpr ⟨hs, hσs⟩⟩).elim

/-! ## Rational event representation for the successor -/

private def successorBeforeEvent
    (X : Process Ω) (c : ℝ) (T : ℝ≥0)
    (σ : Ω → WithTop ℝ≥0) (t : ℝ≥0) : Set Ω :=
  ⋃ q : ℚ,
    {ω | σ ω < (Real.toNNReal q : WithTop ℝ≥0)} ∩
      CadlagLargeJumpStopping.largeJumpBeforeEvent
        (postProcess X (Real.toNNReal q)) c T t

omit [MeasurableSpace Ω] in
private theorem successorBeforeEvent_eq
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (_hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (ω : Ω) {t : ℝ≥0} (_htt : t ≤ T) :
    ω ∈ successorBeforeEvent X c T σ t ↔
      ∃ s, s ∈ largeJumpTimeSet (fun u => X u ω) c T ∧
        σ ω < (s : WithTop ℝ≥0) ∧ s < t := by
  constructor
  · intro hω
    simp only [successorBeforeEvent, Set.mem_iUnion, Set.mem_inter_iff]
      at hω
    rcases hω with ⟨q, hσq, hbefore⟩
    rcases hbefore with ⟨s, hs, hst⟩
    have hpost := (postProcess_largeJumpTimeSet_mem_iff
      (q := Real.toNNReal q) (c := c) (T := T) (t := s) hLeft hc ω).mp hs
    have hqs : Real.toNNReal q < s := hpost.2
    exact ⟨s, hpost.1, hσq.trans_le (WithTop.coe_le_coe.mpr hqs.le), hst⟩
  · rintro ⟨s, hs, hσs, hst⟩
    have hσfinite : σ ω ≠ ⊤ := by
      intro htop
      rw [htop] at hσs
      exact (not_lt_of_ge le_top) hσs
    lift σ ω to ℝ≥0 using hσfinite with σ₀ hσ₀
    have hσs' : σ₀ < s := by
      apply WithTop.coe_lt_coe.mp
      simpa only [hσ₀] using hσs
    obtain ⟨q, hqnonneg, hσq, hqs⟩ :=
      (NNReal.lt_iff_exists_rat_btwn σ₀ s).mp hσs'
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    refine ⟨?_, ?_⟩
    · change σ ω < (Real.toNNReal q : WithTop ℝ≥0)
      rw [← hσ₀]
      exact WithTop.coe_lt_coe.mpr hσq
    · refine ⟨s, ?_, hst⟩
      apply (postProcess_largeJumpTimeSet_mem_iff
        (q := Real.toNNReal q) (c := c) (T := T) (t := s) hLeft hc ω).mpr
      exact ⟨hs, hqs⟩

private theorem measurableSet_successorBeforeEvent
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (hX : StronglyAdapted ℱ X) (hσ : IsStoppingTime ℱ σ)
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (t : ℝ≥0)
    (htt : t ≤ T) :
    MeasurableSet[ℱ t] (successorBeforeEvent X c T σ t) := by
  unfold successorBeforeEvent
  apply MeasurableSet.iUnion
  intro q
  by_cases hqt : (Real.toNNReal q) ≤ t
  · have hσq : MeasurableSet[ℱ t]
        {ω | σ ω < (Real.toNNReal q : WithTop ℝ≥0)} :=
      hσ.measurableSet_lt_le (i := Real.toNNReal q) (j := t) hqt
    have hpostX : StronglyAdapted ℱ (postProcess X (Real.toNNReal q)) :=
      postProcess_stronglyAdapted hX (Real.toNNReal q)
    have hpostRight := postProcess_rightContinuous hRight (Real.toNNReal q)
    have hpostLeft := postProcess_leftLimits hLeft (Real.toNNReal q)
    have hbefore : MeasurableSet[ℱ t]
        (CadlagLargeJumpStopping.largeJumpBeforeEvent
          (postProcess X (Real.toNNReal q)) c T t) := by
      rw [CadlagLargeJumpStopping.largeJumpBeforeEvent_eq_oscillationEvent
        hpostRight hpostLeft hc htt]
      exact CadlagLargeJumpStopping.measurableSet_oscillationEvent hpostX c t
    exact hσq.inter hbefore
  · have hbeforeEmpty :
        CadlagLargeJumpStopping.largeJumpBeforeEvent
          (postProcess X (Real.toNNReal q)) c T t = ∅ := by
      ext ω
      constructor
      · rintro ⟨s, hs, hst⟩
        have hpost :=
          (postProcess_largeJumpTimeSet_mem_iff
            (q := Real.toNNReal q) (c := c) (T := T) (t := s) hLeft hc ω).mp hs
        have htq : t < Real.toNNReal q := lt_of_not_ge hqt
        exact (not_lt_of_ge htq.le) (hpost.2.trans hst)
      · intro h
        exact h.elim
    rw [hbeforeEmpty, Set.inter_empty]
    exact @MeasurableSet.empty Ω (ℱ t)

private def endpointEvent
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (σ : Ω → WithTop ℝ≥0) : Set Ω :=
  {ω | σ ω < (T : WithTop ℝ≥0)} ∩
    {ω | c < |processLeftJump X T ω|}

private theorem measurableSet_endpointEvent
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (hX : StronglyAdapted ℱ X) (hσ : IsStoppingTime ℱ σ)
    (hLeft : ProcessHasLeftLimits X) :
    MeasurableSet[ℱ T] (endpointEvent X c T σ) := by
  have hσT : MeasurableSet[ℱ T]
      {ω | σ ω < (T : WithTop ℝ≥0)} := hσ.measurableSet_lt T
  have hleft : StronglyMeasurable[ℱ T]
      (fun ω => Function.leftLim (fun s => X s ω) T) := by
    have hp : IsStronglyPredictable ℱ
        (fun t ω => Function.leftLim (X · ω) t) :=
      ProcessHasLeftLimits.stronglyPredictable_leftLim hLeft hX
    exact hp.stronglyAdapted T
  have hjump : StronglyMeasurable[ℱ T]
      (fun ω => processLeftJump X T ω) := by
    change StronglyMeasurable[ℱ T]
      (fun ω => X T ω - Function.leftLim (fun s => X s ω) T)
    exact (hX T).sub hleft
  have hlarge : MeasurableSet[ℱ T]
      {ω | c < |processLeftJump X T ω|} := by
    simpa only [Real.norm_eq_abs] using
      (stronglyMeasurable_const.measurableSet_lt hjump.norm)
  simpa only [endpointEvent] using hσT.inter hlarge

private theorem measurableSet_successor_lt
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (hX : StronglyAdapted ℱ X) (hσ : IsStoppingTime ℱ σ)
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (t : ℝ≥0) :
    MeasurableSet[ℱ t]
      {ω | nextLargeJumpTime X c T σ ω < (t : WithTop ℝ≥0)} := by
  by_cases htt : t ≤ T
  · rw [show {ω | nextLargeJumpTime X c T σ ω < (t : WithTop ℝ≥0)} =
        successorBeforeEvent X c T σ t by
      ext ω
      exact (nextLargeJumpTime_lt_iff hRight hLeft hc ω t htt).trans
        (successorBeforeEvent_eq hRight hLeft hc ω htt).symm]
    exact measurableSet_successorBeforeEvent hX hσ hRight hLeft hc t htt
  · have hTt : T < t := lt_of_not_ge htt
    have hpre : MeasurableSet[ℱ T]
        (successorBeforeEvent X c T σ T) :=
      measurableSet_successorBeforeEvent hX hσ hRight hLeft hc T le_rfl
    have hend : MeasurableSet[ℱ T] (endpointEvent X c T σ) :=
      measurableSet_endpointEvent hX hσ hLeft
    have heq : {ω | nextLargeJumpTime X c T σ ω < (t : WithTop ℝ≥0)} =
        successorBeforeEvent X c T σ T ∪ endpointEvent X c T σ := by
      ext ω
      constructor
      · intro hω
        change nextLargeJumpTime X c T σ ω < (t : WithTop ℝ≥0) at hω
        by_cases hpreω : ω ∈ successorBeforeEvent X c T σ T
        · exact Or.inl hpreω
        · right
          have hnot : ¬∃ s, s ∈ largeJumpTimeSet (fun u => X u ω) c T ∧
              σ ω < (s : WithTop ℝ≥0) ∧ s < T := by
            intro h
            exact hpreω ((successorBeforeEvent_eq hRight hLeft hc ω le_rfl).mpr h)
          have hJ : (largeJumpTimeSetAfter X c T σ ω).Nonempty := by
            by_contra hne
            rw [nextLargeJumpTime_eq_top_of_empty X c T σ ω hne] at hω
            exact ((not_lt_of_ge (le_top : (t : WithTop ℝ≥0) ≤ ⊤)) hω).elim
          obtain ⟨s, hs, hσs⟩ := hJ
          have hT : s = T := by
            by_contra hne
            have hltT : s < T := lt_of_le_of_ne hs.1.2 hne
            exact hnot ⟨s, hs, hσs, hltT⟩
          subst s
          exact ⟨hσs, by
            change c < |processLeftJump X T ω|
            have hjump := hs.2
            change c < |cadlagLeftJump (fun u => X u ω) T| at hjump
            simpa only [processLeftJump, cadlagLeftJump] using hjump⟩
      · intro hω
        rcases hω with hpreω | hendω
        · have hltT : nextLargeJumpTime X c T σ ω < (T : WithTop ℝ≥0) := by
            rcases (successorBeforeEvent_eq hRight hLeft hc ω le_rfl).mp hpreω with
              ⟨s, hs, hσs, hst⟩
            exact (nextLargeJumpTime_lt_iff hRight hLeft hc ω
              (T := T) (t := T) le_rfl).mpr ⟨s, hs, hσs, hst⟩
          exact hltT.trans (WithTop.coe_lt_coe.mpr hTt)
        · rcases hendω with ⟨hσT, hjump⟩
          change σ ω < (T : WithTop ℝ≥0) at hσT
          change c < |processLeftJump X T ω| at hjump
          have hTpos : 0 < T := by
            by_contra hT0
            have hTzero : T = 0 := le_antisymm (not_lt.mp hT0) bot_le
            subst T
            have hleft0 : Function.leftLim (fun s => X s ω) 0 = X 0 ω :=
              leftLim_eq_of_isBot isBot_bot
            have : processLeftJump X 0 ω = 0 := by
              simp [processLeftJump, hleft0]
            rw [this, abs_zero] at hjump
            exact (not_lt_of_ge (le_of_lt (by positivity : (0 : ℝ) < c))) hjump
          have hTmem : T ∈ largeJumpTimeSet (fun s => X s ω) c T := by
            refine ⟨⟨hTpos, le_rfl⟩, ?_⟩
            change c < |cadlagLeftJump (fun s => X s ω) T|
            simpa only [processLeftJump, cadlagLeftJump] using hjump
          have hnextle : nextLargeJumpTime X c T σ ω ≤ (T : WithTop ℝ≥0) := by
            exact nextLargeJumpTime_le_of_mem X c T σ ω ⟨hTmem, hσT⟩
          exact hnextle.trans_lt (WithTop.coe_lt_coe.mpr hTt)
    rw [heq]
    exact ℱ.mono (show T ≤ t from le_of_lt hTt) _ (hpre.union hend)

/-! ## Recursive coordinates -/

omit [MeasurableSpace Ω] in
/-- The zero coordinate starts immediately after deterministic time zero. -/
noncomputable def largeJumpTimeEnumeration
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) : ℕ → Ω → WithTop ℝ≥0
  | 0 => nextLargeJumpTime X c T (fun _ => (0 : WithTop ℝ≥0))
  | n + 1 => nextLargeJumpTime X c T (largeJumpTimeEnumeration X c T n)

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_zero
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) :
    largeJumpTimeEnumeration X c T 0 =
      nextLargeJumpTime X c T (fun _ => (0 : WithTop ℝ≥0)) := by
  rfl

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_succ
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    largeJumpTimeEnumeration X c T (n + 1) =
      nextLargeJumpTime X c T (largeJumpTimeEnumeration X c T n) := by
  rfl

theorem largeJumpTimeEnumeration_isStoppingTime
  {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    [ℱ.IsRightContinuous]
    (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ n, IsStoppingTime ℱ
      (largeJumpTimeEnumeration X c T n) := by
  intro n
  induction n with
  | zero =>
      apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
      intro t
      exact measurableSet_successor_lt hX (isStoppingTime_const ℱ 0)
        hRight hLeft hc t
  | succ n ih =>
      apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
      intro t
      exact measurableSet_successor_lt hX ih hRight hLeft hc t

omit [MeasurableSpace Ω] in
theorem nextLargeJumpTime_ge
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {σ : Ω → WithTop ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (ω : Ω) :
    σ ω ≤ nextLargeJumpTime X c T σ ω := by
  by_cases hJ : (largeJumpTimeSetAfter X c T σ ω).Nonempty
  · rw [nextLargeJumpTime_eq_sInf_of_nonempty X c T σ ω hJ]
    exact (hJ.csInf_mem (finite_largeJumpTimeSetAfter ω
      (finite_largeJumpTimeSet (fun s => hRight ω s) (fun s => hLeft ω s) hc T))).2.le
  · rw [nextLargeJumpTime_eq_top_of_empty X c T σ ω hJ]
    exact le_top

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_monotone
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ ω, Monotone (largeJumpTimeEnumeration X c T · ω) := by
  intro ω
  apply monotone_nat_of_le_succ
  intro n
  rw [largeJumpTimeEnumeration_succ]
  exact nextLargeJumpTime_ge hRight hLeft hc ω

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_succ_lt_of_ne_top
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
  (ω : Ω) (n : ℕ)
    (hnext : largeJumpTimeEnumeration X c T (n + 1) ω ≠ ⊤) :
    largeJumpTimeEnumeration X c T n ω <
      largeJumpTimeEnumeration X c T (n + 1) ω := by
  change nextLargeJumpTime X c T
      (largeJumpTimeEnumeration X c T n) ω ≠ ⊤ at hnext
  rw [largeJumpTimeEnumeration_succ]
  have hJ : (largeJumpTimeSetAfter X c T
      (largeJumpTimeEnumeration X c T n) ω).Nonempty := by
    by_contra hne
    rw [nextLargeJumpTime_eq_top_of_empty _ _ _ _ _ hne] at hnext
    exact hnext rfl
  rw [nextLargeJumpTime_eq_sInf_of_nonempty _ _ _ _ _ hJ]
  exact (hJ.csInf_mem (finite_largeJumpTimeSetAfter ω
    (finite_largeJumpTimeSet (fun s => hRight ω s) (fun s => hLeft ω s) hc T))).2

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_mem_of_ne_top
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (ω : Ω) (n : ℕ)
    (hcoord : largeJumpTimeEnumeration X c T n ω ≠ ⊤) :
    ∃ t : ℝ≥0, t ∈ largeJumpTimeSet (fun s => X s ω) c T ∧
      largeJumpTimeEnumeration X c T n ω = (t : WithTop ℝ≥0) := by
  cases n with
  | zero =>
      change nextLargeJumpTime X c T (fun _ => (0 : WithTop ℝ≥0)) ω ≠ ⊤ at hcoord
      have hJ : (largeJumpTimeSetAfter X c T
          (fun _ => (0 : WithTop ℝ≥0)) ω).Nonempty := by
        by_contra hne
        rw [nextLargeJumpTime_eq_top_of_empty _ _ _ _ _ hne] at hcoord
        exact hcoord rfl
      refine ⟨sInf (largeJumpTimeSetAfter X c T
        (fun _ => (0 : WithTop ℝ≥0)) ω), ?_, ?_⟩
      · exact (hJ.csInf_mem (finite_largeJumpTimeSetAfter ω
          (finite_largeJumpTimeSet (fun s => hRight ω s) (fun s => hLeft ω s) hc T))).1
      · rw [largeJumpTimeEnumeration_zero,
          nextLargeJumpTime_eq_sInf_of_nonempty _ _ _ _ _ hJ]
  | succ n =>
      change nextLargeJumpTime X c T
        (largeJumpTimeEnumeration X c T n) ω ≠ ⊤ at hcoord
      have hJ : (largeJumpTimeSetAfter X c T
          (largeJumpTimeEnumeration X c T n) ω).Nonempty := by
        by_contra hne
        rw [nextLargeJumpTime_eq_top_of_empty _ _ _ _ _ hne] at hcoord
        exact hcoord rfl
      refine ⟨sInf (largeJumpTimeSetAfter X c T
          (largeJumpTimeEnumeration X c T n) ω), ?_, ?_⟩
      · exact (hJ.csInf_mem (finite_largeJumpTimeSetAfter ω
          (finite_largeJumpTimeSet (fun s => hRight ω s) (fun s => hLeft ω s) hc T))).1
      · rw [largeJumpTimeEnumeration_succ,
          nextLargeJumpTime_eq_sInf_of_nonempty _ _ _ _ _ hJ]

omit [MeasurableSpace Ω] in
theorem largeJumpTimeEnumeration_eventually_top
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (ω : Ω) :
    ∃ N, ∀ n ≥ N, largeJumpTimeEnumeration X c T n ω = ⊤ := by
  let A : Set ℕ := {n | largeJumpTimeEnumeration X c T n ω ≠ ⊤}
  let J : Set ℝ≥0 := largeJumpTimeSet (fun s => X s ω) c T
  let Jtop : Set (WithTop ℝ≥0) := (fun t : ℝ≥0 =>
    (t : WithTop ℝ≥0)) '' J
  have hmono : Monotone (largeJumpTimeEnumeration X c T · ω) :=
    largeJumpTimeEnumeration_monotone hRight hLeft hc ω
  have hactive_of_le : ∀ {m n : ℕ}, m ≤ n →
      largeJumpTimeEnumeration X c T n ω ≠ ⊤ →
      largeJumpTimeEnumeration X c T m ω ≠ ⊤ := by
    intro m n hmn hn hm
    have hle := hmono hmn
    have htop : (⊤ : WithTop ℝ≥0) ≤
        largeJumpTimeEnumeration X c T n ω := by simpa [hm] using hle
    exact hn (top_unique htop)
  have hstrict_of_lt : ∀ {m n : ℕ}, m < n →
      largeJumpTimeEnumeration X c T n ω ≠ ⊤ →
      largeJumpTimeEnumeration X c T m ω <
        largeJumpTimeEnumeration X c T n ω := by
    intro m n hmn
    induction n with
    | zero => omega
    | succ n ih =>
        intro hn
        by_cases hmn_eq : m = n
        · subst m
          exact largeJumpTimeEnumeration_succ_lt_of_ne_top
            hRight hLeft hc ω n hn
        · have hmn' : m < n := by omega
          have hn' := hactive_of_le (Nat.le_succ n) hn
          exact (ih hmn' hn').trans
            (largeJumpTimeEnumeration_succ_lt_of_ne_top
              hRight hLeft hc ω n hn)
  have hAinj : Set.InjOn
      (largeJumpTimeEnumeration X c T · ω) A := by
    intro m hm n hn heq
    by_cases hmn : m < n
    · have hlt := hstrict_of_lt hmn hn
      exact False.elim ((ne_of_lt hlt) heq)
    · by_cases hnm : n < m
      · have hlt := hstrict_of_lt hnm hm
        exact False.elim ((ne_of_gt hlt) heq)
      · omega
  have hJtopfin : Jtop.Finite := by
    apply (finite_largeJumpTimeSet (fun s => hRight ω s)
      (fun s => hLeft ω s) hc T).image
  have hAimage : (largeJumpTimeEnumeration X c T · ω) '' A ⊆ Jtop := by
    intro z hz
    rcases hz with ⟨n, hn, rfl⟩
    rcases largeJumpTimeEnumeration_mem_of_ne_top hRight hLeft hc ω n hn with
      ⟨t, ht, heq⟩
    exact ⟨t, ht, heq.symm⟩
  have hAfinite : A.Finite :=
    (hJtopfin.subset hAimage).of_finite_image hAinj
  obtain ⟨N, hN⟩ := hAfinite.exists_le
  refine ⟨N + 1, ?_⟩
  intro n hn
  by_contra hactive
  exact (not_lt_of_ge (hN n hactive))
    (lt_of_lt_of_le (Nat.lt_succ_self N) hn)

omit [MeasurableSpace Ω] in
theorem mem_range_largeJumpTimeEnumeration
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (ω : Ω)
    {t : ℝ≥0} (ht : t ∈ largeJumpTimeSet (fun s => X s ω) c T) :
    ∃ n, largeJumpTimeEnumeration X c T n ω = (t : WithTop ℝ≥0) := by
  obtain ⟨N, hN⟩ := largeJumpTimeEnumeration_eventually_top hRight hLeft hc ω
  have htop : largeJumpTimeEnumeration X c T (N + 1) ω = ⊤ :=
    hN (N + 1) (Nat.le_succ N)
  have hbelow : ∀ n, ∀ {s : ℝ≥0},
      s ∈ largeJumpTimeSet (fun u => X u ω) c T →
      (s : WithTop ℝ≥0) < largeJumpTimeEnumeration X c T n ω →
      ∃ k, largeJumpTimeEnumeration X c T k ω = (s : WithTop ℝ≥0) := by
    intro n
    induction n with
    | zero =>
        intro s hs hlt
        have hsafter : s ∈ largeJumpTimeSetAfter X c T
            (fun _ => (0 : WithTop ℝ≥0)) ω := by
          exact ⟨hs, WithTop.coe_pos.mpr hs.1.1⟩
        have hle := nextLargeJumpTime_le_of_mem X c T
          (fun _ => (0 : WithTop ℝ≥0)) ω hsafter
        rw [largeJumpTimeEnumeration_zero] at hlt
        exact False.elim ((not_lt_of_ge hle) hlt)
    | succ n ih =>
        intro s hs hlt
        by_cases hltprev : (s : WithTop ℝ≥0) <
            largeJumpTimeEnumeration X c T n ω
        · exact ih hs hltprev
        · have hprevle : largeJumpTimeEnumeration X c T n ω ≤
              (s : WithTop ℝ≥0) := le_of_not_gt hltprev
          have heq : largeJumpTimeEnumeration X c T n ω = (s : WithTop ℝ≥0) := by
            by_contra hne
            have hprevlt : largeJumpTimeEnumeration X c T n ω <
                (s : WithTop ℝ≥0) := lt_of_le_of_ne hprevle hne
            have hsafter : s ∈ largeJumpTimeSetAfter X c T
                (largeJumpTimeEnumeration X c T n) ω :=
              ⟨hs, hprevlt⟩
            have hnextle := nextLargeJumpTime_le_of_mem X c T
              (largeJumpTimeEnumeration X c T n) ω hsafter
            rw [largeJumpTimeEnumeration_succ] at hlt
            exact (not_lt_of_ge hnextle) hlt
          exact ⟨n, heq⟩
  exact hbelow (N + 1) ht (by simpa [htop] using (WithTop.coe_lt_top t))

end CadlagLargeJumpEnumeration

end FTAPTheorem42
