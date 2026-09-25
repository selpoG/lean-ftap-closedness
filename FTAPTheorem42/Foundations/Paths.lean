/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.Topology.Order.LeftRightLim
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Foundations.ProcessIndistinguishable

/-! # Paths shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The left jump of a real-valued process.  At time zero this is zero because
`Function.leftLim` uses the current value at a bottom element. -/
noncomputable def processLeftJump (X : Process Ω) : Process Ω :=
  fun t ω => X t ω - Function.leftLim (fun s => X s ω) t

/-- Every sample path tends to its selected left limit from the left. -/
def ProcessHasLeftLimits (X : Process Ω) : Prop :=
  ∀ ω t, Tendsto (fun s => X s ω) (𝓝[<] t)
    (𝓝 (Function.leftLim (fun s => X s ω) t))

omit [MeasurableSpace Ω] in
/-- Multiplication by a fixed event indicator preserves pathwise left
limits. -/
theorem ProcessHasLeftLimits.indicator {X : Process Ω}
    (hX : ProcessHasLeftLimits X) (B : Set Ω) :
    ProcessHasLeftLimits fun t => B.indicator (X t) := by
  intro ω t
  by_cases hω : ω ∈ B
  · simpa only [Set.indicator_of_mem hω] using hX ω t
  · simpa only [Set.indicator_of_notMem hω] using
      (tendsto_leftLim_of_tendsto
        (f := fun _ : ℝ≥0 => (0 : ℝ)) (a := t)
        ⟨0, tendsto_const_nhds⟩)

omit [MeasurableSpace Ω] in
/-- Stopping a process preserves pathwise left limits. -/
theorem ProcessHasLeftLimits.stoppedProcess {X : Process Ω}
    (hX : ProcessHasLeftLimits X) (ρ : Ω → WithTop ℝ≥0) :
    ProcessHasLeftLimits (MeasureTheory.stoppedProcess X ρ) := by
  intro ω t
  apply tendsto_leftLim_of_tendsto
  by_cases hρTop : ρ ω = ⊤
  · have heq : (fun s => MeasureTheory.stoppedProcess X ρ s ω) =
        fun s => X s ω := by
      funext s
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      simp only [hρTop, le_top]
    exact ⟨_, by rw [heq]; exact hX ω t⟩
  · lift ρ ω to ℝ≥0 using hρTop with r hr
    by_cases htr : t ≤ r
    · have heq : Filter.EventuallyEq (nhdsWithin t (Set.Iio t))
          (fun s => MeasureTheory.stoppedProcess X ρ s ω)
          (fun s => X s ω) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        apply MeasureTheory.stoppedProcess_eq_of_le
        rw [← hr]
        exact WithTop.coe_le_coe.mpr (hs.le.trans htr)
      exact ⟨_, (hX ω t).congr' heq.symm⟩
    · have hrt : r < t := lt_of_not_ge htr
      have heq : Filter.EventuallyEq (nhdsWithin t (Set.Iio t))
          (fun s => MeasureTheory.stoppedProcess X ρ s ω)
          (fun _ => X r ω) := by
        filter_upwards [Ico_mem_nhdsLT hrt] with s hs
        rw [MeasureTheory.stoppedProcess_eq_of_ge]
        · rw [← hr, WithTop.untopA_eq_untop WithTop.coe_ne_top,
            WithTop.untop_coe]
        · rw [← hr]
          exact WithTop.coe_le_coe.mpr hs.1
      exact ⟨X r ω, tendsto_const_nhds.congr' heq.symm⟩

omit [MeasurableSpace Ω] in
theorem ProcessHasLeftLimits.add {X Y : Process Ω}
    (hX : ProcessHasLeftLimits X) (hY : ProcessHasLeftLimits Y) :
    ProcessHasLeftLimits fun t ω => X t ω + Y t ω := by
  intro ω t
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simp [hbot]
  · have hsum := (hX ω t).add (hY ω t)
    rw [leftLim_eq_of_tendsto hsum]
    exact hsum

omit [MeasurableSpace Ω] in
theorem ProcessHasLeftLimits.neg {X : Process Ω}
    (hX : ProcessHasLeftLimits X) :
    ProcessHasLeftLimits fun t ω => -X t ω := by
  intro ω t
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simp [hbot]
  · have hneg := (hX ω t).neg
    rw [leftLim_eq_of_tendsto hneg]
    exact hneg

omit [MeasurableSpace Ω] in
/-- Multiplication by a real constant preserves pathwise left limits. -/
theorem ProcessHasLeftLimits.const_mul {X : Process Ω}
    (hX : ProcessHasLeftLimits X) (c : ℝ) :
    ProcessHasLeftLimits fun t ω => c * X t ω := by
  intro ω t
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simp [hbot]
  · have hmul := (hX ω t).const_mul c
    rw [leftLim_eq_of_tendsto hmul]
    exact hmul

omit [MeasurableSpace Ω] in
theorem ProcessHasLeftLimits.sub {X Y : Process Ω}
    (hX : ProcessHasLeftLimits X) (hY : ProcessHasLeftLimits Y) :
    ProcessHasLeftLimits fun t ω => X t ω - Y t ω :=
  hX.add hY.neg

omit [MeasurableSpace Ω] in
theorem processLeftJump_add {X Y : Process Ω}
    (hX : ProcessHasLeftLimits X) (hY : ProcessHasLeftLimits Y)
    (t : ℝ≥0) (ω : Ω) :
    processLeftJump (fun s ω => X s ω + Y s ω) t ω =
      processLeftJump X t ω + processLeftJump Y t ω := by
  have hsum := (hX ω t).add (hY ω t)
  unfold processLeftJump
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot _ hbot,
      leftLim_eq_of_eq_bot _ hbot, leftLim_eq_of_eq_bot _ hbot]
    ring
  · rw [show Function.leftLim (fun s => X s ω + Y s ω) t =
        Function.leftLim (fun s => X s ω) t +
          Function.leftLim (fun s => Y s ω) t by
      apply leftLim_eq_of_tendsto
      exact hsum]
    ring

omit [MeasurableSpace Ω] in
/-- The left jump of a constant multiple is the same multiple of the left
jump. -/
theorem processLeftJump_const_mul {X : Process Ω}
    (hX : ProcessHasLeftLimits X) (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    processLeftJump (fun s ω => c * X s ω) t ω =
      c * processLeftJump X t ω := by
  have hmul := (hX ω t).const_mul c
  unfold processLeftJump
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot _ hbot,
      leftLim_eq_of_eq_bot _ hbot]
    ring
  · rw [show Function.leftLim (fun s => c * X s ω) t =
        c * Function.leftLim (fun s => X s ω) t by
      apply leftLim_eq_of_tendsto
      exact hmul]
    ring

omit [MeasurableSpace Ω] in
/-- Left jumps commute with subtraction for processes having pathwise left
limits. -/
theorem processLeftJump_sub {X Y : Process Ω}
    (hX : ProcessHasLeftLimits X) (hY : ProcessHasLeftLimits Y)
    (t : ℝ≥0) (ω : Ω) :
    processLeftJump (fun s ω => X s ω - Y s ω) t ω =
      processLeftJump X t ω - processLeftJump Y t ω := by
  have hNeg : ProcessHasLeftLimits (fun s ω => (-1 : ℝ) * Y s ω) :=
    hY.const_mul (-1)
  rw [show (fun s ω => X s ω - Y s ω) =
      (fun s ω => X s ω + (-1 : ℝ) * Y s ω) by
        funext s ω
        ring]
  rw [processLeftJump_add hX hNeg,
    processLeftJump_const_mul hY (-1)]
  ring

omit [MeasurableSpace Ω] in
/-- Before and at a stopping time, the stopped process has the same left
jump as the original process. -/
theorem processLeftJump_stoppedProcess_eq_of_le
    (X : Process Ω) (hX : ProcessHasLeftLimits X)
    (ρ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : (t : WithTop ℝ≥0) ≤ ρ ω) :
    processLeftJump (MeasureTheory.stoppedProcess X ρ) t ω =
      processLeftJump X t ω := by
  have heq : (fun s => MeasureTheory.stoppedProcess X ρ s ω) =ᶠ[𝓝[<] t]
      fun s => X s ω := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply MeasureTheory.stoppedProcess_eq_of_le
    exact (WithTop.coe_le_coe.mpr hs.le).trans ht
  have hlim : Tendsto
      (fun s => MeasureTheory.stoppedProcess X ρ s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => X s ω) t)) :=
    (hX ω t).congr' heq.symm
  unfold processLeftJump
  rw [MeasureTheory.stoppedProcess_eq_of_le ht]
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot _ hbot,
      leftLim_eq_of_eq_bot _ hbot,
      MeasureTheory.stoppedProcess_eq_of_le ht]
  · rw [show Function.leftLim
        (fun s => MeasureTheory.stoppedProcess X ρ s ω) t =
          Function.leftLim (fun s => X s ω) t by
      exact leftLim_eq_of_tendsto hlim]

omit [MeasurableSpace Ω] in
/-- Strictly after a stopping time, the stopped process has zero left jump. -/
theorem processLeftJump_stoppedProcess_eq_zero_of_lt
    (X : Process Ω) (ρ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) (ht : ρ ω < (t : WithTop ℝ≥0)) :
    processLeftJump (MeasureTheory.stoppedProcess X ρ) t ω = 0 := by
  have hρTop : ρ ω ≠ ⊤ := ne_top_of_lt ht
  lift ρ ω to ℝ≥0 using hρTop with r hr
  have hrt : r < t := WithTop.coe_lt_coe.mp ht
  let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨r, hrt⟩
  have hvalue : MeasureTheory.stoppedProcess X ρ t ω = X r ω := by
    rw [MeasureTheory.stoppedProcess_eq_of_ge]
    · rw [← hr, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    · rw [← hr]
      exact WithTop.coe_le_coe.mpr hrt.le
  have heq : (fun s => MeasureTheory.stoppedProcess X ρ s ω) =ᶠ[𝓝[<] t]
      fun _ => X r ω := by
    filter_upwards [Ico_mem_nhdsLT hrt] with s hs
    rw [MeasureTheory.stoppedProcess_eq_of_ge]
    · rw [← hr, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    · rw [← hr]
      exact WithTop.coe_le_coe.mpr hs.1
  have hlim : Tendsto
      (fun s => MeasureTheory.stoppedProcess X ρ s ω) (𝓝[<] t)
      (𝓝 (X r ω)) := tendsto_const_nhds.congr' heq.symm
  unfold processLeftJump
  rw [hvalue, leftLim_eq_of_tendsto hlim, sub_self]

omit [MeasurableSpace Ω] in
/-- Pointwise form of the stopped jump-envelope estimate. -/
theorem abs_processLeftJump_stoppedProcess_le_of_le_horizon_at
    (X : Process Ω) (hX : ProcessHasLeftLimits X)
    (ρ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (J : Ω → ℝ) (ω : Ω)
    (hρT : ρ ω ≤ (T : WithTop ℝ≥0))
    (hJ : 0 ≤ J ω)
    (hJump : ∀ t, t ≤ T → |processLeftJump X t ω| ≤ J ω) :
    ∀ t,
      |processLeftJump (MeasureTheory.stoppedProcess X ρ) t ω| ≤ J ω := by
  intro t
  by_cases ht : (t : WithTop ℝ≥0) ≤ ρ ω
  · rw [processLeftJump_stoppedProcess_eq_of_le X hX ρ t ω ht]
    apply hJump t
    exact WithTop.coe_le_coe.mp (ht.trans hρT)
  · rw [processLeftJump_stoppedProcess_eq_zero_of_lt
      X ρ t ω (lt_of_not_ge ht), abs_zero]
    exact hJ

omit [MeasurableSpace Ω] in
/-- A path bounded up to a deterministic horizon has every left jump before
that horizon bounded by twice the same constant. -/
theorem abs_processLeftJump_le_two_mul_of_bound_upTo
    (X : Process Ω) {C : ℝ} {T t : ℝ≥0}
    (hbound : ∀ s, s ≤ T → |X s ω| ≤ C) (ht : t ≤ T)
    (hX : Tendsto (fun s => X s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => X s ω) t))) :
    |processLeftJump X t ω| ≤ 2 * C := by
  have hC : 0 ≤ C :=
    (abs_nonneg (X 0 ω)).trans (hbound 0 bot_le)
  by_cases ht0 : t = 0
  · subst t
    change |X 0 ω - Function.leftLim (fun s => X s ω) 0| ≤ 2 * C
    rw [show Function.leftLim (fun s => X s ω) 0 = X 0 ω from
      leftLim_eq_of_isBot isBot_bot]
    rw [sub_self, abs_zero]
    positivity
  · have htpos : (0 : ℝ≥0) < t := (pos_iff_ne_zero).2 ht0
    let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hLeftBound :
        |Function.leftLim (fun s => X s ω) t| ≤ C := by
      apply le_of_tendsto hX.abs
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hbound s (hs.le.trans ht)
    calc
      |processLeftJump X t ω| =
          |X t ω - Function.leftLim (fun s => X s ω) t| := rfl
      _ ≤ |X t ω| + |Function.leftLim (fun s => X s ω) t| :=
        abs_sub _ _
      _ ≤ C + C := add_le_add (hbound t ht) hLeftBound
      _ = 2 * C := by ring

omit [MeasurableSpace Ω] in
/-- A path bounded in absolute value by `C` has every left jump bounded by
`2 * C`. -/
theorem abs_processLeftJump_le_two_mul_of_bound
    (X : Process Ω) {C : ℝ} (hbound : ∀ t, |X t ω| ≤ C)
    (t : ℝ≥0)
    (hX : Tendsto (fun s => X s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => X s ω) t))) :
    |processLeftJump X t ω| ≤ 2 * C := by
  exact abs_processLeftJump_le_two_mul_of_bound_upTo X
    (fun s _ => hbound s) (le_refl t) hX

/-- Indistinguishable component decompositions preserve the left-jump
identity on one full-measure set, simultaneously at every time. -/
theorem ProcessIndistinguishable.processLeftJump_eq_add
    {μ : Measure Ω} {X M A : Process Ω}
    (h : ProcessIndistinguishable μ X (fun t ω => M t ω + A t ω))
    (hM : ProcessHasLeftLimits M) (hA : ProcessHasLeftLimits A) :
    ∀ᵐ ω ∂μ, ∀ t,
      processLeftJump X t ω =
        processLeftJump M t ω + processLeftJump A t ω := by
  filter_upwards [h] with ω hω
  intro t
  have hPath : (fun s => X s ω) = fun s => M s ω + A s ω :=
    funext hω
  have hLeft := congrArg (fun f : ℝ≥0 → ℝ => Function.leftLim f t) hPath
  simpa only [processLeftJump, hω t, hLeft] using
    (processLeftJump_add hM hA t ω)

/-- Indistinguishable processes have the same left jumps on one
full-measure set, simultaneously at every time. -/
theorem ProcessIndistinguishable.processLeftJump_eq
    {μ : Measure Ω} {X Y : Process Ω}
    (h : ProcessIndistinguishable μ X Y) :
    ∀ᵐ ω ∂μ, ∀ t,
      processLeftJump X t ω = processLeftJump Y t ω := by
  filter_upwards [h] with ω hω
  intro t
  have hPath : (fun s => X s ω) = fun s => Y s ω := funext hω
  unfold processLeftJump
  rw [hω t, congrArg (fun f : ℝ≥0 → ℝ => Function.leftLim f t) hPath]

end FTAPTheorem42
