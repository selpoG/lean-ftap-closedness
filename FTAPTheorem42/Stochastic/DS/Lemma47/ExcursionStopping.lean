/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.FirstPassage

/-!
# Chronological martingale excursions for Lemma 4.7

The excursion times in the Delbaen--Schachermayer argument are successive
strict first passages of the displacement from the preceding stopped value.
Writing that displacement as `X - X^τ` makes it an adapted right-continuous
process and avoids treating a nonchronological skeleton enumeration as a
trading clock.  Every time below is clamped at one deterministic horizon.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Lemma47ExcursionStopping

/-- Displacement from the value attained at a finite stopping time.  Before
the stopping time this process is zero; afterwards it is `X_t - X_τ`. -/
noncomputable def displacementAfter
    (X : Process Ω) (τ : Ω → ℝ≥0) : Process Ω :=
  fun t ω => X t ω - MeasureTheory.stoppedProcess X
    (fun ω => (τ ω : WithTop ℝ≥0)) t ω

omit [MeasurableSpace Ω] in
@[simp]
theorem displacementAfter_eq_zero_of_le
    (X : Process Ω) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : t ≤ τ ω) :
    displacementAfter X τ t ω = 0 := by
  unfold displacementAfter
  rw [MeasureTheory.stoppedProcess_eq_of_le]
  · exact sub_self _
  · exact WithTop.coe_le_coe.mpr ht

omit [MeasurableSpace Ω] in
theorem displacementAfter_eq_sub_of_ge
    (X : Process Ω) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : τ ω ≤ t) :
    displacementAfter X τ t ω = X t ω - X (τ ω) ω := by
  unfold displacementAfter
  rw [MeasureTheory.stoppedProcess_eq_of_ge]
  · rw [WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  · exact WithTop.coe_le_coe.mpr ht

/-- The displacement from a stopping time is strongly adapted. -/
theorem stronglyAdapted_displacementAfter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyAdapted ℱ (displacementAfter X τ) := by
  exact hX.sub
    (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hX hτ hXRight)

omit [MeasurableSpace Ω] in
/-- The displacement from a stopping time has right-continuous paths. -/
theorem displacementAfter_rightContinuous
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (displacementAfter X τ · ω) (Set.Ici t) t := by
  intro ω t
  exact (hXRight ω t).sub
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      X hXRight ω t)

omit [MeasurableSpace Ω] in
/-- The displacement from a stopping time has left limits. -/
theorem displacementAfter_hasLeftLimits
    {X : Process Ω} (hXLeft : ProcessHasLeftLimits X)
    (τ : Ω → ℝ≥0) :
    ProcessHasLeftLimits (displacementAfter X τ) :=
  hXLeft.sub (hXLeft.stoppedProcess fun ω => (τ ω : WithTop ℝ≥0))

omit [MeasurableSpace Ω] in
/-- Before and at the stopping time, the displacement process has no left
jump. -/
theorem processLeftJump_displacementAfter_eq_zero_of_le
    (X : Process Ω) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : t ≤ τ ω) :
    processLeftJump (displacementAfter X τ) t ω = 0 := by
  have hlim : Tendsto (fun s => displacementAfter X τ s ω) (𝓝[<] t)
      (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (displacementAfter_eq_zero_of_le X τ s ω
      (hs.le.trans ht)).symm
  unfold processLeftJump
  rw [displacementAfter_eq_zero_of_le X τ t ω ht]
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot _ hbot,
      displacementAfter_eq_zero_of_le X τ t ω ht, sub_self]
  · rw [leftLim_eq_of_tendsto hlim]
    exact sub_self (0 : ℝ)

omit [MeasurableSpace Ω] in
/-- Strictly after the stopping time, the displacement process has the same
left jump as the original process. -/
theorem processLeftJump_displacementAfter_eq_of_lt
    (X : Process Ω) (hXLeft : ProcessHasLeftLimits X)
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (ht : τ ω < t) :
    processLeftJump (displacementAfter X τ) t ω =
      processLeftJump X t ω := by
  let : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨τ ω, ht⟩
  have heq : (fun s => displacementAfter X τ s ω) =ᶠ[𝓝[<] t]
      fun s => X s ω - X (τ ω) ω := by
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact displacementAfter_eq_sub_of_ge X τ s ω hs.1.le
  have hlim : Tendsto (fun s => displacementAfter X τ s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => X s ω) t - X (τ ω) ω)) := by
    exact ((hXLeft ω t).sub tendsto_const_nhds).congr' heq.symm
  unfold processLeftJump
  rw [displacementAfter_eq_sub_of_ge X τ t ω ht.le,
    leftLim_eq_of_tendsto hlim]
  ring

omit [MeasurableSpace Ω] in
/-- A jump bound at one sample point also controls the displacement from an
arbitrary finite stopping time at that point. -/
theorem abs_processLeftJump_displacementAfter_le_at
    (X : Process Ω) (hXLeft : ProcessHasLeftLimits X)
    (τ : Ω → ℝ≥0) (J : Ω → ℝ) (ω : Ω)
    (hJump : ∀ t, |processLeftJump X t ω| ≤ J ω) :
    ∀ t, |processLeftJump (displacementAfter X τ) t ω| ≤ J ω := by
  intro t
  by_cases ht : t ≤ τ ω
  · rw [processLeftJump_displacementAfter_eq_zero_of_le X τ t ω ht,
      abs_zero]
    exact (abs_nonneg (processLeftJump X t ω)).trans (hJump t)
  · rw [processLeftJump_displacementAfter_eq_of_lt X hXLeft τ t ω
      (lt_of_not_ge ht)]
    exact hJump t

/-- The next excursion time is the strict unit-displacement passage, clamped
at the deterministic horizon `T`. -/
noncomputable def nextTime
    (X : Process Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0) : Ω → ℝ≥0 :=
  fun ω =>
    (min (absoluteStrictHittingAfter (displacementAfter X τ) 1 ω)
      (T : WithTop ℝ≥0)).untopA

omit [MeasurableSpace Ω] in
@[simp]
theorem coe_nextTime
    (X : Process Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    (nextTime X τ T ω : WithTop ℝ≥0) =
      min (absoluteStrictHittingAfter (displacementAfter X τ) 1 ω)
        (T : WithTop ℝ≥0) := by
  unfold nextTime
  rw [WithTop.untopA_eq_untop]
  · exact WithTop.coe_untop _ _
  · exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)

omit [MeasurableSpace Ω] in
theorem nextTime_le
    (X : Process Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    nextTime X τ T ω ≤ T := by
  exact WithTop.coe_le_coe.mp <| by
    rw [coe_nextTime]
    exact min_le_right _ _

omit [MeasurableSpace Ω] in
/-- The displacement cannot cross its positive level before `τ`. -/
theorem coe_le_absoluteStrictHittingAfter_displacementAfter
    (X : Process Ω) (τ : Ω → ℝ≥0) (ω : Ω) :
    (τ ω : WithTop ℝ≥0) ≤
      absoluteStrictHittingAfter (displacementAfter X τ) 1 ω := by
  by_contra h
  have hlt : absoluteStrictHittingAfter (displacementAfter X τ) 1 ω <
      (τ ω : WithTop ℝ≥0) := lt_of_not_ge h
  unfold absoluteStrictHittingAfter RightContinuousHittingTime.strictHittingAfter at hlt
  rw [MeasureTheory.hittingAfter_lt_iff] at hlt
  obtain ⟨t, ht, hcross⟩ := hlt
  have htτ : t ≤ τ ω := ht.2.le
  rw [displacementAfter_eq_zero_of_le X τ t ω htτ] at hcross
  have : (1 : ℝ) < 0 := by simpa only [abs_zero, mem_Ioi] using hcross
  norm_num at this

omit [MeasurableSpace Ω] in
theorem le_nextTime
    (X : Process Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    τ ω ≤ nextTime X τ T ω := by
  exact WithTop.coe_le_coe.mp <| by
    rw [coe_nextTime]
    exact le_min
      (coe_le_absoluteStrictHittingAfter_displacementAfter X τ ω)
      (WithTop.coe_le_coe.mpr (hτT ω))

omit [MeasurableSpace Ω] in
/-- If the next clamped excursion occurs strictly before the horizon, its
sampled displacement has reached the unit level. -/
theorem one_le_abs_displacementAfter_nextTime_of_lt
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (ω : Ω)
    (hnext : nextTime X τ T ω < T) :
    1 ≤ |displacementAfter X τ (nextTime X τ T ω) ω| := by
  have hHitT : absoluteStrictHittingAfter (displacementAfter X τ) 1 ω <
      (T : WithTop ℝ≥0) := by
    by_contra h
    have hTle : (T : WithTop ℝ≥0) ≤
        absoluteStrictHittingAfter (displacementAfter X τ) 1 ω :=
      le_of_not_gt h
    have hEq : nextTime X τ T ω = T := by
      apply WithTop.coe_injective
      rw [coe_nextTime, min_eq_right hTle]
    exact hnext.ne (hEq)
  have hHitNe :
      absoluteStrictHittingAfter (displacementAfter X τ) 1 ω ≠ ⊤ :=
    ne_top_of_lt hHitT
  have hnextEq : nextTime X τ T ω =
      (absoluteStrictHittingAfter (displacementAfter X τ) 1 ω).untopA := by
    apply WithTop.coe_injective
    rw [coe_nextTime, min_eq_left hHitT.le,
      WithTop.untopA_eq_untop hHitNe, WithTop.coe_untop _ hHitNe]
  rw [hnextEq]
  exact le_abs_untopA_absoluteStrictHittingAfter
    (displacementAfter X τ)
    (displacementAfter_rightContinuous X hXRight τ) 1 ω hHitNe

omit [MeasurableSpace Ω] in
/-- Once the current excursion time equals the deterministic horizon, the
next clamped excursion time remains there. -/
theorem nextTime_eq_of_tau_eq_horizon
    (X : Process Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0) (ω : Ω)
    (hτ : τ ω = T) :
    nextTime X τ T ω = T := by
  apply WithTop.coe_injective
  rw [coe_nextTime, min_eq_right]
  rw [← hτ]
  exact coe_le_absoluteStrictHittingAfter_displacementAfter X τ ω

/-- The next clamped excursion time is a stopping time. -/
theorem nextTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) :
    IsStoppingTime ℱ
      (fun ω => (nextTime X τ T ω : WithTop ℝ≥0)) := by
  have hHit : IsStoppingTime ℱ
      (absoluteStrictHittingAfter (displacementAfter X τ) 1) :=
    absoluteStrictHittingAfter_isStoppingTime
      (stronglyAdapted_displacementAfter hX hXRight hτ)
      (displacementAfter_rightContinuous X hXRight τ) 1
  simpa only [coe_nextTime] using hHit.min_const T

/-- Successive unit excursions of `X`, all clamped at `T`. -/
noncomputable def time
    (X : Process Ω) (T : ℝ≥0) : ℕ → Ω → ℝ≥0
  | 0 => fun _ => 0
  | n + 1 => nextTime X (time X T n) T

omit [MeasurableSpace Ω] in
@[simp]
theorem time_zero (X : Process Ω) (T : ℝ≥0) :
    time X T 0 = fun _ => 0 := rfl

omit [MeasurableSpace Ω] in
@[simp]
theorem time_succ (X : Process Ω) (T : ℝ≥0) (n : ℕ) :
    time X T (n + 1) = nextTime X (time X T n) T := rfl

omit [MeasurableSpace Ω] in
theorem time_le (X : Process Ω) (T : ℝ≥0) :
    ∀ n ω, time X T n ω ≤ T := by
  intro n
  induction n with
  | zero => exact fun _ => bot_le
  | succ n _ => exact nextTime_le X (time X T n) T

omit [MeasurableSpace Ω] in
theorem time_mono (X : Process Ω) (T : ℝ≥0) :
    ∀ n ω, time X T n ω ≤ time X T (n + 1) ω := by
  intro n ω
  exact le_nextTime X (time X T n) T (time_le X T n) ω

omit [MeasurableSpace Ω] in
/-- A sampled increment smaller than the unit passage level means that the
clamped next excursion time is exactly the horizon. -/
theorem time_succ_eq_horizon_of_abs_sub_lt_one
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) (ω : Ω)
    (hsmall :
      |X (time X T (n + 1) ω) ω - X (time X T n ω) ω| < 1) :
    time X T (n + 1) ω = T := by
  apply le_antisymm (time_le X T (n + 1) ω)
  apply le_of_not_gt
  intro hnext
  have hone := one_le_abs_displacementAfter_nextTime_of_lt
    X hXRight (time X T n) T ω (by simpa only [time_succ] using hnext)
  rw [← time_succ X T n] at hone
  rw [displacementAfter_eq_sub_of_ge X (time X T n)
    (time X T (n + 1) ω) ω (time_mono X T n ω)] at hone
  exact (not_le_of_gt hsmall) hone

omit [MeasurableSpace Ω] in
/-- The deterministic horizon is absorbing for the recursive excursion
clock. -/
theorem time_eq_horizon_of_le_of_eq
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) {n m : ℕ}
    (hnm : n ≤ m) (hn : time X T n ω = T) :
    time X T m ω = T := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa only [Nat.add_zero] using hn
  | succ k ih =>
      rw [Nat.add_succ, time_succ]
      exact nextTime_eq_of_tau_eq_horizon X (time X T (n + k)) T ω ih

/-- Every excursion time is an actual bounded stopping time. -/
theorem time_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) :
    ∀ n, IsStoppingTime ℱ
      (fun ω => (time X T n ω : WithTop ℝ≥0)) := by
  intro n
  induction n with
  | zero => simpa only [time_zero] using isStoppingTime_const ℱ 0
  | succ n hn =>
      simpa only [time_succ] using
        nextTime_isStoppingTime hX hXRight hn T

omit [MeasurableSpace Ω] in
/-- A jump envelope at one sample point controls the overshoot of one
clamped excursion at that point. -/
theorem abs_displacementAfter_nextTime_le_at
    (X : Process Ω) (hXLeft : ProcessHasLeftLimits X)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (J : Ω → ℝ)
    (ω : Ω) (hJ : 0 ≤ J ω)
    (hJump : ∀ t,
      |processLeftJump (displacementAfter X τ) t ω| ≤ J ω) :
    |displacementAfter X τ (nextTime X τ T ω) ω| ≤ 1 + J ω := by
  let σ := absoluteStrictHittingAfter (displacementAfter X τ) 1 ω
  by_cases hσT : σ ≤ (T : WithTop ℝ≥0)
  · have hσTop : σ ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hσT
    have hnext : nextTime X τ T ω = σ.untopA := by
      apply WithTop.coe_injective
      rw [coe_nextTime, min_eq_left hσT,
        WithTop.untopA_eq_untop hσTop, WithTop.coe_untop _ hσTop]
    rw [hnext]
    exact (abs_untopA_absoluteStrictHittingAfter_le_add_leftJump
      (displacementAfter X τ)
      (displacementAfter_hasLeftLimits hXLeft τ) 1 ω
      (by
        rw [displacementAfter_eq_zero_of_le X τ 0 ω bot_le,
          abs_zero]
        norm_num)
      hσTop).trans (add_le_add le_rfl (hJump σ.untopA))
  · have hTσ : (T : WithTop ℝ≥0) < σ := lt_of_not_ge hσT
    have hnext : nextTime X τ T ω = T := by
      apply WithTop.coe_injective
      rw [coe_nextTime, min_eq_right hTσ.le]
    rw [hnext]
    exact (abs_le_of_lt_absoluteStrictHittingAfter
      (displacementAfter X τ) 1 ω T hTσ).trans
        (le_add_of_nonneg_right hJ)

omit [MeasurableSpace Ω] in
/-- Pointwise version of the sampled-increment overshoot estimate. -/
theorem abs_time_succ_sub_time_le_at
    (X : Process Ω) (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hJ : 0 ≤ J n ω)
    (hJump : ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω) :
    |X (time X T (n + 1) ω) ω - X (time X T n ω) ω| ≤
      1 + J n ω := by
  have hmono := time_mono X T n ω
  rw [show X (time X T (n + 1) ω) ω - X (time X T n ω) ω =
      displacementAfter X (time X T n) (time X T (n + 1) ω) ω by
    symm
    exact displacementAfter_eq_sub_of_ge X (time X T n)
      (time X T (n + 1) ω) ω hmono]
  simpa only [time_succ] using
    abs_displacementAfter_nextTime_le_at X hXLeft (time X T n) T
      (J n) ω hJ hJump

end Lemma47ExcursionStopping

end FTAPTheorem42
