/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Passage
import FTAPTheorem42.Foundations.RightContinuousHittingTime
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStoppingCalculus
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# The first rescale-and-stop step of Lemma 4.7

The Delbaen--Schachermayer argument stops when either the martingale part or
the whole gain first exceeds its prescribed level.  This module constructs
that stopping time and the corresponding rescaled strategy in the general
stochastic-integrable class.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Strictly before the absolute-value passage, the process remains below
the passage level. -/
theorem abs_le_of_lt_absoluteStrictHittingAfter
    (X : Process Ω) (r : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < absoluteStrictHittingAfter X r ω) :
    |X t ω| ≤ r := by
  have hnot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := fun t ω => |X t ω|) (s := Set.Ioi r) (n := (0 : ℝ≥0))
    (ω := ω) (k := t) ht bot_le
  exact le_of_not_gt hnot

omit [MeasurableSpace Ω] in
/-- At a finite strict absolute-value passage, right continuity forces the
value at the passage time to belong to the closure of the strict upper ray.
In particular, it is at least the passage level. -/
theorem le_abs_untopA_absoluteStrictHittingAfter
    (X : Process Ω)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (r : ℝ) (ω : Ω)
    (hτ : absoluteStrictHittingAfter X r ω ≠ ⊤) :
    r ≤ |X ((absoluteStrictHittingAfter X r ω).untopA) ω| := by
  let A : Set ℝ≥0 := {t | (0 : ℝ≥0) ≤ t ∧ r < |X t ω|}
  have hA : A.Nonempty := by
    simp only [ne_eq, absoluteStrictHittingAfter,
      RightContinuousHittingTime.strictHittingAfter,
      MeasureTheory.hittingAfter_eq_top_iff, not_forall, not_not] at hτ
    obtain ⟨t, _, ht⟩ := hτ
    exact ⟨t, bot_le, ht⟩
  have hHit :
      (absoluteStrictHittingAfter X r ω).untopA = sInf A := by
    have hExists : ∃ j, (0 : ℝ≥0) ≤ j ∧ |X j ω| ∈ Set.Ioi r := by
      obtain ⟨j, hj⟩ := hA
      exact ⟨j, hj.1, hj.2⟩
    unfold absoluteStrictHittingAfter
      RightContinuousHittingTime.strictHittingAfter
    rw [MeasureTheory.hittingAfter_def]
    dsimp only
    rw [ite_eq_left hExists]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
    rfl
  have hBelow : BddBelow A := by
    exact ⟨0, fun _ ht => ht.1⟩
  let τ := (absoluteStrictHittingAfter X r ω).untopA
  have hτClosure : τ ∈ closure A := by
    dsimp only [τ]
    rw [hHit]
    exact csInf_mem_closure hA hBelow
  have hAτ : A ⊆ Set.Ici τ := by
    intro t ht
    dsimp only [τ]
    rw [hHit]
    exact csInf_le hBelow ht
  have hValueClosure : |X τ ω| ∈ closure (Set.Ioi r) :=
    ((hRight ω τ).abs.mono hAτ).mem_closure hτClosure
      (fun _ ht => ht.2)
  simpa only [closure_Ioi, Set.mem_Ici] using hValueClosure

omit [MeasurableSpace Ω] in
/-- At a finite absolute-value passage time, overshoot beyond the level is
bounded by the left jump.  The initial-value assumption handles a passage at
time zero. -/
theorem abs_untopA_absoluteStrictHittingAfter_le_add_leftJump
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r : ℝ) (ω : Ω) (hInitial : |X 0 ω| ≤ r)
    (hτ : absoluteStrictHittingAfter X r ω ≠ ⊤) :
    |X ((absoluteStrictHittingAfter X r ω).untopA) ω| ≤
      r + |processLeftJump X
        ((absoluteStrictHittingAfter X r ω).untopA) ω| := by
  let τ := (absoluteStrictHittingAfter X r ω).untopA
  have hτcoe : (τ : WithTop ℝ≥0) = absoluteStrictHittingAfter X r ω := by
    dsimp only [τ]
    rw [WithTop.untopA_eq_untop hτ]
    exact WithTop.coe_untop _ hτ
  change |X τ ω| ≤ r + |processLeftJump X τ ω|
  by_cases hτ0 : τ = 0
  · rw [hτ0]
    have hleft : Function.leftLim (fun s => X s ω) 0 = X 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    simpa only [processLeftJump, hleft, sub_self, abs_zero, add_zero]
      using hInitial
  · have hτpos : (0 : ℝ≥0) < τ := (pos_iff_ne_zero).2 hτ0
    let : NeBot (𝓝[<] τ) := nhdsLT_neBot_of_exists_lt ⟨0, hτpos⟩
    have hLeftBound :
        |Function.leftLim (fun s => X s ω) τ| ≤ r := by
      apply le_of_tendsto (hLeft ω τ).abs
      filter_upwards [self_mem_nhdsWithin] with s hs
      apply abs_le_of_lt_absoluteStrictHittingAfter X r ω s
      rw [← hτcoe]
      exact WithTop.coe_lt_coe.mpr hs
    calc
      |X τ ω| =
          |(X τ ω - Function.leftLim (fun s => X s ω) τ) +
            Function.leftLim (fun s => X s ω) τ| := by ring_nf
      _ ≤ |X τ ω - Function.leftLim (fun s => X s ω) τ| +
          |Function.leftLim (fun s => X s ω) τ| := abs_add_le _ _
      _ ≤ |processLeftJump X τ ω| + r :=
        by
          rw [processLeftJump]
          gcongr
      _ = r + |processLeftJump X τ ω| := add_comm _ _

omit [MeasurableSpace Ω] in
/-- Stopping no later than an absolute first passage gives a uniform path
bound by the level plus a bound on left jumps. -/
theorem abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting
    (X : Process Ω) (hLeft : ProcessHasLeftLimits X)
    (r J : ℝ) (hJ : 0 ≤ J) (ω : Ω)
    (hInitial : |X 0 ω| ≤ r)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : σ ω ≤ absoluteStrictHittingAfter X r ω)
    (hJump : ∀ t, |processLeftJump X t ω| ≤ J) :
    ∀ t, |MeasureTheory.stoppedProcess X σ t ω| ≤ r + J := by
  intro t
  let u := RightContinuousStoppedMartingale.boundedTime t σ ω
  rw [← RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess]
  change |X u ω| ≤ r + J
  have huHit : (u : WithTop ℝ≥0) ≤ absoluteStrictHittingAfter X r ω := by
    rw [RightContinuousStoppedMartingale.coe_boundedTime]
    exact (min_le_right _ _).trans hσ
  rcases huHit.eq_or_lt with huEq | huLt
  · have hHitNe : absoluteStrictHittingAfter X r ω ≠ ⊤ := by
      rw [← huEq]
      exact WithTop.coe_ne_top
    have hUntop :
        (absoluteStrictHittingAfter X r ω).untopA = u := by
      rw [WithTop.untopA_eq_untop hHitNe]
      apply WithTop.coe_injective
      rw [WithTop.coe_untop _ hHitNe]
      exact huEq.symm
    have hAt := abs_untopA_absoluteStrictHittingAfter_le_add_leftJump
      X hLeft r ω hInitial hHitNe
    rw [hUntop] at hAt
    apply hAt.trans
    gcongr
    exact hJump u
  · exact (abs_le_of_lt_absoluteStrictHittingAfter X r ω u huLt).trans
      (le_add_of_nonneg_right hJ)

theorem absoluteStrictHittingAfter_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (r : ℝ) :
    IsStoppingTime ℱ (absoluteStrictHittingAfter X r) := by
  apply RightContinuousHittingTime.strictHittingAfter_isStoppingTime
  · intro t
    simpa only [Real.norm_eq_abs] using (hX t).norm
  · exact fun ω t => (hXRight ω t).abs

/-- Stop when either `|H·M|` exceeds `martingaleLevel` or `|H·S|` exceeds
`gainLevel`. -/
noncomputable def lemma47FirstPassage
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D)
    (martingaleLevel gainLevel : ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => min
    (absoluteStrictHittingAfter H.martingalePart martingaleLevel ω)
    (absoluteStrictHittingAfter H.stochasticIntegral gainLevel ω)

theorem lemma47FirstPassage_isStoppingTime
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D)
    (martingaleLevel gainLevel : ℝ) :
    IsStoppingTime ℱ
      (lemma47FirstPassage H martingaleLevel gainLevel) := by
  exact (absoluteStrictHittingAfter_isStoppingTime H.martingalePart_isStronglyAdapted
      H.martingalePart_isRightContinuous martingaleLevel).min
    (absoluteStrictHittingAfter_isStoppingTime H.stochasticIntegral_isStronglyAdapted
      H.stochasticIntegral_isRightContinuous gainLevel)

end FTAPTheorem42
