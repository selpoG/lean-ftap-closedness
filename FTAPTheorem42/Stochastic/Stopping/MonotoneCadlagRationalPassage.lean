/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.RightContinuousHittingTime
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Rational passages of monotone càdlàg paths

This module contains the pathwise and stopping-time part of the rational
passage argument.  It is deliberately independent of any particular
semimartingale or finite-variation carrier.  A nonnegative monotone process
with right-continuous paths has every nonzero left jump represented by a
strict passage through one of a fixed countable family of positive rational
levels.  The passage is clamped at a deterministic horizon, so it is a finite
stopping time.

The process-level identification of a predictable version with a càdlàg
version is not part of this module.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace MonotoneCadlagRationalPassage

/-! ## A fixed countable family of positive levels -/

/-- A fixed enumeration of the positive rational numbers, embedded in the
reals.  The default value is positive, so every level is strictly positive. -/
noncomputable def positiveRationalLevel (n : ℕ) : ℝ :=
  (((Encodable.decode n).getD
    (⟨1, by norm_num⟩ : {q : ℚ // 0 < q})).1 : ℚ)

theorem positiveRationalLevel_pos (n : ℕ) :
    0 < positiveRationalLevel n := by
  let q : {q : ℚ // 0 < q} :=
    (Encodable.decode n).getD ⟨1, by norm_num⟩
  change 0 < (q.1 : ℝ)
  exact_mod_cast q.2

theorem exists_positiveRationalLevel_eq (q : ℚ) (hq : 0 < q) :
    ∃ n, positiveRationalLevel n = (q : ℝ) :=
  ⟨Encodable.encode (⟨q, hq⟩ : {q : ℚ // 0 < q}), by
    simp [positiveRationalLevel]⟩

/-! ## Strict passage and its elementary pathwise properties -/

omit [MeasurableSpace Ω] in
/-- If all values strictly before `t` lie below `l`, while the value at `t`
lies above `c > l`, then the first strict upper-level passage is `t`. -/
theorem strictHittingAfter_eq_of_forall_lt_le
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) {t : ℝ≥0} {l c : ℝ}
    (hbefore : ∀ s, s < t → X s ω ≤ l) (hlc : l < c)
    (hct : c < X t ω) :
    RightContinuousHittingTime.strictHittingAfter X c ω = t := by
  rw [RightContinuousHittingTime.strictHittingAfter,
    MeasureTheory.hittingAfter]
  rw [ite_eq_left ⟨t, bot_le, hct⟩]
  norm_cast
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun s hs => hs.1⟩
    · exact ⟨bot_le, hct⟩
  · apply le_csInf
    · exact ⟨t, bot_le, hct⟩
    · intro s hs
      by_contra hts
      have hst : s < t := lt_of_not_ge hts
      exact (not_lt_of_ge (hbefore s hst)) (hlc.trans hs.2)

/-! ## Finite clamped passages -/

/-- The first strict passage through `c`, clamped at the deterministic time
`T`.  The result is a finite nonnegative time. -/
noncomputable def clampedStrictPassage
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (c : ℝ) : Ω → ℝ≥0 :=
  fun ω =>
    (min (RightContinuousHittingTime.strictHittingAfter X c ω)
      (T : WithTop ℝ≥0)).untopA

omit [MeasurableSpace Ω] in
/-- Clamping makes the passage no later than the deterministic horizon. -/
theorem clampedStrictPassage_le
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (c : ℝ) (ω : Ω) :
    clampedStrictPassage X T c ω ≤ T := by
  have hne : min
      (RightContinuousHittingTime.strictHittingAfter X c ω)
      (T : WithTop ℝ≥0) ≠ ⊤ := by
    exact ne_of_lt ((min_le_right _ _).trans_lt (WithTop.coe_lt_top T))
  unfold clampedStrictPassage
  rw [WithTop.untopA_eq_untop hne]
  apply WithTop.coe_le_coe.mp
  rw [WithTop.coe_untop _ hne]
  exact min_le_right _ _

theorem clampedStrictPassage_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (c : ℝ) :
    IsStoppingTime ℱ
      (fun ω => (clampedStrictPassage X T c ω : WithTop ℝ≥0)) := by
  have hσ :=
    (RightContinuousHittingTime.strictHittingAfter_isStoppingTime
      hX hRight c).min (isStoppingTime_const ℱ T)
  convert hσ using 1
  funext ω
  have hne : min
      (RightContinuousHittingTime.strictHittingAfter X c ω)
      (T : WithTop ℝ≥0) ≠ ⊤ := by
    exact ne_of_lt ((min_le_right _ _).trans_lt (WithTop.coe_lt_top T))
  rw [clampedStrictPassage, WithTop.untopA_eq_untop hne,
    WithTop.coe_untop _ hne]

/-! ## Monotone paths and their jumps -/

omit [MeasurableSpace Ω] in
/-- At a point where the left jump vanishes, right continuity and existence
of the left limit give continuity. -/
theorem continuousAt_of_rightContinuous_of_leftLimit_of_processLeftJump_eq_zero
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hRight : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hLeft : ∀ s,
      Tendsto f (nhdsWithin s (Set.Iio s))
        (nhds (Function.leftLim f s)))
    (hJump : f t - Function.leftLim f t = 0) :
    ContinuousAt f t := by
  apply continuousAt_iff_continuous_left'_right'.2
  constructor
  · have hLeftEq : Function.leftLim f t = f t := by
      linarith [hJump]
    change Tendsto f (nhdsWithin t (Set.Iio t)) (nhds (f t))
    rw [← hLeftEq]
    exact hLeft t
  · exact (hRight t).mono Ioi_subset_Ici_self

/-! ## Rational jump cover -/

omit [MeasurableSpace Ω] in
/-- Every nonzero left jump of a nonnegative monotone path before `T` is
exactly a clamped strict passage through one positive rational level. -/
theorem exists_clampedStrictPassage_eq_of_processLeftJump_ne_zero
    (X : ℝ≥0 → Ω → ℝ)
    (hNonnegative : ∀ ω t, 0 ≤ X t ω)
    (hMonotone : ∀ ω, Monotone (X · ω))
    {T : ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (htT : t ≤ T)
    (hjump : processLeftJump X t ω ≠ 0) :
    ∃ n, clampedStrictPassage X T (positiveRationalLevel n) ω = t := by
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    have hleft : Function.leftLim (fun s => X s ω) (0 : ℝ≥0) = X 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    exact hjump (by simp [processLeftJump, hleft])
  let f : ℝ≥0 → ℝ := fun s => X s ω
  have hmono : Monotone f := hMonotone ω
  have hleft_le : Function.leftLim f t ≤ f t := by
    exact hmono.leftLim_le le_rfl
  have hleft_ne : Function.leftLim f t ≠ f t := by
    intro hEq
    apply hjump
    simp only [processLeftJump, f, hEq, sub_self]
  have hleft_lt : Function.leftLim f t < f t :=
    lt_of_le_of_ne hleft_le hleft_ne
  have hleft_nonnegative : 0 ≤ Function.leftLim f t := by
    exact (hNonnegative ω 0).trans
      (hmono.le_leftLim ((pos_iff_ne_zero).2 ht0))
  obtain ⟨q, hleft_q, hq_right⟩ := exists_rat_btwn hleft_lt
  have hq_pos : 0 < q := by
    exact_mod_cast hleft_nonnegative.trans_lt hleft_q
  obtain ⟨n, hn⟩ := exists_positiveRationalLevel_eq q hq_pos
  have hbefore : ∀ s, s < t → X s ω ≤ Function.leftLim f t := by
    intro s hst
    exact hmono.le_leftLim hst
  have hpassage :
      RightContinuousHittingTime.strictHittingAfter X
        (positiveRationalLevel n) ω = t := by
    apply strictHittingAfter_eq_of_forall_lt_le X ω hbefore
    · rw [hn]
      exact hleft_q
    · rw [hn]
      exact hq_right
  refine ⟨n, ?_⟩
  unfold clampedStrictPassage
  rw [hpassage, min_eq_left]
  · rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    exact WithTop.untop_coe t
  · exact_mod_cast htT

end MonotoneCadlagRationalPassage

end FTAPTheorem42
