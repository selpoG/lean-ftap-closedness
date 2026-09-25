/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Process.CadlagLargeJumpEnumeration
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Foundations.RightContinuousProgressive

/-!
# The stochastic finite large-jump process

The deterministic finite-jump path from `CadlagLargeJumpPath` is made into a
process by using the chronological stopping-time enumeration.  The process is
defined as a countable sum of stopped jump coordinates; pathwise only
finitely many coordinates are nonzero, so the sum agrees exactly with the
finite path core.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteLargeJumpProcess

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## The coordinate process -/

noncomputable def pathData
    (X : Process Ω) (c : ℝ) (T : ℝ≥0)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (ω : Ω) :
    LargeJumpPathData (fun t => X t ω) c T :=
  largeJumpPathData (fun t => hRight ω t) (fun t => hLeft ω t) hc

private noncomputable abbrev jumpTime (X : Process Ω) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    Ω → WithTop ℝ≥0 :=
  CadlagLargeJumpEnumeration.largeJumpTimeEnumeration X c T n

private noncomputable def jumpCoordinate
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if jumpTime X c T n ω ≤ (t : WithTop ℝ≥0) then
    MeasureTheory.stoppedProcess (processLeftJump X)
      (jumpTime X c T n) t ω
  else 0

omit [MeasurableSpace Ω] in
private theorem jumpCoordinate_eq_zero_of_top
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ω : Ω)
    (h : jumpTime X c T n ω = ⊤) :
    jumpCoordinate X c T n t ω = 0 := by
  rw [jumpCoordinate, h]
  rw [ite_eq_right (not_le_of_gt (WithTop.coe_lt_top t))]

omit [MeasurableSpace Ω] in
private theorem jumpCoordinate_eq_jump_of_active
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {n : ℕ} {ω : Ω}
    {s : ℝ≥0}
    (hseq : jumpTime X c T n ω = (s : WithTop ℝ≥0))
    (hst : jumpTime X c T n ω ≤ (t : WithTop ℝ≥0)) :
    jumpCoordinate X c T n t ω = processLeftJump X s ω := by
  rw [jumpCoordinate, ite_eq_left hst]
  rw [MeasureTheory.stoppedProcess_eq_of_ge]
  · rw [hseq]
    rfl
  · exact hst

/-! The measurable finite-horizon coordinates are obtained from the stopped
process of the left-jump process.  In particular the branch with a top-valued
coordinate is zero and never asks for a value of `X` at `⊤`. -/

private theorem processLeftJump_isStronglyProgressive
    {X : Process Ω}
    (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) :
    IsStronglyProgressive ℱ (processLeftJump X) := by
  have hXprog : IsStronglyProgressive ℱ X :=
    FTAPTheorem42.StronglyAdapted.isStronglyProgressive_of_rightContinuous hX hRight
  have hleftPred : IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim (X · ω) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim hLeft hX
  have hleftProg : IsStronglyProgressive ℱ
      (fun t ω => Function.leftLim (X · ω) t) :=
    hleftPred.isStronglyProgressive
  have hsub := hXprog.sub hleftProg
  exact hsub

private theorem jumpCoordinate_stronglyAdapted
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted ℱ (jumpCoordinate X c T n) := by
  intro t
  have hτ : IsStoppingTime ℱ (jumpTime X c T n) :=
    CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_isStoppingTime
      hX hRight hLeft hc n
  have hJprog : IsStronglyProgressive ℱ (processLeftJump X) :=
    processLeftJump_isStronglyProgressive hX hRight hLeft
  have hstop : StronglyAdapted ℱ
      (MeasureTheory.stoppedProcess (processLeftJump X)
        (jumpTime X c T n)) :=
    hJprog.stronglyAdapted_stoppedProcess hτ
  have hset : MeasurableSet[ℱ t]
      {ω | jumpTime X c T n ω ≤ (t : WithTop ℝ≥0)} :=
    hτ.measurableSet_le t
  unfold jumpCoordinate
  exact StronglyMeasurable.ite hset (hstop t) stronglyMeasurable_const

/-! ## The countable sum and its pathwise finite support -/

noncomputable def process
    (X : Process Ω) (c : ℝ) (T : ℝ≥0) : Process Ω :=
  fun t ω => ∑' n : ℕ, jumpCoordinate X c T n t ω

theorem stronglyAdapted_process
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (T : ℝ≥0) :
    StronglyAdapted ℱ (process X c T) := by
  intro t
  unfold process
  apply @StronglyMeasurable.tsum Ω ℝ ℕ (ℱ t)
  intro n
  exact jumpCoordinate_stronglyAdapted hX hRight hLeft hc T n t

omit [MeasurableSpace Ω] in
private theorem process_eq_sum_range_of_eventually_top
    {X : Process Ω} {c : ℝ} {T : ℝ≥0} {t : ℝ≥0} {ω : Ω}
    {N : ℕ} (hN : ∀ n ≥ N, jumpTime X c T n ω = ⊤) :
    process X c T t ω = ∑ n ∈ Finset.range N, jumpCoordinate X c T n t ω := by
  unfold process
  rw [tsum_eq_sum (s := Finset.range N)]
  intro n hn
  exact jumpCoordinate_eq_zero_of_top X c T n t ω (hN n
    (Nat.le_of_not_gt (by simpa using hn)))

omit [MeasurableSpace Ω] in
private theorem process_eq_path_at
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    process X c T t ω =
      (pathData X c T hRight hLeft hc ω).path t := by
  let D := pathData X c T hRight hLeft hc ω
  obtain ⟨N, hN⟩ :=
    CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_eventually_top
      (X := X) (c := c) (T := T)
      hRight hLeft hc ω
  let I : Finset ℕ := (Finset.range N).filter
    (fun n => jumpTime X c T n ω ≠ ⊤)
  have hI_sub : I ⊆ Finset.range N := by
    exact Finset.filter_subset _ _
  have hcoord_zero : ∀ n ∈ Finset.range N, n ∉ I →
      jumpCoordinate X c T n t ω = 0 := by
    intro n hn hnot
    have htop : jumpTime X c T n ω = ⊤ := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
    exact jumpCoordinate_eq_zero_of_top X c T n t ω htop
  have hsum_filter :
      (∑ n ∈ I, jumpCoordinate X c T n t ω) =
        ∑ n ∈ Finset.range N, jumpCoordinate X c T n t ω := by
    exact Finset.sum_subset hI_sub hcoord_zero
  have hstrict_of_lt : ∀ {m n : ℕ}, m < n →
      jumpTime X c T n ω ≠ ⊤ →
      jumpTime X c T m ω < jumpTime X c T n ω := by
    intro m n hmn
    induction n with
    | zero => omega
    | succ n ih =>
        intro hn
        by_cases hmn_eq : m = n
        · subst m
          exact CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_succ_lt_of_ne_top
            (X := X) (c := c) (T := T)
            hRight hLeft hc ω n hn
        · have hmn' : m < n := by omega
          have hn' : jumpTime X c T n ω ≠ ⊤ := by
            intro htop
            have hle : jumpTime X c T n ω ≤
                jumpTime X c T (n + 1) ω :=
              (CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_monotone
                (X := X) (c := c) (T := T)
                hRight hLeft hc) ω
                (Nat.le_succ n)
            rw [htop] at hle
            exact hn (top_unique hle)
          exact (ih hmn' hn').trans
            (CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_succ_lt_of_ne_top
              (X := X) (c := c) (T := T)
              hRight hLeft hc ω n hn)
  have hmem_of_active (n : ℕ) (hn : n ∈ I) :
      ∃ s : ℝ≥0, s ∈ D.times ∧
        jumpTime X c T n ω = (s : WithTop ℝ≥0) := by
    have hne : jumpTime X c T n ω ≠ ⊤ :=
      (Finset.mem_filter.mp hn).2
    obtain ⟨s, hs, hseq⟩ :=
      CadlagLargeJumpEnumeration.largeJumpTimeEnumeration_mem_of_ne_top
        (X := X) (c := c) (T := T)
        hRight hLeft hc ω n hne
    exact ⟨s, (D.times_mem s).mpr hs, hseq⟩
  let i (n : ℕ) (hn : n ∈ I) : ℝ≥0 :=
    Classical.choose (hmem_of_active n hn)
  have hi_spec (n : ℕ) (hn : n ∈ I) :
      i n hn ∈ D.times ∧
        jumpTime X c T n ω = (i n hn : WithTop ℝ≥0) :=
    Classical.choose_spec (hmem_of_active n hn)
  have hi_inj : ∀ (m : ℕ) (hm : m ∈ I) (n : ℕ) (hn : n ∈ I),
      i m hm = i n hn → m = n := by
    intro m hm n hn heq
    have hmeq : jumpTime X c T m ω = jumpTime X c T n ω := by
      rw [(hi_spec m hm).2, (hi_spec n hn).2, heq]
    by_cases hmn_eq : m = n
    · exact hmn_eq
    · rcases lt_or_gt_of_ne hmn_eq with hmn | hnm
      · have hlt := hstrict_of_lt hmn (by
          intro htop
          have htop' := (hi_spec n hn).2
          rw [htop] at htop'
          exact (WithTop.coe_ne_top :
            (i n hn : WithTop ℝ≥0) ≠ ⊤) htop'.symm)
        exact False.elim ((ne_of_lt hlt) hmeq)
      · have hlt := hstrict_of_lt hnm (by
          intro htop
          have htop' := (hi_spec m hm).2
          rw [htop] at htop'
          exact (WithTop.coe_ne_top :
            (i m hm : WithTop ℝ≥0) ≠ ⊤) htop'.symm)
        exact False.elim ((ne_of_gt hlt) hmeq)
  have hi_surj : ∀ s ∈ D.times, ∃ n, ∃ hn : n ∈ I, i n hn = s := by
    intro s hs
    have hslarge : s ∈ largeJumpTimeSet (fun u => X u ω) c T :=
      (D.times_mem s).mp hs
    obtain ⟨n, hseq⟩ :=
      CadlagLargeJumpEnumeration.mem_range_largeJumpTimeEnumeration
        (X := X) (c := c) (T := T)
        hRight hLeft hc ω hslarge
    have hnlt : n < N := by
      by_contra hnN
      have hnge : n ≥ N := Nat.le_of_not_gt hnN
      have htop := hN n hnge
      exact (WithTop.coe_ne_top : (s : WithTop ℝ≥0) ≠ ⊤)
        (hseq.symm.trans htop)
    have hnI : n ∈ I := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hnlt, ?_⟩
      intro htop
      exact (WithTop.coe_ne_top : (s : WithTop ℝ≥0) ≠ ⊤)
        (hseq.symm.trans htop)
    refine ⟨n, hnI, ?_⟩
    have hchosen := (hi_spec n hnI).2
    exact_mod_cast (hchosen.symm.trans hseq)
  have hsum_active :
      (∑ n ∈ I, jumpCoordinate X c T n t ω) =
        ∑ s ∈ D.times, if s ≤ t then D.jump s else 0 := by
    apply Finset.sum_bij i
    · intro n hn
      exact (hi_spec n hn).1
    · intro m hm n hn heq
      exact hi_inj m hm n hn heq
    · intro s hs
      obtain ⟨n, hn, hns⟩ := hi_surj s hs
      exact ⟨n, hn, hns⟩
    · intro n hn
      have hseq := (hi_spec n hn).2
      by_cases hnt : jumpTime X c T n ω ≤ (t : WithTop ℝ≥0)
      · have hsle : i n hn ≤ t := by
          exact WithTop.coe_le_coe.mp (hseq ▸ hnt)
        rw [jumpCoordinate_eq_jump_of_active hseq hnt]
        simp [hsle, LargeJumpPathData.jump, processLeftJump, cadlagLeftJump]
      · have hsnot : ¬i n hn ≤ t := by
          intro hsle
          apply hnt
          simpa [hseq] using (WithTop.coe_le_coe.mpr hsle)
        rw [jumpCoordinate, ite_eq_right hnt]
        simp [hsnot]
  have hpath : D.path t = ∑ s ∈ D.times, if s ≤ t then D.jump s else 0 := by
    rfl
  rw [show process X c T t ω =
      ∑ n ∈ Finset.range N, jumpCoordinate X c T n t ω by
        exact process_eq_sum_range_of_eventually_top hN]
  rw [← hsum_filter, hsum_active, hpath]

omit [MeasurableSpace Ω] in
theorem process_eq_path
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    process X c T =
      fun t ω => (pathData X c T hRight hLeft hc ω).path t := by
  funext t ω
  exact process_eq_path_at hRight hLeft hc

/-! ## Path regularity and jump identities -/

omit [MeasurableSpace Ω] in
theorem process_zero
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    process X c T 0 = 0 := by
  rw [process_eq_path hRight hLeft hc]
  funext ω
  exact (pathData X c T hRight hLeft hc ω).path_zero

omit [MeasurableSpace Ω] in
theorem process_rightContinuous
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ ω t, ContinuousWithinAt ((process X c T) · ω) (Ici t) t := by
  intro ω t
  rw [process_eq_path hRight hLeft hc]
  exact (pathData X c T hRight hLeft hc ω).path_continuousWithinAt t

omit [MeasurableSpace Ω] in
theorem process_hasLeftLimits
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ProcessHasLeftLimits (process X c T) := by
  intro ω t
  rw [process_eq_path hRight hLeft hc]
  exact (pathData X c T hRight hLeft hc ω).path_hasLeftLimits t

omit [MeasurableSpace Ω] in
theorem process_boundedVariationOn_univ
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ ω, BoundedVariationOn ((process X c T) · ω) Set.univ := by
  intro ω
  rw [process_eq_path hRight hLeft hc]
  exact (pathData X c T hRight hLeft hc ω).path_boundedVariationOn_univ

omit [MeasurableSpace Ω] in
theorem process_locallyBoundedVariationOn
    {X : Process Ω} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ ω, LocallyBoundedVariationOn ((process X c T) · ω) Set.univ := by
  intro ω
  rw [process_eq_path hRight hLeft hc]
  exact (pathData X c T hRight hLeft hc ω).path_locallyBoundedVariationOn

omit [MeasurableSpace Ω] in
private theorem process_leftJump_eq_path
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    processLeftJump (process X c T) t ω =
      (pathData X c T hRight hLeft hc ω).path t -
        Function.leftLim (pathData X c T hRight hLeft hc ω).path t := by
  have hpath : (fun s => process X c T s ω) =
      (pathData X c T hRight hLeft hc ω).path := by
    funext s
    exact congrFun (congrFun (process_eq_path hRight hLeft hc) s) ω
  unfold processLeftJump
  rw [show process X c T t ω =
      (pathData X c T hRight hLeft hc ω).path t by
        exact congrFun hpath t,
    hpath, (pathData X c T hRight hLeft hc ω).path_leftLim_eq]

omit [MeasurableSpace Ω] in
theorem process_leftJump_eq_of_large
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (ht : t ∈ largeJumpTimeSet (fun s => X s ω) c T) :
    processLeftJump (process X c T) t ω = processLeftJump X t ω := by
  rw [process_leftJump_eq_path hRight hLeft hc]
  calc
    (pathData X c T hRight hLeft hc ω).path t -
        Function.leftLim (pathData X c T hRight hLeft hc ω).path t =
        cadlagLeftJump (fun s => X s ω) t :=
      (pathData X c T hRight hLeft hc ω).path_leftJump_eq_of_large ht
    _ = processLeftJump X t ω := by rfl

omit [MeasurableSpace Ω] in
theorem process_leftJump_eq_of_not_large
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    (ht : t ∉ largeJumpTimeSet (fun s => X s ω) c T) :
    processLeftJump (process X c T) t ω = 0 := by
  rw [process_leftJump_eq_path hRight hLeft hc]
  calc
    (pathData X c T hRight hLeft hc ω).path t -
        Function.leftLim (pathData X c T hRight hLeft hc ω).path t = 0 :=
      (pathData X c T hRight hLeft hc ω).path_leftJump_eq_of_not_large ht
    _ = 0 := rfl

omit [MeasurableSpace Ω] in
theorem process_eq_horizon_of_le
    {X : Process Ω} {c : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (hTt : T ≤ t) :
    process X c T t ω = process X c T T ω := by
  rw [process_eq_path hRight hLeft hc]
  let D := pathData X c T hRight hLeft hc ω
  apply Finset.sum_congr rfl
  intro s hs
  have hsT : s ≤ T := ((D.times_mem s).mp ((show D =
      pathData X c T hRight hLeft hc ω from rfl) ▸ hs)).1.2
  simp [hsT, hsT.trans hTt]

end FiniteLargeJumpProcess

end FTAPTheorem42
