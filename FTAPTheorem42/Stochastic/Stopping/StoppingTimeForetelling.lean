/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable

/-!
# Announcements of finite stopping times

The standard structure imposes no range restriction.  A compatibility
structure additionally records countable range for older discrete optional-
sampling consumers.  Neither structure asserts existence for an arbitrary
stopping time; providers must construct an announcement for the predictable
graph under consideration.
-/

namespace FTAPTheorem42

open Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An increasing sequence of finite stopping times strictly below `τ` and
converging pointwise to `τ`.  No range restriction is imposed; this is the
standard announcement notion used by the graph characterization of
predictable stopping times. -/
structure StoppingTimeAnnouncement
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) where
  time : ℕ → Ω → ℝ≥0
  isStoppingTime : ∀ n, IsStoppingTime ℱ
    (fun ω => (time n ω : WithTop ℝ≥0))
  monotone : ∀ ω, Monotone fun n => time n ω
  lt : ∀ n ω, time n ω < τ ω
  tendsto : ∀ ω, Tendsto (fun n => time n ω) atTop (𝓝 (τ ω))

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Foretelling possibly infinite stopping times

The predictable-section argument uses auxiliary stopping times which may be
zero or infinite.  `StoppingTimeForetelling` is the standard announcing
notion for that setting: strictness is required exactly on the event where
the target is nonzero.  A strictly positive finite target can subsequently
be converted to `StoppingTimeAnnouncement`.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A monotone sequence of stopping times which foretells a possibly
infinite stopping time.  At time zero the approximants are allowed to equal
the target; away from zero they are strictly smaller. -/
structure StoppingTimeForetelling
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → WithTop ℝ≥0) where
  time : ℕ → Ω → WithTop ℝ≥0
  isStoppingTime : ∀ n, IsStoppingTime ℱ (time n)
  monotone : ∀ ω, Monotone fun n => time n ω
  le : ∀ n ω, time n ω ≤ τ ω
  lt_of_ne_zero : ∀ n ω, τ ω ≠ 0 → time n ω < τ ω
  tendsto : ∀ ω, Tendsto (fun n => time n ω) atTop (𝓝 (τ ω))

namespace StoppingTimeForetelling

/-- Running maxima of strict left factorial approximations. -/
noncomputable def runningLeftApprox : ℕ → ℝ≥0 → ℝ≥0
  | 0, t => LeftContinuousPredictable.approx 0 t
  | n + 1, t => max (runningLeftApprox n t)
      (LeftContinuousPredictable.approx (n + 1) t)

omit [MeasurableSpace Ω] in
theorem runningLeftApprox_le (n : ℕ) (t : ℝ≥0) :
    runningLeftApprox n t ≤ t := by
  induction n with
  | zero => exact LeftContinuousPredictable.approx_le 0 t
  | succ n ih =>
      exact max_le ih (LeftContinuousPredictable.approx_le (n + 1) t)

omit [MeasurableSpace Ω] in
theorem runningLeftApprox_lt {t : ℝ≥0} (ht : t ≠ 0) (n : ℕ) :
    runningLeftApprox n t < t := by
  induction n with
  | zero => exact LeftContinuousPredictable.approx_lt ht 0
  | succ n ih =>
      exact max_lt ih (LeftContinuousPredictable.approx_lt ht (n + 1))

omit [MeasurableSpace Ω] in
theorem runningLeftApprox_mono (t : ℝ≥0) :
    Monotone fun n => runningLeftApprox n t := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

omit [MeasurableSpace Ω] in
theorem approx_le_runningLeftApprox (n : ℕ) (t : ℝ≥0) :
    LeftContinuousPredictable.approx n t ≤ runningLeftApprox n t := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

omit [MeasurableSpace Ω] in
theorem tendsto_runningLeftApprox (t : ℝ≥0) :
    Tendsto (fun n => runningLeftApprox n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (LeftContinuousPredictable.tendsto_approx t) tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun n =>
      approx_le_runningLeftApprox n t
  · exact Filter.Eventually.of_forall fun n => runningLeftApprox_le n t

/-- Canonical deterministic approximation of an element of
`WithTop ℝ≥0`. -/
noncomputable def constApprox (n : ℕ) (t : WithTop ℝ≥0) : WithTop ℝ≥0 :=
  t.recTopCoe ((n : ℝ≥0) : WithTop ℝ≥0)
    (fun s => (runningLeftApprox n s : WithTop ℝ≥0))

omit [MeasurableSpace Ω] in
theorem constApprox_mono (t : WithTop ℝ≥0) :
    Monotone fun n => constApprox n t := by
  induction t using WithTop.recTopCoe with
  | top =>
      intro n k hnk
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hnk)
  | coe t =>
      intro n k hnk
      exact WithTop.coe_le_coe.mpr (runningLeftApprox_mono t hnk)

omit [MeasurableSpace Ω] in
theorem constApprox_le (n : ℕ) (t : WithTop ℝ≥0) :
    constApprox n t ≤ t := by
  induction t using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
      exact WithTop.coe_le_coe.mpr (runningLeftApprox_le n t)

omit [MeasurableSpace Ω] in
theorem constApprox_lt_of_ne_zero (n : ℕ) {t : WithTop ℝ≥0}
    (ht : t ≠ 0) : constApprox n t < t := by
  induction t using WithTop.recTopCoe with
  | top => exact WithTop.coe_lt_top _
  | coe t =>
      apply WithTop.coe_lt_coe.mpr
      apply runningLeftApprox_lt
      intro ht0
      apply ht
      simp only [ht0, WithTop.coe_zero]

omit [MeasurableSpace Ω] in
theorem tendsto_constApprox (t : WithTop ℝ≥0) :
    Tendsto (fun n => constApprox n t) atTop (𝓝 t) := by
  induction t using WithTop.recTopCoe with
  | top =>
      exact WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  | coe t =>
      exact WithTop.continuous_coe.continuousAt.tendsto.comp
        (tendsto_runningLeftApprox t)

/-- Every deterministic time, including zero and infinity, is foretold. -/
noncomputable def const
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (t : WithTop ℝ≥0) :
    StoppingTimeForetelling ℱ (fun _ => t) where
  time := fun n _ => constApprox n t
  isStoppingTime := fun n i => by
    by_cases h : constApprox n t ≤ (i : WithTop ℝ≥0)
    · have heq : {ω : Ω | constApprox n t ≤ (i : WithTop ℝ≥0)} =
          Set.univ := Set.eq_univ_of_forall fun _ => h
      rw [heq]
      exact @MeasurableSet.univ Ω (ℱ i)
    · have heq : {ω : Ω | constApprox n t ≤ (i : WithTop ℝ≥0)} =
          ∅ := Set.eq_empty_iff_forall_notMem.2 fun _ => h
      rw [heq]
      exact @MeasurableSet.empty Ω (ℱ i)
  monotone := fun _ => constApprox_mono t
  le := fun n _ => constApprox_le n t
  lt_of_ne_zero := fun n _ ht => constApprox_lt_of_ne_zero n ht
  tendsto := fun _ => tendsto_constApprox t

/-- The maximum of two foretold stopping times is foretold. -/
noncomputable def max
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ)
    (b : StoppingTimeForetelling ℱ τ) :
    StoppingTimeForetelling ℱ (fun ω => Max.max (σ ω) (τ ω)) where
  time := fun n ω => Max.max (a.time n ω) (b.time n ω)
  isStoppingTime := fun n => (a.isStoppingTime n).max (b.isStoppingTime n)
  monotone := fun ω _ _ h =>
    max_le_max (a.monotone ω h) (b.monotone ω h)
  le := fun n ω => max_le
    ((a.le n ω).trans (le_max_left _ _))
    ((b.le n ω).trans (le_max_right _ _))
  lt_of_ne_zero := fun n ω htarget => by
    have htargetPos : 0 < Max.max (σ ω) (τ ω) :=
      pos_iff_ne_zero.mpr htarget
    have haLt : a.time n ω < Max.max (σ ω) (τ ω) := by
      by_cases hσ : σ ω = 0
      · exact (a.le n ω).trans_lt (hσ ▸ htargetPos)
      · exact (a.lt_of_ne_zero n ω hσ).trans_le (le_max_left _ _)
    have hbLt : b.time n ω < Max.max (σ ω) (τ ω) := by
      by_cases hτ : τ ω = 0
      · exact (b.le n ω).trans_lt (hτ ▸ htargetPos)
      · exact (b.lt_of_ne_zero n ω hτ).trans_le (le_max_right _ _)
    exact max_lt haLt hbLt
  tendsto := fun ω => (a.tendsto ω).max (b.tendsto ω)

/-- The minimum of two foretold stopping times is foretold. -/
noncomputable def min
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ)
    (b : StoppingTimeForetelling ℱ τ) :
    StoppingTimeForetelling ℱ (fun ω => Min.min (σ ω) (τ ω)) where
  time := fun n ω => Min.min (a.time n ω) (b.time n ω)
  isStoppingTime := fun n => (a.isStoppingTime n).min (b.isStoppingTime n)
  monotone := fun ω _ _ h =>
    min_le_min (a.monotone ω h) (b.monotone ω h)
  le := fun n ω => min_le_min (a.le n ω) (b.le n ω)
  lt_of_ne_zero := fun n ω htarget => by
    have hσ : σ ω ≠ 0 := by
      intro h
      apply htarget
      rw [h]
      exact min_eq_left bot_le
    have hτ : τ ω ≠ 0 := by
      intro h
      apply htarget
      rw [h]
      exact min_eq_right bot_le
    exact min_lt_min (a.lt_of_ne_zero n ω hσ)
      (b.lt_of_ne_zero n ω hτ)
  tendsto := fun ω => (a.tendsto ω).min (b.tendsto ω)

/-- Running pointwise minima of a sequence of extended random times. -/
def runningMinTarget (τ : ℕ → Ω → WithTop ℝ≥0) :
    ℕ → Ω → WithTop ℝ≥0
  | 0 => τ 0
  | n + 1 => fun ω => Min.min (runningMinTarget τ n ω) (τ (n + 1) ω)

/-- Every finite running minimum of foretold times is foretold. -/
noncomputable def runningMin
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (a : ∀ n, StoppingTimeForetelling ℱ (τ n)) :
    ∀ n, StoppingTimeForetelling ℱ (runningMinTarget τ n)
  | 0 => a 0
  | n + 1 => (runningMin a n).min (a (n + 1))

/-- A foretelling of a strictly positive finite target is an ordinary
stopping-time announcement. -/
noncomputable def toStoppingTimeAnnouncement
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → ℝ≥0}
    (a : StoppingTimeForetelling ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτpos : ∀ ω, 0 < τ ω) : StoppingTimeAnnouncement ℱ τ := by
  let htarget : ∀ ω, (τ ω : WithTop ℝ≥0) ≠ 0 := fun ω => by
    exact_mod_cast (ne_of_gt (hτpos ω))
  let hfinite : ∀ n ω, a.time n ω ≠ ⊤ := fun n ω =>
    ne_top_of_lt (a.lt_of_ne_zero n ω (htarget ω))
  let σ : ℕ → Ω → ℝ≥0 := fun n ω =>
    (a.time n ω).untop (hfinite n ω)
  have hcoe : ∀ n ω, (σ n ω : WithTop ℝ≥0) = a.time n ω :=
    fun n ω => WithTop.coe_untop _ (hfinite n ω)
  refine
    { time := σ
      isStoppingTime := ?_
      monotone := ?_
      lt := ?_
      tendsto := ?_ }
  · intro n
    have heq : (fun ω => (σ n ω : WithTop ℝ≥0)) = a.time n := by
      funext ω
      exact hcoe n ω
    rw [heq]
    exact a.isStoppingTime n
  · intro ω n k hnk
    apply WithTop.coe_le_coe.mp
    rw [hcoe n ω, hcoe k ω]
    exact a.monotone ω hnk
  · intro n ω
    apply WithTop.coe_lt_coe.mp
    rw [hcoe n ω]
    exact a.lt_of_ne_zero n ω (htarget ω)
  · intro ω
    have hconv := (WithTop.tendsto_untopD 0
      (WithTop.coe_ne_top : (τ ω : WithTop ℝ≥0) ≠ ⊤)).comp (a.tendsto ω)
    convert hconv using 1
    · funext n
      change σ n ω = WithTop.untopD 0 (a.time n ω)
      rw [← hcoe n ω]
      rfl
    · rw [show WithTop.untopD 0 (τ ω : WithTop ℝ≥0) = τ ω from rfl]

/-- Diagonal finite maximum used to foretell a countable supremum. -/
noncomputable def diagonalSupTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (a : ∀ i, StoppingTimeForetelling ℱ (τ i))
    (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun i => (a i).time n ω

/-- A finite pointwise supremum of stopping times is a stopping time. -/
theorem isStoppingTime_finset_sup
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {τ : ι → Ω → WithTop ℝ≥0}
    (hτ : ∀ i ∈ s, IsStoppingTime ℱ (τ i)) :
    IsStoppingTime ℱ (fun ω => s.sup' hs fun i => τ i ω) := by
  classical
  intro t
  have heq : {ω | s.sup' hs (fun i => τ i ω) ≤ (t : WithTop ℝ≥0)} =
      ⋂ i ∈ s, {ω | τ i ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.sup'_le_iff]
  rw [heq]
  exact Finset.measurableSet_biInter s fun i hi => hτ i hi t

theorem diagonalSupTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (a : ∀ i, StoppingTimeForetelling ℱ (τ i)) (n : ℕ) :
    IsStoppingTime ℱ (diagonalSupTime a n) := by
  exact isStoppingTime_finset_sup Finset.nonempty_range_add_one
    fun i _ => (a i).isStoppingTime n

/-- A countable supremum of foretold stopping times is foretold.  The
diagonal construction simultaneously increases the number of coordinates
and the accuracy of every retained announcement. -/
noncomputable def iSup
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (a : ∀ i, StoppingTimeForetelling ℱ (τ i)) :
    StoppingTimeForetelling ℱ (fun ω => ⨆ i, τ i ω) where
  time := diagonalSupTime a
  isStoppingTime := diagonalSupTime_isStoppingTime a
  monotone := fun ω n k hnk => by
    apply Finset.sup'_le Finset.nonempty_range_add_one
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
    calc
      (a i).time n ω ≤ (a i).time k ω := (a i).monotone ω hnk
      _ ≤ diagonalSupTime a k ω :=
        Finset.le_sup' (fun j => (a j).time k ω)
          (Finset.mem_range.2 (hin.trans hnk |>.trans_lt
            (Nat.lt_succ_self k)))
  le := fun n ω => by
    apply Finset.sup'_le Finset.nonempty_range_add_one
    intro i hi
    exact ((a i).le n ω).trans (le_iSup (fun j => τ j ω) i)
  lt_of_ne_zero := fun n ω htarget => by
    change (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun i => (a i).time n ω) < ⨆ i, τ i ω
    rw [Finset.sup'_lt_iff]
    intro i hi
    by_cases hτi : τ i ω = 0
    · exact ((a i).le n ω).trans_lt (hτi ▸ pos_iff_ne_zero.mpr htarget)
    · exact ((a i).lt_of_ne_zero n ω hτi).trans_le
        (le_iSup (fun j => τ j ω) i)
  tendsto := fun ω => by
    have hmono : Monotone fun n => diagonalSupTime a n ω := by
      intro n k hnk
      apply Finset.sup'_le Finset.nonempty_range_add_one
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
      calc
        (a i).time n ω ≤ (a i).time k ω := (a i).monotone ω hnk
        _ ≤ diagonalSupTime a k ω :=
          Finset.le_sup' (fun j => (a j).time k ω)
            (Finset.mem_range.2 (hin.trans hnk |>.trans_lt
              (Nat.lt_succ_self k)))
    have hlimit : (⨆ n, diagonalSupTime a n ω) = ⨆ i, τ i ω := by
      apply le_antisymm
      · apply iSup_le
        intro n
        apply Finset.sup'_le Finset.nonempty_range_add_one
        intro i hi
        exact ((a i).le n ω).trans (le_iSup (fun j => τ j ω) i)
      · apply iSup_le
        intro i
        apply le_of_tendsto ((a i).tendsto ω)
        filter_upwards [eventually_ge_atTop i] with n hin
        exact (Finset.le_sup' (fun j => (a j).time n ω)
          (Finset.mem_range.2 (hin.trans_lt (Nat.lt_succ_self n)))).trans
          (le_iSup (fun k => diagonalSupTime a k ω) n)
    rw [← hlimit]
    exact tendsto_atTop_iSup hmono

/-- Keep `σ` on `{σ ≤ τ}` and send the complementary event to infinity. -/
noncomputable def restrictLE
    (σ τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => if σ ω ≤ τ ω then σ ω else ⊤

/-- The raw restricted approximant. -/
noncomputable def restrictLEApprox
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ)
    (τ : Ω → WithTop ℝ≥0) (n : ℕ) : Ω → WithTop ℝ≥0 :=
  fun ω => if a.time n ω ≤ τ ω then a.time n ω else ⊤

/-- Restricting a stopping time to the event that it is no later than a
second stopping time preserves the stopping-time property. -/
theorem restrictLEApprox_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (n : ℕ) : IsStoppingTime ℱ (restrictLEApprox a τ n) := by
  let E : Set Ω := {ω | a.time n ω ≤ τ ω}
  have hE : MeasurableSet[(a.isStoppingTime n).measurableSpace] E :=
    (a.isStoppingTime n).measurableSet_le_stopping_time hτ
  intro t
  have heq : {ω | restrictLEApprox a τ n ω ≤ (t : WithTop ℝ≥0)} =
      E ∩ {ω | a.time n ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    by_cases hω : ω ∈ E
    · have hcond : a.time n ω ≤ τ ω := hω
      simp [restrictLEApprox, E, hω, hcond]
    · have hcond : ¬a.time n ω ≤ τ ω := hω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hω, false_and,
        restrictLEApprox, hcond, ite_false, WithTop.top_le_iff]
      exact iff_false_intro WithTop.coe_ne_top
  rw [heq]
  exact ((a.isStoppingTime n).measurableSet E).1 hE |>.2 t

/-- The raw restricted approximants increase. -/
theorem restrictLEApprox_mono
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Monotone fun n => restrictLEApprox a τ n ω := by
  intro n k hnk
  by_cases hk : a.time k ω ≤ τ ω
  · have hn : a.time n ω ≤ τ ω := (a.monotone ω hnk).trans hk
    simp only [restrictLEApprox, ite_eq_left hk, ite_eq_left hn]
    exact a.monotone ω hnk
  · simp only [restrictLEApprox, ite_eq_right hk]
    exact le_top

/-- If a foretold time is kept on the event where it precedes an arbitrary
stopping time and sent to infinity otherwise, the resulting time is still
foretold.  The deterministic cap prevents the approximants themselves from
becoming infinite. -/
noncomputable def on_le
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    StoppingTimeForetelling ℱ (restrictLE σ τ) where
  time := fun n ω => Min.min (constApprox n ⊤) (restrictLEApprox a τ n ω)
  isStoppingTime := fun n =>
    ((const ℱ ⊤).isStoppingTime n).min
      (restrictLEApprox_isStoppingTime a hτ n)
  monotone := fun ω n k hnk => min_le_min
    (constApprox_mono ⊤ hnk) (restrictLEApprox_mono a τ ω hnk)
  le := fun n ω => by
    by_cases hστ : σ ω ≤ τ ω
    · have han : a.time n ω ≤ τ ω := (a.le n ω).trans hστ
      simp only [restrictLE, hστ, ite_true]
      rw [restrictLEApprox, ite_eq_left han]
      exact min_le_of_right_le (a.le n ω)
    · simp only [restrictLE, hστ, ite_false]
      exact le_top
  lt_of_ne_zero := fun n ω htarget => by
    by_cases hστ : σ ω ≤ τ ω
    · have hσ : σ ω ≠ 0 := by
        simpa only [restrictLE, hστ, ite_true] using htarget
      have han : a.time n ω ≤ τ ω := (a.le n ω).trans hστ
      simp only [restrictLE, hστ, ite_true]
      rw [restrictLEApprox, ite_eq_left han]
      exact (min_le_right _ _).trans_lt (a.lt_of_ne_zero n ω hσ)
    · simp only [restrictLE, hστ, ite_false]
      exact (min_le_left _ _).trans_lt
        (constApprox_lt_of_ne_zero n (by simp))
  tendsto := fun ω => by
    by_cases hστ : σ ω ≤ τ ω
    · have hraw : ∀ n, restrictLEApprox a τ n ω = a.time n ω := by
        intro n
        have han : a.time n ω ≤ τ ω := (a.le n ω).trans hστ
        simp only [restrictLEApprox, han, ite_true]
      have htend := (tendsto_constApprox ⊤).min (a.tendsto ω)
      simpa only [hraw, restrictLE, hστ, ite_true,
        min_eq_right le_top] using htend
    · have hevent : ∀ᶠ n in atTop, τ ω < a.time n ω :=
        (a.tendsto ω).eventually (Ioi_mem_nhds (lt_of_not_ge hστ))
      have heq : (fun n => Min.min (constApprox n ⊤)
          (restrictLEApprox a τ n ω)) =ᶠ[atTop]
          fun n => constApprox n ⊤ := by
        filter_upwards [hevent] with n hn
        have hnot : ¬a.time n ω ≤ τ ω := not_le_of_gt hn
        simp only [restrictLEApprox, hnot, ite_false,
          min_eq_left le_top]
      simpa only [restrictLE, hστ, ite_false] using
        (tendsto_constApprox ⊤).congr' heq.symm

end StoppingTimeForetelling

end FTAPTheorem42
