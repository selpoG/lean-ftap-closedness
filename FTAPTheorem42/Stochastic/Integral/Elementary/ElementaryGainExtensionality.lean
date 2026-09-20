/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand

/-!
# Pathwise extensionality of finite elementary gains

This file records the finite, deterministic part of the elementary
integral normal-form argument.  At a fixed path, a finite list of interval
blocks is a step function with finitely many endpoints.  The jump of that
step function at an endpoint is the sum of the coefficients of blocks ending
there minus the sum of the coefficients of blocks starting there.  Regrouping
the finite increment sum by endpoints then shows that the step function
determines the gain against every real-valued path.

No measurability, almost-everywhere equality, or regularity of the integrator
is used here.  The filtered and random-endpoint normalisation problem is left
to a later module.
-/

open scoped BigOperators NNReal
open MeasureTheory

namespace FTAPTheorem42

noncomputable section

/-! ## The scalar pathwise core -/

/-- A deterministic interval block at one fixed sample point. -/
structure PathElementaryInterval where
  coefficient : ℝ
  startTime : ℝ≥0
  stopTime : ℝ≥0
  start_le_stop : startTime ≤ stopTime

namespace PathElementaryInterval

/-- The step function represented by one interval block. -/
def step (B : PathElementaryInterval) (s : ℝ≥0) : ℝ :=
  if B.startTime < s ∧ s ≤ B.stopTime then B.coefficient else 0

/-- The gain of one interval block against a scalar path. -/
def gain (X : ℝ≥0 → ℝ) (B : PathElementaryInterval) (t : ℝ≥0) : ℝ :=
  B.coefficient *
    (X (min t B.stopTime) - X (min t B.startTime))

end PathElementaryInterval

abbrev PathElementaryStrategy := List PathElementaryInterval

namespace PathElementaryStrategy

/-- The step function represented by a finite block list. -/
def step (H : PathElementaryStrategy) (s : ℝ≥0) : ℝ :=
  (H.map fun B => B.step s).sum

/-- The finite increment sum of a block list. -/
def gain (X : ℝ≥0 → ℝ) (H : PathElementaryStrategy) (t : ℝ≥0) : ℝ :=
  (H.map fun B => B.gain X t).sum

/-- All endpoints occurring in a finite block list. -/
def endpointSet (H : PathElementaryStrategy) : Finset ℝ≥0 :=
  (H.map PathElementaryInterval.startTime ++
      H.map PathElementaryInterval.stopTime).toFinset

/-- The total coefficient of blocks starting at an endpoint. -/
def startSum (H : PathElementaryStrategy) (e : ℝ≥0) : ℝ :=
  (H.map fun B => if B.startTime = e then B.coefficient else 0).sum

/-- The total coefficient of blocks stopping at an endpoint. -/
def stopSum (H : PathElementaryStrategy) (e : ℝ≥0) : ℝ :=
  (H.map fun B => if B.stopTime = e then B.coefficient else 0).sum

/-- The signed endpoint coefficient (stop minus start). -/
def jump (H : PathElementaryStrategy) (e : ℝ≥0) : ℝ :=
  H.stopSum e - H.startSum e

theorem start_mem_endpointSet {H : PathElementaryStrategy}
    {B : PathElementaryInterval} (hB : B ∈ H) :
    B.startTime ∈ endpointSet H := by
  unfold endpointSet
  simp only [List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl ⟨B, hB, rfl⟩

theorem stop_mem_endpointSet {H : PathElementaryStrategy}
    {B : PathElementaryInterval} (hB : B ∈ H) :
    B.stopTime ∈ endpointSet H := by
  unfold endpointSet
  simp only [List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inr ⟨B, hB, rfl⟩

theorem step_cons (B : PathElementaryInterval) (H : PathElementaryStrategy)
    (s : ℝ≥0) :
    step (B :: H) s = B.step s + step H s := by
  rfl

theorem gain_cons (X : ℝ≥0 → ℝ) (B : PathElementaryInterval)
    (H : PathElementaryStrategy) (t : ℝ≥0) :
    gain X (B :: H) t = B.gain X t + gain X H t := by
  rfl

/-! ### Finite endpoint gaps -/

/-- A finite set has a point immediately to the right of any prescribed point
    in the sense that no member lies strictly between the two points. -/
theorem exists_right_gap (E : Finset ℝ≥0) (e : ℝ≥0) :
    ∃ s, e < s ∧ ∀ x ∈ E, x ≤ e ∨ s ≤ x := by
  classical
  let F := E.filter (fun x => e < x)
  by_cases hF : F.Nonempty
  · let m : ℝ≥0 := F.min' hF
    have hem : e < m := by
      exact (Finset.mem_filter.mp (F.min'_mem hF)).2
    obtain ⟨s, hes, hsm⟩ := exists_between hem
    refine ⟨s, hes, ?_⟩
    intro x hx
    by_cases hxe : x ≤ e
    · exact Or.inl hxe
    · right
      have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hxe⟩
      exact hsm.le.trans (F.min'_le x hxF)
  · refine ⟨e + 1, lt_add_of_pos_right e zero_lt_one, ?_⟩
    intro x hx
    by_cases hxe : x ≤ e
    · exact Or.inl hxe
    · exfalso
      exact False.elim (hF ⟨x, Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hxe⟩⟩)

private theorem interval_step_sub_of_gap
    (B : PathElementaryInterval) {e s : ℝ≥0}
    (hes : e < s)
    (hgap_start : B.startTime ≤ e ∨ s ≤ B.startTime)
    (hgap_stop : B.stopTime ≤ e ∨ s ≤ B.stopTime) :
    B.step s - B.step e =
      (if B.startTime = e then B.coefficient else 0) -
        (if B.stopTime = e then B.coefficient else 0) := by
  by_cases hstart : B.startTime = e
  · by_cases hstop : B.stopTime = e
    · simp [PathElementaryInterval.step, hstart, hstop, hes]
    · have hstart_le : e ≤ B.stopTime := by
        rw [← hstart]
        exact B.start_le_stop
      have hestop : e < B.stopTime :=
        lt_of_le_of_ne hstart_le (Ne.symm hstop)
      have hsstop : s ≤ B.stopTime := by
        rcases hgap_stop with h | h
        · exact False.elim ((not_lt_of_ge h) hestop)
        · exact h
      simp [PathElementaryInterval.step, hstart, hstop, hes, hsstop]
  · by_cases hstop : B.stopTime = e
    · have hstart_le : B.startTime ≤ e := by
        rw [← hstop]
        exact B.start_le_stop
      have hstart_lt : B.startTime < e :=
        lt_of_le_of_ne hstart_le hstart
      simp [PathElementaryInterval.step, hes, hstart_lt, hstart, hstop]
    · have hstart_iff : B.startTime < s ↔ B.startTime < e := by
        constructor
        · intro h
          rcases le_total (B.startTime) e with hle | hge
          · exact hle.lt_of_ne hstart
          · have : s ≤ B.startTime := by
              rcases hgap_start with h | h
              · exact False.elim (hstart (le_antisymm h hge))
              · exact h
            exact False.elim ((not_lt_of_ge this) h)
        · intro h
          exact h.trans hes
      have hstop_iff : s ≤ B.stopTime ↔ e ≤ B.stopTime := by
        constructor
        · intro h
          exact le_trans hes.le h
        · intro h
          rcases lt_or_gt_of_ne hstop with hlt | hgt
          · exact False.elim ((not_lt_of_ge h) hlt)
          · have : s ≤ B.stopTime := by
              rcases hgap_stop with h | h
              · exact False.elim ((not_lt_of_ge h) hgt)
              · exact h
            exact this
      by_cases hse : B.startTime < e ∧ e ≤ B.stopTime
      · have hss : B.startTime < s ∧ s ≤ B.stopTime :=
          ⟨hstart_iff.mpr hse.1, hstop_iff.mpr hse.2⟩
        simp [PathElementaryInterval.step, hse, hss, hstart, hstop]
      · have hss : ¬(B.startTime < s ∧ s ≤ B.stopTime) := by
          intro h
          exact hse ⟨hstart_iff.mp h.1, hstop_iff.mp h.2⟩
        simp [PathElementaryInterval.step, hse, hss, hstart, hstop]

private theorem step_sub_of_gap
    (H : PathElementaryStrategy) {e s : ℝ≥0}
    (hes : e < s)
    (hgap : ∀ x ∈ endpointSet H, x ≤ e ∨ s ≤ x) :
    step H s - step H e = -jump H e := by
  induction H with
  | nil => simp [step, jump, startSum, stopSum]
  | cons B H ih =>
      have hstart := hgap B.startTime
        (start_mem_endpointSet (H := B :: H) (B := B) (by simp))
      have hstop := hgap B.stopTime
        (stop_mem_endpointSet (H := B :: H) (B := B) (by simp))
      have hgap_tail : ∀ x ∈ endpointSet H, x ≤ e ∨ s ≤ x := by
        intro x hx
        have hx' : x ∈ endpointSet (B :: H) := by
          simp only [endpointSet, List.map_cons, List.mem_toFinset,
            List.mem_append] at hx ⊢
          aesop
        exact hgap x hx'
      have ih' := ih hgap_tail
      calc
        step (B :: H) s - step (B :: H) e =
            (B.step s - B.step e) + (step H s - step H e) := by
              rw [step_cons, step_cons]
              ring
        _ = -jump (B :: H) e := by
          rw [interval_step_sub_of_gap B hes hstart hstop, ih']
          simp only [jump, startSum, stopSum, List.map_cons, List.sum_cons]
          ring

/-! ### Regrouping the gain by endpoints -/

private theorem interval_gain_endpoint_decomposition
    (X : ℝ≥0 → ℝ) (B : PathElementaryInterval) (t : ℝ≥0) :
    B.gain X t =
      (if B.stopTime ≤ t then B.coefficient * X B.stopTime else 0) -
        (if B.startTime ≤ t then B.coefficient * X B.startTime else 0) +
        (if t < B.stopTime then B.coefficient * X t else 0) -
        (if t < B.startTime then B.coefficient * X t else 0) := by
  by_cases hstop : B.stopTime ≤ t <;>
    by_cases hstart : B.startTime ≤ t
  · have hstop' : ¬t < B.stopTime := not_lt_of_ge hstop
    have hstart' : ¬t < B.startTime := not_lt_of_ge hstart
    simp [PathElementaryInterval.gain, hstop, hstart, hstop', hstart']; ring
  · have hstart' : t < B.startTime := lt_of_not_ge hstart
    have hstart_le : B.startTime ≤ t :=
      B.start_le_stop.trans hstop
    exact False.elim ((not_lt_of_ge hstart_le) hstart')
  · have hstop' : t < B.stopTime := lt_of_not_ge hstop
    simp [PathElementaryInterval.gain, min_eq_left hstop'.le,
      hstop, hstart, hstop', not_lt_of_ge hstart]; ring
  · have hstop' : t < B.stopTime := lt_of_not_ge hstop
    have hstart' : t < B.startTime := lt_of_not_ge hstart
    simp [PathElementaryInterval.gain, min_eq_left hstop'.le,
      min_eq_left hstart'.le, hstop, hstart, hstop', hstart']

private theorem single_endpoint_sum
    (E : Finset ℝ≥0) (e : ℝ≥0) (he : e ∈ E)
    (p : ℝ≥0 → Prop) [DecidablePred p] (c : ℝ) (X : ℝ≥0 → ℝ) :
    Finset.sum (E.filter p) (fun x => (if e = x then c else 0) * X x) =
      if p e then c * X e else 0 := by
  classical
  by_cases hpe : p e
  · have he' : e ∈ E.filter p := Finset.mem_filter.mpr ⟨he, hpe⟩
    have hs :
        Finset.sum (E.filter p) (fun x => (if e = x then c else 0) * X x) =
          (if e = e then c else 0) * X e := by
      apply Finset.sum_eq_single (s := E.filter p) e
      · intro x hx hxe
        simp [Ne.symm hxe]
      · intro h
        exact (h he').elim
    rw [ite_eq_left hpe]
    simp only [ite_true] at hs
    exact hs
  · have hs :
        Finset.sum (E.filter p) (fun x => (if e = x then c else 0) * X x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxe : e ≠ x := by
        intro h
        apply hpe
        simpa [h] using (Finset.mem_filter.mp hx).2
      simp [hxe]
    simpa only [ite_eq_right hpe] using hs

private theorem sum_endpoint_weighted_eq
    (H : PathElementaryStrategy) (E : Finset ℝ≥0)
    (hE : ∀ B ∈ H, B.stopTime ∈ E)
    (p : ℝ≥0 → Prop) [DecidablePred p] (X : ℝ≥0 → ℝ) :
    (H.map fun B => if p B.stopTime then B.coefficient * X B.stopTime else 0).sum =
      Finset.sum (E.filter p) (fun e => H.stopSum e * X e) := by
  induction H with
  | nil => simp [stopSum]
  | cons B H ih =>
      have hB := hE B (by simp)
      have hH : ∀ C ∈ H, C.stopTime ∈ E := by
        intro C hC
        exact hE C (by simp [hC])
      rw [List.map_cons, List.sum_cons, ih hH]
      rw [← single_endpoint_sum E B.stopTime hB p B.coefficient X]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : B.stopTime = e
      · simp [stopSum, h]; ring
      · simp [stopSum, h]

private theorem sum_start_endpoint_weighted_eq
    (H : PathElementaryStrategy) (E : Finset ℝ≥0)
    (hE : ∀ B ∈ H, B.startTime ∈ E)
    (p : ℝ≥0 → Prop) [DecidablePred p] (X : ℝ≥0 → ℝ) :
    (H.map fun B => if p B.startTime then B.coefficient * X B.startTime else 0).sum =
      Finset.sum (E.filter p) (fun e => H.startSum e * X e) := by
  induction H with
  | nil => simp [startSum]
  | cons B H ih =>
      have hB := hE B (by simp)
      have hH : ∀ C ∈ H, C.startTime ∈ E := by
        intro C hC
        exact hE C (by simp [hC])
      rw [List.map_cons, List.sum_cons, ih hH]
      rw [← single_endpoint_sum E B.startTime hB p B.coefficient X]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : B.startTime = e
      · simp [startSum, h]; ring
      · simp [startSum, h]

private theorem gain_eq_block_decomposition
    (X : ℝ≥0 → ℝ) (H : PathElementaryStrategy) (t : ℝ≥0) :
    gain X H t =
      (H.map fun B =>
        if B.stopTime ≤ t then B.coefficient * X B.stopTime else 0).sum -
        (H.map fun B =>
          if B.startTime ≤ t then B.coefficient * X B.startTime else 0).sum +
        (H.map fun B =>
          if t < B.stopTime then B.coefficient * X t else 0).sum -
        (H.map fun B =>
          if t < B.startTime then B.coefficient * X t else 0).sum := by
  induction H with
  | nil => simp [gain]
  | cons B H ih =>
      rw [gain_cons, ih, interval_gain_endpoint_decomposition]
      simp only [List.map_cons, List.sum_cons]
      ring

private theorem gain_eq_endpoint_sum
    (X : ℝ≥0 → ℝ) (H : PathElementaryStrategy) (E : Finset ℝ≥0)
    (hE : ∀ B ∈ H, B.startTime ∈ E ∧ B.stopTime ∈ E)
    (t : ℝ≥0) :
    gain X H t =
      (Finset.sum (E.filter (fun e => e ≤ t)) (fun e => jump H e * X e)) +
        (Finset.sum (E.filter (fun e => t < e)) (fun e => jump H e)) * X t := by
  have hstopLe := sum_endpoint_weighted_eq H E
    (fun B hB => (hE B hB).2) (fun e => e ≤ t) X
  have hstartLe := sum_start_endpoint_weighted_eq H E
    (fun B hB => (hE B hB).1) (fun e => e ≤ t) X
  have hstopGt := sum_endpoint_weighted_eq H E
    (fun B hB => (hE B hB).2) (fun e => t < e) (fun _ => X t)
  have hstartGt := sum_start_endpoint_weighted_eq H E
    (fun B hB => (hE B hB).1) (fun e => t < e) (fun _ => X t)
  rw [gain_eq_block_decomposition, hstopLe, hstartLe, hstopGt, hstartGt]
  simp only [jump, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [sub_mul, Finset.sum_mul, Finset.sum_mul]
  ring

/-! ### Bounds from the pathwise step function

The next estimates are deliberately phrased in terms of the step function,
not in terms of the (possibly much larger) sum of absolute coefficients.  This
is the estimate used when a bounded predictable test is applied to an error
path: cancellations in a block representation are then harmless.
-/

theorem abs_jump_le_two_mul_of_step_bound
    (H : PathElementaryStrategy) (ε : ℝ) (_hε : 0 ≤ ε)
    (hstep : ∀ s, |H.step s| ≤ ε) {e : ℝ≥0}
    (_he : e ∈ endpointSet H) :
    |H.jump e| ≤ 2 * ε := by
  obtain ⟨s, hes, hgap⟩ := exists_right_gap (endpointSet H) e
  have hsub := step_sub_of_gap H hes hgap
  have hjump : H.jump e = H.step e - H.step s := by
    linarith
  rw [hjump]
  calc
    |H.step e - H.step s| ≤ |H.step e| + |H.step s| := abs_sub _ _
    _ ≤ ε + ε := add_le_add (hstep e) (hstep s)
    _ = 2 * ε := by ring

theorem endpointSet_card_le_two_mul_length
    (H : PathElementaryStrategy) :
    (endpointSet H).card ≤ 2 * H.length := by
  unfold endpointSet
  calc
    (H.map PathElementaryInterval.startTime ++
        H.map PathElementaryInterval.stopTime).toFinset.card ≤
        (H.map PathElementaryInterval.startTime ++
          H.map PathElementaryInterval.stopTime).length :=
      List.toFinset_card_le _
    _ = 2 * H.length := by
      simp only [List.length_append, List.length_map]
      omega

theorem abs_gain_le_of_step_bound
    (X : ℝ≥0 → ℝ) (H : PathElementaryStrategy) (t : ℝ≥0)
    (ε E : ℝ) (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hstep : ∀ s, |H.step s| ≤ ε)
    (hX : ∀ u, u ≤ t → |X u| ≤ E) :
    |H.gain X t| ≤ 8 * (H.length : ℝ) * ε * E := by
  classical
  let F₁ := (endpointSet H).filter (fun e => e ≤ t)
  let F₂ := (endpointSet H).filter (fun e => t < e)
  let C : ℝ := 2 * ε * E
  have hjump (e : ℝ≥0) (he : e ∈ endpointSet H) :
      |H.jump e| ≤ 2 * ε :=
    abs_jump_le_two_mul_of_step_bound H ε hε hstep he
  have hterm₁ (e : ℝ≥0) (he : e ∈ F₁) :
      |H.jump e * X e| ≤ C := by
    have he' : e ∈ endpointSet H := (Finset.mem_filter.mp he).1
    have het : e ≤ t := (Finset.mem_filter.mp he).2
    rw [abs_mul]
    calc
      |H.jump e| * |X e| ≤ (2 * ε) * E := by
        exact mul_le_mul (hjump e he') (hX e het)
          (abs_nonneg _) (by positivity)
      _ = C := by rfl
  have hterm₂ (e : ℝ≥0) (he : e ∈ F₂) :
      |H.jump e * X t| ≤ C := by
    have he' : e ∈ endpointSet H := (Finset.mem_filter.mp he).1
    rw [abs_mul]
    calc
      |H.jump e| * |X t| ≤ (2 * ε) * E := by
        exact mul_le_mul (hjump e he') (hX t le_rfl)
          (abs_nonneg _) (by positivity)
      _ = C := by rfl
  have hsum₁ :
      |∑ e ∈ F₁, H.jump e * X e| ≤ (F₁.card : ℝ) * C := by
    calc
      |∑ e ∈ F₁, H.jump e * X e| ≤
          ∑ e ∈ F₁, |H.jump e * X e| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ F₁, C :=
        Finset.sum_le_sum fun e he => hterm₁ e he
      _ = (F₁.card : ℝ) * C := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hsum₂ :
      |(∑ e ∈ F₂, H.jump e) * X t| ≤ (F₂.card : ℝ) * C := by
    rw [Finset.sum_mul]
    calc
      |∑ e ∈ F₂, H.jump e * X t| ≤
          ∑ e ∈ F₂, |H.jump e * X t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ F₂, C :=
        Finset.sum_le_sum fun e he => hterm₂ e he
      _ = (F₂.card : ℝ) * C := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hcard₁ : F₁.card ≤ (endpointSet H).card :=
    Finset.card_filter_le _ _
  have hcard₂ : F₂.card ≤ (endpointSet H).card :=
    Finset.card_filter_le _ _
  have hC : 0 ≤ C := by nlinarith
  rw [gain_eq_endpoint_sum X H (endpointSet H)
    (fun B hB => ⟨start_mem_endpointSet hB, stop_mem_endpointSet hB⟩) t]
  calc
    |(∑ e ∈ F₁, H.jump e * X e) +
          (∑ e ∈ F₂, H.jump e) * X t| ≤
        |∑ e ∈ F₁, H.jump e * X e| +
          |(∑ e ∈ F₂, H.jump e) * X t| := abs_add_le _ _
    _ ≤ (F₁.card : ℝ) * C + (F₂.card : ℝ) * C :=
      add_le_add hsum₁ hsum₂
    _ ≤ ((endpointSet H).card : ℝ) * C +
        ((endpointSet H).card : ℝ) * C := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard₁) hC)
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard₂) hC)
    _ = 2 * ((endpointSet H).card : ℝ) * C := by ring
    _ ≤ 4 * (H.length : ℝ) * C := by
      have hcard := endpointSet_card_le_two_mul_length H
      have hcard' :
          2 * ((endpointSet H).card : ℝ) ≤
            4 * (H.length : ℝ) := by
        exact_mod_cast (show 2 * (endpointSet H).card ≤
          4 * H.length by nlinarith [hcard])
      exact mul_le_mul_of_nonneg_right hcard' hC
    _ = 8 * (H.length : ℝ) * ε * E := by
      dsimp [C]
      ring

end PathElementaryStrategy

/-! ## Predictable elementary strategies at a fixed path -/

namespace PredictableElementaryStrategy

variable {Ω : Type*} [MeasurableSpace Ω]
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Forget a predictable block list down to its deterministic block list at a
    fixed sample point. -/
def pathStrategy (H : PredictableElementaryStrategy ℱ) (ω : Ω) :
    PathElementaryStrategy :=
  H.map fun B =>
    { coefficient := B.interval.coefficient ω
      startTime := B.interval.startTime ω
      stopTime := B.interval.stopTime ω
      start_le_stop := B.interval.start_le_stop ω }

theorem step_pathStrategy (H : PredictableElementaryStrategy ℱ)
    (s : ℝ≥0) (ω : Ω) :
    (pathStrategy H ω).step s = H.integrand s ω := by
  induction H with
  | nil => simp [pathStrategy, PathElementaryStrategy.step,
      FTAPTheorem42.PredictableElementaryStrategy.integrand]
  | cons B H ih =>
      change
        (if B.interval.startTime ω < s ∧ s ≤ B.interval.stopTime ω then
            B.interval.coefficient ω else 0) +
          (pathStrategy H ω).step s =
        FTAPTheorem42.PredictableElementaryInterval.integrand B s ω +
          FTAPTheorem42.PredictableElementaryStrategy.integrand H s ω
      rw [ih]
      rfl

theorem gain_pathStrategy
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (t : ℝ≥0) (ω : Ω) :
    (pathStrategy H ω).gain (fun s => S s ω) t =
      ElementaryStrategy.gain S
        (FTAPTheorem42.PredictableElementaryStrategy.toElementary H) t ω := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change
        PathElementaryStrategy.gain (fun s => S s ω)
            (({ coefficient := B.interval.coefficient ω
                startTime := B.interval.startTime ω
                stopTime := B.interval.stopTime ω
                start_le_stop := B.interval.start_le_stop ω } :
              PathElementaryInterval) :: pathStrategy H ω) t =
          ElementaryInterval.gain S B.interval t ω +
            ElementaryStrategy.gain S
              (FTAPTheorem42.PredictableElementaryStrategy.toElementary H) t ω
      rw [PathElementaryStrategy.gain_cons, ih]
      rfl

/-! ### Predictable elementary consumers for the pathwise estimates -/

/-- A pointwise bound on a predictable elementary step integrand gives the
corresponding pathwise gain bound.  The estimate depends on the finite number
of blocks, but not on the absolute coefficient sum of their representation. -/
theorem abs_gain_le_of_integrand_bound
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (t : ℝ≥0) (ω : Ω) (ε E : ℝ)
    (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hintegrand : ∀ s, |H.integrand s ω| ≤ ε)
    (hS : ∀ u, u ≤ t → |S u ω| ≤ E) :
    |ElementaryStrategy.gain S H.toElementary t ω| ≤
      8 * (H.length : ℝ) * ε * E := by
  rw [← H.gain_pathStrategy S t ω]
  have hPath := PathElementaryStrategy.abs_gain_le_of_step_bound
    (fun s => S s ω) (H.pathStrategy ω) t ε E hε hE
      (by
        intro s
        simpa only [H.step_pathStrategy] using hintegrand s)
      hS
  simpa only [PredictableElementaryStrategy.pathStrategy, List.length_map] using hPath

end PredictableElementaryStrategy

end
end FTAPTheorem42
