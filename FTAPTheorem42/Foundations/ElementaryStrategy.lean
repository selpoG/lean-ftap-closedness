/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.ElementaryIntegral
import FTAPTheorem42.Foundations.Paths

/-!
# Finite elementary stochastic-integral strategies

Finite lists of elementary interval blocks form a concrete gain-process
model.  Stopping, post-stopping tails, event restriction, and switching are
defined blockwise.  Their running- and terminal-gain identities follow from
the interval calculus in `ElementaryIntegral`.
-/

namespace FTAPTheorem42

open scoped BigOperators
open MeasureTheory

variable {Ω Time : Type*} [LinearOrder Time]

/-- A finite elementary strategy is a finite sum of interval blocks. -/
abbrev ElementaryStrategy (Ω Time : Type*) [LinearOrder Time] :=
  List (ElementaryInterval Ω Time)

namespace ElementaryStrategy

attribute [local instance] Classical.propDecidable

/-- Running gain of a finite elementary strategy. -/
def gain (S : Time → Ω → ℝ)
    (H : ElementaryStrategy Ω Time) (t : Time) (ω : Ω) : ℝ :=
  (H.map fun B => B.gain S t ω).sum

/-- A gain at time `t` only uses the price path up to `t`. -/
theorem gain_congr_price_upto
    {S T : Time → Ω → ℝ}
    (H : ElementaryStrategy Ω Time) (t : Time) (ω : Ω)
    (hST : ∀ s, s ≤ t → S s ω = T s ω) :
    gain S H t ω = gain T H t ω := by
  unfold gain
  congr 1
  apply List.map_congr_left
  intro B _
  simp only [ElementaryInterval.gain, hST _ (min_le_left _ _)]

/-- A pathwise equality of price paths preserves a finite strategy gain. -/
theorem gain_congr_price
    {S T : Time → Ω → ℝ}
    (H : ElementaryStrategy Ω Time) (t : Time) (ω : Ω)
    (hST : ∀ s, S s ω = T s ω) :
    gain S H t ω = gain T H t ω := by
  induction H with
  | nil => simp [gain]
  | cons B H ih =>
      change B.gain S t ω + gain S H t ω =
        B.gain T t ω + gain T H t ω
      rw [B.gain_congr_price t ω hST, ih]

/-- A finite elementary strategy is linear in the price integrator. -/
theorem gain_add_price
    (S T : Time → Ω → ℝ)
    (H : ElementaryStrategy Ω Time) (t : Time) (ω : Ω) :
    gain (fun s ω' => S s ω' + T s ω') H t ω =
      gain S H t ω + gain T H t ω := by
  induction H with
  | nil => simp [gain]
  | cons B H ih =>
      change
        B.gain (fun s ω' => S s ω' + T s ω') t ω +
            gain (fun s ω' => S s ω' + T s ω') H t ω =
          (B.gain S t ω + gain S H t ω) +
            (B.gain T t ω + gain T H t ω)
      rw [B.gain_add_price S T t ω, ih]
      ring

/-- Retain the post-`τ` tail of every elementary block. -/
def after (H : ElementaryStrategy Ω Time)
    (τ : Ω → Time) : ElementaryStrategy Ω Time :=
  H.map fun B => B.after τ

/-- Multiply all block coefficients by the same random scalar. -/
def mulCoefficient (c : Ω → ℝ)
    (H : ElementaryStrategy Ω Time) : ElementaryStrategy Ω Time :=
  H.map fun B => B.mulCoefficient c

/-- Negate an elementary strategy. -/
def neg (H : ElementaryStrategy Ω Time) : ElementaryStrategy Ω Time :=
  ElementaryStrategy.mulCoefficient (fun _ => -1) H

/-- Restrict all gains of an elementary strategy to an event. -/
noncomputable def restrict (s : Set Ω)
    (H : ElementaryStrategy Ω Time) : ElementaryStrategy Ω Time :=
  ElementaryStrategy.mulCoefficient
    (fun ω => if ω ∈ s then 1 else 0) H

@[simp]
theorem gain_append (S : Time → Ω → ℝ)
    (H K : ElementaryStrategy Ω Time) (t : Time) (ω : Ω) :
    gain S (H ++ K) t ω = gain S H t ω + gain S K t ω := by
  simp [gain]

theorem gain_after (S : Time → Ω → ℝ)
    (H : ElementaryStrategy Ω Time) (τ : Ω → Time)
    (t : Time) (ω : Ω) :
    gain S (ElementaryStrategy.after H τ) t ω =
      gain S H t ω - gain S H (min t (τ ω)) ω := by
  induction H with
  | nil => simp [ElementaryStrategy.after, gain]
  | cons B H ih =>
      change
        (B.after τ).gain S t ω +
            gain S (ElementaryStrategy.after H τ) t ω =
          (B.gain S t ω + gain S H t ω) -
            (B.gain S (min t (τ ω)) ω +
              gain S H (min t (τ ω)) ω)
      rw [ElementaryInterval.gain_after, ih]
      ring

theorem gain_mulCoefficient (S : Time → Ω → ℝ)
    (c : Ω → ℝ) (H : ElementaryStrategy Ω Time)
    (t : Time) (ω : Ω) :
    gain S (ElementaryStrategy.mulCoefficient c H) t ω =
      c ω * gain S H t ω := by
  induction H with
  | nil => simp [mulCoefficient, gain]
  | cons B H ih =>
      change
        (B.mulCoefficient c).gain S t ω +
            gain S (ElementaryStrategy.mulCoefficient c H) t ω =
          c ω * (B.gain S t ω + gain S H t ω)
      rw [ElementaryInterval.gain_mulCoefficient, ih]
      ring

@[simp]
theorem gain_neg (S : Time → Ω → ℝ)
    (H : ElementaryStrategy Ω Time) (t : Time) (ω : Ω) :
    gain S (ElementaryStrategy.neg H) t ω = -gain S H t ω := by
  rw [neg, gain_mulCoefficient]
  simp

theorem gain_restrict (S : Time → Ω → ℝ)
    (s : Set Ω) (H : ElementaryStrategy Ω Time)
    (t : Time) (ω : Ω) :
    gain S (ElementaryStrategy.restrict s H) t ω =
      if ω ∈ s then gain S H t ω else 0 := by
  classical
  rw [restrict, gain_mulCoefficient]
  split_ifs <;> simp_all

end ElementaryStrategy

end FTAPTheorem42

namespace FTAPTheorem42.ElementaryStrategy

/-! ## Finite stopping and initial constants in elementary gains -/

open MeasureTheory
open scoped NNReal

variable {Ω : Type*}

theorem gain_sub_initial (S : Process Ω) (H : ElementaryStrategy Ω NNReal) :
    gain (fun t ω => S t ω - S 0 ω) H = gain S H := by
  funext t ω
  unfold gain
  congr 1
  apply List.map_congr_left
  intro B _
  unfold ElementaryInterval.gain
  congr 1
  ring

theorem gain_finiteStoppedProcess (S : Process Ω) (H : ElementaryStrategy Ω NNReal)
    (τ : Ω → NNReal) :
    gain (stoppedProcess S (fun ω => (τ ω : WithTop NNReal))) H =
      stoppedProcess (gain S H) (fun ω => (τ ω : WithTop NNReal)) := by
  funext t ω
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, gain]
  congr 1
  apply List.map_congr_left
  intro B _
  simp only [ElementaryInterval.gain, stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [min_right_comm t (B.stopTime ω) (τ ω), min_right_comm t (B.startTime ω) (τ ω)]

end FTAPTheorem42.ElementaryStrategy
