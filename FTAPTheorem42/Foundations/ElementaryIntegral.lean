/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Trading.Basic

/-!
# Elementary interval stochastic integrals

This module constructs the pathwise integral calculus for finite sums of
buy-and-hold blocks. Stopping an interval and retaining
only its post-stopping tail are concrete operations, and their gain identities
are proved rather than postulated.

Measurability and predictability are deliberately not included in this file.
They belong to the filtered-market layer which selects the admissible
elementary blocks.
-/

open scoped BigOperators

namespace FTAPTheorem42

/-- One elementary buy-and-hold block on a random ordered interval. -/
structure ElementaryInterval
    (Ω Time : Type*) [LinearOrder Time] where
  coefficient : Ω → ℝ
  startTime : Ω → Time
  stopTime : Ω → Time
  start_le_stop : ∀ ω, startTime ω ≤ stopTime ω

namespace ElementaryInterval

variable {Ω Time : Type*} [LinearOrder Time]

theorem ext
    {B C : ElementaryInterval Ω Time}
    (hCoefficient : B.coefficient = C.coefficient)
    (hStart : B.startTime = C.startTime)
    (hStop : B.stopTime = C.stopTime) :
    B = C := by
  cases B with
  | mk Bco Bst Bsp hB =>
    cases C with
    | mk Cco Cst Csp hC =>
      simp only at hCoefficient hStart hStop
      subst Cco
      subst Cst
      subst Csp
      rfl

/-- Running gain of one elementary block against a price path `S`. -/
def gain (S : Time → Ω → ℝ)
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω) : ℝ :=
  B.coefficient ω *
    (S (min t (B.stopTime ω)) ω -
      S (min t (B.startTime ω)) ω)

/-- A pathwise equality of price paths preserves one interval gain. -/
theorem gain_congr_price
    {S T : Time → Ω → ℝ}
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω)
    (hST : ∀ s, S s ω = T s ω) :
    B.gain S t ω = B.gain T t ω := by
  simp only [gain]
  rw [hST, hST]

/-- One elementary interval is linear in the price integrator. -/
theorem gain_add_price
    (S T : Time → Ω → ℝ)
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω) :
    B.gain (fun s ω' => S s ω' + T s ω') t ω =
      B.gain S t ω + B.gain T t ω := by
  simp only [gain]
  ring

/-- Retain only the part of an elementary block strictly after `τ`. -/
def after (B : ElementaryInterval Ω Time)
    (τ : Ω → Time) : ElementaryInterval Ω Time where
  coefficient := B.coefficient
  startTime := fun ω => max (B.startTime ω) (τ ω)
  stopTime := fun ω => max (B.stopTime ω) (τ ω)
  start_le_stop := fun ω =>
    max_le_max_right (τ ω) (B.start_le_stop ω)

/-- Multiply the coefficient of a block by a scalar function. -/
def mulCoefficient (c : Ω → ℝ)
    (B : ElementaryInterval Ω Time) : ElementaryInterval Ω Time where
  coefficient := fun ω => c ω * B.coefficient ω
  startTime := B.startTime
  stopTime := B.stopTime
  start_le_stop := B.start_le_stop

/-- Negate the coefficient of a block. -/
def neg (B : ElementaryInterval Ω Time) : ElementaryInterval Ω Time :=
  B.mulCoefficient (fun _ => -1)

private theorem after_interval_identity
    (f : Time → ℝ) {a b c t : Time} (hab : a ≤ b) :
    f (min t (max b c)) - f (min t (max a c)) =
      (f (min t b) - f (min t a)) -
        (f (min (min t c) b) - f (min (min t c) a)) := by
  rcases le_total c a with hca | hac
  · have hcb : c ≤ b := hca.trans hab
    simp only [max_eq_left hca, max_eq_left hcb]
    have hmina : min (min t c) a = min t c := by
      simp [min_assoc, min_eq_left hca]
    have hminb : min (min t c) b = min t c := by
      simp [min_assoc, min_eq_left hcb]
    rw [hmina, hminb]
    ring
  · rcases le_total c b with hcb | hbc
    · rw [max_eq_right hac, max_eq_left hcb]
      rcases le_total t c with htc | hct
      · have htb0 : min t b = t :=
          min_eq_left (htc.trans hcb)
        have htc0 : min t c = t := min_eq_left htc
        have htb : min (min t c) b = min t b := by
          rw [min_eq_left htc]
        have hta' : min (min t c) a = min t a := by
          rw [min_eq_left htc]
        rw [htb, hta', htb0, htc0]
        ring
      · have hminc : min t c = c := min_eq_right hct
        have hca' : min c a = a := min_eq_right hac
        have hcb' : min c b = c := min_eq_left hcb
        have hta : min t a = a :=
          min_eq_right (hac.trans hct)
        rw [hminc, hca', hcb', hta]
        ring
    · have hac' : a ≤ c := hab.trans hbc
      rw [max_eq_right hac', max_eq_right hbc]
      rcases le_total t c with htc | hct
      · have htc0 : min t c = t := min_eq_left htc
        rw [htc0]
        ring
      · have hminc : min t c = c := min_eq_right hct
        have htb : min t b = b := min_eq_right (hbc.trans hct)
        have hta : min t a = a :=
          min_eq_right (hab.trans (hbc.trans hct))
        have hcb' : min c b = b := min_eq_right hbc
        have hca' : min c a = a := min_eq_right hac'
        rw [hminc, htb, hta, hcb', hca']
        ring

theorem gain_after
    (S : Time → Ω → ℝ) (B : ElementaryInterval Ω Time)
    (τ : Ω → Time) (t : Time) (ω : Ω) :
    (B.after τ).gain S t ω =
      B.gain S t ω - B.gain S (min t (τ ω)) ω := by
  simp only [gain, after]
  rw [after_interval_identity
    (fun s => S s ω) (B.start_le_stop ω)]
  ring

theorem gain_mulCoefficient
    (S : Time → Ω → ℝ) (c : Ω → ℝ)
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω) :
    (B.mulCoefficient c).gain S t ω =
      c ω * B.gain S t ω := by
  simp [gain, mulCoefficient]
  ring

end ElementaryInterval

end FTAPTheorem42
