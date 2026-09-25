/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisNormalized

/-!
# The discrete pathwise Davis inequality

Assemble the pathwise estimates for a finite real-valued sequence.
-/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

lemma lowerPotential_homogeneous_pos (lambda x m q : ℝ)
    (hm : 0 < m) (hq : 0 ≤ q) (hlambda : 0 < lambda) :
    finiteDiscreteDavisLowerPotential (lambda * x) (lambda * m)
        (lambda ^ 2 * q) =
      lambda * finiteDiscreteDavisLowerPotential x m q := by
  have hscale : 0 < lambda * m := by positivity
  have hleft := lowerPotential_scale_pos (lambda * x) (lambda * m)
    (lambda ^ 2 * q) hscale (by positivity)
  have hright := lowerPotential_scale_pos x m q
    hm hq
  rw [hleft]
  have hxratio : (lambda * x) / (lambda * m) = x / m := by
    field_simp [ne_of_gt hlambda, ne_of_gt hm]
  have hqratio : (lambda ^ 2 * q) / (lambda * m) ^ 2 = q / m ^ 2 := by
    field_simp [ne_of_gt hlambda, ne_of_gt hm]
  rw [hxratio, hqratio, hright]
  ring

lemma max_abs_scale_pos (m y : ℝ) (hm : 0 < m) :
    max m |y| = m * max 1 |y / m| := by
  have hm0 : 0 ≤ m := hm.le
  have habs : |y / m| = |y| / m := by
    rw [abs_div, abs_of_pos hm]
  by_cases hy : |y| ≤ m
  · rw [max_eq_left hy, habs, max_eq_left]
    · field_simp
    · exact (div_le_iff₀ hm).2 (by simpa using hy)
  · have hy' : m ≤ |y| := le_of_not_ge hy
    rw [max_eq_right hy', habs, max_eq_right]
    · field_simp
    · exact (le_div_iff₀ hm).2 (by simpa using hy')

lemma lowerPotential_step_pos (x m q d : ℝ) (hm : 0 < m)
    (hq : 0 ≤ q) (hx : |x| ≤ m) (hd : 0 ≤ d) :
    finiteDiscreteDavisLowerPotential (x + d) (max m |x + d|)
        (q + d ^ 2) - finiteDiscreteDavisLowerPotential x m q ≤
      x * d / Real.sqrt (m ^ 2 + q) +
        (Real.sqrt (q + d ^ 2) - Real.sqrt q) := by
  let x₀ := x / m
  let d₀ := d / m
  let q₀ := q / m ^ 2
  let M₀ := max 1 |x₀ + d₀|
  have hq₀ : 0 ≤ q₀ := by
    dsimp [q₀]
    positivity
  have hd₀ : 0 ≤ d₀ := by
    dsimp [d₀]
    exact div_nonneg hd (le_of_lt hm)
  have hx₀ : |x₀| ≤ 1 := by
    dsimp [x₀]
    rw [abs_div, abs_of_pos hm]
    exact (div_le_iff₀ hm).2 (by simpa using hx)
  have hnorm := normalized_step_dispatch x₀ q₀ d₀ hq₀ hx₀ hd₀
  have hxd : x₀ + d₀ = (x + d) / m := by
    dsimp [x₀, d₀]
    ring
  have hM : max m |x + d| = m * M₀ := by
    dsimp [M₀]
    rw [hxd]
    exact max_abs_scale_pos m (x + d) hm
  have hqsum : m ^ 2 * (q₀ + d₀ ^ 2) = q + d ^ 2 := by
    dsimp [q₀, d₀]
    field_simp [ne_of_gt hm]
  have hqscale : m ^ 2 * q₀ = q := by
    dsimp [q₀]
    field_simp [ne_of_gt hm]
  have hleft := lowerPotential_homogeneous_pos m (x₀ + d₀) M₀
    (q₀ + d₀ ^ 2) (by positivity : 0 < M₀)
    (by positivity : 0 ≤ q₀ + d₀ ^ 2) hm
  have hright := lowerPotential_homogeneous_pos m x₀ 1 q₀
    (by norm_num) hq₀ hm
  have hargxd : m * (x₀ + d₀) = x + d := by
    rw [hxd]
    field_simp
  have hargx : m * x₀ = x := by
    dsimp [x₀]
    field_simp
  have hnorm' :
      finiteDiscreteDavisLowerPotential (x₀ + d₀) M₀
          (q₀ + d₀ ^ 2) -
        finiteDiscreteDavisLowerPotential x₀ 1 q₀ ≤
      x₀ * d₀ / Real.sqrt (1 + q₀) +
        (Real.sqrt (q₀ + d₀ ^ 2) - Real.sqrt q₀) := by
    simpa [M₀] using hnorm
  have hscaled :
      finiteDiscreteDavisLowerPotential (x + d) (max m |x + d|)
          (q + d ^ 2) - finiteDiscreteDavisLowerPotential x m q =
        m * (finiteDiscreteDavisLowerPotential (x₀ + d₀) M₀
          (q₀ + d₀ ^ 2) - finiteDiscreteDavisLowerPotential x₀ 1 q₀) := by
    rw [hargxd, ← hM, hqsum] at hleft
    simp only [mul_one] at hright
    rw [hqscale, hargx] at hright
    rw [hleft, hright]
    ring
  have hcoef :
      m * (x₀ * d₀ / Real.sqrt (1 + q₀) +
        (Real.sqrt (q₀ + d₀ ^ 2) - Real.sqrt q₀)) =
      x * d / Real.sqrt (m ^ 2 + q) +
        (Real.sqrt (q + d ^ 2) - Real.sqrt q) := by
    have hq0arg : q₀ + d₀ ^ 2 = (q + d ^ 2) / m ^ 2 := by
      dsimp [q₀, d₀]
      field_simp [ne_of_gt hm]
    have hsqrtq0 : Real.sqrt q₀ = Real.sqrt q / m := by
      dsimp [q₀]
      rw [Real.sqrt_div hq, Real.sqrt_sq hm.le]
    have hsqrtQ0 : Real.sqrt (q₀ + d₀ ^ 2) =
        Real.sqrt (q + d ^ 2) / m := by
      rw [hq0arg, Real.sqrt_div (by positivity), Real.sqrt_sq hm.le]
    have hden0 : Real.sqrt (1 + q₀) =
        Real.sqrt (m ^ 2 + q) / m := by
      dsimp [q₀]
      have harg : 1 + q / m ^ 2 = (m ^ 2 + q) / m ^ 2 := by
        field_simp [ne_of_gt hm]
      rw [harg, Real.sqrt_div (by positivity), Real.sqrt_sq hm.le]
    rw [hsqrtq0, hsqrtQ0, hden0]
    dsimp [x₀, d₀]
    have hmqpos : 0 < m ^ 2 + q := by nlinarith [sq_nonneg m]
    have hdenne : Real.sqrt (m ^ 2 + q) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hmqpos)
    field_simp [ne_of_gt hm, hdenne]
  rw [hscaled]
  calc
    _ ≤ m * (x₀ * d₀ / Real.sqrt (1 + q₀) +
        (Real.sqrt (q₀ + d₀ ^ 2) - Real.sqrt q₀)) :=
      mul_le_mul_of_nonneg_left hnorm' hm.le
    _ = _ := hcoef

lemma lowerPotential_even (x m q : ℝ) :
    finiteDiscreteDavisLowerPotential (-x) m q =
      finiteDiscreteDavisLowerPotential x m q := by
  unfold finiteDiscreteDavisLowerPotential
  rw [neg_sq]

lemma lowerPotential_step_general (x m q d : ℝ) (hm : 0 ≤ m)
    (hq : 0 ≤ q) (hx : |x| ≤ m) :
    finiteDiscreteDavisLowerPotential (x + d) (max m |x + d|)
        (q + d ^ 2) - finiteDiscreteDavisLowerPotential x m q ≤
      x * d / Real.sqrt (m ^ 2 + q) +
        (Real.sqrt (q + d ^ 2) - Real.sqrt q) := by
  by_cases hm0 : m = 0
  · have hx0 : x = 0 := by
      have habs : |x| = 0 :=
        le_antisymm (by simpa [hm0] using hx) (abs_nonneg x)
      exact abs_eq_zero.mp habs
    subst x
    simpa [hm0] using lowerPotential_mzero_step q d hq
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    by_cases hd : 0 ≤ d
    · exact lowerPotential_step_pos x m q d hmpos hq hx hd
    · have hneg := lowerPotential_step_pos (-x) m q (-d) hmpos hq
        (by simpa [abs_neg] using hx) (by linarith)
      have harg : -x + -d = -(x + d) := by ring
      have hd2 : (-d) ^ 2 = d ^ 2 := by ring
      rw [harg, abs_neg, hd2] at hneg
      have hmul : -x * -d = x * d := by ring
      rw [hmul] at hneg
      simpa only [lowerPotential_even] using hneg

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisPathwise (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    finiteDiscreteDavisStar X n omega ≤
      6 * finiteDiscreteDavisRoot X n omega +
        2 * discretePredictableIntegral
          (finiteDiscreteDavisCoefficient X) X n omega := by
  apply finiteDiscreteDavisPathwise_of_potential_step X n omega
  intro k hk
  have hstep := lowerPotential_step_general
    (X k omega)
    (finiteDiscreteDavisStar X k omega)
    (finiteDiscreteDavisSquare X k omega)
    (X (k + 1) omega - X k omega)
    (finiteDiscreteDavisStar_nonneg X k omega)
    (finiteDiscreteDavisSquare_nonneg X k omega)
    (finiteDiscreteDavisStar_value_le X k omega)
  simpa [finiteDiscreteDavisSquare_succ, finiteDiscreteDavisStar_succ,
    add_comm, add_left_comm, add_assoc] using hstep

end FTAPTheorem42.SIntegrableFiniteVariationBridge
