/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisCaseI
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisCaseII

/-!
# Normalized discrete Davis estimates

Prove the discrete estimates after normalizing the maximal and square functions.
-/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

lemma lowerPotential_mzero_step (q d : ℝ) (hq : 0 ≤ q) :
    finiteDiscreteDavisLowerPotential d |d| (q + d ^ 2) -
        finiteDiscreteDavisLowerPotential 0 0 q ≤
      0 * d / Real.sqrt (0 ^ 2 + q) +
        (Real.sqrt (q + d ^ 2) - Real.sqrt q) := by
  let a := Real.sqrt q
  let v := |d|
  let b := Real.sqrt (a ^ 2 + v ^ 2)
  let s := Real.sqrt (a ^ 2 + 2 * v ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; exact Real.sqrt_nonneg _
  have hv : 0 ≤ v := abs_nonneg _
  have hb : 0 ≤ b := by dsimp [b]; exact Real.sqrt_nonneg _
  have hs : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg _
  have ha2 : a ^ 2 = q := by
    dsimp [a]
    exact Real.sq_sqrt hq
  have hv2 : v ^ 2 = d ^ 2 := by
    dsimp [v]
    exact sq_abs d
  have hb2 : b ^ 2 = a ^ 2 + v ^ 2 := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = a ^ 2 + 2 * v ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have havb : a ≤ b := by
    apply (sq_le_sq₀ ha hb).mp
    nlinarith [hb2, sq_nonneg v]
  have hright : 0 ≤ 3 * b - 2 * a := by linarith
  have hpoly : 12 * a ^ 2 + 7 * v ^ 2 ≥ 12 * a * b := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [hb2, sq_nonneg (12 * a ^ 2 + 7 * v ^ 2 - 12 * a * b)]
  have hsle : s ≤ 3 * b - 2 * a := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hright
    · nlinarith [hs2, hpoly]
  have hmain : s + 2 * a ≤ 3 * b := by linarith
  unfold finiteDiscreteDavisLowerPotential
  rw [show |d| ^ 2 = d ^ 2 by exact sq_abs d]
  have hrootQ : Real.sqrt (q + d ^ 2) = b := by
    dsimp [b]
    rw [ha2, hv2]
  have hroot2Q : Real.sqrt ((0 : ℝ) ^ 2 + q) = a := by
    simpa using (show Real.sqrt q = a by rfl)
  have hrootS : Real.sqrt (d ^ 2 + (q + d ^ 2)) = s := by
    dsimp [s]
    rw [ha2, hv2]
    congr 1
    ring
  rw [hrootQ, hroot2Q, hrootS]
  have hrootq : Real.sqrt q = a := by rfl
  rw [hrootq]
  simp only [sub_self, zero_mul, zero_div, zero_add, sub_zero]
  linarith [hmain]

lemma normalized_step_dispatch (x q d : ℝ) (hq : 0 ≤ q) (hx : |x| ≤ 1)
    (hd : 0 ≤ d) :
    finiteDiscreteDavisLowerPotential (x + d) (max 1 |x + d|) (q + d ^ 2) -
        finiteDiscreteDavisLowerPotential x 1 q ≤
      x * d / Real.sqrt (1 + q) +
        (Real.sqrt (q + d ^ 2) - Real.sqrt q) := by
  by_cases hd0 : d = 0
  · subst d
    simp [max_eq_left hx]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    by_cases hI : |x + d| ≤ 1
    · have hcase := caseI x q d hq hx hd hI
      have hle := sub_nonpos.mp hcase
      rw [max_eq_left hI]
      simpa using hle
    · have hcase := caseII x q d hq hx hdpos (le_of_not_ge hI)
      have hle := sub_nonpos.mp hcase
      have hypos : 0 ≤ x + d := by
        have hxge : -1 ≤ x := (abs_le.mp hx).1
        have hy_lower : -1 < x + d := by linarith
        by_contra hneg
        have hlt : x + d < 0 := lt_of_not_ge hneg
        have hlt1 : x + d < 1 := by linarith
        have habs : |x + d| < 1 := (abs_lt).2 ⟨hy_lower, hlt1⟩
        linarith
      have hmax : max 1 |x + d| = |x + d| := max_eq_right (le_of_not_ge hI)
      rw [hmax, abs_of_nonneg hypos]
      simpa using hle

lemma lowerPotential_scale_pos (x m q : ℝ) (hm : 0 < m) (hq : 0 ≤ q) :
    finiteDiscreteDavisLowerPotential x m q =
      m * finiteDiscreteDavisLowerPotential (x / m) 1 (q / m ^ 2) := by
  have hm0 : 0 ≤ m := hm.le
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmq : 0 ≤ m ^ 2 + q := by positivity
  have hmqpos : 0 < m ^ 2 + q := by nlinarith [sq_nonneg m]
  have hden : Real.sqrt (m ^ 2 + q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hmqpos)
  have hscaleq : Real.sqrt (q / m ^ 2) = Real.sqrt q / m := by
    rw [Real.sqrt_div hq]
    rw [Real.sqrt_sq hm0]
  have hscaled : Real.sqrt (1 + q / m ^ 2) =
      Real.sqrt (m ^ 2 + q) / m := by
    have harg : 1 + q / m ^ 2 = (m ^ 2 + q) / m ^ 2 := by
      field_simp [hmne]
    rw [harg, Real.sqrt_div hmq]
    rw [Real.sqrt_sq hm0]
  unfold finiteDiscreteDavisLowerPotential
  simp only [one_pow]
  rw [hscaleq, hscaled]
  field_simp [hden, hmne]

end FTAPTheorem42.SIntegrableFiniteVariationBridge
