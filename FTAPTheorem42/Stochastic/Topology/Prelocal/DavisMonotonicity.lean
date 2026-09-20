/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisCore

/-!
# Monotonicity in the discrete Davis estimates

Compare the running maximal and square functions used in the discrete Davis inequality.
-/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

lemma sqrt_quad_increment_le (r y₁ y₂ Q : ℝ) (hr : 0 < r)
    (hy₁ : 1 ≤ y₁) (hyle : y₁ ≤ y₂) (hQ : 0 ≤ Q)
    (hroot₁ : r ≤ Real.sqrt (y₁ ^ 2 + Q))
    (hroot₂ : r ≤ Real.sqrt (y₂ ^ 2 + Q)) :
    Real.sqrt (y₂ ^ 2 + Q) - Real.sqrt (y₁ ^ 2 + Q) ≤
      (y₂ ^ 2 - y₁ ^ 2) / (2 * r) := by
  have hnum : 0 ≤ y₂^2-y₁^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyle) (add_nonneg (by linarith) (by linarith))]
  have hsum : 0 < Real.sqrt (y₂^2+Q)+Real.sqrt (y₁^2+Q) := by
    have h₁ : 0 < Real.sqrt (y₁^2+Q) := lt_of_lt_of_le hr hroot₁
    nlinarith [Real.sqrt_nonneg (y₂^2+Q)]
  have hid : Real.sqrt (y₂^2+Q)-Real.sqrt (y₁^2+Q) =
      (y₂^2-y₁^2)/(Real.sqrt (y₂^2+Q)+Real.sqrt (y₁^2+Q)) := by
    field_simp [ne_of_gt hsum]
    have hsq₁ : (Real.sqrt (y₁^2+Q))^2 = y₁^2+Q :=
      Real.sq_sqrt (by positivity)
    have hsq₂ : (Real.sqrt (y₂^2+Q))^2 = y₂^2+Q :=
      Real.sq_sqrt (by positivity)
    nlinarith [hsq₁, hsq₂]
  rw [hid]
  apply div_le_div_of_nonneg_left hnum (by positivity : 0 < 2*r)
  nlinarith [hroot₁, hroot₂]

lemma endpoint_II_small (q d : ℝ) (hq : 0 ≤ q) (hd0 : 0 ≤ d)
    (hd2 : d ≤ 2) :
    Real.sqrt ((Real.sqrt (1+q))^2+d^2) - Real.sqrt (1+q) +
      d^2/(2*Real.sqrt (1+q)) ≤
      3*(Real.sqrt (q+d^2)-Real.sqrt q) := by
  let r := Real.sqrt (1+q)
  let a := Real.sqrt q
  let b := Real.sqrt (a^2+d^2)
  let R := Real.sqrt (r^2+d^2)
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hR : 0 < R := by dsimp [R]; positivity
  have hr2 : r^2 = 1+q := by dsimp [r]; exact Real.sq_sqrt (by positivity)
  have ha2 : a^2 = q := by dsimp [a]; exact Real.sq_sqrt hq
  have hb2 : b^2 = a^2+d^2 := by dsimp [b]; exact Real.sq_sqrt (by positivity)
  have hR2 : R^2 = r^2+d^2 := by dsimp [R]; exact Real.sq_sqrt (by positivity)
  have hRge : r ≤ R := by
    by_contra hnot
    have hlt : R < r := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg d]
  have hRinc : R-r ≤ d^2/(2*r) := by
    have hid : R-r = d^2/(R+r) := by
      have hsum : 0 < R+r := by linarith
      field_simp [ne_of_gt hsum]
      nlinarith [hR2]
    rw [hid]
    apply div_le_div_of_nonneg_left (sq_nonneg d) (by positivity : 0 < 2*r)
    nlinarith [hRge]
  have har : a ≤ r := by
    apply (Real.le_sqrt ha (by positivity)).2
    nlinarith [hr2,ha2]
  have hbd : b ≤ 2*r := by
    have hdr : 0 ≤ 2*r := by positivity
    have hsq : b^2 ≤ (2*r)^2 := by
      calc
        b^2 = a^2+d^2 := hb2
        _ ≤ 4*r^2 := by
          have hq' : a^2 ≤ r^2 := by nlinarith [hr2, ha2]
          nlinarith [hr2, ha2, hd2, hq']
        _ = (2*r)^2 := by ring
    exact (sq_le_sq₀ hb hdr).mp hsq
  have hble : a+b ≤ 3*r := by nlinarith
  have hba : d^2/r ≤ 3*(b-a) := by
    by_cases hz : a+b=0
    · have ha0 : a=0 := by nlinarith
      have hb0 : b=0 := by nlinarith
      have hd0' : d=0 := by nlinarith [hb2]
      simp [ha0, hb0, hd0']
    · have hden : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
      have hba_eq : b-a = d^2/(a+b) := by
        apply (eq_div_iff hden.ne').2
        nlinarith [hb2,ha2]
      rw [hba_eq]
      rw [show 3 * (d^2/(a+b)) = (3*d^2)/(a+b) by ring]
      apply (div_le_div_iff₀ hr hden).2
      have hmul := mul_le_mul_of_nonneg_left hble (sq_nonneg d)
      nlinarith [hmul]
  have hmain : R-r+d^2/(2*r)-3*(b-a) ≤ 0 := by
    calc
      R-r+d^2/(2*r)-3*(b-a) ≤
          d^2/(2*r)+d^2/(2*r)-3*(b-a) := by gcongr
      _ = d^2/r-3*(b-a) := by ring
      _ ≤ 0 := by linarith [hba]
  dsimp [r,a,b,R] at hmain ⊢
  rw [show (Real.sqrt q)^2 = q by exact Real.sq_sqrt hq] at hmain
  linarith [hmain]

end FTAPTheorem42.SIntegrableFiniteVariationBridge
