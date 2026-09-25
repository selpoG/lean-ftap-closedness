/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisLarge

/-!
# Endpoint estimates for the second Davis case

Prove the endpoint bounds used to conclude the second case of the discrete inequality.
-/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

lemma small_base (r R d : ℝ) (hr : 0 < r) (hd : 2 ≤ d)
    (hRge : r ≤ R) (hR2 : R ^ 2 = r ^ 2 + 2 * d ^ 2 - 2 * d) :
    R - r + d / r ≤ d ^ 2 / r := by
  have hRinc : R - r ≤ d * (d - 1) / r := by
    have hRpos : 0 < R := lt_of_lt_of_le hr hRge
    have hsum : 0 < R+r := by linarith
    have hid : R-r = (2*d*(d-1))/(R+r) := by
      field_simp [ne_of_gt hsum]
      nlinarith [hR2]
    rw [hid]
    calc
      2*d*(d-1)/(R+r) ≤ 2*d*(d-1)/(2*r) := by
        have hnum : 0 ≤ 2*d*(d-1) := by
          exact mul_nonneg (mul_nonneg (by norm_num) (by linarith))
            (by linarith)
        apply div_le_div_of_nonneg_left hnum (by positivity : 0 < 2*r)
        nlinarith [hRge]
      _ = d*(d-1)/r := by ring
  calc
    R-r+d/r = (R-r)+d/r := by ring
    _ ≤ d*(d-1)/r+d/r := by
      exact (add_le_add_left hRinc (d/r)) |>.trans_eq (by ring)
    _ = d^2/r := by ring

lemma small_fraction (a r d : ℝ) (hr : 0 < r) (ha0 : 0 ≤ a) (ha : a ≤ r)
    (hd : 0 < d) (hdr : d ≤ r) : d^2/r ≤ 3*d^2/(d+2*a) := by
  have hD : 0 < d+2*a := by nlinarith [ha0]
  have hD_le : d+2*a ≤ 3*r := by
    calc
      d+2*a ≤ d+2*r := by gcongr
      _ ≤ 3*r := by nlinarith [hdr]
  apply (le_div_iff₀ hD).2
  have hmul : d^2 * (d+2*a) ≤ d^2 * (3*r) :=
    mul_le_mul_of_nonneg_left hD_le (sq_nonneg d)
  calc
    d^2/r * (d+2*a) = (d^2 * (d+2*a))/r := by ring
    _ ≤ (d^2 * (3*r))/r :=
      div_le_div_of_nonneg_right hmul (le_of_lt hr)
    _ = 3*d^2 := by field_simp

lemma endpoint_II_large (q d : ℝ) (hq : 0 ≤ q) (hd : 2 ≤ d) :
    Real.sqrt ((Real.sqrt (1+q))^2 + 2*d^2-2*d) -
      Real.sqrt (1+q) + d/Real.sqrt (1+q) ≤
      3*(Real.sqrt (q+d^2)-Real.sqrt q) := by
  let r := Real.sqrt (1+q)
  let a := Real.sqrt q
  let b := Real.sqrt (a^2+d^2)
  let R := Real.sqrt (r^2+2*d^2-2*d)
  have hr1 : 1 ≤ r := by
    dsimp [r]
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [sq_nonneg (Real.sqrt q)]
  have hr : 0 < r := by linarith
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hr2 : r^2 = 1+q := by dsimp [r]; exact Real.sq_sqrt (by positivity)
  have ha2 : a^2 = q := by dsimp [a]; exact Real.sq_sqrt hq
  have hb2 : b^2 = a^2+d^2 := by dsimp [b]; exact Real.sq_sqrt (by positivity)
  have hR2 : R^2 = r^2+2*d^2-2*d := by
    dsimp [R]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg (d-1), hr1])
  have hRge : r ≤ R := by
    by_contra hnot
    have hlt : R < r := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg (d-1)]
  have hRgeD : d ≤ R := by
    by_contra hnot
    have hlt : R < d := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg (d-1), hr1]
  have hsum : 0 < a+b := by
    by_cases hz : a+b=0
    · have : a=0 := by nlinarith
      nlinarith [ha2, hb2]
    · exact lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  have hba_eq : b-a = d^2/(a+b) := by
    apply (eq_div_iff hsum.ne').2
    nlinarith [hb2,ha2]
  have hba_le : a+b ≤ d+2*a := by
    have hble : b ≤ a+d := by
      by_contra hnot
      have hlt : a+d < b := lt_of_not_ge hnot
      nlinarith [hb2, sq_nonneg (a+d)]
    nlinarith
  have hD : 0 < d+2*a := by nlinarith [ha, hd]
  have hDelta : 3*d^2/(d+2*a) ≤ 3*(b-a) := by
    have hfrac : d^2/(d+2*a) ≤ d^2/(a+b) :=
      div_le_div_of_nonneg_left (sq_nonneg d) hsum hba_le
    calc
      3*d^2/(d+2*a) = 3 * (d^2/(d+2*a)) := by ring
      _ ≤ 3 * (d^2/(a+b)) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 3*(b-a) := by rw [hba_eq]
  have hbase : R-r+d/r ≤ 3*d^2/(d+2*a) := by
    by_cases hdr : d ≤ r
    · have hsmall : R-r+d/r ≤ d^2/r := small_base r R d hr hd hRge hR2
      have har : a ≤ r := by
        apply (Real.le_sqrt ha (by positivity)).2
        nlinarith [hr2, ha2]
      have hfrac : d^2/r ≤ 3*d^2/(d+2*a) :=
        small_fraction a r d hr ha har (by linarith) hdr
      exact hsmall.trans hfrac
    · have hdr' : r ≤ d := le_of_not_ge hdr
      have hcross := large_cross a r d R ha hr1 hd hdr'
        (by nlinarith [hr2,ha2]) hR2 hRgeD
      exact (le_div_iff₀ hD).2 hcross
  have hfinal : R-r+d/r ≤ 3*(b-a) := hbase.trans hDelta
  dsimp [r,a,b,R] at hfinal ⊢
  rw [show (Real.sqrt q)^2 = q by exact Real.sq_sqrt hq] at hfinal
  exact hfinal

end FTAPTheorem42.SIntegrableFiniteVariationBridge
