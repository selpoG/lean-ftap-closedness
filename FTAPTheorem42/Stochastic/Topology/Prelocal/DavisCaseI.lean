/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisCore

/-! # The first case of the pathwise Davis estimate

The small-increment square-root inequality and the remaining endpoint bound
combine to give the estimate for the first case. -/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42

lemma k2_I_A (q d : ℝ) (hq : 0 ≤ q) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    Real.sqrt ((1+q)+d^2) - Real.sqrt (1+q) -
      1/(2*Real.sqrt ((1+q)+d^2)) + (1+d^2)/(2*Real.sqrt (1+q)) -
      3*(Real.sqrt (q+d^2)-Real.sqrt q) ≤ 0 := by
  let r := Real.sqrt (1+q)
  let R := Real.sqrt (r^2+d^2)
  let a := Real.sqrt q
  let b := Real.sqrt (a^2+d^2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hr1 : 1 ≤ r := by
    dsimp [r]
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [sq_nonneg (Real.sqrt q)]
  have hr2 : r^2 = 1+q := by dsimp [r]; exact Real.sq_sqrt (by positivity)
  have ha2 : a^2 = q := by dsimp [a]; exact Real.sq_sqrt hq
  have hR2 : R^2 = r^2+d^2 := by dsimp [R]; exact Real.sq_sqrt (by positivity)
  have hb2 : b^2 = a^2+d^2 := by dsimp [b]; exact Real.sq_sqrt (by positivity)
  have hRinc : R-r ≤ d^2/(2*r) := by
    have hid : R-r = d^2/(R+r) := by
      have hsum : 0 < R+r := by linarith
      field_simp [ne_of_gt hsum]
      nlinarith [hR2]
    rw [hid]
    apply div_le_div_of_nonneg_left (sq_nonneg d) (by positivity : 0 < 2*r)
    nlinarith [hR2, sq_nonneg (R-r)]
  have hRge : r ≤ R := by
    by_contra hnot
    have hlt : R < r := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg d]
  have hrec : 1/(2*r)-1/(2*R) ≤ d^2/(4*r) := by
    have hrpos : 0 < r := hr
    have hRpos : 0 < R := hR
    have hdiff : 0 ≤ R-r := by linarith
    have hident : 1/(2*r)-1/(2*R) = (R-r)/(2*r*R) := by field_simp
    rw [hident]
    have hfirst : (R-r)/(2*r*R) ≤ (R-r)/(2*r*r) := by
      apply div_le_div_of_nonneg_left hdiff (by positivity) ?_
      nlinarith
    have hsecond : (R-r)/(2*r*r) ≤ (d^2/(2*r))/(2*r*r) := by
      apply div_le_div_of_nonneg_right hRinc (by positivity)
    have hthird : (d^2/(2*r))/(2*r*r) ≤ d^2/(4*r) := by
      apply (div_le_iff₀ (by positivity : 0 < 2*r*r)).2
      field_simp
      nlinarith [mul_nonneg (sq_nonneg d) (by nlinarith [hr1] : 0 ≤ r^2-1)]
    exact hfirst.trans (hsecond.trans hthird)
  have hba : 3*d^2/(2*r) ≤ 3*(b-a) := by
    by_cases hz : a+b = 0
    · have hab0 : a=0 := by nlinarith
      have hb0 : b=0 := by nlinarith
      have hd0' : d=0 := by nlinarith [hb2]
      simp [hab0,hb0,hd0']
    · have hden : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
      have har : a ≤ r := by
        apply (Real.le_sqrt ha (by positivity)).2
        nlinarith [hr2,ha2]
      have hbd : b ≤ r := by
        by_contra hnot
        have hlt : r < b := lt_of_not_ge hnot
        nlinarith [hr2,ha2,hb2,hd1, sq_nonneg a]
      have hble : a+b ≤ 2*r := by nlinarith
      have hfrac : d^2/(2*r) ≤ d^2/(a+b) := by
        apply div_le_div_of_nonneg_left (sq_nonneg d) hden hble
      have heq : b-a = d^2/(a+b) := by
        apply (eq_div_iff hden.ne').2
        nlinarith [hb2,ha2]
      calc
        3*d^2/(2*r) = 3*(d^2/(2*r)) := by ring
        _ ≤ 3*(d^2/(a+b)) := by
          exact mul_le_mul_of_nonneg_left hfrac (by norm_num)
        _ = 3*(b-a) := by rw [heq]
  have hmain : R-r -1/(2*R)+(1+d^2)/(2*r)-3*(b-a) ≤ 0 := by
    have haux : R-r +(1/(2*r)-1/(2*R)) + d^2/(2*r)-3*(b-a) ≤
        d^2/(2*r)+d^2/(4*r)+d^2/(2*r)-3*(b-a) := by
      calc
        R-r +(1/(2*r)-1/(2*R)) + d^2/(2*r)-3*(b-a) =
            (R-r)+(1/(2*r)-1/(2*R))+d^2/(2*r)-3*(b-a) := by ring
        _ ≤ d^2/(2*r)+(1/(2*r)-1/(2*R))+d^2/(2*r)-3*(b-a) := by gcongr
        _ ≤ d^2/(2*r)+d^2/(4*r)+d^2/(2*r)-3*(b-a) := by gcongr
    have hba' : d^2/(2*r)+d^2/(4*r)+d^2/(2*r) ≤ 3*(b-a) := by
      have hid : d^2/(2*r)+d^2/(4*r)+d^2/(2*r) = 5*d^2/(4*r) := by ring
      rw [hid]
      have hid2 : 3*d^2/(2*r) = 6*d^2/(4*r) := by ring
      rw [hid2] at hba
      have hcoef : 5*d^2/(4*r) ≤ 6*d^2/(4*r) := by
        apply (div_le_iff₀ (by positivity : 0 < 4*r)).2
        field_simp
        nlinarith [sq_nonneg d]
      exact hcoef.trans hba
    have hident : R-r -1/(2*R)+(1+d^2)/(2*r)-3*(b-a) =
        R-r +(1/(2*r)-1/(2*R)) + d^2/(2*r)-3*(b-a) := by ring
    rw [hident]
    exact haux.trans (sub_nonpos.mpr hba')
  dsimp [r,R,a,b] at hmain ⊢
  rw [show (Real.sqrt (1+q))^2 = 1+q by exact Real.sq_sqrt (by positivity)] at hmain
  rw [show (Real.sqrt q)^2 = q by exact Real.sq_sqrt hq] at hmain
  exact hmain

lemma endpoint_I_actual (q d : ℝ) (hq : 0 ≤ q) (hd1 : 1 ≤ d)
    (hd2 : d ≤ 2) :
    Real.sqrt ((Real.sqrt (1+q))^2+d^2) - Real.sqrt (1+q) +
      (d^2-2*d)/(2*Real.sqrt ((Real.sqrt (1+q))^2+d^2)) +
      d/Real.sqrt (1+q) ≤ 3*(Real.sqrt (q+d^2)-Real.sqrt q) := by
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
  have hbd : b ≤ d*r := by
    have hdr : 0 ≤ d*r := mul_nonneg (by linarith) (le_of_lt hr)
    have hdSq : 1 ≤ d^2 := by nlinarith [hd1, sq_nonneg (d-1)]
    have hmul : a^2 ≤ a^2*d^2 := by
      simpa only [one_mul, mul_one] using
        (mul_le_mul_of_nonneg_left hdSq (sq_nonneg a))
    have hsq : b^2 ≤ (d*r)^2 := by
      calc
        b^2 = a^2+d^2 := hb2
        _ ≤ d^2*r^2 := by
          calc
            a^2+d^2 ≤ d^2*(a^2+1) := by nlinarith [hmul]
            _ = d^2*r^2 := by rw [ha2, hr2]; ring
        _ = (d*r)^2 := by ring
    exact (sq_le_sq₀ hb hdr).mp hsq
  have hble : a+b ≤ (d+1)*r := by nlinarith
  have hden : 0 < a+b := by
    by_cases hz : a+b=0
    · have : a=0 := by nlinarith
      nlinarith [ha2, hb2, hd1]
    · exact lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  have hbound : (d+2)*(a+b) ≤ 6*d*r := by
    have hpoly : (d+1)*(d+2) ≤ 6*d := by nlinarith [hd1, hd2]
    have hmul := mul_le_mul_of_nonneg_left hble (by positivity : 0 ≤ d+2)
    nlinarith [hmul, hpoly, hr]
  have hba_eq : b-a = d^2/(a+b) := by
    apply (eq_div_iff hden.ne').2
    nlinarith [hb2,ha2]
  have hfrac : d*(d+2)/(2*r) ≤ 3*(b-a) := by
    rw [hba_eq]
    rw [show 3 * (d^2/(a+b)) = (3*d^2)/(a+b) by ring]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*r) hden).2
    have hmul := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ d)
    nlinarith [hmul]
  have hc : (d^2-2*d)/(2*R) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [hd1, hd2]
    · positivity
  have hmain : R-r+(d^2-2*d)/(2*R)+d/r-3*(b-a) ≤ 0 := by
    calc
      R-r+(d^2-2*d)/(2*R)+d/r-3*(b-a) ≤
          d^2/(2*r)+(d^2-2*d)/(2*R)+d/r-3*(b-a) := by
            gcongr
      _ ≤ d^2/(2*r)+0+d/r-3*(b-a) := by gcongr
      _ = d*(d+2)/(2*r)-3*(b-a) := by ring
      _ ≤ 0 := by linarith [hfrac]
  dsimp [r,a,b,R] at hmain ⊢
  rw [show (Real.sqrt q)^2 = q by exact Real.sq_sqrt hq] at hmain
  linarith [hmain]

lemma caseI (x q d : ℝ) (hq : 0 ≤ q) (hx : |x| ≤ 1) (hd : 0 ≤ d)
    (hI : |x + d| ≤ 1) :
    finiteDiscreteDavisLowerPotential (x+d) 1 (q+d^2) -
        finiteDiscreteDavisLowerPotential x 1 q -
        (x*d/Real.sqrt (1+q) +
          (Real.sqrt (q+d^2)-Real.sqrt q)) ≤ 0 := by
  let r := Real.sqrt (1+q)
  let R := Real.sqrt (r^2+d^2)
  let a := Real.sqrt q
  let b := Real.sqrt (a^2+d^2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hr2 : r^2 = 1+q := by dsimp [r]; exact Real.sq_sqrt (by positivity)
  have ha2 : a^2 = q := by dsimp [a]; exact Real.sq_sqrt hq
  have hR2 : R^2 = r^2+d^2 := by dsimp [R]; exact Real.sq_sqrt (by positivity)
  have hRge : r ≤ R := by
    by_contra hnot
    have hlt : R < r := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg d]
  have hrootQ : Real.sqrt (q+d^2) = b := by
    dsimp [b]
    rw [show a^2 = q by exact ha2]
  have hrootR : Real.sqrt (1+(q+d^2)) = R := by
    dsimp [R]
    rw [show 1+(q+d^2) = r^2+d^2 by nlinarith [hr2]]
  have hrootR' : Real.sqrt (1+q+d^2) = R := by
    rw [show 1 + q + d ^ 2 = 1 + (q + d ^ 2) by ring]
    exact hrootR
  have hroot1 : Real.sqrt (1+q) = r := by rfl
  have hrootq : Real.sqrt q = a := by rfl
  have hres :
      finiteDiscreteDavisLowerPotential (x+d) 1 (q+d^2) -
          finiteDiscreteDavisLowerPotential x 1 q -
          (x*d/Real.sqrt (1+q) +
            (Real.sqrt (q+d^2)-Real.sqrt q)) =
        (R-r - 1/(2*R) + (1+d^2)/(2*r) - 3*(b-a)) +
          (x+d)^2 * (1/(2*R)-1/(2*r)) := by
    unfold finiteDiscreteDavisLowerPotential
    simp only [one_pow]
    rw [hrootQ, hrootR, hroot1, hrootq]
    ring
  rw [hres]
  have hk0 : 1/(2*R)-1/(2*r) ≤ 0 := by
    have hrec : 1/R ≤ 1/r := one_div_le_one_div_of_le (by positivity) hRge
    have hrec' : 1/(2*R) ≤ 1/(2*r) := by
      calc
        1/(2*R) = (1/R)/2 := by ring
        _ ≤ (1/r)/2 := div_le_div_of_nonneg_right hrec (by norm_num)
        _ = 1/(2*r) := by ring
    exact sub_nonpos.mpr hrec'
  have hy_le : x+d ≤ 1 := le_trans (le_abs_self (x+d)) hI
  have hxge : -1 ≤ x := (abs_le.mp hx).1
  have hy_ge : -1 ≤ x+d := by linarith
  have hd2 : d ≤ 2 := by linarith
  by_cases hdle : d ≤ 1
  · have hbase : R-r -1/(2*R)+(1+d^2)/(2*r)-3*(b-a) ≤ 0 := by
      have hbase0 := k2_I_A q d hq hd hdle
      rw [hrootR', hroot1, hrootQ, hrootq] at hbase0
      exact hbase0
    have hmul : (x+d)^2 * (1/(2*R)-1/(2*r)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hk0
    exact add_nonpos hbase hmul
  · have hdge : 1 ≤ d := le_of_not_ge hdle
    have hy0 : 0 ≤ x+d := by linarith
    have hsquare : (d-1)^2 ≤ (x+d)^2 := by
      have hm := mul_nonneg (sub_nonneg.mpr (by linarith : d-1 ≤ x+d))
        (add_nonneg (by linarith : 0 ≤ d-1) (by linarith : 0 ≤ x+d))
      nlinarith [hm]
    have htmp : R-r + (d^2-2*d)/(2*R)+d/r ≤ 3*(b-a) := by
      have htmp0 := endpoint_I_actual q d hq hdge hd2
      rw [hrootQ, hrootq, hroot1] at htmp0
      have hrootRE :
          Real.sqrt ((Real.sqrt (1+q))^2+d^2) = R := by
        dsimp [R, r]
      rw [hrootRE] at htmp0
      exact htmp0
    have hend : R-r + ((d-1)^2-1)/(2*R)+d/r-3*(b-a) ≤ 0 := by
      apply sub_nonpos.mpr
      simpa only [show (d-1)^2-1 = d^2-2*d by ring] using htmp
    have hdiff : 0 ≤ (x+d)^2-(d-1)^2 := by linarith
    have hmul : ((x+d)^2-(d-1)^2) * (1/(2*R)-1/(2*r)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdiff hk0
    have hrewrite :
        R-r -1/(2*R)+(1+d^2)/(2*r)-3*(b-a) +
            (x+d)^2*(1/(2*R)-1/(2*r)) =
          (R-r+((d-1)^2-1)/(2*R)+d/r-3*(b-a)) +
            ((x+d)^2-(d-1)^2)*(1/(2*R)-1/(2*r)) := by ring
    rw [hrewrite]
    exact add_nonpos hend hmul

end FTAPTheorem42.SIntegrableFiniteVariationBridge
