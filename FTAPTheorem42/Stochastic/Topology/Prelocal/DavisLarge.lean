import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisCore

/-!
# Large increments in the Davis inequality

Control the increments selected by the large-increment case of the pathwise argument.
-/
open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42
namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

lemma endpoint_poly (a r d : ℝ) (ha : 0 ≤ a) (hr1 : 1 ≤ r)
    (hd2 : 2 ≤ d) (hdr : r ≤ d) (har : a ^ 2 + 1 = r ^ 2) :
    (4 * d * r + 2 * d - 2 * r) * (r - 1 / (2 * r)) +
        (d ^ 2 * (1 - r) - 3 * d * r ^ 2 - d * r) ≤ 0 := by
  have hrpos : 0 < r := by linarith
  have harle : a ≤ r := by
    by_contra hnot
    have hlt : r < a := lt_of_not_ge hnot
    nlinarith
  have hsum : 0 < r+a := by nlinarith
  have hdiff : r-a = 1/(r+a) := by
    apply (eq_div_iff hsum.ne').2
    nlinarith [har]
  have hrec : 1/(2*r) ≤ 1/(r+a) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have habound : a ≤ r-1/(2*r) := by nlinarith [hdiff,hrec]
  let C := 4*d*r+2*d-2*r
  have hC : 0 ≤ C := by dsimp [C]; nlinarith
  have hN : r * (C*(r-1/(2*r)) + (d^2*(1-r)-3*d*r^2-d*r)) ≤ 0 := by
    by_cases hrl : r ≤ 2
    · let N := -d^2*r^2+d^2*r+d*r^3+d*r^2-2*d*r-d-2*r^3+r
      have hN2 : N = -2*r^2+r-2 + (d-2) *
          (-d*r^2+d*r+r^3-r^2-1) := by dsimp [N]; ring
      have hb : -d*r^2+d*r+r^3-r^2-1 ≤ 0 := by
        have hmul : 0 ≤ (d-r)*r*(r-1) := by
          exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
        nlinarith [hmul]
      have hfac : (d-2) *
          (-d*r^2+d*r+r^3-r^2-1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hb
      have hNle : N ≤ 0 := by
        rw [hN2]
        nlinarith [hfac, sq_nonneg (r-1)]
      dsimp [N] at hNle
      field_simp
      nlinarith [hNle]
    · have hrl' : 2 ≤ r := by linarith
      let N := -d^2*r^2+d^2*r+d*r^3+d*r^2-2*d*r-d-2*r^3+r
      have hNr : N = -2*r^2 + (d-r) *
          (-d*r^2+d*r+2*r^2-2*r-1) := by dsimp [N]; ring
      have hb : -d*r^2+d*r+2*r^2-2*r-1 ≤ 0 := by
        have hmul : 0 ≤ (d-2)*r*(r-1) := by
          exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
        nlinarith [hmul]
      have hfac : (d-r) * (-d*r^2+d*r+2*r^2-2*r-1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hb
      have hNle : N ≤ 0 := by
        rw [hNr]
        nlinarith [hfac]
      dsimp [N] at hNle
      field_simp
      nlinarith [hNle]
  apply (le_of_mul_le_mul_right ?_ hrpos)
  simpa [mul_comm, C] using hN

lemma large_cross (a r d R : ℝ) (ha : 0 ≤ a) (hr1 : 1 ≤ r)
    (hd2 : 2 ≤ d) (hdr : r ≤ d) (har : a ^ 2 + 1 = r ^ 2)
    (hR2 : R ^ 2 = r ^ 2 + 2 * d ^ 2 - 2 * d) (hRgeD : d ≤ R) :
    (R - r + d / r) * (d + 2 * a) ≤ 3 * d ^ 2 := by
  have hr : 0 < r := by linarith
  have harle : a ≤ r := by
    by_contra hnot
    have hlt : r < a := lt_of_not_ge hnot
    nlinarith
  have hC0 : d+2*a-3*d*r ≤ 0 := by nlinarith
  have hpoly := endpoint_poly a r d ha hr1 hd2 hdr har
  have hEd :
      (d+2*a)*(2*(d-1)*r+d+r) - 3*d*r*(d+r) ≤ 0 := by
    have habound : a ≤ r-1/(2*r) := by
      have hsumra : 0 < r+a := by nlinarith
      have hdiff : r-a = 1/(r+a) := by
        apply (eq_div_iff hsumra.ne').2
        nlinarith [har]
      have hrec : 1/(2*r) ≤ 1/(r+a) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [harle]
      nlinarith
    have hC : 0 ≤ 4*d*r+2*d-2*r := by nlinarith [ha]
    have hbound := mul_le_mul_of_nonneg_left habound hC
    nlinarith [hpoly, hbound]
  have hER :
      (d+2*a)*(2*(d-1)*r+R+r) - 3*d*r*(R+r) ≤ 0 := by
    have hterm : (d+2*a-3*d*r)*R ≤
        (d+2*a-3*d*r)*d :=
      mul_le_mul_of_nonpos_left hRgeD hC0
    nlinarith [hEd, hterm]
  have hER' :
      (d+2*a)*(2*(d-1)*r+R+r) ≤ 3*d*r*(R+r) := by
    linarith [hER]
  have hident :
      (R-r+d/r)*(d+2*a)*(r*(R+r)) =
        d*(d+2*a)*(2*(d-1)*r+R+r) := by
    have hrr : 0 < r := hr
    field_simp [ne_of_gt hrr]
    ring_nf
    nlinarith [hR2]
  have hprod :
      (R-r+d/r)*(d+2*a)*(r*(R+r)) ≤
        3*d^2*(r*(R+r)) := by
    calc
      (R-r+d/r)*(d+2*a)*(r*(R+r)) =
          d*(d+2*a)*(2*(d-1)*r+R+r) := hident
      _ ≤ d*(3*d*r*(R+r)) := by
        calc
          d*(d+2*a)*(2*(d-1)*r+R+r) =
              d*((d+2*a)*(2*(d-1)*r+R+r)) := by ring
          _ ≤ d*(3*d*r*(R+r)) :=
            mul_le_mul_of_nonneg_left hER' (by linarith)
      _ = 3*d^2*(r*(R+r)) := by ring
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hRgeD
  have hpos : 0 < r*(R+r) := mul_pos hr (by linarith)
  have hprod' :
      ((R-r+d/r)*(d+2*a))*(r*(R+r)) ≤
        (3*d^2)*(r*(R+r)) := by
    simpa [mul_assoc] using hprod
  exact le_of_mul_le_mul_right hprod' hpos

end FTAPTheorem42.SIntegrableFiniteVariationBridge
