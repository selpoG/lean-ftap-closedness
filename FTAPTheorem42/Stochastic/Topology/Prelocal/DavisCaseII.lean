import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisMonotonicity
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisEndpointII

/-!
# The second case of the Davis inequality

Bound the pathwise sums in the second case of the discrete Davis argument.
-/
open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open FTAPTheorem42
namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

lemma root_lower_large (r q d : ℝ) (hr : 0 < r) (hr2 : r ^ 2 = 1 + q)
    (hq : 0 ≤ q) (hd : 2 ≤ d) :
    r ≤ Real.sqrt ((d-1)^2+(q+d^2)) := by
  have hprod : 0 ≤ d*(d-1) := by
    have hd0 : 0 ≤ d := by linarith
    have hdminus : 0 ≤ d-1 := by linarith
    exact mul_nonneg hd0 hdminus
  have hsq : r^2 ≤ (d-1)^2+(q+d^2) := by
    rw [hr2]
    nlinarith only [hprod]
  exact (Real.le_sqrt (le_of_lt hr) (by positivity)).2 hsq

lemma endpoint_argument_identity (r q d : ℝ) (hr2 : r ^ 2 = 1 + q) :
    (d - 1) ^ 2 + (q + d ^ 2) = r ^ 2 + 2 * d ^ 2 - 2 * d := by
  nlinarith only [hr2]

lemma large_monotonic_endpoint (x q d r a b : ℝ)
    (harg : (d - 1) ^ 2 + (q + d ^ 2) = r ^ 2 + 2 * d ^ 2 - 2 * d)
    (hmon :
      Real.sqrt ((x + d) ^ 2 + (q + d ^ 2)) - r +
          (1 + d ^ 2 - (x + d) ^ 2) / (2 * r) - 3 * (b - a) ≤
        Real.sqrt ((d - 1) ^ 2 + (q + d ^ 2)) - r +
          (1 + d ^ 2 - (d - 1) ^ 2) / (2 * r) - 3 * (b - a)) :
    Real.sqrt ((x + d) ^ 2 + (q + d ^ 2)) - r +
          (1 + d ^ 2 - (x + d) ^ 2) / (2 * r) - 3 * (b - a) ≤
        Real.sqrt (r ^ 2 + 2 * d ^ 2 - 2 * d) - r + d / r - 3 * (b - a) := by
  calc
    _ ≤ Real.sqrt ((d - 1) ^ 2 + (q + d ^ 2)) - r +
        (1 + d ^ 2 - (d - 1) ^ 2) / (2 * r) - 3 * (b - a) := hmon
    _ = _ := by
      rw [harg]
      ring

lemma sub_nonpos_of_le_real {u v : ℝ} (h : u ≤ v) : u - v ≤ 0 :=
  sub_nonpos.mpr h

lemma caseII (x q d : ℝ) (hq : 0 ≤ q) (hx : |x| ≤ 1) (hd : 0 < d)
    (hI : 1 ≤ |x + d|) :
    finiteDiscreteDavisLowerPotential (x+d) (x+d) (q+d^2) -
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
  have hrootQ : Real.sqrt (q+d^2) = b := by
    dsimp [b]
    rw [show a^2 = q by exact ha2]
  have hroot1 : Real.sqrt (1+q) = r := by rfl
  have hrootq : Real.sqrt q = a := by rfl
  have hrootR : Real.sqrt (1+(q+d^2)) = R := by
    dsimp [R]
    rw [show 1+(q+d^2) = r^2+d^2 by nlinarith only [hr2]]
  have hres :
      finiteDiscreteDavisLowerPotential (x+d) (x+d) (q+d^2) -
          finiteDiscreteDavisLowerPotential x 1 q -
          (x*d/Real.sqrt (1+q) +
            (Real.sqrt (q+d^2)-Real.sqrt q)) =
        Real.sqrt ((x+d)^2+(q+d^2)) - r +
          (1+d^2-(x+d)^2)/(2*r) - 3*(b-a) := by
    unfold finiteDiscreteDavisLowerPotential
    simp only [one_pow, sub_self, zero_div]
    rw [hrootQ, hroot1, hrootq]
    ring
  rw [hres]
  have hxge : -1 ≤ x := (abs_le.mp hx).1
  have hy_lower : -1 < x+d := by linarith
  have hy_pos : 1 ≤ x+d := by
    by_contra hnot
    have hylt : x+d < 1 := lt_of_not_ge hnot
    have habs : |x+d| < 1 := (abs_lt).2 ⟨hy_lower, hylt⟩
    linarith
  have hRge : r ≤ R := by
    by_contra hnot
    have hlt : R < r := lt_of_not_ge hnot
    nlinarith [hR2, sq_nonneg d]
  have hmono (y₀ : ℝ) (hy₀ : 1 ≤ y₀) (hyle : y₀ ≤ x+d)
      (hbaseRoot : r ≤ Real.sqrt (y₀^2+(q+d^2))) :
      Real.sqrt ((x+d)^2 + (q+d^2)) - r +
          (1+d^2-(x+d)^2)/(2*r) - 3*(b-a) ≤
        Real.sqrt (y₀^2 + (q+d^2)) - r +
          (1+d^2-y₀^2)/(2*r) - 3*(b-a) := by
    have hrooty : r ≤ Real.sqrt ((x+d)^2+(q+d^2)) := by
      apply (Real.le_sqrt (le_of_lt hr) (by positivity)).2
      nlinarith [hr2, hy_pos, hq, sq_nonneg d,
        sq_nonneg ((x+d)-1)]
    have hinc := sqrt_quad_increment_le r y₀ (x+d) (q+d^2)
      hr hy₀ hyle (by positivity) hbaseRoot hrooty
    have hinc' :
        Real.sqrt ((x+d)^2+(q+d^2)) - Real.sqrt (y₀^2+(q+d^2)) ≤
          ((x+d)^2-y₀^2)/(2*r) := by
      simpa [add_assoc] using hinc
    have hterm :
        Real.sqrt ((x+d)^2+(q+d^2)) - Real.sqrt (y₀^2+(q+d^2)) -
            ((x+d)^2-y₀^2)/(2*r) ≤ 0 := sub_nonpos.mpr hinc'
    have hrewrite :
        (Real.sqrt ((x+d)^2 + (q+d^2)) - r +
            (1+d^2-(x+d)^2)/(2*r) - 3*(b-a)) =
          (Real.sqrt (y₀^2 + (q+d^2)) - r +
            (1+d^2-y₀^2)/(2*r) - 3*(b-a)) +
            (Real.sqrt ((x+d)^2+(q+d^2)) -
              Real.sqrt (y₀^2+(q+d^2)) -
              ((x+d)^2-y₀^2)/(2*r)) := by ring
    rw [hrewrite]
    calc
      _ ≤ (Real.sqrt (y₀^2 + (q+d^2)) - r +
          (1+d^2-y₀^2)/(2*r) - 3*(b-a)) + 0 :=
        by
          simpa [add_comm] using
            (add_le_add_left hterm
              (Real.sqrt (y₀^2 + (q+d^2)) - r +
                (1+d^2-y₀^2)/(2*r) - 3*(b-a)))
      _ = _ := by ring
  by_cases hdle : d ≤ 2
  · have hrootbase : r ≤ Real.sqrt ((1 : ℝ)^2+(q+d^2)) := by
      apply (Real.le_sqrt (le_of_lt hr) (by positivity)).2
      nlinarith [hr2, hq, sq_nonneg d]
    have hmon := hmono (1 : ℝ) (by norm_num) (by linarith) hrootbase
    have hend : R-r+d^2/(2*r) ≤ 3*(b-a) := by
      have hend0 := endpoint_II_small q d hq (le_of_lt hd) hdle
      have hrootRE :
          Real.sqrt ((Real.sqrt (1+q))^2+d^2) = R := by
        dsimp [R, r]
      rw [hrootRE, hrootQ, hroot1] at hend0
      exact hend0
    have hrootbase' : Real.sqrt ((1 : ℝ)^2+(q+d^2)) = R := by
      simp only [one_pow]
      dsimp [R]
      rw [show 1+(q+d^2) = r^2+d^2 by nlinarith only [hr2]]
    rw [hrootbase'] at hmon
    have hmon' :
        Real.sqrt ((x+d)^2+(q+d^2)) - r +
            (1+d^2-(x+d)^2)/(2*r) - 3*(b-a) ≤
          R-r+d^2/(2*r)-3*(b-a) := by
      simpa [one_pow] using hmon
    exact hmon'.trans (sub_nonpos.mpr hend)
  · have hdge : 2 ≤ d := le_of_not_ge hdle
    have hy0 : (1 : ℝ) ≤ d-1 := by linarith
    have hyle : d-1 ≤ x+d := by linarith only [hxge]
    have hrootbase : r ≤ Real.sqrt ((d-1)^2+(q+d^2)) :=
      root_lower_large r q d hr hr2 hq hdge
    have hmon := hmono (d-1) hy0 hyle hrootbase
    have hend :
        Real.sqrt (r^2+2*d^2-2*d)-r+d/r ≤ 3*(b-a) := by
      have hend0 := endpoint_II_large q d hq hdge
      rw [hrootQ, hroot1] at hend0
      exact hend0
    have harg := endpoint_argument_identity r q d hr2
    have hmon' := large_monotonic_endpoint x q d r a b harg hmon
    have hend' := sub_nonpos_of_le_real hend
    exact hmon'.trans hend'

end FTAPTheorem42.SIntegrableFiniteVariationBridge
