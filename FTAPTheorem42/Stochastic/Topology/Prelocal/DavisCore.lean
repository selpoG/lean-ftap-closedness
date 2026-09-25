/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.QuadraticCore
import FTAPTheorem42.Stochastic.Martingale.Quadratic.DiscreteMartingaleSquaredIncrement
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal

/-!
# The finite-sequence Davis potential

This file records the cardinality-free deterministic core used by the
Beiglböck--Siorpaes pathwise proof of Davis' inequality.  The potential is
telescoped before any probabilistic argument is made.  The one-step calculus
inequality for this potential is kept as an explicit input to the reduction;
it is the remaining analytic lemma in this boundary.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

/-! ## Realized square, running maximum, and the Davis coefficient -/

/-- The square of the realized quadratic root, including the initial value. -/
noncomputable def finiteDiscreteDavisSquare
    (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun omega => X 0 omega ^ 2 + discreteSquaredIncrementSum X n omega

/-- The absolute running maximum used in the pathwise Davis transform. -/
noncomputable def finiteDiscreteDavisStar
    (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  finiteRunningMax (fun k omega => |X k omega|) n

/-- The square-root notation for the Davis square. -/
noncomputable def finiteDiscreteDavisRoot
    (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun omega => Real.sqrt (finiteDiscreteDavisSquare X n omega)

/-- The left-endpoint coefficient in the pathwise Davis transform.  Real
division has the desired `0 / 0 = 0` convention. -/
noncomputable def finiteDiscreteDavisCoefficient
    (X : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun omega =>
    X k omega /
      Real.sqrt (finiteDiscreteDavisSquare X k omega +
        (finiteDiscreteDavisStar X k omega) ^ 2)

/-- The Beiglböck--Siorpaes potential for the upper Davis inequality. -/
noncomputable def finiteDiscreteDavisPotential
    (x m q : ℝ) : ℝ :=
  -2 * m + Real.sqrt (m ^ 2 + q) +
    (m ^ 2 - x ^ 2) / (2 * Real.sqrt (m ^ 2 + q))

/-- The lower potential in the Beiglböck--Siorpaes maximum inequality. -/
noncomputable def finiteDiscreteDavisLowerPotential
    (x m q : ℝ) : ℝ :=
  -2 * Real.sqrt q + Real.sqrt (m ^ 2 + q) -
    (m ^ 2 - x ^ 2) / (2 * Real.sqrt (m ^ 2 + q))

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisSquare_nonneg
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    0 ≤ finiteDiscreteDavisSquare X n omega := by
  exact add_nonneg (sq_nonneg _) (discreteSquaredIncrementSum_nonneg X n omega)

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisStar_nonneg
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    0 ≤ finiteDiscreteDavisStar X n omega := by
  exact finiteRunningMax_nonneg _ _ (fun _ _ => abs_nonneg _) omega

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisStar_value_le
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    |X n omega| ≤ finiteDiscreteDavisStar X n omega := by
  unfold finiteDiscreteDavisStar finiteRunningMax
  exact Finset.le_sup' (fun k => |X k omega|)
    (Finset.mem_range.2 (Nat.lt_succ_self n))

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisSquare_succ
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    finiteDiscreteDavisSquare X (n + 1) omega =
      finiteDiscreteDavisSquare X n omega +
        (X (n + 1) omega - X n omega) ^ 2 := by
  unfold finiteDiscreteDavisSquare discreteSquaredIncrementSum
  rw [Finset.sum_range_succ]
  ring

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisStar_succ
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    finiteDiscreteDavisStar X (n + 1) omega =
      max (finiteDiscreteDavisStar X n omega) |X (n + 1) omega| := by
  classical
  unfold finiteDiscreteDavisStar finiteRunningMax
  apply le_antisymm
  · apply Finset.sup'_le Finset.nonempty_range_add_one
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hkn : k = n + 1
    · subst k
      exact le_max_right _ _
    · have hkold : k < n + 1 := by omega
      have hkol : |X k omega| ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun j => |X j omega|) :=
        Finset.le_sup' (fun j => |X j omega|) (Finset.mem_range.2 hkold)
      exact hkol.trans (le_max_left _ _)
  · apply max_le
    · apply Finset.sup'_le Finset.nonempty_range_add_one
      intro k hk
      exact Finset.le_sup' (fun j => |X j omega|)
        (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hk)))
    · exact Finset.le_sup' (fun j => |X j omega|)
        (Finset.mem_range.2 (Nat.lt_succ_self (n + 1)))

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisSquare_initial
    (X : ℕ → Ω → ℝ) (omega : Ω) :
    finiteDiscreteDavisSquare X 0 omega = X 0 omega ^ 2 := by
  simp [finiteDiscreteDavisSquare, discreteSquaredIncrementSum]

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisStar_initial
    (X : ℕ → Ω → ℝ) (omega : Ω) :
    finiteDiscreteDavisStar X 0 omega = |X 0 omega| := by
  simp [finiteDiscreteDavisStar, finiteRunningMax]

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisCoefficient_abs_le_one
    (X : ℕ → Ω → ℝ) (k : ℕ) (omega : Ω) :
    |finiteDiscreteDavisCoefficient X k omega| ≤ 1 := by
  let q := finiteDiscreteDavisSquare X k omega +
    (finiteDiscreteDavisStar X k omega) ^ 2
  have hq : 0 ≤ q := add_nonneg
    (finiteDiscreteDavisSquare_nonneg X k omega)
    (sq_nonneg _)
  have hnum : (X k omega) ^ 2 ≤ q := by
    have hstar := finiteDiscreteDavisStar_value_le X k omega
    have hstarSq : (|X k omega|) ^ 2 ≤
        (finiteDiscreteDavisStar X k omega) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (finiteDiscreteDavisStar_nonneg X k omega)).2
        hstar
    have hxSq : (X k omega) ^ 2 = (|X k omega|) ^ 2 := by
      exact (sq_abs (X k omega)).symm
    rw [hxSq]
    exact hstarSq.trans
      (le_add_of_nonneg_left (finiteDiscreteDavisSquare_nonneg X k omega))
  have hroot : |X k omega| ≤ Real.sqrt q := by
    apply (Real.le_sqrt (abs_nonneg _) hq).2
    simpa only [sq_abs] using hnum
  change |X k omega / Real.sqrt q| ≤ 1
  by_cases hzero : Real.sqrt q = 0
  · simp [hzero]
  · rw [abs_div]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hq_ne : q ≠ 0 := by
      intro hq0
      exact hzero ((Real.sqrt_eq_zero hq).2 hq0)
    apply (div_le_iff₀
      (Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hq_ne)))).2
    simpa only [one_mul] using hroot

theorem finiteDiscreteDavisSquare_stronglyMeasurable_at
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : StronglyAdapted F X) (n : ℕ) :
    StronglyMeasurable[F n] (finiteDiscreteDavisSquare X n) := by
  unfold finiteDiscreteDavisSquare discreteSquaredIncrementSum
  have hZero : StronglyMeasurable[F n] (X 0) :=
    (hX 0).mono (F.mono (Nat.zero_le n))
  apply hZero.pow 2 |>.add
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  have hk' : k < n := Finset.mem_range.1 hk
  exact (((hX (k + 1)).mono (F.mono (Nat.succ_le_of_lt hk'))).sub
    ((hX k).mono (F.mono (Nat.le_of_lt hk')))).pow 2

theorem finiteDiscreteDavisStar_stronglyMeasurable_at
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : StronglyAdapted F X) (n : ℕ) :
    StronglyMeasurable[F n] (finiteDiscreteDavisStar X n) := by
  let _ : MeasurableSpace Ω := F n
  apply (measurable_finiteRunningMax _ _ ?_).stronglyMeasurable
  intro k hk
  exact (((hX k).mono (F.mono hk)).norm).measurable

theorem finiteDiscreteDavisCoefficient_stronglyAdapted
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : StronglyAdapted F X) :
    StronglyAdapted F (finiteDiscreteDavisCoefficient X) := by
  intro n
  have hNum : StronglyMeasurable[F n] (X n) := hX n
  have hSquare := finiteDiscreteDavisSquare_stronglyMeasurable_at hX n
  have hStar := finiteDiscreteDavisStar_stronglyMeasurable_at hX n
  have hDenSq : StronglyMeasurable[F n]
      (finiteDiscreteDavisSquare X n +
        (finiteDiscreteDavisStar X n) ^ 2) := hSquare.add (hStar.pow 2)
  have hDen : StronglyMeasurable[F n]
      (fun omega => Real.sqrt (finiteDiscreteDavisSquare X n omega +
        (finiteDiscreteDavisStar X n omega) ^ 2)) := by
    exact Real.continuous_sqrt.comp_stronglyMeasurable hDenSq
  exact hNum.div hDen

/-! ## The potential telescope -/

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisPotential_initial_nonpos
    (x : ℝ) :
    finiteDiscreteDavisPotential x |x| (x ^ 2) ≤ 0 := by
  unfold finiteDiscreteDavisPotential
  have hx : 0 ≤ |x| := abs_nonneg x
  have hsqrt : Real.sqrt (|x| ^ 2 + x ^ 2) = Real.sqrt 2 * |x| := by
    rw [show |x| ^ 2 = x ^ 2 by exact sq_abs x]
    rw [show x ^ 2 + x ^ 2 = 2 * x ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_sq_eq_abs]
  rw [hsqrt]
  rw [show |x| ^ 2 = x ^ 2 by exact sq_abs x]
  simp only [sub_self, zero_div, add_zero]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  nlinarith

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisPotential_terminal_lower
    (x m q : ℝ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hx : |x| ≤ m) :
    -2 * m + Real.sqrt q ≤ finiteDiscreteDavisPotential x m q := by
  unfold finiteDiscreteDavisPotential
  have hmq : 0 ≤ m ^ 2 + q := add_nonneg (sq_nonneg _) hq
  have hroot : Real.sqrt q ≤ Real.sqrt (m ^ 2 + q) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg m))
  have hden : 0 ≤ (m ^ 2 - x ^ 2) /
      (2 * Real.sqrt (m ^ 2 + q)) := by
    have hxsq : x ^ 2 ≤ m ^ 2 := by
      nlinarith [sq_abs x, sq_abs m, (sq_le_sq₀ (abs_nonneg x) hm).2 hx]
    exact div_nonneg (sub_nonneg.mpr hxsq)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  nlinarith

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisLowerPotential_initial_nonpos
    (x : ℝ) :
    finiteDiscreteDavisLowerPotential x |x| (x ^ 2) ≤ 0 := by
  unfold finiteDiscreteDavisLowerPotential
  rw [show |x| ^ 2 = x ^ 2 by exact sq_abs x]
  simp only [sub_self, zero_div, sub_zero]
  have hsqrt : Real.sqrt (x ^ 2 + x ^ 2) = Real.sqrt 2 * |x| := by
    rw [show x ^ 2 + x ^ 2 = 2 * x ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_sq_eq_abs]
  rw [hsqrt]
  rw [Real.sqrt_sq_eq_abs]
  have hx : 0 ≤ |x| := abs_nonneg x
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  nlinarith

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisLowerPotential_terminal_lower
    (x m q : ℝ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hx : |x| ≤ m) :
    -2 * Real.sqrt q + m / 2 ≤
      finiteDiscreteDavisLowerPotential x m q := by
  unfold finiteDiscreteDavisLowerPotential
  have hmq : 0 ≤ m ^ 2 + q := add_nonneg (sq_nonneg _) hq
  have hr : m ≤ Real.sqrt (m ^ 2 + q) := by
    apply (Real.le_sqrt hm hmq).2
    have : m ^ 2 ≤ m ^ 2 + q := le_add_of_nonneg_right hq
    simpa only [sq_abs] using this
  have hxsq : x ^ 2 ≤ m ^ 2 := by
    nlinarith [sq_abs x, sq_abs m,
      (sq_le_sq₀ (abs_nonneg x) hm).2 hx]
  have ha : 0 ≤ m ^ 2 - x ^ 2 := sub_nonneg.mpr hxsq
  have hden : 0 ≤ 2 * Real.sqrt (m ^ 2 + q) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hquot :
      (m ^ 2 - x ^ 2) /
          (2 * Real.sqrt (m ^ 2 + q)) ≤ m / 2 := by
    by_cases hzero : Real.sqrt (m ^ 2 + q) = 0
    · rw [hzero]
      simp only [mul_zero, div_zero]
      exact div_nonneg hm (show (0 : ℝ) ≤ 2 by norm_num)
    · have hrpos : 0 < Real.sqrt (m ^ 2 + q) := by
        exact Real.sqrt_pos.2 (lt_of_le_of_ne hmq (Ne.symm (by
          intro hq0
          exact hzero ((Real.sqrt_eq_zero hmq).2 hq0))))
      apply (div_le_iff₀ (mul_pos (by norm_num) hrpos)).2
      have hmul : m ^ 2 - x ^ 2 ≤ m * Real.sqrt (m ^ 2 + q) := by
        calc
          m ^ 2 - x ^ 2 ≤ m ^ 2 := sub_le_self _ (sq_nonneg x)
          _ ≤ m * Real.sqrt (m ^ 2 + q) := by
            nlinarith [mul_nonneg hm (sub_nonneg.mpr hr)]
      nlinarith
  have hnonneg : 0 ≤ Real.sqrt (m ^ 2 + q) := Real.sqrt_nonneg _
  nlinarith

/-! The next theorem is the exact finite-sum reduction.  Its one-step input is
the calculus lemma for the Davis potential; no pathwise inequality is hidden
in a structure field. -/

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisPathwise_of_potential_step
    (X : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω)
    (hStep : ∀ k < n,
      finiteDiscreteDavisLowerPotential (X (k + 1) omega)
          (finiteDiscreteDavisStar X (k + 1) omega)
          (finiteDiscreteDavisSquare X (k + 1) omega) -
        finiteDiscreteDavisLowerPotential (X k omega)
          (finiteDiscreteDavisStar X k omega)
          (finiteDiscreteDavisSquare X k omega) ≤
        (X k omega) * (X (k + 1) omega - X k omega) /
            Real.sqrt (finiteDiscreteDavisSquare X k omega +
              (finiteDiscreteDavisStar X k omega) ^ 2) +
          (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
            Real.sqrt (finiteDiscreteDavisSquare X k omega))) :
    finiteDiscreteDavisStar X n omega ≤
      6 * finiteDiscreteDavisRoot X n omega +
        2 * discretePredictableIntegral
          (finiteDiscreteDavisCoefficient X) X n omega := by
  let p : ℕ → ℝ := fun k =>
    finiteDiscreteDavisLowerPotential (X k omega)
      (finiteDiscreteDavisStar X k omega)
      (finiteDiscreteDavisSquare X k omega)
  have hInitial : p 0 ≤ 0 := by
    dsimp [p]
    rw [finiteDiscreteDavisStar_initial, finiteDiscreteDavisSquare_initial]
    exact finiteDiscreteDavisLowerPotential_initial_nonpos (X 0 omega)
  have hTerminal :
      -2 * finiteDiscreteDavisRoot X n omega +
          finiteDiscreteDavisStar X n omega / 2 ≤ p n := by
    dsimp [p, finiteDiscreteDavisRoot]
    apply finiteDiscreteDavisLowerPotential_terminal_lower
      (X n omega)
      (finiteDiscreteDavisStar X n omega)
      (finiteDiscreteDavisSquare X n omega)
      (finiteDiscreteDavisStar_nonneg X n omega)
      (finiteDiscreteDavisSquare_nonneg X n omega)
    exact finiteDiscreteDavisStar_value_le X n omega
  have hTel : p n - p 0 =
      ∑ k ∈ Finset.range n, (p (k + 1) - p k) := by
    exact (Finset.sum_range_sub p n).symm
  have hStepSum :
      (∑ k ∈ Finset.range n, (p (k + 1) - p k)) ≤
        ∑ k ∈ Finset.range n,
          ((X k omega) * (X (k + 1) omega - X k omega) /
              Real.sqrt (finiteDiscreteDavisSquare X k omega +
                (finiteDiscreteDavisStar X k omega) ^ 2) +
            (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
              Real.sqrt (finiteDiscreteDavisSquare X k omega))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hStep k (Finset.mem_range.1 hk)
  have hRhs :
      (∑ k ∈ Finset.range n,
          ((X k omega) * (X (k + 1) omega - X k omega) /
              Real.sqrt (finiteDiscreteDavisSquare X k omega +
                (finiteDiscreteDavisStar X k omega) ^ 2) +
              (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
              Real.sqrt (finiteDiscreteDavisSquare X k omega)))) =
        discretePredictableIntegral
            (finiteDiscreteDavisCoefficient X) X n omega +
          (finiteDiscreteDavisRoot X n omega -
            finiteDiscreteDavisRoot X 0 omega) := by
    calc
      (∑ k ∈ Finset.range n,
          ((X k omega) * (X (k + 1) omega - X k omega) /
              Real.sqrt (finiteDiscreteDavisSquare X k omega +
                (finiteDiscreteDavisStar X k omega) ^ 2) +
              (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
              Real.sqrt (finiteDiscreteDavisSquare X k omega)))) =
          ∑ k ∈ Finset.range n,
            (finiteDiscreteDavisCoefficient X k omega *
                (X (k + 1) omega - X k omega) +
              (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
                Real.sqrt (finiteDiscreteDavisSquare X k omega))) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold finiteDiscreteDavisCoefficient
        ring
      _ = ∑ k ∈ Finset.range n,
            (finiteDiscreteDavisCoefficient X k omega *
                (X (k + 1) omega - X k omega)) +
          ∑ k ∈ Finset.range n,
            (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
              Real.sqrt (finiteDiscreteDavisSquare X k omega)) := by
        rw [← Finset.sum_add_distrib]
      _ = discretePredictableIntegral
            (finiteDiscreteDavisCoefficient X) X n omega +
          (finiteDiscreteDavisRoot X n omega -
            finiteDiscreteDavisRoot X 0 omega) := by
        unfold discretePredictableIntegral
        have hRootTel :
            ∑ k ∈ Finset.range n,
                (Real.sqrt (finiteDiscreteDavisSquare X (k + 1) omega) -
                  Real.sqrt (finiteDiscreteDavisSquare X k omega)) =
              finiteDiscreteDavisRoot X n omega -
                finiteDiscreteDavisRoot X 0 omega := by
          exact Finset.sum_range_sub
            (fun k => Real.sqrt (finiteDiscreteDavisSquare X k omega)) n
        rw [hRootTel]
  have hMain :
      -2 * finiteDiscreteDavisRoot X n omega +
          finiteDiscreteDavisStar X n omega / 2 ≤
        discretePredictableIntegral
            (finiteDiscreteDavisCoefficient X) X n omega +
          (finiteDiscreteDavisRoot X n omega -
            finiteDiscreteDavisRoot X 0 omega) := by
    calc
      -2 * finiteDiscreteDavisRoot X n omega +
          finiteDiscreteDavisStar X n omega / 2 ≤ p n := hTerminal
      _ = p n - p 0 + p 0 := by ring
      _ ≤ p n - p 0 := by linarith
      _ = ∑ k ∈ Finset.range n, (p (k + 1) - p k) := hTel
      _ ≤ _ := hStepSum
      _ = _ := hRhs
  have hStar0 : 0 ≤ finiteDiscreteDavisStar X 0 omega :=
    finiteDiscreteDavisStar_nonneg X 0 omega
  have hRoot : 0 ≤ finiteDiscreteDavisRoot X n omega := by
    exact Real.sqrt_nonneg _
  have hRoot0 : 0 ≤ finiteDiscreteDavisRoot X 0 omega := by
    exact Real.sqrt_nonneg _
  nlinarith [hMain, hStar0, hRoot, hRoot0,
    finiteDiscreteDavisSquare_nonneg X n omega,
    finiteDiscreteDavisStar_nonneg X n omega]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
