/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisGeneric

/-! # Finite discrete Davis estimates using only first moments -/

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

open Filter MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem finiteDiscreteDavisRoot_le_abs_initial_add_sum
    (X : Nat → Ω → Real) (n : Nat) (w : Ω) :
    finiteDiscreteDavisRoot X n w ≤
      |X 0 w| + ∑ k ∈ Finset.range n, |X (k + 1) w - X k w| := by
  have hNonneg : 0 ≤ ∑ k ∈ Finset.range n, |X (k + 1) w - X k w| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range n)
    (fun k _ => abs_nonneg (X (k + 1) w - X k w))
  simp only [sq_abs] at hSq
  apply (Real.sqrt_le_iff).mpr
  refine ⟨add_nonneg (abs_nonneg _) hNonneg, ?_⟩
  dsimp only [finiteDiscreteDavisSquare, discreteSquaredIncrementSum]
  nlinarith [sq_abs (X 0 w), mul_nonneg (abs_nonneg (X 0 w)) hNonneg]

theorem finiteDiscreteDavisStar_integrable_of_martingale
    {mu : Measure Ω} {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {X : Nat → Ω → Real} (hX : Martingale X F mu) (n : Nat) :
    Integrable (finiteDiscreteDavisStar X n) mu := by
  have hInt : Integrable (fun w => ∑ k ∈ Finset.range (n + 1), |X k w|) mu :=
    integrable_finsetSum _ (fun k _ => (hX.integrable k).abs)
  apply hInt.mono'
    ((finiteDiscreteDavisStar_stronglyMeasurable_at hX.stronglyAdapted n).mono
      (F.le n)).aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteDiscreteDavisStar_nonneg X n w)]
  exact Finset.sup'_le Finset.nonempty_range_add_one (fun k => |X k w|)
    (fun k hk => Finset.single_le_sum (fun i _ => abs_nonneg (X i w)) hk)

theorem finiteDiscreteDavisRoot_integrable_of_martingale
    {mu : Measure Ω} {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {X : Nat → Ω → Real} (hX : Martingale X F mu) (n : Nat) :
    Integrable (finiteDiscreteDavisRoot X n) mu := by
  have hInt : Integrable
      (fun w => |X 0 w| + ∑ k ∈ Finset.range n, |X (k + 1) w - X k w|) mu :=
    (hX.integrable 0).abs.add (integrable_finsetSum _ (fun k _ =>
      ((hX.integrable (k + 1)).sub (hX.integrable k)).abs))
  have hMeas : StronglyMeasurable (finiteDiscreteDavisRoot X n) :=
    Real.continuous_sqrt.comp_stronglyMeasurable
      ((finiteDiscreteDavisSquare_stronglyMeasurable_at hX.stronglyAdapted n).mono (F.le n))
  apply hInt.mono' hMeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ finiteDiscreteDavisRoot X n w from
    Real.sqrt_nonneg _)]
  exact finiteDiscreteDavisRoot_le_abs_initial_add_sum X n w

theorem integral_finiteDiscreteDavis_le_six_root_of_martingale
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {X : Nat → Ω → Real} (hX : Martingale X F mu) (n : Nat) :
    (∫ w, finiteDiscreteDavisStar X n w ∂mu) ≤
      6 * ∫ w, finiteDiscreteDavisRoot X n w ∂mu := by
  have hM := DiscretePredictableIntegral.isMartingale_of_integrable (C := fun _ => (1 : Real))
    hX (finiteDiscreteDavisCoefficient_stronglyAdapted hX.stronglyAdapted)
    (fun k => Eventually.of_forall (finiteDiscreteDavisCoefficient_abs_le_one X k))
  have hI := hM.integrable n
  have hZero :
      (∫ w, discretePredictableIntegral (finiteDiscreteDavisCoefficient X) X n w ∂mu) = 0 :=
    by simpa using (hM.setIntegral_eq (Nat.zero_le n) (s := univ) MeasurableSet.univ).symm
  have hStar := finiteDiscreteDavisStar_integrable_of_martingale hX n
  have hRoot := finiteDiscreteDavisRoot_integrable_of_martingale hX n
  have hBound := integral_mono_ae hStar ((hRoot.const_mul 6).add (hI.const_mul 2))
    (Eventually.of_forall (finiteDiscreteDavisPathwise X n))
  simp only [Pi.add_apply] at hBound
  rw [integral_add (hRoot.const_mul 6) (hI.const_mul 2), integral_const_mul,
    integral_const_mul, hZero, mul_zero, add_zero] at hBound
  exact hBound

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## Reverse Davis estimates for finite martingales -/

open Filter MeasureTheory Set
open scoped NNReal ENNReal

private theorem upperPotential_step (x m q d : Real)
    (hm : 0 ≤ m) (hq : 0 ≤ q) (hx : |x| ≤ m) :
    finiteDiscreteDavisPotential (x + d) (max m |x + d|) (q + d ^ 2) -
        finiteDiscreteDavisPotential x m q ≤
      -(x * d / Real.sqrt (m ^ 2 + q)) + 5 * (max m |x + d| - m) := by
  let M := max m |x + d|
  let r := Real.sqrt (m ^ 2 + q)
  let R := Real.sqrt (M ^ 2 + (q + d ^ 2))
  have hmM : m ≤ M := le_max_left _ _
  have hyM : |x + d| ≤ M := le_max_right _ _
  have hM : 0 ≤ M := hm.trans hmM
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = m ^ 2 + q := Real.sq_sqrt (by positivity)
  have hRsq : R ^ 2 = M ^ 2 + (q + d ^ 2) := Real.sq_sqrt (by positivity)
  have hmr : m ≤ r := (Real.le_sqrt hm (by positivity)).mpr (by nlinarith)
  have hrR : r ≤ R := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hOld : 0 ≤ m ^ 2 - x ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg x) hm).mpr hx
    nlinarith [sq_abs x]
  have hNew : 0 ≤ M ^ 2 - (x + d) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (x + d)) hM).mpr hyM
    nlinarith [sq_abs (x + d)]
  by_cases hr : r = 0
  · have hm0 : m = 0 := le_antisymm (by simpa [hr] using hmr) hm
    have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hm0] using hx) (abs_nonneg _))
    have hq0 : q = 0 := by rw [hr, hm0] at hrsq; nlinarith
    subst m
    subst x
    subst q
    norm_num [finiteDiscreteDavisPotential, max_eq_right (abs_nonneg d), sq_abs]
    nlinarith [Real.sq_sqrt (show 0 ≤ d ^ 2 + d ^ 2 by positivity),
      Real.sqrt_nonneg (d ^ 2 + d ^ 2), sq_abs d, abs_nonneg d]
  have hrPos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hRPos : 0 < R := hrPos.trans_le hrR
  have hOldDiv : 0 ≤ (m ^ 2 - x ^ 2) / (2 * r) := div_nonneg hOld (by positivity)
  change -2 * M + R + (M ^ 2 - (x + d) ^ 2) / (2 * R) -
    (-2 * m + r + (m ^ 2 - x ^ 2) / (2 * r)) ≤ -(x * d / r) + 5 * (M - m)
  by_cases hSmall : M ≤ 2 * m
  · have hTangent : R - r ≤ (M ^ 2 - m ^ 2 + d ^ 2) / (2 * r) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr
      nlinarith [sq_nonneg (R - r)]
    have hQuot : (M ^ 2 - (x + d) ^ 2) / (2 * R) ≤
        (M ^ 2 - (x + d) ^ 2) / (2 * r) :=
      div_le_div_of_nonneg_left hNew (by positivity) (by linarith)
    have hAlgebra : (M ^ 2 - m ^ 2 + d ^ 2) / (2 * r) +
        (M ^ 2 - (x + d) ^ 2) / (2 * r) -
        (m ^ 2 - x ^ 2) / (2 * r) + x * d / r = (M ^ 2 - m ^ 2) / r := by ring
    have hBound : (M ^ 2 - m ^ 2) / r ≤ 3 * (M - m) := by
      apply (div_le_iff₀ hrPos).mpr
      nlinarith [mul_nonneg (show 0 ≤ 3 * r - (M + m) by linarith)
        (sub_nonneg.mpr hmM)]
    linarith
  · have hLarge : 2 * m < M := lt_of_not_ge hSmall
    have hMEq : M = |x + d| := max_eq_right (by
      dsimp only [M] at hLarge
      by_contra h
      rw [max_eq_left (le_of_not_ge h)] at hLarge
      linarith)
    have hd : |d| ≤ M + m := by
      calc
        |d| = |(x + d) - x| := by congr 1; ring
        _ ≤ |x + d| + |x| := abs_sub _ _
        _ ≤ M + m := add_le_add hyM hx
    have hRoot : R - r ≤ 4 * (M - m) := by
      have hdSq : d ^ 2 ≤ (M + m) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) (add_nonneg hM hm)).mpr hd
      have hProd := mul_nonneg (show 0 ≤ M - 2 * m by linarith)
        (show 0 ≤ 3 * M - 2 * m by linarith)
      have hrProd := mul_nonneg hr0 (sub_nonneg.mpr hmM)
      nlinarith [sq_nonneg (M - m)]
    have hCoeff : x * d / r ≤ |d| := by
      apply (div_le_iff₀ hrPos).mpr
      have h := mul_le_mul_of_nonneg_right (hx.trans hmr) (abs_nonneg d)
      nlinarith [le_abs_self (x * d), abs_mul x d]
    have hNewZero : M ^ 2 - (x + d) ^ 2 = 0 := by rw [hMEq, sq_abs, sub_self]
    rw [hNewZero, zero_div, add_zero]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem finiteDiscreteReverseDavisPathwise (X : Nat → Ω → Real) (n : Nat) (w : Ω) :
    finiteDiscreteDavisRoot X n w ≤ 7 * finiteDiscreteDavisStar X n w -
      discretePredictableIntegral (finiteDiscreteDavisCoefficient X) X n w := by
  let p := fun k => finiteDiscreteDavisPotential (X k w)
    (finiteDiscreteDavisStar X k w) (finiteDiscreteDavisSquare X k w)
  have hStep (k : Nat) : p (k + 1) - p k ≤
      -(finiteDiscreteDavisCoefficient X k w * (X (k + 1) w - X k w)) +
        5 * (finiteDiscreteDavisStar X (k + 1) w - finiteDiscreteDavisStar X k w) := by
    have h := upperPotential_step (X k w) (finiteDiscreteDavisStar X k w)
      (finiteDiscreteDavisSquare X k w) (X (k + 1) w - X k w)
      (finiteDiscreteDavisStar_nonneg X k w) (finiteDiscreteDavisSquare_nonneg X k w)
      (finiteDiscreteDavisStar_value_le X k w)
    dsimp only [p]
    rw [finiteDiscreteDavisStar_succ, finiteDiscreteDavisSquare_succ]
    simp only [add_sub_cancel] at h
    convert h using 1
    unfold finiteDiscreteDavisCoefficient
    rw [add_comm (finiteDiscreteDavisSquare X k w)]
    ring
  have hSum := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hStep k)
  rw [Finset.sum_range_sub] at hSum
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hSum
  rw [Finset.sum_range_sub (fun k => finiteDiscreteDavisStar X k w) n] at hSum
  have hInit : p 0 ≤ 0 := by
    dsimp only [p]
    rw [finiteDiscreteDavisStar_initial, finiteDiscreteDavisSquare_initial]
    exact finiteDiscreteDavisPotential_initial_nonpos _
  have hTerm := finiteDiscreteDavisPotential_terminal_lower (X n w)
    (finiteDiscreteDavisStar X n w) (finiteDiscreteDavisSquare X n w)
    (finiteDiscreteDavisStar_nonneg X n w) (finiteDiscreteDavisSquare_nonneg X n w)
    (finiteDiscreteDavisStar_value_le X n w)
  change -2 * finiteDiscreteDavisStar X n w + finiteDiscreteDavisRoot X n w ≤ p n at hTerm
  change _ ≤ -(discretePredictableIntegral (finiteDiscreteDavisCoefficient X) X n w) + _ at hSum
  linarith [finiteDiscreteDavisStar_nonneg X 0 w]

theorem integral_finiteDiscrete_root_le_seven_star_of_martingale
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {X : Nat → Ω → Real} (hX : Martingale X F mu) (n : Nat) :
    (∫ w, finiteDiscreteDavisRoot X n w ∂mu) ≤
      7 * ∫ w, finiteDiscreteDavisStar X n w ∂mu := by
  have hM := DiscretePredictableIntegral.isMartingale_of_integrable (C := fun _ => (1 : Real))
    hX (finiteDiscreteDavisCoefficient_stronglyAdapted hX.stronglyAdapted)
    (fun k => Eventually.of_forall (finiteDiscreteDavisCoefficient_abs_le_one X k))
  have hI := hM.integrable n
  have hZero :
      (∫ w, discretePredictableIntegral (finiteDiscreteDavisCoefficient X) X n w ∂mu) = 0 := by
    simpa using (hM.setIntegral_eq (Nat.zero_le n) (s := univ) MeasurableSet.univ).symm
  have hStar := finiteDiscreteDavisStar_integrable_of_martingale hX n
  have hRoot := finiteDiscreteDavisRoot_integrable_of_martingale hX n
  have hBound := integral_mono_ae hRoot ((hStar.const_mul 7).sub hI)
    (Eventually.of_forall (finiteDiscreteReverseDavisPathwise X n))
  simp only [Pi.sub_apply] at hBound
  rw [integral_sub (hStar.const_mul 7) hI, integral_const_mul, hZero, sub_zero] at hBound
  exact hBound

end FTAPTheorem42.SIntegrableFiniteVariationBridge
