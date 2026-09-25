/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.WeakStar
import FTAPTheorem42.Core.FSpace
import FTAPTheorem42.Core.L1DualRepresentation
import FTAPTheorem42.Core.WeakStarBoundedSlice
import FTAPTheorem42.Core.KreinSmulian
import FTAPTheorem42.Core.KreinSmulianC0
import FTAPTheorem42.Core.KreinSmulianC0Separation
import FTAPTheorem42.Core.C0DualCoefficients
import FTAPTheorem42.Core.KreinSmulianPredualSeparator
import FTAPTheorem42.Core.KreinSmulianCriterion
import FTAPTheorem42.Core.WeakStarFatouClosed

/-!
# Numerical schedules for Lemma 4.7

This module isolates the elementary asymptotics of the excursion count used
in the Delbaen--Schachermayer Lemma 4.7 argument.
-/

open Filter
open scoped Topology

namespace FTAPTheorem42

/--
The number of martingale excursions retained at scale `n`.

The factor `α / 4` is the one used in the probability aggregation step of
Lemma 4.7.
-/
noncomputable def lemma47ExcursionCount (α : ℝ) (n : ℕ) : ℕ :=
  ⌊(α / 4) * (n : ℝ)⌋₊

/-- The first rescaling in Lemma 4.7. -/
noncomputable def lemma47FirstScale (n : ℕ) : ℝ :=
  (((n : ℝ) ^ 2))⁻¹

/-- A gain-envelope norm bounded by `bound` yields a unit jump-envelope norm
after the inverse-square rescaling once `6 * bound ≤ n²`. -/
theorem lemma47FirstScale_mul_six_le_one
    {n : ℕ} (hn : 0 < n) {bound : ℝ}
    {B : ENNReal} (hB : B ≤ ENNReal.ofReal bound)
    (hNumeric : 6 * bound ≤ (n : ℝ) ^ 2) :
    ENNReal.ofReal |lemma47FirstScale n| * (6 * B) ≤ 1 := by
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnSq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnReal
  have hScaleNonnegative : 0 ≤ lemma47FirstScale n := by
    exact inv_nonneg.mpr (sq_nonneg (n : ℝ))
  have hSix : 6 * B ≤ ENNReal.ofReal (6 * bound) := by
    calc
      6 * B ≤ 6 * ENNReal.ofReal bound := by gcongr
      _ = ENNReal.ofReal (6 * bound) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
        norm_num
  calc
    ENNReal.ofReal |lemma47FirstScale n| * (6 * B) ≤
        ENNReal.ofReal (lemma47FirstScale n) *
          ENNReal.ofReal (6 * bound) := by
      rw [abs_of_nonneg hScaleNonnegative]
      gcongr
    _ = ENNReal.ofReal (lemma47FirstScale n * (6 * bound)) := by
      rw [ENNReal.ofReal_mul hScaleNonnegative]
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by
      calc
        lemma47FirstScale n * (6 * bound) ≤
            lemma47FirstScale n * ((n : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hNumeric hScaleNonnegative
        _ = 1 := by
          unfold lemma47FirstScale
          exact inv_mul_cancel₀ hnSq.ne')

/-- For `α > 0`, the excursion count tends to infinity. -/
theorem tendsto_lemma47ExcursionCount_atTop
    {α : ℝ} (hα : 0 < α) :
    Tendsto (lemma47ExcursionCount α) atTop atTop := by
  change Tendsto (fun n : ℕ => ⌊(α / 4) * (n : ℝ)⌋₊) atTop atTop
  exact tendsto_nat_floor_mul_atTop (α / 4) (by positivity)

/-- The excursion count has asymptotic density `α / 4`. -/
theorem tendsto_lemma47ExcursionCount_div
    {α : ℝ} (hα : 0 ≤ α) :
    Tendsto
      (fun n : ℕ => (lemma47ExcursionCount α n : ℝ) / (n : ℝ))
      atTop (𝓝 (α / 4)) := by
  change Tendsto
    (fun n : ℕ => (⌊(α / 4) * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
    atTop (𝓝 (α / 4))
  exact (tendsto_nat_floor_mul_div_atTop
    (R := ℝ) (a := α / 4) (by positivity)).comp
      tendsto_natCast_atTop_atTop

/-- Eventually the excursion count is nonzero. -/
theorem eventually_lemma47ExcursionCount_pos
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n in atTop, 0 < lemma47ExcursionCount α n :=
  (tendsto_lemma47ExcursionCount_atTop hα).eventually
    (eventually_gt_atTop 0)

/-- The reciprocal asymptotic density of the excursion count. -/
theorem tendsto_nat_div_lemma47ExcursionCount
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun n : ℕ => (n : ℝ) / lemma47ExcursionCount α n)
      atTop (𝓝 ((α / 4)⁻¹)) := by
  have hratio := tendsto_lemma47ExcursionCount_div hα.le
  have hinv := hratio.inv₀ (by positivity : α / 4 ≠ 0)
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 0,
    eventually_lemma47ExcursionCount_pos hα] with n hn hk
  rw [inv_div]

/--
The square-root scale is negligible compared with the excursion count.
-/
theorem tendsto_sqrt_nat_div_lemma47ExcursionCount
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt (n : ℝ) / lemma47ExcursionCount α n)
      atTop (𝓝 0) := by
  have hsqrtInv :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrtDiv :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
    apply hsqrtInv.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_div_self.symm
  have hproduct := hsqrtDiv.mul
    (tendsto_nat_div_lemma47ExcursionCount hα)
  simpa only [zero_mul] using hproduct.congr' (by
    filter_upwards [eventually_gt_atTop 0,
      eventually_lemma47ExcursionCount_pos hα] with n hn hk
    field_simp)

/--
The representative downside error from the Lemma 4.7 construction.
-/
noncomputable def lemma47Downside (α : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 4 : ℝ)) +
    2 / ((n : ℝ) * lemma47ExcursionCount α n)

/-- The downside error tends to zero for every positive `α`. -/
theorem tendsto_lemma47Downside_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (lemma47Downside α) atTop (𝓝 0) := by
  have hquarter :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hnInv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hkInv :
      Tendsto
        (fun n : ℕ => ((lemma47ExcursionCount α n : ℝ)⁻¹))
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp
        (tendsto_lemma47ExcursionCount_atTop hα))
  have hsecond :
      Tendsto
        (fun n : ℕ =>
          2 / ((n : ℝ) * lemma47ExcursionCount α n))
        atTop (𝓝 0) := by
    have hproduct := hnInv.mul hkInv
    have hscaled :
        Tendsto
          (fun n : ℕ => (2 : ℝ) *
            ((n : ℝ)⁻¹ *
              (lemma47ExcursionCount α n : ℝ)⁻¹))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hproduct :
          Tendsto
            (fun n : ℕ => (2 : ℝ) *
              ((n : ℝ)⁻¹ *
                (lemma47ExcursionCount α n : ℝ)⁻¹))
            atTop (𝓝 ((2 : ℝ) * (0 * 0))))
    simpa only [mul_zero] using hscaled.congr' (by
      filter_upwards [eventually_gt_atTop 0,
        eventually_lemma47ExcursionCount_pos hα] with n hn hk
      field_simp)
  change Tendsto
    (fun n : ℕ =>
      (n : ℝ) ^ (-(1 / 4 : ℝ)) +
        2 / ((n : ℝ) * lemma47ExcursionCount α n))
    atTop (𝓝 0)
  simpa only [zero_add] using hquarter.add hsecond

/-! ## Quantitative terminal schedule -/

/-- The fixed-mass lower bound retained by one finite-variation excursion. -/
noncomputable def lemma47ExcursionMass
    (α normBound : ℝ) (n : ℕ) : ℝ :=
  α ^ 2 - (4 * lemma47FirstScale n * normBound / α) ^ 2

/-- The downside level before the final division by the excursion count. -/
noncomputable def lemma47DownsideLevel (α : ℝ) (n : ℕ) : ℝ :=
  lemma47ExcursionCount α n * (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- The Doob-envelope probability error in the terminal claim estimate. -/
noncomputable def lemma47DoobError (α : ℝ) (n : ℕ) : ℝ :=
  (4 * Real.sqrt (lemma47ExcursionCount α n : ℝ) /
    lemma47DownsideLevel α n) ^ 2

/-- The deterministic positive level reached by the terminal claim. -/
noncomputable def lemma47TerminalLevel
    (α normBound : ℝ) (n : ℕ) : ℝ :=
  α * lemma47ExcursionMass α normBound n / 4 -
    (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- The probability mass remaining after the Doob-envelope error. -/
noncomputable def lemma47TerminalMass
    (α normBound : ℝ) (n : ℕ) : ℝ :=
  lemma47ExcursionMass α normBound n / 2 - lemma47DoobError α n

/-- The first inverse-square scale tends to zero. -/
theorem tendsto_lemma47FirstScale_zero :
    Tendsto lemma47FirstScale atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp hsq

/-- The finite-excursion mass error vanishes. -/
theorem tendsto_lemma47ExcursionMass
    {α : ℝ} (_hα : 0 < α) (normBound : ℝ) :
    Tendsto (lemma47ExcursionMass α normBound) atTop (𝓝 (α ^ 2)) := by
  have hError : Tendsto
      (fun n : ℕ => (4 * lemma47FirstScale n * normBound / α) ^ 2)
      atTop (𝓝 0) := by
    have hCore : Tendsto
        (fun n : ℕ => 4 * lemma47FirstScale n * normBound / α)
        atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul, zero_div] using
        (((tendsto_const_nhds.mul tendsto_lemma47FirstScale_zero).mul_const
          normBound).div_const α)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hCore.pow 2
  change Tendsto
    (fun n : ℕ => α ^ 2 -
      (4 * lemma47FirstScale n * normBound / α) ^ 2)
    atTop (𝓝 (α ^ 2))
  simpa only [sub_zero] using tendsto_const_nhds.sub hError

/-- The terminal positive level converges to `α³ / 4`. -/
theorem tendsto_lemma47TerminalLevel
    {α : ℝ} (hα : 0 < α) (normBound : ℝ) :
    Tendsto (lemma47TerminalLevel α normBound) atTop
      (𝓝 (α ^ 3 / 4)) := by
  have hquarter :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hScaled :=
    (((tendsto_const_nhds (x := α)).mul
      (tendsto_lemma47ExcursionMass hα normBound)).div_const 4).sub hquarter
  change Tendsto
    (fun n : ℕ => α * lemma47ExcursionMass α normBound n / 4 -
      (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 (α ^ 3 / 4))
  convert hScaled using 1
  ring_nf

/-- The first-localized negative jump is eventually bounded by `2/n`; in
fact the estimate holds for every positive `n`. -/
theorem lemma47FirstScale_mul_succ_le_two_div
    {n : ℕ} (hn : 0 < n) :
    lemma47FirstScale n * ((n : ℝ) + 1) ≤ 2 / (n : ℝ) := by
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  unfold lemma47FirstScale
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hnReal)).2
  field_simp
  nlinarith

/-- The retained excursion count never exceeds its unfloored linear scale. -/
theorem lemma47ExcursionCount_cast_le
    {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    (lemma47ExcursionCount α n : ℝ) ≤ α * (n : ℝ) / 4 := by
  unfold lemma47ExcursionCount
  have hFloor :
      (⌊(α / 4) * (n : ℝ)⌋₊ : ℝ) ≤ (α / 4) * (n : ℝ) :=
    Nat.floor_le
      (mul_nonneg (div_nonneg hα (by norm_num)) (Nat.cast_nonneg n))
  calc
    (⌊(α / 4) * (n : ℝ)⌋₊ : ℝ) ≤ (α / 4) * (n : ℝ) := hFloor
    _ = α * (n : ℝ) / 4 := by ring

/-- At the paper's radius `n/2`, the first `floor(αn/4)` excursion
envelopes have total Chebyshev error at most `α`. -/
theorem lemma47_excursionError_le
    {α : ℝ} (hα : 0 < α) (hαQuarter : α ≤ 1 / 4)
    {n : ℕ} (hn : 0 < n) :
    (4 * (lemma47ExcursionCount α n : ℝ) / ((n : ℝ) / 2)) ^ 2 ≤ α := by
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hkNonnegative : 0 ≤ (lemma47ExcursionCount α n : ℝ) :=
    Nat.cast_nonneg _
  have hCount := lemma47ExcursionCount_cast_le hα.le n
  have hRatioNonnegative :
      0 ≤ 4 * (lemma47ExcursionCount α n : ℝ) / ((n : ℝ) / 2) := by
    positivity
  have hRatio :
      4 * (lemma47ExcursionCount α n : ℝ) / ((n : ℝ) / 2) ≤
        2 * α := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) / 2)).2
    nlinarith
  nlinarith [sq_nonneg
    (4 * (lemma47ExcursionCount α n : ℝ) / ((n : ℝ) / 2))]

/-- Inverse-square localization sends the original level `n³` strictly
above the excursion radius `n/2`. -/
theorem lemma47_half_lt_firstScale_mul_cube
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / 2 < lemma47FirstScale n * (n : ℝ) ^ 3 := by
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold lemma47FirstScale
  field_simp
  nlinarith

/-- The raw Doob error is the simpler square-root/count ratio. -/
theorem lemma47DoobError_eq
    {α : ℝ} {n : ℕ} (hn : 0 < n)
    (hk : 0 < lemma47ExcursionCount α n) :
    lemma47DoobError α n =
      16 * Real.sqrt (n : ℝ) / lemma47ExcursionCount α n := by
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hkReal : 0 < (lemma47ExcursionCount α n : ℝ) :=
    Nat.cast_pos.mpr hk
  have hnSqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hkSqrt : 0 < Real.sqrt (lemma47ExcursionCount α n : ℝ) :=
    Real.sqrt_pos.2 hkReal
  have hRpowSq :
      ((n : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 =
        (Real.sqrt (n : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hnReal)]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg hnReal.le, ← Real.sqrt_eq_rpow]
  unfold lemma47DoobError lemma47DownsideLevel
  rw [div_pow]
  rw [mul_pow, mul_pow]
  rw [Real.sq_sqrt hkReal.le, hRpowSq]
  field_simp
  ring

/-- The Doob probability error tends to zero. -/
theorem tendsto_lemma47DoobError_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (lemma47DoobError α) atTop (𝓝 0) := by
  have hSimple' : Tendsto
      (fun n : ℕ => 16 * Real.sqrt (n : ℝ) /
        lemma47ExcursionCount α n) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      ((tendsto_const_nhds (x := (16 : ℝ))).mul
        (tendsto_sqrt_nat_div_lemma47ExcursionCount hα))
  apply hSimple'.congr'
  filter_upwards [eventually_gt_atTop 0,
    eventually_lemma47ExcursionCount_pos hα] with n hn hk
  exact (lemma47DoobError_eq hn hk).symm

/-- The terminal positive mass converges to `α² / 2`. -/
theorem tendsto_lemma47TerminalMass
    {α : ℝ} (hα : 0 < α) (normBound : ℝ) :
    Tendsto (lemma47TerminalMass α normBound) atTop
      (𝓝 (α ^ 2 / 2)) := by
  change Tendsto
    (fun n : ℕ => lemma47ExcursionMass α normBound n / 2 -
      lemma47DoobError α n) atTop (𝓝 (α ^ 2 / 2))
  simpa only [sub_zero] using
    ((tendsto_lemma47ExcursionMass hα normBound).div_const 2).sub
      (tendsto_lemma47DoobError_zero hα)

/-- All pointwise numerical hypotheses and strict limiting conclusions used
by the final Lemma 4.7 contradiction hold simultaneously after one finite
index. -/
theorem eventually_lemma47ConstructionConditions
    {α : ℝ} (hα : 0 < α) (normBound : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧
      0 < lemma47ExcursionCount α n ∧
      6 * normBound ≤ (n : ℝ) ^ 2 ∧
      (normBound / (n : ℝ)) ^ 2 ≤ α ∧
      0 ≤ lemma47ExcursionMass α normBound n ∧
      α ^ 3 / 8 < lemma47TerminalLevel α normBound n ∧
      α ^ 2 / 4 < lemma47TerminalMass α normBound n := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hJump : ∀ᶠ n : ℕ in atTop,
      6 * normBound ≤ (n : ℝ) ^ 2 :=
    hsq.eventually (eventually_ge_atTop (6 * normBound))
  have hInv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hGainLimit : Tendsto
      (fun n : ℕ => (normBound / (n : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((tendsto_const_nhds (x := normBound)).mul hInv).pow 2
  have hGain : ∀ᶠ n : ℕ in atTop,
      (normBound / (n : ℝ)) ^ 2 ≤ α :=
    (hGainLimit.eventually (Iio_mem_nhds hα)).mono fun _ h => h.le
  have hMassPositive : 0 < α ^ 2 := sq_pos_of_pos hα
  have hMass : ∀ᶠ n : ℕ in atTop,
      0 ≤ lemma47ExcursionMass α normBound n :=
    ((tendsto_lemma47ExcursionMass hα normBound).eventually
      (Ioi_mem_nhds hMassPositive)).mono fun _ h => h.le
  have hLevelLimit : α ^ 3 / 8 < α ^ 3 / 4 := by
    have hCube : 0 < α ^ 3 := pow_pos hα 3
    linarith
  have hLevel : ∀ᶠ n : ℕ in atTop,
      α ^ 3 / 8 < lemma47TerminalLevel α normBound n :=
    (tendsto_lemma47TerminalLevel hα normBound).eventually
      (Ioi_mem_nhds hLevelLimit)
  have hTerminalMassLimit : α ^ 2 / 4 < α ^ 2 / 2 := by
    nlinarith [sq_pos_of_pos hα]
  have hTerminalMass : ∀ᶠ n : ℕ in atTop,
      α ^ 2 / 4 < lemma47TerminalMass α normBound n :=
    (tendsto_lemma47TerminalMass hα normBound).eventually
      (Ioi_mem_nhds hTerminalMassLimit)
  filter_upwards [eventually_gt_atTop 0,
    eventually_lemma47ExcursionCount_pos hα, hJump, hGain, hMass,
    hLevel, hTerminalMass] with n hn hk hJumpn hGainn hMassn hLeveln hTerminalMassn
  exact ⟨hn, hk, hJumpn, hGainn, hMassn, hLeveln, hTerminalMassn⟩

end FTAPTheorem42
