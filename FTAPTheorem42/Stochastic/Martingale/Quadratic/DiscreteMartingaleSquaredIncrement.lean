/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal

/-!
# Squared increments of discrete square-integrable martingales

For a real discrete martingale `X`, this file records the elementary square
decomposition

`X_n^2 - X_0^2 = 2 * sum_{k<n} X_k (X_{k+1}-X_k)
  + sum_{k<n} (X_{k+1}-X_k)^2`.

The discrete stochastic-integral isometry identifies the expectation of the
last sum with the centered terminal second moment.  If the martingale is
uniformly bounded by a deterministic constant, the squared-increment sum is
bounded in `L^2`, uniformly in the number of grid cells.  This is the finite
grid estimate used by terminal truncation in the general `M^2` quadratic
variation construction.
-/

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The sum of the first `n` squared increments of a discrete process. -/
noncomputable def discreteSquaredIncrementSum
    (X : Nat -> Omega -> Real) (n : Nat) : Omega -> Real :=
  fun omega =>
    ∑ k ∈ Finset.range n, (X (k + 1) omega - X k omega) ^ 2

omit [MeasurableSpace Omega] in
/-- Squared-increment sums are pointwise nonnegative. -/
theorem discreteSquaredIncrementSum_nonneg
    (X : Nat -> Omega -> Real) (n : Nat) (omega : Omega) :
    0 <= discreteSquaredIncrementSum X n omega := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared-increment sums of strongly measurable coordinates are strongly
measurable. -/
theorem discreteSquaredIncrementSum_stronglyMeasurable
    {X : Nat -> Omega -> Real}
    (hX : forall k, StronglyMeasurable (X k)) (n : Nat) :
    StronglyMeasurable (discreteSquaredIncrementSum X n) := by
  unfold discreteSquaredIncrementSum
  apply (Finset.range n).stronglyMeasurable_fun_sum
  intro k _hk
  exact ((hX (k + 1)).sub (hX k)).pow 2

omit [MeasurableSpace Omega] in
/-- The discrete square decomposition. -/
theorem two_mul_discretePredictableIntegral_add_squaredIncrementSum
    (X : Nat -> Omega -> Real) (n : Nat) (omega : Omega) :
    2 * discretePredictableIntegral X X n omega +
        discreteSquaredIncrementSum X n omega =
      X n omega ^ 2 - X 0 omega ^ 2 := by
  unfold discretePredictableIntegral discreteSquaredIncrementSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range n,
        (2 * (X k omega * (X (k + 1) omega - X k omega)) +
          (X (k + 1) omega - X k omega) ^ 2)) =
        ∑ k ∈ Finset.range n,
          (X (k + 1) omega ^ 2 - X k omega ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := Finset.sum_range_sub (fun k => X k omega ^ 2) n

namespace DiscreteMartingaleSquaredIncrement

variable {mu : Measure Omega}
  {F : Filtration Nat (inferInstance : MeasurableSpace Omega)}
  {X : Nat -> Omega -> Real}

/-- A discrete `M^2` martingale has an integrable squared-increment sum. -/
theorem integrable
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    (n : Nat) :
    Integrable (discreteSquaredIncrementSum X n) mu := by
  unfold discreteSquaredIncrementSum
  apply integrable_finsetSum
  intro k _
  exact ((hXLp (k + 1)).sub (hXLp k)).integrable_sq

/-- The expected squared-increment sum equals the centered terminal second
moment. -/
theorem integral_eq_terminalIncrement_sq
    [IsFiniteMeasure mu]
    (hX : Martingale X F mu)
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    (n : Nat) :
    (∫ omega, discreteSquaredIncrementSum X n omega ∂mu) =
      ∫ omega, (X n omega - X 0 omega) ^ 2 ∂mu := by
  have hOneAdapted : StronglyAdapted F
      (fun _ : Nat => fun _ : Omega => (1 : Real)) :=
    fun _ => stronglyMeasurable_const
  have hOneBound : forall _k : Nat, ∀ᵐ _omega : Omega ∂mu,
      |(1 : Real)| <= (1 : Real) :=
    fun _ => Filter.Eventually.of_forall fun _ => by norm_num
  have hIso := DiscretePredictableIntegral.integral_sq_eq_sum
    hX hXLp hOneAdapted hOneBound n
  rw [discretePredictableIntegral_one] at hIso
  unfold discreteSquaredIncrementSum
  rw [integral_finsetSum]
  · simpa only [one_mul, Pi.sub_apply] using hIso.symm
  · intro k hk
    exact ((hXLp (k + 1)).sub (hXLp k)).integrable_sq

/-- The `L^1` seminorm of the nonnegative squared-increment sum is the
square of the `L^2` seminorm of the centered terminal value. -/
theorem eLpNorm_one_eq_terminalIncrement_two_sq
    [IsFiniteMeasure mu]
    (hX : Martingale X F mu)
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    (n : Nat) :
    eLpNorm (discreteSquaredIncrementSum X n) 1 mu =
      eLpNorm (X n - X 0) (2 : ENNReal) mu ^ 2 := by
  have hQInt : Integrable (discreteSquaredIncrementSum X n) mu :=
    integrable hXLp n
  have hCentered : MemLp (X n - X 0) (2 : ENNReal) mu :=
    (hXLp n).sub (hXLp 0)
  have hQNonneg : forall omega,
      0 <= discreteSquaredIncrementSum X n omega :=
    discreteSquaredIncrementSum_nonneg X n
  rw [eLpNorm_one_eq_lintegral_enorm hQInt.aestronglyMeasurable]
  calc
    (∫⁻ omega, ‖discreteSquaredIncrementSum X n omega‖ₑ ∂mu) =
        ENNReal.ofReal
          (∫ omega, discreteSquaredIncrementSum X n omega ∂mu) := by
      rw [ofReal_integral_eq_lintegral_ofReal hQInt
        (Filter.Eventually.of_forall hQNonneg)]
      apply lintegral_congr
      intro omega
      rw [Real.enorm_eq_ofReal (hQNonneg omega)]
    _ = ENNReal.ofReal
        (∫ omega, (X n omega - X 0 omega) ^ 2 ∂mu) := by
      rw [integral_eq_terminalIncrement_sq hX hXLp n]
    _ = ∫⁻ omega, ‖(X n - X 0) omega‖ₑ ^ 2 ∂mu :=
      (DiscretePredictableIntegral.lintegral_enorm_sq_eq_of_memLp_two
        hCentered).symm
    _ = eLpNorm (X n - X 0) (2 : ENNReal) mu ^ 2 := by
      rw [← ENNReal.rpow_natCast]
      calc
        (∫⁻ omega, ‖(X n - X 0) omega‖ₑ ^ (2 : Nat) ∂mu) =
            ∫⁻ omega, ‖(X n - X 0) omega‖ₑ ^ (2 : Real) ∂mu := by
          apply lintegral_congr
          intro omega
          exact (ENNReal.rpow_natCast _ 2).symm
        _ = eLpNorm (X n - X 0) (2 : ENNReal) mu ^ (2 : Real) :=
          (eLpNorm_nnreal_pow_eq_lintegral
            (f := X n - X 0) (μ := mu) (p := (2 : NNReal))
            (by norm_num) hCentered.aestronglyMeasurable).symm

/-- A square-integrable function whose second moment is bounded by `C^2`
has `L^2` seminorm at most `C`. -/
theorem eLpNorm_two_le_of_integral_sq_le
    {f : Omega -> Real} (hf : MemLp f (2 : ENNReal) mu)
    {C : Real} (hC : 0 <= C)
    (hSecond : (∫ omega, f omega ^ 2 ∂mu) <= C ^ 2) :
    eLpNorm f (2 : ENNReal) mu <= ENNReal.ofReal C := by
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top
    ENNReal.ofReal_ne_top).mp
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hf,
    ENNReal.toReal_ofReal hC]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hC, ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using hSecond

/-- For a bounded discrete martingale, its left-endpoint stochastic
integral against itself has a grid-independent `L^2` bound. -/
theorem eLpNorm_discretePredictableIntegral_self_le
    [IsProbabilityMeasure mu]
    (hX : Martingale X F mu)
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    {C : Real} (hC : 0 <= C)
    (hXBound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= C)
    (n : Nat) :
    eLpNorm (discretePredictableIntegral X X n) (2 : ENNReal) mu <=
      ENNReal.ofReal (2 * C ^ 2) := by
  have hI : MemLp (discretePredictableIntegral X X n)
      (2 : ENNReal) mu :=
    DiscretePredictableIntegral.memLp_two hX hXLp hX.stronglyAdapted
      hXBound n
  have hContract :=
    DiscretePredictableIntegral.integral_sq_le_mul_terminalIncrement_sq
      hX hXLp hX.stronglyAdapted hC hXBound n
  have hDiff : Integrable (fun omega =>
      (X n omega - X 0 omega) ^ 2) mu :=
    ((hXLp n).sub (hXLp 0)).integrable_sq
  have hConst : Integrable (fun _ : Omega => (2 * C) ^ 2) mu :=
    integrable_const _
  have hDiffBound : (∫ omega, (X n omega - X 0 omega) ^ 2 ∂mu) <=
      (2 * C) ^ 2 := by
    calc
      (∫ omega, (X n omega - X 0 omega) ^ 2 ∂mu) <=
          ∫ _omega : Omega, (2 * C) ^ 2 ∂mu := by
        apply integral_mono_ae hDiff hConst
        filter_upwards [hXBound n, hXBound 0] with omega hn hzero
        have habs : |X n omega - X 0 omega| <= 2 * C := by
          calc
            |X n omega - X 0 omega| <=
                |X n omega| + |X 0 omega| := abs_sub _ _
            _ <= C + C := add_le_add hn hzero
            _ = 2 * C := by ring
        rw [← sq_abs]
        exact sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hC) |>.2 habs
      _ = (2 * C) ^ 2 := by simp
  have hSecond : (∫ omega,
      discretePredictableIntegral X X n omega ^ 2 ∂mu) <=
      (2 * C ^ 2) ^ 2 := by
    calc
      (∫ omega, discretePredictableIntegral X X n omega ^ 2 ∂mu) <=
          C ^ 2 * ∫ omega, (X n omega - X 0 omega) ^ 2 ∂mu :=
        hContract
      _ <= C ^ 2 * (2 * C) ^ 2 :=
        mul_le_mul_of_nonneg_left hDiffBound (sq_nonneg C)
      _ = (2 * C ^ 2) ^ 2 := by ring
  exact eLpNorm_two_le_of_integral_sq_le hI
    (mul_nonneg (by norm_num) (sq_nonneg C)) hSecond

/-- Under a deterministic pathwise bound, the squared-increment sum is in
`L^2`. -/
theorem memLp_two_of_bounded
    [IsFiniteMeasure mu]
    (hX : Martingale X F mu)
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    {C : Real}
    (hXBound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= C)
    (n : Nat) :
    MemLp (discreteSquaredIncrementSum X n) (2 : ENNReal) mu := by
  have hI : MemLp (discretePredictableIntegral X X n)
      (2 : ENNReal) mu :=
    DiscretePredictableIntegral.memLp_two hX hXLp hX.stronglyAdapted
      hXBound n
  have hXnSq : MemLp (fun omega => X n omega ^ 2)
      (2 : ENNReal) mu := by
    exact MemLp.of_bound
      (((hX.stronglyMeasurable n).mono (F.le n)).aestronglyMeasurable.pow 2)
      (C ^ 2) (by
        filter_upwards [hXBound n] with omega homega
        rw [Real.norm_eq_abs, abs_pow]
        exact sq_le_sq₀ (abs_nonneg _)
          ((abs_nonneg _).trans homega) |>.2 homega)
  have hXzeroSq : MemLp (fun omega => X 0 omega ^ 2)
      (2 : ENNReal) mu := by
    exact MemLp.of_bound
      (((hX.stronglyMeasurable 0).mono (F.le 0)).aestronglyMeasurable.pow 2)
      (C ^ 2) (by
        filter_upwards [hXBound 0] with omega homega
        rw [Real.norm_eq_abs, abs_pow]
        exact sq_le_sq₀ (abs_nonneg _)
          ((abs_nonneg _).trans homega) |>.2 homega)
  have hRight : MemLp (fun omega =>
      X n omega ^ 2 - X 0 omega ^ 2 -
        2 * discretePredictableIntegral X X n omega)
      (2 : ENNReal) mu := by
    exact (hXnSq.sub hXzeroSq).sub (hI.const_mul 2)
  exact hRight.ae_eq (Filter.Eventually.of_forall fun omega => by
      have hIdentity :=
        two_mul_discretePredictableIntegral_add_squaredIncrementSum X n omega
      linarith)

/-- The `L^2` norm of the squared-increment sum of a bounded martingale is
bounded independently of the grid length. -/
theorem eLpNorm_two_le_of_bounded
    [IsProbabilityMeasure mu]
    (hX : Martingale X F mu)
    (hXLp : forall k, MemLp (X k) (2 : ENNReal) mu)
    {C : Real} (hC : 0 <= C)
    (hXBound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= C)
    (n : Nat) :
    eLpNorm (discreteSquaredIncrementSum X n) (2 : ENNReal) mu <=
      ENNReal.ofReal (6 * C ^ 2) := by
  let I : Omega -> Real := discretePredictableIntegral X X n
  let D : Omega -> Real := fun omega => X n omega ^ 2 - X 0 omega ^ 2
  have hQ : MemLp (discreteSquaredIncrementSum X n) (2 : ENNReal) mu :=
    memLp_two_of_bounded hX hXLp hXBound n
  have hI : MemLp I (2 : ENNReal) mu :=
    DiscretePredictableIntegral.memLp_two hX hXLp hX.stronglyAdapted
      hXBound n
  have hDMeas : AEStronglyMeasurable D mu := by
    have hnMeas : StronglyMeasurable (X n) :=
      (hX.stronglyMeasurable n).mono (F.le n)
    have hzeroMeas : StronglyMeasurable (X 0) :=
      (hX.stronglyMeasurable 0).mono (F.le 0)
    exact ((hnMeas.pow 2).sub (hzeroMeas.pow 2)).aestronglyMeasurable
  have hD : MemLp D (2 : ENNReal) mu := by
    exact MemLp.of_bound
      hDMeas
      (2 * C ^ 2) (by
        filter_upwards [hXBound n, hXBound 0] with omega hn hzero
        change |X n omega ^ 2 - X 0 omega ^ 2| <= 2 * C ^ 2
        calc
          |X n omega ^ 2 - X 0 omega ^ 2| <=
              |X n omega ^ 2| + |X 0 omega ^ 2| := abs_sub _ _
          _ = |X n omega| ^ 2 + |X 0 omega| ^ 2 := by
            rw [abs_pow, abs_pow]
          _ <= C ^ 2 + C ^ 2 := by
            exact add_le_add
              (sq_le_sq₀ (abs_nonneg _) hC |>.2 hn)
              (sq_le_sq₀ (abs_nonneg _) hC |>.2 hzero)
          _ = 2 * C ^ 2 := by ring)
  have hDNorm : eLpNorm D (2 : ENNReal) mu <=
      ENNReal.ofReal (2 * C ^ 2) := by
    have hRaw := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
        (f := D) (C := 2 * C ^ 2) hD.aestronglyMeasurable (by
          filter_upwards [hXBound n, hXBound 0] with omega hn hzero
          change |X n omega ^ 2 - X 0 omega ^ 2| <= 2 * C ^ 2
          calc
            |X n omega ^ 2 - X 0 omega ^ 2| <=
                |X n omega ^ 2| + |X 0 omega ^ 2| := abs_sub _ _
            _ = |X n omega| ^ 2 + |X 0 omega| ^ 2 := by
              rw [abs_pow, abs_pow]
            _ <= C ^ 2 + C ^ 2 := by
              exact add_le_add
                (sq_le_sq₀ (abs_nonneg _) hC |>.2 hn)
                (sq_le_sq₀ (abs_nonneg _) hC |>.2 hzero)
            _ = 2 * C ^ 2 := by ring)
    have hMeasureFactor :
        mu Set.univ ^ (2 : ENNReal).toReal⁻¹ = 1 := by
      simp
    rw [hMeasureFactor, one_mul] at hRaw
    exact hRaw
  have hINorm : eLpNorm I (2 : ENNReal) mu <=
      ENNReal.ofReal (2 * C ^ 2) :=
    eLpNorm_discretePredictableIntegral_self_le hX hXLp hC hXBound n
  have hEq : discreteSquaredIncrementSum X n = D - (2 : Real) • I := by
    funext omega
    have hIdentity :=
      two_mul_discretePredictableIntegral_add_squaredIncrementSum X n omega
    change discreteSquaredIncrementSum X n omega =
      (X n omega ^ 2 - X 0 omega ^ 2) -
        2 * discretePredictableIntegral X X n omega
    linarith
  rw [hEq]
  calc
    eLpNorm (D - (2 : Real) • I) (2 : ENNReal) mu <=
        eLpNorm D (2 : ENNReal) mu +
          eLpNorm ((2 : Real) • I) (2 : ENNReal) mu :=
      eLpNorm_sub_le (by norm_num)
    _ <= ENNReal.ofReal (2 * C ^ 2) +
        (2 : ENNReal) * ENNReal.ofReal (2 * C ^ 2) := by
      rw [eLpNorm_const_smul]
      have htwo : ‖(2 : Real)‖ₑ = (2 : ENNReal) := by
        rw [Real.enorm_eq_ofReal (by norm_num : (0 : Real) <= 2)]
        norm_num
      rw [htwo]
      exact add_le_add hDNorm (by
        simpa only [mul_comm] using mul_le_mul_right hINorm (2 : ENNReal))
    _ = ENNReal.ofReal (6 * C ^ 2) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add]
      · congr 1
        ring
      · positivity
      · positivity

end DiscreteMartingaleSquaredIncrement

end FTAPTheorem42
