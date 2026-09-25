/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Martingale.Basic

/-!
# Discrete predictable integrals of square-integrable martingales

For a real discrete martingale `M` and an adapted bounded coefficient
sequence `K`, this file constructs the elementary predictable integral

`sum k < n, K k * (M (k + 1) - M k)`.

The integral is again a true martingale.  Its terminal second moment is the
sum of the second moments of the weighted increments.  The latter identity
is the finite-grid isometry used to construct a genuine predictable control
measure; it is proved from conditional expectation and martingale
orthogonality, rather than postulated as a stochastic-calculus capability.
-/

namespace FTAPTheorem42

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The elementary discrete predictable integral of `K` against `M`. -/
noncomputable def discretePredictableIntegral
    (K M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => ∑ k ∈ Finset.range n,
    K k ω * (M (k + 1) ω - M k ω)

omit [MeasurableSpace Ω] in
@[simp]
theorem discretePredictableIntegral_zero
    (K M : ℕ → Ω → ℝ) :
    discretePredictableIntegral K M 0 = 0 := by
  funext ω
  simp [discretePredictableIntegral]

omit [MeasurableSpace Ω] in
@[simp]
theorem discretePredictableIntegral_succ
    (K M : ℕ → Ω → ℝ) (n : ℕ) :
    discretePredictableIntegral K M (n + 1) =
      discretePredictableIntegral K M n +
        K n * (M (n + 1) - M n) := by
  funext ω
  simp [discretePredictableIntegral, Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
@[simp]
theorem discretePredictableIntegral_succ_sub
    (K M : ℕ → Ω → ℝ) (n : ℕ) :
    discretePredictableIntegral K M (n + 1) -
        discretePredictableIntegral K M n =
      K n * (M (n + 1) - M n) := by
  rw [discretePredictableIntegral_succ]
  abel

omit [MeasurableSpace Ω] in
/-- The discrete integral with constant coefficient one telescopes to the
terminal increment of its integrator. -/
theorem discretePredictableIntegral_one
    (M : ℕ → Ω → ℝ) (n : ℕ) :
    discretePredictableIntegral (fun _ _ => (1 : ℝ)) M n =
      M n - M 0 := by
  funext ω
  unfold discretePredictableIntegral
  simp only [one_mul, Pi.sub_apply]
  exact Finset.sum_range_sub (fun k => M k ω) n

namespace DiscretePredictableIntegral

/-- A discrete integral of two adapted real processes is adapted. -/
theorem stronglyAdapted_of_stronglyAdapted
    {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {K X : Nat → Ω → Real}
    (hK : StronglyAdapted F K) (hX : StronglyAdapted F X) :
    StronglyAdapted F (discretePredictableIntegral K X) := by
  intro n
  unfold discretePredictableIntegral
  have hSum : StronglyMeasurable[F n]
      ((∑ k ∈ Finset.range n,
        K k * (X (k + 1) - X k)) : Ω → Real) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    exact ((hK k).mono (F.mono hk.le)).mul
      (((hX (k + 1)).mono (F.mono (Nat.succ_le_of_lt hk))).sub
        ((hX k).mono (F.mono hk.le)))
  convert hSum using 1
  funext omega
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

variable {μ : Measure Ω}
  {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
  {K M : ℕ → Ω → ℝ} {C : ℕ → ℝ}

/-- For a real `L²` function, the squared extended-norm integral is the
nonnegative-real lift of its ordinary second moment. -/
theorem lintegral_enorm_sq_eq_of_memLp_two
    {f : Ω → ℝ} (hf : MemLp f (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))]
  apply lintegral_congr
  intro ω
  rw [← sq_abs (f ω), ← Real.norm_eq_abs, ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg (f ω))]

/-- One weighted martingale increment is square integrable when its
coefficient has a deterministic bound. -/
theorem increment_memLp_two
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    MemLp (K n * (M (n + 1) - M n)) (2 : ℝ≥0∞) μ := by
  have hMIncrement : MemLp (M (n + 1) - M n) (2 : ℝ≥0∞) μ :=
    (hMLp (n + 1)).sub (hMLp n)
  have hProductMeas : AEStronglyMeasurable
      (K n * (M (n + 1) - M n)) μ :=
    (((hK n).mono (ℱ.le n)).mul
      (((hM.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))).sub
        ((hM.stronglyMeasurable n).mono (ℱ.le n)))).aestronglyMeasurable
  refine MemLp.of_le_mul (c := C n) hMIncrement hProductMeas ?_
  filter_upwards [hKBound n] with ω hBound
  rw [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_mul,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hBound (abs_nonneg _)

/-- Every finite-time value of the discrete predictable integral is in
`L²`. -/
theorem memLp_two
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    MemLp (discretePredictableIntegral K M n) (2 : ℝ≥0∞) μ := by
  unfold discretePredictableIntegral
  apply memLp_finsetSum
  intro k hk
  exact increment_memLp_two hM hMLp hK hKBound k

/-- The elementary predictable integral is adapted to the same discrete
filtration. -/
theorem stronglyAdapted
    (hM : Martingale M ℱ μ)
  (hK : StronglyAdapted ℱ K) :
    StronglyAdapted ℱ (discretePredictableIntegral K M) := by
  exact stronglyAdapted_of_stronglyAdapted hK hM.stronglyAdapted

/-- A bounded adapted coefficient needs only the first moment of its integrator. -/
theorem increment_integrable
    (hM : Martingale M ℱ μ) (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n) (n : ℕ) :
    Integrable (K n * (M (n + 1) - M n)) μ := by
  apply ((hM.integrable (n + 1)).sub (hM.integrable n)).bdd_mul
    ((hK n).mono (ℱ.le n)).aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using hKBound n

/-- The conditional expectation of one weighted martingale increment is
zero at its left endpoint. -/
theorem condExp_increment_eq_zero
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    μ[K n * (M (n + 1) - M n) | ℱ n] =ᵐ[μ] 0 := by
  have hMIncrementInt : Integrable (M (n + 1) - M n) μ :=
    (hM.integrable (n + 1)).sub (hM.integrable n)
  have hProductInt : Integrable
      (K n * (M (n + 1) - M n)) μ :=
    increment_integrable hM hK hKBound n
  have hPull := condExp_mul_of_stronglyMeasurable_left
    (hK n) hProductInt hMIncrementInt
  have hIncrementZero : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hM.integrable (n + 1))
      (hM.integrable n) (ℱ n), hM.condExp_ae_eq (Nat.le_succ n),
      hM.condExp_ae_eq (le_refl n)] with ω hsub hnext hnow
    change μ[M (n + 1) - M n | ℱ n] ω = 0
    rw [hsub]
    change μ[M (n + 1) | ℱ n] ω - μ[M n | ℱ n] ω = 0
    rw [hnext, hnow, sub_self]
  filter_upwards [hPull, hIncrementZero] with ω hPullω hZero
  rw [hPullω]
  change K n ω * μ[M (n + 1) - M n | ℱ n] ω = 0
  rw [hZero]
  simp only [Pi.zero_apply, mul_zero]

/-- Bounded adapted coefficients transform a discrete square-integrable
martingale into a true martingale. -/
theorem isMartingale
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n) :
    Martingale (discretePredictableIntegral K M) ℱ μ := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (stronglyAdapted hM hK)
  · intro n
    exact (memLp_two hM hMLp hK hKBound n).integrable
      (by norm_num)
  · intro n
    rw [discretePredictableIntegral_succ_sub]
    exact condExp_increment_eq_zero hM hK hKBound n

/-- The accumulated predictable integral is orthogonal to its next weighted
martingale increment. -/
theorem integral_mul_nextIncrement_eq_zero
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    (∫ ω, discretePredictableIntegral K M n ω *
      (K n ω * (M (n + 1) ω - M n ω)) ∂μ) = 0 := by
  let I : Ω → ℝ := discretePredictableIntegral K M n
  let Z : Ω → ℝ := K n * (M (n + 1) - M n)
  have hIMem : MemLp I (2 : ℝ≥0∞) μ :=
    memLp_two hM hMLp hK hKBound n
  have hZMem : MemLp Z (2 : ℝ≥0∞) μ :=
    increment_memLp_two hM hMLp hK hKBound n
  have hI_meas : StronglyMeasurable[ℱ n] I :=
    stronglyAdapted hM hK n
  have hZInt : Integrable Z μ := hZMem.integrable (by norm_num)
  have hIZInt : Integrable (I * Z) μ := hIMem.integrable_mul hZMem
  have hCondZ : μ[Z | ℱ n] =ᵐ[μ] 0 :=
    condExp_increment_eq_zero hM hK hKBound n
  have hPull : μ[I * Z | ℱ n] =ᵐ[μ] I * μ[Z | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left hI_meas hIZInt hZInt
  change (∫ ω, I ω * Z ω ∂μ) = 0
  calc
    (∫ ω, I ω * Z ω ∂μ) = ∫ ω, μ[I * Z | ℱ n] ω ∂μ :=
      (integral_condExp (ℱ.le n)).symm
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hPull, hCondZ] with ω hPullω hZero
      rw [hPullω]
      change I ω * μ[Z | ℱ n] ω = 0
      rw [hZero]
      simp only [Pi.zero_apply, mul_zero]
    _ = 0 := by simp

/-- Finite-grid stochastic-integral isometry in second-moment form. -/
theorem integral_sq_eq_sum
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    (∫ ω, (discretePredictableIntegral K M n ω) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n,
        ∫ ω, (K k ω * (M (k + 1) ω - M k ω)) ^ 2 ∂μ := by
  induction n with
  | zero => simp [discretePredictableIntegral]
  | succ n ih =>
      let I : Ω → ℝ := discretePredictableIntegral K M n
      let Z : Ω → ℝ := K n * (M (n + 1) - M n)
      have hIMem : MemLp I (2 : ℝ≥0∞) μ :=
        memLp_two hM hMLp hK hKBound n
      have hZMem : MemLp Z (2 : ℝ≥0∞) μ :=
        increment_memLp_two hM hMLp hK hKBound n
      have hISqInt : Integrable (I ^ 2) μ := hIMem.integrable_sq
      have hZSqInt : Integrable (Z ^ 2) μ := hZMem.integrable_sq
      have hIZInt : Integrable (I * Z) μ := hIMem.integrable_mul hZMem
      have hCross : (∫ ω, I ω * Z ω ∂μ) = 0 :=
        integral_mul_nextIncrement_eq_zero hM hMLp hK hKBound n
      have hOuterAdd :
          (∫ ω, (I ω ^ 2 + Z ω ^ 2) + 2 * (I ω * Z ω) ∂μ) =
            (∫ ω, I ω ^ 2 + Z ω ^ 2 ∂μ) +
              ∫ ω, 2 * (I ω * Z ω) ∂μ := by
        simpa only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply,
          Pi.smul_apply, smul_eq_mul] using
          integral_add (hISqInt.add hZSqInt) (hIZInt.const_mul 2)
      have hInnerAdd :
          (∫ ω, I ω ^ 2 + Z ω ^ 2 ∂μ) =
            (∫ ω, I ω ^ 2 ∂μ) + ∫ ω, Z ω ^ 2 ∂μ := by
        simpa only [Pi.add_apply, Pi.pow_apply] using
          integral_add hISqInt hZSqInt
      have hScale :
          (∫ ω, 2 * (I ω * Z ω) ∂μ) =
            2 * ∫ ω, I ω * Z ω ∂μ := by
        simpa only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using
          integral_const_mul (μ := μ) 2 (I * Z)
      rw [discretePredictableIntegral_succ, Finset.sum_range_succ]
      change (∫ ω, (I ω + Z ω) ^ 2 ∂μ) = _
      calc
        (∫ ω, (I ω + Z ω) ^ 2 ∂μ) =
            ∫ ω, (I ω ^ 2 + Z ω ^ 2) + 2 * (I ω * Z ω) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by ring
        _ = (∫ ω, I ω ^ 2 ∂μ) + (∫ ω, Z ω ^ 2 ∂μ) +
              2 * ∫ ω, I ω * Z ω ∂μ := by
          rw [hOuterAdd, hInnerAdd, hScale]
        _ = (∫ ω, I ω ^ 2 ∂μ) + ∫ ω, Z ω ^ 2 ∂μ := by
          rw [hCross, mul_zero, add_zero]
        _ = (∑ k ∈ Finset.range n,
              ∫ ω, (K k ω * (M (k + 1) ω - M k ω)) ^ 2 ∂μ) +
              ∫ ω, (K n ω * (M (n + 1) ω - M n ω)) ^ 2 ∂μ := by
          rw [ih]
          rfl
        _ = _ := by rfl

/-- Finite-grid stochastic-integral isometry in the nonnegative integral
form used by predictable control measures. -/
theorem lintegral_enorm_sq_eq_sum
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C n)
    (n : ℕ) :
    (∫⁻ ω, ‖discretePredictableIntegral K M n ω‖ₑ ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n,
        ∫⁻ ω, ‖K k ω * (M (k + 1) ω - M k ω)‖ₑ ^ 2 ∂μ := by
  have hIntegralMem : MemLp (discretePredictableIntegral K M n)
      (2 : ℝ≥0∞) μ := memLp_two hM hMLp hK hKBound n
  rw [lintegral_enorm_sq_eq_of_memLp_two hIntegralMem]
  have hTermMem (k : ℕ) : MemLp
      (K k * (M (k + 1) - M k)) (2 : ℝ≥0∞) μ :=
    increment_memLp_two hM hMLp hK hKBound k
  have hTermMem' (k : ℕ) : MemLp
      (fun ω => K k ω * (M (k + 1) ω - M k ω))
        (2 : ℝ≥0∞) μ := by
    have hEq :
        (fun ω => K k ω * (M (k + 1) ω - M k ω)) =
          K k * (M (k + 1) - M k) := by
      funext ω
      rfl
    rw [hEq]
    exact hTermMem k
  have hTermLIntegral (k : ℕ) :
      (∫⁻ ω, ‖K k ω * (M (k + 1) ω - M k ω)‖ₑ ^ 2 ∂μ) =
        ENNReal.ofReal
          (∫ ω, (K k ω * (M (k + 1) ω - M k ω)) ^ 2 ∂μ) :=
    lintegral_enorm_sq_eq_of_memLp_two (hTermMem' k)
  have hTermNonneg (k : ℕ) :
      0 ≤ ∫ ω, (K k ω * (M (k + 1) ω - M k ω)) ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  simp_rw [hTermLIntegral]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact congrArg ENNReal.ofReal
      (integral_sq_eq_sum hM hMLp hK hKBound n)
  · intro k _
    exact hTermNonneg k

/-- A deterministic bound on an adapted coefficient contracts the terminal
second moment of the discrete integral by that bound. -/
theorem integral_sq_le_mul_terminalIncrement_sq
    [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ n, MemLp (M n) (2 : ℝ≥0∞) μ)
    (hK : StronglyAdapted ℱ K) {B : ℝ} (hB : 0 <= B)
    (hKBound : ∀ n, ∀ᵐ ω ∂μ, |K n ω| <= B)
    (n : ℕ) :
    (∫ ω, (discretePredictableIntegral K M n ω) ^ 2 ∂μ) <=
      B ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  have hOneAdapted : StronglyAdapted ℱ
      (fun _ : ℕ => fun _ : Ω => (1 : ℝ)) :=
    fun _ => stronglyMeasurable_const
  have hOneBound : ∀ _k : ℕ, ∀ᵐ _omega : Ω ∂μ,
      |(1 : ℝ)| <= (1 : ℝ) :=
    fun _ => Filter.Eventually.of_forall fun _ => by norm_num
  have hIncrementSum :
      (∑ k ∈ Finset.range n,
          ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) =
        ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
    have hIso := integral_sq_eq_sum hM hMLp hOneAdapted hOneBound n
    simpa only [discretePredictableIntegral_one, one_mul, Pi.sub_apply]
      using hIso.symm
  rw [integral_sq_eq_sum hM hMLp hK hKBound n]
  calc
    (∑ k ∈ Finset.range n,
        ∫ ω, (K k ω * (M (k + 1) ω - M k ω)) ^ 2 ∂μ) <=
        ∑ k ∈ Finset.range n,
          B ^ 2 * ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro k _
      have hDeltaMem : MemLp (M (k + 1) - M k)
          (2 : ℝ≥0∞) μ := (hMLp (k + 1)).sub (hMLp k)
      have hWeightedMem : MemLp
          (K k * (M (k + 1) - M k)) (2 : ℝ≥0∞) μ :=
        increment_memLp_two hM hMLp hK hKBound k
      have hWeightedInt : Integrable (fun ω =>
          (K k ω * (M (k + 1) ω - M k ω)) ^ 2) μ := by
        simpa only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] using
          hWeightedMem.integrable_sq
      have hDeltaInt : Integrable (fun ω =>
          B ^ 2 * (M (k + 1) ω - M k ω) ^ 2) μ := by
        exact hDeltaMem.integrable_sq.const_mul (B ^ 2)
      rw [← integral_const_mul]
      apply integral_mono_ae hWeightedInt hDeltaInt
      filter_upwards [hKBound k] with ω hKω
      have hKsq : K k ω ^ 2 <= B ^ 2 := by
        rw [← sq_abs (K k ω), ← sq_abs B, abs_of_nonneg hB]
        exact sq_le_sq₀ (abs_nonneg _) hB |>.2 hKω
      calc
        (K k ω * (M (k + 1) ω - M k ω)) ^ 2 =
            K k ω ^ 2 * (M (k + 1) ω - M k ω) ^ 2 := by ring
        _ <= B ^ 2 * (M (k + 1) ω - M k ω) ^ 2 :=
          mul_le_mul_of_nonneg_right hKsq (sq_nonneg _)
    _ = B ^ 2 * ∑ k ∈ Finset.range n,
        ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
      rw [Finset.mul_sum]
    _ = _ := by rw [hIncrementSum]

end DiscretePredictableIntegral

end FTAPTheorem42

namespace FTAPTheorem42.DiscretePredictableIntegral

/-! ## Bounded predictable transforms of integrable discrete martingales -/

open MeasureTheory

theorem isMartingale_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {K M : Nat → Ω → Real} {C : Nat → Real}
    (hM : Martingale M F mu) (hK : StronglyAdapted F K)
    (hBound : ∀ n, ∀ᵐ w ∂mu, |K n w| ≤ C n) :
    Martingale (discretePredictableIntegral K M) F mu := by
  apply martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted hM hK)
  · intro n
    apply integrable_finsetSum
    exact fun k _ => increment_integrable hM hK hBound k
  · intro n
    rw [discretePredictableIntegral_succ_sub]
    exact condExp_increment_eq_zero hM hK hBound n

end FTAPTheorem42.DiscretePredictableIntegral
