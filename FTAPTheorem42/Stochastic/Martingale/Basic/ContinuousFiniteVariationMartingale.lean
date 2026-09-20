/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation
import Mathlib.Probability.Martingale.Basic

/-!
# Continuous finite-variation martingales

A continuous martingale whose paths have a common finite total-variation
bound is constant up to almost-everywhere equality at every deterministic
time.  The proof samples the martingale on the factorial grids clamped at a
fixed horizon.  Martingale orthogonality identifies the expected sum of
squared increments with the squared terminal increment, while continuity
and bounded variation make the pathwise squared sums converge to zero.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace FTAPTheorem42

namespace ContinuousFiniteVariationMartingale

/-- Sum of squared path increments on the factorial grid clamped at `T`. -/
noncomputable def squaredGridVariation
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r * r.factorial),
    (f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
      f (FiniteVariationFactorialApproximation.point T r k)) ^ 2

theorem squaredGridVariation_nonneg
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (r : ℕ) :
    0 ≤ squaredGridVariation f T r := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Consecutive clamped factorial-grid points are at most one mesh apart. -/
theorem dist_point_succ_point_le
    (T : ℝ≥0) (r k : ℕ) :
    dist
        (FiniteVariationFactorialApproximation.point T r (k + 1))
        (FiniteVariationFactorialApproximation.point T r k) ≤
      ((r.factorial : ℝ)⁻¹) := by
  let q : ℝ := (r.factorial : ℝ)
  have hq : q ≠ 0 := by
    dsimp [q]
    positivity
  have hqPos : 0 < q := by
    dsimp [q]
    positivity
  have hraw :
      |((k + 1 : ℕ) : ℝ) / q - (k : ℝ) / q| = q⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one]
    have hdiff : ((k : ℝ) + 1) / q - (k : ℝ) / q = 1 / q := by
      field_simp
      ring
    rw [hdiff, abs_of_pos (div_pos zero_lt_one hqPos), div_eq_mul_inv,
      one_mul]
  rw [NNReal.dist_eq]
  change
    |min (((k + 1 : ℕ) : ℝ) / q) (T : ℝ) -
        min ((k : ℝ) / q) (T : ℝ)| ≤ q⁻¹
  calc
    |min (((k + 1 : ℕ) : ℝ) / q) (T : ℝ) -
        min ((k : ℝ) / q) (T : ℝ)| ≤
        max
          |((k + 1 : ℕ) : ℝ) / q - (k : ℝ) / q|
          |(T : ℝ) - (T : ℝ)| :=
      abs_min_sub_min_le_max _ _ _ _
    _ = q⁻¹ := by rw [hraw]; simp [inv_nonneg.2 (by positivity : 0 ≤ q)]

/-- The total absolute factorial-grid increment is controlled by any common
upper bound for the path variation. -/
theorem sum_abs_gridIncrement_le
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (r : ℕ) {V : ℝ≥0∞}
    (hV : eVariationOn f Set.univ ≤ V) (hVTop : V ≠ ∞) :
    (∑ k ∈ Finset.range (r * r.factorial),
        |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
          f (FiniteVariationFactorialApproximation.point T r k)|) ≤
      V.toReal := by
  let u : ℕ → ℝ≥0 := FiniteVariationFactorialApproximation.point T r
  have hsum :
      (∑ k ∈ Finset.range (r * r.factorial),
          ENNReal.ofReal |f (u (k + 1)) - f (u k)|) ≤ V := by
    calc
      (∑ k ∈ Finset.range (r * r.factorial),
          ENNReal.ofReal |f (u (k + 1)) - f (u k)|) =
          ∑ k ∈ Finset.range (r * r.factorial),
            edist (f (u (k + 1))) (f (u k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [edist_dist, Real.dist_eq]
      _ ≤ eVariationOn f Set.univ :=
        eVariationOn.sum_le
          (FiniteVariationFactorialApproximation.point_monotone T r)
          (fun _ => Set.mem_univ _)
      _ ≤ V := hV
  have hnonneg :
      0 ≤ ∑ k ∈ Finset.range (r * r.factorial),
        |f (u (k + 1)) - f (u k)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum' :
      ENNReal.ofReal
          (∑ k ∈ Finset.range (r * r.factorial),
            |f (u (k + 1)) - f (u k)|) ≤ V := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact hsum
    · exact fun _ _ => abs_nonneg _
  have hreal := ENNReal.toReal_mono hVTop hsum'
  simpa only [ENNReal.toReal_ofReal hnonneg] using hreal

/-- Every squared factorial-grid variation is bounded by the square of a
common total-variation bound. -/
theorem squaredGridVariation_le
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (r : ℕ) {V : ℝ≥0∞}
    (hV : eVariationOn f Set.univ ≤ V) (hVTop : V ≠ ∞) :
    squaredGridVariation f T r ≤ V.toReal ^ 2 := by
  let a : ℕ → ℝ := fun k =>
    |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
      f (FiniteVariationFactorialApproximation.point T r k)|
  calc
    squaredGridVariation f T r =
        ∑ k ∈ Finset.range (r * r.factorial), a k ^ 2 := by
      unfold squaredGridVariation a
      apply Finset.sum_congr rfl
      intro k _
      rw [sq_abs]
    _ ≤ (∑ k ∈ Finset.range (r * r.factorial), a k) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ V.toReal ^ 2 := by
      gcongr
      exact sum_abs_gridIncrement_le f T r hV hVTop

/-- For a continuous bounded-variation path, the squared increments on the
clamped factorial grids converge to zero. -/
theorem tendsto_squaredGridVariation_zero
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) {V : ℝ≥0∞}
    (hV : eVariationOn f Set.univ ≤ V) (hVTop : V ≠ ∞) :
    Tendsto (fun r => squaredGridVariation f T r) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η : ℝ := ε / (V.toReal + 1)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hUniform : UniformContinuousOn f (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUniform) η hη
  have hfactorial :
      Tendsto (fun r : ℕ => (r.factorial : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  have hmesh :
      Tendsto (fun r : ℕ => ((r.factorial : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfactorial
  have hmeshδ : ∀ᶠ r : ℕ in atTop, (r.factorial : ℝ)⁻¹ < δ :=
    hmesh.eventually_lt_const hδ
  obtain ⟨R, hR⟩ := (eventually_atTop.1 hmeshδ)
  refine ⟨R, fun r hr => ?_⟩
  have hsmall (k : ℕ) :
      |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
          f (FiniteVariationFactorialApproximation.point T r k)| < η := by
    rw [← Real.dist_eq]
    apply hmod
    · exact FiniteVariationFactorialApproximation.point_mem_Icc T r (k + 1)
    · exact FiniteVariationFactorialApproximation.point_mem_Icc T r k
    · exact (dist_point_succ_point_le T r k).trans_lt (hR r hr)
  have hsumSmall :
      squaredGridVariation f T r ≤
        η * ∑ k ∈ Finset.range (r * r.factorial),
          |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
            f (FiniteVariationFactorialApproximation.point T r k)| := by
    unfold squaredGridVariation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    calc
      (f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
          f (FiniteVariationFactorialApproximation.point T r k)) ^ 2 =
          |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
            f (FiniteVariationFactorialApproximation.point T r k)| ^ 2 :=
        (sq_abs _).symm
      _ ≤ η *
          |f (FiniteVariationFactorialApproximation.point T r (k + 1)) -
            f (FiniteVariationFactorialApproximation.point T r k)| := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hsmall k).le (abs_nonneg _)
  have hsumBound := sum_abs_gridIncrement_le f T r hV hVTop
  have hηnonneg : 0 ≤ η := hη.le
  have hlt : η * V.toReal < ε := by
    calc
      η * V.toReal < η * (V.toReal + 1) := by
        exact mul_lt_mul_of_pos_left (lt_add_one _) hη
      _ = ε := by
        dsimp [η]
        field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (squaredGridVariation_nonneg f T r)]
  exact (hsumSmall.trans
    (mul_le_mul_of_nonneg_left hsumBound hηnonneg)).trans_lt hlt

@[simp]
theorem point_zero (T : ℝ≥0) (r : ℕ) :
    FiniteVariationFactorialApproximation.point T r 0 = 0 := by
  simp [FiniteVariationFactorialApproximation.point]

theorem point_gridSize
    (T : ℝ≥0) {r : ℕ} (hr : Nat.ceil T ≤ r) :
    FiniteVariationFactorialApproximation.point T r
        (r * r.factorial) = T := by
  apply min_eq_right
  have hTr : T ≤ (r : ℝ≥0) :=
    (Nat.le_ceil T).trans (by exact_mod_cast hr)
  rw [le_div_iff₀ (by positivity : (0 : ℝ≥0) < r.factorial)]
  calc
    T * (r.factorial : ℝ≥0) ≤
        (r : ℝ≥0) * (r.factorial : ℝ≥0) :=
      mul_le_mul_of_nonneg_right hTr (by positivity)
    _ = ((r * r.factorial : ℕ) : ℝ≥0) := by norm_cast

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {X : ℝ≥0 → Ω → ℝ}

/-- The squared factorial-grid variation is a strongly measurable random
variable. -/
theorem stronglyMeasurable_squaredGridVariation
    (hX : StronglyAdapted ℱ X) (T : ℝ≥0) (r : ℕ) :
    StronglyMeasurable fun ω => squaredGridVariation (fun t => X t ω) T r := by
  unfold squaredGridVariation
  apply (Finset.range (r * r.factorial)).stronglyMeasurable_fun_sum
  intro k _
  have hNext : StronglyMeasurable
      (X (FiniteVariationFactorialApproximation.point T r (k + 1))) :=
    (hX (FiniteVariationFactorialApproximation.point T r (k + 1))).mono
      (ℱ.le (FiniteVariationFactorialApproximation.point T r (k + 1)))
  have hCurrent : StronglyMeasurable
      (X (FiniteVariationFactorialApproximation.point T r k)) :=
    (hX (FiniteVariationFactorialApproximation.point T r k)).mono
      (ℱ.le (FiniteVariationFactorialApproximation.point T r k))
  exact (hNext.sub hCurrent).pow 2

/-! ## Random square-integrable variation bounds -/

omit [IsFiniteMeasure μ] in
/-- An almost-everywhere random variation bound is enough to make every
martingale increment square-integrable. -/
theorem martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    (hX : Martingale X ℱ μ) (V : Ω → ℝ)
    (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    (s t : ℝ≥0) :
    MemLp (fun ω => X t ω - X s ω) (2 : ℝ≥0∞) μ := by
  apply hVMem.mono'
  · exact (((hX.stronglyMeasurable t).mono (ℱ.le t)).sub
      ((hX.stronglyMeasurable s).mono (ℱ.le s))).aestronglyMeasurable
  · filter_upwards [hVNonneg, hV] with ω hVNonnegω hVω
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    have hBounded :
        BoundedVariationOn (fun u => X u ω) Set.univ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hVω
    calc
      dist (X t ω) (X s ω) ≤
          (eVariationOn (fun u => X u ω) Set.univ).toReal :=
        hBounded.dist_le (Set.mem_univ _) (Set.mem_univ _)
      _ ≤ (ENNReal.ofReal (V ω)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hVω
      _ = V ω := ENNReal.toReal_ofReal hVNonnegω

/-- Orthogonality of consecutive martingale increments under an
almost-everywhere square-integrable variation bound. -/
theorem martingale_integral_mul_increment_eq_zero_of_ae_memLp_variation
    (hX : Martingale X ℱ μ) (V : Ω → ℝ)
    (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, (X b ω - X a ω) * (X c ω - X b ω) ∂μ) = 0 := by
  let F : Ω → ℝ := fun ω => X b ω - X a ω
  let G : Ω → ℝ := fun ω => X c ω - X b ω
  have hFMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    hX V hVMem hVNonneg hV a b
  have hGMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    hX V hVMem hVNonneg hV b c
  have hFMeas : StronglyMeasurable[ℱ b] F :=
    (hX.stronglyMeasurable b).sub
      ((hX.stronglyMeasurable a).mono (ℱ.mono hab))
  have hGInt : Integrable G μ := hGMem.integrable (by norm_num)
  have hFGInt : Integrable (F * G) μ := hFMem.integrable_mul hGMem
  have hCondG : μ[G | ℱ b] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hX.integrable c) (hX.integrable b) (ℱ b),
      hX.condExp_ae_eq hbc, hX.condExp_ae_eq (le_refl b)]
        with ω hsub hc hb
    change μ[X c - X b | ℱ b] ω = 0
    rw [hsub]
    change μ[X c | ℱ b] ω - μ[X b | ℱ b] ω = 0
    rw [hc, hb, sub_self]
  have hPull : μ[F * G | ℱ b] =ᵐ[μ] F * μ[G | ℱ b] :=
    condExp_mul_of_stronglyMeasurable_left hFMeas hFGInt hGInt
  calc
    (∫ ω, F ω * G ω ∂μ) = ∫ ω, μ[F * G | ℱ b] ω ∂μ :=
      (integral_condExp (ℱ.le b)).symm
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hPull, hCondG] with ω hpull hzero
      rw [hpull]
      change F ω * μ[G | ℱ b] ω = 0
      simpa only [Pi.zero_apply, mul_zero] using
        congrArg (F ω * ·) hzero
    _ = 0 := by simp

/-- Pythagoras' identity under the same almost-everywhere variation
bound. -/
theorem martingale_integral_sq_sub_eq_add_of_ae_memLp_variation
    (hX : Martingale X ℱ μ) (V : Ω → ℝ)
    (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, (X c ω - X a ω) ^ 2 ∂μ) =
      (∫ ω, (X b ω - X a ω) ^ 2 ∂μ) +
        ∫ ω, (X c ω - X b ω) ^ 2 ∂μ := by
  let U : Ω → ℝ := fun ω => X b ω - X a ω
  let W : Ω → ℝ := fun ω => X c ω - X b ω
  have hUMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    hX V hVMem hVNonneg hV a b
  have hWMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    hX V hVMem hVNonneg hV b c
  have hUInt : Integrable (U ^ 2) μ := hUMem.integrable_sq
  have hWInt : Integrable (W ^ 2) μ := hWMem.integrable_sq
  have hUWInt : Integrable (U * W) μ := hUMem.integrable_mul hWMem
  have hCross : (∫ ω, U ω * W ω ∂μ) = 0 :=
    martingale_integral_mul_increment_eq_zero_of_ae_memLp_variation
      hX V hVMem hVNonneg hV hab hbc
  have hOuterAdd :
      (∫ ω, (U ω ^ 2 + W ω ^ 2) + 2 * (U ω * W ω) ∂μ) =
        (∫ ω, U ω ^ 2 + W ω ^ 2 ∂μ) +
          ∫ ω, 2 * (U ω * W ω) ∂μ := by
    simpa only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul] using integral_add (hUInt.add hWInt) (hUWInt.const_mul 2)
  have hInnerAdd :
      (∫ ω, U ω ^ 2 + W ω ^ 2 ∂μ) =
        (∫ ω, U ω ^ 2 ∂μ) + ∫ ω, W ω ^ 2 ∂μ := by
    simpa only [Pi.add_apply, Pi.pow_apply] using integral_add hUInt hWInt
  have hScale :
      (∫ ω, 2 * (U ω * W ω) ∂μ) =
        2 * ∫ ω, U ω * W ω ∂μ := by
    simpa only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using
      integral_const_mul (μ := μ) 2 (U * W)
  calc
    (∫ ω, (X c ω - X a ω) ^ 2 ∂μ) =
        ∫ ω, U ω ^ 2 + W ω ^ 2 + 2 * (U ω * W ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp [U, W]
        ring
    _ = (∫ ω, U ω ^ 2 ∂μ) + (∫ ω, W ω ^ 2 ∂μ) +
        2 * ∫ ω, U ω * W ω ∂μ := by
      rw [hOuterAdd, hInnerAdd, hScale]
    _ = (∫ ω, U ω ^ 2 ∂μ) + ∫ ω, W ω ^ 2 ∂μ := by
      rw [hCross, mul_zero, add_zero]

/-- Martingale orthogonality telescopes on deterministic grids under an
almost-everywhere random variation bound. -/
theorem martingale_integral_sum_sq_sub_eq_of_ae_memLp_variation
    (hX : Martingale X ℱ μ) (V : Ω → ℝ)
    (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range n,
        (X (u (k + 1)) ω - X (u k) ω) ^ 2 ∂μ) =
      ∫ ω, (X (u n) ω - X (u 0) ω) ^ 2 ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hIncMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
        hX V hVMem hVNonneg hV (u n) (u (n + 1))
      have hSumInt : Integrable (fun ω =>
          ∑ k ∈ Finset.range n,
            (X (u (k + 1)) ω - X (u k) ω) ^ 2) μ :=
        integrable_finsetSum (Finset.range n) fun k _ =>
          (martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
            hX V hVMem hVNonneg hV (u k) (u (k + 1))).integrable_sq
      have hIntegralAdd :
          (∫ ω, (∑ k ∈ Finset.range n,
              (X (u (k + 1)) ω - X (u k) ω) ^ 2) +
              (X (u (n + 1)) ω - X (u n) ω) ^ 2 ∂μ) =
            (∫ ω, ∑ k ∈ Finset.range n,
              (X (u (k + 1)) ω - X (u k) ω) ^ 2 ∂μ) +
              ∫ ω, (X (u (n + 1)) ω - X (u n) ω) ^ 2 ∂μ := by
        simpa only [Pi.add_apply] using integral_add hSumInt hIncMem.integrable_sq
      simp_rw [Finset.sum_range_succ]
      rw [hIntegralAdd, ih]
      exact (martingale_integral_sq_sub_eq_add_of_ae_memLp_variation
        hX V hVMem hVNonneg hV
          (hu (Nat.zero_le n)) (hu (Nat.le_succ n))).symm

/-- Factorial-grid orthogonality under an almost-everywhere random
variation bound. -/
theorem martingale_integral_squaredGridVariation_eq_of_ae_memLp_variation
    (hX : Martingale X ℱ μ) (V : Ω → ℝ)
    (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    (T : ℝ≥0) {r : ℕ} (hr : Nat.ceil T ≤ r) :
    (∫ ω, squaredGridVariation (fun t => X t ω) T r ∂μ) =
      ∫ ω, (X T ω - X 0 ω) ^ 2 ∂μ := by
  have hEq := martingale_integral_sum_sq_sub_eq_of_ae_memLp_variation
    hX V hVMem hVNonneg hV
    (FiniteVariationFactorialApproximation.point T r)
    (FiniteVariationFactorialApproximation.point_monotone T r)
    (r * r.factorial)
  simpa only [squaredGridVariation, point_gridSize T hr, point_zero T r]
    using hEq

/-- A continuous finite-variation rigidity statement in the form needed
after predictable-jump localization.  Continuity, nonnegativity of the
random bound, and the variation estimate may all fail on one null set; the
martingale conclusion is unchanged. -/
theorem martingale_ae_eq_initial_of_ae_continuous_eVariationOn_le_memLp
    (hX : Martingale X ℱ μ)
    (hContinuous : ∀ᵐ ω ∂μ, Continuous fun t => X t ω)
    (V : Ω → ℝ) (hVMem : MemLp V (2 : ℝ≥0∞) μ)
    (hVNonneg : ∀ᵐ ω ∂μ, 0 ≤ V ω)
    (hV : ∀ᵐ ω ∂μ,
      eVariationOn (fun t => X t ω) Set.univ ≤ ENNReal.ofReal (V ω))
    (T : ℝ≥0) :
    X T =ᵐ[μ] X 0 := by
  let Q : ℕ → Ω → ℝ := fun r ω =>
    squaredGridVariation (fun t => X t ω) T r
  have hQMeas (r : ℕ) : AEStronglyMeasurable (Q r) μ :=
    (stronglyMeasurable_squaredGridVariation hX.stronglyAdapted T r).aestronglyMeasurable
  have hQBound (r : ℕ) : ∀ᵐ ω ∂μ, ‖Q r ω‖ ≤ V ω ^ 2 := by
    filter_upwards [hVNonneg, hV] with ω hVNonnegω hVω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (squaredGridVariation_nonneg (fun t => X t ω) T r)]
    calc
      squaredGridVariation (fun t => X t ω) T r ≤
          (ENNReal.ofReal (V ω)).toReal ^ 2 :=
        squaredGridVariation_le (fun t => X t ω) T r
          hVω ENNReal.ofReal_ne_top
      _ = V ω ^ 2 := by rw [ENNReal.toReal_ofReal hVNonnegω]
  have hBoundInt : Integrable (fun ω => V ω ^ 2) μ := hVMem.integrable_sq
  have hQLim : ∀ᵐ ω ∂μ, Tendsto (fun r => Q r ω) atTop (nhds 0) := by
    filter_upwards [hContinuous, hV] with ω hContinuousω hVω
    exact tendsto_squaredGridVariation_zero (fun t => X t ω)
      hContinuousω T hVω ENNReal.ofReal_ne_top
  have hIntegralLim :
      Tendsto (fun r => ∫ ω, Q r ω ∂μ) atTop (nhds 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun ω => V ω ^ 2) hQMeas hBoundInt hQBound hQLim
  let terminalSecondMoment : ℝ := ∫ ω, (X T ω - X 0 ω) ^ 2 ∂μ
  have hEventually : ∀ᶠ r : ℕ in atTop,
      (∫ ω, Q r ω ∂μ) = terminalSecondMoment := by
    filter_upwards [eventually_ge_atTop (Nat.ceil T)] with r hr
    exact martingale_integral_squaredGridVariation_eq_of_ae_memLp_variation
      hX V hVMem hVNonneg hV T hr
  have hConstLim :
      Tendsto (fun _ : ℕ => terminalSecondMoment) atTop (nhds 0) :=
    hIntegralLim.congr' hEventually
  have hTerminalZero : terminalSecondMoment = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hConstLim
  have hDiffMem := martingale_sub_memLp_two_of_ae_eVariationOn_le_memLp
    hX V hVMem hVNonneg hV 0 T
  change (∫ ω, (X T ω - X 0 ω) ^ 2 ∂μ) = 0 at hTerminalZero
  have hSqAE : (fun ω => (X T ω - X 0 ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun ω => sq_nonneg (X T ω - X 0 ω)) hDiffMem.integrable_sq).mp
      hTerminalZero
  filter_upwards [hSqAE] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end ContinuousFiniteVariationMartingale

end FTAPTheorem42
