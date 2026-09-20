/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessTerminal
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Process.UniformLimits

/-!
# Completing finite-variation integral processes

The common predictable simple approximations converge in the canonical
variation `L¹` space.  This module turns that product-space convergence into
pathwise control of the associated cumulative finite-variation integrals.
The first step is the sharp variation estimate: the whole-path variation of
the difference of two cumulative integrals is bounded by the pathwise
`L¹(d|A|)` distance of their coefficients.
-/

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- Uniform convergence of bounded-variation paths also converges their
limits at `+∞`.  This is the deterministic interchange needed to identify
the terminal value of the completed finite-variation process. -/
theorem tendsto_limUnder_atTop_of_tendstoUniformly_boundedVariation
    (F : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ)
    (hF : ∀ n, BoundedVariationOn (F n) Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (hUniform : TendstoUniformly F g atTop) :
    Tendsto (fun n => limUnder atTop (F n)) atTop
      (𝓝 (limUnder atTop g)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hHalf : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Metric.tendstoUniformly_iff.mp hUniform) (ε / 2) hHalf)
  refine ⟨N, fun n hn => ?_⟩
  have hDistance : Tendsto (fun t => dist (F n t) (g t)) atTop
      (𝓝 (dist (limUnder atTop (F n)) (limUnder atTop g))) :=
    (hF n).tendsto_atTop_limUnder.dist hg.tendsto_atTop_limUnder
  have hLe : dist (limUnder atTop (F n)) (limUnder atTop g) ≤ ε / 2 :=
    le_of_tendsto hDistance (Eventually.of_forall fun t => by
      simpa only [dist_comm] using (hN n hn t).le)
  exact hLe.trans_lt (half_lt_self hε)

/-- Cumulative finite-variation integration is linear under subtraction for
bounded predictable coefficients. -/
theorem finiteVariationIntegralProcess_sub_coeff
    (E : SIntegrableFiniteVariationBridge H)
    {K L : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (hL : IsStronglyPredictable ℱ L)
    {C D : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hLBound : ∀ t ω, |L t ω| ≤ D) :
    finiteVariationIntegralProcess E (K - L) =
      finiteVariationIntegralProcess E K -
        finiteVariationIntegralProcess E L := by
  funext T ω
  have hKInt : Integrable
      (fun t => finiteVariationIntegralDensity E K (t, ω))
      (pathVariationMeasureUpTo E T ω) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      (integrable_finiteVariationIntegralDensity_section
        E hK hKBound ω).integrableOn
  have hLInt : Integrable
      (fun t => finiteVariationIntegralDensity E L (t, ω))
      (pathVariationMeasureUpTo E T ω) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      (integrable_finiteVariationIntegralDensity_section
        E hL hLBound ω).integrableOn
  change (∫ t, finiteVariationIntegralDensity E (K - L) (t, ω)
      ∂pathVariationMeasureUpTo E T ω) =
    (∫ t, finiteVariationIntegralDensity E K (t, ω)
      ∂pathVariationMeasureUpTo E T ω) -
    ∫ t, finiteVariationIntegralDensity E L (t, ω)
      ∂pathVariationMeasureUpTo E T ω
  rw [← integral_sub hKInt hLInt]
  apply integral_congr_ae
  filter_upwards with t
  simp only [finiteVariationIntegralDensity, Pi.sub_apply]
  ring

/-- The whole-path variation of the difference of two cumulative integrals
is bounded by the pathwise `L¹(d|A|)` distance of their coefficients. -/
theorem eVariationOn_finiteVariationIntegralProcess_sub_le_lintegral
    (E : SIntegrableFiniteVariationBridge H)
    {K L : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (hL : IsStronglyPredictable ℱ L)
    {C D : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hLBound : ∀ t ω, |L t ω| ≤ D) (ω : Ω) :
    eVariationOn (fun t =>
        finiteVariationIntegralProcess E K t ω -
          finiteVariationIntegralProcess E L t ω) Set.univ ≤
      ∫⁻ t, ‖K t ω - L t ω‖ₑ
        ∂(FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let P : Process Ω := K - L
  have hP : IsStronglyPredictable ℱ P := hK.sub hL
  have hPBound : ∀ t ω, |P t ω| ≤ C + D := by
    intro t ω
    exact (abs_sub (K t ω) (L t ω)).trans
      (add_le_add (hKBound t ω) (hLBound t ω))
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let B : ℝ≥0 → ℝ := fun t => finiteVariationIntegralProcess E P t ω
  let hB : BoundedVariationOn B Set.univ :=
    finiteVariationIntegralProcess_isBoundedVariation E hP hPBound ω
  have hBRight : ∀ t, ContinuousWithinAt B (Set.Ici t) t :=
    finiteVariationIntegralProcess_rightContinuous E hP hPBound ω
  have hDensityInt : Integrable
      (fun t => finiteVariationIntegralDensity E P (t, ω)) ν :=
    integrable_finiteVariationIntegralDensity_section E hP hPBound ω
  have hPathEq : (fun t =>
      finiteVariationIntegralProcess E K t ω -
        finiteVariationIntegralProcess E L t ω) = B := by
    funext t
    exact congrFun (congrFun
      (finiteVariationIntegralProcess_sub_coeff
        E hK hL hKBound hLBound) t) ω |>.symm
  rw [hPathEq]
  calc
    eVariationOn B Set.univ ≤
        (FiniteVariationPath.signedMeasure hB).variation Set.univ :=
      FiniteVariationPath.eVariationOn_univ_le_variation_univ hB hBRight
    _ = (ν.withDensityᵥ
          (fun t => finiteVariationIntegralDensity E P (t, ω))).variation
            Set.univ := by
      rw [signedMeasure_finiteVariationIntegralProcess_eq_withDensity
        E hP hPBound ω]
    _ = (ν.withDensity fun t =>
          ‖finiteVariationIntegralDensity E P (t, ω)‖ₑ) Set.univ := by
      rw [Measure.variation_withDensityᵥ hDensityInt]
    _ = ∫⁻ t, ‖finiteVariationIntegralDensity E P (t, ω)‖ₑ ∂ν := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ ≤ ∫⁻ t, ‖K t ω - L t ω‖ₑ ∂ν := by
      apply lintegral_mono
      intro t
      change ‖jumpCorrectedCanonicalVariationDensity E (t, ω) *
        (K t ω - L t ω)‖ₑ ≤ ‖K t ω - L t ω‖ₑ
      rw [enorm_mul]
      calc
        ‖jumpCorrectedCanonicalVariationDensity E (t, ω)‖ₑ *
            ‖K t ω - L t ω‖ₑ ≤
            1 * ‖K t ω - L t ω‖ₑ := by
          apply mul_le_mul_left
          rw [Real.enorm_eq_ofReal_abs]
          exact (ENNReal.ofReal_le_one.mpr
            (abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, ω)))
        _ = ‖K t ω - L t ω‖ₑ := one_mul _

/-- The same pathwise `L¹(d|A|)` distance controls every fixed-time
distance of the two cumulative integral processes. -/
theorem dist_finiteVariationIntegralProcess_le_lintegral_toReal
    (E : SIntegrableFiniteVariationBridge H)
    {K L : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (hL : IsStronglyPredictable ℱ L)
    {C D : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hLBound : ∀ t ω, |L t ω| ≤ D) (ω : Ω) (t : ℝ≥0) :
    dist (finiteVariationIntegralProcess E K t ω)
        (finiteVariationIntegralProcess E L t ω) ≤
      (∫⁻ u, ‖K u ω - L u ω‖ₑ
        ∂(FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation).toReal := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let P : ℝ≥0 → ℝ := fun u =>
    finiteVariationIntegralProcess E K u ω -
      finiteVariationIntegralProcess E L u ω
  have hVariation :=
    eVariationOn_finiteVariationIntegralProcess_sub_le_lintegral
      E hK hL hKBound hLBound ω
  have hSection : StronglyMeasurable fun u => K u ω - L u ω :=
    ((hK.sub hL).mono
      (PredictableKernelMeasure.predictable_le_prod ℱ))
      |>.comp_measurable measurable_prodMk_right
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hSectionInt : Integrable (fun u => K u ω - L u ω) ν := by
    apply (integrable_const (C + D)).mono' hSection.aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_eq_abs]
    exact (abs_sub (K u ω) (L u ω)).trans
      (add_le_add (hKBound u ω) (hLBound u ω))
  have hIntegralFinite :
      (∫⁻ u, ‖K u ω - L u ω‖ₑ ∂ν) ≠ ∞ := hSectionInt.2.ne
  have hPVariation : BoundedVariationOn P Set.univ :=
    ne_top_of_le_ne_top hIntegralFinite hVariation
  have hPZero : P 0 = 0 := by
    simp [P, finiteVariationIntegralProcess, pathVariationMeasureUpTo]
  calc
    dist (finiteVariationIntegralProcess E K t ω)
        (finiteVariationIntegralProcess E L t ω) = |P t - P 0| := by
      rw [hPZero, sub_zero, Real.dist_eq]
    _ ≤ (eVariationOn P Set.univ).toReal :=
      FiniteVariationPath.abs_sub_le_variation hPVariation t 0
    _ ≤ (∫⁻ u, ‖K u ω - L u ω‖ₑ ∂ν).toReal :=
      ENNReal.toReal_mono hIntegralFinite hVariation

/-- The cumulative process obtained from one member of the common
predictable simple approximation. -/
noncomputable def commonFiniteVariationProcessApproximation
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    Process Ω :=
  finiteVariationIntegralProcess E
    (predictableCommonSimpleApproximation f hf n)

/-- A subsequence of the common simple approximations has a predictable,
right-continuous bounded-variation process limit.  The convergence is
uniform on the whole time axis outside one null set, and the whole-path
variation of the error tends to zero there. -/
theorem exists_commonFiniteVariationProcessLimit
    [IsProbabilityMeasure μ]
    (hUsual : Filtration.UsualConditions μ ℱ)
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      ∃ B : Process Ω,
        IsStronglyPredictable ℱ B ∧
          (∀ ω t, ContinuousWithinAt (B · ω) (Set.Ici t) t) ∧
          (∀ ω, BoundedVariationOn (B · ω) Set.univ) ∧
          (∀ᵐ ω ∂μ,
            TendstoUniformly
              (fun n t => commonFiniteVariationProcessApproximation
                E f hf (cutoff n) t ω)
              (fun t => B t ω) atTop ∧
            Tendsto (fun n => eVariationOn (fun t =>
                B t ω - commonFiniteVariationProcessApproximation
                  E f hf (cutoff n) t ω) Set.univ)
              atTop (𝓝 0)) ∧
          ∃ hBTerminal : MemLp
              (fun ω => limUnder atTop (fun t => B t ω)) 1
                E.referenceMeasure,
            hBTerminal.toLp
                (fun ω => limUnder atTop (fun t => B t ω)) =
              finiteVariationTerminalIntegralLp E f hf hF := by
  let K : ℕ → Process Ω := fun n =>
    predictableCommonSimpleApproximation f hf n
  let hKMem : ∀ n, MemLp (Function.uncurry (K n)) 1
      (canonicalVariationMeasure E) := fun n => by
    simpa only [K, uncurry_predictableCommonSimpleApproximation] using
      predictableCommonSimpleApproximationRaw_memLp f hf
        (canonicalVariationMeasure E) 1 hF n
  let F : ℕ → Lp ℝ 1 (canonicalVariationMeasure E) := fun n =>
    (hKMem n).toLp (Function.uncurry (K n))
  have hFTendsto : Tendsto F atTop
      (𝓝 (hF.toLp (Function.uncurry f))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => Function.uncurry (K n)) hKMem
      (Function.uncurry f) hF).mpr
    simpa only [K, uncurry_predictableCommonSimpleApproximation] using
      predictableCommonSimpleApproximationRaw_tendsto_eLpNorm
        f hf (canonicalVariationMeasure E) 1 (by norm_num) hF
  obtain ⟨cutoff, hCutoff, hDistanceSummable⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq F hFTendsto.cauchySeq
  let step : ℕ → ℝ≥0 × Ω → ℝ≥0∞ := fun n p =>
    ‖K (cutoff (n + 1)) p.1 p.2 - K (cutoff n) p.1 p.2‖ₑ
  have hStepMeasurable : ∀ n, Measurable[ℱ.predictable] (step n) := by
    intro n
    exact ((predictableCommonSimpleApproximation_isStronglyPredictable
      f hf (cutoff (n + 1))).sub
        (predictableCommonSimpleApproximation_isStronglyPredictable
          f hf (cutoff n))).enorm
  have hStepNorm : ∀ n,
      (∫⁻ p, step n p ∂canonicalVariationMeasure E) =
        ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) := by
    intro n
    calc
      (∫⁻ p, step n p ∂canonicalVariationMeasure E) =
          eLpNorm (fun p =>
            Function.uncurry (K (cutoff (n + 1))) p -
              Function.uncurry (K (cutoff n)) p)
            1 (canonicalVariationMeasure E) := by
        rw [eLpNorm_one_eq_lintegral_enorm (f := fun p =>
          Function.uncurry (K (cutoff (n + 1))) p - Function.uncurry (K (cutoff n)) p)
          (by exact ((hKMem (cutoff (n + 1))).sub
            (hKMem (cutoff n))).aestronglyMeasurable)]
        rfl
      _ = edist (F (cutoff (n + 1))) (F (cutoff n)) := by
        exact (Lp.edist_toLp_toLp
          (Function.uncurry (K (cutoff (n + 1))))
          (Function.uncurry (K (cutoff n)))
          (hKMem (cutoff (n + 1))) (hKMem (cutoff n))).symm
      _ = ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) :=
        Lp.edist_dist _ _
  have hStepTsum :
      (∑' n, ∫⁻ p, step n p ∂canonicalVariationMeasure E) ≠ ∞ := by
    rw [show (fun n => ∫⁻ p, step n p ∂canonicalVariationMeasure E) =
        fun n => ENNReal.ofReal
          (dist (F (cutoff (n + 1))) (F (cutoff n))) by
      funext n
      exact hStepNorm n]
    exact hDistanceSummable.tsum_ofReal_ne_top
  let pathStep : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t, step n (t, ω)
      ∂(FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let weightedStep : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    (E.referenceDensity ω : ℝ≥0∞) * pathStep n ω
  have hWeightedStepMeasurable : ∀ n, Measurable (weightedStep n) := by
    intro n
    let κ := canonicalTotalVariationKernel E
    let : IsFiniteKernel κ :=
      canonicalTotalVariationKernel.instIsFiniteKernel E
    have hProduct : Measurable (step n) :=
      (hStepMeasurable n).mono
        (PredictableKernelMeasure.predictable_le_prod ℱ) le_rfl
    have hKernel : Measurable fun ω =>
        ∫⁻ t, step n (t, ω) ∂κ ω := by
      exact (hProduct.comp measurable_swap).lintegral_kernel_prod_right'
    convert hKernel using 1
    funext ω
    rw [canonicalTotalVariationKernel_apply, lintegral_smul_measure]
    rfl
  have hWeightedTsum :
      (∑' n, ∫⁻ ω, weightedStep n ω ∂μ) ≠ ∞ := by
    rw [← show (fun n => ∫⁻ p, step n p
        ∂canonicalVariationMeasure E) =
      fun n => ∫⁻ ω, weightedStep n ω ∂μ by
        funext n
        exact lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
          E (hStepMeasurable n)]
    exact hStepTsum
  have hWeightedIntegral :
      (∫⁻ ω, ∑' n, weightedStep n ω ∂μ) ≠ ∞ := by
    rw [lintegral_tsum fun n =>
      (hWeightedStepMeasurable n).aemeasurable]
    exact hWeightedTsum
  have hWeightedFinite : ∀ᵐ ω ∂μ,
      (∑' n, weightedStep n ω) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun n =>
      (hWeightedStepMeasurable n).aemeasurable) hWeightedIntegral
  have hPathFinite : ∀ᵐ ω ∂μ, (∑' n, pathStep n ω) < ∞ := by
    filter_upwards [hWeightedFinite] with ω hω
    have hDensityNe : (E.referenceDensity ω : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (E.referenceDensity_pos ω).ne'
    apply ENNReal.lt_top_of_mul_ne_top_right _ hDensityNe
    rw [← ENNReal.tsum_mul_left]
    simpa only [weightedStep] using hω.ne
  let q : ℕ → Ω → ℝ := fun n ω => (pathStep n ω).toReal
  have hQSummable : ∀ᵐ ω ∂μ, Summable fun n => q n ω := by
    filter_upwards [hPathFinite] with ω hω
    exact ENNReal.summable_toReal hω.ne
  let bound : ℕ → ℝ := fun n => Classical.choose
    (exists_predictableCommonSimpleApproximation_bound f hf (cutoff n))
  have hBound : ∀ n t ω, |K (cutoff n) t ω| ≤ bound n := by
    intro n
    exact Classical.choose_spec
      (exists_predictableCommonSimpleApproximation_bound f hf (cutoff n))
  have hKPredictable : ∀ n,
      IsStronglyPredictable ℱ (K (cutoff n)) := fun n =>
    predictableCommonSimpleApproximation_isStronglyPredictable
      f hf (cutoff n)
  let X : ℕ → Process Ω := fun n =>
    commonFiniteVariationProcessApproximation E f hf (cutoff n)
  have hXRight : ∀ n ω t,
      ContinuousWithinAt (X n · ω) (Set.Ici t) t := by
    intro n ω t
    exact finiteVariationIntegralProcess_rightContinuous E
      (hKPredictable n) (hBound n) ω t
  have hXVariation : ∀ n ω,
      BoundedVariationOn (X n · ω) Set.univ := by
    intro n ω
    exact finiteVariationIntegralProcess_isBoundedVariation E
      (hKPredictable n) (hBound n) ω
  have hPathStepFinite : ∀ n ω, pathStep n ω ≠ ∞ := by
    intro n ω
    let ν := (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
    let : IsFiniteMeasure ν := by
      dsimp only [ν]
      unfold SignedMeasure.totalVariation
      infer_instance
    have hSection : StronglyMeasurable fun t =>
        K (cutoff (n + 1)) t ω - K (cutoff n) t ω :=
      ((hKPredictable (n + 1)).sub (hKPredictable n)
        |>.mono (PredictableKernelMeasure.predictable_le_prod ℱ))
        |>.comp_measurable measurable_prodMk_right
    have hInt : Integrable (fun t =>
        K (cutoff (n + 1)) t ω - K (cutoff n) t ω) ν := by
      apply (integrable_const (bound (n + 1) + bound n)).mono'
        hSection.aestronglyMeasurable
      filter_upwards with t
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans
        (add_le_add (hBound (n + 1) t ω) (hBound n t ω))
    simpa only [pathStep, step, K] using hInt.2.ne
  have hVariationStep : ∀ n ω,
      eVariationOn (fun t => X (n + 1) t ω - X n t ω) Set.univ ≤
        ENNReal.ofReal (q n ω) := by
    intro n ω
    have hVariation :=
      eVariationOn_finiteVariationIntegralProcess_sub_le_lintegral E
        (hKPredictable (n + 1)) (hKPredictable n)
        (hBound (n + 1)) (hBound n) ω
    have hPathEq :
        (∫⁻ t, ‖K (cutoff (n + 1)) t ω - K (cutoff n) t ω‖ₑ
          ∂(FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation) =
          pathStep n ω := by
      rfl
    rw [hPathEq] at hVariation
    change eVariationOn (fun t => X (n + 1) t ω - X n t ω)
      Set.univ ≤ _ at hVariation
    exact hVariation.trans_eq
      (ENNReal.ofReal_toReal (hPathStepFinite n ω)).symm
  have hDistanceStep : ∀ n ω t,
      dist (X n t ω) (X (n + 1) t ω) ≤ q n ω := by
    intro n ω t
    have hDistance :=
      dist_finiteVariationIntegralProcess_le_lintegral_toReal E
        (hKPredictable (n + 1)) (hKPredictable n)
        (hBound (n + 1)) (hBound n) ω t
    rw [dist_comm] at hDistance
    exact hDistance
  let raw : Process Ω := fun t ω => limUnder atTop (fun n => X n t ω)
  have hRawLimit : ∀ᵐ ω ∂μ, ∀ t,
      Tendsto (fun n => X n t ω) atTop (𝓝 (raw t ω)) := by
    filter_upwards [hQSummable] with ω hSum
    intro t
    have hDistance : Summable fun n =>
        dist (X n t ω) (X (n + 1) t ω) :=
      Summable.of_nonneg_of_le (fun _ => dist_nonneg)
        (fun n => hDistanceStep n ω t) hSum
    exact (cauchySeq_of_summable_dist hDistance).tendsto_limUnder
  have hRawUniform : ∀ᵐ ω ∂μ,
      TendstoUniformly (fun n t => X n t ω) (fun t => raw t ω)
        atTop := by
    filter_upwards [hQSummable, hRawLimit] with ω hSum hLimit
    exact tendstoUniformly_of_eventually_dist_step_le_of_summable
      (fun n t => X n t ω) (fun t => raw t ω) (fun n => q n ω)
      hSum (fun n => ENNReal.toReal_nonneg)
      (Eventually.of_forall fun n t => hDistanceStep n ω t) hLimit
  have hRawRight : ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (raw · ω) (Set.Ici t) t := by
    filter_upwards [hRawUniform] with ω hUniform
    exact rightContinuous_of_tendstoUniformly
      (fun n t => X n t ω) (fun t => raw t ω) hUniform
        (fun n => hXRight n ω)
  have hRawVariation : ∀ᵐ ω ∂μ,
      BoundedVariationOn (raw · ω) Set.univ := by
    filter_upwards [hQSummable, hRawLimit] with ω hSum hLimit
    exact boundedVariationOn_limit_of_summable_step_variation
      (fun n t => X n t ω) (fun t => raw t ω) (fun n => q n ω)
      (fun n => hXVariation n ω) hSum
      (Eventually.of_forall fun n => hVariationStep n ω) hLimit
  have hRawVariationTendsto : ∀ᵐ ω ∂μ,
      Tendsto (fun n => eVariationOn
        (fun t => raw t ω - X n t ω) Set.univ) atTop (𝓝 0) := by
    filter_upwards [hQSummable, hRawLimit] with ω hSum hLimit
    exact tendsto_eVariationOn_limit_sub_zero_of_summable_step_variation
      (fun n t => X n t ω) (fun t => raw t ω) (fun n => q n ω)
      hSum (Eventually.of_forall fun n => hVariationStep n ω) hLimit
  have hRawPredictable : IsStronglyPredictable ℱ raw := by
    change StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω => limUnder atTop
        (fun n => X n p.1 p.2))
    exact @StronglyMeasurable.limUnder
      ℕ (ℝ≥0 × Ω) ℝ ℱ.predictable _ _ atTop _
      (fun n p => X n p.1 p.2) _ _
      (fun n => finiteVariationIntegralProcess_isStronglyPredictable E
        (hKPredictable n) (hBound n))
  have hRawRegular : ∀ᵐ ω ∂μ,
      (∀ t, ContinuousWithinAt (raw · ω) (Set.Ici t) t) ∧
        BoundedVariationOn (raw · ω) Set.univ := by
    filter_upwards [hRawRight, hRawVariation] with ω hRight hVariation
    exact ⟨hRight, hVariation⟩
  obtain ⟨B, hBPredictable, hBRight, hBVariation, hBRaw⟩ :=
    ProcessNullSetRegularization.exists_predictable_rightContinuous_boundedVariation_version
      hUsual hRawPredictable hRawRegular
  have hBConvergence : ∀ᵐ ω ∂μ,
      TendstoUniformly (fun n t => X n t ω) (fun t => B t ω) atTop ∧
        Tendsto (fun n => eVariationOn
          (fun t => B t ω - X n t ω) Set.univ) atTop (𝓝 0) := by
    filter_upwards [hRawUniform, hRawVariationTendsto, hBRaw]
        with ω hUniform hVariation hEq
    have hPathEq : (fun t => B t ω) = fun t => raw t ω := by
      funext t
      exact hEq t
    constructor
    · rw [hPathEq]
      exact hUniform
    · have hSequenceEq :
          (fun n => eVariationOn
            (fun t => B t ω - X n t ω) Set.univ) =
            fun n => eVariationOn
              (fun t => raw t ω - X n t ω) Set.univ := by
        funext n
        congr 1
        funext t
        rw [hEq t]
      rw [hSequenceEq]
      exact hVariation
  let terminalX : ℕ → Ω → ℝ := fun n ω =>
    limUnder atTop (fun t => X n t ω)
  let terminalB : Ω → ℝ := fun ω =>
    limUnder atTop (fun t => B t ω)
  have hTerminalTendstoMu : ∀ᵐ ω ∂μ,
      Tendsto (fun n => terminalX n ω) atTop (𝓝 (terminalB ω)) := by
    filter_upwards [hBConvergence] with ω hConvergence
    exact tendsto_limUnder_atTop_of_tendstoUniformly_boundedVariation
      (fun n t => X n t ω) (fun t => B t ω)
      (fun n => hXVariation n ω) (hBVariation ω) hConvergence.1
  have hTerminalTendstoReference : ∀ᵐ ω ∂E.referenceMeasure,
      Tendsto (fun n => terminalX n ω) atTop (𝓝 (terminalB ω)) :=
    (withDensity_absolutelyContinuous μ
      (fun ω => (E.referenceDensity ω : ℝ≥0∞))).ae_le
        hTerminalTendstoMu
  let terminalLp : ℕ → Lp ℝ 1 E.referenceMeasure := fun n =>
    commonFiniteVariationTerminalApproximationLp E f hf hF (cutoff n)
  have hTerminalLpTendsto : Tendsto terminalLp atTop
      (𝓝 (finiteVariationTerminalIntegralLp E f hf hF)) := by
    exact (commonFiniteVariationTerminalApproximationLp_tendsto
      E f hf hF).comp hCutoff.tendsto_atTop
  obtain ⟨terminalCutoff, hTerminalCutoff, hTerminalLpAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hTerminalLpTendsto).exists_seq_tendsto_ae
  have hTerminalCoe : ∀ᵐ ω ∂E.referenceMeasure, ∀ n,
      terminalLp n ω = terminalX n ω := by
    rw [ae_all_iff]
    intro n
    let hApprox :=
      commonFiniteVariationTerminalApproximation_memLp E f hf hF (cutoff n)
    have hProcessTerminal := E.referenceMeasure_ae_eq_iff.mpr
      (finiteVariationIntegralProcess_limUnder_atTop_ae_eq E
        (hKPredictable n) (hBound n))
    filter_upwards [MemLp.coeFn_toLp hApprox, hProcessTerminal]
        with ω hLp hProcess
    exact hLp.trans hProcess.symm
  have hCompletedTerminalAE :
      (finiteVariationTerminalIntegralLp E f hf hF : Ω → ℝ)
        =ᵐ[E.referenceMeasure] terminalB := by
    filter_upwards [hTerminalLpAE, hTerminalTendstoReference, hTerminalCoe]
        with ω hLp hRaw hCoe
    have hLpRaw : Tendsto
        (fun n => terminalX (terminalCutoff n) ω) atTop
        (𝓝 (finiteVariationTerminalIntegralLp E f hf hF ω)) :=
      hLp.congr' (Eventually.of_forall fun n => hCoe (terminalCutoff n))
    exact tendsto_nhds_unique hLpRaw
      (hRaw.comp hTerminalCutoff.tendsto_atTop)
  have hBTerminal : MemLp terminalB 1 E.referenceMeasure :=
    (Lp.memLp (finiteVariationTerminalIntegralLp E f hf hF)).ae_eq
      hCompletedTerminalAE
  have hBTerminalEq : hBTerminal.toLp terminalB =
      finiteVariationTerminalIntegralLp E f hf hF := by
    exact (MemLp.toLp_congr hBTerminal
      (Lp.memLp (finiteVariationTerminalIntegralLp E f hf hF))
      hCompletedTerminalAE.symm).trans
        (Lp.toLp_coeFn (finiteVariationTerminalIntegralLp E f hf hF)
          (Lp.memLp (finiteVariationTerminalIntegralLp E f hf hF)))
  exact ⟨cutoff, hCutoff, B, hBPredictable, hBRight, hBVariation,
    hBConvergence, hBTerminal, hBTerminalEq⟩

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
