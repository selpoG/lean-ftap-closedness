/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcess

/-!
# Terminal values of cumulative finite-variation integrals

The cumulative process constructed from the predictable Doléans direction
must have the same terminal value as the pathwise signed Stieltjes integral
used in the finite-variation `L¹` completion.  The key change-of-density
identity is proved first for simple functions and then for bounded strongly
measurable coefficients by dominated convergence.
-/

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

namespace FiniteVariationPath

/-- Integration of a scalar simple function against a signed Stieltjes
measure can be computed against Jordan variation and any integrable density
representing that signed measure. -/
theorem integral_simpleFunc_eq_integral_density_mul
    {A : ℝ≥0 → ℝ} (hA : BoundedVariationOn A Set.univ)
    {density : ℝ≥0 → ℝ}
    (hDensityIntegrable : Integrable density (signedMeasure hA).totalVariation)
    (hMeasure : signedMeasure hA =
      (signedMeasure hA).totalVariation.withDensityᵥ density)
    (K : SimpleFunc ℝ≥0 ℝ) :
    integral hA K =
      ∫ t, density t * K t ∂(signedMeasure hA).totalVariation := by
  let η := signedMeasure hA
  let ν := η.totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν, η]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hSimpleIntegrable : ∀ φ : SimpleFunc ℝ≥0 ℝ,
      Integrable (φ : ℝ≥0 → ℝ) ν := by
    intro φ
    obtain ⟨C, hC⟩ := φ.exists_forall_norm_le
    exact (integrable_const C).mono' φ.aestronglyMeasurable
      (Eventually.of_forall hC)
  have hVectorIntegrable : ∀ φ : SimpleFunc ℝ≥0 ℝ,
      η.Integrable (φ : ℝ≥0 → ℝ) := by
    intro φ
    change Integrable (φ : ℝ≥0 → ℝ) η.variation
    rw [← signedMeasure_totalVariation_eq_variation]
    exact hSimpleIntegrable φ
  have hMulIntegrable : ∀ φ : SimpleFunc ℝ≥0 ℝ,
      Integrable (fun t => density t * φ t) ν := by
    intro φ
    apply (hDensityIntegrable.simpleFunc_mul φ).congr
    filter_upwards with t
    simp only [Pi.mul_apply]
    ring
  change integral hA K = ∫ t, density t * K t ∂ν
  induction K using SimpleFunc.induction with
  | @const c s hs =>
      simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
        SimpleFunc.coe_const, SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator]
      have hSet := congrArg (fun m : SignedMeasure ℝ≥0 => m s) hMeasure
      rw [withDensityᵥ_apply hDensityIntegrable hs] at hSet
      calc
        integral hA (s.indicator fun _ => c) = c * η s := by
          unfold integral
          rw [VectorMeasure.integral_indicator_const c hs]
          rfl
        _ = c * ∫ t in s, density t ∂ν := by rw [hSet]
        _ = ∫ t in s, density t * c ∂ν := by
          rw [integral_mul_const]
          ring
        _ = ∫ t, density t * s.indicator (fun _ => c) t ∂ν := by
          rw [← MeasureTheory.integral_indicator hs]
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ s <;> simp [ht]
  | @add f g _ hf hg =>
      rw [SimpleFunc.coe_add]
      change integral hA ((f : ℝ≥0 → ℝ) + g) =
        ∫ t, density t * (f t + g t) ∂ν
      have hMulAdd : (fun t => density t * (f t + g t)) =
          (fun t => density t * f t) + fun t => density t * g t := by
        funext t
        simp only [Pi.add_apply]
        ring
      calc
        integral hA ((f : ℝ≥0 → ℝ) + g) =
            integral hA f + integral hA g := by
          unfold integral
          exact VectorMeasure.integral_add
            (hVectorIntegrable f) (hVectorIntegrable g)
        _ = (∫ t, density t * f t ∂ν) +
            ∫ t, density t * g t ∂ν := by rw [hf, hg]
        _ = ∫ t, density t * (f t + g t) ∂ν := by
          rw [hMulAdd]
          exact (MeasureTheory.integral_add
            (hMulIntegrable f) (hMulIntegrable g)).symm

/-- The same change-of-density identity for a bounded strongly measurable
coefficient.  Both sides are obtained from the same uniformly bounded
simple approximations. -/
theorem integral_eq_integral_density_mul_of_bounded
    {A : ℝ≥0 → ℝ} (hA : BoundedVariationOn A Set.univ)
    {density K : ℝ≥0 → ℝ}
    (hDensityIntegrable : Integrable density (signedMeasure hA).totalVariation)
    (hDensityBound : ∀ t, |density t| ≤ 1)
    (hMeasure : signedMeasure hA =
      (signedMeasure hA).totalVariation.withDensityᵥ density)
    (hK : StronglyMeasurable K) {C : ℝ}
    (hKBound : ∀ t, |K t| ≤ C) :
    integral hA K =
      ∫ t, density t * K t ∂(signedMeasure hA).totalVariation := by
  let η := signedMeasure hA
  let ν := η.totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν, η]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hC : 0 ≤ C := (abs_nonneg (K 0)).trans (hKBound 0)
  let Kapprox : ℕ → SimpleFunc ℝ≥0 ℝ := hK.approxBounded C
  have hKapproxMeasurable : ∀ n,
      AEStronglyMeasurable (Kapprox n : ℝ≥0 → ℝ) ν :=
    fun n => (Kapprox n).aestronglyMeasurable
  have hKapproxBound : ∀ n t, ‖Kapprox n t‖ ≤ C := by
    intro n t
    exact hK.norm_approxBounded_le hC n t
  have hKTendsto : ∀ t,
      Tendsto (fun n => Kapprox n t) atTop (𝓝 (K t)) := by
    intro t
    apply hK.tendsto_approxBounded_of_norm_le
    simpa only [Real.norm_eq_abs] using hKBound t
  have hLeftTendsto : Tendsto (fun n => integral hA (Kapprox n)) atTop
      (𝓝 (integral hA K)) := by
    unfold integral
    apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun n => by
        rw [← signedMeasure_totalVariation_eq_variation]
        exact hKapproxMeasurable n
    · exact ⟨C, Eventually.of_forall fun n =>
        Eventually.of_forall fun t => hKapproxBound n t⟩
    · exact Eventually.of_forall hKTendsto
  have hDensityKMeasurable : ∀ n,
      AEStronglyMeasurable (fun t => density t * Kapprox n t) ν :=
    fun n => hDensityIntegrable.aestronglyMeasurable.mul
      (Kapprox n).aestronglyMeasurable
  have hDensityKBound : ∀ n, ∀ᵐ t ∂ν,
      ‖density t * Kapprox n t‖ ≤ C := by
    intro n
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hDensityBound t)).trans
      (hKapproxBound n t)
  have hDensityKTendsto : ∀ᵐ t ∂ν,
      Tendsto (fun n => density t * Kapprox n t) atTop
        (𝓝 (density t * K t)) := by
    filter_upwards with t
    exact tendsto_const_nhds.mul (hKTendsto t)
  have hRightTendsto : Tendsto
      (fun n => ∫ t, density t * Kapprox n t ∂ν) atTop
      (𝓝 (∫ t, density t * K t ∂ν)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => C) hDensityKMeasurable (integrable_const C)
        hDensityKBound hDensityKTendsto
  have hApproxEq : ∀ n, integral hA (Kapprox n) =
      ∫ t, density t * Kapprox n t ∂ν := by
    intro n
    exact integral_simpleFunc_eq_integral_density_mul hA
      hDensityIntegrable hMeasure (Kapprox n)
  have hLeftAsRight : Tendsto
      (fun n => ∫ t, density t * Kapprox n t ∂ν) atTop
      (𝓝 (integral hA K)) :=
    hLeftTendsto.congr' (Eventually.of_forall hApproxEq)
  exact tendsto_nhds_unique hLeftAsRight hRightTendsto

end FiniteVariationPath

namespace SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The cumulative bounded-coefficient integral converges pathwise to the
integral of its oriented density over all source Jordan variation. -/
theorem finiteVariationIntegralProcess_tendsto_atTop
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    Tendsto (fun T => finiteVariationIntegralProcess E K T ω) atTop
      (𝓝 (∫ t, finiteVariationIntegralDensity E K (t, ω)
        ∂(FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation)) := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let g : ℝ≥0 → ℝ := fun t => finiteVariationIntegralDensity E K (t, ω)
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hInt : Integrable g ν :=
    integrable_finiteVariationIntegralDensity_section E hK hKBound ω
  have hmono : Monotone fun T : ℝ≥0 => Ioc (0 : ℝ≥0) T := by
    intro a b hab
    exact Ioc_subset_Ioc_right hab
  have hSetLim : Tendsto (fun T : ℝ≥0 => ∫ t in Ioc 0 T, g t ∂ν) atTop
      (𝓝 (∫ t in ⋃ T : ℝ≥0, Ioc 0 T, g t ∂ν)) :=
    tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) hmono
      hInt.integrableOn
  have hcomp : (Ioi (0 : ℝ≥0))ᶜ = ({0} : Set ℝ≥0) := by
    ext t
    simp
  have hSingleton : (∫ t in ({0} : Set ℝ≥0), g t ∂ν) = 0 := by
    have hνzero : ν ({0} : Set ℝ≥0) = 0 :=
      totalVariation_singleton_zero H E.rightContinuous ω
    rw [integral_singleton, measureReal_def, hνzero]
    simp
  have hIoi : (∫ t in Ioi (0 : ℝ≥0), g t ∂ν) = ∫ t, g t ∂ν := by
    have hAdd := integral_add_compl (μ := ν) (s := Ioi (0 : ℝ≥0))
      measurableSet_Ioi hInt
    rw [hcomp, hSingleton, add_zero] at hAdd
    exact hAdd
  rw [iUnion_Ioc_right, hIoi] at hSetLim
  simpa [g, finiteVariationIntegralProcess, pathVariationMeasureUpTo]
    using hSetLim

/-- Almost every pathwise terminal limit of the cumulative process is the
signed Stieltjes terminal integral used in the finite-variation `L¹`
completion. -/
theorem finiteVariationIntegralProcess_tendsto_terminalIntegral_ae
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun T => finiteVariationIntegralProcess E K T ω) atTop
      (𝓝 (finiteVariationTerminalIntegral E K ω)) := by
  filter_upwards [signedMeasure_finiteVariationPart_eq_withDensity_ae E]
      with ω hMeasure
  have hKSection : StronglyMeasurable fun t : ℝ≥0 => K t ω :=
    (hK.mono (PredictableKernelMeasure.predictable_le_prod ℱ))
      |>.comp_measurable measurable_prodMk_right
  have hTerminalEq := FiniteVariationPath.integral_eq_integral_density_mul_of_bounded
    (H.finiteVariationPart_isBoundedVariation ω)
    (integrable_jumpCorrectedCanonicalVariationDensity_section E ω)
    (fun t => abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, ω))
    hMeasure hKSection (fun t => hKBound t ω)
  change Tendsto (fun T => finiteVariationIntegralProcess E K T ω) atTop
    (𝓝 (FiniteVariationPath.integral
      (H.finiteVariationPart_isBoundedVariation ω) (fun t => K t ω)))
  rw [hTerminalEq]
  simpa only [finiteVariationIntegralDensity] using
    finiteVariationIntegralProcess_tendsto_atTop E hK hKBound ω

/-- The `limUnder` terminal value of the cumulative process agrees almost
everywhere with the existing pathwise terminal-integral representative. -/
theorem finiteVariationIntegralProcess_limUnder_atTop_ae_eq
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    (fun ω => limUnder atTop
      (fun T => finiteVariationIntegralProcess E K T ω)) =ᵐ[μ]
        finiteVariationTerminalIntegral E K := by
  filter_upwards [finiteVariationIntegralProcess_tendsto_terminalIntegral_ae
    E hK hKBound] with ω hω
  exact hω.limUnder_eq

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
