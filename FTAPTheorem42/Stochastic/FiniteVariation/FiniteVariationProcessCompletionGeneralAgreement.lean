/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionAgreement

/-!
# Agreement of the finite-variation completion for general L1 coefficients

Membership in the canonical predictable variation `L1` space implies
pathwise integrability outside one market-null set.  On those paths, the
common bounded predictable approximations converge in pathwise `L1`, hence
their cumulative Stieltjes integrals converge uniformly.  This identifies
the selected completed finite-variation process with the raw cumulative
Stieltjes integral without a boundedness assumption on the coefficient.
-/

namespace FTAPTheorem42

open Filter Function MeasureTheory ProbabilityTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

omit [SigmaFiniteFiltration mu F] in
/-- Canonical variation `L1` membership gives pathwise integrability against
the unweighted Jordan variation outside one market-null set.  Strict
positivity of the bridge reference density is essential here. -/
theorem integrable_section_ae_of_memLp_one_canonicalVariation
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    ∀ᵐ omega ∂mu, Integrable (fun t => f t omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  let pathNorm : Omega -> ENNReal := fun omega =>
    ∫⁻ t, ‖f t omega‖ₑ
      ∂(FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  let weightedNorm : Omega -> ENNReal := fun omega =>
    (E.referenceDensity omega : ENNReal) * pathNorm omega
  have hWeightedMeasurable : Measurable weightedNorm := by
    let kappa := canonicalTotalVariationKernel E
    let : IsFiniteKernel kappa :=
      canonicalTotalVariationKernel.instIsFiniteKernel E
    have hProduct : Measurable fun p : NNReal × Omega =>
        ‖f p.1 p.2‖ₑ :=
      hf.enorm.mono (PredictableKernelMeasure.predictable_le_prod F) le_rfl
    have hKernel : Measurable fun omega =>
        ∫⁻ t, ‖f t omega‖ₑ ∂kappa omega := by
      exact (hProduct.comp measurable_swap).lintegral_kernel_prod_right'
    convert hKernel using 1
    funext omega
    rw [canonicalTotalVariationKernel_apply, lintegral_smul_measure]
    rfl
  have hWeightedIntegral :
      (∫⁻ omega, weightedNorm omega ∂mu) ≠ ∞ := by
    have hFinite :
        (∫⁻ p, ‖Function.uncurry f p‖ₑ
          ∂canonicalVariationMeasure E) ≠ ∞ :=
      (hVariation.integrable (by norm_num)).2.ne
    rw [lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
      E hf.enorm] at hFinite
    simpa only [weightedNorm, pathNorm, Function.uncurry_apply_pair]
      using hFinite
  have hWeightedFinite : ∀ᵐ omega ∂mu, weightedNorm omega < ∞ :=
    ae_lt_top' hWeightedMeasurable.aemeasurable hWeightedIntegral
  have hPathFinite : ∀ᵐ omega ∂mu, pathNorm omega < ∞ := by
    filter_upwards [hWeightedFinite] with omega homega
    have hDensityNe : (E.referenceDensity omega : ENNReal) ≠ 0 := by
      exact_mod_cast (E.referenceDensity_pos omega).ne'
    apply ENNReal.lt_top_of_mul_ne_top_right _ hDensityNe
    simpa only [weightedNorm] using homega.ne
  filter_upwards [hPathFinite] with omega homega
  constructor
  · exact (hf.mono (PredictableKernelMeasure.predictable_le_prod F)
      |>.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    simpa only [pathNorm] using homega

omit [SigmaFiniteFiltration mu F] in
/-- Multiplication by the canonical orientation preserves every pathwise
`L1` coefficient. -/
theorem integrable_finiteVariationIntegralDensity_section_of_integrable
    (E : SIntegrableFiniteVariationBridge G)
    {K : Process Omega} (hK : IsStronglyPredictable F K)
    (omega : Omega)
    (hIntegrable : Integrable (fun t => K t omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation) :
    Integrable (fun t => finiteVariationIntegralDensity E K (t, omega))
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  apply hIntegrable.mono
    ((finiteVariationIntegralDensity_stronglyMeasurable E hK
      |>.mono (PredictableKernelMeasure.predictable_le_prod F))
      |>.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  filter_upwards with t
  change ‖finiteVariationIntegralDensity E K (t, omega)‖ <= ‖K t omega‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    finiteVariationIntegralDensity, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, omega))

omit [SigmaFiniteFiltration mu F] in
/-- Pathwise `L1` distance controls the fixed-time distance of cumulative
Stieltjes integrals without a boundedness hypothesis. -/
theorem dist_finiteVariationIntegralProcess_le_lintegral_toReal_of_integrable
    (E : SIntegrableFiniteVariationBridge G)
    {K L : Process Omega} (hK : IsStronglyPredictable F K)
    (hL : IsStronglyPredictable F L) (omega : Omega)
    (hKIntegrable : Integrable (fun u => K u omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (hLIntegrable : Integrable (fun u => L u omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (t : NNReal) :
    dist (finiteVariationIntegralProcess E K t omega)
        (finiteVariationIntegralProcess E L t omega) <=
      (∫⁻ u, ‖K u omega - L u omega‖ₑ
        ∂(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation omega)).totalVariation).toReal := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  have hKDensity :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hK omega hKIntegrable
  have hLDensity :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hL omega hLIntegrable
  have hKUpTo : Integrable
      (fun u => finiteVariationIntegralDensity E K (u, omega))
      (pathVariationMeasureUpTo E t omega) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      hKDensity.integrableOn
  have hLUpTo : Integrable
      (fun u => finiteVariationIntegralDensity E L (u, omega))
      (pathVariationMeasureUpTo E t omega) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      hLDensity.integrableOn
  have hPointwise (u : NNReal) :
      edist (finiteVariationIntegralDensity E K (u, omega))
          (finiteVariationIntegralDensity E L (u, omega)) <=
        ‖K u omega - L u omega‖ₑ := by
    change ‖jumpCorrectedCanonicalVariationDensity E (u, omega) *
          K u omega -
        jumpCorrectedCanonicalVariationDensity E (u, omega) *
          L u omega‖ₑ <= ‖K u omega - L u omega‖ₑ
    rw [← mul_sub, enorm_mul]
    calc
      ‖jumpCorrectedCanonicalVariationDensity E (u, omega)‖ₑ *
          ‖K u omega - L u omega‖ₑ <=
          1 * ‖K u omega - L u omega‖ₑ := by
        rw [mul_comm ‖jumpCorrectedCanonicalVariationDensity E (u, omega)‖ₑ,
          mul_comm 1]
        apply mul_le_mul_right
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.mpr
          (abs_jumpCorrectedCanonicalVariationDensity_le_one E (u, omega))
      _ = ‖K u omega - L u omega‖ₑ := one_mul _
  have hRestricted :
      (∫⁻ u, edist (finiteVariationIntegralDensity E K (u, omega))
          (finiteVariationIntegralDensity E L (u, omega))
          ∂pathVariationMeasureUpTo E t omega) <=
        ∫⁻ u, ‖K u omega - L u omega‖ₑ ∂nu := by
    calc
      (∫⁻ u, edist (finiteVariationIntegralDensity E K (u, omega))
          (finiteVariationIntegralDensity E L (u, omega))
          ∂pathVariationMeasureUpTo E t omega) <=
          ∫⁻ u, ‖K u omega - L u omega‖ₑ
            ∂pathVariationMeasureUpTo E t omega :=
        lintegral_mono hPointwise
      _ <= ∫⁻ u, ‖K u omega - L u omega‖ₑ ∂nu := by
        exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hFinite : (∫⁻ u, ‖K u omega - L u omega‖ₑ ∂nu) ≠ ∞ :=
    (hKIntegrable.sub hLIntegrable).2.ne
  change dist
      (∫ u, finiteVariationIntegralDensity E K (u, omega)
        ∂pathVariationMeasureUpTo E t omega)
      (∫ u, finiteVariationIntegralDensity E L (u, omega)
        ∂pathVariationMeasureUpTo E t omega) <= _
  exact (dist_integral_le_lintegral_edist hKUpTo hLUpTo).trans
    (ENNReal.toReal_mono hFinite hRestricted)

omit [SigmaFiniteFiltration mu F] in
/-- On every path where the target coefficient is variation-integrable, the
common bounded approximations converge uniformly to its raw cumulative
Stieltjes integral. -/
theorem commonFiniteVariationProcessApproximation_tendstoUniformly_of_integrable
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (omega : Omega)
    (hIntegrable : Integrable (fun t => f t omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation) :
    TendstoUniformly
      (fun n t => commonFiniteVariationProcessApproximation E f hf n t omega)
      (fun t => finiteVariationIntegralProcess E f t omega) atTop := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  let d : Nat -> NNReal -> Real := fun n t =>
    predictableCommonSimpleApproximation f hf n t omega - f t omega
  have hdMeasurable : forall n, AEStronglyMeasurable (d n) nu := by
    intro n
    exact (((predictableCommonSimpleApproximation_isStronglyPredictable
      f hf n).sub hf).mono
        (PredictableKernelMeasure.predictable_le_prod F)
      |>.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  have hdBound : forall n, ∀ᵐ t ∂nu, ‖d n t‖ <= ‖f t omega‖ := by
    intro n
    exact Filter.Eventually.of_forall fun t => by
      simpa only [d, Real.norm_eq_abs] using
        abs_predictableCommonSimpleApproximation_sub_le f hf n t omega
  have hdTendsto : ∀ᵐ t ∂nu,
      Tendsto (fun n => d n t) atTop (nhds 0) := by
    exact Filter.Eventually.of_forall fun t => by
      simpa only [d, sub_self] using
        (predictableCommonSimpleApproximation_tendsto f hf t omega).sub_const
          (f t omega)
  have hIntegralNorm : Tendsto (fun n => ∫ t, ‖d n t‖ ∂nu)
      atTop (nhds 0) := by
    have hDCT := tendsto_integral_of_dominated_convergence
      (μ := nu) (F := fun n t => ‖d n t‖) (f := fun _ => (0 : Real))
      (fun t => ‖f t omega‖)
      (fun n => (hdMeasurable n).norm)
      hIntegrable.norm
      (fun n => by
        filter_upwards [hdBound n] with t ht
        simpa only [norm_norm] using ht)
      (by
        filter_upwards [hdTendsto] with t ht
        simpa using ht.norm)
    simpa using hDCT
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hIntegralNorm) epsilon hepsilon
  filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
  intro t
  have hApproxPredictable :=
    predictableCommonSimpleApproximation_isStronglyPredictable f hf n
  obtain ⟨C, hC⟩ :=
    exists_predictableCommonSimpleApproximation_bound f hf n
  have hApproxIntegrable : Integrable
      (fun u => predictableCommonSimpleApproximation f hf n u omega) nu := by
    apply (integrable_const (max 0 C)).mono'
      ((hApproxPredictable.mono
        (PredictableKernelMeasure.predictable_le_prod F))
        |>.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_eq_abs]
    exact (hC u omega).trans (le_max_right 0 C)
  have hDistance :=
    dist_finiteVariationIntegralProcess_le_lintegral_toReal_of_integrable
      E hApproxPredictable hf omega hApproxIntegrable hIntegrable t
  have hIntegralEq :
      (∫⁻ u, ‖predictableCommonSimpleApproximation f hf n u omega -
          f u omega‖ₑ ∂nu).toReal = ∫ u, ‖d n u‖ ∂nu := by
    rw [integral_norm_eq_lintegral_enorm (hdMeasurable n)]
  rw [hIntegralEq] at hDistance
  have hIntegralNonnegative : 0 <= ∫ u, ‖d n u‖ ∂nu :=
    integral_nonneg fun _ => norm_nonneg _
  have hn' : (∫ u, ‖d n u‖ ∂nu) < epsilon := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hIntegralNonnegative] using hn
  simpa only [commonFiniteVariationProcessApproximation, dist_comm] using
    hDistance.trans_lt hn'

omit [SigmaFiniteFiltration mu F] in
/-- Every canonical variation `L1` coefficient has the same raw and
completed cumulative finite-variation process, up to indistinguishability. -/
theorem completedFiniteVariationProcess_indistinguishable
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E f hf hVariation)
      (finiteVariationIntegralProcess E f) := by
  let data := completedFiniteVariationProcessData
    hUsual E f hf hVariation
  filter_upwards [data.approximation_tendsto,
      integrable_section_ae_of_memLp_one_canonicalVariation
        E f hf hVariation] with omega hCompleted hIntegrable
  intro t
  have hDirect : TendstoUniformly
      (fun n u => commonFiniteVariationProcessApproximation
        E f hf (data.cutoff n) u omega)
      (fun u => finiteVariationIntegralProcess E f u omega) atTop :=
    (tendstoUniformly_iff_seq_tendstoUniformly.mp
      (commonFiniteVariationProcessApproximation_tendstoUniformly_of_integrable
        E f hf omega hIntegrable)) data.cutoff
          data.cutoff_strictMono.tendsto_atTop
  exact tendsto_nhds_unique (hCompleted.1.tendsto_at t)
    (hDirect.tendsto_at t)

omit [SigmaFiniteFiltration mu F] in
/-- The finite-variation component used by every completed finite-horizon
`M2 + A1` graph is the raw cumulative Stieltjes integral of its coefficient.
This is the unbounded-coefficient semantic agreement needed by localized
range realization. -/
theorem finiteHorizonCompletedFiniteVariationPart_indistinguishable
    {T : NNReal}
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E c)
      (finiteVariationIntegralProcess E c.integrand) := by
  exact completedFiniteVariationProcess_indistinguishable
    hUsual E c.integrand c.integrand_isStronglyPredictable
      c.integrand_memLp_variation

end SIntegrableFiniteVariationBridge

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Jumps of variation-integrable cumulative Stieltjes integrals

The bounded predictable approximations of an `L1` coefficient converge
pointwise to the coefficient and their cumulative Stieltjes integrals
converge uniformly on every path on which the coefficient is integrable.
Passing both values and left limits through this common approximation gives
the jump formula without a boundedness assumption on the coefficient.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-- A canonical variation-`L1` coefficient has jump equal to its current
value times the source finite-variation jump, simultaneously at every time
outside one market-null set. -/
theorem processLeftJump_finiteVariationIntegralProcess_eq_of_memLp_one
    (E : SIntegrableFiniteVariationBridge G)
    (K : Process Omega) (hK : IsStronglyPredictable F K)
    (hVariation : MemLp (Function.uncurry K) 1
      (canonicalVariationMeasure E)) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump (finiteVariationIntegralProcess E K) t omega =
        K t omega * processLeftJump G.finiteVariationPart t omega := by
  filter_upwards [integrable_section_ae_of_memLp_one_canonicalVariation
      E K hK hVariation] with omega hIntegrable
  intro t
  let A : Nat -> Process Omega := fun n =>
    commonFiniteVariationProcessApproximation E K hK n
  have hUniform : TendstoUniformly
      (fun n s => A n s omega)
      (fun s => finiteVariationIntegralProcess E K s omega) atTop :=
    commonFiniteVariationProcessApproximation_tendstoUniformly_of_integrable
      E K hK omega hIntegrable
  have hApproxLeft : forall n s, Tendsto (fun u => A n u omega)
      (nhdsWithin s (Iio s))
      (nhds (Function.leftLim (fun u => A n u omega) s)) := by
    intro n s
    let Kapprox := predictableCommonSimpleApproximation K hK n
    obtain ⟨bound, hBound⟩ :=
      exists_predictableCommonSimpleApproximation_bound K hK n
    exact finiteVariationIntegralProcess_hasLeftLimits E
      (predictableCommonSimpleApproximation_isStronglyPredictable K hK n)
      hBound omega s
  have hLeft := tendsto_leftLim_of_tendstoUniformly
    (fun n s => A n s omega)
    (fun s => finiteVariationIntegralProcess E K s omega)
    hUniform hApproxLeft t
  have hJump : Tendsto (fun n => processLeftJump (A n) t omega) atTop
      (nhds (processLeftJump (finiteVariationIntegralProcess E K) t omega)) := by
    simpa only [processLeftJump] using
      (hUniform.tendsto_at t).sub hLeft
  have hProduct : Tendsto (fun n =>
      predictableCommonSimpleApproximation K hK n t omega *
        processLeftJump G.finiteVariationPart t omega) atTop
      (nhds (K t omega * processLeftJump G.finiteVariationPart t omega)) :=
    (predictableCommonSimpleApproximation_tendsto K hK t omega).mul_const _
  have hApproxJump : Tendsto (fun n => processLeftJump (A n) t omega) atTop
      (nhds (K t omega * processLeftJump G.finiteVariationPart t omega)) := by
    apply hProduct.congr'
    filter_upwards with n
    let Kapprox := predictableCommonSimpleApproximation K hK n
    obtain ⟨bound, hBound⟩ :=
      exists_predictableCommonSimpleApproximation_bound K hK n
    exact (processLeftJump_finiteVariationIntegralProcess_eq E
      (predictableCommonSimpleApproximation_isStronglyPredictable K hK n)
      hBound t omega).symm
  exact tendsto_nhds_unique hJump hApproxJump

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
