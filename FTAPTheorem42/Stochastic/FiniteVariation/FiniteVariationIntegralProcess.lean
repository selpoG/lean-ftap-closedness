/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationTerminalCompletion
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansRigidity
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable

/-!
# Process-valued finite-variation integrals of bounded coefficients

The predictable Doléans density identifies the signed Stieltjes measure of
the source finite-variation component with a density against pathwise Jordan
variation.  Multiplying that density by one bounded predictable coefficient
therefore gives a concrete cumulative integral process.  This file proves
adaptedness, right continuity, bounded variation, and predictability of that
process.  It is the process-valued finite-variation half of the common
finite-grid `M² ⊕ A¹` approximation; no realized semimartingale graph is
postulated here.
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

/-- The predictable coefficient oriented by the pathwise Doléans density. -/
noncomputable def finiteVariationIntegralDensity
    (E : SIntegrableFiniteVariationBridge H) (K : Process Ω) :
    ℝ≥0 × Ω → ℝ :=
  fun p => jumpCorrectedCanonicalVariationDensity E p * K p.1 p.2

/-- The oriented coefficient remains strongly predictable. -/
theorem finiteVariationIntegralDensity_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K) :
    StronglyMeasurable[ℱ.predictable]
      (finiteVariationIntegralDensity E K) :=
  (jumpCorrectedCanonicalVariationDensity_stronglyMeasurable E).mul hK

/-- The cumulative pathwise finite-variation integral of a predictable
coefficient. -/
noncomputable def finiteVariationIntegralProcess
    (E : SIntegrableFiniteVariationBridge H) (K : Process Ω) : Process Ω :=
  fun T ω => ∫ t, finiteVariationIntegralDensity E K (t, ω)
    ∂pathVariationMeasureUpTo E T ω

/-- Clamping the coefficient to the current horizon does not change its
integral against the restricted path-variation measure. -/
theorem finiteVariationIntegralProcess_eq_clamped
    (E : SIntegrableFiniteVariationBridge H) (K : Process Ω)
    (T : ℝ≥0) (ω : Ω) :
    finiteVariationIntegralProcess E K T ω =
      ∫ t, finiteVariationIntegralDensity E K (min t T, ω)
        ∂pathVariationKernelUpTo E T ω := by
  rw [finiteVariationIntegralProcess, pathVariationKernelUpTo_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [min_eq_left ht.2]

/-- The cumulative finite-variation integral is strongly adapted. -/
theorem finiteVariationIntegralProcess_stronglyAdapted
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K) :
    StronglyAdapted ℱ (finiteVariationIntegralProcess E K) := by
  intro T
  let κ₀ := pathVariationKernelUpTo E T
  let g₀ : ℝ≥0 → Ω → ℝ := fun t ω =>
    finiteVariationIntegralDensity E K (min t T, ω)
  let C₀ := finiteVariationIntegralProcess E K T
  have hClamp₀ (ω : Ω) :=
    finiteVariationIntegralProcess_eq_clamped E K T ω
  have hg₀ := finiteVariationIntegralDensity_stronglyMeasurable E hK
  let : MeasurableSpace Ω := ℱ T
  let κ : Kernel Ω ℝ≥0 := κ₀
  let g : ℝ≥0 → Ω → ℝ := g₀
  have hToSubtype : Measurable fun p : ℝ≥0 × Ω =>
      (⟨min p.1 T, min_le_right p.1 T⟩ : Set.Iic T) :=
    (measurable_fst.min measurable_const).subtype_mk
  have hMap : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω)
      ((inferInstance : MeasurableSpace ℝ≥0).prod (ℱ T)) ℱ.predictable
      (fun p => (min p.1 T, p.2)) :=
    measurable_inclusion_predictable.comp
      (hToSubtype.prodMk measurable_snd)
  have hg : StronglyMeasurable (Function.uncurry g) :=
    hg₀.comp_measurable hMap
  have hIntegral : StronglyMeasurable fun ω => ∫ t, g t ω ∂κ ω :=
    hg.integral_kernel_prod_left
  have hEq : C₀ = fun ω => ∫ t, g t ω ∂κ ω := by
    funext ω
    exact hClamp₀ ω
  change StronglyMeasurable C₀
  rw [hEq]
  exact hIntegral

private theorem finiteVariationIntegralDensity_section_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K) (ω : Ω) :
    StronglyMeasurable fun t : ℝ≥0 =>
      finiteVariationIntegralDensity E K (t, ω) :=
  (finiteVariationIntegralDensity_stronglyMeasurable E hK
      |>.mono (PredictableKernelMeasure.predictable_le_prod ℱ))
    |>.comp_measurable measurable_prodMk_right

/-- A deterministic bound on a coefficient also bounds its oriented
finite-variation density. -/
theorem abs_finiteVariationIntegralDensity_le
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (t : ℝ≥0) (ω : Ω) :
    |finiteVariationIntegralDensity E K (t, ω)| ≤ max 0 C := by
  calc
    |finiteVariationIntegralDensity E K (t, ω)| =
        |jumpCorrectedCanonicalVariationDensity E (t, ω)| * |K t ω| := by
      rw [finiteVariationIntegralDensity, abs_mul]
    _ ≤ |K t ω| := mul_le_of_le_one_left (abs_nonneg _)
      (abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, ω))
    _ ≤ C := hKBound t ω
    _ ≤ max 0 C := le_max_right 0 C

/-- A bounded predictable oriented coefficient is integrable on every
sample path. -/
theorem integrable_finiteVariationIntegralDensity_section
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    Integrable (fun t : ℝ≥0 =>
      finiteVariationIntegralDensity E K (t, ω))
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  apply (integrable_const (max 0 C)).mono'
    (finiteVariationIntegralDensity_section_stronglyMeasurable E hK ω
      |>.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact abs_finiteVariationIntegralDensity_le E hKBound t ω

/-- A cumulative integral increment is the oriented set integral over the
corresponding half-open interval. -/
theorem finiteVariationIntegralProcess_sub
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b) :
    finiteVariationIntegralProcess E K b ω -
        finiteVariationIntegralProcess E K a ω =
      ∫ t in Ioc a b, finiteVariationIntegralDensity E K (t, ω)
        ∂(FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  have hInt : Integrable
      (fun t => finiteVariationIntegralDensity E K (t, ω)) ν :=
    integrable_finiteVariationIntegralDensity_section E hK hKBound ω
  have hsub : Ioc (0 : ℝ≥0) a ⊆ Ioc 0 b :=
    Ioc_subset_Ioc_right hab
  have hdiff : Ioc (0 : ℝ≥0) b \ Ioc 0 a = Ioc a b := by
    ext t
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · rintro ⟨⟨h0t, htb⟩, hnot⟩
      exact ⟨lt_of_not_ge fun hta => hnot ⟨h0t, hta⟩, htb⟩
    · rintro ⟨hat, htb⟩
      refine ⟨⟨bot_le.trans_lt hat, htb⟩, ?_⟩
      rintro ⟨-, hta⟩
      exact (not_lt_of_ge hta) hat
  rw [finiteVariationIntegralProcess, finiteVariationIntegralProcess,
    pathVariationMeasureUpTo, pathVariationMeasureUpTo]
  change (∫ t in Ioc 0 b, finiteVariationIntegralDensity E K (t, ω) ∂ν) -
      ∫ t in Ioc 0 a, finiteVariationIntegralDensity E K (t, ω) ∂ν = _
  rw [← setIntegral_sdiff measurableSet_Ioc hInt.integrableOn hsub, hdiff]

/-- A cumulative integral increment is bounded by the coefficient bound
times the corresponding source-path variation increment. -/
theorem abs_finiteVariationIntegralProcess_sub_le
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b) :
    |finiteVariationIntegralProcess E K b ω -
        finiteVariationIntegralProcess E K a ω| ≤
      max 0 C *
        (cumulativeVariation H b ω - cumulativeVariation H a ω) := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hBound :
      ‖∫ t in Ioc a b, finiteVariationIntegralDensity E K (t, ω) ∂ν‖ ≤
        max 0 C * ν.real (Ioc a b) :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top ν (Ioc a b))
      fun t _ => by
        rw [Real.norm_eq_abs]
        exact abs_finiteVariationIntegralDensity_le E hKBound t ω
  rw [finiteVariationIntegralProcess_sub E hK hKBound ω hab]
  calc
    |∫ t in Ioc a b, finiteVariationIntegralDensity E K (t, ω) ∂ν| =
        ‖∫ t in Ioc a b,
          finiteVariationIntegralDensity E K (t, ω) ∂ν‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ max 0 C * ν.real (Ioc a b) := hBound
    _ = max 0 C *
        (cumulativeVariation H b ω - cumulativeVariation H a ω) := by
      rw [totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω hab]

/-- The cumulative finite-variation integral of a bounded predictable
coefficient is right-continuous path by path. -/
theorem finiteVariationIntegralProcess_rightContinuous
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => finiteVariationIntegralProcess E K u ω)
      (Set.Ici t) t := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero'
    (g := fun u => max 0 C *
      (cumulativeVariation H u ω - cumulativeVariation H t ω))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Real.norm_eq_abs]
    exact abs_finiteVariationIntegralProcess_sub_le E hK hKBound ω hu
  · have hV : ContinuousWithinAt
        (fun u => max 0 C *
          (cumulativeVariation H u ω - cumulativeVariation H t ω))
        (Set.Ici t) t :=
      continuousWithinAt_const.mul
        ((cumulativeVariation_rightContinuous H E.rightContinuous ω t).sub
          continuousWithinAt_const)
    simpa [ContinuousWithinAt] using hV

/-- The path variation of a bounded-coefficient cumulative integral is
bounded by the coefficient bound times source Jordan variation. -/
theorem eVariationOn_finiteVariationIntegralProcess_le
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    eVariationOn (fun t => finiteVariationIntegralProcess E K t ω)
        Set.univ ≤
      ENNReal.ofReal (max 0 C) *
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
            Set.univ := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hc : 0 ≤ max 0 C := le_max_left 0 C
  apply iSup_le
  rintro ⟨n, u, hu, _huMem⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (finiteVariationIntegralProcess E K (u (i + 1)) ω)
          (finiteVariationIntegralProcess E K (u i) ω)) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal
          |finiteVariationIntegralProcess E K (u (i + 1)) ω -
            finiteVariationIntegralProcess E K (u i) ω| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_dist, Real.dist_eq]
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        (max 0 C *
          (cumulativeVariation H (u (i + 1)) ω -
            cumulativeVariation H (u i) ω)) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.ofReal_le_ofReal
        (abs_finiteVariationIntegralProcess_sub_le E hK hKBound ω
          (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (max 0 C) *
        ∑ i ∈ Finset.range n, ENNReal.ofReal
          (cumulativeVariation H (u (i + 1)) ω -
            cumulativeVariation H (u i) ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul hc]
    _ = ENNReal.ofReal (max 0 C) * ENNReal.ofReal
        (∑ i ∈ Finset.range n,
          (cumulativeVariation H (u (i + 1)) ω -
            cumulativeVariation H (u i) ω)) := by
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      unfold cumulativeVariation
      exact sub_nonneg.mpr <| measureReal_mono
        (Ioc_subset_Ioc_right (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (max 0 C) * ENNReal.ofReal
        (cumulativeVariation H (u n) ω -
          cumulativeVariation H (u 0) ω) := by
      rw [Finset.sum_range_sub fun i => cumulativeVariation H (u i) ω]
    _ = ENNReal.ofReal (max 0 C) * ν (Ioc (u 0) (u n)) := by
      rw [← totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω
        (hu (Nat.zero_le n)), ofReal_measureReal]
    _ ≤ ENNReal.ofReal (max 0 C) * ν Set.univ :=
      mul_le_mul_right
        (measure_mono (subset_univ (Ioc (u 0) (u n))))
        (ENNReal.ofReal (max 0 C))

/-- A bounded predictable coefficient produces a pathwise bounded-
variation cumulative integral. -/
theorem finiteVariationIntegralProcess_isBoundedVariation
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    BoundedVariationOn
      (fun t => finiteVariationIntegralProcess E K t ω) Set.univ := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  exact ne_of_lt
    ((eVariationOn_finiteVariationIntegralProcess_le E hK hKBound ω).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ)))

/-- The signed Stieltjes measure of the cumulative bounded-coefficient
integral is its oriented density against source Jordan variation. -/
theorem signedMeasure_finiteVariationIntegralProcess_eq_withDensity
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    FiniteVariationPath.signedMeasure
        (finiteVariationIntegralProcess_isBoundedVariation
          E hK hKBound ω) =
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
          (fun t => finiteVariationIntegralDensity E K (t, ω)) := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let g : ℝ≥0 → ℝ := fun t =>
    finiteVariationIntegralDensity E K (t, ω)
  let B : ℝ≥0 → ℝ := fun t => finiteVariationIntegralProcess E K t ω
  let hB := finiteVariationIntegralProcess_isBoundedVariation E hK hKBound ω
  have hRight : ∀ t, ContinuousWithinAt B (Set.Ici t) t :=
    finiteVariationIntegralProcess_rightContinuous E hK hKBound ω
  have hInt : Integrable g ν :=
    integrable_finiteVariationIntegralDensity_section E hK hKBound ω
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [FiniteVariationPath.signedMeasure_Ioc hB hRight hab,
      withDensityᵥ_apply hInt measurableSet_Ioc]
    exact finiteVariationIntegralProcess_sub E hK hKBound ω hab
  · let : IsFiniteMeasure ν := by
      dsimp only [ν]
      unfold SignedMeasure.totalVariation
      infer_instance
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
    have hTop : Tendsto B atTop (𝓝 (∫ t, g t ∂ν)) := by
      simpa [B, g, finiteVariationIntegralProcess, pathVariationMeasureUpTo]
        using hSetLim
    have hBot : limUnder atBot B = 0 := by
      rw [atBot_eq_pure_of_isBot isBot_bot]
      have hB0 : B 0 = 0 := by
        simp [B, finiteVariationIntegralProcess, pathVariationMeasureUpTo]
      rw [(tendsto_pure_nhds B (⊥ : ℝ≥0)).limUnder_eq]
      exact hB0
    rw [FiniteVariationPath.signedMeasure_univ hB, hTop.limUnder_eq, hBot,
      sub_zero, withDensityᵥ_apply hInt MeasurableSet.univ, setIntegral_univ]

/-- Every left jump of the cumulative integral is the predictable
coefficient times the corresponding source finite-variation jump. -/
theorem processLeftJump_finiteVariationIntegralProcess_eq
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (t : ℝ≥0) (ω : Ω) :
    processLeftJump (finiteVariationIntegralProcess E K) t ω =
      K t ω * processLeftJump H.finiteVariationPart t ω := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let g : ℝ≥0 → ℝ := fun u =>
    finiteVariationIntegralDensity E K (u, ω)
  have hInt : Integrable g ν :=
    integrable_finiteVariationIntegralDensity_section E hK hKBound ω
  have hMeasure := congrArg (fun m : SignedMeasure ℝ≥0 =>
      m ({t} : Set ℝ≥0))
    (signedMeasure_finiteVariationIntegralProcess_eq_withDensity
      E hK hKBound ω)
  rw [FiniteVariationPath.signedMeasure_singleton
      (finiteVariationIntegralProcess_isBoundedVariation E hK hKBound ω)
      (finiteVariationIntegralProcess_rightContinuous E hK hKBound ω) t,
    withDensityᵥ_apply hInt (MeasurableSet.singleton t),
    integral_singleton, signedMeasure_totalVariation_real_singleton,
    FiniteVariationPath.signedMeasure_singleton
      (H.finiteVariationPart_isBoundedVariation ω) (E.rightContinuous ω) t]
      at hMeasure
  have hJumpFormula :
      processLeftJump (finiteVariationIntegralProcess E K) t ω =
        |processLeftJump H.finiteVariationPart t ω| *
          finiteVariationIntegralDensity E K (t, ω) := by
    change finiteVariationIntegralProcess E K t ω -
        Function.leftLim (fun u => finiteVariationIntegralProcess E K u ω) t =
      |H.finiteVariationPart t ω -
        Function.leftLim (fun u => H.finiteVariationPart u ω) t| *
          finiteVariationIntegralDensity E K (t, ω)
    simpa [ν, g, smul_eq_mul] using hMeasure
  rw [hJumpFormula]
  by_cases hJump : processLeftJump H.finiteVariationPart t ω = 0
  · simp [hJump]
  · rw [finiteVariationIntegralDensity,
      jumpCorrectedCanonicalVariationDensity_eq_leftJump_div_abs E hJump]
    field_simp [abs_ne_zero.mpr hJump]

/-- The bounded-coefficient cumulative integral has left limits on every
sample path. -/
theorem finiteVariationIntegralProcess_hasLeftLimits
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    ProcessHasLeftLimits (finiteVariationIntegralProcess E K) := by
  intro ω t
  exact (finiteVariationIntegralProcess_isBoundedVariation
    E hK hKBound ω).tendsto_leftLim t

/-- The cumulative integral of a bounded predictable coefficient against a
predictable finite-variation component is itself predictable. -/
theorem finiteVariationIntegralProcess_isStronglyPredictable
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    IsStronglyPredictable ℱ (finiteVariationIntegralProcess E K) := by
  have hLeftPredictable : IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim
        (finiteVariationIntegralProcess E K · ω) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim
      (finiteVariationIntegralProcess_hasLeftLimits E hK hKBound)
      (finiteVariationIntegralProcess_stronglyAdapted E hK)
  have hJumpPredictable : IsStronglyPredictable ℱ
      (fun t ω => K t ω * processLeftJump H.finiteVariationPart t ω) :=
    hK.mul H.processLeftJump_finiteVariationPart_isPredictable
  have hEq : finiteVariationIntegralProcess E K =
      fun t ω => Function.leftLim
          (finiteVariationIntegralProcess E K · ω) t +
        K t ω * processLeftJump H.finiteVariationPart t ω := by
    funext t ω
    have hJump := processLeftJump_finiteVariationIntegralProcess_eq
      E hK hKBound t ω
    unfold processLeftJump at hJump
    unfold processLeftJump
    linarith
  rw [hEq]
  exact hLeftPredictable.add hJumpPredictable

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
