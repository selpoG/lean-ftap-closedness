/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansJumpDensity
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Cumulative path integral of the predictable Doléans density

At a deterministic horizon `T`, pathwise total variation restricted to
`(0,T]` is a finite kernel over `ℱ T`.  Integrating the bounded predictable
jump-corrected density against that kernel therefore gives an adapted
cumulative process.  This is the pathwise finite-variation process whose
integrated predictable measure agrees with the original canonical signed
measure.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

private theorem canonicalPathTotalVariation_isFiniteMeasure
    (_E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    IsFiniteMeasure
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  unfold SignedMeasure.totalVariation
  infer_instance

/-- Pathwise Jordan total variation restricted to `(0,T]`. -/
noncomputable def pathVariationMeasureUpTo
    (_E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) (ω : Ω) :
    Measure ℝ≥0 :=
  (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.restrict
    (Ioc 0 T)

private theorem pathVariationMeasureUpTo_isFiniteMeasure
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) (ω : Ω) :
    IsFiniteMeasure (pathVariationMeasureUpTo E T ω) := by
  let := canonicalPathTotalVariation_isFiniteMeasure E ω
  unfold pathVariationMeasureUpTo
  infer_instance

private theorem measurable_pathVariationMeasureUpTo_Ioc
    (E : SIntegrableFiniteVariationBridge H) (T a b : ℝ≥0) (hab : a < b) :
    Measurable[ℱ T] fun ω => pathVariationMeasureUpTo E T ω (Ioc a b) := by
  by_cases haT : a < T
  · have haMin : a ≤ min b T := le_min hab.le haT.le
    have hEq : (fun ω => pathVariationMeasureUpTo E T ω (Ioc a b)) =
        fun ω => ENNReal.ofReal
          (cumulativeVariation H (min b T) ω - cumulativeVariation H a ω) := by
      funext ω
      let := canonicalPathTotalVariation_isFiniteMeasure E ω
      rw [pathVariationMeasureUpTo, Measure.restrict_apply measurableSet_Ioc,
        Ioc_inter_Ioc, max_eq_left (show (0 : ℝ≥0) ≤ a from bot_le),
        ← ofReal_measureReal]
      congr 1
      exact totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω haMin
    rw [hEq]
    exact (((cumulativeVariation_stronglyAdapted H E.rightContinuous)
      |>.stronglyMeasurable_le (min_le_right b T)).measurable.sub
        ((cumulativeVariation_stronglyAdapted H E.rightContinuous)
          |>.stronglyMeasurable_le haT.le).measurable).ennreal_ofReal
  · have hTa : T ≤ a := le_of_not_gt haT
    have hEmpty : Ioc a b ∩ Ioc 0 T = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false]
      exact fun hx => (not_lt_of_ge hTa) (hx.1.1.trans_le hx.2.2)
    have hEq : (fun ω => pathVariationMeasureUpTo E T ω (Ioc a b)) =
        fun _ => 0 := by
      funext ω
      rw [pathVariationMeasureUpTo, Measure.restrict_apply measurableSet_Ioc,
        hEmpty, measure_empty]
    rw [hEq]
    exact measurable_const

private theorem measurable_pathVariationMeasureUpTo_univ
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) :
    Measurable[ℱ T] fun ω => pathVariationMeasureUpTo E T ω Set.univ := by
  have hEq : (fun ω => pathVariationMeasureUpTo E T ω Set.univ) =
      fun ω => ENNReal.ofReal
        (cumulativeVariation H T ω - cumulativeVariation H 0 ω) := by
    funext ω
    let := canonicalPathTotalVariation_isFiniteMeasure E ω
    rw [pathVariationMeasureUpTo, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, ← ofReal_measureReal]
    congr 1
    exact totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω bot_le
  rw [hEq]
  exact (((cumulativeVariation_stronglyAdapted H E.rightContinuous) T).measurable.sub
    ((cumulativeVariation_stronglyAdapted H E.rightContinuous)
      |>.stronglyMeasurable_le bot_le).measurable).ennreal_ofReal

/-- The finite kernel over `ℱ T` whose path measure is Jordan total
variation restricted to `(0,T]`. -/
noncomputable def pathVariationKernelUpTo
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) :
    @Kernel Ω ℝ≥0 (ℱ T) inferInstance :=
  by
    let ρ := pathVariationMeasureUpTo E T
    have hIoc := measurable_pathVariationMeasureUpTo_Ioc E T
    have huniv := measurable_pathVariationMeasureUpTo_univ E T
    have hfinite (ω : Ω) : IsFiniteMeasure (ρ ω) :=
      pathVariationMeasureUpTo_isFiniteMeasure E T ω
    letI : MeasurableSpace Ω := ℱ T
    letI (ω : Ω) : IsFiniteMeasure (ρ ω) := hfinite ω
    exact FiniteVariationKernel.ofFiniteMeasuresIoc ρ hIoc huniv

@[simp]
theorem pathVariationKernelUpTo_apply
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) (ω : Ω) :
    pathVariationKernelUpTo E T ω = pathVariationMeasureUpTo E T ω :=
  by
    unfold pathVariationKernelUpTo
    change pathVariationMeasureUpTo E T ω = pathVariationMeasureUpTo E T ω
    rfl

noncomputable instance pathVariationKernelUpTo.instIsSFiniteKernel
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) :
    IsSFiniteKernel (pathVariationKernelUpTo E T) := by
  have hfinite (ω : Ω) :
      IsFiniteMeasure (pathVariationKernelUpTo E T ω) := by
    rw [pathVariationKernelUpTo_apply]
    exact pathVariationMeasureUpTo_isFiniteMeasure E T ω
  exact @FiniteVariationKernel.isSFiniteKernel_of_finiteMeasures
    Ω ℝ≥0 (ℱ T) inferInstance (pathVariationKernelUpTo E T) hfinite

/-- Cumulative integral of the jump-corrected predictable density against
pathwise Jordan total variation. -/
noncomputable def cumulativeDensityIntegral
    (E : SIntegrableFiniteVariationBridge H) : Process Ω :=
  fun T ω => ∫ t, jumpCorrectedCanonicalVariationDensity E (t, ω)
    ∂pathVariationMeasureUpTo E T ω

/-- At a fixed horizon, clamping the time argument of the density does not
change its integral against the restricted path-variation measure. -/
private theorem cumulativeDensityIntegral_eq_clamped
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) (ω : Ω) :
    cumulativeDensityIntegral E T ω =
      ∫ t, jumpCorrectedCanonicalVariationDensity E (min t T, ω)
        ∂pathVariationKernelUpTo E T ω := by
  rw [cumulativeDensityIntegral, pathVariationKernelUpTo_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [min_eq_left ht.2]

/-- The cumulative density integral is strongly adapted. -/
theorem cumulativeDensityIntegral_stronglyAdapted
    (E : SIntegrableFiniteVariationBridge H) :
    StronglyAdapted ℱ (cumulativeDensityIntegral E) := by
  intro T
  let κ₀ := pathVariationKernelUpTo E T
  let g₀ : ℝ≥0 → Ω → ℝ := fun t ω =>
    jumpCorrectedCanonicalVariationDensity E (min t T, ω)
  let C₀ := cumulativeDensityIntegral E T
  have hg₀ := jumpCorrectedCanonicalVariationDensity_stronglyMeasurable E
  have hClamp₀ (ω : Ω) := cumulativeDensityIntegral_eq_clamped E T ω
  let : MeasurableSpace Ω := ℱ T
  let κ : Kernel Ω ℝ≥0 := κ₀
  let g : ℝ≥0 → Ω → ℝ := g₀
  have hToSubtype : Measurable fun p : ℝ≥0 × Ω =>
      (⟨min p.1 T, min_le_right p.1 T⟩ : Set.Iic T) :=
    (measurable_fst.min measurable_const).subtype_mk
  have hMap : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω)
      ((inferInstance : MeasurableSpace ℝ≥0).prod (ℱ T)) ℱ.predictable
      (fun p => (min p.1 T, p.2)) :=
    measurable_inclusion_predictable.comp (hToSubtype.prodMk measurable_snd)
  have hg : StronglyMeasurable (Function.uncurry g) :=
    hg₀.comp_measurable hMap
  have hIntegral : StronglyMeasurable fun ω => ∫ t, g t ω ∂κ ω :=
    hg.integral_kernel_prod_left
  have hEq : C₀ =
      fun ω => ∫ t, g t ω ∂κ ω := by
    funext ω
    exact hClamp₀ ω
  change StronglyMeasurable C₀
  rw [hEq]
  exact hIntegral

/-- For every sample path, the corrected density is strongly measurable in
time for the ordinary Borel sigma algebra. -/
theorem jumpCorrectedCanonicalVariationDensity_section_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    StronglyMeasurable fun t : ℝ≥0 =>
      jumpCorrectedCanonicalVariationDensity E (t, ω) := by
  exact ((jumpCorrectedCanonicalVariationDensity_stronglyMeasurable E).mono
    (PredictableKernelMeasure.predictable_le_prod ℱ)).comp_measurable
      measurable_prodMk_right

/-- The corrected density is pathwise integrable against Jordan total
variation. -/
theorem integrable_jumpCorrectedCanonicalVariationDensity_section
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    Integrable (fun t : ℝ≥0 =>
      jumpCorrectedCanonicalVariationDensity E (t, ω))
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let := canonicalPathTotalVariation_isFiniteMeasure E ω
  apply (integrable_const (1 : ℝ)).mono'
    (jumpCorrectedCanonicalVariationDensity_section_stronglyMeasurable E ω
      |>.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, ω)

/-- The increment of the cumulative density integral is the density
integral over the corresponding half-open interval. -/
theorem cumulativeDensityIntegral_sub
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω)
    {a b : ℝ≥0} (hab : a ≤ b) :
    cumulativeDensityIntegral E b ω - cumulativeDensityIntegral E a ω =
      ∫ t in Ioc a b, jumpCorrectedCanonicalVariationDensity E (t, ω)
        ∂(FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  have hInt : Integrable (fun t : ℝ≥0 =>
      jumpCorrectedCanonicalVariationDensity E (t, ω)) ν :=
    integrable_jumpCorrectedCanonicalVariationDensity_section E ω
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
  rw [cumulativeDensityIntegral, cumulativeDensityIntegral,
    pathVariationMeasureUpTo, pathVariationMeasureUpTo]
  change (∫ t in Ioc 0 b,
      jumpCorrectedCanonicalVariationDensity E (t, ω) ∂ν) -
      ∫ t in Ioc 0 a,
        jumpCorrectedCanonicalVariationDensity E (t, ω) ∂ν = _
  rw [← setIntegral_sdiff measurableSet_Ioc hInt.integrableOn hsub, hdiff]

/-- A cumulative-density increment is dominated by the corresponding path
variation increment. -/
theorem abs_cumulativeDensityIntegral_sub_le
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω)
    {a b : ℝ≥0} (hab : a ≤ b) :
    |cumulativeDensityIntegral E b ω - cumulativeDensityIntegral E a ω| ≤
      cumulativeVariation H b ω - cumulativeVariation H a ω := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let := canonicalPathTotalVariation_isFiniteMeasure E ω
  have hBound :
      ‖∫ t in Ioc a b, jumpCorrectedCanonicalVariationDensity E (t, ω) ∂ν‖ ≤
        1 * ν.real (Ioc a b) :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top ν (Ioc a b))
      fun t _ => by
        rw [Real.norm_eq_abs]
        exact abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, ω)
  rw [cumulativeDensityIntegral_sub E ω hab]
  calc
    |∫ t in Ioc a b,
        jumpCorrectedCanonicalVariationDensity E (t, ω) ∂ν| =
        ‖∫ t in Ioc a b,
          jumpCorrectedCanonicalVariationDensity E (t, ω) ∂ν‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ 1 * ν.real (Ioc a b) := hBound
    _ = cumulativeVariation H b ω - cumulativeVariation H a ω := by
      rw [one_mul]
      exact totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω hab

/-- The cumulative density integral is right-continuous path by path. -/
theorem cumulativeDensityIntegral_rightContinuous
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => cumulativeDensityIntegral E u ω)
      (Set.Ici t) t := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero'
    (g := fun u => cumulativeVariation H u ω - cumulativeVariation H t ω)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Real.norm_eq_abs]
    exact abs_cumulativeDensityIntegral_sub_le E ω hu
  · have hV : ContinuousWithinAt
        (fun u => cumulativeVariation H u ω - cumulativeVariation H t ω)
        (Set.Ici t) t :=
      (cumulativeVariation_rightContinuous H E.rightContinuous ω t).sub
        continuousWithinAt_const
    simpa [ContinuousWithinAt] using hV

/-- The variation of the cumulative density integral is bounded by the
original pathwise Jordan variation. -/
theorem eVariationOn_cumulativeDensityIntegral_le_pathVariation
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    eVariationOn (fun t => cumulativeDensityIntegral E t ω) Set.univ ≤
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let := canonicalPathTotalVariation_isFiniteMeasure E ω
  apply iSup_le
  rintro ⟨n, u, hu, _huMem⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (cumulativeDensityIntegral E (u (i + 1)) ω)
          (cumulativeDensityIntegral E (u i) ω)) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal
          |cumulativeDensityIntegral E (u (i + 1)) ω -
            cumulativeDensityIntegral E (u i) ω| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_dist, Real.dist_eq]
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        (cumulativeVariation H (u (i + 1)) ω -
          cumulativeVariation H (u i) ω) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.ofReal_le_ofReal
        (abs_cumulativeDensityIntegral_sub_le E ω (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        (cumulativeVariation H (u (i + 1)) ω -
          cumulativeVariation H (u i) ω)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg.mpr <| by
        unfold cumulativeVariation
        exact measureReal_mono (Ioc_subset_Ioc_right (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal
        (cumulativeVariation H (u n) ω - cumulativeVariation H (u 0) ω) := by
      rw [Finset.sum_range_sub fun i => cumulativeVariation H (u i) ω]
    _ = ν (Ioc (u 0) (u n)) := by
      rw [← totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω
        (hu (Nat.zero_le n)), ofReal_measureReal]
    _ ≤ ν Set.univ := measure_mono (subset_univ _)

/-- The cumulative density integral has bounded variation on every sample
path.  Its variation is bounded by the original pathwise Jordan variation. -/
theorem cumulativeDensityIntegral_isBoundedVariation
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    BoundedVariationOn (fun t => cumulativeDensityIntegral E t ω) Set.univ := by
  let := canonicalPathTotalVariation_isFiniteMeasure E ω
  exact ne_of_lt
    ((eVariationOn_cumulativeDensityIntegral_le_pathVariation E ω).trans_lt
      (measure_lt_top _ _))

/-- The Stieltjes measure of the cumulative density integral is exactly the
pathwise Jordan variation weighted by the corrected density. -/
theorem signedMeasure_cumulativeDensityIntegral_eq_withDensity
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    FiniteVariationPath.signedMeasure
        (cumulativeDensityIntegral_isBoundedVariation E ω) =
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
          (fun t => jumpCorrectedCanonicalVariationDensity E (t, ω)) := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let h : ℝ≥0 → ℝ := fun t =>
    jumpCorrectedCanonicalVariationDensity E (t, ω)
  let C : ℝ≥0 → ℝ := fun t => cumulativeDensityIntegral E t ω
  let hC := cumulativeDensityIntegral_isBoundedVariation E ω
  have hRight : ∀ t, ContinuousWithinAt C (Set.Ici t) t :=
    cumulativeDensityIntegral_rightContinuous E ω
  have hInt : Integrable h ν :=
    integrable_jumpCorrectedCanonicalVariationDensity_section E ω
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [FiniteVariationPath.signedMeasure_Ioc hC hRight hab,
      withDensityᵥ_apply hInt measurableSet_Ioc]
    exact cumulativeDensityIntegral_sub E ω hab
  · let := canonicalPathTotalVariation_isFiniteMeasure E ω
    have hmono : Monotone fun T : ℝ≥0 => Ioc (0 : ℝ≥0) T := by
      intro a b hab
      exact Ioc_subset_Ioc_right hab
    have hSetLim : Tendsto (fun T : ℝ≥0 => ∫ t in Ioc 0 T, h t ∂ν) atTop
        (𝓝 (∫ t in ⋃ T : ℝ≥0, Ioc 0 T, h t ∂ν)) :=
      tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) hmono
        hInt.integrableOn
    have hcomp : (Ioi (0 : ℝ≥0))ᶜ = ({0} : Set ℝ≥0) := by
      ext t
      simp
    have hSingleton : (∫ t in ({0} : Set ℝ≥0), h t ∂ν) = 0 := by
      have hνzero : ν ({0} : Set ℝ≥0) = 0 :=
        totalVariation_singleton_zero H E.rightContinuous ω
      rw [integral_singleton, measureReal_def, hνzero]
      simp
    have hIoi : (∫ t in Ioi (0 : ℝ≥0), h t ∂ν) = ∫ t, h t ∂ν := by
      have hAdd := integral_add_compl (μ := ν) (s := Ioi (0 : ℝ≥0))
        measurableSet_Ioi hInt
      rw [hcomp, hSingleton, add_zero] at hAdd
      exact hAdd
    rw [iUnion_Ioc_right, hIoi] at hSetLim
    have hTop : Tendsto C atTop (𝓝 (∫ t, h t ∂ν)) := by
      simpa [C, h, cumulativeDensityIntegral, pathVariationMeasureUpTo]
        using hSetLim
    have hBot : limUnder atBot C = 0 := by
      rw [atBot_eq_pure_of_isBot isBot_bot]
      have hC0 : C 0 = 0 := by
        simp [C, cumulativeDensityIntegral, pathVariationMeasureUpTo]
      rw [(tendsto_pure_nhds C (⊥ : ℝ≥0)).limUnder_eq]
      exact hC0
    rw [FiniteVariationPath.signedMeasure_univ hC, hTop.limUnder_eq, hBot,
      sub_zero, withDensityᵥ_apply hInt MeasurableSet.univ, setIntegral_univ]

/-- The jump correction makes every left jump of the cumulative density
integral agree exactly with the corresponding jump of the original
finite-variation component. -/
theorem processLeftJump_cumulativeDensityIntegral_eq
    (E : SIntegrableFiniteVariationBridge H) (t : ℝ≥0) (ω : Ω) :
    processLeftJump (cumulativeDensityIntegral E) t ω =
      processLeftJump H.finiteVariationPart t ω := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let h : ℝ≥0 → ℝ := fun u =>
    jumpCorrectedCanonicalVariationDensity E (u, ω)
  have hInt : Integrable h ν :=
    integrable_jumpCorrectedCanonicalVariationDensity_section E ω
  have hMeasure := congrArg (fun m : SignedMeasure ℝ≥0 => m ({t} : Set ℝ≥0))
    (signedMeasure_cumulativeDensityIntegral_eq_withDensity E ω)
  rw [FiniteVariationPath.signedMeasure_singleton
      (cumulativeDensityIntegral_isBoundedVariation E ω)
      (cumulativeDensityIntegral_rightContinuous E ω) t,
    withDensityᵥ_apply hInt (MeasurableSet.singleton t),
    integral_singleton,
    signedMeasure_totalVariation_real_singleton,
    FiniteVariationPath.signedMeasure_singleton
      (H.finiteVariationPart_isBoundedVariation ω) (E.rightContinuous ω) t]
      at hMeasure
  have hJumpFormula :
      processLeftJump (cumulativeDensityIntegral E) t ω =
        |processLeftJump H.finiteVariationPart t ω| *
          jumpCorrectedCanonicalVariationDensity E (t, ω) := by
    simpa [processLeftJump, ν, h, smul_eq_mul] using hMeasure
  rw [hJumpFormula]
  by_cases hJump : processLeftJump H.finiteVariationPart t ω = 0
  · simp [hJump]
  · rw [jumpCorrectedCanonicalVariationDensity_eq_leftJump_div_abs E hJump]
    field_simp [abs_ne_zero.mpr hJump]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
