/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.ContinuousFiniteVariationMartingale
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import FTAPTheorem42.Foundations.ProcessIndistinguishable
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansResidual

/-!
# Rigidity of the Doléans finite-variation residual

The difference between the original predictable finite-variation component
and the pathwise integral of its predictable Doléans density is already a
continuous true martingale under an equivalent reference measure.  This
module supplies its square-integrable random variation bound and applies
continuous finite-variation martingale rigidity.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

open ContinuousFiniteVariationMartingale

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- Pathwise Jordan variation bounds the metric variation of the
finite-variation path. -/
theorem eVariationOn_finiteVariationPart_le_pathVariation
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    eVariationOn (fun t => H.finiteVariationPart t ω) Set.univ ≤
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
          Set.univ := by
  let A : ℝ≥0 → ℝ := fun t => H.finiteVariationPart t ω
  let hA : BoundedVariationOn A Set.univ :=
    H.finiteVariationPart_isBoundedVariation ω
  calc
    eVariationOn A Set.univ ≤
        (FiniteVariationPath.signedMeasure hA).variation Set.univ :=
      FiniteVariationPath.eVariationOn_univ_le_variation_univ hA
        (E.rightContinuous ω)
    _ = (FiniteVariationPath.signedMeasure hA).totalVariation Set.univ := by
      rw [signedMeasure_totalVariation_eq_variation]

/-- The Doléans residual has variation at most twice the path's Jordan
variation. -/
theorem eVariationOn_doleansResidual_le_pathVariation
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    eVariationOn (fun t => doleansResidual E t ω) Set.univ ≤
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ +
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, huMem⟩
  have hTerm (i : ℕ) :
      edist (doleansResidual E (u (i + 1)) ω)
          (doleansResidual E (u i) ω) ≤
        edist (H.finiteVariationPart (u (i + 1)) ω)
            (H.finiteVariationPart (u i) ω) +
          edist (cumulativeDensityIntegral E (u (i + 1)) ω)
            (cumulativeDensityIntegral E (u i) ω) := by
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    change
      |((H.finiteVariationPart (u (i + 1)) ω -
          H.finiteVariationPart 0 ω) -
          cumulativeDensityIntegral E (u (i + 1)) ω) -
        ((H.finiteVariationPart (u i) ω -
          H.finiteVariationPart 0 ω) -
          cumulativeDensityIntegral E (u i) ω)| ≤ _
    calc
      |((H.finiteVariationPart (u (i + 1)) ω -
          H.finiteVariationPart 0 ω) -
          cumulativeDensityIntegral E (u (i + 1)) ω) -
        ((H.finiteVariationPart (u i) ω -
          H.finiteVariationPart 0 ω) -
          cumulativeDensityIntegral E (u i) ω)| =
          |(H.finiteVariationPart (u (i + 1)) ω -
              H.finiteVariationPart (u i) ω) +
            -(cumulativeDensityIntegral E (u (i + 1)) ω -
              cumulativeDensityIntegral E (u i) ω)| := by
        congr 1
        ring
      _ ≤ |H.finiteVariationPart (u (i + 1)) ω -
            H.finiteVariationPart (u i) ω| +
          |-(cumulativeDensityIntegral E (u (i + 1)) ω -
            cumulativeDensityIntegral E (u i) ω)| := abs_add_le _ _
      _ = |H.finiteVariationPart (u (i + 1)) ω -
            H.finiteVariationPart (u i) ω| +
          |cumulativeDensityIntegral E (u (i + 1)) ω -
            cumulativeDensityIntegral E (u i) ω| := by rw [abs_neg]
  calc
    (∑ i ∈ Finset.range n,
        edist (doleansResidual E (u (i + 1)) ω)
          (doleansResidual E (u i) ω)) ≤
        ∑ i ∈ Finset.range n,
          (edist (H.finiteVariationPart (u (i + 1)) ω)
              (H.finiteVariationPart (u i) ω) +
            edist (cumulativeDensityIntegral E (u (i + 1)) ω)
              (cumulativeDensityIntegral E (u i) ω)) := by
      exact Finset.sum_le_sum fun i _ => hTerm i
    _ = (∑ i ∈ Finset.range n,
          edist (H.finiteVariationPart (u (i + 1)) ω)
            (H.finiteVariationPart (u i) ω)) +
        ∑ i ∈ Finset.range n,
          edist (cumulativeDensityIntegral E (u (i + 1)) ω)
            (cumulativeDensityIntegral E (u i) ω) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn (fun t => H.finiteVariationPart t ω) Set.univ +
        eVariationOn (fun t => cumulativeDensityIntegral E t ω)
          Set.univ := by
      exact add_le_add (eVariationOn.sum_le (f := fun t => H.finiteVariationPart t ω) hu huMem)
        (eVariationOn.sum_le (f := fun t => cumulativeDensityIntegral E t ω) hu huMem)
    _ ≤ _ + _ := by
      exact add_le_add
        (eVariationOn_finiteVariationPart_le_pathVariation E ω)
        (eVariationOn_cumulativeDensityIntegral_le_pathVariation E ω)

/-- At every deterministic time, the Doléans residual vanishes almost
everywhere. -/
theorem doleansResidual_ae_eq_zero
    (E : SIntegrableFiniteVariationBridge H) (T : ℝ≥0) :
    doleansResidual E T =ᵐ[μ] 0 := by
  let V : Ω → ℝ := fun ω =>
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ +
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ
  have hVMem : MemLp V (2 : ℝ≥0∞) E.referenceMeasure :=
    E.variationMemLpTwo.add E.variationMemLpTwo
  have hVNonneg (ω : Ω) : 0 ≤ V ω := by
    dsimp only [V]
    positivity
  have hV (ω : Ω) :
      eVariationOn (fun t => doleansResidual E t ω) Set.univ ≤
        ENNReal.ofReal (V ω) := by
    let ν := (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
    let : IsFiniteMeasure ν := by
      dsimp only [ν]
      unfold SignedMeasure.totalVariation
      infer_instance
    calc
      eVariationOn (fun t => doleansResidual E t ω) Set.univ ≤
          (FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
              Set.univ +
          (FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
              Set.univ :=
        eVariationOn_doleansResidual_le_pathVariation E ω
      _ = ENNReal.ofReal (V ω) := by
        change ν Set.univ + ν Set.univ =
          ENNReal.ofReal (ν.real Set.univ + ν.real Set.univ)
        rw [ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg),
          ofReal_measureReal]
  have : IsFiniteMeasure
      (μ.withDensity fun ω => (E.referenceDensity ω : ℝ≥0∞)) :=
    referenceMeasure.instIsFiniteMeasure E
  have hEqReference :=
    martingale_ae_eq_initial_of_ae_continuous_eVariationOn_le_memLp
      (doleansResidual_martingale E)
      (Filter.Eventually.of_forall (doleansResidual_continuous E)) V hVMem
      (Filter.Eventually.of_forall hVNonneg) (Filter.Eventually.of_forall hV) T
  have hEq : doleansResidual E T =ᵐ[μ] doleansResidual E 0 :=
    E.referenceMeasure_ae_eq_iff.mp hEqReference
  filter_upwards [hEq] with ω hω
  rw [hω]
  simp [doleansResidual, cumulativeDensityIntegral, pathVariationMeasureUpTo]

/-- The Doléans residual vanishes outside one null set simultaneously at all
times. -/
theorem doleansResidual_indistinguishable_zero
    (E : SIntegrableFiniteVariationBridge H) :
    ProcessIndistinguishable μ (doleansResidual E) (fun _ _ => 0) := by
  apply ProcessIndistinguishable.of_ae_eq_on_rightDense
    (doleansResidual E) (fun _ _ => 0)
    NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
  · exact Filter.Eventually.of_forall fun ω t =>
      (doleansResidual_continuous E ω).continuousWithinAt
  · exact Filter.Eventually.of_forall fun _ _ => continuous_const.continuousWithinAt
  · intro k
    exact doleansResidual_ae_eq_zero E _

/-- The finite-variation component, normalized at time zero, is
indistinguishable from the cumulative integral of its predictable Doléans
density. -/
theorem finiteVariationPart_sub_initial_indistinguishable_cumulativeDensityIntegral
    (E : SIntegrableFiniteVariationBridge H) :
    ProcessIndistinguishable μ
      (fun t ω => H.finiteVariationPart t ω -
        H.finiteVariationPart 0 ω)
      (cumulativeDensityIntegral E) := by
  filter_upwards [doleansResidual_indistinguishable_zero E] with ω hω
  intro t
  have ht := hω t
  rw [doleansResidual] at ht
  linarith

/-- Outside one null set, the signed Stieltjes measure of the original
finite-variation path equals that of the cumulative density integral. -/
theorem signedMeasure_finiteVariationPart_eq_cumulativeDensityIntegral_ae
    (E : SIntegrableFiniteVariationBridge H) :
    ∀ᵐ ω ∂μ,
      FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω) =
        FiniteVariationPath.signedMeasure
          (cumulativeDensityIntegral_isBoundedVariation E ω) := by
  filter_upwards [
    finiteVariationPart_sub_initial_indistinguishable_cumulativeDensityIntegral E]
      with ω hω
  let A : ℝ≥0 → ℝ := fun t => H.finiteVariationPart t ω
  let C : ℝ≥0 → ℝ := fun t => cumulativeDensityIntegral E t ω
  let hA : BoundedVariationOn A Set.univ :=
    H.finiteVariationPart_isBoundedVariation ω
  let hC : BoundedVariationOn C Set.univ :=
    cumulativeDensityIntegral_isBoundedVariation E ω
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [FiniteVariationPath.signedMeasure_Ioc hA (E.rightContinuous ω) hab,
      FiniteVariationPath.signedMeasure_Ioc hC
        (cumulativeDensityIntegral_rightContinuous E ω) hab]
    dsimp only [A, C]
    rw [← hω b, ← hω a]
    ring
  · rw [FiniteVariationPath.signedMeasure_univ hA,
      FiniteVariationPath.signedMeasure_univ hC]
    have hATop := hA.tendsto_atTop_limUnder
    have hCTop := hC.tendsto_atTop_limUnder
    have hCToExpected : Tendsto C atTop
        (𝓝 (limUnder atTop A - A 0)) := by
      apply (hATop.sub tendsto_const_nhds).congr'
      exact Filter.Eventually.of_forall fun t => hω t
    have hTopEq : limUnder atTop C = limUnder atTop A - A 0 :=
      tendsto_nhds_unique hCTop hCToExpected
    have hABot : limUnder atBot A = A 0 := by
      rw [atBot_eq_pure_of_isBot isBot_bot]
      exact (tendsto_pure_nhds A 0).limUnder_eq
    have hCBot : limUnder atBot C = C 0 := by
      rw [atBot_eq_pure_of_isBot isBot_bot]
      exact (tendsto_pure_nhds C 0).limUnder_eq
    have hCZero : C 0 = 0 := by
      have hzero := hω 0
      dsimp only [A, C] at hzero ⊢
      linarith
    rw [hTopEq, hABot, hCBot, hCZero]
    ring

/-- The predictable Doléans density represents the original signed
Stieltjes measure on almost every path. -/
theorem signedMeasure_finiteVariationPart_eq_withDensity_ae
    (E : SIntegrableFiniteVariationBridge H) :
    ∀ᵐ ω ∂μ,
      FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω) =
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t => jumpCorrectedCanonicalVariationDensity E (t, ω)) := by
  filter_upwards [
    signedMeasure_finiteVariationPart_eq_cumulativeDensityIntegral_ae E]
      with ω hω
  exact hω.trans (signedMeasure_cumulativeDensityIntegral_eq_withDensity E ω)

/-- On almost every sample path, the predictable Doléans density has unit
absolute value for pathwise Jordan total variation. -/
theorem abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one_pathwise
    (E : SIntegrableFiniteVariationBridge H) :
    ∀ᵐ ω ∂μ,
      (fun t => |jumpCorrectedCanonicalVariationDensity E (t, ω)|) =ᵐ[
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation]
        (fun _ => (1 : ℝ)) := by
  filter_upwards [signedMeasure_finiteVariationPart_eq_withDensity_ae E]
      with ω hMeasure
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let h : ℝ≥0 → ℝ := fun t =>
    jumpCorrectedCanonicalVariationDensity E (t, ω)
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hInt : Integrable h ν :=
    integrable_jumpCorrectedCanonicalVariationDensity_section E ω
  have hVariation := congrArg VectorMeasure.variation hMeasure
  rw [← signedMeasure_totalVariation_eq_variation,
    Measure.variation_withDensityᵥ hInt] at hVariation
  have hDensityMeasure :
      ν.withDensity (fun t => ‖h t‖ₑ) =
        ν.withDensity (fun _ => (1 : ℝ≥0∞)) := by
    simpa only [withDensity_const, one_smul] using hVariation.symm
  have hEnormEq :
      (fun t => ‖h t‖ₑ) =ᵐ[ν] (fun _ => (1 : ℝ≥0∞)) :=
    (withDensity_eq_iff_of_sigmaFinite
      hInt.aestronglyMeasurable.enorm aemeasurable_const).mp hDensityMeasure
  filter_upwards [hEnormEq] with t ht
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_eq_one] using ht

/-- The predictable Doléans density has unit absolute value for the
integrated pathwise Jordan-variation measure. -/
theorem abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one
    (E : SIntegrableFiniteVariationBridge H) :
    (fun p => |jumpCorrectedCanonicalVariationDensity E p|) =ᵐ[
      canonicalVariationMeasure E] (fun _ => (1 : ℝ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let G : Set (ℝ≥0 × Ω) :=
    {p | |jumpCorrectedCanonicalVariationDensity E p| = 1}
  have hG : MeasurableSet[ℱ.predictable] G := by
    change MeasurableSet[ℱ.predictable]
      ((fun p => |jumpCorrectedCanonicalVariationDensity E p|) ⁻¹' {1})
    exact MeasurableSet.preimage (MeasurableSet.singleton 1)
      (continuous_abs.measurable.comp
        (jumpCorrectedCanonicalVariationDensity_stronglyMeasurable E
          |>.measurable))
  have hSectionZero : ∀ᵐ ω ∂μ,
      canonicalTotalVariationKernel E ω
        ((fun t => (t, ω)) ⁻¹' Gᶜ) = 0 := by
    filter_upwards [
      abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one_pathwise E]
        with ω hω
    rw [canonicalTotalVariationKernel_apply]
    have hGoodMem :
        {t : ℝ≥0 |
          |jumpCorrectedCanonicalVariationDensity E (t, ω)| = 1} ∈
            ae (FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation :=
      hω
    have hZero := mem_ae_iff.mp hGoodMem
    change (E.referenceDensity ω •
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation)
          {t | |jumpCorrectedCanonicalVariationDensity E (t, ω)| = 1}ᶜ = 0
    rw [Measure.smul_apply, hZero]
    simp
  have hBadZero : canonicalVariationMeasure E Gᶜ = 0 := by
    rw [← predictableMeasure_canonicalTotalVariationKernel_eq E,
      PredictableKernelMeasure.predictableMeasure_apply hG.compl]
    calc
      (∫⁻ ω, canonicalTotalVariationKernel E ω
          ((fun t => (t, ω)) ⁻¹' Gᶜ) ∂μ) =
          ∫⁻ _ : Ω, 0 ∂μ := lintegral_congr_ae hSectionZero
      _ = 0 := lintegral_zero
  change G ∈ ae (canonicalVariationMeasure E)
  rw [mem_ae_iff]
  exact hBadZero

/-- Doléans--Dade variation identity: the total variation of the canonical
signed predictable measure is exactly integrated pathwise Jordan variation. -/
theorem totalVariation_canonicalMeasure_eq_canonicalVariationMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableSignedMeasure.totalVariation E.canonicalMeasure =
      canonicalVariationMeasure E := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let h := jumpCorrectedCanonicalVariationDensity E
  have hInt : Integrable h (canonicalVariationMeasure E) := by
    apply (integrable_const (1 : ℝ)).mono'
      (jumpCorrectedCanonicalVariationDensity_stronglyMeasurable E
        |>.aestronglyMeasurable)
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_jumpCorrectedCanonicalVariationDensity_le_one E p
  have hVariation := congrArg VectorMeasure.variation
    (withDensity_jumpCorrectedCanonicalVariationDensity_eq_canonicalMeasure E)
  rw [Measure.variation_withDensityᵥ hInt,
    ← signedMeasure_totalVariation_eq_variation] at hVariation
  calc
    PredictableSignedMeasure.totalVariation E.canonicalMeasure =
        (canonicalVariationMeasure E).withDensity
          (fun p => ‖h p‖ₑ) := hVariation.symm
    _ = (canonicalVariationMeasure E).withDensity
        (fun _ => (1 : ℝ≥0∞)) := by
      apply withDensity_congr_ae
      filter_upwards [abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one E]
        with p hp
      rw [Real.enorm_eq_ofReal_abs, hp, ENNReal.ofReal_one]
    _ = canonicalVariationMeasure E := by
      simp only [withDensity_const, one_smul]

/-- Real-mass form of the Doléans--Dade identity used by predictable Hahn
selection. -/
theorem canonicalMeasure_totalVariationMass_eq_kernelMass
    (E : SIntegrableFiniteVariationBridge H) :
    (PredictableSignedMeasure.totalVariation E.canonicalMeasure).real
        Set.univ =
      (PredictableKernelMeasure.predictableMeasure ℱ μ
        (canonicalPositiveKernel E)).real Set.univ +
      (PredictableKernelMeasure.predictableMeasure ℱ μ
        (canonicalNegativeKernel E)).real Set.univ := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  rw [totalVariation_canonicalMeasure_eq_canonicalVariationMeasure E,
    canonicalVariationMeasure, measureReal_add_apply]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
