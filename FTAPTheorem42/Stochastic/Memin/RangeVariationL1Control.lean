/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationStieltjesCalculus

/-!
# Global variation L¹ control for the Mémín range candidate

The local S¹ normalization used to select the Mémín integrand controls the
stopped source variation and all successive output differences.  To obtain an
actual coefficient in the completed finite-variation space, one must also
control the zeroth output itself.  This module adds a geometric copy of that
base output variation to the same normalizing sequence.

The resulting equivalent finite measure simultaneously makes the base output
variation finite and the successive output variations summable.  The
pathwise Stieltjes identities on the actual carrier then imply that every
approximating integrand, and their canonical pointwise limit, belong to L¹ of
one stopped-source canonical variation measure.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

open SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Whole-axis path variation of the zeroth output after deterministic
stopping. -/
noncomputable def meminStoppedBaseOutputTotalVariation
    (T : ℝ≥0) (hT : 0 < T) (L : ℕ → SIntegrableStrategy D) : Ω → ℝ :=
  fun ω =>
    (FiniteVariationPath.signedMeasure
      (((L 0).toLocally.deterministicallyStopped T hT
        ).finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ

theorem meminStoppedBaseOutputTotalVariation_measurable
    (T : ℝ≥0) (hT : 0 < T) (L : ℕ → SIntegrableStrategy D) :
    Measurable (meminStoppedBaseOutputTotalVariation T hT L) := by
  exact measurable_totalVariation_univ_of_cumulativeVariation
    ((L 0).toLocally.deterministicallyStopped T hT
      ).finiteVariationPart_isRightContinuous

/-- The local S¹ normalizer augmented by a geometric copy of the base output
variation. -/
noncomputable def meminRangeVariationSequence
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) : ℕ → Ω → ℝ := fun k ω =>
  meminJointLocalS1Sequence G T hT L k ω +
    ((1 : ℝ) / 2) ^ k * meminStoppedBaseOutputTotalVariation T hT L ω

theorem meminRangeVariationSequence_measurable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) :
    Measurable (meminRangeVariationSequence G T hT L k) := by
  exact (meminJointLocalS1Sequence_measurable G T hT L k).add
    ((meminStoppedBaseOutputTotalVariation_measurable T hT L).const_mul
      (((1 : ℝ) / 2) ^ k))

theorem meminRangeVariationSequence_nonnegative
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    0 ≤ meminRangeVariationSequence G T hT L k ω := by
  exact add_nonneg (meminJointLocalS1Sequence_nonnegative G T hT L k ω)
    (mul_nonneg (by positivity) measureReal_nonneg)

theorem meminJointLocalS1Sequence_le_rangeVariation
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    meminJointLocalS1Sequence G T hT L k ω ≤
      meminRangeVariationSequence G T hT L k ω := by
  unfold meminRangeVariationSequence
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) measureReal_nonneg)

theorem meminStoppedBaseOutputTotalVariation_le_rangeVariation
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (ω : Ω) :
    meminStoppedBaseOutputTotalVariation T hT L ω ≤
      meminRangeVariationSequence G T hT L 0 ω := by
  simp only [meminRangeVariationSequence, pow_zero, one_mul]
  exact le_add_of_nonneg_left
    (meminJointLocalS1Sequence_nonnegative G T hT L 0 ω)

theorem meminRangeVariationSequence_summable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    ∀ᵐ ω ∂μ, Summable (fun k =>
      meminRangeVariationSequence G T hT L k ω) := by
  filter_upwards [meminJointLocalS1Sequence_summable G T hT L
      hVariationSummable hMartingaleSummable] with ω hω
  exact hω.add (summable_geometric_two.mul_right
    (meminStoppedBaseOutputTotalVariation T hT L ω))

/-- Common equivalent measure for source variation, base output variation,
successive output differences, and martingale envelopes. -/
noncomputable def meminRangeVariationReferenceMeasure
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) : Measure Ω :=
  MeminEquivalentFiniteVariationMeasure.referenceMeasure μ
    (meminRangeVariationSequence G T hT L)

/-- Stopped-source bridge over the range normalizer. -/
noncomputable def meminRangeSourceFiniteVariationBridge
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    SIntegrableFiniteVariationBridge (G.deterministicallyStopped T hT) :=
  SIntegrableFiniteVariationBridge.ofDominatedSummableSequence
    (meminRangeVariationSequence G T hT L)
    (meminRangeVariationSequence_measurable G T hT L)
    (meminRangeVariationSequence_nonnegative G T hT L)
    (meminRangeVariationSequence_summable G T hT L
      hVariationSummable hMartingaleSummable)
    0 fun ω =>
      (meminStoppedSourceTotalVariation_le_joint G T hT L ω).trans <|
        (meminJointVariationSequence_le_jointLocalS1 G T hT L 0 ω).trans <|
          meminJointLocalS1Sequence_le_rangeVariation G T hT L 0 ω

/-- Canonical predictable variation control carried by the augmented
stopped-source bridge. -/
noncomputable def meminRangeVariationControl
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    MeminPredictableControlMeasure ℱ :=
  canonicalVariationMeasure
    (meminRangeSourceFiniteVariationBridge G T hT L
      hVariationSummable hMartingaleSummable)

/-- Bridge for the deterministically stopped base output over the same range
normalizer. -/
noncomputable def meminRangeBaseOutputFiniteVariationBridge
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    SIntegrableFiniteVariationBridge
      ((L 0).toLocally.deterministicallyStopped T hT) :=
  SIntegrableFiniteVariationBridge.ofDominatedSummableSequence
    (meminRangeVariationSequence G T hT L)
    (meminRangeVariationSequence_measurable G T hT L)
    (meminRangeVariationSequence_nonnegative G T hT L)
    (meminRangeVariationSequence_summable G T hT L
      hVariationSummable hMartingaleSummable)
    0 (meminStoppedBaseOutputTotalVariation_le_rangeVariation G T hT L)

/-- Bridge for one deterministically stopped successive output difference
over the same range normalizer. -/
noncomputable def meminRangeStoppedDifferenceFiniteVariationBridge
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω))
    (k : ℕ) :
    SIntegrableFiniteVariationBridge
      ((lemma411Difference (L (k + 1)) (L k)).toLocally
        |>.deterministicallyStopped T hT) :=
  SIntegrableFiniteVariationBridge.ofDominatedSummableSequence
    (meminRangeVariationSequence G T hT L)
    (meminRangeVariationSequence_measurable G T hT L)
    (meminRangeVariationSequence_nonnegative G T hT L)
    (meminRangeVariationSequence_summable G T hT L
      hVariationSummable hMartingaleSummable)
    k fun ω =>
      (deterministicallyStopped_lemma411Difference_totalVariation_le
        (L (k + 1)) (L k) T hT ω).trans <|
          (lemma411DifferenceTotalVariation_le_joint G T hT L k ω).trans <|
            (meminJointVariationSequence_le_jointLocalS1 G T hT L k ω).trans <|
              meminJointLocalS1Sequence_le_rangeVariation G T hT L k ω

theorem meminRangeSourceFiniteVariationBridge_referenceMeasure_eq
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    (meminRangeSourceFiniteVariationBridge G T hT L
      hVariationSummable hMartingaleSummable).referenceMeasure =
        meminRangeVariationReferenceMeasure G T hT L := by
  exact
    SIntegrableFiniteVariationBridge.ofDominatedSummableSequence_referenceMeasure_eq
      (meminRangeVariationSequence G T hT L)
      (meminRangeVariationSequence_measurable G T hT L)
      (meminRangeVariationSequence_nonnegative G T hT L)
      (meminRangeVariationSequence_summable G T hT L
        hVariationSummable hMartingaleSummable)
      0 fun ω =>
        (meminStoppedSourceTotalVariation_le_joint G T hT L ω).trans <|
          (meminJointVariationSequence_le_jointLocalS1 G T hT L 0 ω).trans <|
            meminJointLocalS1Sequence_le_rangeVariation G T hT L 0 ω

theorem meminRangeBaseOutputFiniteVariationBridge_referenceMeasure_eq
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    (meminRangeBaseOutputFiniteVariationBridge G T hT L
      hVariationSummable hMartingaleSummable).referenceMeasure =
        meminRangeVariationReferenceMeasure G T hT L := by
  exact
    SIntegrableFiniteVariationBridge.ofDominatedSummableSequence_referenceMeasure_eq
      (meminRangeVariationSequence G T hT L)
      (meminRangeVariationSequence_measurable G T hT L)
      (meminRangeVariationSequence_nonnegative G T hT L)
      (meminRangeVariationSequence_summable G T hT L
        hVariationSummable hMartingaleSummable)
      0 (meminStoppedBaseOutputTotalVariation_le_rangeVariation G T hT L)

theorem meminRangeStoppedDifferenceFiniteVariationBridge_referenceMeasure_eq
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω))
    (k : ℕ) :
    (meminRangeStoppedDifferenceFiniteVariationBridge G T hT L
      hVariationSummable hMartingaleSummable k).referenceMeasure =
        meminRangeVariationReferenceMeasure G T hT L := by
  exact
    SIntegrableFiniteVariationBridge.ofDominatedSummableSequence_referenceMeasure_eq
      (meminRangeVariationSequence G T hT L)
      (meminRangeVariationSequence_measurable G T hT L)
      (meminRangeVariationSequence_nonnegative G T hT L)
      (meminRangeVariationSequence_summable G T hT L
        hVariationSummable hMartingaleSummable)
      k fun ω =>
        (deterministicallyStopped_lemma411Difference_totalVariation_le
          (L (k + 1)) (L k) T hT ω).trans <|
            (lemma411DifferenceTotalVariation_le_joint G T hT L k ω).trans <|
              (meminJointVariationSequence_le_jointLocalS1 G T hT L k ω).trans <|
                meminJointLocalS1Sequence_le_rangeVariation G T hT L k ω

/-- The stopped successive-output canonical variation masses remain
summable under the augmented range normalizer. -/
theorem tsum_meminRangeStoppedDifference_canonicalVariationMeasure_ne_top
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    (∑' k, canonicalVariationMeasure
      (meminRangeStoppedDifferenceFiniteVariationBridge G T hT L
        hVariationSummable hMartingaleSummable k) Set.univ) ≠ ∞ := by
  simp_rw [canonicalVariationMeasure_univ_eq_lintegral_totalVariation,
    meminRangeStoppedDifferenceFiniteVariationBridge_referenceMeasure_eq
      G T hT L hVariationSummable hMartingaleSummable]
  apply ne_top_of_le_ne_top
    (MeminEquivalentFiniteVariationMeasure.tsum_lintegral_referenceMeasure_ne_top
      (μ := μ) (meminRangeVariationSequence_measurable G T hT L))
  apply ENNReal.tsum_le_tsum
  intro k
  apply lintegral_mono
  intro ω
  exact ENNReal.ofReal_le_ofReal <|
    (deterministicallyStopped_lemma411Difference_totalVariation_le
      (L (k + 1)) (L k) T hT ω).trans <|
        (lemma411DifferenceTotalVariation_le_joint G T hT L k ω).trans <|
          (meminJointVariationSequence_le_jointLocalS1 G T hT L k ω).trans <|
            meminJointLocalS1Sequence_le_rangeVariation G T hT L k ω

end SIntegrablePredictableMultiplierLinearL2Calculus

namespace SIntegrableFiniteVariationStieltjesCalculus

open SIntegrableFiniteVariationBridge
open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}
  {G : ActualLocallySIntegrableStrategy R}

/-- The zeroth actual integrand is globally L¹ under the augmented stopped
source control. -/
theorem meminBaseIntegrand_memLp_one_rangeVariation
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (T : ℝ≥0) (hT : 0 < T)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω)) :
    MemLp (Function.uncurry (L 0).val.integrand) 1
      (meminRangeVariationControl G.val T hT
        (ActualSIntegrableStrategy.rawSequence L)
          hVariationSummable hMartingaleSummable) := by
  let raw := ActualSIntegrableStrategy.rawSequence L
  let source := meminRangeSourceFiniteVariationBridge G.val T hT raw
    hVariationSummable hMartingaleSummable
  let target := meminRangeBaseOutputFiniteVariationBridge G.val T hT raw
    hVariationSummable hMartingaleSummable
  change MemLp (Function.uncurry (L 0).val.integrand) 1
    (canonicalVariationMeasure source)
  have hDensity : ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
              (L 0).val.integrand t ω) =
        FiniteVariationPath.signedMeasure
          (((L 0).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) := by
    filter_upwards [C.finiteVariationPart_stopped_signedMeasure (L 0) T hT,
      source.jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection]
        with ω hStieltjes hDirection
    refine (WithDensityᵥEq.congr_ae ?_).trans hStieltjes
    filter_upwards [hDirection] with t ht
    rw [ht]
    rfl
  have hMass :=
    integrandLIntegral_eq_canonicalVariation_of_pathwiseDensity
      source (L 0).val target
      ((meminRangeSourceFiniteVariationBridge_referenceMeasure_eq
          G.val T hT raw hVariationSummable hMartingaleSummable).trans
        (meminRangeBaseOutputFiniteVariationBridge_referenceMeasure_eq
          G.val T hT raw hVariationSummable hMartingaleSummable).symm)
      (C.finiteVariationPart_stopped_integrable (L 0) T hT) hDensity
  apply memLp_one_iff_integrable.mpr
  refine ⟨(L 0).val.integrand_isPredictable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
  simpa only [Function.uncurry, Real.enorm_eq_ofReal_abs] using
    hMass.trans_ne
      (measure_ne_top (canonicalVariationMeasure target) Set.univ)

/-- One successive integrand difference has exactly the canonical variation
mass of its stopped output difference. -/
theorem meminIntegrandDifferenceLIntegral_eq_rangeVariation
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (T : ℝ≥0) (hT : 0 < T)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω))
    (k : ℕ) :
    meminIntegrandDifferenceLIntegral
        (meminRangeVariationControl G.val T hT
          (ActualSIntegrableStrategy.rawSequence L)
            hVariationSummable hMartingaleSummable)
        (L (k + 1)).val (L k).val =
      canonicalVariationMeasure
        (meminRangeStoppedDifferenceFiniteVariationBridge G.val T hT
          (ActualSIntegrableStrategy.rawSequence L)
            hVariationSummable hMartingaleSummable k) Set.univ := by
  let raw := ActualSIntegrableStrategy.rawSequence L
  let source := meminRangeSourceFiniteVariationBridge G.val T hT raw
    hVariationSummable hMartingaleSummable
  let target := meminRangeStoppedDifferenceFiniteVariationBridge G.val T hT
    raw hVariationSummable hMartingaleSummable k
  apply
    meminIntegrandDifferenceLIntegral_eq_canonicalVariation_of_pathwiseDensity
      source (L (k + 1)).val (L k).val target
  · exact
      (meminRangeSourceFiniteVariationBridge_referenceMeasure_eq
        G.val T hT raw hVariationSummable hMartingaleSummable).trans
      (meminRangeStoppedDifferenceFiniteVariationBridge_referenceMeasure_eq
        G.val T hT raw hVariationSummable hMartingaleSummable k).symm
  · exact C.meminIntegrandDifference_stopped_pathIntegrable
      (L (k + 1)) (L k) T hT
  · exact C.meminIntegrandDifference_stopped_pathDensity
      (L (k + 1)) (L k) T hT source

/-- The successive distances of the actual integrands are summable under
the common augmented variation control. -/
theorem tsum_meminApproximantIntegrand_edist_rangeVariation_ne_top
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (T : ℝ≥0) (hT : 0 < T)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω)) :
    (∑' k, ∫⁻ p,
      edist ((L (k + 1)).val.integrand p.1 p.2)
        ((L k).val.integrand p.1 p.2)
        ∂meminRangeVariationControl G.val T hT
          (ActualSIntegrableStrategy.rawSequence L)
            hVariationSummable hMartingaleSummable) ≠ ∞ := by
  let raw := ActualSIntegrableStrategy.rawSequence L
  let source := meminRangeSourceFiniteVariationBridge G.val T hT raw
    hVariationSummable hMartingaleSummable
  change (∑' k, ∫⁻ p,
    edist ((L (k + 1)).val.integrand p.1 p.2)
      ((L k).val.integrand p.1 p.2)
      ∂canonicalVariationMeasure source) ≠ ∞
  have hStepEq : (fun k => ∫⁻ p,
      edist ((L (k + 1)).val.integrand p.1 p.2)
        ((L k).val.integrand p.1 p.2)
        ∂canonicalVariationMeasure source) = fun k =>
      canonicalVariationMeasure
        (meminRangeStoppedDifferenceFiniteVariationBridge G.val T hT raw
          hVariationSummable hMartingaleSummable k) Set.univ := by
    funext k
    rw [← C.meminIntegrandDifferenceLIntegral_eq_rangeVariation
      L T hT hVariationSummable hMartingaleSummable k]
    simp only [meminIntegrandDifferenceLIntegral,
      meminIntegrandDifference, edist_dist, Real.dist_eq]
    rfl
  rw [hStepEq]
  exact tsum_meminRangeStoppedDifference_canonicalVariationMeasure_ne_top
    G.val T hT raw hVariationSummable hMartingaleSummable

/-- The canonical Mémín limit integrand belongs to the same augmented
stopped-source L¹ space. -/
theorem meminLimitIntegrand_memLp_one_rangeVariation
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (T : ℝ≥0) (hT : 0 < T)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω)) :
    MemLp (Function.uncurry (meminLimitIntegrand
      (ActualSIntegrableStrategy.rawSequence L))) 1
        (meminRangeVariationControl G.val T hT
          (ActualSIntegrableStrategy.rawSequence L)
            hVariationSummable hMartingaleSummable) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  change MemLp (fun p : ℝ≥0 × Ω =>
    limUnder atTop (fun n => (L n).val.integrand p.1 p.2)) 1
      (meminRangeVariationControl G.val T hT
        (ActualSIntegrableStrategy.rawSequence L)
          hVariationSummable hMartingaleSummable)
  exact MeminL1.memLp_one_limUnder_of_summable_steps
    (ν := meminRangeVariationControl G.val T hT
      (ActualSIntegrableStrategy.rawSequence L)
        hVariationSummable hMartingaleSummable)
    (fun n p => (L n).val.integrand p.1 p.2)
    (fun n => (L n).val.integrand_isPredictable.aestronglyMeasurable)
    (C.meminBaseIntegrand_memLp_one_rangeVariation L T hT
      hVariationSummable hMartingaleSummable)
    (C.tsum_meminApproximantIntegrand_edist_rangeVariation_ne_top
      L T hT hVariationSummable hMartingaleSummable)

end SIntegrableFiniteVariationStieltjesCalculus

end FTAPTheorem42
