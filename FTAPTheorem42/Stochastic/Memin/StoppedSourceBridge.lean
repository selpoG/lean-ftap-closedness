/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Memin.FiniteVariationBridge

/-!
# Joint Doléans normalization for stopped sources and Mémín differences

For each deterministic source horizon, this module places the stopped
finite-variation source and all successive Lemma 4.11 finite-variation
differences over one equivalent finite measure.  A small geometric copy of
the source variation is added to every difference variation before applying
the squared reciprocal normalization.  Thus the zeroth normalizing term
dominates the source variation, while every term dominates the corresponding
output variation.

The everywhere-positive repaired densities may differ on the exceptional
set where the joint envelope is infinite.  They nevertheless induce the same
reference measure because they all agree almost everywhere with the joint
density.  This removes the measure-normalization part of the stochastic
realization boundary; only the actual stochastic-integral density identities
and their integrability remain as inputs to the final consumer below.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

open MeminEquivalentFiniteVariationMeasure

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- A finite-variation process whose path variation is dominated by one term
of an almost surely summable nonnegative sequence admits a Doléans bridge
over the sequence's normalized reference measure. -/
noncomputable def ofDominatedSummableSequence
    (V : ℕ → Ω → ℝ) (hV : ∀ n, Measurable (V n))
    (hVNonnegative : ∀ n ω, 0 ≤ V n ω)
    (hSummable : ∀ᵐ ω ∂μ, Summable (fun n => V n ω))
    (n : ℕ)
    (hDominates : ∀ ω,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ ≤ V n ω) :
    SIntegrableFiniteVariationBridge H := by
  apply ofCumulativeVariationWithDensity
    (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity V n)
    (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity_measurable
      hV n)
    (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity_pos V n)
    (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity_le_one V n)
    (C := 1) ENNReal.one_lt_top
  · intro ω
    let ν := FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)
    let : IsFiniteMeasure ν.totalVariation := by
      dsimp only [ν]
      unfold SignedMeasure.totalVariation
      infer_instance
    have hTop : ν.totalVariation Set.univ ≠ ∞ := measure_ne_top _ _
    rw [← ofReal_measureReal hTop]
    calc
      (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity V n ω :
          ℝ≥0∞) * ENNReal.ofReal (ν.totalVariation.real Set.univ) ≤
          (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity V n ω :
            ℝ≥0∞) * ENNReal.ofReal (V n ω) := by
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hDominates ω)) _
      _ ≤ 1 :=
        MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity_mul_term_le_one
          V n ω
  · rw [withDensity_repairedReferenceDensity_eq_referenceMeasure hSummable n]
    apply (MeminEquivalentFiniteVariationMeasure.term_memLp_two_referenceMeasure
      hV hVNonnegative n).mono'
      (measurable_totalVariation_univ_of_cumulativeVariation
        H.finiteVariationPart_isRightContinuous).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hDominates ω

/-- The bridge constructed from a dominated summable sequence uses exactly
the sequence's common normalized reference measure. -/
theorem ofDominatedSummableSequence_referenceMeasure_eq
    (V : ℕ → Ω → ℝ) (hV : ∀ n, Measurable (V n))
    (hVNonnegative : ∀ n ω, 0 ≤ V n ω)
    (hSummable : ∀ᵐ ω ∂μ, Summable (fun n => V n ω))
    (n : ℕ)
    (hDominates : ∀ ω,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ ≤ V n ω) :
    referenceMeasure
        (ofDominatedSummableSequence V hV hVNonnegative hSummable n hDominates) =
      MeminEquivalentFiniteVariationMeasure.referenceMeasure μ V := by
  change μ.withDensity (fun ω =>
      (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity V n ω :
        ℝ≥0∞)) =
    MeminEquivalentFiniteVariationMeasure.referenceMeasure μ V
  exact
    MeminEquivalentFiniteVariationMeasure.withDensity_repairedReferenceDensity_eq_referenceMeasure
      hSummable n

end SIntegrableFiniteVariationBridge

namespace SIntegrablePredictableMultiplierLinearL2Calculus

open SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Whole-axis path variation of a deterministically stopped local source. -/
noncomputable def meminStoppedSourceTotalVariation
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T) : Ω → ℝ :=
  fun ω =>
    (FiniteVariationPath.signedMeasure
      ((G.deterministicallyStopped T hT
        ).finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ

/-- Joint normalizing sequence for one stopped source and all successive
finite-variation output differences. -/
noncomputable def meminJointVariationSequence
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) : ℕ → Ω → ℝ := fun k ω =>
  lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω +
    ((1 : ℝ) / 2) ^ k * meminStoppedSourceTotalVariation G T hT ω

theorem meminStoppedSourceTotalVariation_measurable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T) :
    Measurable (meminStoppedSourceTotalVariation G T hT) := by
  exact measurable_totalVariation_univ_of_cumulativeVariation
    (G.deterministicallyStopped T hT).finiteVariationPart_isRightContinuous

theorem meminJointVariationSequence_measurable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) :
    Measurable (meminJointVariationSequence G T hT L k) := by
  exact (lemma411_differenceTotalVariation_measurable (L (k + 1)) (L k)).add
    ((meminStoppedSourceTotalVariation_measurable G T hT).const_mul
      (((1 : ℝ) / 2) ^ k))

theorem meminJointVariationSequence_nonnegative
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    0 ≤ meminJointVariationSequence G T hT L k ω := by
  apply add_nonneg measureReal_nonneg
  exact mul_nonneg (by positivity) measureReal_nonneg

theorem meminStoppedSourceTotalVariation_le_joint
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (ω : Ω) :
    meminStoppedSourceTotalVariation G T hT ω ≤
      meminJointVariationSequence G T hT L 0 ω := by
  simp only [meminJointVariationSequence, pow_zero, one_mul]
  exact le_add_of_nonneg_left measureReal_nonneg

theorem lemma411DifferenceTotalVariation_le_joint
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω ≤
      meminJointVariationSequence G T hT L k ω := by
  unfold meminJointVariationSequence
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) measureReal_nonneg)

theorem meminJointVariationSequence_summable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω)) :
    ∀ᵐ ω ∂μ, Summable (fun k =>
      meminJointVariationSequence G T hT L k ω) := by
  filter_upwards [hSummable] with ω hω
  apply hω.add
  exact summable_geometric_two.mul_right
    (meminStoppedSourceTotalVariation G T hT ω)

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42
