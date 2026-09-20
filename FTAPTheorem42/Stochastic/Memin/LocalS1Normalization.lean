/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.StoppedSourceBridge

/-!
# Finite-horizon martingale envelopes for the Mémin subsequence

This module records the measurable maximal quantity used for the martingale
half of the prelocal `S¹` estimate.  For càdlàg component paths it is the
genuine supremum of the successive martingale difference on the deterministic
horizon.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Finite-horizon maximal envelope of one successive martingale difference. -/
noncomputable def meminMartingaleDifferenceEnvelope
    (L : ℕ → SIntegrableStrategy D) (T : ℝ≥0) (k : ℕ) : Ω → ℝ :=
  FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
    (lemma411Difference (L (k + 1)) (L k)).martingalePart T

theorem meminMartingaleDifferenceEnvelope_measurable
    (L : ℕ → SIntegrableStrategy D) (T : ℝ≥0) (k : ℕ) :
    Measurable (meminMartingaleDifferenceEnvelope L T k) := by
  have hStrong :=
    FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (lemma411Difference
        (L (k + 1)) (L k)).martingalePart_isStronglyAdapted T
  exact (hStrong.mono (ℱ.le T)).measurable

theorem meminMartingaleDifferenceEnvelope_nonnegative
    (L : ℕ → SIntegrableStrategy D) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    0 ≤ meminMartingaleDifferenceEnvelope L T k ω := by
  unfold meminMartingaleDifferenceEnvelope
  unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
  exact Real.sqrt_nonneg _

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Joint local S¹ normalization for the Mémin subsequence

The strict Lemma 4.11 subsequence has summable successive finite-variation
differences on the whole time axis and summable martingale maximal envelopes
on every deterministic finite horizon.  At one positive source horizon this
module combines both quantities with the geometrically repeated stopped-source
variation.  Squared reciprocal normalization then gives one equivalent finite
measure under which

* the martingale maximal-envelope `L¹` sizes are summable;
* every maximal envelope is in `L²`;
* the stopped source and every output finite-variation difference have the
  Doléans bridges used by the predictable-integrand limit argument.

Thus the martingale and finite-variation halves of the prelocal `S¹` estimate
use the same reference measure.  The actual stochastic-integral density
identity remains a separate provider boundary.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

open SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- One sequence which simultaneously dominates the martingale maximum, the
output variation, and a geometric copy of the stopped-source variation. -/
noncomputable def meminJointLocalS1Sequence
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) : ℕ → Ω → ℝ := fun k ω =>
  meminMartingaleDifferenceEnvelope L T k ω +
    meminJointVariationSequence G T hT L k ω

theorem meminJointLocalS1Sequence_measurable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) :
    Measurable (meminJointLocalS1Sequence G T hT L k) := by
  exact (meminMartingaleDifferenceEnvelope_measurable L T k).add
    (meminJointVariationSequence_measurable G T hT L k)

theorem meminJointLocalS1Sequence_nonnegative
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    0 ≤ meminJointLocalS1Sequence G T hT L k ω := by
  exact add_nonneg (meminMartingaleDifferenceEnvelope_nonnegative L T k ω)
    (meminJointVariationSequence_nonnegative G T hT L k ω)

theorem meminJointVariationSequence_le_jointLocalS1
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D) (k : ℕ) (ω : Ω) :
    meminJointVariationSequence G T hT L k ω ≤
      meminJointLocalS1Sequence G T hT L k ω := by
  unfold meminJointLocalS1Sequence
  exact le_add_of_nonneg_left
    (meminMartingaleDifferenceEnvelope_nonnegative L T k ω)

theorem meminJointLocalS1Sequence_summable
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    ∀ᵐ ω ∂μ, Summable (fun k =>
      meminJointLocalS1Sequence G T hT L k ω) := by
  filter_upwards [hMartingaleSummable,
    meminJointVariationSequence_summable G T hT L hVariationSummable]
      with ω hM hA
  exact hM.add hA

/-- Doléans bridge for the deterministically stopped source over the joint
local-`S¹` reference measure. -/
noncomputable def meminLocalS1SourceFiniteVariationBridge
    (G : LocallySIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T)
    (L : ℕ → SIntegrableStrategy D)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)) (L k) ω))
    (hMartingaleSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope L T k ω)) :
    SIntegrableFiniteVariationBridge (G.deterministicallyStopped T hT) :=
  ofDominatedSummableSequence
    (meminJointLocalS1Sequence G T hT L)
    (meminJointLocalS1Sequence_measurable G T hT L)
    (meminJointLocalS1Sequence_nonnegative G T hT L)
    (meminJointLocalS1Sequence_summable G T hT L
      hVariationSummable hMartingaleSummable)
    0 fun ω =>
      (meminStoppedSourceTotalVariation_le_joint G T hT L ω).trans
        (meminJointVariationSequence_le_jointLocalS1 G T hT L 0 ω)

/-!
## Stopped finite-variation outputs in the Mémin control argument

The finite-variation output paired with a deterministically stopped source
must be stopped at the same horizon.  Its path variation is bounded by the
whole-axis variation of the original output difference, so the joint local
`S¹` normalization still makes all target canonical variation masses
summable.  This replaces the stronger, generally unavailable identification
of a stopped source density with an unstopped output measure.
-/

/-- Stopping a successive finite-variation difference at a deterministic
horizon cannot increase its whole-axis path variation. -/
theorem deterministicallyStopped_lemma411Difference_totalVariation_le
    (H K : SIntegrableStrategy D) (T : ℝ≥0) (hT : 0 < T) (ω : Ω) :
    (FiniteVariationPath.signedMeasure
      (((lemma411Difference H K).toLocally.deterministicallyStopped T hT
        ).finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ ≤ lemma411DifferenceTotalVariation H K ω := by
  let R := lemma411Difference H K
  have hStop := congrArg ENNReal.toReal
    (FiniteVariationStoppedPath.totalVariation_univ_stopAt
      (R.finiteVariationPart · ω)
      (R.finiteVariationPart_isBoundedVariation ω)
      (R.finiteVariationPart_isRightContinuous ω) T)
  have hNonnegative : 0 ≤
      variationOnFromTo (R.finiteVariationPart · ω) Set.univ 0 T :=
    variationOnFromTo.nonneg_of_le _ _ bot_le
  have hStoppedVariation :
      (FiniteVariationPath.signedMeasure
        (((lemma411Difference H K).toLocally.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.real
            Set.univ =
        variationOnFromTo (R.finiteVariationPart · ω) Set.univ 0 T := by
    convert hStop using 1 <;>
      simp only [R, SIntegrableStrategy.toLocally,
        LocallySIntegrableStrategy.deterministicallyStopped,
        Measure.real,
        ENNReal.toReal_ofReal hNonnegative]
    congr
  calc
    (FiniteVariationPath.signedMeasure
        (((lemma411Difference H K).toLocally.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ =
        variationOnFromTo (R.finiteVariationPart · ω) Set.univ 0 T :=
      hStoppedVariation
    _ = lemma411DifferenceVariation H K 0 T ω := by
      exact FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
        (R.finiteVariationPart_isBoundedVariation ω)
        (R.finiteVariationPart_isRightContinuous ω) bot_le
    _ ≤ lemma411DifferenceTotalVariation H K ω :=
      lemma411DifferenceVariation_le_totalVariation H K ω 0 T

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42
