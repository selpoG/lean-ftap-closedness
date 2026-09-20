/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.PassageThreshold
import FTAPTheorem42.Foundations.MaximalProbability

/-!
# Normalized localized tails for Lemma 4.8

The fully localized convex tail has deterministic lower bound
`-(a + N) * δ`.  When this number is strictly negative, rescaling by its
positive reciprocal produces a one-admissible actual strategy.  This module
also transports the left-limit, initial-value, `L²` gain-envelope, and large
martingale-event properties needed for the second application of Lemma 4.7.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Left limits of finite weighted sums -/

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Finite weighted aggregation preserves left limits of the martingale
parts. -/
theorem weightedPrefixSum_martingalePart_hasLeftLimits
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (hH : ∀ i, ProcessHasLeftLimits (H i).martingalePart) :
    ∀ n, ProcessHasLeftLimits (weightedPrefixSum H weight n).martingalePart := by
  intro n
  induction n with
  | zero =>
      change ProcessHasLeftLimits fun t ω => 0 * (H 0).martingalePart t ω
      exact (hH 0).const_mul 0
  | succ n ih =>
      change ProcessHasLeftLimits fun t ω =>
        (weightedPrefixSum H weight n).martingalePart t ω +
          weight n * (H n).martingalePart t ω
      exact ih.add ((hH n).const_mul (weight n))

end SIntegrableStrategy

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- A post-passage tail retains left limits of the original martingale
part. -/
theorem lemma48Tail_martingalePart_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D) (c : ℝ)
    (hM : ProcessHasLeftLimits H.martingalePart) :
    ProcessHasLeftLimits (C.lemma48Tail H c).martingalePart := by
  change ProcessHasLeftLimits fun t ω =>
    H.martingalePart t ω -
      (C.stopAtTop (lemma48FirstPassage H c)
        (lemma48FirstPassage_isStoppingTime H c) H).martingalePart t ω
  exact hM.sub (C.martingalePart_stopAtTop_hasLeftLimits
    (lemma48FirstPassage H c)
    (lemma48FirstPassage_isStoppingTime H c) H hM)

/-- The finite convex tail has left limits whenever all original martingale
parts do. -/
theorem lemma48TailConvexStrategy_martingalePart_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ)
    (hM : ∀ i, ProcessHasLeftLimits (H i).martingalePart) :
    ProcessHasLeftLimits
      (C.lemma48TailConvexStrategy H weight n c).martingalePart :=
  SIntegrableStrategy.weightedPrefixSum_martingalePart_hasLeftLimits
    (fun i => C.lemma48Tail (H i) c) weight
    (fun i => C.lemma48Tail_martingalePart_hasLeftLimits (H i) c (hM i)) n

/-! ## Normalized actual strategy and envelope -/

/-- The fully localized convex tail divided by its deterministic
admissibility scale. -/
noncomputable def lemma48NormalizedTailConvexStrategy
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ) : SIntegrableStrategy D :=
  (C.lemma48FullyLocalizedTailConvexStrategy
    H weight n c N δ ε).smul (((a + N) * δ)⁻¹)

/-- The correspondingly normalized event-restricted gain envelope. -/
noncomputable def lemma48NormalizedTailGainEnvelope
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ) (N δ a : ℝ) : Ω → ℝ :=
  ((a + N) * δ)⁻¹ • lemma48TailGainEnvelope H weight n c q

/-- The normalized localized martingale part has pathwise left limits. -/
theorem lemma48NormalizedTailConvexStrategy_martingalePart_hasLeftLimits
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ)
    (hM : ∀ i, ProcessHasLeftLimits (H i).martingalePart) :
    ProcessHasLeftLimits
      (C.lemma48NormalizedTailConvexStrategy
        H weight n c N δ ε a).martingalePart := by
  change ProcessHasLeftLimits fun t ω => ((a + N) * δ)⁻¹ *
    (C.lemma48FullyLocalizedTailConvexStrategy
      H weight n c N δ ε).martingalePart t ω
  exact (C.martingalePart_stopAtTop_hasLeftLimits
    (C.lemma48FullCutoff H weight n c N δ ε)
    (C.lemma48FullCutoff_isStoppingTime H weight n c N δ ε)
    (C.lemma48TailConvexStrategy H weight n c)
    (C.lemma48TailConvexStrategy_martingalePart_hasLeftLimits
      H weight n c hM)).const_mul _

/-- A finite convex combination of post-passage martingale tails starts
from zero, independently of the initial values of the original martingales. -/
theorem lemma48TailConvexStrategy_martingalePart_zero
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    (C.lemma48TailConvexStrategy H weight n c).martingalePart 0 =ᵐ[μ] 0 := by
  filter_upwards [C.lemma48TailConvexStrategy_martingalePart
    H weight n c] with ω hTail
  rw [hTail 0]
  apply Finset.sum_eq_zero
  intro i hi
  rw [postStoppingTailProcess_eq_zero_of_le]
  · ring
  · exact bot_le

/-- The fully localized tail martingale starts from zero. -/
theorem lemma48FullyLocalizedTailConvexStrategy_martingalePart_zero
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) :
    (C.lemma48FullyLocalizedTailConvexStrategy
      H weight n c N δ ε).martingalePart 0 =ᵐ[μ] 0 := by
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_martingalePart
      H weight n c N δ ε,
    C.lemma48TailConvexStrategy_martingalePart_zero
      H weight n c] with ω hStop hTailZero
  rw [hStop 0, MeasureTheory.stoppedProcess_eq_of_le bot_le, hTailZero]

/-- Normalization preserves the zero initial value of the martingale part. -/
theorem lemma48NormalizedTailConvexStrategy_martingalePart_zero
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ) :
    (C.lemma48NormalizedTailConvexStrategy
      H weight n c N δ ε a).martingalePart 0 =ᵐ[μ] 0 := by
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_martingalePart_zero
    H weight n c N δ ε] with ω hω
  change ((a + N) * δ)⁻¹ *
    (C.lemma48FullyLocalizedTailConvexStrategy
      H weight n c N δ ε).martingalePart 0 ω = 0
  simpa only [Pi.zero_apply, mul_zero] using
    congrArg (fun x => ((a + N) * δ)⁻¹ * x) hω

/-- Division by the positive deterministic lower-bound scale makes the
localized tail one-admissible. -/
theorem lemma48NormalizedTailConvexStrategy_admissible
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ)
    (hδ : 0 < δ) (haN : 0 < a + N)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hLower : ∀ i, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      -a ≤ (H i).stochasticIntegral t ω) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (-1 : ℝ) ≤
      (C.lemma48NormalizedTailConvexStrategy
        H weight n c N δ ε a).stochasticIntegral t ω := by
  have hScale : 0 < (a + N) * δ := mul_pos haN hδ
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_stochasticIntegral_lower_bound
    H weight n c N δ ε hδ.le haN.le hWeight hLower] with ω hω
  intro t
  change (-1 : ℝ) ≤ ((a + N) * δ)⁻¹ *
    (C.lemma48FullyLocalizedTailConvexStrategy
      H weight n c N δ ε).stochasticIntegral t ω
  calc
    (-1 : ℝ) = ((a + N) * δ)⁻¹ * (-((a + N) * δ)) := by
      rw [mul_neg, inv_mul_cancel₀ hScale.ne']
    _ ≤ ((a + N) * δ)⁻¹ *
        (C.lemma48FullyLocalizedTailConvexStrategy
          H weight n c N δ ε).stochasticIntegral t ω :=
      mul_le_mul_of_nonneg_left (by
        simpa only [neg_mul] using hω t) (inv_nonneg.mpr hScale.le)

/-- The normalized gain is dominated by the normalized event-restricted
envelope. -/
theorem lemma48NormalizedTailConvexStrategy_gain_le_envelope
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ) (q : Ω → ℝ)
    (hScale : 0 < (a + N) * δ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hGainBound : ∀ i, ∀ᵐ ω ∂μ, ∀ t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖) :
    ∀ᵐ ω ∂μ, ∀ t,
      |(C.lemma48NormalizedTailConvexStrategy
        H weight n c N δ ε a).stochasticIntegral t ω| ≤
          lemma48NormalizedTailGainEnvelope H weight n c q N δ a ω := by
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_gain_le_lemma48TailGainEnvelope
    H weight n c N δ ε q hWeight hGainBound] with ω hω
  intro t
  change |((a + N) * δ)⁻¹ *
      (C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).stochasticIntegral t ω| ≤
    ((a + N) * δ)⁻¹ * lemma48TailGainEnvelope H weight n c q ω
  rw [abs_mul, abs_of_pos (inv_pos.mpr hScale)]
  exact mul_le_mul_of_nonneg_left (hω t) (inv_nonneg.mpr hScale.le)

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The normalized event-restricted envelope belongs to `L²`. -/
theorem lemma48NormalizedTailGainEnvelope_memLp
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ) (N δ a : ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ) :
    MemLp (lemma48NormalizedTailGainEnvelope
      H weight n c q N δ a) (2 : ℝ≥0∞) μ :=
  (lemma48TailGainEnvelope_memLp H weight n c q hq).const_mul _

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- If the raw envelope norm is at most the positive normalization scale,
the normalized envelope has `L²` seminorm at most one. -/
theorem eLpNorm_lemma48NormalizedTailGainEnvelope_le_one
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ) (N δ a : ℝ)
    (hScale : 0 < (a + N) * δ)
    (hNorm : eLpNorm (lemma48TailGainEnvelope H weight n c q)
      (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal ((a + N) * δ)) :
    eLpNorm (lemma48NormalizedTailGainEnvelope
      H weight n c q N δ a) (2 : ℝ≥0∞) μ ≤ 1 := by
  rw [lemma48NormalizedTailGainEnvelope, eLpNorm_const_smul,
    Real.enorm_eq_ofReal (inv_nonneg.mpr hScale.le)]
  calc
    ENNReal.ofReal (((a + N) * δ)⁻¹) *
        eLpNorm (lemma48TailGainEnvelope H weight n c q)
          (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal (((a + N) * δ)⁻¹) *
          ENNReal.ofReal ((a + N) * δ) :=
      by simpa only [mul_comm] using
        mul_le_mul_right hNorm (ENNReal.ofReal (((a + N) * δ)⁻¹))
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hScale.le),
        inv_mul_cancel₀ hScale.ne']
      norm_num

omit [SigmaFiniteFiltration μ ℱ] in
/-- The common passage threshold may be chosen so that every later finite
convex combination has active-cutoff error at most `δ` and normalized gain
envelope `L²` seminorm at most one. -/
theorem exists_lemma48PassageThreshold_with_normalizedGainEnvelope
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (δ N a : ℝ) (hδ : 0 < δ) (haN : 0 < a + N)
    (hMaximal : ∀ η : ℝ, 0 < η →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ i,
        μ {ω | ENNReal.ofReal R <
          ⨆ t : ℝ≥0,
            ENNReal.ofReal |(H i).martingalePart t ω|} ≤
              ENNReal.ofReal η) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧
      ∀ (weight : ℕ → ℝ) (n : ℕ) (c : ℝ), c₀ ≤ c →
        (∀ i ∈ Finset.range n, 0 ≤ weight i) →
        (∑ i ∈ Finset.range n, weight i = 1) →
        μ.real {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ≤ δ ∧
        MemLp (lemma48NormalizedTailGainEnvelope
          H weight n c q N δ a) (2 : ℝ≥0∞) μ ∧
        eLpNorm (lemma48NormalizedTailGainEnvelope
          H weight n c q N δ a) (2 : ℝ≥0∞) μ ≤ 1 := by
  have hScale : 0 < (a + N) * δ := mul_pos haN hδ
  have hHalfScale : 0 < ((a + N) * δ) / 2 := half_pos hScale
  obtain ⟨c₀, hc₀, hThreshold⟩ :=
    exists_lemma48PassageThreshold_with_activeError_and_gainEnvelope
      H q hq δ (((a + N) * δ) / 2) hδ hHalfScale hMaximal
  refine ⟨c₀, hc₀, ?_⟩
  intro weight n c hc hWeight hWeightSum
  obtain ⟨hActive, hMemLp, hNorm⟩ :=
    hThreshold weight n c hc hWeight hWeightSum
  refine ⟨hActive,
    lemma48NormalizedTailGainEnvelope_memLp
      H weight n c q N δ a hq, ?_⟩
  apply eLpNorm_lemma48NormalizedTailGainEnvelope_le_one
    H weight n c q N δ a hScale
  exact hNorm.trans_eq (by
    calc
      2 * ENNReal.ofReal (((a + N) * δ) / 2) =
          ENNReal.ofReal 2 * ENNReal.ofReal (((a + N) * δ) / 2) := by
            norm_num
      _ = ENNReal.ofReal (2 * (((a + N) * δ) / 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal ((a + N) * δ) := by ring_nf)

/-- A high martingale event of the fully localized tail remains high after
normalization, at the correspondingly rescaled threshold. -/
theorem lemma48FullyLocalizedMartingaleHighEvent_subset_normalized
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a : ℝ)
    (hScale : 0 < (a + N) * δ) (hε : 0 < ε) :
    C.lemma48FullyLocalizedMartingaleHighEvent H weight n c N δ ε ⊆
      {ω | ENNReal.ofReal (((a + N) * δ)⁻¹ * (ε / 2)) <
        ⨆ t : ℝ≥0, ENNReal.ofReal
          |(C.lemma48NormalizedTailConvexStrategy
            H weight n c N δ ε a).martingalePart t ω|} := by
  intro ω hω
  change ENNReal.ofReal (ε / 2) <
    ⨆ t : ℝ≥0, ENNReal.ofReal
      |(C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).martingalePart t ω| at hω
  change ENNReal.ofReal (((a + N) * δ)⁻¹ * (ε / 2)) <
    ⨆ t : ℝ≥0, ENNReal.ofReal
      |(C.lemma48NormalizedTailConvexStrategy
        H weight n c N δ ε a).martingalePart t ω|
  rw [lt_iSup_iff] at hω ⊢
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (inv_nonneg.mpr hScale.le) (by positivity))).2
  change ((a + N) * δ)⁻¹ * (ε / 2) <
    |((a + N) * δ)⁻¹ *
      (C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).martingalePart t ω|
  rw [abs_mul, abs_of_pos (inv_pos.mpr hScale)]
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hScale)
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 ht

/-- The quantitative high-event estimate, after normalization.  The only
lost mass is still the common-gain-cap and active-cutoff error. -/
theorem measureReal_lemma48NormalizedMartingaleHighEvent_gt
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε a rawMass gainError activeError : ℝ)
    (hScale : 0 < (a + N) * δ) (hε : 0 < ε)
    (hRaw : rawMass <
      μ.real (C.lemma48TailMartingalePassageFiniteEvent H weight n c ε))
    (hGain : μ.real {ω | lemma48CommonGainCap H N ω ≠ ⊤} ≤ gainError)
    (hActive : μ.real {ω |
      lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ≤ activeError) :
    rawMass - gainError - activeError <
      μ.real {ω | ENNReal.ofReal (((a + N) * δ)⁻¹ * (ε / 2)) <
        ⨆ t : ℝ≥0, ENNReal.ofReal
          |(C.lemma48NormalizedTailConvexStrategy
            H weight n c N δ ε a).martingalePart t ω|} := by
  exact (C.measureReal_lemma48FullyLocalizedMartingaleHighEvent_gt
    H weight n c N δ ε rawMass gainError activeError
      hε hRaw hGain hActive).trans_le
    (measureReal_mono
      (C.lemma48FullyLocalizedMartingaleHighEvent_subset_normalized
        H weight n c N δ ε a hScale hε))

omit [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ] in
/-- An a.e. common `L²` gain envelope supplies a deterministic common cap
whose finite-passage event has arbitrarily small probability. -/
theorem exists_lemma48CommonGainCap_measureReal_le
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (η : ℝ) (hη : 0 < η)
    (hGainBound : ∀ i, ∀ᵐ ω ∂μ, ∀ t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖) :
    ∃ N : ℝ, 0 ≤ N ∧
      μ.real {ω | lemma48CommonGainCap H N ω ≠ ⊤} ≤ η := by
  have hQBounded : BoundedInProbability μ
      (fun _ : ℕ => fun ω => ‖q ω‖) :=
    BoundedInProbability.const_of_aestronglyMeasurable hq.norm.aestronglyMeasurable
  obtain ⟨N, hN, hTail⟩ := hQBounded η hη
  have hTailENN : μ {ω | N < ‖q ω‖} ≤ ENNReal.ofReal η := by
    simpa only [abs_norm] using hTail 0
  have hTailReal : μ.real {ω | N < ‖q ω‖} ≤ η := by
    change (μ {ω | N < ‖q ω‖}).toReal ≤ η
    calc
      (μ {ω | N < ‖q ω‖}).toReal ≤ (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hTailENN
      _ = η := ENNReal.toReal_ofReal hη.le
  have hGainBoundAll : ∀ᵐ ω ∂μ, ∀ i t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖ := by
    rw [ae_all_iff]
    exact hGainBound
  have hSubset : {ω | lemma48CommonGainCap H N ω ≠ ⊤} ≤ᵐ[μ]
      {ω | N < ‖q ω‖} := by
    filter_upwards [hGainBoundAll] with ω hω
    intro hCap
    obtain ⟨i, t, hit⟩ :=
      lemma48CommonGainCap_ne_top_imp_exists_lt_abs H N ω hCap
    exact hit.trans_le (hω i t)
  refine ⟨N, hN, ?_⟩
  exact (ENNReal.toReal_mono (by finiteness)
    (measure_mono_ae hSubset)).trans hTailReal

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
