/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.GainEnvelope

/-!
# Uniform passage thresholds for Lemma 4.8

The contradiction in Lemma 4.8 first chooses a sufficiently high martingale
passage threshold and only afterwards selects a bad finite convex
combination.  The one-level selection theorem is therefore strengthened here
to a threshold theorem: its probability and `L²` indicator estimates remain
valid at every larger passage level.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- Raising the martingale passage level can only shrink the event that the
passage is finite. -/
theorem lemma48PassageFiniteEvent_antitone
    (H : SIntegrableStrategy D) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    lemma48PassageFiniteEvent H d ⊆ lemma48PassageFiniteEvent H c := by
  have hd : 0 ≤ d := hc.trans hcd
  rw [lemma48PassageFiniteEvent_eq_allTimeMaximalEvent H d hd,
    lemma48PassageFiniteEvent_eq_allTimeMaximalEvent H c hc]
  intro ω hω
  exact (ENNReal.ofReal_le_ofReal hcd).trans_lt hω

omit [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ] in
/-- The probability of a finite passage is antitone in a nonnegative passage
level. -/
theorem measureReal_lemma48PassageFiniteEvent_mono
    (H : SIntegrableStrategy D) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    μ.real (lemma48PassageFiniteEvent H d) ≤
      μ.real (lemma48PassageFiniteEvent H c) :=
  measureReal_mono (lemma48PassageFiniteEvent_antitone H hc hcd)

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- Restricting a function to the finite-passage event has antitone `L²`
seminorm as the passage level increases. -/
theorem eLpNorm_indicator_lemma48PassageFiniteEvent_mono
    (H : SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    eLpNorm ((lemma48PassageFiniteEvent H d).indicator
        fun ω => ‖q ω‖) (2 : ℝ≥0∞) μ ≤
      eLpNorm ((lemma48PassageFiniteEvent H c).indicator
        fun ω => ‖q ω‖) (2 : ℝ≥0∞) μ := by
  apply eLpNorm_mono
    (hq.norm.aestronglyMeasurable.indicator (measurableSet_lemma48PassageFiniteEvent H d))
  exact norm_indicator_le_of_subset
    (lemma48PassageFiniteEvent_antitone H hc hcd) _

omit [SigmaFiniteFiltration μ ℱ] in
/-- The Lemma 4.7 maximal estimate supplies a genuine threshold: every
larger passage level has the same uniform probability and indicator-norm
bounds. -/
theorem exists_lemma48PassageThreshold_with_probability_and_indicatorNorm
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hMaximal : ∀ η : ℝ, 0 < η →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ i,
        μ {ω | ENNReal.ofReal R <
          ⨆ t : ℝ≥0,
            ENNReal.ofReal |(H i).martingalePart t ω|} ≤
              ENNReal.ofReal η) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ c, c₀ ≤ c →
      (∀ i, μ.real (lemma48PassageFiniteEvent (H i) c) ≤ δ ^ 2) ∧
      ∀ i, eLpNorm ((lemma48PassageFiniteEvent (H i) c).indicator
        fun ω => ‖q ω‖) (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal r := by
  obtain ⟨c₀, hc₀, hProbability, hIndicator⟩ :=
    exists_lemma48PassageLevel_with_probability_and_indicatorNorm
      H q hq δ r hδ hr hMaximal
  refine ⟨c₀, hc₀, ?_⟩
  intro c hc
  constructor
  · intro i
    exact (measureReal_lemma48PassageFiniteEvent_mono
      (H i) hc₀ hc).trans (hProbability i)
  · intro i
    exact (eLpNorm_indicator_lemma48PassageFiniteEvent_mono
      (H i) q hq hc₀ hc).trans (hIndicator i)

omit [SigmaFiniteFiltration μ ℱ] in
/-- Above the common threshold, every finite convex combination has both the
active-cutoff error bound and the quantitative `L²` gain envelope needed for
the normalized Lemma 4.7 family. -/
theorem exists_lemma48PassageThreshold_with_activeError_and_gainEnvelope
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r)
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
        MemLp (lemma48TailGainEnvelope H weight n c q)
          (2 : ℝ≥0∞) μ ∧
        eLpNorm (lemma48TailGainEnvelope H weight n c q)
          (2 : ℝ≥0∞) μ ≤ 2 * ENNReal.ofReal r := by
  obtain ⟨c₀, hc₀, hThreshold⟩ :=
    exists_lemma48PassageThreshold_with_probability_and_indicatorNorm
      H q hq δ r hδ hr hMaximal
  refine ⟨c₀, hc₀, ?_⟩
  intro weight n c hc hWeight hWeightSum
  obtain ⟨hPassage, hIndicator⟩ := hThreshold c hc
  refine ⟨measureReal_lemma48ActiveMassCutoff_ne_top_le
      H weight n c δ hδ hWeight hWeightSum
        (fun i hi => hPassage i),
    lemma48TailGainEnvelope_memLp H weight n c q hq, ?_⟩
  exact eLpNorm_lemma48TailGainEnvelope_le H weight n c q hq
    hWeight hWeightSum (fun i hi => hIndicator i)

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
