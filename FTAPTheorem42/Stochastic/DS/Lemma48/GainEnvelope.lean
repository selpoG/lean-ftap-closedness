/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.TailMartingaleCutoff
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Gain envelopes for the localized tails in Lemma 4.8

If one random variable `q` dominates every original gain, the tail after an
individual martingale passage is dominated by `2q` on the event that this
passage is finite.  This module realizes that estimate for finite convex
combinations and for the fully localized actual strategy.  Absolute
continuity of the `L²` norm on small events then supplies one passage level
which simultaneously controls the active-weight error and the gain-envelope
norm.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- `2‖q‖` restricted to the event that the individual martingale passage is
finite. -/
noncomputable def lemma48SingleTailGainEnvelope
    (H : SIntegrableStrategy D) (c : ℝ) (q : Ω → ℝ) : Ω → ℝ :=
  (2 : ℝ) • (lemma48PassageFiniteEvent H c).indicator fun ω => ‖q ω‖

/-- Convex sum of the individual post-passage gain envelopes. -/
noncomputable def lemma48TailGainEnvelope
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ) : Ω → ℝ :=
  ∑ i ∈ Finset.range n,
    weight i • lemma48SingleTailGainEnvelope (H i) c q

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- A single post-passage gain is dominated by its event-restricted common
envelope. -/
theorem abs_postStoppingTailProcess_le_lemma48SingleTailGainEnvelope
    (H : SIntegrableStrategy D) (c : ℝ) (q : Ω → ℝ)
    (ω : Ω)
    (hGainBound : ∀ t, |H.stochasticIntegral t ω| ≤ ‖q ω‖) :
    ∀ t, |postStoppingTailProcess H.stochasticIntegral
      (lemma48FirstPassage H c) t ω| ≤
        lemma48SingleTailGainEnvelope H c q ω := by
  intro t
  by_cases hActive : lemma48FirstPassage H c ω < (t : WithTop ℝ≥0)
  · have hFinite : ω ∈ lemma48PassageFiniteEvent H c :=
      ne_top_of_lt hActive
    rw [postStoppingTailProcess_eq_sub_of_lt
      H.stochasticIntegral (lemma48FirstPassage H c) t ω hActive]
    simp only [lemma48SingleTailGainEnvelope, Pi.smul_apply, smul_eq_mul,
      Set.indicator_of_mem hFinite]
    calc
      |H.stochasticIntegral t ω -
          H.stochasticIntegral (lemma48FirstPassage H c ω).untopA ω| ≤
          |H.stochasticIntegral t ω| +
            |H.stochasticIntegral
              (lemma48FirstPassage H c ω).untopA ω| := abs_sub _ _
      _ ≤ ‖q ω‖ + ‖q ω‖ :=
        add_le_add (hGainBound t) (hGainBound _)
      _ = 2 * ‖q ω‖ := by ring
  · have ht : (t : WithTop ℝ≥0) ≤ lemma48FirstPassage H c ω :=
      le_of_not_gt hActive
    rw [postStoppingTailProcess_eq_zero_of_le
      H.stochasticIntegral (lemma48FirstPassage H c) t ω ht, abs_zero]
    by_cases hFinite : ω ∈ lemma48PassageFiniteEvent H c
    · simp [lemma48SingleTailGainEnvelope, hFinite]
    · simp [lemma48SingleTailGainEnvelope, hFinite]

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48SingleTailGainEnvelope_memLp
    (H : SIntegrableStrategy D) (c : ℝ) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ) :
    MemLp (lemma48SingleTailGainEnvelope H c q) (2 : ℝ≥0∞) μ := by
  have hIndicator : MemLp
      ((lemma48PassageFiniteEvent H c).indicator fun ω => ‖q ω‖)
      (2 : ℝ≥0∞) μ :=
    MemLp.indicator (measurableSet_lemma48PassageFiniteEvent H c) hq.norm
  change MemLp (fun ω => 2 *
    (lemma48PassageFiniteEvent H c).indicator (fun ω => ‖q ω‖) ω)
      (2 : ℝ≥0∞) μ
  exact hIndicator.const_mul 2

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48TailGainEnvelope_memLp
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ) :
    MemLp (lemma48TailGainEnvelope H weight n c q) (2 : ℝ≥0∞) μ := by
  unfold lemma48TailGainEnvelope
  exact memLp_finsetSum' (s := Finset.range n)
    (fun i hi => (lemma48SingleTailGainEnvelope_memLp
      (H i) c q hq).const_mul (weight i))

/-- The raw finite convex tail is dominated by the convex sum of the
individual event-restricted envelopes. -/
theorem lemma48TailConvexStrategy_gain_le_lemma48TailGainEnvelope
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hGainBound : ∀ i, ∀ᵐ ω ∂μ, ∀ t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖) :
    ∀ᵐ ω ∂μ, ∀ t,
      |(C.lemma48TailConvexStrategy H weight n c).stochasticIntegral t ω| ≤
        lemma48TailGainEnvelope H weight n c q ω := by
  have hGainBoundAll : ∀ᵐ ω ∂μ, ∀ i t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖ := by
    rw [ae_all_iff]
    exact hGainBound
  filter_upwards [C.lemma48TailConvexStrategy_stochasticIntegral
    H weight n c, hGainBoundAll] with ω hTail hBound
  intro t
  rw [hTail t]
  calc
    |∑ i ∈ Finset.range n, weight i *
        postStoppingTailProcess (H i).stochasticIntegral
          (lemma48FirstPassage (H i) c) t ω| ≤
        ∑ i ∈ Finset.range n,
          |weight i * postStoppingTailProcess (H i).stochasticIntegral
            (lemma48FirstPassage (H i) c) t ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, weight i *
        |postStoppingTailProcess (H i).stochasticIntegral
          (lemma48FirstPassage (H i) c) t ω| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hWeight i hi)]
    _ ≤ ∑ i ∈ Finset.range n, weight i *
        lemma48SingleTailGainEnvelope (H i) c q ω := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (abs_postStoppingTailProcess_le_lemma48SingleTailGainEnvelope
          (H i) c q ω (hBound i) t) (hWeight i hi)
    _ = lemma48TailGainEnvelope H weight n c q ω := by
      simp only [lemma48TailGainEnvelope, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]

/-- The same gain envelope dominates the actual strategy after all three
cutoffs. -/
theorem lemma48FullyLocalizedTailConvexStrategy_gain_le_lemma48TailGainEnvelope
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ ε : ℝ) (q : Ω → ℝ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hGainBound : ∀ i, ∀ᵐ ω ∂μ, ∀ t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖) :
    ∀ᵐ ω ∂μ, ∀ t,
      |(C.lemma48FullyLocalizedTailConvexStrategy
        H weight n c N δ ε).stochasticIntegral t ω| ≤
          lemma48TailGainEnvelope H weight n c q ω := by
  filter_upwards [C.lemma48FullyLocalizedTailConvexStrategy_stochasticIntegral
      H weight n c N δ ε,
    C.lemma48TailConvexStrategy_gain_le_lemma48TailGainEnvelope
      H weight n c q hWeight hGainBound] with ω hStop hEnvelope
  intro t
  rw [hStop t]
  simpa only [MeasureTheory.stoppedProcess] using
    hEnvelope ((min (t : WithTop ℝ≥0)
      (C.lemma48FullCutoff H weight n c N δ ε ω)).untopA)

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- If every event-restricted copy of `‖q‖` has `L²` norm at most `r`,
the convex tail envelope has norm at most `2r`. -/
theorem eLpNorm_lemma48TailGainEnvelope_le
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (q : Ω → ℝ)
    (_hq : MemLp q (2 : ℝ≥0∞) μ)
    {r : ℝ}
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hWeightSum : ∑ i ∈ Finset.range n, weight i = 1)
    (hIndicator : ∀ i ∈ Finset.range n,
      eLpNorm ((lemma48PassageFiniteEvent (H i) c).indicator
        fun ω => ‖q ω‖) (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal r) :
    eLpNorm (lemma48TailGainEnvelope H weight n c q)
      (2 : ℝ≥0∞) μ ≤ 2 * ENNReal.ofReal r := by
  calc
    eLpNorm (lemma48TailGainEnvelope H weight n c q)
        (2 : ℝ≥0∞) μ ≤
        ∑ i ∈ Finset.range n,
          eLpNorm (weight i • lemma48SingleTailGainEnvelope (H i) c q)
            (2 : ℝ≥0∞) μ := by
      unfold lemma48TailGainEnvelope
      exact eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ i ∈ Finset.range n,
        ENNReal.ofReal (weight i) * (2 * ENNReal.ofReal r) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [eLpNorm_const_smul, lemma48SingleTailGainEnvelope,
        eLpNorm_const_smul, Real.enorm_eq_ofReal (hWeight i hi)]
      rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      gcongr
      exact hIndicator i hi
    _ = 2 * ENNReal.ofReal r := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hWeight,
        hWeightSum]
      norm_num

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- One level from the Lemma 4.7 maximal estimate simultaneously makes all
individual passage probabilities at most `δ²` and all copies of `‖q‖`
restricted to those events have `L²` norm at most `r`. -/
theorem exists_lemma48PassageLevel_with_probability_and_indicatorNorm
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hMaximal : ∀ η : ℝ, 0 < η →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ i,
        μ {ω | ENNReal.ofReal R <
          ⨆ t : ℝ≥0,
            ENNReal.ofReal |(H i).martingalePart t ω|} ≤
              ENNReal.ofReal η) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ i, μ.real (lemma48PassageFiniteEvent (H i) c) ≤ δ ^ 2) ∧
      ∀ i, eLpNorm ((lemma48PassageFiniteEvent (H i) c).indicator
        fun ω => ‖q ω‖) (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal r := by
  obtain ⟨ηBound, hηBound, hNormSmall⟩ :=
    hq.norm.eLpNorm_indicator_le (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) (ENNReal.ofReal_pos.2 hr)
  obtain ⟨ηNorm, _, hηNorm, hηBoundReal⟩ :=
    ENNReal.lt_iff_exists_real_btwn.1 hηBound
  have hηNorm : 0 < ηNorm := ENNReal.ofReal_pos.1 hηNorm
  let η := min ηNorm (δ ^ 2)
  have hη : 0 < η := lt_min hηNorm (sq_pos_of_pos hδ)
  obtain ⟨c, hc, hTail⟩ := hMaximal η hη
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have hMeasure : μ (lemma48PassageFiniteEvent (H i) c) ≤
        ENNReal.ofReal η := by
      rw [lemma48PassageFiniteEvent_eq_allTimeMaximalEvent (H i) c hc]
      exact hTail i
    change (μ (lemma48PassageFiniteEvent (H i) c)).toReal ≤ δ ^ 2
    calc
      (μ (lemma48PassageFiniteEvent (H i) c)).toReal ≤
          (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hMeasure
      _ = η := ENNReal.toReal_ofReal hη.le
      _ ≤ δ ^ 2 := min_le_right _ _
  · intro i
    apply hNormSmall (lemma48PassageFiniteEvent (H i) c)
      (measurableSet_lemma48PassageFiniteEvent (H i) c)
    have hMeasure : μ (lemma48PassageFiniteEvent (H i) c) ≤
        ENNReal.ofReal η := by
      rw [lemma48PassageFiniteEvent_eq_allTimeMaximalEvent (H i) c hc]
      exact hTail i
    exact hMeasure.trans
      ((ENNReal.ofReal_le_ofReal (min_le_left ηNorm (δ ^ 2))).trans hηBoundReal.le)

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
