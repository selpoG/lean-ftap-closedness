/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.ActiveWeightCutoff
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Probability of the active-weight cutoff in Lemma 4.8

For nonnegative convex weights, the terminal active mass is the weighted sum
of the events that the individual martingale passages are finite.  Markov's
inequality therefore bounds the probability that the active-mass cutoff is
ever reached.  No independence is used.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Event that the martingale first passage used in Lemma 4.8 is finite. -/
def lemma48PassageFiniteEvent
    (H : SIntegrableStrategy D) (c : ℝ) : Set Ω :=
  {ω | lemma48FirstPassage H c ω ≠ ⊤}

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem measurableSet_lemma48PassageFiniteEvent
    (H : SIntegrableStrategy D) (c : ℝ) :
    MeasurableSet (lemma48PassageFiniteEvent H c) := by
  have hTop : MeasurableSet {ω | lemma48FirstPassage H c ω = ⊤} :=
    (measurableSet_singleton (⊤ : WithTop ℝ≥0)).preimage
      (lemma48FirstPassage_isStoppingTime H c).measurable'
  have hCompl : lemma48PassageFiniteEvent H c =
      {ω | lemma48FirstPassage H c ω = ⊤}ᶜ := by
    ext ω
    simp [lemma48PassageFiniteEvent]
  rw [hCompl]
  exact hTop.compl

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- Finite first passage is exactly the event that the genuine all-time
martingale maximum is strictly above the passage level. -/
theorem lemma48PassageFiniteEvent_eq_allTimeMaximalEvent
    (H : SIntegrableStrategy D) (c : ℝ) (hc : 0 ≤ c) :
    lemma48PassageFiniteEvent H c =
      {ω | ENNReal.ofReal c <
        ⨆ t : ℝ≥0, ENNReal.ofReal |H.martingalePart t ω|} := by
  ext ω
  constructor
  · intro hFinite
    have hExists : ∃ t : ℝ≥0, ∃ (_ : 0 ≤ t),
        c < |H.martingalePart t ω| := by
      simpa only [lemma48PassageFiniteEvent, lemma48FirstPassage,
        absoluteStrictHittingAfter,
        RightContinuousHittingTime.strictHittingAfter, ne_eq,
        MeasureTheory.hittingAfter_eq_top_iff, Set.mem_Ioi,
        Set.mem_ofPred_eq, not_forall, not_not] using hFinite
    obtain ⟨t, ht, htc⟩ := hExists
    change ENNReal.ofReal c <
      ⨆ s : ℝ≥0, ENNReal.ofReal |H.martingalePart s ω|
    rw [lt_iSup_iff]
    exact ⟨t,
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).2 htc⟩
  · intro hMaximum
    change ENNReal.ofReal c <
      ⨆ t : ℝ≥0, ENNReal.ofReal |H.martingalePart t ω| at hMaximum
    rw [lt_iSup_iff] at hMaximum
    obtain ⟨t, ht⟩ := hMaximum
    have htc : c < |H.martingalePart t ω| :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).1 ht
    change lemma48FirstPassage H c ω ≠ ⊤
    intro hTop
    unfold lemma48FirstPassage absoluteStrictHittingAfter
      RightContinuousHittingTime.strictHittingAfter at hTop
    have hNoHit :=
      (MeasureTheory.hittingAfter_eq_top_iff.mp hTop) t bot_le
    exact hNoHit htc

/-- Total convex weight of components whose individual martingale passage is
finite. -/
noncomputable def lemma48TerminalActiveMass
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, weight i *
    (lemma48PassageFiniteEvent (H i) c).indicator (fun _ => (1 : ℝ)) ω

omit [SigmaFiniteFiltration μ ℱ] in
theorem lemma48TerminalActiveMass_integrable
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    Integrable (lemma48TerminalActiveMass H weight n c) μ := by
  unfold lemma48TerminalActiveMass
  apply integrable_finsetSum
  intro i hi
  exact ((integrable_const (1 : ℝ)).indicator
    (measurableSet_lemma48PassageFiniteEvent (H i) c)).const_mul (weight i)

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
theorem lemma48TerminalActiveMass_nonnegative
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i) :
    ∀ ω, 0 ≤ lemma48TerminalActiveMass H weight n c ω := by
  intro ω
  rw [lemma48TerminalActiveMass]
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hWeight i hi)
  by_cases hω : ω ∈ lemma48PassageFiniteEvent (H i) c
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- At every finite time the active mass is bounded by its terminal mass. -/
theorem lemma48ActiveMass_le_terminalActiveMass
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i) :
    ∀ t ω, lemma48ActiveMass H weight n c t ω ≤
      lemma48TerminalActiveMass H weight n c ω := by
  intro t ω
  rw [lemma48ActiveMass, lemma48TerminalActiveMass]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hWeight i hi)
  by_cases hτt : lemma48FirstPassage (H i) c ω <
      (t : WithTop ℝ≥0)
  · have hFinite : ω ∈ lemma48PassageFiniteEvent (H i) c := by
      exact ne_top_of_lt hτt
    rw [ite_eq_left hτt, Set.indicator_of_mem hFinite]
  · rw [ite_eq_right hτt]
    by_cases hFinite : ω ∈ lemma48PassageFiniteEvent (H i) c
    · simp [Set.indicator_of_mem hFinite]
    · simp [Set.indicator_of_notMem hFinite]

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- If the active-mass cutoff is finite, the terminal active mass is strictly
larger than the cutoff level. -/
theorem lemma48ActiveMassCutoff_ne_top_imp_lt_terminalActiveMass
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c δ : ℝ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i) :
    ∀ ω, lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤ →
      δ < lemma48TerminalActiveMass H weight n c ω := by
  intro ω hCutoff
  have hExists : ∃ t : ℝ≥0, ∃ (_ : 0 ≤ t),
      δ < lemma48ActiveMass H weight n c t ω := by
    simpa only [lemma48ActiveMassCutoff,
      LeftContinuousHittingTime.strictHittingAfter, ne_eq,
      MeasureTheory.hittingAfter_eq_top_iff, Set.mem_Ioi,
      not_forall, not_not] using hCutoff
  obtain ⟨t, ht, hδt⟩ := hExists
  exact hδt.trans_le
    (lemma48ActiveMass_le_terminalActiveMass H weight n c hWeight t ω)

omit [SigmaFiniteFiltration μ ℱ] in
/-- The expectation of the terminal active mass is the convexly weighted sum
of the individual passage probabilities. -/
theorem integral_lemma48TerminalActiveMass
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    (∫ ω, lemma48TerminalActiveMass H weight n c ω ∂μ) =
      ∑ i ∈ Finset.range n, weight i *
        μ.real (lemma48PassageFiniteEvent (H i) c) := by
  change (∫ ω, ∑ i ∈ Finset.range n, weight i *
      (lemma48PassageFiniteEvent (H i) c).indicator
        (fun _ => (1 : ℝ)) ω ∂μ) = _
  calc
    (∫ ω, ∑ i ∈ Finset.range n, weight i *
        (lemma48PassageFiniteEvent (H i) c).indicator
          (fun _ => (1 : ℝ)) ω ∂μ) =
        ∑ i ∈ Finset.range n, ∫ ω, weight i *
          (lemma48PassageFiniteEvent (H i) c).indicator
            (fun _ => (1 : ℝ)) ω ∂μ := by
      apply integral_finsetSum
      intro i hi
      exact ((integrable_const (1 : ℝ)).indicator
        (measurableSet_lemma48PassageFiniteEvent (H i) c)).const_mul
          (weight i)
    _ = ∑ i ∈ Finset.range n, weight i *
        μ.real (lemma48PassageFiniteEvent (H i) c) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      apply congrArg (weight i * ·)
      change (∫ a : Ω, (lemma48PassageFiniteEvent (H i) c).indicator
        (1 : Ω → ℝ) a ∂μ) = _
      exact integral_indicator_one (μ := μ)
        (measurableSet_lemma48PassageFiniteEvent (H i) c)

omit [SigmaFiniteFiltration μ ℱ] in
/-- If every individual martingale passage has probability at most `δ²`,
then a convex active mass crosses the level `δ` with probability at most
`δ`.  This is the localization-error estimate in Lemma 4.8. -/
theorem measureReal_lemma48ActiveMassCutoff_ne_top_le
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c δ : ℝ)
    (hδ : 0 < δ)
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hWeightSum : ∑ i ∈ Finset.range n, weight i = 1)
    (hPassage : ∀ i ∈ Finset.range n,
      μ.real (lemma48PassageFiniteEvent (H i) c) ≤ δ ^ 2) :
    μ.real {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ≤ δ := by
  let F := lemma48TerminalActiveMass H weight n c
  have hFNonnegative : 0 ≤ᵐ[μ] F :=
    Filter.Eventually.of_forall
      (lemma48TerminalActiveMass_nonnegative H weight n c hWeight)
  have hFIntegrable : Integrable F μ :=
    lemma48TerminalActiveMass_integrable H weight n c
  have hCutoffSubset :
      {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ⊆
        {ω | δ ≤ F ω} := by
    intro ω hω
    exact (lemma48ActiveMassCutoff_ne_top_imp_lt_terminalActiveMass
      H weight n c δ hWeight ω hω).le
  have hMarkov : δ * μ.real {ω | δ ≤ F ω} ≤ ∫ ω, F ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg hFNonnegative hFIntegrable δ
  have hIntegral : (∫ ω, F ω ∂μ) ≤ δ ^ 2 := by
    rw [show (∫ ω, F ω ∂μ) =
        ∑ i ∈ Finset.range n, weight i *
          μ.real (lemma48PassageFiniteEvent (H i) c) by
      exact integral_lemma48TerminalActiveMass H weight n c]
    calc
      (∑ i ∈ Finset.range n, weight i *
          μ.real (lemma48PassageFiniteEvent (H i) c)) ≤
          ∑ i ∈ Finset.range n, weight i * δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hPassage i hi) (hWeight i hi)
      _ = δ ^ 2 := by rw [← Finset.sum_mul, hWeightSum, one_mul]
  have hScaled : δ *
      μ.real {ω | lemma48ActiveMassCutoff H weight n c δ ω ≠ ⊤} ≤
        δ ^ 2 := by
    exact (mul_le_mul_of_nonneg_left
      (measureReal_mono hCutoffSubset) hδ.le).trans
        (hMarkov.trans hIntegral)
  nlinarith

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
