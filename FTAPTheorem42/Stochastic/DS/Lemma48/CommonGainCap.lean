/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.ActiveWeightProbability

/-!
# The common gain cap in Lemma 4.8

The admissibility estimate in Lemma 4.8 only needs an upper bound for each
original gain at the time when its post-passage tail starts.  A single
countable infimum of absolute-value passage times supplies that bound for the
whole sequence.  This module constructs the common cap, controls its error by
any common gain envelope, and combines it with the active-weight cutoff on an
actual realized strategy.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- A post-stopping tail has the usual active-indicator lower bound when the
upper bound for the original process is known only strictly before a second
time `σ`.  In the active case its starting time is automatically strictly
before `σ`; no bound at `σ` itself is needed. -/
theorem postStoppingTailProcess_lower_bound_before
    (X : Process Ω) (τ σ : Ω → WithTop ℝ≥0)
    {a b : ℝ} (ω : Ω)
    (hLower : ∀ t : ℝ≥0, -a ≤ X t ω)
    (hUpper : ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < σ ω → X t ω ≤ b) :
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ σ ω →
      -(a + b) * (if τ ω < (t : WithTop ℝ≥0) then 1 else 0) ≤
        postStoppingTailProcess X τ t ω := by
  intro t htσ
  by_cases hτt : τ ω < (t : WithTop ℝ≥0)
  · rw [ite_eq_left hτt, postStoppingTailProcess_eq_sub_of_lt X τ t ω hτt]
    have hτσ : τ ω < σ ω := hτt.trans_le htσ
    have hτne : τ ω ≠ ⊤ := ne_top_of_lt hτσ
    have hτcoe : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop hτne, WithTop.coe_untop _ hτne]
    have hUpperτ : X (τ ω).untopA ω ≤ b :=
      hUpper (τ ω).untopA (by rw [hτcoe]; exact hτσ)
    linarith [hLower t]
  · rw [ite_eq_right hτt]
    have htτ : (t : WithTop ℝ≥0) ≤ τ ω := le_of_not_gt hτt
    rw [postStoppingTailProcess_eq_zero_of_le X τ t ω htτ]
    simp

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The first time at which any gain in a countable sequence exceeds `N` in
absolute value. -/
noncomputable def lemma48CommonGainCap
    (H : ℕ → SIntegrableStrategy D) (N : ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => ⨅ i, absoluteStrictHittingAfter (H i).stochasticIntegral N ω

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48CommonGainCap_isStoppingTime
    (H : ℕ → SIntegrableStrategy D) (N : ℝ) :
    IsStoppingTime ℱ (lemma48CommonGainCap H N) := by
  apply IsStoppingTime.iInf
  intro i
  exact absoluteStrictHittingAfter_isStoppingTime
    (H i).stochasticIntegral_isStronglyAdapted
    (H i).stochasticIntegral_isRightContinuous N

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- Strictly before the common cap, every gain in the sequence is bounded by
the common level. -/
theorem abs_stochasticIntegral_le_of_lt_lemma48CommonGainCap
    (H : ℕ → SIntegrableStrategy D) (N : ℝ)
    (i : ℕ) (t : ℝ≥0) (ω : Ω)
    (ht : (t : WithTop ℝ≥0) < lemma48CommonGainCap H N ω) :
    |(H i).stochasticIntegral t ω| ≤ N := by
  apply abs_le_of_lt_absoluteStrictHittingAfter
  exact ht.trans_le (iInf_le (fun j =>
    absoluteStrictHittingAfter (H j).stochasticIntegral N ω) i)

omit [ℱ.IsRightContinuous] [IsProbabilityMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- If the common cap is finite, some original gain exceeds the cap level. -/
theorem lemma48CommonGainCap_ne_top_imp_exists_lt_abs
    (H : ℕ → SIntegrableStrategy D) (N : ℝ) (ω : Ω)
    (hCap : lemma48CommonGainCap H N ω ≠ ⊤) :
    ∃ i t, N < |(H i).stochasticIntegral t ω| := by
  have hExistsPassage : ∃ i,
      absoluteStrictHittingAfter (H i).stochasticIntegral N ω ≠ ⊤ := by
    by_contra hNone
    simp only [not_exists, not_not] at hNone
    apply hCap
    unfold lemma48CommonGainCap
    exact iInf_eq_top.2 hNone
  obtain ⟨i, hi⟩ := hExistsPassage
  have hExistsTime : ∃ t : ℝ≥0, ∃ (_ : 0 ≤ t),
      N < |(H i).stochasticIntegral t ω| := by
    simpa only [absoluteStrictHittingAfter,
      RightContinuousHittingTime.strictHittingAfter, ne_eq,
      MeasureTheory.hittingAfter_eq_top_iff, Set.mem_Ioi,
      not_forall, not_not] using hi
  obtain ⟨t, _, ht⟩ := hExistsTime
  exact ⟨i, t, ht⟩

/-- Before the common gain cap, the convex post-passage tail has a lower
bound involving only the original lower bound and the deterministic cap
level. -/
theorem lemma48TailConvexStrategy_stochasticIntegral_lower_bound_before_commonGainCap
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N : ℝ)
    {a : ℝ}
    (hWeight : ∀ i ∈ Finset.range n, 0 ≤ weight i)
    (hLower : ∀ i, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      -a ≤ (H i).stochasticIntegral t ω) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) ≤ lemma48CommonGainCap H N ω →
      -(a + N) * lemma48ActiveMass H weight n c t ω ≤
        (C.lemma48TailConvexStrategy H weight n c).stochasticIntegral t ω := by
  have hLowerAll : ∀ᵐ ω ∂μ, ∀ i, ∀ t : ℝ≥0,
      -a ≤ (H i).stochasticIntegral t ω := by
    rw [ae_all_iff]
    exact hLower
  filter_upwards [C.lemma48TailConvexStrategy_stochasticIntegral
    H weight n c, hLowerAll] with ω hTail hLowerω
  intro t htCap
  rw [hTail t]
  calc
    -(a + N) * lemma48ActiveMass H weight n c t ω =
        ∑ i ∈ Finset.range n, weight i *
          (-(a + N) *
            if lemma48FirstPassage (H i) c ω < (t : WithTop ℝ≥0)
            then 1 else 0) := by
      rw [lemma48ActiveMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range n, weight i *
        postStoppingTailProcess (H i).stochasticIntegral
          (lemma48FirstPassage (H i) c) t ω := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hWeight i hi)
      apply postStoppingTailProcess_lower_bound_before
        (H i).stochasticIntegral (lemma48FirstPassage (H i) c)
          (lemma48CommonGainCap H N) ω (hLowerω i)
      · intro s hs
        exact (le_abs_self _).trans
          (abs_stochasticIntegral_le_of_lt_lemma48CommonGainCap
            H N i s ω hs)
      · exact htCap

/-- Stop the tail sum at the earlier of the common gain cap and the
active-weight cutoff. -/
noncomputable def lemma48GainActiveCutoff
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ : ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => min (lemma48CommonGainCap H N ω)
    (lemma48ActiveMassCutoff H weight n c δ ω)

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48GainActiveCutoff_isStoppingTime
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c N δ : ℝ) :
    IsStoppingTime ℱ (lemma48GainActiveCutoff H weight n c N δ) :=
  (lemma48CommonGainCap_isStoppingTime H N).min
    (lemma48ActiveMassCutoff_isStoppingTime H weight n c δ)

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
