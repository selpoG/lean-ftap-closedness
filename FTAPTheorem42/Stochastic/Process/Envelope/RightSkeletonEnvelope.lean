/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Skeleton
import FTAPTheorem42.Stochastic.Compactness.MaximalCauchyEnvelope

/-! # A common skeleton envelope from all-time Cauchy estimates -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Extraction followed by a measurable skeleton envelope -/

/--
All-time Cauchy in probability yields a measurable common envelope on any
right-dense countable skeleton.  The selected subsequence is dominated at all
times, not only on the skeleton.
-/
theorem exists_strictMono_measurable_rightSkeletonNormEnvelope_of_allTimeGap
    {Time Ω : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time] [MeasurableSpace Ω] {μ : Measure Ω}
    (u : ℕ → Time → Ω → ℝ) (skeleton : ℕ → Time)
    (hRightDense : ∀ t, t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hRightCont : ∀ n ω t,
      ContinuousWithinAt (u n · ω) (Set.Ici t) t)
    (hMeas : ∀ n k, Measurable (u n (skeleton k)))
    (hanchor : ∀ n, ∀ᵐ ω ∂μ,
      BddAbove (Set.range fun t => ‖u n t ω‖))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖u n t ω - u m t ω‖} ≤
          ENNReal.ofReal δ) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      Measurable
        (rightSkeletonNormEnvelope
          (fun k t ω => u (cutoff k) t ω) skeleton) ∧
      ∀ᵐ ω ∂μ, ∀ k t,
        ‖u (cutoff k) t ω‖ ≤
          rightSkeletonNormEnvelope
            (fun j s ω => u (cutoff j) s ω) skeleton ω := by
  obtain ⟨cutoff, hcutoff, hglobal⟩ :=
    exists_strictMono_ae_uniform_bddAbove_of_allTimeGap_cauchyInMeasure
      u hanchor hcauchy
  have henvMeas :
      Measurable
        (rightSkeletonNormEnvelope
          (fun k t ω => u (cutoff k) t ω) skeleton) :=
    measurable_rightSkeletonNormEnvelope
      (u := fun k t ω => u (cutoff k) t ω) skeleton
      (fun k j => hMeas (cutoff k) j)
  refine ⟨cutoff, hcutoff, henvMeas, ?_⟩
  filter_upwards [hglobal] with ω hω
  have hsubset : Set.range (fun p : ℕ × ℕ =>
      ‖u (cutoff p.1) (skeleton p.2) ω‖) ⊆
      Set.range (fun p : ℕ × Time =>
        ‖u (cutoff p.1) p.2 ω‖) := by
    rintro _ ⟨⟨k, j⟩, rfl⟩
    exact ⟨⟨k, skeleton j⟩, rfl⟩
  have hωskeleton : BddAbove (Set.range (fun p : ℕ × ℕ =>
      ‖u (cutoff p.1) (skeleton p.2) ω‖)) :=
    BddAbove.mono hsubset hω
  exact norm_le_rightSkeletonNormEnvelope_of_bddAbove
    (u := fun k t ω => u (cutoff k) t ω) skeleton hRightDense
    (fun k ω t => hRightCont (cutoff k) ω t) hωskeleton

end FTAPTheorem42
