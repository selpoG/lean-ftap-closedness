/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Market.Transfer.EquivalentMeasure
import FTAPTheorem42.Stochastic.Process.Envelope.RightSkeletonEnvelope
import FTAPTheorem42.Stochastic.Process.CadlagPathBoundedness
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import FTAPTheorem42.Foundations.BoundedSource

/-! # Measurable envelopes for a Cauchy family of regular paths -/

namespace FTAPTheorem42.AnalyticInterface
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A subsequence of a uniformly Cauchy family has one measurable path envelope. -/
theorem regular_common_envelope
    (Y : Nat → Process Ω) (hYA : ∀ n, StronglyAdapted F (Y n))
    (hYR : ∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t)
    (hYL : ∀ n, ProcessHasLeftLimits (Y n))
    (terminal : Nat → Ω → Real)
    (hTerminal : ∀ n, ∀ᵐ ω ∂μ, Tendsto (Y n · ω) atTop (𝓝 (terminal n ω)))
    (hC : ∀ ε : Real, 0 < ε → ∀ δ : Real, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖Y n t ω - Y m t ω‖} ≤ ENNReal.ofReal δ) :
    ∃ (f : Nat → Nat) (q : Ω → Real), StrictMono f ∧ Measurable q ∧
      (∀ ω, 0 ≤ q ω) ∧ (∀ᵐ ω ∂μ, ∀ n t, |Y (f n) t ω| ≤ q ω) := by
  have hMeas n k : Measurable (Y n (NNRealRightDenseSkeleton.skeleton k)) :=
    ((hYA n _).mono (F.le _)).measurable
  have hBound n : ∀ᵐ ω ∂μ, BddAbove (Set.range fun t => ‖Y n t ω‖) := by
    filter_upwards [hTerminal n] with ω hω
    exact bddAbove_range_norm_of_cadlag_of_tendsto (hRight := hYR n ω)
      (hLeft := hYL n ω) hω
  obtain ⟨f, hf, hMeas, hDom⟩ :=
    exists_strictMono_measurable_rightSkeletonNormEnvelope_of_allTimeGap Y
      NNRealRightDenseSkeleton.skeleton NNRealRightDenseSkeleton.skeleton_rightDense
      hYR hMeas hBound hC
  let q : Ω → Real := fun ω => max
    (rightSkeletonNormEnvelope (fun n t ω => Y (f n) t ω)
      NNRealRightDenseSkeleton.skeleton ω) 0
  refine ⟨f, q, hf, hMeas.max measurable_const, fun ω => le_max_right _ _, ?_⟩
  filter_upwards [hDom] with ω hω
  exact fun n t => (hω n t).trans (le_max_left _ _)

/-- Exponential tilting makes a finite measurable envelope square integrable. -/
theorem equivalent_envelope_measure
    (hUsual : Filtration.UsualConditions μ F)
    (q : Ω → Real) (hq : Measurable q) (hq0 : ∀ ω, 0 ≤ q ω) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ μ ∧ μ ≪ Q ∧
      MemLp q 2 Q ∧ Filtration.UsualConditions Q F := by
  let Q := CommonEnvelopeMeasure.tilted μ q
  have hQμ : Q ≪ μ := CommonEnvelopeMeasure.tilted_absolutelyContinuous
  have hμQ : μ ≪ Q := CommonEnvelopeMeasure.absolutelyContinuous_tilted hq hq0
  exact ⟨Q, CommonEnvelopeMeasure.tilted_isProbabilityMeasure hq hq0, hQμ, hμQ,
    CommonEnvelopeMeasure.memLp_two_tilted hq hq0,
    (Filtration.usualConditions_iff_of_mutuallyAbsolutelyContinuous hμQ hQμ).mp hUsual⟩

end FTAPTheorem42.AnalyticInterface
