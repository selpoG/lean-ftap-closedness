/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization
import FTAPTheorem42.Stochastic.Construction.FiniteConvexGain
import FTAPTheorem42.Foundations.ConvexProcesses

/-! # Finite convex gains retain the same component weights -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open LocalCompletedM2A PredictableElementaryEmery
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- The gain and both components use exactly the supplied finite weights. -/
theorem originalGain_convexCombination
    (source : BoundedSemimartingaleSource S F μ) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    (Y : Nat → OriginalSpecialGain source Q) {n : Nat} (w : TailConvexWeights n) :
    ∃ V : OriginalSpecialGain source Q,
      V.original.gain = w.applyVector (fun i => (Y i).original.gain) ∧
      V.decomposition.N = w.applyVector (fun i => (Y i).decomposition.N) ∧
      V.decomposition.A = w.applyVector (fun i => (Y i).decomposition.A) := by
  choose R hR using fun i => (Y i).original.exists_realized source hQμ hμQ
  let E : ∀ i, J1Decomposition (R i).gain F Q := fun i => {
    (Y i).decomposition with
    decomposition := by rw [hR i]; exact (Y i).decomposition.decomposition }
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  obtain ⟨V, hV, D, hN, hA, hDP⟩ := exists_realized_finiteSum_with_components
    hS R E (fun i => (Y i).predictable) w.support w.weight w.nonneg
  refine ⟨⟨OriginalGain.ofRealized source V hQμ hμQ, D, hDP⟩, ?_, ?_, ?_⟩
  · change V.gain = _
    funext t ω
    rw [hV, TailConvexWeights.applyVector_process_apply]
    simp only [hR, TailConvexWeights.apply]
  · change D.N = _
    funext t ω
    rw [hN, TailConvexWeights.applyVector_process_apply]
    rfl
  · change D.A = _
    funext t ω
    rw [hA, TailConvexWeights.applyVector_process_apply]
    rfl

end FTAPTheorem42.BoundedSourceIntegralMarket
