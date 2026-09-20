/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcess

/-!
# Predictable elementary strategies on finite chronological grids

A bounded predictable coefficient can be sampled at the left endpoints of a
finite chronological grid.  This module turns those samples into an actual
finite list of predictable buy-and-hold blocks.  Its running gain is exactly
the finite-grid process already used in the concrete martingale completion.

The associated step integrand is also constructed explicitly.  On the
`k`-th block it equals the left-endpoint coefficient on the half-open interval
`(t_k,t_{k+1}]`.  Its predictability is proved from the generators of the
predictable sigma algebra, rather than postulated as a realization
capability.
-/

open MeasureTheory Set
open scoped BigOperators NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ChronologicalGrid

variable {N : ℕ} (G : ChronologicalGrid ℝ≥0 N)

/-- The predictable step coefficient carried by one deterministic grid
interval. -/
noncomputable def deterministicIntervalCoefficient
    (K : Process Ω) (s t : ℝ≥0) : Process Ω :=
  fun u ω => if u ∈ Ioc s t then K s ω else 0

/-- A coefficient known at `s`, used only on `(s,t]`, is predictable. -/
theorem deterministicIntervalCoefficient_isStronglyPredictable
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (s t : ℝ≥0) :
    IsStronglyPredictable ℱ
      (deterministicIntervalCoefficient K s t) := by
  have hKs : StronglyMeasurable[ℱ s] (K s) :=
    hK.stronglyAdapted s
  have hInterval : MeasurableSet[ℱ.predictable]
      (Ioc s t ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod s t MeasurableSet.univ
  apply Measurable.stronglyMeasurable
  intro u hu
  have hOn : MeasurableSet[ℱ.predictable]
      (Ioc s t ×ˢ ((K s) ⁻¹' u)) :=
    measurableSet_predictable_Ioc_prod s t (hKs.measurable hu)
  by_cases hzero : (0 : ℝ) ∈ u
  · rw [show (Function.uncurry
          (deterministicIntervalCoefficient K s t)) ⁻¹' u =
        (Ioc s t ×ˢ ((K s) ⁻¹' u)) ∪
          (Ioc s t ×ˢ (Set.univ : Set Ω))ᶜ by
      ext p
      change (if p.1 ∈ Ioc s t then K s p.2 else 0) ∈ u ↔
        (p.1 ∈ Ioc s t ∧ K s p.2 ∈ u) ∨
          ¬(p.1 ∈ Ioc s t ∧ p.2 ∈ (Set.univ : Set Ω))
      by_cases hp : p.1 ∈ Ioc s t <;> simp [hp, hzero]]
    exact hOn.union hInterval.compl
  · rw [show (Function.uncurry
          (deterministicIntervalCoefficient K s t)) ⁻¹' u =
        Ioc s t ×ˢ ((K s) ⁻¹' u) by
      ext p
      change (if p.1 ∈ Ioc s t then K s p.2 else 0) ∈ u ↔
        p.1 ∈ Ioc s t ∧ K s p.2 ∈ u
      by_cases hp : p.1 ∈ Ioc s t <;> simp [hp, hzero]]
    exact hOn

/-- The left-step predictable process associated with a finite chronological
grid. -/
noncomputable def predictableStepProcess (K : Process Ω) : Process Ω :=
  ∑ k ∈ Finset.range N,
    deterministicIntervalCoefficient K
      (G.sampledTime k) (G.sampledTime (k + 1))

/-- One predictable buy-and-hold block on the `k`-th deterministic grid
interval. -/
noncomputable def predictableElementaryBlock
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K) (k : ℕ) :
    PredictableElementaryInterval ℱ where
  interval :=
    { coefficient := K (G.sampledTime k)
      startTime := fun _ => G.sampledTime k
      stopTime := fun _ => G.sampledTime (k + 1)
      start_le_stop := fun _ => G.sampledTime_mono (Nat.le_succ k) }
  startStopping := isStoppingTime_const ℱ (G.sampledTime k)
  stopStopping := isStoppingTime_const ℱ (G.sampledTime (k + 1))
  coefficient_measurable := by
    rw [IsStoppingTime.measurableSpace_const]
    exact (hK.stronglyAdapted (G.sampledTime k)).measurable

/-- The actual finite predictable elementary strategy obtained from all
left-endpoint grid samples. -/
noncomputable def predictableElementaryStrategy
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K) :
    PredictableElementaryStrategy ℱ :=
  (List.range N).map fun k => G.predictableElementaryBlock K hK k

/-- The integrand represented by one deterministic grid block is its
half-open left-step coefficient. -/
theorem predictableElementaryBlock_integrand
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K) (k : ℕ) :
    (G.predictableElementaryBlock K hK k).integrand =
      deterministicIntervalCoefficient K
        (G.sampledTime k) (G.sampledTime (k + 1)) := by
  funext u ω
  simp only [PredictableElementaryInterval.integrand,
    predictableElementaryBlock, deterministicIntervalCoefficient,
    Set.mem_Ioc]
  rfl

/-- The generic integrand of the concrete elementary grid strategy is
exactly the finite-grid left-step process. -/
theorem predictableElementaryStrategy_integrand
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K) :
    (G.predictableElementaryStrategy K hK).integrand =
      G.predictableStepProcess K := by
  unfold predictableElementaryStrategy
    PredictableElementaryStrategy.integrand predictableStepProcess
  simp only [List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k _
  exact G.predictableElementaryBlock_integrand K hK k

/-- The gain of one grid block is the corresponding deterministic interval
martingale transform, pathwise and for every integrator. -/
theorem predictableElementaryBlock_gain
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K)
    (M : Process Ω) (k : ℕ) (u : ℝ≥0) (ω : Ω) :
    (G.predictableElementaryBlock K hK k).interval.gain M u ω =
      deterministicIntervalMartingaleTransform K M
        (G.sampledTime k) (G.sampledTime (k + 1)) u ω := by
  simp only [predictableElementaryBlock, ElementaryInterval.gain,
    deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply]

/-- The running gain of the concrete elementary grid strategy is exactly the
finite-grid martingale integral process used by the completion theory. -/
theorem predictableElementaryStrategy_gain
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K)
    (M : Process Ω) (u : ℝ≥0) (ω : Ω) :
    ElementaryStrategy.gain M
        (PredictableElementaryStrategy.toElementary
          (G.predictableElementaryStrategy K hK)) u ω =
      G.martingaleIntegralProcess K M u ω := by
  unfold predictableElementaryStrategy
    PredictableElementaryStrategy.toElementary
    ElementaryStrategy.gain martingaleIntegralProcess
  simp only [List.map_map, Finset.sum_apply]
  change ((List.range N).map fun k =>
      (G.predictableElementaryBlock K hK k).interval.gain M u ω).sum =
    ∑ k ∈ Finset.range N,
      deterministicIntervalMartingaleTransform K M
        (G.sampledTime k) (G.sampledTime (k + 1)) u ω
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k _
  exact G.predictableElementaryBlock_gain K hK M k u ω

end ChronologicalGrid

end FTAPTheorem42
