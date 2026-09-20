/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.EventSwitching
import FTAPTheorem42.Stochastic.Topology.J1.Triangle

/-!
# Terminal switching in the realized elementary Emery carrier

This file supplies the full switch-after operation for the realized elementary
Emery terminal market.  It uses the event-tail restriction from the preceding
module and adds candidate-specific terminal semantics.  Admissibility and the
pasting consumer remain separate boundaries.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## Negation and full switching in the realized carrier -/

private theorem elementaryGain_neg_event
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ) :
    elementaryGain S H.neg = fun t ω => -elementaryGain S H t ω := by
  funext t ω
  simp only [elementaryGain, PredictableElementaryStrategy.toElementary_neg,
    ElementaryStrategy.gain_neg]

private theorem testedGain_neg_event
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) :
    testedGain S J H.neg = fun t ω => -testedGain S J H t ω := by
  unfold testedGain
  rw [strategy_mul_neg_eq_neg_mul]
  exact elementaryGain_neg_event S (J.strategy.mul H)

private theorem testedDifference_neg_neg_event
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    testedDifference S J H.neg K.neg =
      fun t ω => -testedDifference S J H K t ω := by
  unfold testedDifference
  rw [testedGain_neg_event, testedGain_neg_event]
  funext t ω
  ring

private theorem gauge_neg_neg_event
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (_hS : IsStronglyProgressive ℱ S)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    gauge μ S H.neg K.neg T = gauge μ S H K T := by
  have hTest : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ,
      testValue μ S J H.neg K.neg T = testValue μ S J H K T := by
    intro J
    unfold testValue
    rw [testedDifference_neg_neg_event]
    apply congrArg (fun X => SemimartingaleQuasiNorm.truncatedExpectation μ X)
    funext ω
    exact cappedFiniteHorizonAbsoluteEnvelope_neg
      (testedDifference S J H K) T ω
  unfold gauge
  apply congrArg sSup
  ext b
  constructor
  · intro hb
    rcases Set.mem_insert_iff.mp hb with hb | ⟨J, hJ⟩
    · exact Set.mem_insert_iff.mpr (Or.inl hb)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨J, (hTest J).symm.trans hJ⟩)
  · intro hb
    rcases Set.mem_insert_iff.mp hb with hb | ⟨J, hJ⟩
    · exact Set.mem_insert_iff.mpr (Or.inl hb)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨J, (hTest J).trans hJ⟩)

noncomputable def RealizedStrategy.neg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : RealizedStrategy (ℱ := ℱ) μ S) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n => (H.representative n).neg
  representativeBound := H.representativeBound
  representative_coefficientAbsSum_le := by
    intro n ω
    rw [PredictableElementaryStrategy.coefficientAbsSum_neg]
    exact H.representative_coefficientAbsSum_le n ω
  gain := fun t ω => -H.gain t ω
  gain_stronglyAdapted := by
    intro t
    exact (H.gain_stronglyAdapted t).neg
  gain_rightContinuous := by
    intro ω t
    exact (H.gain_rightContinuous ω t).neg
  gain_hasLeftLimits := H.gain_hasLeftLimits.neg
  gain_convergence := by
    intro r
    have hEnvelope :
        (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n).neg t ω -
            (-H.gain t ω)) ((r + 1 : ℕ) : ℝ≥0)) =
        (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n) t ω -
            H.gain t ω) ((r + 1 : ℕ) : ℝ≥0)) := by
      funext n ω
      have hDiffN :
          (fun t ω => elementaryGain S (H.representative n).neg t ω -
            (-H.gain t ω)) =
            (fun t ω => -(elementaryGain S (H.representative n) t ω -
              H.gain t ω)) := by
        funext t ω
        rw [elementaryGain_neg_event]
        ring
      rw [hDiffN]
      exact cappedFiniteHorizonAbsoluteEnvelope_neg
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        ((r + 1 : ℕ) : ℝ≥0) ω
    rw [hEnvelope]
    exact H.gain_convergence r
  isCauchy := by
    intro T
    have hEq : ∀ p : ℕ × ℕ,
        gauge μ S (H.representative p.1).neg
            (H.representative p.2).neg T =
          gauge μ S (H.representative p.1)
            (H.representative p.2) T := by
      intro p
      exact gauge_neg_neg_event S hS (H.representative p.1)
        (H.representative p.2) T
    convert H.isCauchy T using 1
    funext p
    exact hEq p

noncomputable def RealizedStrategy.switchAfter
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    RealizedStrategy (ℱ := ℱ) μ S :=
  H.add S hS ((K.add S hS (H.neg S hS)).eventTailAfter S hS hSRight
    τ hτ s hs T hτT)

@[simp]
theorem RealizedStrategy.switchAfter_gain
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (H.switchAfter S hS hSRight K τ hτ s hs T hτT).gain =
      fun t ω => if ω ∈ s then
        H.gain (min t (τ ω)) ω + K.gain t ω -
          K.gain (min t (τ ω)) ω
      else H.gain t ω := by
  funext t ω
  change H.gain t ω +
      ((K.add S hS (H.neg S hS)).eventTailAfter S hS hSRight
        τ hτ s hs T hτT).gain t ω = _
  rw [RealizedStrategy.eventTailAfter_gain_apply]
  dsimp only [RealizedStrategy.add, RealizedStrategy.neg]
  by_cases hω : ω ∈ s
  · simp only [hω, ite_true]
    ring
  · simp only [hω, ite_false]
    ring

theorem RealizedStrategy.switchAfter_gain_apply
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (t : ℝ≥0) (ω : Ω) :
    (H.switchAfter S hS hSRight K τ hτ s hs T hτT).gain t ω =
      if ω ∈ s then
        H.gain (min t (τ ω)) ω + K.gain t ω -
          K.gain (min t (τ ω)) ω
      else H.gain t ω := by
  exact congrFun (congrFun (RealizedStrategy.switchAfter_gain
    S hS hSRight H K τ hτ s hs T hτT) t) ω

theorem RealizedStrategy.switchAfter_gain_outside
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (t : ℝ≥0) (ω : Ω) (hω : ω ∉ s) :
    (H.switchAfter S hS hSRight K τ hτ s hs T hτT).gain t ω =
      H.gain t ω := by
  rw [RealizedStrategy.switchAfter_gain_apply]
  simp [hω]

/-! ## Candidate-specific terminal switching -/

noncomputable def TerminalStrategy.switchAfter
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : TerminalStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    TerminalStrategy (ℱ := ℱ) μ S where
  realized := H.realized.switchAfter S hS hSRight K.realized
    τ hτ s hs T hτT
  terminalGain := fun ω => if ω ∈ s then
      K.terminalGain ω + H.realized.gain (τ ω) ω -
        K.realized.gain (τ ω) ω
    else H.terminalGain ω
  terminalWitness := by
    filter_upwards [H.terminalWitness, K.terminalWitness]
      with ω hH hK
    by_cases hω : ω ∈ s
    · have hStoppedH : Tendsto
          (fun _ : ℝ≥0 => H.realized.gain (τ ω) ω)
          atTop (𝓝 (H.realized.gain (τ ω) ω)) :=
        tendsto_const_nhds
      have hStoppedK : Tendsto
          (fun _ : ℝ≥0 => K.realized.gain (τ ω) ω)
          atTop (𝓝 (K.realized.gain (τ ω) ω)) :=
        tendsto_const_nhds
      have hLimit := (hStoppedH.add hK).sub hStoppedK
      have hSwitchEventually : ∀ᶠ t : ℝ≥0 in atTop,
          (H.realized.switchAfter S hS hSRight K.realized
            τ hτ s hs T hτT).gain t ω =
            H.realized.gain (τ ω) ω + K.realized.gain t ω -
              K.realized.gain (τ ω) ω := by
        filter_upwards [eventually_ge_atTop T] with t ht
        rw [RealizedStrategy.switchAfter_gain_apply]
        simp only [hω, ite_true, min_eq_right ((hτT ω).trans ht)]
      simp only [hω, ite_true]
      simpa only [add_comm] using hLimit.congr'
        (Filter.EventuallyEq.symm hSwitchEventually)
    · have hSwitchEventually : ∀ᶠ t : ℝ≥0 in atTop,
          (H.realized.switchAfter S hS hSRight K.realized
            τ hτ s hs T hτT).gain t ω = H.realized.gain t ω :=
        Filter.Eventually.of_forall fun t =>
          RealizedStrategy.switchAfter_gain_outside S hS hSRight
            H.realized K.realized τ hτ s hs T hτT t ω hω
      simp only [hω, ite_false]
      exact hH.congr' (Filter.EventuallyEq.symm hSwitchEventually)

@[simp]
theorem TerminalStrategy.switchAfter_realized
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : TerminalStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (TerminalStrategy.switchAfter S hS hSRight H K τ hτ s hs T hτT).realized =
      H.realized.switchAfter S hS hSRight K.realized τ hτ s hs T hτT :=
  rfl

@[simp]
theorem TerminalStrategy.switchAfter_terminalGain
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : TerminalStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (TerminalStrategy.switchAfter S hS hSRight H K τ hτ s hs T hτT).terminalGain =
      fun ω => if ω ∈ s then
        K.terminalGain ω + H.realized.gain (τ ω) ω -
          K.realized.gain (τ ω) ω
      else H.terminalGain ω :=
  rfl

theorem TerminalStrategy.switchAfter_gain_apply
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : TerminalStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (t : ℝ≥0) (ω : Ω) :
    (TerminalStrategy.switchAfter S hS hSRight H K τ hτ s hs T hτT).realized.gain t ω =
      if ω ∈ s then
        H.realized.gain (min t (τ ω)) ω + K.realized.gain t ω -
          K.realized.gain (min t (τ ω)) ω
      else H.realized.gain t ω := by
  rw [TerminalStrategy.switchAfter_realized]
  exact RealizedStrategy.switchAfter_gain_apply S hS hSRight
    H.realized K.realized τ hτ s hs T hτT t ω

end PredictableElementaryEmery

end FTAPTheorem42

namespace FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

/-! ## Differences retaining the normalized components of realized gains -/

open MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Subtract two original-price realizations using the existing linear operations. -/
noncomputable def sub (R : RealizedStrategy (ℱ := F) μ S)
    (hS : IsStronglyProgressive F S) (V : RealizedStrategy (ℱ := F) μ S) :
    RealizedStrategy (ℱ := F) μ S := R.add S hS (V.neg S hS)

omit [SigmaFiniteFiltration μ F] in
@[simp]
theorem sub_gain (R : RealizedStrategy (ℱ := F) μ S)
    (hS : IsStronglyProgressive F S) (V : RealizedStrategy (ℱ := F) μ S) :
    (R.sub hS V).gain = R.gain - V.gain := by
  funext t ω
  exact (sub_eq_add_neg _ _).symm

/-- The same difference of components is a decomposition of the actual
original-price difference; no new decomposition is selected. -/
noncomputable def subDecomposition (R : RealizedStrategy (ℱ := F) μ S)
    (hS : IsStronglyProgressive F S) (V : RealizedStrategy (ℱ := F) μ S)
    (D : J1Decomposition R.gain F μ) (E : J1Decomposition V.gain F μ) :
    J1Decomposition (R.sub hS V).gain F μ := D.add E.neg

@[simp]
theorem subDecomposition_N (R : RealizedStrategy (ℱ := F) μ S)
    (hS : IsStronglyProgressive F S) (V : RealizedStrategy (ℱ := F) μ S)
    (D : J1Decomposition R.gain F μ) (E : J1Decomposition V.gain F μ) :
    (R.subDecomposition hS V D E).N = D.N - E.N := (sub_eq_add_neg _ _).symm

@[simp]
theorem subDecomposition_A (R : RealizedStrategy (ℱ := F) μ S)
    (hS : IsStronglyProgressive F S) (V : RealizedStrategy (ℱ := F) μ S)
    (D : J1Decomposition R.gain F μ) (E : J1Decomposition V.gain F μ) :
    (R.subDecomposition hS V D E).A = D.A - E.A := (sub_eq_add_neg _ _).symm

end FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy
