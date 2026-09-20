/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.EventSwitching

import FTAPTheorem42.Interface.IntegralClosure
import FTAPTheorem42.Stochastic.DS.Lemma411.FiniteHahnImprovement

/-! # Finite terminal claims from sums in the original general graph -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Return the exact finite stopped terminal of a sum to the original
market at its proved admissibility level. -/
theorem finiteStopped_sum_mem_original_terminalClaims
    (source : BoundedSemimartingaleSource S F μ)
    {K H X Y : Process Ω}
    (hX : IsTruncatedIntegralGraph (unitSource source) K X)
    (hY : IsTruncatedIntegralGraph (unitSource source) H Y)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (T : NNReal) (hτT : ∀ ω, τ ω ≤ T)
    {a : Real} (ha : 0 < a)
    (hLower : ∀ᵐ ω ∂μ, ∀ t, -a ≤ (X + Y) (min t (τ ω)) ω) :
    (fun ω => (X + Y) (τ ω) ω) ∈ truncatedTerminalClaimsBy (unitSource source) a := by
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  obtain ⟨R, hR⟩ := truncated_integralGraph_exists_realizedStrategy source hX
  obtain ⟨V, hV⟩ := truncated_integralGraph_exists_realizedStrategy source hY
  have hSum : ∃ J, IsTruncatedIntegralGraph (unitSource source) J (X + Y) := by
    apply (exists_truncatedIntegralGraph_iff_exists_realizedStrategy source (X + Y)).mpr
    exact ⟨R.add S hS V, hR.add hV⟩
  obtain ⟨J, hJ⟩ := hSum
  have hStop := truncated_integralGraph_finiteStopped source hJ τ hτ
  refine ⟨ha, _, _, hStop, ?_, ?_⟩
  · intro t
    exact hLower.mono fun ω hω => hω t
  · apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    change (X + Y) (τ ω) ω = (X + Y) (min t (τ ω)) ω
    rw [min_eq_right ((hτT ω).trans ht)]

/-! ## Returning finite event pasting to the original general graph -/

open Classical in
/-- Stop one original gain and, on an event known at `T`, add the
second gain's increment from `T` to `U`. -/
theorem exists_generalGraph_of_finite_event_pasting
    (source : BoundedSemimartingaleSource S F μ)
    {K H X Y : Process Ω}
    (hX : IsTruncatedIntegralGraph (unitSource source) K X)
    (hY : IsTruncatedIntegralGraph (unitSource source) H Y)
    (σ : Ω → NNReal) (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop NNReal)))
    (T U : NNReal) (hTU : T ≤ U) (hσT : ∀ ω, σ ω ≤ T)
    (s : Set Ω) (hs : MeasurableSet[F T] s) :
    ∃ J, IsTruncatedIntegralGraph (unitSource source) J
      (fun t ω => X (min t (σ ω)) ω +
        if ω ∈ s then Y (min t U) ω - Y (min t T) ω else 0) := by
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  obtain ⟨R, hR⟩ := truncated_integralGraph_exists_realizedStrategy source hX
  obtain ⟨V, hV⟩ := truncated_integralGraph_exists_realizedStrategy source hY
  let A := R.stopAt S hS source.rightContinuous σ hσ T hσT
  let B := V.stopAt S hS source.rightContinuous (fun _ => U)
    (isStoppingTime_const F U) U (fun _ => le_rfl)
  have hs' : MeasurableSet[(isStoppingTime_const F T).measurableSpace] s := by
    rw [IsStoppingTime.measurableSpace_const]
    exact hs
  let C := B.eventTailAfter S hS source.rightContinuous (fun _ => T)
    (isStoppingTime_const F T) s hs' T (fun _ => le_rfl)
  apply (exists_truncatedIntegralGraph_iff_exists_realizedStrategy source _).mpr
  refine ⟨A.add S hS C, ?_⟩
  filter_upwards [hR, hV] with ω hr hv
  intro t
  change A.gain t ω + C.gain t ω = _
  rw [show A.gain t ω = R.gain (min t (σ ω)) ω from
    R.stopAt_gain_apply S hS source.rightContinuous σ hσ T t hσT ω]
  rw [RealizedStrategy.eventTailAfter_gain_apply]
  have hB u : B.gain u ω = Y (min u U) ω := by
    rw [RealizedStrategy.stopAt_gain_apply, hv]
  rw [hr, hB, hB, min_eq_left ((min_le_right t T).trans hTU)]

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## The continued Hahn improvement is an original-market terminal claim -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  [F.IsRightContinuous] {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Extend the finite Hahn interval by the original baseline on survival.
The exact pasted process retains its admissibility and its own terminal. -/
theorem finiteHahnPastedGain_mem_original_terminalClaims
    (source : BoundedSemimartingaleSource S F μ)
    {H K Y V N M C : Process Ω}
    (hYGraph : IsTruncatedIntegralGraph (unitSource source) H Y)
    (hVGraph : IsTruncatedIntegralGraph (unitSource source) K V)
    (hN : StronglyAdapted F N) (hM : StronglyAdapted F M)
    (hNR : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t)
    (hMR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    {T U : NNReal} (hTU : T ≤ U) {δ : Real} (hδ : 0 ≤ δ)
    (hYLower : ∀ᵐ ω ∂μ, ∀ t, (-1 : Real) ≤ Y t ω)
    (hStop : ∀ᵐ ω ∂μ, ∀ t, -(1 + δ) ≤
      (Y + V) (min t (finiteHahnDownsideTime N M δ T ω)) ω)
    (hV : V T =ᵐ[μ] (N + C) T) (hC : ∀ᵐ ω ∂μ, 0 ≤ C T ω) :
    let Z := finiteHahnPastedGain Y V N M δ T U
    (∃ J, IsTruncatedIntegralGraph (unitSource source) J Z) ∧
    (∀ᵐ ω ∂μ, ∀ t, -(1 + δ) ≤ Z t ω) ∧
    Z U ∈ truncatedTerminalClaimsBy (unitSource source) (1 + δ) := by
  let Z := finiteHahnPastedGain Y V N M δ T U
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  have hSum : ∃ J, IsTruncatedIntegralGraph (unitSource source) J (Y + V) := by
    obtain ⟨R, hR⟩ := truncated_integralGraph_exists_realizedStrategy source hYGraph
    obtain ⟨W, hW⟩ := truncated_integralGraph_exists_realizedStrategy source hVGraph
    apply (exists_truncatedIntegralGraph_iff_exists_realizedStrategy source (Y + V)).mpr
    exact ⟨R.add S hS W, hR.add hW⟩
  let ρ := lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ
  let τ := finiteHahnDownsideTime N M δ T
  have hρ : IsStoppingTime F ρ := by
    apply lowerStrictHittingAfter_isStoppingTime
    · exact fun t => (hN t).sub (((hM t).measurable.max measurable_const).stronglyMeasurable)
    · exact fun ω t => (hNR ω t).sub ((hMR ω t).max continuousWithinAt_const)
  have hτ := finiteHahnDownsideTime_isStoppingTime hN hM hNR hMR δ T
  have hτT : ∀ ω, τ ω ≤ T := RightContinuousStoppedMartingale.boundedTime_le _ _
  have hs : MeasurableSet[F T] {ω | (T : WithTop NNReal) < ρ ω} := by
    simpa only [Set.compl_ofPred, not_le] using (hρ T).compl
  obtain ⟨J, hJ⟩ := hSum
  have hGraph : ∃ J, IsTruncatedIntegralGraph (unitSource source) J Z := by
    obtain ⟨K, hK⟩ :=
      exists_generalGraph_of_finite_event_pasting source hJ hYGraph τ hτ T U hTU hτT _ hs
    refine ⟨K, ?_⟩
    convert hK using 1
    funext t ω
    by_cases he : (T : WithTop NNReal) <
        lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω
    · simp only [Z, finiteHahnPastedGain, ρ, Set.mem_ofPred_eq, ite_eq_left he, τ]
    · simp only [Z, finiteHahnPastedGain, ρ, Set.mem_ofPred_eq, ite_eq_right he, τ]
  have hLower : ∀ᵐ ω ∂μ, ∀ t, -(1 + δ) ≤ Z t ω := by
    filter_upwards [hYLower, hStop, hV, hC] with ω hy hs hv hc
    exact finiteHahnPastedGain_lower_bound hTU ω hy hs hv hc
  refine ⟨hGraph, hLower, ?_⟩
  obtain ⟨J, hJ⟩ := hGraph
  refine ⟨by linarith, J, Z, hJ, fun t => hLower.mono fun ω hω => hω t, ?_⟩
  apply Eventually.of_forall
  intro ω
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop U] with t ht
  exact (finiteHahnPastedGain_eventually_constant Y V N M hTU δ ω t ht).symm

end FTAPTheorem42.BoundedSourceIntegralMarket
