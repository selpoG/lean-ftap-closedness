/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Stochastic.Topology.Emery.MeasureTransfer
import FTAPTheorem42.Stochastic.Topology.Emery.UniformTestLimit

/-! # Elementary-test convergence of processes, without special certificates -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem uniform_integral_transfer {ι : Type*} {f : Nat → ι → Ω → Real}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (hf : ∀ n i, StronglyMeasurable (f n i))
    (hb : ∀ n i w, 0 ≤ f n i w ∧ f n i w ≤ 1)
    (h : ∀ ε > (0 : Real), ∀ᶠ n in atTop, ∀ i, ∫ w, f n i w ∂μ ≤ ε) :
    ∀ ε > (0 : Real), ∀ᶠ n in atTop, ∀ i, ∫ w, f n i w ∂ν ≤ ε := by
  intro ε hε
  by_contra hn
  have hbad : ∀ k : Nat, ∃ n ≥ k, ∃ i, ε < ∫ w, f n i w ∂ν := by
    simpa only [eventually_atTop, not_exists, not_forall, not_le, exists_prop] using hn
  choose ns hns is his using hbad
  have hμlim : Tendsto (fun k => ∫ w, f (ns k) (is k) w ∂μ) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun k => ha.trans_le (integral_nonneg fun w => (hb _ _ w).1)
    · intro b hbpos
      obtain ⟨N, hN⟩ := eventually_atTop.mp (h (b / 2) (half_pos hbpos))
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (hN (ns k) (hk.trans (hns k)) (is k)).trans_lt (half_lt_self hbpos)
  open PredictableElementaryEmery in
  have hνlim :=
    integral_tendsto_zero_of_integral_tendsto_zero_of_mutuallyAbsolutelyContinuous
      hμν hνμ (fun k => hf (ns k) (is k)) (fun k w => hb (ns k) (is k) w) hμlim
  obtain ⟨k, hk⟩ := (hνlim.eventually (gt_mem_nhds hε)).exists
  exact (his k).not_gt hk

/-- The Cauchy tail is chosen before the test, including after measure change.
This transfers a topology, not the existence of a special decomposition. -/
theorem ElementaryEmeryConverges.of_equivalentMeasure
    {X : Nat → Process Ω} {Y : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (h : ElementaryEmeryConverges μ F X Y) :
    ElementaryEmeryConverges ν F X Y := by
  intro T
  apply uniform_integral_transfer hμν hνμ _ _ (h T)
  · intro n J
    exact (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      ((PredictableElementaryStrategy.stronglyAdapted_gain _ (hX n) J.strategy).sub
        (PredictableElementaryStrategy.stronglyAdapted_gain _ hY J.strategy)) T).mono (F.le T)
  · intro n J w
    exact ⟨FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _⟩

/-- Existing representatives converge in the process-level relation. This
does not choose or assert the existence of a limiting integrand. -/
theorem PredictableElementaryEmery.RealizedStrategy.elementaryEmeryConverges
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (H : PredictableElementaryEmery.RealizedStrategy (ℱ := F) μ S) :
    ElementaryEmeryConverges μ F
      (fun n => PredictableElementaryEmery.elementaryGain S (H.representative n)) H.gain := by
  intro T ε hε
  obtain ⟨N, hN⟩ := H.uniform_test_error_tail hS hRight T hε
  filter_upwards [eventually_ge_atTop N] with n hn
  intro J
  have heq := PredictableElementaryEmery.elementaryGain_source_mul S J.strategy (H.representative n)
  change (∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (fun t w => PredictableElementaryEmery.elementaryGain
      (PredictableElementaryEmery.elementaryGain S (H.representative n)) J.strategy t w -
      PredictableElementaryEmery.elementaryGain H.gain J.strategy t w) T w ∂μ) ≤ ε
  rw [heq]
  exact hN n hn J

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Uniqueness of zero-initial elementary Emery limits -/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem ElementaryEmeryConverges.test_convergence
    {X : Nat → Process Ω} {Y : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (h : ElementaryEmeryConverges μ F X Y)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    TendstoInMeasure μ (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => ElementaryStrategy.gain (X n) J.strategy.toElementary t w -
        ElementaryStrategy.gain Y J.strategy.toElementary t w) T) atTop 0 := by
  apply PredictableElementaryEmery.tendstoInMeasure_of_integral_tendsto_zero_of_bounded
  · intro n
    exact (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      ((PredictableElementaryStrategy.stronglyAdapted_gain _ (hX n) J.strategy).sub
        (PredictableElementaryStrategy.stronglyAdapted_gain _ hY J.strategy)) T).mono (F.le T)
  · intro n w
    exact ⟨FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _⟩
  · apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun w =>
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)
    · intro b hb
      filter_upwards [h T (b / 2) (half_pos hb)] with n hn
      exact (hn J).trans_lt (half_lt_self hb)

/-- Elementary tests first identify increments. The explicit common initial
value then identifies the whole right-continuous processes on one null set. -/
theorem ElementaryEmeryConverges.limit_indistinguishable
    {X : Nat → Process Ω} {Y Z : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hY : IsStronglyProgressive F Y) (hZ : IsStronglyProgressive F Z)
    (hYr : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hZr : ∀ w t, ContinuousWithinAt (Z · w) (Ici t) t)
    (hInitial : Y 0 =ᵐ[μ] Z 0)
    (hXY : ElementaryEmeryConverges μ F X Y) (hXZ : ElementaryEmeryConverges μ F X Z) :
    ProcessIndistinguishable μ Y Z := by
  have hTest (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
      ProcessIndistinguishable μ
        (ElementaryStrategy.gain Y J.strategy.toElementary)
        (ElementaryStrategy.gain Z J.strategy.toElementary) :=
    FactorialChronologicalGrid.processIndistinguishable_of_common_cappedFiniteHorizon_limit
      (fun n => ElementaryStrategy.gain (X n) J.strategy.toElementary) _ _
      (PredictableElementaryStrategy.rightContinuous_gain Y hYr J.strategy)
      (PredictableElementaryStrategy.rightContinuous_gain Z hZr J.strategy)
      (fun r => ElementaryEmeryConverges.test_convergence (X := X) (Y := Y)
        hX hY hXY J ((r + 1 : Nat) : NNReal))
      (fun r => ElementaryEmeryConverges.test_convergence (X := X) (Y := Z)
        hX hZ hXZ J ((r + 1 : Nat) : NNReal))
  have hEval (t : NNReal) : Y t =ᵐ[μ] Z t := by
    have ht := (hTest
      (BoundedPredictableElementaryMultiplier.horizonUnit (ℱ := F) t)).eventuallyEq_at t
    filter_upwards [ht, hInitial] with w hw h0
    simp only [BoundedPredictableElementaryMultiplier.horizonUnit,
      PredictableElementaryStrategy.toElementary, List.map_cons, List.map_nil,
      ElementaryStrategy.gain, List.sum_cons, List.sum_nil, add_zero,
      ElementaryInterval.gain,
      FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.horizonBlock,
      min_self, min_zero, one_mul] at hw
    exact sub_left_injective (hw.trans (congrArg (fun a => Z t w - a) h0.symm))
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense Y Z
    NNRealRightDenseSkeleton.skeleton NNRealRightDenseSkeleton.skeleton_rightDense
    (Eventually.of_forall hYr) (Eventually.of_forall hZr) (fun k => hEval _)

omit [IsProbabilityMeasure μ] in
/-- Replacing each approximating process on a common null set preserves the
uniform test tail, with no choice of test-dependent exceptional sets. -/
theorem ElementaryEmeryConverges.congr_sequence_eventually
    {X X' : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hEq : ∀ᶠ n in atTop, ProcessIndistinguishable μ (X n) (X' n)) :
    ElementaryEmeryConverges μ F X' Y := by
  intro T ε hε
  filter_upwards [h T ε hε, hEq] with n hn hnEq
  intro J
  have hInt : (∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => ElementaryStrategy.gain (X' n) J.strategy.toElementary t w -
        ElementaryStrategy.gain Y J.strategy.toElementary t w) T w ∂μ) =
      ∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => ElementaryStrategy.gain (X n) J.strategy.toElementary t w -
        ElementaryStrategy.gain Y J.strategy.toElementary t w) T w ∂μ := by
    apply integral_congr_ae
    filter_upwards [hnEq] with w hw
    unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    congr 2
    apply iSup_congr
    intro r
    congr 1
    unfold FactorialChronologicalGrid.factorialRunningMax
    apply Finset.sup'_congr
    · rfl
    · intro k hk
      simp only [ChronologicalGrid.natSample]
      rw [J.strategy.toElementary.gain_congr_price _ w (fun t => (hw t).symm)]
  rw [hInt]
  exact hn J

omit [IsProbabilityMeasure μ] in
theorem ElementaryEmeryConverges.congr_sequence
    {X X' : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hEq : ∀ n, ProcessIndistinguishable μ (X n) (X' n)) :
    ElementaryEmeryConverges μ F X' Y :=
  h.congr_sequence_eventually (Eventually.of_forall hEq)

omit [IsProbabilityMeasure μ] in
theorem ElementaryEmeryConverges.refl (X : Process Ω) :
    ElementaryEmeryConverges μ F (fun _ => X) X := by
  intro T ε hε
  apply Eventually.of_forall
  intro n J
  simpa [FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope,
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope,
    FactorialChronologicalGrid.factorialRunningMax, finiteRunningMax,
    ChronologicalGrid.natSample] using hε.le

end FTAPTheorem42
