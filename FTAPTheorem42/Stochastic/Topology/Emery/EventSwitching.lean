/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.FiniteStopping
import FTAPTheorem42.Trading.MaximalClaims
import FTAPTheorem42.Stochastic.Process.Envelope.RightSkeletonEnvelope

/-!
# Event-tail switching in the realized elementary Emery carrier

This file records the event-tail operation used when a strategy is replaced
after a bounded stopping time on an event known at that time.  The event is
implemented by the predictable elementary restriction already present in the
elementary calculus.  This module stops at the event-tail restriction itself;
the full terminal switch, its admissibility, and the pasting consumer are left
to the next boundary.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_indicator_le
    (X : Process Ω) (s : Set Ω) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => s.indicator (X t) ω) T ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω := by
  by_cases hω : ω ∈ s
  · have hfactorial : ∀ r : ℕ,
        FactorialChronologicalGrid.factorialRunningMax
            (fun t ω' => |s.indicator (X t) ω'|) T r ω =
          FactorialChronologicalGrid.factorialRunningMax
            (fun t ω' => |X t ω'|) T r ω := by
      intro r
      unfold FactorialChronologicalGrid.factorialRunningMax finiteRunningMax
      have hfun :
          (fun k =>
              ((FactorialChronologicalGrid.stoppedGrid T r).natSample
                (fun t ω' => |s.indicator (X t) ω'|) k) ω) =
            (fun k =>
              ((FactorialChronologicalGrid.stoppedGrid T r).natSample
                (fun t ω' => |X t ω'|) k) ω) := by
        funext k
        simp only [ChronologicalGrid.natSample]
        simp [hω]
      rw [hfun]
    have hEnvelope :
        FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
            (fun t ω' => |s.indicator (X t) ω'|) T ω =
          FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
            (fun t ω' => |X t ω'|) T ω := by
      unfold FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
      apply iSup_congr
      intro r
      rw [hfactorial r]
    unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    rw [hEnvelope]
  · unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    unfold FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    have hfactorial : ∀ r : ℕ,
        FactorialChronologicalGrid.factorialRunningMax
            (fun t ω' => |s.indicator (X t) ω'|) T r ω = 0 := by
      intro r
      unfold FactorialChronologicalGrid.factorialRunningMax finiteRunningMax
      apply le_antisymm
      · apply Finset.sup'_le
          (Finset.nonempty_range_add_one)
        intro k hk
        simp only [ChronologicalGrid.natSample]
        rw [Set.indicator_of_notMem hω]
        simp
      · exact finiteRunningMax_nonneg _ _ (fun _ _ => abs_nonneg _) ω
    have hEnvelope :
        (⨆ r, ENNReal.ofReal
            (FactorialChronologicalGrid.factorialRunningMax
              (fun t ω' => |s.indicator (X t) ω'|) T r ω)) = 0 := by
      apply le_antisymm
      · apply iSup_le
        intro r
        rw [hfactorial r, ENNReal.ofReal_zero]
      · exact bot_le
    rw [hEnvelope]
    simp

/-! ## Compatibility with predictable elementary multiplication -/

private theorem interval_mul_restrictAfter_eq_restrictAfter_mul
    (B C : PredictableElementaryInterval ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    (B.mul (C.restrictAfter τ hτ s hs)).interval =
      ((B.mul C).restrictAfter τ hτ s hs).interval := by
  apply ElementaryInterval.ext
  · funext ω
    simp [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.restrictAfter,
      ElementaryInterval.after, ElementaryInterval.mulCoefficient]
  · funext ω
    simp only [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.restrictAfter,
      ElementaryInterval.after, ElementaryInterval.mulCoefficient]
    exact (max_assoc _ _ _).symm
  · funext ω
    simp only [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.restrictAfter,
      ElementaryInterval.after, ElementaryInterval.mulCoefficient]
    exact max_max_min_stop_identity
      (C.interval.start_le_stop ω)

private theorem strategy_mul_restrictAfter_eq_restrictAfter_mul
    (J H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    J.mul (H.restrictAfter τ hτ s hs) =
      (J.mul H).restrictAfter τ hτ s hs := by
  induction J with
  | nil => rfl
  | cons B J ih =>
      unfold PredictableElementaryStrategy.mul
      simp only [List.flatMap_cons, PredictableElementaryStrategy.restrictAfter,
        List.map_append, List.map_map]
      have hHead :
          List.map (fun C => B.mul (C.restrictAfter τ hτ s hs)) H =
            List.map (fun C => (B.mul C).restrictAfter τ hτ s hs) H := by
        apply List.map_congr_left
        intro C hC
        apply PredictableElementaryInterval.ext
        exact interval_mul_restrictAfter_eq_restrictAfter_mul B C τ hτ s hs
      have hTail :
          List.flatMap
              (fun B => List.map (fun C => B.mul (C.restrictAfter τ hτ s hs)) H) J =
            List.map (fun B => B.restrictAfter τ hτ s hs)
              (List.flatMap (fun B => List.map B.mul H) J) := by
        simpa only [PredictableElementaryStrategy.mul,
          PredictableElementaryStrategy.restrictAfter, List.map_map,
          Function.comp_def] using ih
      simp only [Function.comp_def] at ⊢
      rw [hHead, hTail]

theorem testedGain_restrictAfter
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    testedGain S J (H.restrictAfter τ hτ s hs) =
      fun t ω => if ω ∈ s then
        testedGain S J H t ω - testedGain S J H (min t (τ ω)) ω
      else 0 := by
  unfold testedGain
  change elementaryGain S (J.strategy.mul (H.restrictAfter τ hτ s hs)) = _
  rw [strategy_mul_restrictAfter_eq_restrictAfter_mul]
  change ElementaryStrategy.gain S
      (PredictableElementaryStrategy.toElementary
        ((J.strategy.mul H).restrictAfter τ hτ s hs)) = _
  rw [PredictableElementaryStrategy.toElementary_restrictAfter]
  funext t ω
  rw [ElementaryStrategy.gain_restrict]
  by_cases hω : ω ∈ s
  · simp only [hω, ite_true]
    rw [ElementaryStrategy.gain_after]
  · simp [hω]

theorem testedDifference_restrictAfter
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    testedDifference S J (H.restrictAfter τ hτ s hs)
        (K.restrictAfter τ hτ s hs) =
      fun t ω => if ω ∈ s then
        testedDifference S J H K t ω -
          testedDifference S J H K (min t (τ ω)) ω
      else 0 := by
  unfold testedDifference
  rw [testedGain_restrictAfter, testedGain_restrictAfter]
  funext t ω
  by_cases hω : ω ∈ s
  · simp [hω]
    ring
  · simp [hω]

theorem elementaryGain_restrictAfter
    (S : Process Ω)
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    elementaryGain S (H.restrictAfter τ hτ s hs) =
      fun t ω => if ω ∈ s then
        elementaryGain S H t ω - elementaryGain S H (min t (τ ω)) ω
      else 0 := by
  unfold elementaryGain
  change ElementaryStrategy.gain S
      (PredictableElementaryStrategy.toElementary
        (H.restrictAfter τ hτ s hs)) = _
  rw [PredictableElementaryStrategy.toElementary_restrictAfter]
  funext t ω
  rw [ElementaryStrategy.gain_restrict]
  by_cases hω : ω ∈ s
  · simp only [hω, ite_true]
    rw [ElementaryStrategy.gain_after]
  · simp [hω]

/-! ## The event stopping time and its stopped-process formula -/

noncomputable def eventStoppingTimeTop
    (τ : Ω → WithTop ℝ≥0) (s : Set Ω) : Ω → WithTop ℝ≥0 :=
  s.piecewise τ (fun _ => ⊤)

theorem eventStoppingTimeTop_isStoppingTime
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ)
    {s : Set Ω} (hs : MeasurableSet[hτ.measurableSpace] s) :
    IsStoppingTime ℱ (eventStoppingTimeTop τ s) := by
  intro t
  have hs' := hs.2 t
  have hSet : {ω | eventStoppingTimeTop τ s ω ≤ (t : WithTop ℝ≥0)} =
      s ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    by_cases hω : ω ∈ s
    · change eventStoppingTimeTop τ s ω ≤ (t : WithTop ℝ≥0) ↔
        ω ∈ s ∧ τ ω ≤ (t : WithTop ℝ≥0)
      rw [eventStoppingTimeTop,
        Set.piecewise_eq_of_mem s τ (fun _ => ⊤) hω]
      simp [hω]
    · change eventStoppingTimeTop τ s ω ≤ (t : WithTop ℝ≥0) ↔
        ω ∈ s ∧ τ ω ≤ (t : WithTop ℝ≥0)
      rw [eventStoppingTimeTop,
        Set.piecewise_eq_of_notMem s τ (fun _ => ⊤) hω]
      simp only [hω, false_and]
      simpa only [iff_false] using (WithTop.not_top_le_coe t)
  rw [hSet]
  exact hs'

omit [MeasurableSpace Ω] in
theorem stoppedProcess_eventStoppingTimeTop_apply
    (X : Process Ω) (τ : Ω → WithTop ℝ≥0) (s : Set Ω)
    (t : ℝ≥0) (ω : Ω) :
    MeasureTheory.stoppedProcess X (eventStoppingTimeTop τ s) t ω =
      if ω ∈ s then MeasureTheory.stoppedProcess X τ t ω else X t ω := by
  by_cases hω : ω ∈ s
  · change X (min (t : WithTop ℝ≥0)
      (eventStoppingTimeTop τ s ω)).untopA ω = _
    rw [eventStoppingTimeTop,
      Set.piecewise_eq_of_mem s τ (fun _ => ⊤) hω]
    simp only [ite_eq_left hω]
    rfl
  · change X (min (t : WithTop ℝ≥0)
      (eventStoppingTimeTop τ s ω)).untopA ω = _
    rw [eventStoppingTimeTop,
      Set.piecewise_eq_of_notMem s τ (fun _ => ⊤) hω]
    simp only [ite_eq_right hω]
    rw [min_eq_left le_top]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_indicator_sub_le_add
    (X Y : Process Ω) (s : Set Ω) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => s.indicator (fun ω => X t ω - Y t ω) ω) T ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω +
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope Y T ω := by
  have hIndicator := cappedFiniteHorizonAbsoluteEnvelope_indicator_le
    (fun t ω => X t ω - Y t ω) s T ω
  have hSub := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
    X Y (fun _ _ => (0 : ℝ)) T ω
  have hNegX :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => (0 : ℝ) - X t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω := by
    simpa only [zero_sub] using
      (cappedFiniteHorizonAbsoluteEnvelope_neg X T ω)
  have hNegY :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => (0 : ℝ) - Y t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope Y T ω := by
    simpa only [zero_sub] using
      (cappedFiniteHorizonAbsoluteEnvelope_neg Y T ω)
  rw [hNegX, hNegY] at hSub
  exact hIndicator.trans hSub

theorem testValue_restrictAfter_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (R : ℝ≥0) :
    testValue μ S J (H.restrictAfter τ hτ s hs)
        (K.restrictAfter τ hτ s hs) R ≤
      testValue μ S J H K R +
        testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R := by
  let EEvent := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J (H.restrictAfter τ hτ s hs)
      (K.restrictAfter τ hτ s hs)) R
  let EOrig := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H K) R
  let EStop := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ)) R
  have hIntEvent : Integrable EEvent μ := by
    simpa only [EEvent] using testEnvelope_integrable S hS J
      (H.restrictAfter τ hτ s hs) (K.restrictAfter τ hτ s hs) R
  have hIntOrig : Integrable EOrig μ := by
    simpa only [EOrig] using testEnvelope_integrable S hS J H K R
  have hIntStop : Integrable EStop μ := by
    simpa only [EStop] using testEnvelope_integrable S hS J
      (H.stopAt τ hτ) (K.stopAt τ hτ) R
  have hDiff :
      testedDifference S J (H.restrictAfter τ hτ s hs)
          (K.restrictAfter τ hτ s hs) =
        fun t ω => s.indicator (fun ω =>
          testedDifference S J H K t ω -
            testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ) t ω) ω := by
    funext t ω
    rw [testedDifference_restrictAfter, testedDifference_stopAt]
    by_cases hω : ω ∈ s <;> simp [hω]
  have hPoint : ∀ ω, EEvent ω ≤ EOrig ω + EStop ω := by
    intro ω
    change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S J (H.restrictAfter τ hτ s hs)
        (K.restrictAfter τ hτ s hs)) R ω ≤ _
    rw [hDiff]
    exact cappedFiniteHorizonAbsoluteEnvelope_indicator_sub_le_add
      (testedDifference S J H K)
      (testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ)) s R ω
  calc
    testValue μ S J (H.restrictAfter τ hτ s hs)
        (K.restrictAfter τ hτ s hs) R = ∫ ω, EEvent ω ∂μ := by
      simpa only [EEvent] using testValue_eq_integral μ S J
        (H.restrictAfter τ hτ s hs) (K.restrictAfter τ hτ s hs) R
    _ ≤ ∫ ω, (EOrig ω + EStop ω) ∂μ := by
      apply integral_mono_ae hIntEvent (hIntOrig.add hIntStop)
      filter_upwards [] with ω
      exact hPoint ω
    _ = (∫ ω, EOrig ω ∂μ) + ∫ ω, EStop ω ∂μ :=
      integral_add hIntOrig hIntStop
    _ = testValue μ S J H K R +
        testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R := by
      rw [testValue_eq_integral, testValue_eq_integral]

theorem gauge_restrictAfter_le_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T R : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    gauge μ S (H.restrictAfter τ hτ s hs)
        (K.restrictAfter τ hτ s hs) R ≤
      gauge μ S H K R +
        gauge μ S H K ((Nat.ceil T + 1 : ℕ) : ℝ≥0) := by
  let N : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
  have hTN : T ≤ N := by
    dsimp [N]
    exact ((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _)))
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · exact add_nonneg (gauge_nonnegative S hS H K R)
      (gauge_nonnegative S hS H K N)
  · have hVal := testValue_restrictAfter_le (μ := μ) (ℱ := ℱ)
      S hS J H K τ hτ s hs R
    have hOrig : testValue μ S J H K R ≤ gauge μ S H K R :=
      le_csSup (gauge_bddAbove S hS H K R)
        (Set.mem_insert_of_mem 0 (Set.mem_range_self J))
    have hStop :
        testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R ≤
          gauge μ S (H.stopAt τ hτ) (K.stopAt τ hτ) R :=
      le_csSup (gauge_bddAbove S hS (H.stopAt τ hτ) (K.stopAt τ hτ) R)
        (Set.mem_insert_of_mem 0 (Set.mem_range_self J))
    have hStopGauge :
        gauge μ S (H.stopAt τ hτ) (K.stopAt τ hτ) R ≤ gauge μ S H K N :=
      gauge_stopAt_le_of_bounded S hS hSRight H K τ hτ T R N hτT hTN
    have hAdd :
        gauge μ S H K R +
            gauge μ S (H.stopAt τ hτ) (K.stopAt τ hτ) R ≤
          gauge μ S H K R + gauge μ S H K N :=
      add_le_add (le_refl _) hStopGauge
    exact (hVal.trans (add_le_add hOrig hStop)).trans hAdd

theorem isCauchy_restrictAfter_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    IsCauchy μ S
      (fun n => (H n).restrictAfter τ hτ s hs) := by
  intro R
  let N : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
  have hUpper : Tendsto (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2) R)
      atTop (𝓝 0) := hH R
  have hUpperN : Tendsto (fun p : ℕ × ℕ =>
      gauge μ S (H p.1) (H p.2) N) atTop (𝓝 0) := hH N
  have hSum : Tendsto (fun p : ℕ × ℕ =>
      gauge μ S (H p.1) (H p.2) R +
        gauge μ S (H p.1) (H p.2) N) atTop (𝓝 0) := by
    simpa only [add_zero] using hUpper.add hUpperN
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hSum
  · filter_upwards [] with p
    exact gauge_nonnegative S hS
      ((H p.1).restrictAfter τ hτ s hs) ((H p.2).restrictAfter τ hτ s hs) R
  · exact Filter.Eventually.of_forall fun p =>
      gauge_restrictAfter_le_of_bounded S hS hSRight (H p.1) (H p.2)
        τ hτ s hs T R hτT

theorem eventTail_error_eq_indicator_sub
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (t : ℝ≥0) (ω : Ω) :
    elementaryGain S ((H.representative n).restrictAfter τ hτ s hs) t ω -
        (H.gain t ω -
          MeasureTheory.stoppedProcess H.gain
            (eventStoppingTimeTop
              (fun ω => (τ ω : WithTop ℝ≥0)) s) t ω) =
    s.indicator (fun ω =>
        (elementaryGain S (H.representative n) t ω - H.gain t ω) -
          (elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
            MeasureTheory.stoppedProcess H.gain
              (fun ω => (τ ω : WithTop ℝ≥0)) t ω)) ω := by
  rw [elementaryGain_restrictAfter,
    stoppedProcess_eventStoppingTimeTop_apply]
  by_cases hω : ω ∈ s
  · simp only [hω, Set.indicator_of_mem, ite_true]
    rw [show elementaryGain S ((H.representative n).stopAt τ hτ) t ω =
        elementaryGain S (H.representative n) (min t (τ ω)) ω by
      exact congrFun (congrFun (elementaryGain_stopAt S
        (H.representative n) τ hτ) t) ω]
    ring
  · simp [hω]

private theorem coefficientAbsSum_restrictAfter_event
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (ω : Ω) :
    (H.restrictAfter τ hτ s hs).coefficientAbsSum ω =
      if ω ∈ s then H.coefficientAbsSum ω else 0 := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.restrictAfter,
      PredictableElementaryStrategy.coefficientAbsSum]
  | cons B H ih =>
      simp only [PredictableElementaryStrategy.restrictAfter, List.map_cons]
      have hB :
          |(B.restrictAfter τ hτ s hs).interval.coefficient ω| =
            if ω ∈ s then |B.interval.coefficient ω| else 0 := by
        simp only [PredictableElementaryInterval.restrictAfter_interval,
          ElementaryInterval.after, ElementaryInterval.mulCoefficient]
        by_cases hω : ω ∈ s <;> simp [hω]
      have ih' :
          PredictableElementaryStrategy.coefficientAbsSum
              (List.map (fun B => B.restrictAfter τ hτ s hs) H) ω =
            if ω ∈ s then PredictableElementaryStrategy.coefficientAbsSum H ω
              else 0 := by
        simpa only [PredictableElementaryStrategy.restrictAfter] using ih
      change |(B.restrictAfter τ hτ s hs).interval.coefficient ω| +
        PredictableElementaryStrategy.coefficientAbsSum
          (List.map (fun B => B.restrictAfter τ hτ s hs) H) ω =
        if ω ∈ s then |B.interval.coefficient ω| +
          PredictableElementaryStrategy.coefficientAbsSum H ω else 0
      rw [hB, ih']
      by_cases hω : ω ∈ s <;> simp [hω]

/-! ## Event-tail restriction of a realized strategy -/

noncomputable def RealizedStrategy.eventTailAfter
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    RealizedStrategy (ℱ := ℱ) μ S := by
  let ρ : Ω → WithTop ℝ≥0 :=
    eventStoppingTimeTop (fun ω => (τ ω : WithTop ℝ≥0)) s
  have hρ : IsStoppingTime ℱ ρ := by
    exact eventStoppingTimeTop_isStoppingTime hτ hs
  refine
    { representative := fun n =>
        (H.representative n).restrictAfter τ hτ s hs
      representativeBound := H.representativeBound
      representative_coefficientAbsSum_le := by
        intro n ω
        rw [coefficientAbsSum_restrictAfter_event]
        by_cases hω : ω ∈ s
        · simpa only [hω, ite_true] using
            H.representative_coefficientAbsSum_le n ω
        · simp only [hω, ite_false]
          positivity
      gain := fun t ω =>
        H.gain t ω - MeasureTheory.stoppedProcess H.gain ρ t ω
      gain_stronglyAdapted := by
        exact H.gain_stronglyAdapted.sub
          (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
            H.gain_stronglyAdapted hρ H.gain_rightContinuous)
      gain_rightContinuous := by
        intro ω t
        exact (H.gain_rightContinuous ω t).sub
          (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
            (τ := ρ) H.gain H.gain_rightContinuous ω t)
      gain_hasLeftLimits := H.gain_hasLeftLimits.sub
        (H.gain_hasLeftLimits.stoppedProcess ρ)
      gain_convergence := by
        intro r
        let EEvent : ℕ → Ω → ℝ := fun n =>
          FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
            (fun t ω =>
              elementaryGain S ((H.representative n).restrictAfter τ hτ s hs) t ω -
                (H.gain t ω - MeasureTheory.stoppedProcess H.gain ρ t ω))
            ((r + 1 : ℕ) : ℝ≥0)
        let EOrig : ℕ → Ω → ℝ := fun n =>
          FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
            (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
            ((r + 1 : ℕ) : ℝ≥0)
        let EStop : ℕ → Ω → ℝ := fun n =>
          FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
            (fun t ω =>
              elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
                MeasureTheory.stoppedProcess H.gain
                  (fun ω => (τ ω : WithTop ℝ≥0)) t ω)
            ((r + 1 : ℕ) : ℝ≥0)
        have hOrig : TendstoInMeasure μ EOrig atTop (fun _ => (0 : ℝ)) := by
          simpa only [EOrig] using H.gain_convergence r
        have hStop : TendstoInMeasure μ EStop atTop (fun _ => (0 : ℝ)) := by
          simpa only [EStop, RealizedStrategy.stopAt,
            RealizedStrategy.stopAt_gain] using
            (H.stopAt S hS hSRight τ hτ T hτT).gain_convergence r
        have hPoint : ∀ n ω, 0 ≤ EEvent n ω ∧
            EEvent n ω ≤ EOrig n ω + EStop n ω := by
          intro n ω
          have hError :
              (fun t ω =>
                elementaryGain S ((H.representative n).restrictAfter τ hτ s hs) t ω -
                  (H.gain t ω - MeasureTheory.stoppedProcess H.gain ρ t ω)) =
                (fun t ω => s.indicator (fun ω =>
                  (elementaryGain S (H.representative n) t ω - H.gain t ω) -
                    (elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
                      MeasureTheory.stoppedProcess H.gain
                        (fun ω => (τ ω : WithTop ℝ≥0)) t ω)) ω) := by
            funext t ω
            exact eventTail_error_eq_indicator_sub S H n τ hτ s hs t ω
          constructor
          · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
              _ _ _
          · change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
              (fun t ω =>
                elementaryGain S ((H.representative n).restrictAfter τ hτ s hs) t ω -
                  (H.gain t ω - MeasureTheory.stoppedProcess H.gain ρ t ω))
              ((r + 1 : ℕ) : ℝ≥0) ω ≤ _
            rw [hError]
            exact cappedFiniteHorizonAbsoluteEnvelope_indicator_sub_le_add
              (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
              (fun t ω => elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
                MeasureTheory.stoppedProcess H.gain
                  (fun ω => (τ ω : WithTop ℝ≥0)) t ω)
              s ((r + 1 : ℕ) : ℝ≥0) ω
        have hEvent : TendstoInMeasure μ EEvent atTop (fun _ => (0 : ℝ)) := by
          apply tendstoInMeasure_of_nonneg_le_add
          · exact fun n ω => (hPoint n ω).1
          · exact fun n ω => (hPoint n ω).2
          · exact hOrig
          · exact hStop
        simpa only [EEvent] using hEvent
      isCauchy := isCauchy_restrictAfter_of_bounded S hS hSRight
        H.representative H.isCauchy τ hτ s hs T hτT }

theorem RealizedStrategy.eventTailAfter_gain_apply
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (t : ℝ≥0) (ω : Ω) :
    (H.eventTailAfter S hS hSRight τ hτ s hs T hτT).gain t ω =
      if ω ∈ s then H.gain t ω - H.gain (min t (τ ω)) ω else 0 := by
  dsimp only [RealizedStrategy.eventTailAfter]
  rw [stoppedProcess_eventStoppingTimeTop_apply]
  by_cases hω : ω ∈ s
  · simp only [hω, ite_true]
    rw [MeasureTheory.stoppedProcess]
    rw [← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  · simp only [hω, ite_false]
    ring

end PredictableElementaryEmery

end FTAPTheorem42
