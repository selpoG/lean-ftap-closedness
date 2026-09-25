/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.TerminalMarket
import FTAPTheorem42.Stochastic.Martingale.Basic.ContinuousDoobEnvelope
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryStoppingIntegrand

/-!
# Deterministic stopping in the realized elementary Emery carrier

This module closes the finite deterministic-horizon restriction of the
realized completion.  The stopped representative is the predictable
algebraic stop, while the realized gain is the stopped càdlàg gain process.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! Product and stopping commute at the finite elementary level. -/

omit [MeasurableSpace Ω] in
theorem max_max_min_stop_identity
    {a b c d x : ℝ≥0} (hcd : c ≤ d) :
    max (max a (max c x)) (min b (max d x)) =
      max (max (max a c) (min b d)) x := by
  rcases le_total x d with hxd | hdx
  · rw [max_eq_left hxd]
    ac_rfl
  · have hcx : c ≤ x := hcd.trans hdx
    have hminx : min b x ≤ max a x :=
      (min_le_right _ _).trans (le_max_right _ _)
    let base : ℝ≥0 := max (max a c) (min b d)
    have haBase : a ≤ base :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hcBase : c ≤ base :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hmaxax : max a x ≤ max base x := by
      exact max_le
        (haBase.trans (le_max_left _ _))
        (le_max_right _ _)
    have hbaseLe : base ≤ max (max a x) (min b x) := by
      apply max_le
      · apply max_le
        · exact (le_max_left _ _).trans (le_max_left _ _)
        · exact hcx.trans (le_max_right a x) |>.trans
            (le_max_left _ _)
      · have hxL : x ≤ max (max a x) (min b x) :=
          (le_max_right a x).trans (le_max_left _ _)
        exact (min_le_right _ _).trans hdx |>.trans hxL
    rw [max_eq_right hcx, max_eq_right hdx]
    change max (max a x) (min b x) = max base x
    apply le_antisymm
    · have hminR : min b x ≤ max base x := hminx.trans hmaxax
      exact max_le hmaxax hminR
    · have hxL : x ≤ max (max a x) (min b x) :=
        (le_max_right a x).trans (le_max_left _ _)
      exact max_le hbaseLe hxL

private theorem interval_mul_after_eq_after_mul
    (B C : PredictableElementaryInterval ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    (B.mul (C.after τ hτ)).interval =
      ((B.mul C).after τ hτ).interval := by
  apply ElementaryInterval.ext
  · funext ω
    simp [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.after, ElementaryInterval.after]
  · funext ω
    simp only [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.after, ElementaryInterval.after]
    exact (max_assoc _ _ _).symm
  · funext ω
    simp only [PredictableElementaryInterval.mul,
      PredictableElementaryInterval.after, ElementaryInterval.after]
    exact max_max_min_stop_identity
      (C.interval.start_le_stop ω)

private theorem interval_mul_neg_eq_neg_mul
    (B C : PredictableElementaryInterval ℱ) :
    (B.mul C.neg).interval = (B.mul C).interval.neg := by
  apply ElementaryInterval.ext
  · funext ω
    simp [PredictableElementaryInterval.mul, PredictableElementaryInterval.neg,
      ElementaryInterval.neg, ElementaryInterval.mulCoefficient]
  · funext ω
    simp [PredictableElementaryInterval.mul, PredictableElementaryInterval.neg,
      ElementaryInterval.neg, ElementaryInterval.mulCoefficient]
  · funext ω
    simp [PredictableElementaryInterval.mul, PredictableElementaryInterval.neg,
      ElementaryInterval.neg, ElementaryInterval.mulCoefficient]

private theorem strategy_mul_after_eq_after_mul
    (J H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    J.mul (H.after τ hτ) = (J.mul H).after τ hτ := by
  induction J with
  | nil => rfl
  | cons B J ih =>
      unfold PredictableElementaryStrategy.mul
      simp only [List.flatMap_cons, PredictableElementaryStrategy.after,
        List.map_append, List.map_map]
      have hHead :
          List.map (fun C => (B.mul (C.after τ hτ))) H =
            List.map (fun C => (B.mul C).after τ hτ) H := by
        apply List.map_congr_left
        intro C hC
        apply PredictableElementaryInterval.ext
        exact interval_mul_after_eq_after_mul B C τ hτ
      have hTail :
          List.flatMap (fun B =>
              List.map (fun C => B.mul (C.after τ hτ)) H) J =
            List.map (fun B => B.after τ hτ)
              (List.flatMap (fun B => List.map B.mul H) J) := by
        simpa only [PredictableElementaryStrategy.mul,
          PredictableElementaryStrategy.after, List.map_map,
          Function.comp_def] using ih
      simp only [Function.comp_def] at ⊢
      rw [hHead, hTail]

theorem strategy_mul_neg_eq_neg_mul
    (J H : PredictableElementaryStrategy ℱ) :
    J.mul H.neg = (J.mul H).neg := by
  induction J with
  | nil => rfl
  | cons B J ih =>
      unfold PredictableElementaryStrategy.mul
      simp only [List.flatMap_cons, PredictableElementaryStrategy.neg,
        List.map_map]
      have hHead :
          List.map (fun C => B.mul C.neg) H =
            List.map (fun C => (B.mul C).neg) H := by
        apply List.map_congr_left
        intro C hC
        apply PredictableElementaryInterval.ext
        exact interval_mul_neg_eq_neg_mul B C
      have hTail :
          List.flatMap (fun B => List.map (fun C => B.mul C.neg) H) J =
            List.map PredictableElementaryInterval.neg
              (List.flatMap (fun B => List.map B.mul H) J) := by
        simpa only [PredictableElementaryStrategy.mul,
          PredictableElementaryStrategy.neg, List.map_map,
          Function.comp_def] using ih
      have hHead' :
          List.map (fun C => (B.mul C).neg) H =
            List.map PredictableElementaryInterval.neg
              (List.map B.mul H) := by
        simp only [List.map_map, Function.comp_def]
      simp only [Function.comp_def] at ⊢
      rw [hHead, hHead', hTail, List.map_append]

private theorem elementaryGain_neg
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ) :
    elementaryGain S H.neg = fun t ω => -elementaryGain S H t ω := by
  funext t ω
  simp only [elementaryGain, PredictableElementaryStrategy.toElementary_neg,
    ElementaryStrategy.gain_neg]

private theorem elementaryGain_after
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    elementaryGain S (H.after τ hτ) =
      fun t ω => elementaryGain S H t ω -
        elementaryGain S H (min t (τ ω)) ω := by
  funext t ω
  simp only [elementaryGain, PredictableElementaryStrategy.toElementary_after,
    ElementaryStrategy.gain_after]

theorem testedGain_stopAt
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    testedGain S J (H.stopAt τ hτ) =
      fun t ω => testedGain S J H (min t (τ ω)) ω := by
  unfold testedGain
  change elementaryGain S (J.strategy.mul (H.stopAt τ hτ)) =
    fun t ω => elementaryGain S (J.strategy.mul H)
      (min t (τ ω)) ω
  rw [show H.stopAt τ hτ = H ++ (H.after τ hτ).neg by rfl,
    elementaryGain_mul_append, strategy_mul_neg_eq_neg_mul,
    elementaryGain_neg, strategy_mul_after_eq_after_mul,
    elementaryGain_after]
  funext t ω
  ring

theorem testedDifference_stopAt
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ) =
      fun t ω => testedDifference S J H K (min t (τ ω)) ω := by
  unfold testedDifference
  rw [testedGain_stopAt, testedGain_stopAt]

theorem elementaryGain_stopAt
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    elementaryGain S (H.stopAt τ hτ) =
      fun t ω => elementaryGain S H (min t (τ ω)) ω := by
  rw [show H.stopAt τ hτ = H ++ (H.after τ hτ).neg by rfl,
    elementaryGain_append, elementaryGain_neg, elementaryGain_after]
  funext t ω
  ring

/-! The stopped compact-uniform envelope is controlled by a larger
deterministic horizon of the original process. -/

omit [MeasurableSpace Ω] in
private theorem eFactorialRunningMaxEnvelope_stopped_le
    (X : Process Ω) (T R N : ℝ≥0)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hTN : T ≤ N) (ω : Ω) :
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => |X (min t T) ω|) R ω ≤
      FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => |X t ω|) N ω := by
  have hRightAbs : ∀ ω t,
      ContinuousWithinAt ((fun s => |X s ω|)) (Set.Ici t) t := by
    intro ω t
    exact (hRight ω t).abs
  apply iSup_le
  intro r
  obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (r * r.factorial + 1))
    Finset.nonempty_range_add_one
    (fun j =>
      (FactorialChronologicalGrid.stoppedGrid R r).natSample
        (fun t ω => |X (min t T) ω|) j ω)
  rw [show FactorialChronologicalGrid.factorialRunningMax
      (fun t ω => |X (min t T) ω|) R r ω =
        (FactorialChronologicalGrid.stoppedGrid R r).natSample
          (fun t ω => |X (min t T) ω|) k ω by
      exact hkEq]
  change ENNReal.ofReal
      |X (min ((FactorialChronologicalGrid.stoppedGrid R r).sampledTime k) T) ω| ≤ _
  apply FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
    (fun t ω => |X t ω|) N hRightAbs ω
  exact (min_le_right _ _).trans hTN

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_stopped_le
    (X : Process Ω) (T R N : ℝ≥0)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hTN : T ≤ N) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X (min t T) ω) R ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X N ω := by
  let EStop := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    (fun t ω => |X (min t T) ω|) R ω
  let EOrig := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    (fun t ω => |X t ω|) N ω
  have hE : EStop ≤ EOrig := by
    exact eFactorialRunningMaxEnvelope_stopped_le X T R N hRight hTN ω
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  change (min EStop 1).toReal ≤ (min EOrig 1).toReal
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by finiteness) (min_le_right EOrig 1))
  exact min_le_min hE le_rfl

theorem testValue_stopAt_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (T R N : ℝ≥0) (hTN : T ≤ N) :
    testValue μ S J (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
        (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R ≤
      gauge μ S H K N := by
  let EStop := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J
      (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
      (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T))) R
  let EOrig := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H K) N
  have hIntStop : Integrable EStop μ := by
    simpa only [EStop] using testEnvelope_integrable S hS J
      (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
      (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R
  have hIntOrig : Integrable EOrig μ := by
    simpa only [EOrig] using testEnvelope_integrable S hS J H K N
  have hPoint : ∀ ω, EStop ω ≤ EOrig ω := by
    intro ω
    change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S J
        (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
        (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T))) R ω ≤ _
    rw [testedDifference_stopAt]
    exact cappedFiniteHorizonAbsoluteEnvelope_stopped_le
      (testedDifference S J H K) T R N
      (testedDifference_rightContinuous S hSRight J H K) hTN ω
  have hValue :
      testValue μ S J
          (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
          (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R =
        ∫ ω, EStop ω ∂μ := by
    simpa only [EStop] using testValue_eq_integral μ S J
      (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
      (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R
  calc
    testValue μ S J
        (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
        (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R =
        ∫ ω, EStop ω ∂μ := hValue
    _ ≤ ∫ ω, EOrig ω ∂μ := by
      apply integral_mono_ae hIntStop hIntOrig
      filter_upwards [] with ω
      exact hPoint ω
    _ = testValue μ S J H K N :=
      (testValue_eq_integral μ S J H K N).symm
    _ ≤ gauge μ S H K N := by
      exact le_csSup (gauge_bddAbove S hS H K N)
        (Set.mem_insert_of_mem 0 (Set.mem_range_self J))

theorem gauge_stopAt_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : PredictableElementaryStrategy ℱ)
    (T R N : ℝ≥0) (hTN : T ≤ N) :
    gauge μ S
        (H.stopAt (fun _ => T) (isStoppingTime_const ℱ T))
        (K.stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R ≤
      gauge μ S H K N := by
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · exact gauge_nonnegative S hS H K N
  · exact testValue_stopAt_le S hS hSRight J H K T R N hTN

theorem isCauchy_stopAt
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H) (T : ℝ≥0) :
    IsCauchy μ S
      (fun n => (H n).stopAt (fun _ => T) (isStoppingTime_const ℱ T)) := by
  intro R
  have hUpper : Tendsto
      (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2)
        ((Nat.ceil T + 1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
    hH ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds) hUpper
  · filter_upwards [] with p
    exact gauge_nonnegative S hS
      ((H p.1).stopAt (fun _ => T) (isStoppingTime_const ℱ T))
      ((H p.2).stopAt (fun _ => T) (isStoppingTime_const ℱ T)) R
  · exact Filter.Eventually.of_forall fun p =>
      gauge_stopAt_le S hS hSRight (H p.1) (H p.2) T R
        ((Nat.ceil T + 1 : ℕ) : ℝ≥0) (((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _))))

/-! The realized carrier is closed under deterministic stopping. -/

noncomputable def RealizedStrategy.deterministicallyStop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : ℝ≥0) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n =>
    (H.representative n).stopAt (fun _ => T) (isStoppingTime_const ℱ T)
  representativeBound := fun n => 2 * H.representativeBound n
  representative_coefficientAbsSum_le := by
    intro n ω
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    exact mul_le_mul_of_nonneg_left
      (H.representative_coefficientAbsSum_le n ω) (by positivity)
  gain := MeasureTheory.stoppedProcess H.gain
    (fun _ : Ω => (T : WithTop ℝ≥0))
  gain_stronglyAdapted := by
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.gain_stronglyAdapted (isStoppingTime_const ℱ T) H.gain_rightContinuous
  gain_rightContinuous := by
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      H.gain H.gain_rightContinuous
  gain_hasLeftLimits := by
    exact H.gain_hasLeftLimits.stoppedProcess
      (fun _ : Ω => (T : WithTop ℝ≥0))
  gain_convergence := by
    intro r
    let N : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
    have hTN : T ≤ N := ((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _)))
    refine tendstoInMeasure_of_nonneg_le
      (f := fun n =>
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S
              ((H.representative n).stopAt
                (fun _ => T) (isStoppingTime_const ℱ T)) t ω -
            MeasureTheory.stoppedProcess H.gain
              (fun _ : Ω => (T : WithTop ℝ≥0)) t ω)
          ((r + 1 : ℕ) : ℝ≥0))
      (g := fun n ω =>
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n) t ω -
            H.gain t ω) N ω) ?_ ?_
    · intro n ω
      constructor
      · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
          _ _ _
      · have hDiff :
            (fun t ω => elementaryGain S
                ((H.representative n).stopAt
                  (fun _ => T) (isStoppingTime_const ℱ T)) t ω -
              MeasureTheory.stoppedProcess H.gain
                (fun _ : Ω => (T : WithTop ℝ≥0)) t ω) =
              (fun t ω =>
                (fun s ω => elementaryGain S (H.representative n) s ω -
                  H.gain s ω) (min t T) ω) := by
          funext t ω
          rw [elementaryGain_stopAt, stoppedProcess_const_apply]
        have hRightDiff : ∀ ω t,
              ContinuousWithinAt
                ((fun s => elementaryGain S (H.representative n) s ω -
                  H.gain s ω)) (Set.Ici t) t := by
          intro ω t
          exact
            (PredictableElementaryStrategy.rightContinuous_gain S hSRight
              (H.representative n) ω t).sub
              (H.gain_rightContinuous ω t)
        rw [hDiff]
        exact cappedFiniteHorizonAbsoluteEnvelope_stopped_le
          (fun t ω => elementaryGain S (H.representative n) t ω -
            H.gain t ω)
          T ((r + 1 : ℕ) : ℝ≥0) N hRightDiff hTN ω
    · simpa only [N] using H.gain_convergence (Nat.ceil T)
  isCauchy := isCauchy_stopAt S hS hSRight H.representative H.isCauchy T

@[simp]
theorem RealizedStrategy.deterministicallyStop_gain
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : ℝ≥0) :
    (H.deterministicallyStop S hS hSRight T).gain =
      MeasureTheory.stoppedProcess H.gain
        (fun _ : Ω => (T : WithTop ℝ≥0)) :=
  rfl

theorem RealizedStrategy.deterministicallyStop_gain_apply
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T t : ℝ≥0) (ω : Ω) :
    (H.deterministicallyStop S hS hSRight T).gain t ω =
      H.gain (min t T) ω := by
  rw [RealizedStrategy.deterministicallyStop_gain,
    stoppedProcess_const_apply]

end PredictableElementaryEmery

end FTAPTheorem42
