/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Stopping
import FTAPTheorem42.Stochastic.Topology.Emery.Multiplier

/-!
# Finite stopping in the realized elementary Émery carrier

Stopping at a bounded finite stopping time preserves the test-error and
gauge bounds needed for Cauchy sequences. This module constructs the stopped
realized strategy and identifies its gain with the stopped original gain.
It also proves scalar linearity of elementary gains in the source process.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] in
private theorem cappedFiniteHorizonAbsoluteEnvelope_stoppedAt_le
    (X : Process Ω) (τ : Ω → ℝ≥0) (T R N : ℝ≥0)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hτT : ∀ ω, τ ω ≤ T) (hTN : T ≤ N) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => X (min t (τ ω)) ω) R ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X N ω := by
  have hRightAbs : ∀ ω t,
      ContinuousWithinAt ((fun s => |X s ω|)) (Set.Ici t) t := by
    intro ω t
    exact (hRight ω t).abs
  have hE : FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
      (fun t ω => |X (min t (τ ω)) ω|) R ω ≤
      FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => |X t ω|) N ω := by
    apply iSup_le
    intro r
    obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (r * r.factorial + 1))
      Finset.nonempty_range_add_one
      (fun j =>
        (FactorialChronologicalGrid.stoppedGrid R r).natSample
          (fun t ω => |X (min t (τ ω)) ω|) j ω)
    rw [show FactorialChronologicalGrid.factorialRunningMax
        (fun t ω => |X (min t (τ ω)) ω|) R r ω =
        (FactorialChronologicalGrid.stoppedGrid R r).natSample
          (fun t ω => |X (min t (τ ω)) ω|) k ω by
      exact hkEq]
    change ENNReal.ofReal
        |X (min ((FactorialChronologicalGrid.stoppedGrid R r).sampledTime k)
          (τ ω)) ω| ≤ _
    apply FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
      (fun t ω => |X t ω|) N hRightAbs ω
        (t := min ((FactorialChronologicalGrid.stoppedGrid R r).sampledTime k)
          (τ ω))
    exact (min_le_right _ _).trans (hτT ω) |>.trans hTN
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  change (min
      (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => |X (min t (τ ω)) ω|) R ω) 1).toReal ≤
    (min
      (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => |X t ω|) N ω) 1).toReal
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by finiteness)
      (min_le_right
        (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t ω => |X t ω|) N ω) 1))
  exact min_le_min hE le_rfl

theorem testValue_stopAt_le_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T R N : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (hTN : T ≤ N) :
    testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R ≤
      gauge μ S H K N := by
  let EStop := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ)) R
  let EOrig := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H K) N
  have hIntStop : Integrable EStop μ := by
    simpa only [EStop] using testEnvelope_integrable S hS J
      (H.stopAt τ hτ) (K.stopAt τ hτ) R
  have hIntOrig : Integrable EOrig μ := by
    simpa only [EOrig] using testEnvelope_integrable S hS J H K N
  have hPoint : ∀ ω, EStop ω ≤ EOrig ω := by
    intro ω
    change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S J (H.stopAt τ hτ) (K.stopAt τ hτ)) R ω ≤ _
    rw [testedDifference_stopAt]
    exact cappedFiniteHorizonAbsoluteEnvelope_stoppedAt_le
      (testedDifference S J H K) τ T R N
      (testedDifference_rightContinuous S hSRight J H K) hτT hTN ω
  have hValue :
      testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R =
        ∫ ω, EStop ω ∂μ := by
    simpa only [EStop] using testValue_eq_integral μ S J
      (H.stopAt τ hτ) (K.stopAt τ hτ) R
  calc
    testValue μ S J (H.stopAt τ hτ) (K.stopAt τ hτ) R =
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

theorem gauge_stopAt_le_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H K : PredictableElementaryStrategy ℱ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T R N : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (hTN : T ≤ N) :
    gauge μ S (H.stopAt τ hτ) (K.stopAt τ hτ) R ≤ gauge μ S H K N := by
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · exact gauge_nonnegative S hS H K N
  · exact testValue_stopAt_le_of_bounded S hS hSRight J H K τ hτ T R N hτT hTN

theorem isCauchy_stopAt_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    IsCauchy μ S (fun n => (H n).stopAt τ hτ) := by
  intro R
  let N : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
  have hUpper : Tendsto (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2) N)
      atTop (𝓝 0) := hH N
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds) hUpper
  · filter_upwards [] with p
    exact gauge_nonnegative S hS ((H p.1).stopAt τ hτ) ((H p.2).stopAt τ hτ) R
  · exact Filter.Eventually.of_forall fun p =>
      gauge_stopAt_le_of_bounded S hS hSRight (H p.1) (H p.2) τ hτ T R N
        hτT (by
          dsimp [N]
          exact ((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _))))

noncomputable def RealizedStrategy.stopAt
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n => (H.representative n).stopAt τ hτ
  representativeBound := fun n => 2 * H.representativeBound n
  representative_coefficientAbsSum_le := by
    intro n ω
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    exact mul_le_mul_of_nonneg_left
      (H.representative_coefficientAbsSum_le n ω) (by positivity)
  gain := MeasureTheory.stoppedProcess H.gain
    (fun ω => (τ ω : WithTop ℝ≥0))
  gain_stronglyAdapted := by
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      H.gain_stronglyAdapted hτ H.gain_rightContinuous
  gain_rightContinuous := by
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      H.gain H.gain_rightContinuous
  gain_hasLeftLimits := H.gain_hasLeftLimits.stoppedProcess
    (fun ω => (τ ω : WithTop ℝ≥0))
  gain_convergence := by
    intro r
    let N : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
    have hTN : T ≤ N := by
      dsimp [N]
      exact ((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _)))
    refine tendstoInMeasure_of_nonneg_le
      (f := fun n =>
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
            MeasureTheory.stoppedProcess H.gain
              (fun ω => (τ ω : WithTop ℝ≥0)) t ω)
          ((r + 1 : ℕ) : ℝ≥0))
      (g := fun n ω =>
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          N ω) ?_ ?_
    · intro n ω
      constructor
      · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
          _ _ _
      · have hDiff :
            (fun t ω => elementaryGain S ((H.representative n).stopAt τ hτ) t ω -
              MeasureTheory.stoppedProcess H.gain
                (fun ω => (τ ω : WithTop ℝ≥0)) t ω) =
              (fun t ω =>
                (fun s ω => elementaryGain S (H.representative n) s ω - H.gain s ω)
                  (min t (τ ω)) ω) := by
          funext t ω
          rw [elementaryGain_stopAt]
          simp only [MeasureTheory.stoppedProcess]
          rw [← WithTop.coe_min,
            WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
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
        exact cappedFiniteHorizonAbsoluteEnvelope_stoppedAt_le
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          τ T ((r + 1 : ℕ) : ℝ≥0) N hRightDiff hτT hTN ω
    · simpa only [N] using H.gain_convergence (Nat.ceil T)
  isCauchy := isCauchy_stopAt_of_bounded S hS hSRight H.representative H.isCauchy
    τ hτ T hτT

@[simp]
theorem RealizedStrategy.stopAt_gain
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (H.stopAt S hS hSRight τ hτ T hτT).gain =
      MeasureTheory.stoppedProcess H.gain
        (fun ω => (τ ω : WithTop ℝ≥0)) :=
  rfl

theorem RealizedStrategy.stopAt_gain_apply
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (T t : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    (H.stopAt S hS hSRight τ hτ T hτT).gain t ω =
      H.gain (min t (τ ω)) ω := by
  rw [RealizedStrategy.stopAt_gain, MeasureTheory.stoppedProcess]
  rw [← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

/-! ## Source linearity -/

theorem elementaryGain_smul_source
    (c : ℝ) (X : Process Ω) (J : PredictableElementaryStrategy ℱ) :
    elementaryGain (fun t ω => c * X t ω) J =
      (fun t ω => c * elementaryGain X J t ω) := by
  induction J with
  | nil =>
      funext t ω
      simp [elementaryGain, PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      change ElementaryInterval.gain
          (fun s ω' => c * X s ω') B.interval t ω +
          elementaryGain (fun s ω' => c * X s ω') J t ω =
        c * (ElementaryInterval.gain X B.interval t ω +
          elementaryGain X J t ω)
      have hB : ElementaryInterval.gain
          (fun s ω' => c * X s ω') B.interval t ω =
          c * ElementaryInterval.gain X B.interval t ω := by
        simp only [ElementaryInterval.gain]
        ring
      rw [hB, congrFun (congrFun ih t) ω]
      ring

end PredictableElementaryEmery

end FTAPTheorem42
