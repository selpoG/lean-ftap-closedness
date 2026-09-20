/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Algebra

/-!
# Positive scalar multiplication on the realized elementary Emery carrier

The capped Emery gauge is stable under positive scalar multiplication with
the factor `max c 1`.  This module keeps that analytic estimate separate from
the basic zero and addition operations on the realized carrier.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## Positive scalar multiplication on elementary gains -/

private theorem elementaryInterval_gain_mul_posSMul_right
    (S : Process Ω) (B C : PredictableElementaryInterval ℱ)
    (c : ℝ) (hc : 0 < c) (t : ℝ≥0) (ω : Ω) :
    ElementaryInterval.gain S
        (B.mul (C.posSMul c hc)).interval t ω =
      c * ElementaryInterval.gain S (B.mul C).interval t ω := by
  simp [PredictableElementaryInterval.mul,
    PredictableElementaryInterval.posSMul,
    ElementaryInterval.gain, ElementaryInterval.mulCoefficient]
  ring

private theorem elementaryGain_mul_map_posSMul_right
    (S : Process Ω) (B : PredictableElementaryInterval ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) :
    ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (H.map fun C => B.mul (C.posSMul c hc))) =
      fun t ω => c * ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (H.map fun C => B.mul C)) t ω := by
  induction H with
  | nil =>
      funext t ω
      simp [PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons C H ih =>
      funext t ω
      change ElementaryInterval.gain S
          (B.mul (C.posSMul c hc)).interval t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (H.map fun C => B.mul (C.posSMul c hc))) t ω =
        c * (ElementaryInterval.gain S (B.mul C).interval t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (H.map fun C => B.mul C)) t ω)
      rw [elementaryInterval_gain_mul_posSMul_right,
        congrFun (congrFun ih t) ω]
      ring

private theorem elementaryGain_mul_posSMul_right
    (S : Process Ω) (J H : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) :
    ElementaryStrategy.gain S
      (PredictableElementaryStrategy.toElementary
        (PredictableElementaryStrategy.mul J (H.posSMul c hc))) =
      fun t ω => c * ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (PredictableElementaryStrategy.mul J H)) t ω := by
  induction J with
  | nil =>
      funext t ω
      simp [PredictableElementaryStrategy.mul,
        PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      unfold PredictableElementaryStrategy.mul
      simp only [List.flatMap_cons]
      simp only [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      have hTail : ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.flatMap (fun B => List.map B.mul
                (H.posSMul c hc)) J)) t ω =
          c * ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.flatMap (fun B => List.map B.mul H) J)) t ω := by
        simpa only [PredictableElementaryStrategy.mul] using
          congrFun (congrFun ih t) ω
      have hHead := elementaryGain_mul_map_posSMul_right S B H c hc
      have hHead' : ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul (H.posSMul c hc))) t ω =
          c * ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul H)) t ω := by
        simpa [PredictableElementaryStrategy.posSMul, Function.comp_def] using
          congrFun (congrFun hHead t) ω
      rw [hHead', hTail]
      ring

theorem elementaryGain_posSMul
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) :
    elementaryGain S (H.posSMul c hc) =
      fun t ω => c * elementaryGain S H t ω := by
  funext t ω
  simp only [elementaryGain, PredictableElementaryStrategy.toElementary_posSMul,
    ElementaryStrategy.gain_mulCoefficient]

theorem testedGain_posSMul
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) :
    testedGain S J (H.posSMul c hc) =
      fun t ω => c * testedGain S J H t ω := by
  exact elementaryGain_mul_posSMul_right S J.strategy H c hc

theorem testedDifference_posSMul
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) :
    testedDifference S J (H.posSMul c hc) (K.posSMul c hc) =
      fun t ω => c * testedDifference S J H K t ω := by
  unfold testedDifference
  rw [testedGain_posSMul, testedGain_posSMul]
  funext t ω
  ring

omit [MeasurableSpace Ω] in
private theorem finiteRunningMax_posSMul
    (a : ℝ) (ha : 0 ≤ a) (f : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) :
    finiteRunningMax (fun k ω => a * f k ω) n ω =
      a * finiteRunningMax f n ω := by
  let s := Finset.range (n + 1)
  have hs : s.Nonempty := Finset.nonempty_range_add_one
  have hmax : ∃ k ∈ s, finiteRunningMax f n ω = f k ω := by
    exact Finset.exists_mem_eq_sup' hs (fun k => f k ω)
  rcases hmax with ⟨k, hk, hkeq⟩
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro j hj
    rw [hkeq]
    have hle : f j ω ≤ finiteRunningMax f n ω := by
      change f j ω ≤ s.sup' hs (fun l => f l ω)
      exact Finset.le_sup' (fun l => f l ω) hj
    exact mul_le_mul_of_nonneg_left (hle.trans_eq hkeq) ha
  · rw [hkeq]
    change a * f k ω ≤ s.sup' hs (fun l => a * f l ω)
    exact Finset.le_sup' (fun l => a * f l ω) hk

omit [MeasurableSpace Ω] in
private theorem eFactorialRunningMaxEnvelope_posSMul
    (X : Process Ω) (a : ℝ) (ha : 0 ≤ a) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => a * abs (X t ω)) T ω =
      ENNReal.ofReal a *
        FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t ω => abs (X t ω)) T ω := by
  unfold FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro r
  unfold FactorialChronologicalGrid.factorialRunningMax
  have hMax := finiteRunningMax_posSMul a ha
    (fun k ω' => abs (X
      ((FactorialChronologicalGrid.stoppedGrid T r).sampledTime k) ω'))
    (r * r.factorial) ω
  have hMaxEq :
      finiteRunningMax
          ((FactorialChronologicalGrid.stoppedGrid T r).natSample
            (fun t ω => a * abs (X t ω)))
          (r * r.factorial) ω =
        a * finiteRunningMax
          ((FactorialChronologicalGrid.stoppedGrid T r).natSample
            (fun t ω => abs (X t ω)))
          (r * r.factorial) ω := by
    exact hMax
  rw [hMaxEq, ENNReal.ofReal_mul ha]

omit [MeasurableSpace Ω] in
/-- Positive scalar multiplication is controlled by the capped envelope with
the factor `max c 1`. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_posSMul_le
    (X : Process Ω) (c : ℝ) (hc : 0 < c) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => c * X t ω) T ω ≤
      max c 1 * FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        X T ω := by
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  simp only [abs_mul]
  rw [eFactorialRunningMaxEnvelope_posSMul X (abs c) (abs_nonneg c) T ω]
  simpa only [abs_of_pos hc] using
    (SemimartingaleQuasiNorm.cappedEnvelope_cap_scale (abs c) (abs_nonneg c)
      (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
        (fun t ω => abs (X t ω)) T ω))

theorem testValue_posSMul_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) (T : ℝ≥0) :
    testValue μ S J (H.posSMul c hc) (K.posSMul c hc) T ≤
      max c 1 * testValue μ S J H K T := by
  let E := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H K) T
  let Ec := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J (H.posSMul c hc) (K.posSMul c hc)) T
  have hIntE : Integrable E μ := by
    simpa only [E] using testEnvelope_integrable S hS J H K T
  have hIntEc : Integrable Ec μ := by
    simpa only [Ec] using testEnvelope_integrable S hS J
      (H.posSMul c hc) (K.posSMul c hc) T
  have hPoint : ∀ ω, Ec ω ≤ max c 1 * E ω := by
    intro ω
    change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S J (H.posSMul c hc) (K.posSMul c hc)) T ω ≤ _
    rw [testedDifference_posSMul]
    exact cappedFiniteHorizonAbsoluteEnvelope_posSMul_le
      (testedDifference S J H K) c hc T ω
  calc
    testValue μ S J (H.posSMul c hc) (K.posSMul c hc) T = ∫ ω, Ec ω ∂μ := by
      simpa only [Ec] using testValue_eq_integral μ S J
        (H.posSMul c hc) (K.posSMul c hc) T
    _ ≤ ∫ ω, max c 1 * E ω ∂μ := by
      apply integral_mono_ae hIntEc (hIntE.const_mul (max c 1))
      filter_upwards [] with ω
      exact hPoint ω
    _ = max c 1 * ∫ ω, E ω ∂μ :=
      MeasureTheory.integral_const_mul (max c 1) E
    _ = max c 1 * testValue μ S J H K T := by
      rw [← testValue_eq_integral μ S J H K T]

theorem gauge_posSMul_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H K : PredictableElementaryStrategy ℱ)
    (c : ℝ) (hc : 0 < c) (T : ℝ≥0) :
    gauge μ S (H.posSMul c hc) (K.posSMul c hc) T ≤
      max c 1 * gauge μ S H K T := by
  have hBound := gauge_bddAbove (μ := μ) (ℱ := ℱ) S hS H K T
  have hGauge : 0 ≤ gauge μ S H K T := gauge_nonnegative S hS H K T
  have hFactor : 0 ≤ max c 1 := le_trans (by positivity) (le_max_right c 1)
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · exact mul_nonneg hFactor hGauge
  · have hTest := testValue_posSMul_le
      (μ := μ) (ℱ := ℱ) S hS J H K c hc T
    have hBase : testValue μ S J H K T ≤ gauge μ S H K T := by
      exact le_csSup hBound (Set.mem_insert_of_mem 0 (Set.mem_range_self J))
    exact hTest.trans (mul_le_mul_of_nonneg_left hBase hFactor)

theorem isCauchy_posSMul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H)
    (c : ℝ) (hc : 0 < c) :
    IsCauchy μ S (fun n => (H n).posSMul c hc) := by
  intro T
  have hFactor : 0 ≤ max c 1 := le_trans (by positivity) (le_max_right c 1)
  have hUpper : Tendsto
      (fun p : ℕ × ℕ => max c 1 * gauge μ S (H p.1) (H p.2) T)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hH T).const_mul (max c 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds) hUpper
  · filter_upwards [] with p
    exact gauge_nonnegative S hS
      ((H p.1).posSMul c hc) ((H p.2).posSMul c hc) T
  · filter_upwards [] with p
    exact gauge_posSMul_le S hS (H p.1) (H p.2) c hc T

/-- The deterministic coefficient bound after positive scalar multiplication. -/
noncomputable def posSMulCoefficientBound
    (c : ℝ) (hc : 0 < c) (C : ℝ≥0) : ℝ≥0 :=
  ⟨c * (C : ℝ), mul_nonneg hc.le C.2⟩

theorem coefficientAbsSum_posSMul_le
    (c : ℝ) (hc : 0 < c)
    (H : PredictableElementaryStrategy ℱ) (C : ℝ≥0)
    (hH : ∀ ω, H.coefficientAbsSum ω ≤ C) :
    ∀ ω, (H.posSMul c hc).coefficientAbsSum ω ≤
      posSMulCoefficientBound c hc C := by
  intro ω
  rw [PredictableElementaryStrategy.coefficientAbsSum_posSMul]
  exact mul_le_mul_of_nonneg_left (hH ω) hc.le

/-! ## Positive scalar multiplication on realized gains -/

noncomputable def RealizedStrategy.posSMul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (c : ℝ) (hc : 0 < c) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n => (H.representative n).posSMul c hc
  representativeBound := fun n =>
    posSMulCoefficientBound c hc (H.representativeBound n)
  representative_coefficientAbsSum_le := by
    intro n ω
    exact coefficientAbsSum_posSMul_le c hc (H.representative n)
      (H.representativeBound n) (H.representative_coefficientAbsSum_le n) ω
  gain := fun t ω => c * H.gain t ω
  gain_stronglyAdapted := by
    intro t
    change StronglyMeasurable[ℱ t] (c • H.gain t)
    exact (H.gain_stronglyAdapted t).const_smul c
  gain_rightContinuous := by
    intro ω t
    exact (H.gain_rightContinuous ω t).const_mul c
  gain_hasLeftLimits := H.gain_hasLeftLimits.const_mul c
  gain_convergence := by
    intro r
    refine tendstoInMeasure_of_nonneg_le
      (f := fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S
            ((H.representative n).posSMul c hc) t ω - c * H.gain t ω)
        ((r + 1 : ℕ) : ℝ≥0))
      (g := fun n ω => max c 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          ((r + 1 : ℕ) : ℝ≥0) ω) ?_ ?_
    · intro n ω
      constructor
      · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
          _ _ _
      · have hDiff :
            (fun t ω => elementaryGain S
                ((H.representative n).posSMul c hc) t ω -
              c * H.gain t ω) =
              (fun t ω => c *
                (elementaryGain S (H.representative n) t ω - H.gain t ω)) := by
          funext t ω
          rw [elementaryGain_posSMul]
          ring
        simpa only [hDiff] using
          (cappedFiniteHorizonAbsoluteEnvelope_posSMul_le
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          c hc ((r + 1 : ℕ) : ℝ≥0) ω)
    · have hScaled := FTAPTheorem42.tendstoInMeasure_smul_const (max c 1)
        (H.gain_convergence r)
      simpa only [mul_zero] using hScaled
  isCauchy := isCauchy_posSMul S hS H.representative H.isCauchy c hc

end PredictableElementaryEmery

end FTAPTheorem42
