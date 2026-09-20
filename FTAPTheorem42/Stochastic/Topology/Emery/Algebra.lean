/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Realization

/-!
# Addition in the realized elementary Emery carrier

This module supplies the first algebraic operations on the realized carrier.
The representative of a sum is the pointwise list sum, while the gain is the
pointwise sum of the two limiting gain processes.  The only estimates used
below are the finite-sum gain identities and the triangle inequality for the
capped factorial envelope; no terminal value is added to the carrier.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## Finite elementary gain identities -/

theorem elementaryGain_append
    (S : Process Ω) (H K : PredictableElementaryStrategy ℱ) :
    elementaryGain S (H ++ K) =
      fun t ω => elementaryGain S H t ω + elementaryGain S K t ω := by
  funext t ω
  simp only [elementaryGain, PredictableElementaryStrategy.toElementary_append,
    ElementaryStrategy.gain_append]

/-! The product test is distributed at the level of its finite gain sum. -/

private theorem elementaryGain_mul_map_append
    (S : Process Ω)
    (B : PredictableElementaryInterval ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (List.map B.mul (H ++ K))) =
      fun t ω =>
        ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary (List.map B.mul H)) t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary (List.map B.mul K)) t ω := by
  induction H with
  | nil =>
      funext t ω
      simp [PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons C H ih =>
      funext t ω
      change ElementaryStrategy.gain S
          (PredictableElementaryStrategy.toElementary
            (B.mul C :: List.map B.mul (H ++ K))) t ω =
        ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (B.mul C :: List.map B.mul H)) t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul K)) t ω
      have hTail : ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul (H ++ K))) t ω =
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul H)) t ω +
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.map B.mul K)) t ω := by
        exact congrFun (congrFun ih t) ω
      rw [show ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (B.mul C :: List.map B.mul (H ++ K))) t ω =
          ElementaryInterval.gain S (B.mul C).interval t ω +
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.map B.mul (H ++ K))) t ω by rfl]
      rw [show ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (B.mul C :: List.map B.mul H)) t ω =
          ElementaryInterval.gain S (B.mul C).interval t ω +
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.map B.mul H)) t ω by rfl]
      rw [hTail]
      ring

theorem elementaryGain_mul_append
    (S : Process Ω)
    (J H K : PredictableElementaryStrategy ℱ) :
    elementaryGain S (J.mul (H ++ K)) =
      fun t ω => elementaryGain S (J.mul H) t ω +
        elementaryGain S (J.mul K) t ω := by
  induction J with
  | nil =>
      funext t ω
      simp [PredictableElementaryStrategy.mul, elementaryGain,
        PredictableElementaryStrategy.toElementary, ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      unfold PredictableElementaryStrategy.mul elementaryGain
      change ElementaryStrategy.gain S
          (PredictableElementaryStrategy.toElementary
            (List.map B.mul (H ++ K) ++
              List.flatMap (fun B => List.map B.mul (H ++ K)) J)) t ω =
        ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul H ++
                List.flatMap (fun B => List.map B.mul H) J)) t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.map B.mul K ++
                List.flatMap (fun B => List.map B.mul K) J)) t ω
      rw [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append,
        PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append,
        PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      have hHead := elementaryGain_mul_map_append S B H K
      have hTail := congrFun (congrFun ih t) ω
      have hTail' : ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.flatMap (fun B => List.map B.mul (H ++ K)) J)) t ω =
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (List.flatMap (fun B => List.map B.mul H) J)) t ω +
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.flatMap (fun B => List.map B.mul K) J)) t ω := by
        simpa only [PredictableElementaryStrategy.mul, elementaryGain] using hTail
      rw [hHead, hTail']
      ring

theorem testedGain_append
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    testedGain S J (H ++ K) =
      fun t ω => testedGain S J H t ω + testedGain S J K t ω := by
  simpa only [testedGain, elementaryGain] using
    (elementaryGain_mul_append S J.strategy H K)

theorem cappedFiniteHorizonAbsoluteEnvelope_testedDifference_append_le_add
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H H' K K' : PredictableElementaryStrategy ℱ) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S J (H ++ K) (H' ++ K')) T ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S J H H') T ω +
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J K K') T ω := by
  have hBase :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (testedGain S J (H ++ K))
      (testedGain S J (H' ++ K'))
      (testedGain S J (H ++ K')) T ω
  have hLeft :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => testedGain S J (H ++ K) t ω -
            testedGain S J (H' ++ K') t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J (H ++ K) (H' ++ K')) T ω := by
    rfl
  have hFirst :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => testedGain S J (H ++ K') t ω -
            testedGain S J (H ++ K) t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J K K') T ω := by
    have hDiff :
        (fun t ω => testedGain S J (H ++ K') t ω -
          testedGain S J (H ++ K) t ω) =
          (fun t ω => -testedDifference S J K K' t ω) := by
      funext t ω
      rw [testedGain_append, testedGain_append]
      dsimp [testedDifference]
      ring
    rw [hDiff]
    exact cappedFiniteHorizonAbsoluteEnvelope_neg
      (testedDifference S J K K') T ω
  have hSecond :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => testedGain S J (H ++ K') t ω -
            testedGain S J (H' ++ K') t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J H H') T ω := by
    have hDiff :
        (fun t ω => testedGain S J (H ++ K') t ω -
          testedGain S J (H' ++ K') t ω) =
          testedDifference S J H H' := by
      funext t ω
      rw [testedGain_append, testedGain_append]
      dsimp [testedDifference]
      ring
    rw [hDiff]
  rw [hLeft, hFirst, hSecond] at hBase
  simpa only [add_comm] using hBase

theorem testValue_append_append_le_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H H' K K' : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S J (H ++ K) (H' ++ K') T ≤
      testValue μ S J H H' T + testValue μ S J K K' T := by
  let E := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J (H ++ K) (H' ++ K')) T
  let EH := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H H') T
  let EK := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J K K') T
  have hIntE : Integrable E μ := by
    simpa only [E] using testEnvelope_integrable S hS J (H ++ K) (H' ++ K') T
  have hIntEH : Integrable EH μ := by
    simpa only [EH] using testEnvelope_integrable S hS J H H' T
  have hIntEK : Integrable EK μ := by
    simpa only [EK] using testEnvelope_integrable S hS J K K' T
  have hPoint : ∀ ω, E ω ≤ EH ω + EK ω := by
    intro ω
    simpa only [E, EH, EK] using
      cappedFiniteHorizonAbsoluteEnvelope_testedDifference_append_le_add
        S J H H' K K' T ω
  calc
    testValue μ S J (H ++ K) (H' ++ K') T = ∫ ω, E ω ∂μ :=
      testValue_eq_integral μ S J (H ++ K) (H' ++ K') T
    _ ≤ ∫ ω, (EH ω + EK ω) ∂μ := by
      apply integral_mono_ae hIntE (hIntEH.add hIntEK)
      filter_upwards [] with ω
      exact hPoint ω
    _ = (∫ ω, EH ω ∂μ) + ∫ ω, EK ω ∂μ :=
      integral_add hIntEH hIntEK
    _ = testValue μ S J H H' T + testValue μ S J K K' T := by
      rw [testValue_eq_integral, testValue_eq_integral]

theorem gauge_append_append_le_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H H' K K' : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    gauge μ S (H ++ K) (H' ++ K') T ≤
      gauge μ S H H' T + gauge μ S K K' T := by
  let A := gauge μ S H H' T
  let B := gauge μ S K K' T
  have hA : 0 ≤ A := gauge_nonnegative S hS H H' T
  have hB : 0 ≤ B := gauge_nonnegative S hS K K' T
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · exact hAB
  · have hTest := testValue_append_append_le_add
      (μ := μ) (ℱ := ℱ) S hS J H H' K K' T
    have hHH' : testValue μ S J H H' T ≤ A := by
      exact le_csSup (gauge_bddAbove S hS H H' T)
        (Set.mem_insert_of_mem 0 (Set.mem_range_self J))
    have hKK' : testValue μ S J K K' T ≤ B := by
      exact le_csSup (gauge_bddAbove S hS K K' T)
        (Set.mem_insert_of_mem 0 (Set.mem_range_self J))
    exact hTest.trans (add_le_add hHH' hKK')

private theorem cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_append_sub_add_le
    (S : Process Ω)
    (H K : PredictableElementaryStrategy ℱ)
    (X Y : Process Ω) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (H ++ K) t ω -
          (X t ω + Y t ω)) T ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S H t ω - X t ω) T ω +
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S K t ω - Y t ω) T ω := by
  have hBase :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (fun t ω => elementaryGain S (H ++ K) t ω)
      (fun t ω => X t ω + Y t ω)
      (fun t ω => elementaryGain S H t ω + Y t ω) T ω
  have hLeft :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H ++ K) t ω -
            (X t ω + Y t ω)) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H ++ K) t ω -
            (X t ω + Y t ω)) T ω := by
    rfl
  have hFirst :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S H t ω + Y t ω -
            elementaryGain S (H ++ K) t ω) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S K t ω - Y t ω) T ω := by
    have hDiff :
        (fun t ω => elementaryGain S H t ω + Y t ω -
          elementaryGain S (H ++ K) t ω) =
          (fun t ω => -(elementaryGain S K t ω - Y t ω)) := by
      funext t ω
      rw [elementaryGain_append]
      ring
    rw [hDiff]
    exact cappedFiniteHorizonAbsoluteEnvelope_neg
      (fun t ω => elementaryGain S K t ω - Y t ω) T ω
  have hSecond :
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S H t ω + Y t ω -
            (X t ω + Y t ω)) T ω =
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S H t ω - X t ω) T ω := by
    have hDiff :
        (fun t ω => elementaryGain S H t ω + Y t ω -
          (X t ω + Y t ω)) =
          (fun t ω => elementaryGain S H t ω - X t ω) := by
      funext t ω
      ring
    rw [hDiff]
  rw [hLeft, hFirst, hSecond] at hBase
  simpa only [add_comm] using hBase

theorem isCauchy_append
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H K : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H) (hK : IsCauchy μ S K) :
    IsCauchy μ S (fun n => H n ++ K n) := by
  intro T
  have hSum : Tendsto
      (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2) T +
        gauge μ S (K p.1) (K p.2) T)
      atTop (𝓝 0) := by
    simpa only [add_zero] using (hH T).add (hK T)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds) hSum
  · filter_upwards [] with p
    exact gauge_nonnegative S hS
      (H p.1 ++ K p.1) (H p.2 ++ K p.2) T
  · filter_upwards [] with p
    exact gauge_append_append_le_add S hS
      (H p.1) (H p.2) (K p.1) (K p.2) T

private theorem gain_convergence_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (H K : RealizedStrategy (ℱ := ℱ) μ S)
    (r : ℕ) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S
            (H.representative n ++ K.representative n) t ω -
          (H.gain t ω + K.gain t ω))
        ((r + 1 : ℕ) : ℝ≥0))
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_nonneg_le_add
  · intro n ω
    exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
      _ _ _
  · intro n ω
    exact cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_append_sub_add_le
      S (H.representative n) (K.representative n) H.gain K.gain
      ((r + 1 : ℕ) : ℝ≥0) ω
  · exact H.gain_convergence r
  · exact K.gain_convergence r

/-- The empty elementary sequence is the canonical zero in the realized
carrier.  It is constructed directly with the zero gain process, so it needs
no càdlàg or left-limit hypothesis on the source and introduces no terminal
witness. -/
noncomputable def RealizedStrategy.zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S) :
    RealizedStrategy (ℱ := ℱ) μ S :=
  { representative := fun _ => []
    representativeBound := fun _ => 0
    representative_coefficientAbsSum_le := by
      intro n ω
      simp [PredictableElementaryStrategy.coefficientAbsSum]
    gain := fun _ _ => 0
    gain_stronglyAdapted := by
      intro t
      exact stronglyMeasurable_const
    gain_rightContinuous := by
      intro ω t
      exact continuousWithinAt_const
    gain_hasLeftLimits := by
      intro ω t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : ℝ≥0 => (0 : ℝ)) (a := t)
        ⟨0, tendsto_const_nhds⟩
    gain_convergence := by
      intro r
      have hDiff :
          (fun t ω => elementaryGain S
              ([] : PredictableElementaryStrategy ℱ) t ω - 0) =
            (fun _ _ => (0 : ℝ)) := by
        funext t ω
        simp [elementaryGain, PredictableElementaryStrategy.toElementary,
          ElementaryStrategy.gain]
      rw [hDiff]
      convert tendstoInMeasure_const μ (fun _ : Ω => (0 : ℝ)) using 1
      funext n ω
      exact cappedFiniteHorizonAbsoluteEnvelope_zero
        ((r + 1 : ℕ) : ℝ≥0) ω
    isCauchy := PredictableElementaryEmery.constant_isCauchy S hS [] }

/-! ## The realized sum -/

noncomputable def RealizedStrategy.add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H K : RealizedStrategy (ℱ := ℱ) μ S) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n => H.representative n ++ K.representative n
  representativeBound := fun n => H.representativeBound n + K.representativeBound n
  representative_coefficientAbsSum_le := by
    intro n ω
    rw [PredictableElementaryStrategy.coefficientAbsSum_append]
    calc
      (H.representative n).coefficientAbsSum ω +
          (K.representative n).coefficientAbsSum ω ≤
          (H.representativeBound n : ℝ) +
            (K.representativeBound n : ℝ) :=
        add_le_add (H.representative_coefficientAbsSum_le n ω)
          (K.representative_coefficientAbsSum_le n ω)
      _ = ((H.representativeBound n + K.representativeBound n : ℝ≥0) : ℝ) := by
        norm_num
  gain := fun t ω => H.gain t ω + K.gain t ω
  gain_stronglyAdapted := by
    intro t
    exact (H.gain_stronglyAdapted t).add (K.gain_stronglyAdapted t)
  gain_rightContinuous := by
    intro ω t
    exact (H.gain_rightContinuous ω t).add (K.gain_rightContinuous ω t)
  gain_hasLeftLimits := H.gain_hasLeftLimits.add K.gain_hasLeftLimits
  gain_convergence := by
    intro r
    exact gain_convergence_add S H K r
  isCauchy := isCauchy_append S hS H.representative K.representative
    H.isCauchy K.isCauchy

end PredictableElementaryEmery

end FTAPTheorem42
