/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness
import FTAPTheorem42.Foundations.ElementaryPredictableProcess
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.PredictableIndicatorRing
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Stochastic.Topology.Emery.TruncatedExpectation
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# A finite-horizon Emery gauge for predictable elementary strategies

This file fixes the first boundary of the realized Emery completion.  The
test family consists of predictable elementary multipliers whose summed
integrand is bounded in absolute value by one.  The gauge is formed from the
measurable capped factorial-grid envelope of the difference of the two tested
elementary gains.  In particular, no terminal value, decomposition, or raw
integrand is stored in the completion relation.

The binary formulation below is intentional.  It makes the metric laws
independent of an unproved distributivity theorem for the blockwise product:
the tested process for `(H,K)` is the difference of the two tested gains.
Once elementary stochastic-integral linearity is available, this agrees with
the usual notation `(J (H-K)) · S`.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace BoundedPredictableElementaryMultiplier

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The deterministic unit test on a finite positive horizon. -/
noncomputable def horizonUnit (T : ℝ≥0) :
    BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ where
  strategy :=
    [FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.horizonBlock T]
  abs_integrand_le_one := by
    intro t ω
    simp only [PredictableElementaryStrategy.integrand, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      PredictableElementaryInterval.integrand,
      FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.horizonBlock]
    split_ifs <;> simp

end BoundedPredictableElementaryMultiplier

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The gain obtained by testing an elementary strategy with `J`. -/
noncomputable def testedGain
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) : Process Ω :=
  ElementaryStrategy.gain S
    (PredictableElementaryStrategy.toElementary (J.strategy.mul H))

/-- The process tested in the binary Emery gauge. -/
noncomputable def testedDifference
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) : Process Ω :=
  fun t ω => testedGain S J H t ω - testedGain S J K t ω

theorem testedDifference_rightContinuous
    (S : Process Ω)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    ∀ ω t, ContinuousWithinAt
      (testedDifference S J H K · ω) (Set.Ici t) t := by
  intro ω t
  exact
    (PredictableElementaryStrategy.rightContinuous_gain S hSRight
      (J.strategy.mul H) ω t).sub
      (PredictableElementaryStrategy.rightContinuous_gain S hSRight
        (J.strategy.mul K) ω t)

/-- A test value: the expectation of the measurable capped factorial-grid
envelope of a tested gain difference. -/
noncomputable def testValue
    (μ : Measure Ω) (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) : ℝ :=
  SemimartingaleQuasiNorm.truncatedExpectation μ
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S J H K) T)

/-- The finite-horizon binary Emery gauge. -/
noncomputable def gauge
    (μ : Measure Ω) (S : Process Ω)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) : ℝ :=
  sSup (insert 0 (Set.range fun J => testValue μ S J H K T))

/-- Emery--Cauchy sequences for all finite horizons. -/
def IsCauchy
    (μ : Measure Ω) (S : Process Ω)
    (H : ℕ → PredictableElementaryStrategy ℱ) : Prop :=
  ∀ T : ℝ≥0,
    Tendsto (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2) T)
      atTop (𝓝 0)

theorem testedGain_stronglyAdapted
    (S : Process Ω)
    (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) :
    StronglyAdapted ℱ (testedGain S J H) := by
  exact PredictableElementaryStrategy.stronglyAdapted_gain S hS
    (J.strategy.mul H)

theorem testedDifference_stronglyAdapted
    (S : Process Ω)
    (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    StronglyAdapted ℱ (testedDifference S J H K) := by
  exact (testedGain_stronglyAdapted S hS J H).sub
    (testedGain_stronglyAdapted S hS J K)

theorem testEnvelope_stronglyMeasurable
    (S : Process Ω)
    (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    StronglyMeasurable
      (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S J H K) T) := by
  exact (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference_stronglyAdapted S hS J H K) T).mono (ℱ.le T)

theorem testValue_nonnegative
    (μ : Measure Ω) (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    0 ≤ testValue μ S J H K T := by
  exact SemimartingaleQuasiNorm.truncatedExpectation_nonnegative

theorem testValue_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S J H K T ≤ 1 := by
  exact SemimartingaleQuasiNorm.truncatedExpectation_le_one
    (testEnvelope_stronglyMeasurable S hS J H K T)

theorem gauge_bddAbove
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    BddAbove (insert 0 (Set.range fun J => testValue μ S J H K T)) := by
  refine ⟨1, ?_⟩
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨J, rfl⟩
  · norm_num
  · exact testValue_le_one S hS J H K T

theorem gauge_nonnegative
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    0 ≤ gauge μ S H K T := by
  unfold gauge
  apply le_csSup (gauge_bddAbove S hS H K T)
  exact Set.mem_insert 0 (Set.range fun J => testValue μ S J H K T)

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_neg
    (X : Process Ω) (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => -X t ω) T ω =
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω := by
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  simp only [abs_neg]

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_zero
    (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun _ _ => (0 : ℝ)) T ω = 0 := by
  simp [FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope,
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope,
    FactorialChronologicalGrid.factorialRunningMax,
    finiteRunningMax, ChronologicalGrid.natSample]

theorem testEnvelope_integrable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    Integrable
      (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S J H K) T) μ := by
  let E := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (testedDifference S J H K) T
  have hE : StronglyMeasurable E :=
    testEnvelope_stronglyMeasurable S hS J H K T
  apply Integrable.of_bound hE.aestronglyMeasurable 1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
      (testedDifference S J H K) T ω)]
  exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
    (testedDifference S J H K) T ω

theorem testValue_eq_integral
    (μ : Measure Ω) (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S J H K T =
      ∫ ω,
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J H K) T ω ∂μ := by
  unfold testValue SemimartingaleQuasiNorm.truncatedExpectation
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [abs_of_nonneg
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
      (testedDifference S J H K) T ω)]
  exact min_eq_left
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
      (testedDifference S J H K) T ω)

theorem testValue_self
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S J H H T = 0 := by
  unfold testValue SemimartingaleQuasiNorm.truncatedExpectation
  have hzero :
      (fun ω => min
          |FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
            (testedDifference S J H H) T ω| 1) =ᵐ[μ] 0 := by
    filter_upwards [] with ω
    have hDiff : testedDifference S J H H = (fun _ _ => (0 : ℝ)) := by
      funext t ω
      simp [testedDifference]
    rw [hDiff, cappedFiniteHorizonAbsoluteEnvelope_zero]
    simp
  rw [integral_congr_ae hzero]
  simp

theorem gauge_self
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    gauge μ S H H T = 0 := by
  unfold gauge
  apply le_antisymm
  · apply csSup_le (Set.insert_nonempty 0 _)
    intro b hb
    rcases Set.mem_insert_iff.mp hb with hb | ⟨J, rfl⟩
    · simp [hb]
    · change testValue μ S J H H T ≤ 0
      rw [testValue_self]
  · apply le_csSup (gauge_bddAbove S hS H H T)
    exact Set.mem_insert 0 (Set.range fun J => testValue μ S J H H T)

theorem constant_isCauchy
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : PredictableElementaryStrategy ℱ) :
    IsCauchy μ S (fun _ : ℕ => H) := by
  intro T
  have hzero :
      (fun p : ℕ × ℕ => gauge μ S H H T) =
        (fun _ => (0 : ℝ)) := by
    funext p
    exact gauge_self S hS H T
  rw [hzero]
  exact tendsto_const_nhds

end PredictableElementaryEmery

end FTAPTheorem42

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

omit [MeasurableSpace Omega] in
theorem cappedFiniteHorizonAbsoluteEnvelope_add_le
    (U V : Process Omega) (T : NNReal) (omega : Omega) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t omega => U t omega + V t omega) T omega ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope U T omega +
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope V T omega := by
  have h := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
    (fun t omega => U t omega + V t omega) (fun _ _ => (0 : Real)) U T omega
  have hFirst : (fun t omega =>
      (U t omega + V t omega) - 0) = (fun t omega => U t omega + V t omega) := by
    funext t omega
    ring
  have hSecond : (fun t omega => U t omega -
      (U t omega + V t omega)) = (fun t omega => -V t omega) := by
    funext t omega
    ring
  rw [hFirst, hSecond] at h
  rw [PredictableElementaryEmery.cappedFiniteHorizonAbsoluteEnvelope_neg] at h
  simpa only [sub_zero, add_comm] using h

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
