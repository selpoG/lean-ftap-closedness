/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.ElementaryIntegrand
import FTAPTheorem42.Foundations.ElementaryPredictable
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval

/-!
# Integrand processes of predictable elementary strategies

A predictable elementary block with coefficient `h`, starting time `τ`, and
stopping time `σ` represents the integrand `h 1_(τ,σ]`.  This module proves
that process predictable directly.  The proof uses the predictable lift of
an event known at `τ` and the predictable stochastic interval `(0,σ]`.
Finite sums then give the integrand of an elementary strategy.
-/

open MeasureTheory Set
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

namespace PredictableElementaryInterval

omit [MeasurableSpace Ω] in
/-- Membership in the predictable lift of an event known at a finite
stopping time. -/
theorem mem_stoppingTimeEventPredictableLift_iff
    (σ : Ω → ℝ≥0) (B : Set Ω) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ stoppingTimeEventPredictableLift σ B ↔
      σ ω < t ∧ ω ∈ B := by
  simp only [stoppingTimeEventPredictableLift, Set.mem_iUnion,
    Set.mem_prod, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hqt, hB, hσq⟩
    exact ⟨hσq.trans_lt hqt, hB⟩
  · rintro ⟨hσt, hB⟩
    obtain ⟨q, -, hσq, hqt⟩ :=
      (NNReal.lt_iff_exists_rat_btwn (σ ω) t).1 hσt
    exact ⟨q, hqt, hB, hσq.le⟩

/-- Membership in the active stochastic interval of one block. -/
private theorem mem_activeSet_iff
    (B : PredictableElementaryInterval ℱ) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈
        stoppingTimeEventPredictableLift B.interval.startTime Set.univ ∩
          stochasticIntervalIocZero B.interval.stopTime ↔
      B.interval.startTime ω < t ∧ t ≤ B.interval.stopTime ω := by
  rw [Set.mem_inter_iff,
    mem_stoppingTimeEventPredictableLift_univ_iff,
    mem_stochasticIntervalIocZero_iff]
  constructor
  · rintro ⟨hstart, -, hstop⟩
    exact ⟨hstart, hstop⟩
  · rintro ⟨hstart, hstop⟩
    exact ⟨hstart, bot_le.trans_lt hstart, hstop⟩

/-- A predictable elementary block represents a strongly predictable
integrand process. -/
theorem integrand_isStronglyPredictable
    (B : PredictableElementaryInterval ℱ) :
    IsStronglyPredictable ℱ B.integrand := by
  let active : Set (ℝ≥0 × Ω) :=
    stoppingTimeEventPredictableLift B.interval.startTime Set.univ ∩
      stochasticIntervalIocZero B.interval.stopTime
  have hStartUniv : MeasurableSet[ℱ.predictable]
      (stoppingTimeEventPredictableLift
        B.interval.startTime Set.univ) :=
    IsStoppingTime.measurableSet_stoppingTimeEventPredictableLift
      B.startStopping
      (MeasurableSet.univ :
        MeasurableSet[B.startStopping.measurableSpace] Set.univ)
  have hStop : MeasurableSet[ℱ.predictable]
      (stochasticIntervalIocZero B.interval.stopTime) :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero B.stopStopping
  have hActive : MeasurableSet[ℱ.predictable] active :=
    hStartUniv.inter hStop
  apply Measurable.stronglyMeasurable
  intro u hu
  have hCoefficient : MeasurableSet[B.startStopping.measurableSpace]
      (B.interval.coefficient ⁻¹' u) :=
    B.coefficient_measurable hu
  have hStartCoefficient : MeasurableSet[ℱ.predictable]
      (stoppingTimeEventPredictableLift B.interval.startTime
        (B.interval.coefficient ⁻¹' u)) :=
    IsStoppingTime.measurableSet_stoppingTimeEventPredictableLift
      B.startStopping hCoefficient
  have hOn : MeasurableSet[ℱ.predictable]
      (stoppingTimeEventPredictableLift B.interval.startTime
          (B.interval.coefficient ⁻¹' u) ∩
        stochasticIntervalIocZero B.interval.stopTime) :=
    hStartCoefficient.inter hStop
  by_cases hzero : (0 : ℝ) ∈ u
  · rw [show (Function.uncurry B.integrand) ⁻¹' u =
        (stoppingTimeEventPredictableLift B.interval.startTime
            (B.interval.coefficient ⁻¹' u) ∩
          stochasticIntervalIocZero B.interval.stopTime) ∪ activeᶜ by
      ext p
      change
        (if B.interval.startTime p.2 < p.1 ∧
            p.1 ≤ B.interval.stopTime p.2 then
          B.interval.coefficient p.2 else 0) ∈ u ↔
        p ∈ stoppingTimeEventPredictableLift B.interval.startTime
              (B.interval.coefficient ⁻¹' u) ∩
              stochasticIntervalIocZero B.interval.stopTime ∨
          p ∉ active
      rw [Set.mem_inter_iff,
        mem_stoppingTimeEventPredictableLift_iff,
        mem_stochasticIntervalIocZero_iff,
        show p ∈ active ↔
            B.interval.startTime p.2 < p.1 ∧
              p.1 ≤ B.interval.stopTime p.2 by
          exact B.mem_activeSet_iff p.1 p.2]
      by_cases hp : B.interval.startTime p.2 < p.1 ∧
          p.1 ≤ B.interval.stopTime p.2
      · have hpos : 0 < p.1 := bot_le.trans_lt hp.1
        simp [hp, hpos]
      · simp [hp, hzero]]
    exact hOn.union hActive.compl
  · rw [show (Function.uncurry B.integrand) ⁻¹' u =
        stoppingTimeEventPredictableLift B.interval.startTime
            (B.interval.coefficient ⁻¹' u) ∩
          stochasticIntervalIocZero B.interval.stopTime by
      ext p
      change
        (if B.interval.startTime p.2 < p.1 ∧
            p.1 ≤ B.interval.stopTime p.2 then
          B.interval.coefficient p.2 else 0) ∈ u ↔
        p ∈ stoppingTimeEventPredictableLift B.interval.startTime
              (B.interval.coefficient ⁻¹' u) ∩
              stochasticIntervalIocZero B.interval.stopTime
      rw [Set.mem_inter_iff,
        mem_stoppingTimeEventPredictableLift_iff,
        mem_stochasticIntervalIocZero_iff]
      by_cases hp : B.interval.startTime p.2 < p.1 ∧
          p.1 ≤ B.interval.stopTime p.2
      · have hpos : 0 < p.1 := bot_le.trans_lt hp.1
        simp [hp, hpos]
      · rw [ite_eq_right hp]
        constructor
        · intro hz
          exact (hzero hz).elim
        · rintro ⟨⟨hstart, -⟩, -, hstop⟩
          exact (hp ⟨hstart, hstop⟩).elim]
    exact hOn

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

/-- The integrand of a predictable elementary strategy is strongly
predictable. -/
theorem integrand_isStronglyPredictable
    (H : PredictableElementaryStrategy ℱ) :
    IsStronglyPredictable ℱ H.integrand := by
  induction H with
  | nil =>
      exact stronglyMeasurable_zero
  | cons B H ih =>
      change IsStronglyPredictable ℱ
        (B.integrand + PredictableElementaryStrategy.integrand H)
      exact B.integrand_isStronglyPredictable.add ih

/-- Positive scalar multiplication of an elementary strategy acts
pointwise on its predictable integrand. -/
@[simp]
theorem integrand_posSMul
    (c : ℝ) (hc : 0 < c)
    (H : PredictableElementaryStrategy ℱ) :
    (H.posSMul c hc).integrand = fun t omega => c * H.integrand t omega := by
  induction H with
  | nil =>
      funext t omega
      simp [integrand, PredictableElementaryStrategy.posSMul]
  | cons B H ih =>
      funext t omega
      change
        (B.posSMul c hc).integrand t omega +
            (PredictableElementaryStrategy.posSMul c hc H).integrand t omega =
          c * (B.integrand t omega +
            PredictableElementaryStrategy.integrand H t omega)
      rw [ih]
      simp only [PredictableElementaryInterval.integrand,
        PredictableElementaryInterval.posSMul_interval,
        ElementaryInterval.mulCoefficient]
      by_cases hactive :
          B.interval.startTime omega < t ∧ t ≤ B.interval.stopTime omega
      · simp [hactive]
        ring
      · simp [hactive]

end PredictableElementaryStrategy

end FTAPTheorem42
