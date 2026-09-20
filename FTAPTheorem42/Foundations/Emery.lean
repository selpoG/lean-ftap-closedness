/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Envelope
import FTAPTheorem42.Foundations.ElementaryIntegrand
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Emery shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A predictable elementary multiplier admissible as an Emery test. -/
structure BoundedPredictableElementaryMultiplier
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) where
  strategy : PredictableElementaryStrategy ℱ
  abs_integrand_le_one : ∀ t ω, |strategy.integrand t ω| ≤ 1

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def elementaryEmeryTestError (X Y : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) : Ω → Real :=
  FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (fun t w => ElementaryStrategy.gain X J.strategy.toElementary t w -
      ElementaryStrategy.gain Y J.strategy.toElementary t w) T

theorem elementaryEmeryTestError_measurable {X Y : Process Ω}
    (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    StronglyMeasurable (elementaryEmeryTestError X Y J T) :=
  (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
    ((PredictableElementaryStrategy.stronglyAdapted_gain _ hX J.strategy).sub
      (PredictableElementaryStrategy.stronglyAdapted_gain _ hY J.strategy)) T).mono (F.le T)

theorem elementaryEmeryTestError_bounds (X Y : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) (w : Ω) :
    0 ≤ elementaryEmeryTestError X Y J T w ∧ elementaryEmeryTestError X Y J T w ≤ 1 :=
  ⟨FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _,
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _⟩

theorem elementaryEmeryTestError_integrable {X Y : Process Ω}
    (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    Integrable (elementaryEmeryTestError X Y J T) μ :=
  (integrable_const (1 : Real)).mono'
    (elementaryEmeryTestError_measurable hX hY J T).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (elementaryEmeryTestError_bounds X Y J T w).1]
      exact (elementaryEmeryTestError_bounds X Y J T w).2)

/-- The test may be chosen only after the common two-tail threshold. -/
def ElementaryEmeryCauchy (μ : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (X : Nat → Process Ω) : Prop :=
  ∀ T : NNReal, ∀ ε > (0 : Real), ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      ∫ w, elementaryEmeryTestError (X m) (X n) J T w ∂μ ≤ ε

/-- Uniform convergence under unit-bounded predictable elementary tests.
The relation imposes no martingale/FV decomposition on any process. Tests
only see increments; zero initial values must be required separately when
using this relation to construct an integral graph or a separated topology. -/
def ElementaryEmeryConverges (μ : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : Nat → Process Ω) (Y : Process Ω) : Prop :=
  ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => ElementaryStrategy.gain (X n) J.strategy.toElementary t w -
          ElementaryStrategy.gain Y J.strategy.toElementary t w) T w ∂μ) ≤ ε

/-- Markov's inequality converts the common expected-error cutoff into a
probability cutoff, still chosen before the elementary test. -/
theorem ElementaryEmeryCauchy.uniform_probability
    {Y : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F Y)
    (hY : ∀ n, IsStronglyProgressive F (Y n)) :
    ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∀ J : BoundedPredictableElementaryMultiplier F,
        μ.real {ω | ε < elementaryEmeryTestError (Y m) (Y n) J T ω} ≤ ε := by
  intro T ε hε
  obtain ⟨N, hN⟩ := h T (ε * ε) (mul_pos hε hε)
  refine ⟨N, fun m hm n hn J => ?_⟩
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun ω =>
      (elementaryEmeryTestError_bounds (Y m) (Y n) J T ω).1)
    (elementaryEmeryTestError_integrable (hY m) (hY n) J T) ε
  have hTail : μ.real {ω | ε < elementaryEmeryTestError (Y m) (Y n) J T ω} ≤
      μ.real {ω | ε ≤ elementaryEmeryTestError (Y m) (Y n) J T ω} :=
    measureReal_mono (by
      intro ω hω
      change ε ≤ elementaryEmeryTestError (Y m) (Y n) J T ω
      exact le_of_lt hω)
  have hBound := hMarkov.trans (hN m hm n hn J)
  nlinarith

/-- Equality up to one horizon suffices for every elementary test, without
any assumption about the processes after that horizon. -/
theorem elementaryEmeryTestError_congr_upto
    {X X' Y Y' : Process Ω}
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) (ω : Ω)
    (hX : ∀ t, t ≤ T → X t ω = X' t ω)
    (hY : ∀ t, t ≤ T → Y t ω = Y' t ω) :
    elementaryEmeryTestError X Y J T ω = elementaryEmeryTestError X' Y' J T ω := by
  unfold elementaryEmeryTestError FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  congr 2
  apply iSup_congr
  intro r
  congr 1
  unfold FactorialChronologicalGrid.factorialRunningMax
  apply Finset.sup'_congr
  · rfl
  · intro k hk
    simp only [ChronologicalGrid.natSample]
    have ht : (FactorialChronologicalGrid.stoppedGrid T r).sampledTime k ≤ T := min_le_right _ _
    rw [J.strategy.toElementary.gain_congr_price_upto _ ω (fun t ht' => hX t (ht'.trans ht)),
      J.strategy.toElementary.gain_congr_price_upto _ ω (fun t ht' => hY t (ht'.trans ht))]

end FTAPTheorem42
