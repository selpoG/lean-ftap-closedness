/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Semimartingale
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Tail consumers for the realized Emery carrier

This file records two small consumers used by the direct closure argument.
The first turns the product-filter Cauchy statement into the correct two-sided
tail statement.  In particular, it does not claim that an arbitrary fixed
index is eventually close to the sequence: both indices have to be beyond the
same threshold.

The second consumer applies the elementary good-integrator property to a
sequence of uniformly vanishing predictable tests multiplied by one fixed
elementary representative.  The coefficient-sum bound is used only for this
fixed representative; no such bound is inferred for the varying test rows.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## The product-filter tail -/

/-- A product-filter Cauchy sequence is eventually small when both indices are
past one common threshold.  This is the form needed when the reference index
is selected from the tail; it deliberately does not quantify over arbitrary
fixed reference indices. -/
theorem RealizedStrategy.gauge_twoTail
    {μ : Measure Ω} {S : Process Ω}
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n k : ℕ, N₀ ≤ n → N₀ ≤ k →
      gauge μ S (H.representative n) (H.representative k) T < ε := by
  have hEvent : ∀ᶠ p : ℕ × ℕ in atTop,
      gauge μ S (H.representative p.1) (H.representative p.2) T < ε := by
    exact (tendsto_order.1 (H.isCauchy T)).2 ε hε
  rcases (Filter.eventually_atTop_prod_self' (α := ℕ)).1 hEvent with
    ⟨N₀, hN₀⟩
  exact ⟨N₀, fun n k hn hk => hN₀ n hn k hk⟩

end PredictableElementaryEmery

end FTAPTheorem42

namespace FTAPTheorem42.PredictableElementaryEmery

/-! ## Uniform elementary-test convergence to the stored gain -/

open Filter MeasureTheory Set Topology
open scoped NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Process Ω}

private noncomputable def errorEnvelope
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : NNReal) (n : Nat)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) : Ω → Real :=
  FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    (fun t omega => testedGain S J (H.representative n) t omega -
      elementaryGain H.gain J.strategy t omega) T

omit [IsProbabilityMeasure μ] in
private theorem errorEnvelope_measurable
    (hS : IsStronglyProgressive ℱ S) (H : RealizedStrategy (ℱ := ℱ) μ S)
    (T : NNReal) (n : Nat) (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) :
    StronglyMeasurable (errorEnvelope H T n J) := by
  have hGain := PredictableElementaryStrategy.stronglyAdapted_gain H.gain
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      H.gain_stronglyAdapted H.gain_rightContinuous) J.strategy
  exact (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
    ((testedGain_stronglyAdapted S hS J (H.representative n)).sub hGain) T).mono (ℱ.le T)

omit [IsProbabilityMeasure μ] in
private theorem errorEnvelope_norm_le
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : NNReal) (n : Nat)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) (omega : Ω) :
    ‖errorEnvelope H T n J omega‖ ≤ 1 := by
  unfold errorEnvelope
  rw [Real.norm_eq_abs, abs_of_nonneg
    (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)]
  exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _

private theorem errorEnvelope_integrable
    (hS : IsStronglyProgressive ℱ S) (H : RealizedStrategy (ℱ := ℱ) μ S)
    (T : NNReal) (n : Nat) (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) :
    Integrable (errorEnvelope H T n J) μ :=
  (integrable_const (1 : Real)).mono' (errorEnvelope_measurable hS H T n J).aestronglyMeasurable
    (Eventually.of_forall (errorEnvelope_norm_le H T n J))

/-- The tail is chosen before the test. The Cauchy estimate is uniform in
the test, while the vanishing auxiliary subsequence may depend on it. -/
theorem RealizedStrategy.uniform_test_error_tail
    (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : NNReal) {ε : Real} (hε : 0 < ε) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ,
      (∫ omega, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t omega => testedGain S J (H.representative n) t omega -
          elementaryGain H.gain J.strategy t omega) T omega ∂μ) ≤ ε := by
  obtain ⟨N, hN⟩ := H.gauge_twoTail T hε
  refine ⟨N, ?_⟩
  intro n hn J
  have hConv := H.transformed_gain_error_convergence_at_horizon S hSRight
    J.strategy 1 zero_le_one J.abs_integrand_le_one T
  obtain ⟨f, hf, hAE⟩ := hConv.exists_seq_tendsto_ae
  have hInt : Tendsto (fun k => ∫ omega, errorEnvelope H T (f k) J omega ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : Real))
      (fun k => (errorEnvelope_measurable hS H T (f k) J).aestronglyMeasurable)
      (integrable_const 1)
      (fun k => Eventually.of_forall (errorEnvelope_norm_le H T (f k) J)) hAE
    simpa only [integral_zero] using h
  have hBound : ∀ᶠ k in atTop,
      (∫ omega, errorEnvelope H T n J omega ∂μ) ≤
        ε + ∫ omega, errorEnvelope H T (f k) J omega ∂μ := by
    filter_upwards [hf.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
    have hPoint : ∀ omega, errorEnvelope H T n J omega ≤
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J (H.representative (f k)) (H.representative n)) T omega +
            errorEnvelope H T (f k) J omega := fun omega =>
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
        (testedGain S J (H.representative n)) (elementaryGain H.gain J.strategy)
        (testedGain S J (H.representative (f k))) T omega
    have hIneq := integral_mono_ae (errorEnvelope_integrable hS H T n J)
      ((testEnvelope_integrable S hS J (H.representative (f k)) (H.representative n) T).add
        (errorEnvelope_integrable hS H T (f k) J)) (Eventually.of_forall hPoint)
    simp only [Pi.add_apply] at hIneq
    rw [integral_add
      (testEnvelope_integrable S hS J (H.representative (f k)) (H.representative n) T)
      (errorEnvelope_integrable hS H T (f k) J), ← testValue_eq_integral] at hIneq
    have hTest : testValue μ S J (H.representative (f k)) (H.representative n) T ≤
        gauge μ S (H.representative (f k)) (H.representative n) T :=
      le_csSup (gauge_bddAbove S hS _ _ T) (Set.mem_insert_of_mem _ ⟨J, rfl⟩)
    exact hIneq.trans (add_le_add (hTest.trans (hN _ _ hk hn).le) le_rfl)
  simpa only [add_zero, errorEnvelope] using ge_of_tendsto (tendsto_const_nhds.add hInt) hBound

end FTAPTheorem42.PredictableElementaryEmery
