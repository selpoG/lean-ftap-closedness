/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.UniformTestLimit
import FTAPTheorem42.Stochastic.Topology.Emery.MeasureTransfer

/-!
# A fixed-time consumer for the direct Emery triangle

The binary Emery gauge controls the capped finite-horizon envelope of every
unit-bounded predictable elementary test.  This file turns convergence of the
corresponding test values into convergence in measure of one fixed-time
tested gain.  An eventually unit-bounded test sequence is totalized by a
bounded multiplier on its finite initial segment; the eventual equality with
the original tests is kept explicit when the result is transferred back.

The argument uses only the càdlàg path regularity of the tested elementary
gains.  It does not infer a coefficient-sum bound for the moving tests, and it
does not claim any convergence at all times from a fixed-time statement.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## Totalizing an eventual unit bound -/

/-- Totalize an eventually unit-bounded sequence of elementary tests.  The
fallback test is used only on the finite initial segment where the hypothesis
does not hold. -/
noncomputable def eventuallyUnitBoundedMultiplier
    (J : ℕ → PredictableElementaryStrategy ℱ)
    (T : ℝ≥0) :
    ℕ → BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ :=
  by
    classical
    exact fun n =>
      if h : ∀ t ω, |(J n).integrand t ω| ≤ 1 then
        { strategy := J n
          abs_integrand_le_one := h }
      else
        BoundedPredictableElementaryMultiplier.horizonUnit (ℱ := ℱ) T

theorem eventuallyUnitBoundedMultiplier_strategy_eq
    (J : ℕ → PredictableElementaryStrategy ℱ)
    (hJ : ∀ᶠ n in atTop, ∀ t ω, |(J n).integrand t ω| ≤ 1)
    (T : ℝ≥0) :
    ∀ᶠ n in atTop,
      (eventuallyUnitBoundedMultiplier J T n).strategy = J n := by
  classical
  filter_upwards [hJ] with n hn
  simp only [eventuallyUnitBoundedMultiplier]
  rw [dite_eq_left hn]

/-! ## Regularity of a tested elementary difference -/

private theorem testedDifference_hasLeftLimits_direct
    (S : Process Ω) (hSLeft : ProcessHasLeftLimits S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    ProcessHasLeftLimits (testedDifference S J H K) := by
  unfold testedDifference testedGain
  exact
    (ElementaryStrategy.gain_hasLeftLimits S hSLeft
      (J.strategy.mul H).toElementary).sub
      (ElementaryStrategy.gain_hasLeftLimits S hSLeft
        (J.strategy.mul K).toElementary)

/-! ## Test value to capped-envelope convergence -/

private theorem cappedTestEnvelope_eLpNorm_one_eq_testValue
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    eLpNorm
        (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (testedDifference S J H K) T)
        (1 : ℝ≥0∞) μ =
      ENNReal.ofReal (testValue μ S J H K T) := by
  let E : Ω → ℝ :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S J H K) T
  have hStrong : StronglyMeasurable E := by
    exact testEnvelope_stronglyMeasurable S hS J H K T
  have hInt : Integrable E μ := by
    exact testEnvelope_integrable S hS J H K T
  have hMem : MemLp E (1 : ℝ≥0∞) μ :=
    memLp_one_iff_integrable.mpr hInt
  change eLpNorm E (1 : ℝ≥0∞) μ = ENNReal.ofReal (testValue μ S J H K T)
  rw [← MeasureTheory.ofReal_lpNorm hMem]
  rw [lpNorm_one_eq_integral_norm hStrong.aestronglyMeasurable]
  congr 1
  calc
    (∫ x, ‖E x‖ ∂μ) = ∫ x, E x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg
        (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
          (testedDifference S J H K) T ω)]
    _ = testValue μ S J H K T :=
      (testValue_eq_integral μ S J H K T).symm

theorem cappedTestEnvelope_tendstoInMeasure_zero_of_testValue_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : ℕ → BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : ℕ → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hTest : Tendsto
      (fun n => testValue μ S (J n) (H n) (K n) T)
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S (J n) (H n) (K n)) T)
      atTop (fun _ => (0 : ℝ)) := by
  let E : ℕ → Ω → ℝ := fun n =>
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S (J n) (H n) (K n)) T
  have hStrong : ∀ n, StronglyMeasurable (E n) := by
    intro n
    exact testEnvelope_stronglyMeasurable S hS (J n) (H n) (K n) T
  have hNorm : Tendsto
      (fun n => eLpNorm (E n - (fun _ : Ω => (0 : ℝ)))
        (1 : ℝ≥0∞) μ)
      atTop (𝓝 0) := by
    have hEq : ∀ n,
        eLpNorm (E n - (fun _ : Ω => (0 : ℝ)))
            (1 : ℝ≥0∞) μ =
          ENNReal.ofReal (testValue μ S (J n) (H n) (K n) T) := by
      intro n
      have hSub : E n - (fun _ : Ω => (0 : ℝ)) = E n := by
        funext ω
        simp
      rw [hSub]
      simpa only [E] using
        cappedTestEnvelope_eLpNorm_one_eq_testValue
          (μ := μ) S hS (J n) (H n) (K n) T
    have hOfReal := ENNReal.tendsto_ofReal hTest
    rw [show (fun n => eLpNorm (E n - (fun _ : Ω => (0 : ℝ)))
        (1 : ℝ≥0∞) μ) =
          (fun n => ENNReal.ofReal (testValue μ S (J n) (H n) (K n) T)) by
      funext n
      exact hEq n]
    simpa only [ENNReal.ofReal_zero] using hOfReal
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞))
    (by norm_num) hNorm
  change TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (testedDifference S (J n) (H n) (K n)) T)
      atTop 0
  simpa only [E, Pi.zero_def] using hMeasure

/-! ## The fixed-time direct consumer -/

/-- Convergence of unit-bounded test values controls a fixed-time tested gain.
The bounded test rows `J` may differ from the original rows `Jraw`; the
eventual equality of their integrands is supplied explicitly. -/
theorem fixedTime_testedDifference_tendstoInMeasure_zero_of_testValue_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (J : ℕ → BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (Jraw : ℕ → PredictableElementaryStrategy ℱ)
    (hJ : ∀ᶠ n in atTop, (J n).strategy = Jraw n)
    (H K : ℕ → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hTest : Tendsto
      (fun n => testValue μ S (J n) (H n) (K n) T)
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n => elementaryGain S ((Jraw n).mul (H n)) T -
        elementaryGain S ((Jraw n).mul (K n)) T)
      atTop (fun _ => (0 : ℝ)) := by
  have hCapped := cappedTestEnvelope_tendstoInMeasure_zero_of_testValue_tendsto
    (μ := μ) S hS J H K T hTest
  have hEnvelope : TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (testedDifference S (J n) (H n) (K n)) T)
      atTop (fun _ => (0 : ℝ)) := by
    exact FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_capped
      T hCapped
  have hFixed : TendstoInMeasure μ
      (fun n => |testedDifference S (J n) (H n) (K n) T|)
      atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_nonneg_le
    · intro n ω
      refine ⟨abs_nonneg _, ?_⟩
      exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (testedDifference_rightContinuous S hSRight
          (J n) (H n) (K n))
        (testedDifference_hasLeftLimits_direct S hSLeft
          (J n) (H n) (K n)) T T le_rfl
    exact hEnvelope
  have hBoundedEq : ∀ᶠ n in atTop,
      (fun ω =>
        elementaryGain S ((J n).strategy.mul (H n)) T ω -
          elementaryGain S ((J n).strategy.mul (K n)) T ω) =
        (fun ω =>
          elementaryGain S ((Jraw n).mul (H n)) T ω -
            elementaryGain S ((Jraw n).mul (K n)) T ω) := by
    filter_upwards [hJ] with n hn
    funext ω
    rw [hn]
  have hWrapped : TendstoInMeasure μ
      (fun n =>
        fun ω =>
          elementaryGain S ((J n).strategy.mul (H n)) T ω -
            elementaryGain S ((J n).strategy.mul (K n)) T ω)
      atTop (fun _ => (0 : ℝ)) := by
    have hAbs : TendstoInMeasure μ
        (fun n => fun ω =>
          |elementaryGain S ((J n).strategy.mul (H n)) T ω -
            elementaryGain S ((J n).strategy.mul (K n)) T ω|)
        atTop (fun _ => (0 : ℝ)) := by
      have hAbsEq : ∀ n,
          (fun ω => |testedDifference S (J n) (H n) (K n) T ω|) =
            (fun ω =>
              |elementaryGain S ((J n).strategy.mul (H n)) T ω -
                elementaryGain S ((J n).strategy.mul (K n)) T ω|) := by
        intro n
        funext ω
        rfl
      exact TendstoInMeasure.congr_left
        (fun n => Eventually.of_forall (fun ω => congrFun (hAbsEq n) ω))
        hFixed
    rw [MeasureTheory.tendstoInMeasure_iff_norm] at hAbs ⊢
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_abs] using hAbs
  have hRaw : TendstoInMeasure μ
      (fun n =>
        fun ω =>
          elementaryGain S ((Jraw n).mul (H n)) T ω -
            elementaryGain S ((Jraw n).mul (K n)) T ω)
      atTop (fun _ => (0 : ℝ)) := by
    apply hWrapped.congr'
    · filter_upwards [hBoundedEq] with n hn
      exact Filter.Eventually.of_forall (fun ω => congrFun hn ω)
    · exact EventuallyEq.rfl
  change TendstoInMeasure μ
      (fun n ω => elementaryGain S ((Jraw n).mul (H n)) T ω -
        elementaryGain S ((Jraw n).mul (K n)) T ω)
      atTop (fun _ => (0 : ℝ))
  exact hRaw

/-- A gauge-convergent sequence of tested differences satisfies the same
fixed-time conclusion.  The gauge is used only through its supremum consumer,
so no unbounded raw test is inserted into the gauge. -/
theorem fixedTime_testedDifference_tendstoInMeasure_zero_of_eventuallyUnitBounded_gauge_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (Jraw : ℕ → PredictableElementaryStrategy ℱ)
    (hJraw : ∀ᶠ n in atTop,
      ∀ t ω, |(Jraw n).integrand t ω| ≤ 1)
    (H K : ℕ → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hGauge : Tendsto (fun n => gauge μ S (H n) (K n) T)
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n => elementaryGain S ((Jraw n).mul (H n)) T -
        elementaryGain S ((Jraw n).mul (K n)) T)
      atTop (fun _ => (0 : ℝ)) := by
  let J := eventuallyUnitBoundedMultiplier Jraw T
  have hTest : Tendsto
      (fun n => testValue μ S (J n) (H n) (K n) T)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hGauge
    · filter_upwards [] with n
      exact testValue_nonnegative μ S (J n) (H n) (K n) T
    · filter_upwards [] with n
      exact testValue_le_gauge S hS (J n) (H n) (K n) T
  exact fixedTime_testedDifference_tendstoInMeasure_zero_of_testValue_tendsto
    S hS hSRight hSLeft J Jraw
    (eventuallyUnitBoundedMultiplier_strategy_eq Jraw hJraw T)
    H K T hTest

end PredictableElementaryEmery

end FTAPTheorem42
