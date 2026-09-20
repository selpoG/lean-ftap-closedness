/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.StoppedGoodIntegrator
import FTAPTheorem42.Stochastic.Stopping.FiniteTruncation
import FTAPTheorem42.Stochastic.DS.Lemma411.MaximalApproximation

/-! # Uniform maximal tightness of unit elementary integrals -/

namespace FTAPTheorem42.IsSemimartingale

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsFiniteMeasure μ] [F.IsRightContinuous]

/-- Stopping at the first strict passage upgrades terminal tightness to a
bound for the entire finite horizon, uniformly over all unit tests. -/
theorem uniformly_boundedInProbability_elementaryGain_maximal
    {S : Process Ω} (hS : IsSemimartingale S F μ)
    (hAdapted : StronglyAdapted F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (T : NNReal) :
    ∀ ε > (0 : Real), ∃ R > (0 : Real),
      ∀ H : PredictableElementaryStrategy F,
        (∀ t w, |H.integrand t w| ≤ 1) →
        μ {w | ∃ t ≤ T, R < |ElementaryStrategy.gain S H.toElementary t w|} ≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨r, hr, hTail⟩ := hS.claimSetBoundedInProbability_unitBoundedElementaryGainSet T ε hε
  refine ⟨r + 1, by linarith, fun H hH => ?_⟩
  let X := ElementaryStrategy.gain S H.toElementary
  have hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t :=
    PredictableElementaryStrategy.rightContinuous_gain S hRight H
  let τ := absoluteStrictHittingAfter X (r + 1)
  have hτ : IsStoppingTime F τ := absoluteStrictHittingAfter_isStoppingTime
    (PredictableElementaryStrategy.stronglyAdapted_gain S
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous hAdapted hRight) H) hXR (r + 1)
  let σ := PredictableElementaryStrategy.truncatedStoppingTime τ T
  have hσ := PredictableElementaryStrategy.truncatedStoppingTime_isStoppingTime hτ T
  let K := H.stopAt σ hσ
  have hK : ∀ t w, |K.integrand t w| ≤ 1 := by
    intro t w
    rw [PredictableElementaryStrategy.integrand_stopAt]
    split_ifs
    · exact hH t w
    · norm_num
  apply (measure_mono (show {w | ∃ t ≤ T, r + 1 < |X t w|} ⊆
    {w | r < |ElementaryStrategy.gain S K.toElementary T w|} from ?_)).trans
    (hTail _ ⟨K, hK, rfl⟩)
  rintro w ⟨t, ht, hx⟩
  have hτt : τ w ≤ (t : WithTop NNReal) := by
    by_contra hn
    exact (not_le_of_gt hx) (abs_le_of_lt_absoluteStrictHittingAfter X (r + 1) w t
      (lt_of_not_ge hn))
  have hτT : τ w ≤ (T : WithTop NNReal) := hτt.trans (by exact_mod_cast ht)
  have hTop : τ w ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτT
  have hσeq : σ w = (τ w).untopA := by
    change (min (τ w) (T : WithTop NNReal)).untopA = _
    rw [min_eq_left hτT]
  have hσT : σ w ≤ T := by
    have hcoe := congrFun (PredictableElementaryStrategy.coe_truncatedStoppingTime
      (τ := τ) T) w
    exact_mod_cast (hcoe.trans_le (min_le_right _ _))
  change r < |ElementaryStrategy.gain S (H.stopAt σ hσ).toElementary T w|
  rw [PredictableElementaryStrategy.gain_stopAt, min_eq_right hσT, hσeq]
  exact (lt_add_one r).trans_le
    (le_abs_untopA_absoluteStrictHittingAfter X hXR (r + 1) w hTop)

end FTAPTheorem42.IsSemimartingale

namespace FTAPTheorem42.IsSemimartingale

/-! ## Uniform small-scalar estimates from the good-integrator property -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [F.IsRightContinuous]

theorem uniform_smallScalar_integral
    {S : Process Ω} (hS : IsSemimartingale S F μ)
    (hProg : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (T : NNReal) (ε : Real) (hε : 0 < ε) :
    ∃ δ > (0 : Real), ∀ a : Real, |a| ≤ δ →
      ∀ H : PredictableElementaryStrategy F, (∀ t w, |H.integrand t w| ≤ 1) →
      (∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => a * ElementaryStrategy.gain S H.toElementary t w) T w ∂μ) ≤ ε := by
  obtain ⟨R, hR, hTail⟩ := hS.uniformly_boundedInProbability_elementaryGain_maximal
    hProg.stronglyAdapted hRight T (ε / 2) (by positivity)
  refine ⟨ε / 4 / R, by positivity, fun a ha H hH => ?_⟩
  let X := ElementaryStrategy.gain S H.toElementary
  let f := FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope (fun t w => a * X t w) T
  have hf : StronglyMeasurable f :=
    (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      (fun t => (PredictableElementaryStrategy.stronglyAdapted_gain S hProg H t).const_smul a)
      T).mono (F.le T)
  have hBounds w : 0 ≤ f w ∧ f w ≤ 1 :=
    ⟨FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _⟩
  have hInt : Integrable f μ := (integrable_const (1 : Real)).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBounds w).1]
      exact (hBounds w).2)
  let E := {w | ε / 2 ≤ f w}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf.measurable
  have hSubset : E ⊆ {w | ∃ t ≤ T, R < |X t w|} := by
    intro w hw
    by_contra hn
    change ¬ ∃ t ≤ T, R < |X t w| at hn
    push Not at hn
    have hBound : ∀ t, t ≤ T → |a * X t w| ≤ |a| * R := by
      intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hn t ht) (abs_nonneg a)
    have hCap : f w ≤ |a| * R := by
      apply ENNReal.toReal_le_of_le_ofReal (by positivity)
      exact (min_le_left _ _).trans
        (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_le_of_bound _ T hBound)
    have hSmall : |a| * R ≤ ε / 4 := (le_div_iff₀ hR).mp ha
    change ε / 2 ≤ f w at hw
    linarith
  have hMeasure : μ.real E ≤ ε / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_mono hSubset).trans (hTail H hH))
  have hUpper w : f w ≤ ε / 2 + E.indicator (fun _ => (1 : Real)) w := by
    by_cases hw : w ∈ E
    · rw [indicator_of_mem hw]
      linarith [(hBounds w).2]
    · rw [indicator_of_notMem hw]
      exact (le_of_lt (lt_of_not_ge hw)).trans (by simp)
  have h := integral_mono_ae hInt
    ((integrable_const (ε / 2)).add ((integrable_const (1 : Real)).indicator hE))
    (Eventually.of_forall hUpper)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const (ε / 2)) ((integrable_const (1 : Real)).indicator hE)] at h
  simp only [integral_const, integral_indicator hE, smul_eq_mul,
    mul_one] at h
  simp at h
  exact h.trans (by linarith)

end FTAPTheorem42.IsSemimartingale
