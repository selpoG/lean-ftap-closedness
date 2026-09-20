/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryFiniteVariationProcess
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Foundations.RightContinuousProgressive

/-! # Locally finite-variation processes are elementary good integrators -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

theorem ElementaryIntegrandsTendstoUniformlyZero.gain_tendsto_of_boundedVariation
    {H : Nat → PredictableElementaryStrategy F} (hH : ElementaryIntegrandsTendstoUniformlyZero H)
    (A : Process Ω) (hA : ∀ w, BoundedVariationOn (A · w) univ)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t) (T : NNReal) (w : Ω) :
    Tendsto (fun n => ElementaryStrategy.gain A (H n).toElementary T w) atTop (𝓝 0) := by
  let ν := FiniteVariationPath.signedMeasure (hA w)
  let : IsFiniteMeasure (ν : VectorMeasure NNReal Real).variation := by
    rw [← signedMeasure_totalVariation_eq_variation]
    infer_instance
  have hMeas (n : Nat) : AEStronglyMeasurable
      ((Ioc 0 T).indicator (fun t => (H n).integrand t w))
      (ν : VectorMeasure NNReal Real).variation := by
    rw [← signedMeasure_totalVariation_eq_variation]
    exact ((H n).integrable_integrand_section_totalVariation A hA w).aestronglyMeasurable
      |>.indicator measurableSet_Ioc
  have hBound : ∃ C : Real, ∀ᶠ n in atTop, ∀ᵐ t ∂(ν : VectorMeasure NNReal Real).variation,
      ‖(Ioc 0 T).indicator (fun t => (H n).integrand t w) t‖ ≤ C := by
    refine ⟨1, ?_⟩
    filter_upwards [hH 1 zero_lt_one] with n hn
    exact Eventually.of_forall (fun t => by
      by_cases ht : t ∈ Ioc 0 T
      · simpa only [indicator_of_mem ht, Real.norm_eq_abs] using hn t w
      · simp only [indicator_of_notMem ht, norm_zero, zero_le_one])
  have hLim : ∀ᵐ t ∂(ν : VectorMeasure NNReal Real).variation, Tendsto
      (fun n => (Ioc 0 T).indicator (fun t => (H n).integrand t w) t) atTop (𝓝 (0 : Real)) := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Ioc 0 T
    · simp only [indicator_of_mem ht]
      apply tendsto_order.mpr
      constructor
      · intro b hb
        filter_upwards [hH (-b / 2) (by linarith)] with n hn
        have := (abs_le.mp (hn t w)).1
        linarith
      · intro b hb
        filter_upwards [hH (b / 2) (by linarith)] with n hn
        exact (le_abs_self _).trans_lt ((hn t w).trans_lt (by linarith))
    · simp only [indicator_of_notMem ht]
      exact tendsto_const_nhds
  have h : Tendsto (fun n => FiniteVariationPath.integral (hA w)
      ((Ioc 0 T).indicator (fun t => (H n).integrand t w))) atTop
      (𝓝 (FiniteVariationPath.integral (hA w) (fun _ => 0))) := by
    exact VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall hMeas) hBound hLim
  have hGain (n : Nat) : ElementaryStrategy.gain A (H n).toElementary T w =
      FiniteVariationPath.integral (hA w) ((Ioc 0 T).indicator (fun t => (H n).integrand t w)) :=
    ((H n).finiteVariationIntegral_eq_gain A hA hRight T w).symm.trans
      ((H n).finiteVariationIntegral_eq_integral_indicator_integrand A hA T w)
  simpa only [hGain, FiniteVariationPath.integral, ν, VectorMeasure.integral_zero] using h

theorem ElementaryIntegrandsTendstoUniformlyZero.gain_tendsto_of_locallyBoundedVariation
    {H : Nat → PredictableElementaryStrategy F} (hH : ElementaryIntegrandsTendstoUniformlyZero H)
    (A : Process Ω) (hA : ∀ w, LocallyBoundedVariationOn (A · w) univ)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t) (T : NNReal) (w : Ω) :
    Tendsto (fun n => ElementaryStrategy.gain A (H n).toElementary T w) atTop (𝓝 0) := by
  let B : Process Ω := fun t w => A (min t T) w
  have hB : ∀ w, BoundedVariationOn (B · w) univ := fun w =>
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn (hA w) T
  have hBR : ∀ w t, ContinuousWithinAt (B · w) (Ici t) t := fun w =>
    FiniteVariationStoppedPath.rightContinuous_stopAt (A · w) (hRight w) T
  have hEq (K : ElementaryStrategy Ω NNReal) :
      ElementaryStrategy.gain B K T w = ElementaryStrategy.gain A K T w := by
    simp [ElementaryStrategy.gain, ElementaryInterval.gain, B,
      min_comm]
  simpa only [hEq] using hH.gain_tendsto_of_boundedVariation B hB hBR T w

theorem isSemimartingale_of_locallyBoundedVariation [IsFiniteMeasure mu]
    (A : Process Ω) (hAdapted : StronglyAdapted F A)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (hA : ∀ w, LocallyBoundedVariationOn (A · w) univ) : IsSemimartingale A F mu := by
  have hMeas (H : PredictableElementaryStrategy F) (T : NNReal) :
      AEStronglyMeasurable (ElementaryStrategy.gain A H.toElementary T) mu :=
    ((H.stronglyAdapted_gain A
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous hAdapted hRight) T).mono
      (F.le T)).aestronglyMeasurable
  refine ⟨hMeas, ?_⟩
  intro H hH T
  exact tendstoInMeasure_of_tendsto_ae (fun n => hMeas (H n) T)
    (Eventually.of_forall (hH.gain_tendsto_of_locallyBoundedVariation A hA hRight T))

end FTAPTheorem42
