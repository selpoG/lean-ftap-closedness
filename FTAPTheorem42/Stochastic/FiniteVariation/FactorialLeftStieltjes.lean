/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FactorialCellStieltjes

/-! # Left endpoint sums converge to the left-limit Stieltjes integral -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.LeftContinuousPredictable

private noncomputable def leftCell (f : NNReal → Real) (T : NNReal) (r : Nat) : NNReal → Real :=
  fun s => f (min (approx r s) T)

private theorem leftCell_measurable (f : NNReal → Real) (T : NNReal) (r : Nat) :
    Measurable (leftCell f T r) := by
  have hIndex : Measurable (leftIndex r) :=
    ((measurable_id.mul_const (denominator r : NNReal)).nat_ceil).sub_const 1
  exact (measurable_of_countable (f := fun k : Nat => f (min (gridPoint r k) T))).comp hIndex

private theorem leftCell_tendsto (f : NNReal → Real)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {T s : NNReal} (hs : s ∈ Ioc 0 T) :
    Tendsto (fun r => leftCell f T r s) atTop (𝓝 (Function.leftLim f s)) := by
  have hLower : Tendsto (fun r => approx r s) atTop (𝓝[<] s) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_approx s, Eventually.of_forall (fun r => approx_lt (ne_of_gt hs.1) r)⟩
  simpa only [leftCell, Function.comp_def, min_eq_left ((approx_le _ s).trans hs.2)] using
    (hLeft s).comp hLower

private theorem leftCell_integrable (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (T : NNReal) (η : SignedMeasure NNReal) (r : Nat) : η.Integrable (leftCell f T r) := by
  obtain ⟨C, hC⟩ :=
    FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits f hRight hLeft T
  change Integrable _ η.variation
  rw [← signedMeasure_totalVariation_eq_variation]
  exact (integrable_const C).mono' (leftCell_measurable f T r).aestronglyMeasurable
    (Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs, leftCell] using hC (min (approx r s) T) (min_le_right _ _))

private theorem leftCell_integral_tendsto (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (T : NNReal) (η : SignedMeasure NNReal) :
    Tendsto (fun r => ∫ᵛ s in Ioc (0 : NNReal) T, leftCell f T r s ∂•η) atTop
      (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T, Function.leftLim f s ∂•η)) := by
  have hVariation : (η.restrict (Ioc 0 T)).variation =
      η.totalVariation.restrict (Ioc 0 T) := by
    rw [VectorMeasure.variation_restrict measurableSet_Ioc,
      ← signedMeasure_totalVariation_eq_variation]
  have hMeas : ∀ r, AEStronglyMeasurable (leftCell f T r)
      (η.restrict (Ioc 0 T)).variation := fun r => (leftCell_measurable f T r).aestronglyMeasurable
  have hLimit : ∀ᵐ s ∂(η.restrict (Ioc 0 T)).variation,
      Tendsto (fun r => leftCell f T r s) atTop (𝓝 (Function.leftLim f s)) := by
    rw [hVariation]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact leftCell_tendsto f hLeft hs
  obtain ⟨C, hC⟩ :=
    FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits f hRight hLeft T
  have hBound : ∀ r, ∀ᵐ s ∂(η.restrict (Ioc 0 T)).variation, ‖leftCell f T r s‖ ≤ C :=
    fun r => Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs, leftCell] using hC (min (approx r s) T) (min_le_right _ _)
  refine VectorMeasure.tendsto_integral_of_L1 _
    (aestronglyMeasurable_of_tendsto_ae atTop hMeas hLimit)
    (Eventually.of_forall fun r => (leftCell_integrable f hRight hLeft T η r).integrableOn) ?_
  have hInt : Integrable (fun _ : NNReal => C) (η.restrict (Ioc 0 T)).variation := by
    rw [hVariation]
    exact integrable_const C
  simpa only [← ofReal_norm] using
    tendsto_lintegral_norm_of_dominated_convergence hMeas hInt.hasFiniteIntegral hBound hLimit

private theorem leftCell_integral_eq_sum
    (f A : NNReal → Real)
    (hfRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hfLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (hA : BoundedVariationOn A univ) (hARight : ∀ s, ContinuousWithinAt A (Ici s) s)
    (T : NNReal) (r n : Nat) :
    (∫ᵛ s in Ioc (0 : NNReal) (min (gridPoint r n) T),
      leftCell f T r s ∂•(FiniteVariationPath.signedMeasure hA)) =
      ∑ k ∈ Finset.range n, f (min (gridPoint r k) T) *
        (A (min (gridPoint r (k + 1)) T) - A (min (gridPoint r k) T)) := by
  induction n with
  | zero => simp [gridPoint]
  | succ n ih =>
    have hle : min (gridPoint r n) T ≤ min (gridPoint r (n + 1)) T :=
      min_le_min_right _
        (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity))
    have hInt := leftCell_integrable f hfRight hfLeft T (FiniteVariationPath.signedMeasure hA) r
    have hCell : ∀ s ∈ Ioc (min (gridPoint r n) T) (min (gridPoint r (n + 1)) T),
        leftCell f T r s = f (min (gridPoint r n) T) := by
      intro s hs
      have hs' : s ∈ Ioc (gridPoint r n) (gridPoint r (n + 1)) :=
        ⟨(min_lt_iff.mp hs.1).resolve_right (not_lt_of_ge (hs.2.trans (min_le_right _ _))),
          hs.2.trans (min_le_left _ _)⟩
      simp only [leftCell, approx_eq_gridPoint_of_mem_Ioc hs']
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : NNReal) ≤ min (gridPoint r n) T from bot_le) hle,
      VectorMeasure.setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
        measurableSet_Ioc measurableSet_Ioc hInt.integrableOn hInt.integrableOn,
      ih, VectorMeasure.setIntegral_congr_fun hCell,
      FiniteVariationPath.setIntegral_const_Ioc hA hARight hle, Finset.sum_range_succ]

/-- The unmodified chronological left endpoint sums converge for any
càdlàg integrand and locally finite-variation integrator. -/
theorem tendsto_leftSum_stieltjes
    (f Q : NNReal → Real)
    (hfRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hfLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (hQ : LocallyBoundedVariationOn Q univ)
    (hQRight : ∀ s, ContinuousWithinAt Q (Ici s) s) (T : NNReal) :
    Tendsto (fun r => ∑ k ∈ Finset.range ((r + 1) * (r + 1).factorial),
      f (min (gridPoint r k) T) *
        (Q (min (gridPoint r (k + 1)) T) - Q (min (gridPoint r k) T))) atTop
      (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T, Function.leftLim f s
        ∂•(FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
            hQ T)))) := by
  have hA := FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn hQ T
  have hARight := FiniteVariationStoppedPath.rightContinuous_stopAt Q hQRight T
  apply (leftCell_integral_tendsto f hfRight hfLeft T
    (FiniteVariationPath.signedMeasure hA)).congr'
  filter_upwards [eventually_ge_atTop (Nat.ceil T)] with r hr
  have hT : T ≤ (r + 1 : Nat) :=
    (Nat.le_ceil T).trans (by exact_mod_cast hr.trans (Nat.le_succ r))
  have hEnd : gridPoint r ((r + 1) * (r + 1).factorial) = (r + 1 : Nat) := by
    simp only [gridPoint, denominator, Nat.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
  have hSum := leftCell_integral_eq_sum f _ hfRight hfLeft hA hARight
    T r ((r + 1) * (r + 1).factorial)
  rw [hEnd, min_eq_right hT] at hSum
  simpa only [FiniteVariationStoppedPath.stopAt, min_assoc, min_self, min_comm T] using hSum

end FTAPTheorem42.LeftContinuousPredictable
