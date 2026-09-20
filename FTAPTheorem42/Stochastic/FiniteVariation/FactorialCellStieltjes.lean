/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Process.FactorialCellJumpLimit
import FTAPTheorem42.Stochastic.Martingale.Quadratic.FiniteGridMartingaleQuadraticDecomposition

/-! # Stieltjes limits of factorial cell increments -/

namespace FTAPTheorem42.LeftContinuousPredictable

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The cell integral is exactly the product of the stopped path increment
and the integrator increment. -/
theorem setIntegral_cellIncrement_Ioc
    (f A : NNReal → Real) (hA : BoundedVariationOn A univ)
    (hRight : ∀ s, ContinuousWithinAt A (Ici s) s) (T : NNReal) (r k : Nat) :
    (∫ᵛ s in Ioc (min (gridPoint r k) T) (min (gridPoint r (k + 1)) T),
      cellIncrement f T r s ∂•(FiniteVariationPath.signedMeasure hA)) =
      (f (min (gridPoint r (k + 1)) T) - f (min (gridPoint r k) T)) *
        (A (min (gridPoint r (k + 1)) T) - A (min (gridPoint r k) T)) := by
  have hCell : ∀ s ∈ Ioc (min (gridPoint r k) T) (min (gridPoint r (k + 1)) T),
      cellIncrement f T r s =
        f (min (gridPoint r (k + 1)) T) - f (min (gridPoint r k) T) := by
    intro s hs
    apply cellIncrement_eq_of_mem_Ioc f T
    exact ⟨(min_lt_iff.mp hs.1).resolve_right (not_lt_of_ge (hs.2.trans (min_le_right _ _))),
      hs.2.trans (min_le_left _ _)⟩
  rw [VectorMeasure.setIntegral_congr_fun hCell]
  apply FiniteVariationPath.setIntegral_const_Ioc hA hRight
  exact min_le_min_right _
    (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity))

private theorem cellIncrement_integrable
    (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (T : NNReal) (η : SignedMeasure NNReal) (r : Nat) :
    η.Integrable (cellIncrement f T r) := by
  obtain ⟨C, hC⟩ :=
    FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits
      f hRight hLeft T
  change Integrable _ η.variation
  rw [← signedMeasure_totalVariation_eq_variation]
  refine (integrable_const (2 * C)).mono'
    (cellIncrement_measurable f T r).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by
    linarith [hC (min (gridPoint r (leftIndex r s + 1)) T) (min_le_right _ _),
      hC (min (approx r s) T) (min_le_right _ _)])

/-- Summing the mesh cells recovers the stopped finite cross-increment sum. -/
theorem setIntegral_cellIncrement_eq_sum
    (f A : NNReal → Real)
    (hfRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hfLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (hA : BoundedVariationOn A univ)
    (hARight : ∀ s, ContinuousWithinAt A (Ici s) s) (T : NNReal) (r n : Nat) :
    (∫ᵛ s in Ioc (0 : NNReal) (min (gridPoint r n) T),
      cellIncrement f T r s ∂•(FiniteVariationPath.signedMeasure hA)) =
      ∑ k ∈ Finset.range n,
        (f (min (gridPoint r (k + 1)) T) - f (min (gridPoint r k) T)) *
          (A (min (gridPoint r (k + 1)) T) - A (min (gridPoint r k) T)) := by
  induction n with
  | zero => simp [gridPoint]
  | succ n ih =>
    have hle : min (gridPoint r n) T ≤ min (gridPoint r (n + 1)) T :=
      min_le_min_right _
        (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity))
    have hInt := cellIncrement_integrable f hfRight hfLeft T
      (FiniteVariationPath.signedMeasure hA) r
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : NNReal) ≤ min (gridPoint r n) T from bot_le) hle,
      VectorMeasure.setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
        measurableSet_Ioc measurableSet_Ioc hInt.integrableOn hInt.integrableOn,
      ih, setIntegral_cellIncrement_Ioc f A hA hARight, Finset.sum_range_succ]

/-- Cell increments converge in signed Stieltjes integral. The convergence
is obtained from the stronger error estimate under Jordan total variation. -/
theorem tendsto_setIntegral_cellIncrement
    (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (T : NNReal) (η : SignedMeasure NNReal) :
    Tendsto (fun r => ∫ᵛ s in Ioc (0 : NNReal) T,
      cellIncrement f T r s ∂•η) atTop
      (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T, f s - Function.leftLim f s ∂•η)) := by
  have hVariation : (η.restrict (Ioc 0 T)).variation =
      η.totalVariation.restrict (Ioc 0 T) := by
    rw [VectorMeasure.variation_restrict measurableSet_Ioc,
      ← signedMeasure_totalVariation_eq_variation]
  have hMeas : ∀ r, AEStronglyMeasurable (cellIncrement f T r)
      (η.restrict (Ioc 0 T)).variation := fun r =>
    (cellIncrement_measurable f T r).aestronglyMeasurable
  have hLimit : ∀ᵐ s ∂(η.restrict (Ioc 0 T)).variation,
      Tendsto (fun r => cellIncrement f T r s) atTop
        (𝓝 (f s - Function.leftLim f s)) := by
    rw [hVariation]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact tendsto_cellIncrement f hRight hLeft hs
  refine VectorMeasure.tendsto_integral_of_L1 _
    (aestronglyMeasurable_of_tendsto_ae atTop hMeas hLimit) ?_ ?_
  · exact Eventually.of_forall (fun r =>
      (cellIncrement_integrable f hRight hLeft T η r).integrableOn)
  · rw [hVariation]
    simpa only [← ofReal_norm, Real.norm_eq_abs] using
      tendsto_lintegral_cellIncrement_error f hRight hLeft T η.totalVariation

end FTAPTheorem42.LeftContinuousPredictable

namespace FTAPTheorem42.FactorialChronologicalGrid

/-! ## Factorial cross-increment sums converge to a Stieltjes jump integral -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LeftContinuousPredictable

/-- The actual finite grid cross sum converges, pathwise, when the second
path has locally bounded variation. The limiting integral uses its stop at
the same horizon, so no global variation assumption is needed. -/
theorem tendsto_crossIncrementProcess_stieltjes
    {Ω : Type*} (X Q : Process Ω) (omega : Ω)
    (hRight : ∀ s, ContinuousWithinAt (X · omega) (Ici s) s)
    (hLeft : ∀ s, Tendsto (X · omega) (𝓝[<] s)
      (𝓝 (Function.leftLim (X · omega) s)))
    (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    (hQRight : ∀ s, ContinuousWithinAt (Q · omega) (Ici s) s) (T : NNReal) :
    Tendsto (fun r => (grid (r + 1)).crossIncrementProcess X Q T omega) atTop
      (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T,
        X s omega - Function.leftLim (X · omega) s
          ∂•(FiniteVariationPath.signedMeasure
            (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
              hQ T)))) := by
  let A := FiniteVariationStoppedPath.stopAt (Q · omega) T
  have hA :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn hQ T
  have hARight := FiniteVariationStoppedPath.rightContinuous_stopAt (Q · omega) hQRight T
  have hLimit := tendsto_setIntegral_cellIncrement (X · omega) hRight hLeft T
    (FiniteVariationPath.signedMeasure hA)
  apply hLimit.congr'
  filter_upwards [eventually_ge_atTop (Nat.ceil T)] with r hr
  have hT : T ≤ (r + 1 : Nat) :=
    (Nat.le_ceil T).trans (by exact_mod_cast hr.trans (Nat.le_succ r))
  have hEnd : gridPoint r ((r + 1) * (r + 1).factorial) = (r + 1 : Nat) := by
    simp only [gridPoint, denominator, Nat.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
  have hSum := setIntegral_cellIncrement_eq_sum (X · omega) A hRight hLeft hA hARight
    T r ((r + 1) * (r + 1).factorial)
  rw [hEnd, min_eq_right hT] at hSum
  rw [hSum]
  unfold ChronologicalGrid.crossIncrementProcess
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < (r + 1) * (r + 1).factorial := Finset.mem_range.mp hk
  have hTime : ∀ j ≤ (r + 1) * (r + 1).factorial,
      (grid (r + 1)).sampledTime j = gridPoint r j := by
    intro j hj
    simp only [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid,
      min_eq_left hj, gridPoint, denominator]
  rw [hTime k (Nat.le_of_lt hk'), hTime (k + 1) hk']
  simp only [A, FiniteVariationStoppedPath.stopAt, min_assoc, min_self, min_comm T]

end FTAPTheorem42.FactorialChronologicalGrid
