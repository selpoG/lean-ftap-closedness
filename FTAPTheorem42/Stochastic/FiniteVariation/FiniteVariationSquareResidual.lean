/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FactorialLeftStieltjes
import FTAPTheorem42.Stochastic.FiniteVariation.FactorialCellStieltjes
import FTAPTheorem42.Stochastic.Process.CadlagJumpStieltjesSeries

/-! # Finite-variation square residuals as left-limit Stieltjes integrals -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.FactorialChronologicalGrid

open LeftContinuousPredictable

theorem tendsto_martingaleIntegralProcess_stieltjes
    {Ω : Type*} (K Q : Process Ω) (omega : Ω)
    (hRight : ∀ s, ContinuousWithinAt (K · omega) (Ici s) s)
    (hLeft : ∀ s, Tendsto (K · omega) (𝓝[<] s)
      (𝓝 (Function.leftLim (K · omega) s)))
    (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    (hQRight : ∀ s, ContinuousWithinAt (Q · omega) (Ici s) s) (T : NNReal) :
    Tendsto (fun r => (grid (r + 1)).martingaleIntegralProcess K Q T omega) atTop
      (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T, Function.leftLim (K · omega) s
        ∂•(FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
            hQ T)))) := by
  apply (tendsto_leftSum_stieltjes (K · omega) (Q · omega) hRight hLeft hQ hQRight T).congr'
  apply Eventually.of_forall
  intro r
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply, deterministicIntervalMartingaleTransform, stoppedProcess_const_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < (r + 1) * (r + 1).factorial := Finset.mem_range.mp hk
  have hTime : ∀ j ≤ (r + 1) * (r + 1).factorial,
      (grid (r + 1)).sampledTime j = gridPoint r j := by
    intro j hj
    simp only [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid,
      min_eq_left hj, gridPoint, denominator]
  rw [hTime k (Nat.le_of_lt hk'), hTime (k + 1) hk']
  by_cases hkt : gridPoint r k ≤ T
  · simp only [min_eq_left hkt, min_eq_right hkt, min_comm T]
  · have htk := le_of_not_ge hkt
    have htk1 : T ≤ gridPoint r (k + 1) := htk.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity))
    simp only [min_eq_left htk, min_eq_left htk1, min_eq_right htk, min_eq_right htk1,
      sub_self, mul_zero]

end FTAPTheorem42.FactorialChronologicalGrid

namespace FTAPTheorem42

theorem finiteVariation_squareResidual_eq_stieltjes
    {Ω : Type*} [MeasurableSpace Ω] (Q : Process Ω)
    (hRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t)
    (hLeft : ProcessHasLeftLimits Q)
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ) (T : NNReal) (omega : Ω) :
    Q T omega ^ 2 - Q 0 omega ^ 2 -
      (∑' s : Ioc (0 : NNReal) T, (processLeftJump Q s omega) ^ 2) =
      2 * (∫ᵛ s in Ioc (0 : NNReal) T, Function.leftLim (Q · omega) s
        ∂•(FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
            (hQ omega) T))) := by
  have hIntegral := FactorialChronologicalGrid.tendsto_martingaleIntegralProcess_stieltjes Q Q omega
    (hRight omega) (hLeft omega) (hQ omega) (hRight omega) T
  have hCross := FactorialChronologicalGrid.tendsto_crossIncrementProcess_stieltjes Q Q omega
    (hRight omega) (hLeft omega) (hQ omega) (hRight omega) T
  change Tendsto _ atTop (𝓝 (∫ᵛ s in Ioc (0 : NNReal) T, processLeftJump Q s omega
    ∂•(FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (hQ omega) T)))) at hCross
  rw [setIntegral_processLeftJump_eq_tsum Q Q hRight hLeft hRight hLeft hQ] at hCross
  have hLimit := (hIntegral.const_mul 2).add hCross
  have hConst : Tendsto (fun r =>
      2 * (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess Q Q T omega +
        (FactorialChronologicalGrid.grid (r + 1)).crossIncrementProcess Q Q T omega)
      atTop (𝓝 (Q T omega ^ 2 - Q 0 omega ^ 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Nat.ceil T)] with r hr
    have hT : T ≤ (r + 1 : Nat) :=
      (Nat.le_ceil T).trans (by exact_mod_cast hr.trans (Nat.le_succ r))
    have hEq := ChronologicalGrid.two_mul_martingaleIntegralProcess_add_squaredIncrementProcess
      (FactorialChronologicalGrid.grid (r + 1)) Q T omega
    have hLast : (FactorialChronologicalGrid.grid (r + 1)).sampledTime
        ((r + 1) * (r + 1).factorial) = (r + 1 : Nat) := by
      simp only [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        FactorialChronologicalGrid.grid, min_self, Nat.cast_mul]
      exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
    have hFirst : (FactorialChronologicalGrid.grid (r + 1)).sampledTime 0 = 0 := by
      simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        FactorialChronologicalGrid.grid]
    rw [hLast, hFirst, min_eq_left hT, min_eq_right (show (0 : NNReal) ≤ T from bot_le)] at hEq
    simpa only [ChronologicalGrid.crossIncrementProcess, ChronologicalGrid.squaredIncrementProcess,
      pow_two] using hEq.symm
  have hEq := tendsto_nhds_unique hLimit hConst
  simp only [← pow_two] at hEq
  linarith

end FTAPTheorem42
