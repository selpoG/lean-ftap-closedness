/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationSquareResidual
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticStoppingConsistency
import FTAPTheorem42.Stochastic.Stopping.LocalVariationPassage

/-! # Stopped finite-grid integrals

Predictable gating preserves the martingale property under stopping. Path
variation bounds the integrals and cross increments; discrete integration by
parts identifies the product decomposition. -/

namespace FTAPTheorem42.ChronologicalGrid

open Filter MeasureTheory Set Topology
open scoped NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] in
/-- A stopped coefficient can be gated strictly before the stop, because
all integrator increments after the stop vanish. -/
theorem martingaleIntegralProcess_stopped_eq_gated {N : Nat} (G : ChronologicalGrid NNReal N)
    (K M : Process Ω) (tau : Ω → NNReal) :
    G.martingaleIntegralProcess (stoppedProcess K (fun w => (tau w : WithTop NNReal)))
      (stoppedProcess M (fun w => (tau w : WithTop NNReal))) =
    G.martingaleIntegralProcess (fun s w => if s < tau w then K s w else 0)
      (stoppedProcess M (fun w => (tau w : WithTop NNReal))) := by
  classical
  funext t omega
  unfold martingaleIntegralProcess
  simp only [Finset.sum_apply, deterministicIntervalMartingaleTransform, stoppedProcess_const_apply,
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : G.sampledTime k < tau omega
  · simp only [hk, ite_true, min_eq_left hk.le]
  · have htk : tau omega ≤ G.sampledTime k := le_of_not_gt hk
    have htk1 : tau omega ≤ G.sampledTime (k + 1) := htk.trans (G.sampledTime_mono (Nat.le_succ k))
    simp only [hk, ite_false, min_assoc, min_eq_right htk, min_eq_right htk1, sub_self, mul_zero]

/-- The stopped coefficient may have a large terminal jump. Only its
strict-prefix bound is needed for the finite-grid martingale law. -/
theorem martingaleIntegralProcess_stopped_isMartingale {N : Nat} (G : ChronologicalGrid NNReal N)
    {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (K M : Process Ω) (tau : Ω → NNReal)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hK : StronglyAdapted F K)
    (hM : Martingale (stoppedProcess M (fun w => (tau w : WithTop NNReal))) F mu)
    (hRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    {a : Real} (ha : 0 ≤ a) (hBound : ∀ omega s, s < tau omega → |K s omega| ≤ a) :
    Martingale (G.martingaleIntegralProcess
      (stoppedProcess K (fun w => (tau w : WithTop NNReal)))
      (stoppedProcess M (fun w => (tau w : WithTop NNReal)))) F mu := by
  classical
  rw [G.martingaleIntegralProcess_stopped_eq_gated]
  have hGate : StronglyAdapted F (fun s w => if s < tau w then K s w else 0) := by
    intro s
    have hSet : MeasurableSet[F s] {w | s < tau w} := by
      simpa only [Set.compl_ofPred, not_le, WithTop.coe_lt_coe] using
        (hTau.measurableSet_le s).compl
    exact (hK s).piecewise hSet stronglyMeasurable_const
  apply G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted hM
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hRight) hGate
    (C := fun _ => a)
  intro s
  apply Eventually.of_forall
  intro omega
  split_ifs with h
  · exact hBound omega s h
  · simpa only [abs_zero] using ha

end FTAPTheorem42.ChronologicalGrid

/-! ## Variation domination for bounded finite-grid integrands -/

namespace FTAPTheorem42.ChronologicalGrid

open MeasureTheory Set
open scoped NNReal

theorem abs_martingaleIntegralProcess_le_variation
    {Ω : Type*} {N : Nat} (G : ChronologicalGrid NNReal N)
    (K Q : Process Ω) (omega : Ω)
    (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    {a : Real} (ha : 0 ≤ a) (hK : ∀ s, |K s omega| ≤ a) (t : NNReal) :
    |G.martingaleIntegralProcess K Q t omega| ≤ a * localVariation Q t omega := by
  unfold martingaleIntegralProcess
  simp only [Finset.sum_apply, deterministicIntervalMartingaleTransform, stoppedProcess_const_apply]
  calc
    _ ≤ ∑ k ∈ Finset.range N, a *
        |Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hK _) (abs_nonneg _)
    _ = a * ∑ k ∈ Finset.range N,
        |Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (G.sum_abs_increment_le_variation Q omega hQ t) ha

theorem abs_martingaleIntegralProcess_stopped_le_variation
    {Ω : Type*} {N : Nat} (G : ChronologicalGrid NNReal N)
    (K Q : Process Ω) (tau : Ω → NNReal) (omega : Ω)
    (hQ : LocallyBoundedVariationOn
      (fun s => stoppedProcess Q (fun w => (tau w : WithTop NNReal)) s omega) univ)
    {a : Real} (ha : 0 ≤ a) (hK : ∀ s, s < tau omega → |K s omega| ≤ a) (t : NNReal) :
    |G.martingaleIntegralProcess
      (stoppedProcess K (fun w => (tau w : WithTop NNReal)))
      (stoppedProcess Q (fun w => (tau w : WithTop NNReal))) t omega| ≤
        a * localVariation (stoppedProcess Q (fun w => (tau w : WithTop NNReal))) t omega := by
  rw [G.martingaleIntegralProcess_stopped_eq_gated]
  apply G.abs_martingaleIntegralProcess_le_variation _ _ omega hQ ha
  intro s
  split_ifs with hs
  · exact hK s hs
  · simpa only [abs_zero] using ha

end FTAPTheorem42.ChronologicalGrid

namespace FTAPTheorem42.ChronologicalGrid

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} {N : Nat} (G : ChronologicalGrid NNReal N)

theorem product_decomposition (L Q : Process Ω) (t : NNReal) (omega : Ω) :
    G.martingaleIntegralProcess L Q t omega + G.martingaleIntegralProcess Q L t omega =
      L (min t (G.sampledTime N)) omega * Q (min t (G.sampledTime N)) omega -
        L (min t (G.sampledTime 0)) omega * Q (min t (G.sampledTime 0)) omega -
          G.crossIncrementProcess L Q t omega := by
  have hTerm (k : Nat) :
      L (G.sampledTime k) omega *
          (Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega) +
        Q (G.sampledTime k) omega *
          (L (min t (G.sampledTime (k + 1))) omega - L (min t (G.sampledTime k)) omega) +
        (L (min t (G.sampledTime (k + 1))) omega - L (min t (G.sampledTime k)) omega) *
          (Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega) =
      L (min t (G.sampledTime (k + 1))) omega * Q (min t (G.sampledTime (k + 1))) omega -
        L (min t (G.sampledTime k)) omega * Q (min t (G.sampledTime k)) omega := by
    by_cases hk : G.sampledTime k ≤ t
    · rw [min_eq_right hk]; ring
    · have ht := le_of_not_ge hk
      rw [min_eq_left ht, min_eq_left (ht.trans (G.sampledTime_mono (Nat.le_succ k)))]
      ring
  apply eq_sub_iff_add_eq.mpr
  unfold martingaleIntegralProcess crossIncrementProcess
  simp only [Finset.sum_apply, deterministicIntervalMartingaleTransform, stoppedProcess_const_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact (Finset.sum_congr rfl (fun k _ => hTerm k)).trans
    (Finset.sum_range_sub (fun k =>
      L (min t (G.sampledTime k)) omega * Q (min t (G.sampledTime k)) omega) N)

theorem abs_crossIncrementProcess_le_variation (L Q : Process Ω) (omega : Ω)
    (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    {b : Real} (hb : 0 ≤ b) (hL : ∀ s, |L s omega| ≤ b) (t : NNReal) :
    |G.crossIncrementProcess L Q t omega| ≤ 2 * b * localVariation Q t omega := by
  unfold crossIncrementProcess
  calc
    _ ≤ ∑ k ∈ Finset.range N, (2 * b) *
        |Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (abs_sub _ _).trans (by
        linarith [hL (min t (G.sampledTime (k + 1))), hL (min t (G.sampledTime k))])
    _ = (2 * b) * ∑ k ∈ Finset.range N,
        |Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (G.sum_abs_increment_le_variation Q omega hQ t)
      (mul_nonneg (by norm_num) hb)

theorem abs_product_integrals_le_three_mul_variation
    (L Q : Process Ω) (omega : Ω)
    (hQ : ∀ w, LocallyBoundedVariationOn (Q · w) univ) (hZero : Q 0 = 0)
    (hFirst : G.sampledTime 0 = 0)
    {b : Real} (hb : 0 ≤ b) (hL : ∀ s, |L s omega| ≤ b) (t : NNReal) :
    |G.martingaleIntegralProcess L Q t omega + G.martingaleIntegralProcess Q L t omega| ≤
      3 * b * localVariation Q t omega := by
  rw [G.product_decomposition, hFirst, min_eq_right (show (0 : NNReal) ≤ t from bot_le),
    hZero, Pi.zero_apply, mul_zero, sub_zero]
  have hProd : |L (min t (G.sampledTime N)) omega * Q (min t (G.sampledTime N)) omega| ≤
      b * localVariation Q t omega := by
    rw [abs_mul]
    apply mul_le_mul (hL _) _ (abs_nonneg _) hb
    exact (abs_le_localVariation hQ hZero omega _).trans
      (variationOnFromTo.monotoneOn (hQ omega) (mem_univ _) (mem_univ _) (mem_univ _)
        (min_le_left _ _))
  have hCross := G.abs_crossIncrementProcess_le_variation L Q omega (hQ omega) hb hL t
  linarith [abs_sub (L (min t (G.sampledTime N)) omega * Q (min t (G.sampledTime N)) omega)
    (G.crossIncrementProcess L Q t omega)]

end FTAPTheorem42.ChronologicalGrid
