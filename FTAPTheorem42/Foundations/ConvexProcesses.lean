/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Foundations.HilbertConvexification
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.Nat.Pairing

/-! # Regularity of processes with fixed finite convex weights -/

namespace FTAPTheorem42.TailConvexWeights

open MeasureTheory Set Filter
open scoped NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  {n : Nat} (w : TailConvexWeights n) (M : Nat → Process Ω)

omit [MeasurableSpace Ω] in
theorem applyVector_process_apply (t : NNReal) (ω : Ω) :
    w.applyVector M t ω = w.apply (fun i => M i t) ω := by
  simp only [applyVector, apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem applyVector_martingale (hM : ∀ i, Martingale (M i) F μ) :
    Martingale (w.applyVector M) F μ := by
  classical
  unfold applyVector
  induction w.support using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using martingale_zero Real F μ
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ((hM i).smul (w.weight i)).add ih

omit [MeasurableSpace Ω] in
theorem applyVector_rightContinuous
    (hM : ∀ i ω t, ContinuousWithinAt (M i · ω) (Ici t) t) :
    ∀ ω t, ContinuousWithinAt (w.applyVector M · ω) (Ici t) t := by
  intro ω t
  simp only [applyVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact tendsto_finsetSum _ (fun i _ => continuousWithinAt_const.mul (hM i ω t))

theorem applyVector_stronglyAdapted (hM : ∀ i, StronglyAdapted F (M i)) :
    StronglyAdapted F (w.applyVector M) := by
  classical
  unfold applyVector
  induction w.support using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using stronglyAdapted_zero Real F
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ((hM i).smul (w.weight i)).add ih

theorem applyVector_zero_ae (hM : ∀ i, M i 0 =ᵐ[μ] 0) :
    w.applyVector M 0 =ᵐ[μ] 0 := by
  filter_upwards [ae_all_iff.mpr hM] with ω hω
  simp only [applyVector, Finset.sum_apply, Pi.smul_apply, hω, Pi.zero_apply,
    smul_zero, Finset.sum_const_zero]

end FTAPTheorem42.TailConvexWeights

namespace FTAPTheorem42

/-! ## Forward convex combinations preserve the same uniform limit -/

open Filter Topology

/-- One convex row per tail preserves uniform convergence on the whole domain.
The weights need not satisfy any bound on the number of terms in their support. -/
theorem TailConvexWeights.tendstoUniformly_apply
    {α : Type*} (w : ∀ n, TailConvexWeights n)
    {f : Nat → α → Real} {g : α → Real}
    (h : TendstoUniformly f g atTop) :
    TendstoUniformly (fun n => (w n).apply f) g atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε / 2) (half_pos hε))
  refine eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
  have hDiff := congrFun ((w n).apply_sub_constFunction f g) x
  rw [Real.dist_eq, abs_sub_comm, ← hDiff]
  change |∑ i ∈ (w n).support, (w n).weight i * (f i x - g x)| < ε
  calc
    _ ≤ ∑ i ∈ (w n).support, |(w n).weight i * (f i x - g x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ (w n).support, (w n).weight i * (ε / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg ((w n).nonneg i hi)]
      apply mul_le_mul_of_nonneg_left _ ((w n).nonneg i hi)
      have hix := hN i (hn.trans ((w n).tail i hi)) x
      simpa only [Real.dist_eq, abs_sub_comm] using hix.le
    _ = ε / 2 := by rw [← Finset.sum_mul, (w n).sum_eq_one, one_mul]
    _ < ε := half_lt_self hε

end FTAPTheorem42

namespace FTAPTheorem42.TailConvexWeights

/-! ## Embedding a finite convex family at one integer horizon -/

open scoped BigOperators

/-- Put every index on the same second coordinate of the countable pair
encoding. No convex coefficient is changed. -/
def atPair (w : TailConvexWeights 0) (r : Nat) : TailConvexWeights 0 where
  support := w.support.image (fun i => Nat.pair i r)
  weight := fun k => w.weight (Nat.unpair k).1
  tail := fun _ _ => Nat.zero_le _
  nonneg := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    simpa only [Nat.unpair_pair] using w.nonneg i hi
  sum_eq_one := by
    rw [Finset.sum_image]
    · simpa only [Nat.unpair_pair] using w.sum_eq_one
    · intro i _ j _ hij
      exact (Nat.pair_eq_pair.mp hij).1

/-- The encoded family has exactly the original weighted values at the
chosen horizon coordinate. -/
theorem atPair_apply {Ω : Type*} (w : TailConvexWeights 0) (r : Nat)
    (X : Nat → Ω → Real) :
    (w.atPair r).apply X = w.apply (fun i => X (Nat.pair i r)) := by
  funext ω
  unfold apply atPair
  rw [Finset.sum_image]
  · simp only [Nat.unpair_pair]
  · intro i _ j _ hij
    exact (Nat.pair_eq_pair.mp hij).1

end FTAPTheorem42.TailConvexWeights
