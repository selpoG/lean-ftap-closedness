/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcess
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Quadratic decompositions on finite martingale grids

For a finite chronological grid, the elementary identity

`x_{k+1}² - x_k² = 2 x_k (x_{k+1} - x_k) + (x_{k+1} - x_k)²`

decomposes the stopped square of a process into a left-endpoint martingale
transform and a sum of squared stopped increments.  The coefficient in the
transform is the source process itself.  It is adapted, but need not be
predictable as a continuous-time process; the finite-grid martingale theorem
therefore uses only adaptedness at the deterministic left endpoints.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The sum of the squared increments stopped inside every cell of a finite
chronological grid. -/
noncomputable def squaredIncrementProcess (X : Process Omega) : Process Omega :=
  fun t omega =>
    ∑ k ∈ Finset.range N,
      (X (min t (G.sampledTime (k + 1))) omega -
        X (min t (G.sampledTime k)) omega) ^ 2

omit [MeasurableSpace Omega] in
/-- The finite-grid squared-increment process is pointwise nonnegative. -/
theorem squaredIncrementProcess_nonneg
    (X : Process Omega) (t : NNReal) (omega : Omega) :
    0 <= G.squaredIncrementProcess X t omega := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [MeasurableSpace Omega] in
/-- A squared-increment process starts from zero. -/
theorem squaredIncrementProcess_zero (X : Process Omega) :
    G.squaredIncrementProcess X 0 = 0 := by
  funext omega
  unfold squaredIncrementProcess
  simp

omit [MeasurableSpace Omega] in
/-- At a grid time, the squared-increment process is exactly the prefix sum
of the full grid increments. -/
theorem squaredIncrementProcess_sampledTime_eq_prefixSum
    (X : Process Omega) {j : Nat} (hj : j <= N) (omega : Omega) :
    G.squaredIncrementProcess X (G.sampledTime j) omega =
      ∑ k ∈ Finset.range j,
        (X (G.sampledTime (k + 1)) omega -
          X (G.sampledTime k) omega) ^ 2 := by
  unfold squaredIncrementProcess
  have hsubset : Finset.range j ⊆ Finset.range N :=
    Finset.range_mono hj
  have hsum :
      (∑ k ∈ Finset.range j,
        (X (min (G.sampledTime j) (G.sampledTime (k + 1))) omega -
          X (min (G.sampledTime j) (G.sampledTime k)) omega) ^ 2) =
      ∑ k ∈ Finset.range N,
        (X (min (G.sampledTime j) (G.sampledTime (k + 1))) omega -
          X (min (G.sampledTime j) (G.sampledTime k)) omega) ^ 2 := by
    apply Finset.sum_subset hsubset
    intro k _hkN hkJ
    have hjk : j <= k := by
      exact Nat.le_of_not_gt fun hkj => hkJ (Finset.mem_range.mpr hkj)
    have hjk1 : G.sampledTime j <= G.sampledTime (k + 1) :=
      G.sampledTime_mono (hjk.trans (Nat.le_succ k))
    have hjk0 : G.sampledTime j <= G.sampledTime k :=
      G.sampledTime_mono hjk
    rw [min_eq_left hjk1, min_eq_left hjk0, sub_self, zero_pow]
    norm_num
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < j := Finset.mem_range.mp hk
  have hk1j : k + 1 <= j := Nat.succ_le_iff.mpr hklt
  rw [min_eq_right (G.sampledTime_mono hk1j),
    min_eq_right (G.sampledTime_mono hklt.le)]

omit [MeasurableSpace Omega] in
/-- The squared-increment process is monotone along the chronological grid. -/
theorem squaredIncrementProcess_sampledTime_mono
    (X : Process Omega) {j l : Nat} (hjl : j <= l) (hl : l <= N)
    (omega : Omega) :
    G.squaredIncrementProcess X (G.sampledTime j) omega <=
      G.squaredIncrementProcess X (G.sampledTime l) omega := by
  rw [G.squaredIncrementProcess_sampledTime_eq_prefixSum X
      (hjl.trans hl) omega,
    G.squaredIncrementProcess_sampledTime_eq_prefixSum X hl omega]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjl)
    fun k _hk _ => sq_nonneg
      (X (G.sampledTime (k + 1)) omega - X (G.sampledTime k) omega)

omit [MeasurableSpace Omega] in
/-- The squared-increment process is monotone between any two times occurring
in the range of its chronological grid. -/
theorem squaredIncrementProcess_mono_of_mem_range
    (X : Process Omega) {s t : NNReal}
    (hs : s ∈ Set.range G.time) (ht : t ∈ Set.range G.time)
    (hst : s <= t) (omega : Omega) :
    G.squaredIncrementProcess X s omega <=
      G.squaredIncrementProcess X t omega := by
  obtain ⟨j, rfl⟩ := hs
  obtain ⟨l, rfl⟩ := ht
  by_cases hjl : j <= l
  · simpa only [G.sampledTime_fin_eq] using
      G.squaredIncrementProcess_sampledTime_mono X
        (show j.val <= l.val from hjl)
        (Nat.le_of_lt_succ l.isLt) omega
  · have hlj : l <= j := le_of_not_ge hjl
    have hreverse : G.time l <= G.time j := G.monotone_time hlj
    rw [le_antisymm hst hreverse]

omit [MeasurableSpace Omega] in
/-- The martingale transform plus the squared-increment process telescopes
to the stopped square increment between the two ends of the grid. -/
theorem two_mul_martingaleIntegralProcess_add_squaredIncrementProcess
    (X : Process Omega) (t : NNReal) (omega : Omega) :
    2 * G.martingaleIntegralProcess X X t omega +
        G.squaredIncrementProcess X t omega =
      X (min t (G.sampledTime N)) omega ^ 2 -
        X (min t (G.sampledTime 0)) omega ^ 2 := by
  have hTerm (k : Nat) :
      2 * (X (G.sampledTime k) omega *
          (X (min t (G.sampledTime (k + 1))) omega -
            X (min t (G.sampledTime k)) omega)) +
          (X (min t (G.sampledTime (k + 1))) omega -
            X (min t (G.sampledTime k)) omega) ^ 2 =
        X (min t (G.sampledTime (k + 1))) omega ^ 2 -
          X (min t (G.sampledTime k)) omega ^ 2 := by
    by_cases hkt : G.sampledTime k <= t
    · rw [min_eq_right hkt]
      ring
    · have htk : t <= G.sampledTime k := le_of_not_ge hkt
      have htk1 : t <= G.sampledTime (k + 1) :=
        htk.trans (G.sampledTime_mono (Nat.le_succ k))
      rw [min_eq_left htk, min_eq_left htk1]
      ring
  unfold martingaleIntegralProcess squaredIncrementProcess
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range N,
        (2 * deterministicIntervalMartingaleTransform X X
            (G.sampledTime k) (G.sampledTime (k + 1)) t omega +
          (X (min t (G.sampledTime (k + 1))) omega -
            X (min t (G.sampledTime k)) omega) ^ 2)) =
        ∑ k ∈ Finset.range N,
          (X (min t (G.sampledTime (k + 1))) omega ^ 2 -
            X (min t (G.sampledTime k)) omega ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa only [deterministicIntervalMartingaleTransform,
        stoppedProcess_const_apply] using hTerm k
    _ = _ := Finset.sum_range_sub
      (fun k => X (min t (G.sampledTime k)) omega ^ 2) N

/-- Twice the left-endpoint transform by a bounded adapted source is a true
martingale. -/
theorem two_smul_martingaleIntegralProcess_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {X : Process Omega} {C : NNReal -> Real}
    (hX : Martingale X F mu)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXBound : ∀ t, ∀ᵐ omega ∂mu, |X t omega| <= C t) :
    Martingale
      ((2 : Real) • G.martingaleIntegralProcess X X) F mu := by
  exact Martingale.smul 2
    (G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted
      hX hXRight hX.stronglyAdapted hXBound)

omit [MeasurableSpace Omega] in
/-- Twice the finite-grid martingale transform is right-continuous. -/
theorem two_smul_martingaleIntegralProcess_rightContinuous
    (X : Process Omega)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t) :
    ∀ omega t, ContinuousWithinAt
      ((2 : Real) • G.martingaleIntegralProcess X X · omega) (Ici t) t := by
  intro omega t
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (G.martingaleIntegralProcess_rightContinuous X X hXRight omega t).const_mul 2

end ChronologicalGrid

end FTAPTheorem42

namespace FTAPTheorem42.ChronologicalGrid

/-! ## Quadratic algebra on the same stopped chronological grid -/

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The cross increment sum uses exactly the same stopped cells as the
existing squared-increment process. -/
noncomputable def crossIncrementProcess (X Y : Process Ω) : Process Ω := fun t omega =>
  ∑ k ∈ Finset.range N,
    (X (min t (G.sampledTime (k + 1))) omega - X (min t (G.sampledTime k)) omega) *
    (Y (min t (G.sampledTime (k + 1))) omega - Y (min t (G.sampledTime k)) omega)

/-- Exact quadratic decomposition at every time, including times inside
a grid cell. No martingale or path regularity assumption is needed. -/
theorem squaredIncrementProcess_add (X Y : Process Ω) (t : NNReal) (omega : Ω) :
    G.squaredIncrementProcess (fun s w => X s w + Y s w) t omega =
      G.squaredIncrementProcess X t omega + 2 * G.crossIncrementProcess X Y t omega +
        G.squaredIncrementProcess Y t omega := by
  simp only [squaredIncrementProcess, crossIncrementProcess]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Cauchy--Schwarz for the stopped cell increments. -/
theorem crossIncrementProcess_le_root_mul (X Y : Process Ω) (t : NNReal) (omega : Ω) :
    G.crossIncrementProcess X Y t omega ≤
      Real.sqrt (G.squaredIncrementProcess X t omega) *
        Real.sqrt (G.squaredIncrementProcess Y t omega) :=
  Real.sum_mul_le_sqrt_mul_sqrt (Finset.range N) _ _

/-- The quadratic root satisfies the triangle inequality on each grid. -/
theorem sqrt_squaredIncrementProcess_add_le (X Y : Process Ω) (t : NNReal) (omega : Ω) :
    Real.sqrt (G.squaredIncrementProcess (fun s w => X s w + Y s w) t omega) ≤
      Real.sqrt (G.squaredIncrementProcess X t omega) +
        Real.sqrt (G.squaredIncrementProcess Y t omega) := by
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [G.squaredIncrementProcess_add]
  have hX := Real.sq_sqrt (G.squaredIncrementProcess_nonneg X t omega)
  have hY := Real.sq_sqrt (G.squaredIncrementProcess_nonneg Y t omega)
  nlinarith [G.crossIncrementProcess_le_root_mul X Y t omega]

/-- Total absolute cell increments are controlled by the path variation
on `[0,t]`, even when the grid has repeated points or starts after zero. -/
theorem sum_abs_increment_le_variation
    (Q : Process Ω) (omega : Ω) (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    (t : NNReal) :
    (∑ k ∈ Finset.range N,
      |Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega|) ≤
        variationOnFromTo (Q · omega) univ 0 t := by
  have hBV : eVariationOn (Q · omega) (Icc 0 t) ≠ ∞ := by
    change BoundedVariationOn (Q · omega) (Icc 0 t)
    simpa only [univ_inter] using hQ 0 t (mem_univ _) (mem_univ _)
  have hSum : (∑ k ∈ Finset.range N,
      edist (Q (min t (G.sampledTime (k + 1))) omega)
        (Q (min t (G.sampledTime k)) omega)) ≤ eVariationOn (Q · omega) (Icc 0 t) :=
    eVariationOn.sum_le_of_monotoneOn_Iic (f := (Q · omega))
      (u := fun k => min t (G.sampledTime k))
      (fun _ _ _ _ h => min_le_min_left t (G.sampledTime_mono h))
      (fun _ _ => ⟨bot_le, min_le_left _ _⟩)
  have hReal := ENNReal.toReal_mono hBV hSum
  rw [ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _)] at hReal
  rw [variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le), univ_inter]
  simpa only [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal, abs_nonneg] using hReal

/-- The quadratic root of locally finite-variation increments is bounded
by the same path variation, uniformly over chronological grids. -/
theorem sqrt_squaredIncrementProcess_le_variation
    (Q : Process Ω) (omega : Ω) (hQ : LocallyBoundedVariationOn (Q · omega) univ)
    (t : NNReal) :
    Real.sqrt (G.squaredIncrementProcess Q t omega) ≤
      variationOnFromTo (Q · omega) univ 0 t := by
  let a : Nat → Real := fun k =>
    Q (min t (G.sampledTime (k + 1))) omega - Q (min t (G.sampledTime k)) omega
  have hAbs : 0 ≤ ∑ k ∈ Finset.range N, |a k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSq : (∑ k ∈ Finset.range N, (a k) ^ 2) ≤ (∑ k ∈ Finset.range N, |a k|) ^ 2 := by
    simpa only [sq_abs] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range N) (fun k _ => abs_nonneg (a k))
  have hRoot : Real.sqrt (G.squaredIncrementProcess Q t omega) ≤ ∑ k ∈ Finset.range N, |a k| :=
    (Real.sqrt_le_iff).2 ⟨hAbs, hSq⟩
  exact hRoot.trans (G.sum_abs_increment_le_variation Q omega hQ t)

end FTAPTheorem42.ChronologicalGrid
