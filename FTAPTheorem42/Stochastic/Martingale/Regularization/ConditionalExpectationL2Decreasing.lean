/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalAlgebra
import FTAPTheorem42.Foundations.UsualConditions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Conditional expectations along decreasing sigma algebras in L²

Orthogonal projections of one `L²` vector onto a decreasing sequence of
measurable subspaces form a Cauchy sequence.  This is the Hilbert-space input
for right-continuity of conditional-expectation martingales under a
right-continuous filtration.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [m0 : MeasurableSpace Omega]

/-- The ordinary `L²` value underlying conditional expectation onto `m`. -/
noncomputable def condExpL2Value
    (mu : Measure Omega) (m : MeasurableSpace Omega) (hm : m ≤ m0)
    (f : Lp Real 2 mu) : Lp Real 2 mu :=
  (condExpL2 Real Real (m := m) (m0 := m0) (μ := mu) hm f : Lp Real 2 mu)

/-- Pythagoras for conditional expectations onto two nested sigma
algebras, without packaging them as a sequence. -/
theorem norm_sub_condExpL2Value_sq_eq_of_le
    {mu : Measure Omega} {mSmall mLarge : MeasurableSpace Omega}
    (hSmall : mSmall ≤ m0) (hLarge : mLarge ≤ m0)
    (hNested : mSmall ≤ mLarge) (f : Lp Real 2 mu) :
    ‖condExpL2Value (m0 := m0) mu mLarge hLarge f -
        condExpL2Value (m0 := m0) mu mSmall hSmall f‖ ^ 2 =
      ‖condExpL2Value (m0 := m0) mu mLarge hLarge f‖ ^ 2 -
        ‖condExpL2Value (m0 := m0) mu mSmall hSmall f‖ ^ 2 := by
  have hSmallMeas : AEStronglyMeasurable[mSmall]
      (condExpL2Value (m0 := m0) mu mSmall hSmall f : Omega → Real) mu := by
    simpa only [condExpL2Value] using
      (aestronglyMeasurable_condExpL2 (m := mSmall) (m0 := m0) (μ := mu)
        hSmall f)
  have hSmallMeasLarge : AEStronglyMeasurable[mLarge]
      (condExpL2Value (m0 := m0) mu mSmall hSmall f : Omega → Real) mu :=
    hSmallMeas.mono hNested
  have hInner : inner Real
      (condExpL2Value (m0 := m0) mu mLarge hLarge f)
      (condExpL2Value (m0 := m0) mu mSmall hSmall f) =
      inner Real
        (condExpL2Value (m0 := m0) mu mSmall hSmall f)
        (condExpL2Value (m0 := m0) mu mSmall hSmall f) := by
    calc
      inner Real (condExpL2Value (m0 := m0) mu mLarge hLarge f)
          (condExpL2Value (m0 := m0) mu mSmall hSmall f) =
          inner Real f (condExpL2Value (m0 := m0) mu mSmall hSmall f) := by
        simpa only [condExpL2Value] using
          (inner_condExpL2_eq_inner_fun (m := mLarge) (m0 := m0) (μ := mu)
            hLarge f (condExpL2Value (m0 := m0) mu mSmall hSmall f)
              hSmallMeasLarge)
      _ = inner Real (condExpL2Value (m0 := m0) mu mSmall hSmall f)
          (condExpL2Value (m0 := m0) mu mSmall hSmall f) := by
        symm
        simpa only [condExpL2Value] using
          (inner_condExpL2_eq_inner_fun (m := mSmall) (m0 := m0) (μ := mu)
            hSmall f (condExpL2Value (m0 := m0) mu mSmall hSmall f)
              hSmallMeas)
  rw [norm_sub_sq_real, hInner, real_inner_self_eq_norm_sq]
  ring

/-- Moving the conditioning sigma algebra farther from a fixed smaller one
can only increase the corresponding `L²` projection distance. -/
theorem norm_sub_condExpL2Value_mono_of_le
    {mu : Measure Omega} {m0' m1 m2 : MeasurableSpace Omega}
    (h0 : m0' ≤ m0) (h1 : m1 ≤ m0) (h2 : m2 ≤ m0)
    (h01 : m0' ≤ m1) (h12 : m1 ≤ m2) (f : Lp Real 2 mu) :
    ‖condExpL2Value (m0 := m0) mu m1 h1 f -
        condExpL2Value (m0 := m0) mu m0' h0 f‖ ≤
      ‖condExpL2Value (m0 := m0) mu m2 h2 f -
        condExpL2Value (m0 := m0) mu m0' h0 f‖ := by
  have hSq01 := norm_sub_condExpL2Value_sq_eq_of_le (m0 := m0)
    h0 h1 h01 f
  have hSq02 := norm_sub_condExpL2Value_sq_eq_of_le (m0 := m0)
    h0 h2 (h01.trans h12) f
  have hSq12 := norm_sub_condExpL2Value_sq_eq_of_le (m0 := m0)
    h1 h2 h12 f
  have hSqLe :
      ‖condExpL2Value (m0 := m0) mu m1 h1 f -
          condExpL2Value (m0 := m0) mu m0' h0 f‖ ^ 2 ≤
        ‖condExpL2Value (m0 := m0) mu m2 h2 f -
          condExpL2Value (m0 := m0) mu m0' h0 f‖ ^ 2 := by
    rw [hSq01, hSq02]
    nlinarith [sq_nonneg
      ‖condExpL2Value (m0 := m0) mu m2 h2 f -
        condExpL2Value (m0 := m0) mu m1 h1 f‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hSqLe

theorem condExpL2Value_inner_eq_of_antitone
    {mu : Measure Omega} (m : Nat → MeasurableSpace Omega)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    (f : Lp Real 2 mu) {n k : Nat} (hnk : n ≤ k) :
    inner Real (condExpL2Value mu (m n) (hm0 n) f)
        (condExpL2Value mu (m k) (hm0 k) f) =
      inner Real (condExpL2Value mu (m k) (hm0 k) f)
        (condExpL2Value mu (m k) (hm0 k) f) := by
  have hkMeasAtK : AEStronglyMeasurable[m k]
      (condExpL2Value mu (m k) (hm0 k) f : Omega → Real) mu := by
    simpa only [condExpL2Value] using
      (aestronglyMeasurable_condExpL2 (m := m k) (m0 := m0) (μ := mu)
        (hm0 k) f)
  have hkMeas : AEStronglyMeasurable[m n]
      (condExpL2Value mu (m k) (hm0 k) f : Omega → Real) mu :=
    hkMeasAtK.mono (hm hnk)
  calc
    inner Real (condExpL2Value mu (m n) (hm0 n) f)
        (condExpL2Value mu (m k) (hm0 k) f) =
        inner Real f (condExpL2Value mu (m k) (hm0 k) f) :=
      by
        simpa only [condExpL2Value] using
          (inner_condExpL2_eq_inner_fun (m := m n) (m0 := m0) (μ := mu)
            (hm0 n) f (condExpL2Value mu (m k) (hm0 k) f) hkMeas)
    _ = inner Real (condExpL2Value mu (m k) (hm0 k) f)
        (condExpL2Value mu (m k) (hm0 k) f) := by
      symm
      simpa only [condExpL2Value] using
          (inner_condExpL2_eq_inner_fun (m := m k) (m0 := m0) (μ := mu)
          (hm0 k) f (condExpL2Value mu (m k) (hm0 k) f)
          hkMeasAtK)

/-- Pythagoras for two nested conditional-expectation projections. -/
theorem norm_sub_condExpL2Value_sq_eq
    {mu : Measure Omega} (m : Nat → MeasurableSpace Omega)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    (f : Lp Real 2 mu) {n k : Nat} (hnk : n ≤ k) :
    ‖condExpL2Value mu (m n) (hm0 n) f -
        condExpL2Value mu (m k) (hm0 k) f‖ ^ 2 =
      ‖condExpL2Value mu (m n) (hm0 n) f‖ ^ 2 -
        ‖condExpL2Value mu (m k) (hm0 k) f‖ ^ 2 := by
  rw [norm_sub_sq_real,
    condExpL2Value_inner_eq_of_antitone m hm hm0 f hnk,
    real_inner_self_eq_norm_sq]
  ring

/-- Conditional expectations of one `L²` vector along a decreasing
sequence of sigma algebras form a Cauchy sequence in `L²`. -/
theorem cauchySeq_condExpL2Value_of_antitone
    {mu : Measure Omega} (m : Nat → MeasurableSpace Omega)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    (f : Lp Real 2 mu) :
    CauchySeq (fun n => condExpL2Value mu (m n) (hm0 n) f) := by
  let x : Nat → Lp Real 2 mu := fun n =>
    condExpL2Value mu (m n) (hm0 n) f
  let q : Nat → Real := fun n => ‖x n‖ ^ 2
  have hq : Antitone q := by
    intro n k hnk
    have hsq := norm_sub_condExpL2Value_sq_eq m hm hm0 f hnk
    have hnonneg : 0 ≤ ‖x n - x k‖ ^ 2 := sq_nonneg _
    dsimp only [x, q]
    dsimp only [x] at hnonneg
    linarith
  have hqBound : BddBelow (Set.range q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sq_nonneg _
  have hqTendsto : Tendsto q atTop (𝓝 (⨅ n, q n)) :=
    tendsto_atTop_ciInf hq hqBound
  have hqCauchy : CauchySeq q := hqTendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hqCauchy
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hqCauchy (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, ?_⟩
  intro n hn k hk
  by_cases hnk : n ≤ k
  · have hqDist := hN n hn k hk
    have hsq := norm_sub_condExpL2Value_sq_eq m hm hm0 f hnk
    have hqOrder : q k ≤ q n := hq hnk
    have hsqLt : ‖x n - x k‖ ^ 2 < epsilon ^ 2 := by
      rw [show ‖x n - x k‖ ^ 2 = q n - q k by simpa [x, q] using hsq]
      have habs : |q n - q k| < epsilon ^ 2 := by
        simpa only [Real.dist_eq] using hqDist
      rwa [abs_of_nonneg (sub_nonneg.mpr hqOrder)] at habs
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).mp hsqLt
  · have hkn : k ≤ n := le_of_not_ge hnk
    have hqDist := hN k hk n hn
    have hsq := norm_sub_condExpL2Value_sq_eq m hm hm0 f hkn
    have hqOrder : q n ≤ q k := hq hkn
    have hsqLt : ‖x k - x n‖ ^ 2 < epsilon ^ 2 := by
      rw [show ‖x k - x n‖ ^ 2 = q k - q n by simpa [x, q] using hsq]
      have habs : |q k - q n| < epsilon ^ 2 := by
        simpa only [Real.dist_eq] using hqDist
      rwa [abs_of_nonneg (sub_nonneg.mpr hqOrder)] at habs
    rw [dist_eq_norm, norm_sub_rev]
    exact (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).mp hsqLt

/-- The canonical deterministic approximation of `t` from the right. -/
noncomputable def condExpRightApproxTime (t : NNReal) (n : Nat) : NNReal :=
  t + PredictableIntervalAlgebra.rightApproxZero n

theorem condExpRightApproxTime_antitone (t : NNReal) :
    Antitone (condExpRightApproxTime t) := by
  intro n k hnk
  dsimp only [condExpRightApproxTime,
    PredictableIntervalAlgebra.rightApproxZero]
  gcongr

theorem tendsto_condExpRightApproxTime (t : NNReal) :
    Tendsto (condExpRightApproxTime t) atTop (𝓝 t) := by
  change Tendsto (fun n =>
    t + PredictableIntervalAlgebra.rightApproxZero n) atTop (𝓝 t)
  simpa only [add_zero] using
    (tendsto_const_nhds.add
      PredictableIntervalAlgebra.tendsto_rightApproxZero)

/-- For a right-continuous filtration, the sigma algebras at the canonical
right approximations decrease exactly to the sigma algebra at `t`. -/
theorem iInf_filtration_condExpRightApproxTime_eq
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRight : F.IsRightContinuous) (t : NNReal) :
    (⨅ n, F (condExpRightApproxTime t n)) = F t := by
  apply le_antisymm
  · apply le_trans ?_ (hRight.RC t)
    rw [F.rightCont_eq]
    refine le_iInf fun s => le_iInf fun hts => ?_
    have heventually : ∀ᶠ n in atTop,
        condExpRightApproxTime t n ∈ Set.Iio s :=
      (tendsto_condExpRightApproxTime t).eventually (Iio_mem_nhds hts)
    obtain ⟨n, hn⟩ := heventually.exists
    exact (iInf_le _ n).trans (F.mono hn.le)
  · refine le_iInf fun n => F.mono ?_
    exact le_add_of_nonneg_right bot_le

end FTAPTheorem42
