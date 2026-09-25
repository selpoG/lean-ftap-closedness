/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.TerminalLimit
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.UniformConvergence
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Core.Closedness
import Mathlib.MeasureTheory.Measure.Real

/-! # Uniform limits of paths

Summable step bounds yield uniform convergence. Right continuity, left limits,
and continuous-time terminal limits pass to the same uniform limit. -/

namespace FTAPTheorem42

open Filter Set Topology
open scoped BigOperators

/-- Summable consecutive differences give uniform Cauchy control on a set,
without requiring a pointwise limit as input. -/
theorem uniformCauchySeqOn_of_eventually_dist_step_le_of_summable
    {Time : Type*} (F : ℕ → Time → ℝ) (s : Set Time) (q : ℕ → ℝ)
    (hq : Summable q) (hqNonneg : ∀ k, 0 ≤ q k)
    (hStep : ∀ᶠ k in atTop, ∀ t ∈ s,
      dist (F k t) (F (k + 1) t) ≤ q k) :
    UniformCauchySeqOn F atTop s := by
  have hTail : Tendsto (fun n => ∑' m, q (n + m)) atTop (𝓝 0) := by
    have hPartial := hq.tendsto_sum_tsum_nat
    have hSub : Tendsto
        (fun n => (∑' m, q m) - ∑ m ∈ Finset.range n, q m)
        atTop (𝓝 ((∑' m, q m) - ∑' m, q m)) :=
      tendsto_const_nhds.sub hPartial
    convert hSub using 1
    · funext n
      have hSplit := hq.sum_add_tsum_nat_add n
      rw [show (fun m => q (n + m)) = (fun m => q (m + n)) by
        funext m
        rw [add_comm]]
      linarith
    · simp
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 hStep
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hTail.eventually (Iio_mem_nhds hε))
  refine ⟨max K N, fun m hm n hn t ht => ?_⟩
  wlog hmn : m ≤ n generalizing m n
  · rw [dist_comm]
    exact this n hn m hm (le_of_not_ge hmn)
  calc
    dist (F m t) (F n t) ≤ ∑ i ∈ Finset.Ico m n, q i := by
      apply dist_le_Ico_sum_of_dist_le hmn
      intro k hmk _hkn
      simpa only [Nat.succ_eq_add_one] using
        hK k (((le_max_left K N).trans hm).trans hmk) t ht
    _ ≤ ∑' r, q (m + r) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hShiftSummable : Summable (fun r => q (m + r)) :=
        hq.comp_injective (fun _ _ h => Nat.add_left_cancel h)
      exact hShiftSummable.sum_le_tsum (Finset.range (n - m))
        (fun i _ => hqNonneg (m + i))
    _ < ε := hN m ((le_max_right K N).trans hm)

/-- An eventually uniform summable bound on consecutive differences upgrades
pointwise convergence to uniform convergence. -/
theorem tendstoUniformly_of_eventually_dist_step_le_of_summable
    {Time : Type*} [Nonempty Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ) (q : ℕ → ℝ)
    (hq : Summable q) (hqNonneg : ∀ k, 0 ≤ q k)
    (hStep : ∀ᶠ k in atTop, ∀ t,
      dist (F k t) (F (k + 1) t) ≤ q k)
    (hLimit : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    TendstoUniformly F f atTop := by
  apply tendstoUniformlyOn_univ.mp
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  · exact uniformCauchySeqOn_of_eventually_dist_step_le_of_summable F univ q hq hqNonneg
      (hStep.mono fun _ hk t _ => hk t)
  · exact fun t _ => hLimit t

/-- A uniform limit of right-continuous paths is right-continuous. -/
theorem rightContinuous_of_tendstoUniformly
    {Time : Type*} [Preorder Time] [TopologicalSpace Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ)
    (hUniform : TendstoUniformly F f atTop)
    (hRight : ∀ k t, ContinuousWithinAt (F k) (Set.Ici t) t) :
    ∀ t, ContinuousWithinAt f (Set.Ici t) t := by
  intro t
  exact hUniform.tendsto_of_eventually_tendsto
    (Filter.Eventually.of_forall fun k => hRight k t)
    (hUniform.tendsto_at t)

/-- A uniform limit of real-valued paths with left limits again has a left
limit at every time.  The left limits of the approximants form a Cauchy
sequence because their pairwise distances are bounded by the uniform
distance of the paths. -/
theorem leftLimits_of_tendstoUniformly
    {Time : Type*} [LinearOrder Time] [TopologicalSpace Time]
    [OrderTopology Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ)
    (hUniform : TendstoUniformly F f atTop)
    (hLeft : ∀ k t, Tendsto (F k) (𝓝[<] t)
      (𝓝 (Function.leftLim (F k) t))) :
    ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) := by
  intro t
  apply tendsto_leftLim_of_tendsto
  let L : ℕ → ℝ := fun k => Function.leftLim (F k) t
  have hLCauchy : CauchySeq L := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    have hHalf : 0 < epsilon / 2 := by positivity
    have hUniformCauchy : UniformCauchySeqOn F atTop Set.univ :=
      hUniform.tendstoUniformlyOn.uniformCauchySeqOn
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp
      hUniformCauchy (epsilon / 2) hHalf
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases eq_or_neBot (𝓝[<] t) with hbot | hne
    · rw [show L m = F m t by
          simp only [L, leftLim_eq_of_eq_bot (F m) hbot],
        show L n = F n t by
          simp only [L, leftLim_eq_of_eq_bot (F n) hbot]]
      exact (hN m hm n hn t (Set.mem_univ t)).trans
        (half_lt_self hepsilon)
    · have hDistance : Tendsto (fun s => dist (F m s) (F n s))
          (𝓝[<] t) (𝓝 (dist (L m) (L n))) := by
        exact (hLeft m t).dist (hLeft n t)
      have hBound : dist (L m) (L n) ≤ epsilon / 2 :=
        le_of_tendsto hDistance (Filter.Eventually.of_forall fun s =>
          (hN m hm n hn s (Set.mem_univ s)).le)
      exact hBound.trans_lt (half_lt_self hepsilon)
  exact ⟨limUnder atTop L,
    hUniform.tendsto_of_eventually_tendsto
      (Filter.Eventually.of_forall fun k => hLeft k t)
      hLCauchy.tendsto_limUnder⟩

/-- Under uniform convergence, the selected left limits of the approximating
paths converge to the selected left limit of the limiting path. -/
theorem tendsto_leftLim_of_tendstoUniformly
    {Time : Type*} [LinearOrder Time] [TopologicalSpace Time]
    [OrderTopology Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ)
    (hUniform : TendstoUniformly F f atTop)
    (hLeft : ∀ k t, Tendsto (F k) (𝓝[<] t)
      (𝓝 (Function.leftLim (F k) t)))
    (t : Time) :
    Tendsto (fun k => Function.leftLim (F k) t) atTop
      (𝓝 (Function.leftLim f t)) := by
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simpa only [leftLim_eq_of_eq_bot (F _) hbot,
      leftLim_eq_of_eq_bot f hbot] using hUniform.tendsto_at t
  let L : ℕ → ℝ := fun k => Function.leftLim (F k) t
  have hLCauchy : CauchySeq L := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    have hHalf : 0 < epsilon / 2 := by positivity
    have hUniformCauchy : UniformCauchySeqOn F atTop Set.univ :=
      hUniform.tendstoUniformlyOn.uniformCauchySeqOn
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp
      hUniformCauchy (epsilon / 2) hHalf
    refine ⟨N, fun m hm n hn => ?_⟩
    have hDistance : Tendsto (fun s => dist (F m s) (F n s))
        (𝓝[<] t) (𝓝 (dist (L m) (L n))) := by
      exact (hLeft m t).dist (hLeft n t)
    have hBound : dist (L m) (L n) ≤ epsilon / 2 :=
      le_of_tendsto hDistance (Filter.Eventually.of_forall fun s =>
        (hN m hm n hn s (Set.mem_univ s)).le)
    exact hBound.trans_lt (half_lt_self hepsilon)
  have hL : Tendsto L atTop (𝓝 (limUnder atTop L)) :=
    hLCauchy.tendsto_limUnder
  have hfLimit : Tendsto f (𝓝[<] t) (𝓝 (limUnder atTop L)) :=
    hUniform.tendsto_of_eventually_tendsto
      (Filter.Eventually.of_forall fun k => hLeft k t) hL
  have hfLeft : Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) :=
    leftLimits_of_tendstoUniformly F f hUniform hLeft t
  have hEq : limUnder atTop L = Function.leftLim f t :=
    tendsto_nhds_unique hfLimit hfLeft
  simpa only [L, hEq] using hL

end FTAPTheorem42

/-! ## Path regularity of locally uniform limits -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

/-- Local uniform convergence preserves both right continuity and left
limits. Clamping to a finite horizon reduces this to uniform convergence. -/
theorem cadlag_of_locallyUniform_limit
    (X : Nat → NNReal → Real) (Y : NNReal → Real)
    (hU : ∀ T, TendstoUniformlyOn X Y atTop (Iic T))
    (hR : ∀ n t, ContinuousWithinAt (X n) (Ici t) t)
    (hL : ∀ n t, Tendsto (X n) (𝓝[<] t) (𝓝 (Function.leftLim (X n) t))) :
    (∀ t, ContinuousWithinAt Y (Ici t) t) ∧
      ∀ t, Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)) := by
  have hClamp (T : NNReal) : TendstoUniformly
      (fun n s => X n (min s T)) (fun s => Y (min s T)) atTop := by
    apply tendstoUniformlyOn_univ.mp
    exact ((hU T).comp (fun s => min s T)).mono (fun s _ => min_le_right s T)
  have hClampR (T : NNReal) : ∀ t,
      ContinuousWithinAt (fun s => Y (min s T)) (Ici t) t :=
    rightContinuous_of_tendstoUniformly _ _ (hClamp T)
      (fun n t => FiniteVariationStoppedPath.rightContinuous_stopAt (X n) (hR n) T t)
  have hClampL (T : NNReal) : ∀ t, Tendsto (fun s => Y (min s T)) (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => Y (min s T)) t)) := by
    apply leftLimits_of_tendstoUniformly _ _ (hClamp T)
    intro n t
    have h : ProcessHasLeftLimits (fun s (_ : Unit) => X n s) := fun _ => hL n
    simpa only [stoppedProcess, stoppedValue, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using
      h.stoppedProcess (fun _ => (T : WithTop NNReal)) () t
  have hEq (t : NNReal) : Y =ᶠ[𝓝 t] (fun s => Y (min s (t + 1))) := by
    filter_upwards [Iio_mem_nhds (show t < t + 1 by simp)] with s hs
    rw [min_eq_left hs.le]
  constructor
  · intro t
    exact (hClampR (t + 1) t).congr_of_eventuallyEq
      ((hEq t).filter_mono nhdsWithin_le_nhds) (by rw [min_eq_left (by simp)])
  · intro t
    apply tendsto_leftLim_of_tendsto
    exact ⟨_, (hClampL (t + 1) t).congr'
      ((hEq t).filter_mono nhdsWithin_le_nhds).symm⟩

end FTAPTheorem42
