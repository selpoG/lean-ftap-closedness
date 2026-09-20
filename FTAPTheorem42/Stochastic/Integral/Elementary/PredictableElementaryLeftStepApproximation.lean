/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcessCompletion
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridPredictableElementaryStrategy
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct

/-!
# Left-step approximation of predictable elementary integrands

The raw integrand of a predictable elementary block uses the half-open
interval `(start, stop]`.  It is therefore left-continuous in time on every
sample path.  Factorial approximation from the left consequently converges
pointwise to the original elementary integrand.

For a deterministically bounded elementary integrand and any finite
predictable control, dominated convergence upgrades this fact to `L¹`
convergence.  This is the finite-variation estimate needed before realizing
the left steps on strict chronological grids.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryInterval

/-- The half-open raw integrand of one predictable elementary block is
left-continuous on every sample path. -/
theorem continuousWithinAt_integrand_Iic
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt (B.integrand · omega) (Iic t) t := by
  by_cases hActive :
      B.interval.startTime omega < t ∧ t ≤ B.interval.stopTime omega
  · have hEventually : ∀ᶠ u in 𝓝[Iic t] t,
        B.integrand u omega = B.interval.coefficient omega := by
      filter_upwards
        [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hActive.1),
          self_mem_nhdsWithin] with u hu hule
      have hStartU : B.interval.startTime omega < u := hu
      have hUStop : u ≤ B.interval.stopTime omega :=
        hule.trans hActive.2
      simp [PredictableElementaryInterval.integrand, hStartU, hUStop]
    apply continuousWithinAt_const.congr_of_eventuallyEq hEventually
    simp [PredictableElementaryInterval.integrand, hActive]
  · by_cases hBefore : t ≤ B.interval.startTime omega
    · have hEventually : ∀ᶠ u in 𝓝[Iic t] t,
          B.integrand u omega = 0 := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hNotStart : ¬ B.interval.startTime omega < u :=
          not_lt_of_ge (hu.trans hBefore)
        simp [PredictableElementaryInterval.integrand, hNotStart]
      apply continuousWithinAt_const.congr_of_eventuallyEq hEventually
      have hNotStart : ¬ B.interval.startTime omega < t :=
        not_lt_of_ge hBefore
      simp [PredictableElementaryInterval.integrand, hNotStart]
    · have hStart : B.interval.startTime omega < t :=
        lt_of_not_ge hBefore
      have hAfter : B.interval.stopTime omega < t := by
        exact lt_of_not_ge fun htStop => hActive ⟨hStart, htStop⟩
      have hEventually : ∀ᶠ u in 𝓝[Iic t] t,
          B.integrand u omega = 0 := by
        filter_upwards
          [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hAfter)] with u hu
        have hNotStop : ¬ u ≤ B.interval.stopTime omega :=
          not_le_of_gt hu
        simp [PredictableElementaryInterval.integrand, hNotStop]
      apply continuousWithinAt_const.congr_of_eventuallyEq hEventually
      have hNotStop : ¬ t ≤ B.interval.stopTime omega :=
        not_le_of_gt hAfter
      simp [PredictableElementaryInterval.integrand, hNotStop]

end PredictableElementaryInterval

namespace LeftContinuousPredictable

/-- The first `N + 1` points of the level-`r` left factorial mesh, ordered
chronologically. -/
noncomputable def finiteGrid (r N : Nat) : ChronologicalGrid NNReal N where
  time k := gridPoint r k
  monotone_time := by
    intro k l hkl
    unfold gridPoint
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) (by positivity)

/-- Natural sampling within the finite mesh does not clamp an index which is
already below the last grid point. -/
theorem finiteGrid_sampledTime_eq
    (r N k : Nat) (hk : k ≤ N) :
    (finiteGrid r N).sampledTime k = gridPoint r k := by
  simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
    finiteGrid, min_eq_left hk]

/-- Number of left-factorial cells needed to cover a deterministic horizon. -/
noncomputable def horizonCellCount (r : Nat) (T : NNReal) : Nat :=
  Nat.ceil (T * (denominator r : NNReal))

/-- The last mesh point selected by `horizonCellCount` covers the requested
horizon. -/
theorem le_gridPoint_horizonCellCount (r : Nat) (T : NNReal) :
    T ≤ gridPoint r (horizonCellCount r T) := by
  have hd : (0 : NNReal) < (denominator r : NNReal) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  rw [gridPoint, horizonCellCount, le_div_iff₀ hd]
  exact_mod_cast Nat.le_ceil (T * (denominator r : NNReal))

end LeftContinuousPredictable

namespace ChronologicalGrid

/-- A uniform bound on a coefficient process gives the expected finite
bound on the absolute coefficient sum of its chronological grid strategy. -/
theorem coefficientAbsSum_predictableElementaryStrategy_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K : Process Omega) (hK : IsStronglyPredictable F K)
    (C : NNReal) (hBound : ∀ t omega, |K t omega| ≤ (C : Real))
    (omega : Omega) :
    (G.predictableElementaryStrategy K hK).coefficientAbsSum omega ≤
      (N : Real) * (C : Real) := by
  unfold predictableElementaryStrategy
    PredictableElementaryStrategy.coefficientAbsSum
  simp only [List.map_map]
  calc
    ((List.range N).map fun k =>
        |K (G.sampledTime k) omega|).sum ≤
        ((List.range N).map fun _ => (C : Real)).sum := by
      exact List.sum_le_sum fun k _ => hBound (G.sampledTime k) omega
    _ = (N : Real) * (C : Real) := by simp

omit [MeasurableSpace Omega] in
/-- On one block of a chronological grid, the finite left-step process is
exactly its left-endpoint coefficient. -/
theorem predictableStepProcess_eq_of_mem_Ioc
    {N : Nat} (G : ChronologicalGrid NNReal N) (K : Process Omega)
    {k : Nat} (hk : k < N) {t : NNReal}
    (ht : t ∈ Ioc (G.sampledTime k) (G.sampledTime (k + 1))) :
    G.predictableStepProcess K t = K (G.sampledTime k) := by
  funext omega
  unfold predictableStepProcess deterministicIntervalCoefficient
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp [ht]
  · intro j hj hjne
    have hnot : t ∉ Ioc (G.sampledTime j) (G.sampledTime (j + 1)) := by
      rw [Finset.mem_range] at hj
      intro hmem
      rcases lt_or_gt_of_ne hjne with hjk | hkj
      · have hEndLe : G.sampledTime (j + 1) ≤ G.sampledTime k :=
          G.sampledTime_mono (Nat.succ_le_of_lt hjk)
        exact (not_le_of_gt (hEndLe.trans_lt ht.1)) hmem.2
      · have hStartGe : G.sampledTime (k + 1) ≤ G.sampledTime j :=
          G.sampledTime_mono (Nat.succ_le_of_lt hkj)
        exact (not_lt_of_ge (ht.2.trans hStartGe)) hmem.1
    simp [hnot]
  · simp [hk]

end ChronologicalGrid

namespace PredictableElementaryStrategy

/-- A finite predictable elementary integrand is pathwise left-continuous. -/
theorem continuousWithinAt_integrand_Iic
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (omega : Omega) (t : NNReal) :
    ContinuousWithinAt (H.integrand · omega) (Iic t) t := by
  induction H with
  | nil =>
      change ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Iic t) t
      exact continuousWithinAt_const
  | cons B H ih =>
      change ContinuousWithinAt
        (fun u => B.integrand u omega +
          PredictableElementaryStrategy.integrand H u omega) (Iic t) t
      exact (B.continuousWithinAt_integrand_Iic omega t).add ih

/-- The canonical left-factorial steps of an elementary integrand converge
pointwise to that integrand. -/
theorem tendsto_leftStep_integrand
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (t : NNReal) (omega : Omega) :
    Tendsto
      (fun r => LeftContinuousPredictable.step r H.integrand t omega)
      atTop (nhds (H.integrand t omega)) := by
  apply (H.continuousWithinAt_integrand_Iic omega t).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨LeftContinuousPredictable.tendsto_approx t,
    Filter.Eventually.of_forall fun r =>
      LeftContinuousPredictable.approx_le r t⟩

/-- Every predictable elementary integrand vanishes at the initial time. -/
theorem integrand_zero
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) :
    H.integrand 0 = 0 := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change B.integrand 0 +
        PredictableElementaryStrategy.integrand H 0 = 0
      rw [ih]
      funext omega
      simp [PredictableElementaryInterval.integrand]

/-- The finite factorial-grid step process agrees with the canonical
left-factorial step throughout its covered time interval. -/
theorem finiteGrid_predictableStepProcess_eq_leftStep
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r N : Nat) {t : NNReal}
    (ht : t ≤ LeftContinuousPredictable.gridPoint r N) :
    (LeftContinuousPredictable.finiteGrid r N).predictableStepProcess
        H.integrand t =
      LeftContinuousPredictable.step r H.integrand t := by
  by_cases ht0 : t = 0
  · subst t
    have hStepZero :
        LeftContinuousPredictable.step r H.integrand 0 = 0 := by
      unfold LeftContinuousPredictable.step LeftContinuousPredictable.approx
        LeftContinuousPredictable.leftIndex LeftContinuousPredictable.gridPoint
      simpa using H.integrand_zero
    rw [hStepZero]
    funext omega
    unfold ChronologicalGrid.predictableStepProcess
      ChronologicalGrid.deterministicIntervalCoefficient
    simp
  · obtain ⟨k, hk⟩ :=
      LeftContinuousPredictable.exists_mem_Ioc_gridPoint ht0 r
    have hkN : k < N := by
      by_contra hnot
      have hNk : N ≤ k := Nat.le_of_not_gt hnot
      have hGridLe :
          LeftContinuousPredictable.gridPoint r N ≤
            LeftContinuousPredictable.gridPoint r k := by
        unfold LeftContinuousPredictable.gridPoint
        exact div_le_div_of_nonneg_right (by exact_mod_cast hNk) bot_le
      exact (not_lt_of_ge ht) (hGridLe.trans_lt hk.1)
    have hBlock :
        (LeftContinuousPredictable.finiteGrid r N).predictableStepProcess
            H.integrand t =
          H.integrand
            ((LeftContinuousPredictable.finiteGrid r N).sampledTime k) := by
      apply ChronologicalGrid.predictableStepProcess_eq_of_mem_Ioc
        (LeftContinuousPredictable.finiteGrid r N) H.integrand hkN
      simpa only [LeftContinuousPredictable.finiteGrid_sampledTime_eq
          r N k hkN.le,
        LeftContinuousPredictable.finiteGrid_sampledTime_eq
          r N (k + 1) hkN] using hk
    rw [hBlock,
      LeftContinuousPredictable.finiteGrid_sampledTime_eq r N k hkN.le,
      LeftContinuousPredictable.step_eq_of_mem_Ioc H.integrand hk]

/-- The concrete finite chronological strategy whose integrand is the
left-factorial step on the first `N` mesh cells. -/
noncomputable def finiteLeftStepStrategy
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r N : Nat) :
    PredictableElementaryStrategy F :=
  (LeftContinuousPredictable.finiteGrid r N).predictableElementaryStrategy
    H.integrand H.integrand_isStronglyPredictable

/-- On its covered interval, the actual finite chronological strategy has
exactly the canonical left-factorial step as its raw integrand. -/
theorem finiteLeftStepStrategy_integrand_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r N : Nat) {t : NNReal}
    (ht : t ≤ LeftContinuousPredictable.gridPoint r N) :
    (H.finiteLeftStepStrategy r N).integrand t =
      LeftContinuousPredictable.step r H.integrand t := by
  rw [finiteLeftStepStrategy,
    ChronologicalGrid.predictableElementaryStrategy_integrand]
  exact H.finiteGrid_predictableStepProcess_eq_leftStep r N ht

/-- A finite chronological left-step strategy whose last grid point covers
the deterministic horizon `T`. -/
noncomputable def horizonLeftStepStrategy
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r : Nat) (T : NNReal) :
    PredictableElementaryStrategy F :=
  H.finiteLeftStepStrategy r
    (LeftContinuousPredictable.horizonCellCount r T)

/-- The horizon-covering actual strategy agrees with the canonical left step
at every time up to that horizon. -/
theorem horizonLeftStepStrategy_integrand_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r : Nat) (T : NNReal)
    {t : NNReal} (ht : t ≤ T) :
    (H.horizonLeftStepStrategy r T).integrand t =
      LeftContinuousPredictable.step r H.integrand t := by
  apply H.finiteLeftStepStrategy_integrand_eq
  exact ht.trans
    (LeftContinuousPredictable.le_gridPoint_horizonCellCount r T)

/-- Every horizon-covering left-grid strategy has a deterministic absolute
coefficient-sum bound inherited from the original elementary strategy. -/
theorem horizonLeftStepStrategy_coefficientAbsSum_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (r : Nat) (T : NNReal)
    (C : NNReal) (hCoefficient : ∀ omega,
      H.coefficientAbsSum omega ≤ C) (omega : Omega) :
    (H.horizonLeftStepStrategy r T).coefficientAbsSum omega ≤
      ((LeftContinuousPredictable.horizonCellCount r T : Nat) : Real) *
        (C : Real) := by
  apply ChronologicalGrid.coefficientAbsSum_predictableElementaryStrategy_le
  intro t omega'
  exact (H.abs_integrand_le_coefficientAbsSum t omega').trans
    (by exact_mod_cast hCoefficient omega')

end PredictableElementaryStrategy

end FTAPTheorem42
