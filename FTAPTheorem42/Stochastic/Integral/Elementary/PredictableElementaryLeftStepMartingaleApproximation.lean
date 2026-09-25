/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepApproximation
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct

/-!
# Martingale gains of chronological left-step approximations

For one predictable elementary block, sampling its half-open integrand on a
deterministic left factorial grid produces a telescoping martingale increment.
Its endpoints are the first grid points strictly to the right of the original
stopping times, clipped at the deterministic horizon.  Right continuity then
identifies the pathwise limit with the original elementary gain.

Finite additivity upgrades this calculation to every predictable elementary
strategy.  Thus the chronological strategies constructed in
`PredictableElementaryLeftStepApproximation` approximate not only the raw
integrand under finite-variation controls, but also the actual martingale gain
at each deterministic horizon.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LeftContinuousPredictable

/-- Index of the first level-`r` grid point strictly to the right of `t`. -/
noncomputable def rightIndex (r : Nat) (t : NNReal) : Nat :=
  Nat.floor (t * (denominator r : NNReal)) + 1

/-- The first level-`r` grid point strictly to the right of `t`. -/
noncomputable def strictRightApprox (r : Nat) (t : NNReal) : NNReal :=
  gridPoint r (rightIndex r t)

/-- A grid point is strictly after `t` exactly when its index is at least the
strict right index of `t`. -/
theorem lt_gridPoint_iff_rightIndex_le (r k : Nat) (t : NNReal) :
    t < gridPoint r k ↔ rightIndex r t ≤ k := by
  have hd : (0 : NNReal) < (denominator r : NNReal) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  rw [gridPoint, lt_div_iff₀ hd]
  change t * (denominator r : NNReal) < (k : NNReal) ↔
    Nat.floor (t * (denominator r : NNReal)) + 1 ≤ k
  rw [Nat.add_one_le_iff]
  exact (Nat.floor_lt bot_le).symm

/-- A grid point lies at or before `t` exactly when its index is below the
strict right index of `t`. -/
theorem gridPoint_le_iff_lt_rightIndex (r k : Nat) (t : NNReal) :
    gridPoint r k ≤ t ↔ k < rightIndex r t := by
  have hd : (0 : NNReal) < (denominator r : NNReal) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  rw [gridPoint, div_le_iff₀ hd]
  change (k : NNReal) ≤ t * (denominator r : NNReal) ↔
    k < Nat.floor (t * (denominator r : NNReal)) + 1
  rw [Nat.lt_succ_iff, Nat.le_floor_iff bot_le]

/-- Strict right indices preserve the order of their target times. -/
theorem rightIndex_mono (r : Nat) : Monotone (rightIndex r) := by
  intro s t hst
  unfold rightIndex
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hst bot_le

/-- The strict right approximation is no more than one mesh beyond its
target. -/
theorem strictRightApprox_le_add_inv (r : Nat) (t : NNReal) :
    strictRightApprox r t ≤ t + (denominator r : NNReal)⁻¹ := by
  have hd : (0 : NNReal) < (denominator r : NNReal) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  rw [strictRightApprox, gridPoint, div_le_iff₀ hd]
  simp only [rightIndex, Nat.cast_add, Nat.cast_one]
  change (Nat.floor (t * (denominator r : NNReal)) : NNReal) + 1 ≤
    (t + (denominator r : NNReal)⁻¹) * (denominator r : NNReal)
  calc
    (Nat.floor (t * (denominator r : NNReal)) : NNReal) + 1 ≤
        t * (denominator r : NNReal) + 1 :=
      add_le_add (Nat.floor_le bot_le) le_rfl
    _ = (t + (denominator r : NNReal)⁻¹) *
        (denominator r : NNReal) := by
      rw [add_mul, inv_mul_cancel₀ hd.ne']

/-- Strict right approximations converge to their target. -/
theorem tendsto_strictRightApprox (t : NNReal) :
    Tendsto (fun r => strictRightApprox r t) atTop (nhds t) := by
  have hdenom : Tendsto (fun r : Nat => (denominator r : NNReal))
      atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    have hadd : Tendsto (fun r : Nat => r + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro n
      filter_upwards [eventually_ge_atTop n] with r hr
      exact hr.trans (Nat.le_succ r)
    change Tendsto (fun r : Nat => (r + 1).factorial) atTop atTop
    exact factorial_tendsto_atTop.comp hadd
  have hinv : Tendsto (fun r : Nat => (denominator r : NNReal)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hdenom
  have hupper : Tendsto
      (fun r : Nat => t + (denominator r : NNReal)⁻¹)
      atTop (nhds t) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun r =>
      (lt_gridPoint_iff_rightIndex_le r (rightIndex r t) t).2 le_rfl |>.le
  · exact Filter.Eventually.of_forall fun r =>
      strictRightApprox_le_add_inv r t

/-- Clipping the strict right approximation through the finite horizon grid
has the same value as clipping it directly at the horizon. -/
theorem min_gridPoint_min_rightIndex_horizonCellCount
    (r : Nat) (T t : NNReal) :
    min T (gridPoint r
      (min (rightIndex r t) (horizonCellCount r T))) =
      min T (strictRightApprox r t) := by
  by_cases hIndex : rightIndex r t ≤ horizonCellCount r T
  · rw [min_eq_left hIndex]
    rfl
  · have hCountLe : horizonCellCount r T ≤ rightIndex r t :=
      le_of_not_ge hIndex
    rw [min_eq_right hCountLe]
    have hLastLe : gridPoint r (horizonCellCount r T) ≤
        gridPoint r (rightIndex r t) := by
      unfold gridPoint
      exact div_le_div_of_nonneg_right (by exact_mod_cast hCountLe) bot_le
    have hTLeLast := le_gridPoint_horizonCellCount r T
    rw [min_eq_left hTLeLast]
    change T = min T (gridPoint r (rightIndex r t))
    rw [
      min_eq_left (hTLeLast.trans hLastLe)]

end LeftContinuousPredictable

omit [MeasurableSpace Omega] in
/-- A finite interval of nonzero increments telescopes after truncating both
endpoint indices at `N`. -/
theorem sum_range_interval_increment
    (x : Nat → Real) (c : Real) {a b N : Nat} (hab : a ≤ b) :
    (∑ k ∈ Finset.range N,
      (if a ≤ k ∧ k < b then c else 0) * (x (k + 1) - x k)) =
      c * (x (min b N) - x (min a N)) := by
  classical
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range N).filter (fun k => a ≤ k ∧ k < b) =
        Finset.Ico (min a N) (min b N) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter, ← Finset.mul_sum]
  have hmin : min a N ≤ min b N := min_le_min_right N hab
  rw [Finset.sum_Ico_eq_sub _ hmin,
    Finset.sum_range_sub, Finset.sum_range_sub]
  ring

namespace PredictableElementaryInterval

/-- The finite-grid transform of one elementary block is the block
coefficient times the martingale increment between its clipped strict-right
endpoint approximations. -/
theorem finiteGrid_martingaleIntegralProcess_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (r N : Nat) (T : NNReal) (omega : Omega) :
    (LeftContinuousPredictable.finiteGrid r N).martingaleIntegralProcess
        B.integrand M T omega =
      B.interval.coefficient omega *
        (M (min T (LeftContinuousPredictable.gridPoint r
            (min (LeftContinuousPredictable.rightIndex r
              (B.interval.stopTime omega)) N))) omega -
          M (min T (LeftContinuousPredictable.gridPoint r
            (min (LeftContinuousPredictable.rightIndex r
              (B.interval.startTime omega)) N))) omega) := by
  classical
  let a := LeftContinuousPredictable.rightIndex r
    (B.interval.startTime omega)
  let b := LeftContinuousPredictable.rightIndex r
    (B.interval.stopTime omega)
  let x : Nat → Real := fun k =>
    M (min T (LeftContinuousPredictable.gridPoint r k)) omega
  have hab : a ≤ b :=
    LeftContinuousPredictable.rightIndex_mono r
      (B.interval.start_le_stop omega)
  have hsum :
      (LeftContinuousPredictable.finiteGrid r N).martingaleIntegralProcess
          B.integrand M T omega =
        ∑ k ∈ Finset.range N,
          (if a ≤ k ∧ k < b then B.interval.coefficient omega else 0) *
            (x (k + 1) - x k) := by
    unfold ChronologicalGrid.martingaleIntegralProcess
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [deterministicIntervalMartingaleTransform,
      stoppedProcess_const_apply]
    rw [LeftContinuousPredictable.finiteGrid_sampledTime_eq r N k hk.le,
      LeftContinuousPredictable.finiteGrid_sampledTime_eq r N (k + 1) hk]
    change B.integrand (LeftContinuousPredictable.gridPoint r k) omega *
        (x (k + 1) - x k) = _
    rw [PredictableElementaryInterval.integrand]
    simp only [LeftContinuousPredictable.lt_gridPoint_iff_rightIndex_le,
      LeftContinuousPredictable.gridPoint_le_iff_lt_rightIndex, a, b]
  rw [hsum, sum_range_interval_increment x
    (B.interval.coefficient omega) hab]

/-- At a horizon-covering grid, the preceding identity uses direct clipping
of the strict-right time approximations. -/
theorem horizonGrid_martingaleIntegralProcess_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (r : Nat) (T : NNReal) (omega : Omega) :
    (LeftContinuousPredictable.finiteGrid r
      (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
        B.integrand M T omega =
      B.interval.coefficient omega *
        (M (min T (LeftContinuousPredictable.strictRightApprox r
            (B.interval.stopTime omega))) omega -
          M (min T (LeftContinuousPredictable.strictRightApprox r
            (B.interval.startTime omega))) omega) := by
  rw [B.finiteGrid_martingaleIntegralProcess_eq M r
    (LeftContinuousPredictable.horizonCellCount r T) T omega,
    LeftContinuousPredictable.min_gridPoint_min_rightIndex_horizonCellCount,
    LeftContinuousPredictable.min_gridPoint_min_rightIndex_horizonCellCount]

/-- Right continuity makes the horizon-grid transform of one elementary
block converge pathwise to its actual gain at that horizon. -/
theorem tendsto_horizonGrid_martingaleIntegralProcess
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (omega : Omega) :
    Tendsto
      (fun r =>
        (LeftContinuousPredictable.finiteGrid r
          (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
            B.integrand M T omega)
      atTop (nhds (B.interval.gain M T omega)) := by
  have hTime (s : NNReal) : Tendsto
      (fun r => min T (LeftContinuousPredictable.strictRightApprox r s))
      atTop (nhds (min T s)) := by
    exact tendsto_const_nhds.min
      (LeftContinuousPredictable.tendsto_strictRightApprox s)
  have hSample (s : NNReal) : Tendsto
      (fun r => M (min T
        (LeftContinuousPredictable.strictRightApprox r s)) omega)
      atTop (nhds (M (min T s) omega)) := by
    apply (hMRight omega (min T s)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hTime s, Filter.Eventually.of_forall fun r =>
      min_le_min le_rfl
        ((LeftContinuousPredictable.lt_gridPoint_iff_rightIndex_le
          r (LeftContinuousPredictable.rightIndex r s) s).2 le_rfl).le⟩
  rw [show (fun r =>
      (LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
          B.integrand M T omega) =
      fun r => B.interval.coefficient omega *
        (M (min T (LeftContinuousPredictable.strictRightApprox r
            (B.interval.stopTime omega))) omega -
          M (min T (LeftContinuousPredictable.strictRightApprox r
            (B.interval.startTime omega))) omega) by
    funext r
    exact B.horizonGrid_martingaleIntegralProcess_eq M r T omega]
  exact tendsto_const_nhds.mul
    ((hSample (B.interval.stopTime omega)).sub
      (hSample (B.interval.startTime omega)))

end PredictableElementaryInterval

namespace ChronologicalGrid

omit [MeasurableSpace Omega] in
/-- The finite-grid transform of the zero coefficient process is zero. -/
@[simp]
theorem martingaleIntegralProcess_zero
    {N : Nat} (G : ChronologicalGrid NNReal N) (M : Process Omega) :
    G.martingaleIntegralProcess 0 M = 0 := by
  funext t omega
  unfold martingaleIntegralProcess
    deterministicIntervalMartingaleTransform
  simp

omit [MeasurableSpace Omega] in
/-- The finite-grid transform is additive in its coefficient process. -/
theorem martingaleIntegralProcess_add
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K L M : Process Omega) :
    G.martingaleIntegralProcess (K + L) M =
      G.martingaleIntegralProcess K M +
        G.martingaleIntegralProcess L M := by
  funext t omega
  unfold martingaleIntegralProcess
    deterministicIntervalMartingaleTransform
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end ChronologicalGrid

/-- Pointwise convergence with one `L²` dominator implies convergence in the
`L²` seminorm.  This is the squared dominated-convergence form used for the
elementary martingale gains below. -/
theorem tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    {mu : Measure Omega}
    {f : Nat → Omega → Real} {g B : Omega → Real}
    (hf : ∀ n, AEStronglyMeasurable (f n) mu)
    (hg : AEStronglyMeasurable g mu)
    (hB : MemLp B (2 : ENNReal) mu)
    (hBound : ∀ n, ∀ᵐ omega ∂mu,
      ‖f n omega - g omega‖ ≤ ‖B omega‖)
    (hTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n => f n omega) atTop (nhds (g omega))) :
    Tendsto (fun n => eLpNorm (f n - g) (2 : ENNReal) mu)
      atTop (nhds 0) := by
  let errorSq : Nat → Omega → Real := fun n omega =>
    (f n omega - g omega) ^ 2
  have hErrorMeas : ∀ n, AEStronglyMeasurable (errorSq n) mu := by
    intro n
    exact ((hf n).sub hg).pow 2
  have hBoundIntegral : HasFiniteIntegral
      (fun omega => ‖B omega‖ ^ 2) mu :=
    (hB.integrable_norm_pow (by norm_num)).hasFiniteIntegral
  have hErrorBound : ∀ n, ∀ᵐ omega ∂mu,
      ‖errorSq n omega‖ ≤ ‖B omega‖ ^ 2 := by
    intro n
    filter_upwards [hBound n] with omega homega
    simp only [errorSq, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) homega 2
  have hErrorTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n => errorSq n omega) atTop (nhds 0) := by
    filter_upwards [hTendsto] with omega homega
    have hzero : Tendsto (fun n => f n omega - g omega)
        atTop (nhds 0) := by
      simpa using homega.sub_const (g omega)
    simpa only [errorSq, zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
      hzero.pow 2
  have hIntegral := tendsto_lintegral_norm_of_dominated_convergence
    hErrorMeas hBoundIntegral hErrorBound hErrorTendsto
  have hIntegral' : Tendsto
      (fun n => ∫⁻ omega, ‖f n omega - g omega‖ₑ ^ 2 ∂mu)
      atTop (nhds 0) := by
    convert hIntegral using 1
    ext n
    apply lintegral_congr
    intro omega
    dsimp only [errorSq]
    rw [sub_zero, ofReal_norm, enorm_pow]
  have hPow := hIntegral'.ennrpow_const (1 / 2 : Real)
  have hPow' : Tendsto
      (fun n => (∫⁻ omega, ‖f n omega - g omega‖ₑ ^ 2 ∂mu) ^
        (1 / 2 : Real)) atTop (nhds 0) := by
    simpa only [ENNReal.zero_rpow_of_pos
      (show (0 : Real) < 1 / 2 by norm_num)] using hPow
  apply hPow'.congr'
  exact Filter.Eventually.of_forall fun n => by
    change (∫⁻ omega, ‖f n omega - g omega‖ₑ ^ 2 ∂mu) ^
        (1 / 2 : Real) = eLpNorm (f n - g) (2 : ENNReal) mu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (show (2 : ENNReal) ≠ 0 by norm_num)
      (show (2 : ENNReal) ≠ ∞ by norm_num) ((hf n).sub hg)]
    norm_num only [ENNReal.toReal_ofNat, Pi.sub_apply]
    congr 2
    funext omega
    exact (ENNReal.rpow_natCast _ 2).symm

namespace PredictableElementaryStrategy

/-- The horizon-grid transforms of an elementary integrand converge
pathwise to the actual elementary gain. -/
theorem tendsto_horizonGrid_martingaleIntegralProcess
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (omega : Omega) :
    Tendsto
      (fun r =>
        (LeftContinuousPredictable.finiteGrid r
          (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
            H.integrand M T omega)
      atTop (nhds (ElementaryStrategy.gain M H.toElementary T omega)) := by
  induction H with
  | nil =>
      simp [PredictableElementaryStrategy.integrand,
        PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons B H ih =>
      have hAdd (r : Nat) :
          (LeftContinuousPredictable.finiteGrid r
            (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
              (B.integrand +
                PredictableElementaryStrategy.integrand H) M =
            (LeftContinuousPredictable.finiteGrid r
              (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
                B.integrand M +
            (LeftContinuousPredictable.finiteGrid r
              (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
                (PredictableElementaryStrategy.integrand H) M :=
        ChronologicalGrid.martingaleIntegralProcess_add _ _ _ _
      change Tendsto
        (fun r =>
          (LeftContinuousPredictable.finiteGrid r
            (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
              (B.integrand +
                PredictableElementaryStrategy.integrand H) M T omega)
        atTop (nhds (B.interval.gain M T omega +
          ElementaryStrategy.gain M
            (PredictableElementaryStrategy.toElementary (ℱ := F) H)
            T omega))
      apply ((B.tendsto_horizonGrid_martingaleIntegralProcess
        M hMRight T omega).add ih).congr'
      exact Filter.Eventually.of_forall fun r =>
        (congrFun (congrFun (hAdd r) T) omega).symm

/-- A common pathwise envelope for `M` up to `T` controls every horizon-grid
transform by the absolute block-coefficient sum. -/
theorem norm_horizonGrid_martingaleIntegralProcess_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (T : NNReal) (omega : Omega) (E : Real)
    (hM : ∀ t, t ≤ T → ‖M t omega‖ ≤ E) (r : Nat) :
    ‖(LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
          H.integrand M T omega‖ ≤
      2 * H.coefficientAbsSum omega * E := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.integrand, coefficientAbsSum]
  | cons B H ih =>
      let G := LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)
      have hAdd := ChronologicalGrid.martingaleIntegralProcess_add
        G B.integrand (PredictableElementaryStrategy.integrand H) M
      have hBlock :
          ‖G.martingaleIntegralProcess B.integrand M T omega‖ ≤
            2 * |B.interval.coefficient omega| * E := by
        rw [B.horizonGrid_martingaleIntegralProcess_eq M r T omega]
        calc
          ‖B.interval.coefficient omega *
              (M (min T (LeftContinuousPredictable.strictRightApprox r
                  (B.interval.stopTime omega))) omega -
                M (min T (LeftContinuousPredictable.strictRightApprox r
                  (B.interval.startTime omega))) omega)‖ =
              ‖B.interval.coefficient omega‖ *
                ‖M (min T (LeftContinuousPredictable.strictRightApprox r
                    (B.interval.stopTime omega))) omega -
                  M (min T (LeftContinuousPredictable.strictRightApprox r
                    (B.interval.startTime omega))) omega‖ := norm_mul _ _
          _ ≤ ‖B.interval.coefficient omega‖ * (E + E) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (norm_sub_le _ _).trans (add_le_add
              (hM _ (min_le_left _ _)) (hM _ (min_le_left _ _)))
          _ = 2 * |B.interval.coefficient omega| * E := by
            rw [Real.norm_eq_abs]
            ring
      change ‖G.martingaleIntegralProcess
          (B.integrand + PredictableElementaryStrategy.integrand H)
          M T omega‖ ≤ _
      rw [congrFun (congrFun hAdd T) omega]
      calc
        ‖G.martingaleIntegralProcess B.integrand M T omega +
            G.martingaleIntegralProcess
              (PredictableElementaryStrategy.integrand H) M T omega‖ ≤
            ‖G.martingaleIntegralProcess B.integrand M T omega‖ +
              ‖G.martingaleIntegralProcess
                (PredictableElementaryStrategy.integrand H) M T omega‖ :=
          norm_add_le _ _
        _ ≤ 2 * |B.interval.coefficient omega| * E +
            2 * coefficientAbsSum H omega * E := add_le_add hBlock ih
        _ = 2 * coefficientAbsSum (B :: H) omega * E := by
          simp only [coefficientAbsSum, List.map_cons, List.sum_cons]
          ring

/-- The same envelope controls the original actual elementary gain. -/
theorem norm_gain_le_coefficientAbsSum_mul
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (T : NNReal) (omega : Omega) (E : Real)
    (hM : ∀ t, t ≤ T → ‖M t omega‖ ≤ E) :
    ‖ElementaryStrategy.gain M H.toElementary T omega‖ ≤
      2 * H.coefficientAbsSum omega * E := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.toElementary,
      ElementaryStrategy.gain, coefficientAbsSum]
  | cons B H ih =>
      have hBlock : ‖B.interval.gain M T omega‖ ≤
          2 * |B.interval.coefficient omega| * E := by
        unfold ElementaryInterval.gain
        calc
          ‖B.interval.coefficient omega *
              (M (min T (B.interval.stopTime omega)) omega -
                M (min T (B.interval.startTime omega)) omega)‖ =
              ‖B.interval.coefficient omega‖ *
                ‖M (min T (B.interval.stopTime omega)) omega -
                  M (min T (B.interval.startTime omega)) omega‖ :=
            norm_mul _ _
          _ ≤ ‖B.interval.coefficient omega‖ * (E + E) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (norm_sub_le _ _).trans (add_le_add
              (hM _ (min_le_left _ _)) (hM _ (min_le_left _ _)))
          _ = 2 * |B.interval.coefficient omega| * E := by
            rw [Real.norm_eq_abs]
            ring
      change ‖B.interval.gain M T omega +
          ElementaryStrategy.gain M
            (PredictableElementaryStrategy.toElementary (ℱ := F) H)
            T omega‖ ≤ _
      calc
        ‖B.interval.gain M T omega +
            ElementaryStrategy.gain M
              (PredictableElementaryStrategy.toElementary (ℱ := F) H)
              T omega‖ ≤
            ‖B.interval.gain M T omega‖ +
              ‖ElementaryStrategy.gain M
                (PredictableElementaryStrategy.toElementary (ℱ := F) H)
                T omega‖ := norm_add_le _ _
        _ ≤ 2 * |B.interval.coefficient omega| * E +
            2 * coefficientAbsSum H omega * E := add_le_add hBlock ih
        _ = 2 * coefficientAbsSum (B :: H) omega * E := by
          simp only [coefficientAbsSum, List.map_cons, List.sum_cons]
          ring

/-- The concrete horizon-covering chronological strategies have martingale
gains converging pathwise to the original actual elementary gain. -/
theorem horizonLeftStepStrategy_gain_tendsto
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (omega : Omega) :
    Tendsto
      (fun r => ElementaryStrategy.gain M
        (H.horizonLeftStepStrategy r T).toElementary T omega)
      atTop (nhds (ElementaryStrategy.gain M H.toElementary T omega)) := by
  have hLimit := H.tendsto_horizonGrid_martingaleIntegralProcess
    M hMRight T omega
  apply hLimit.congr'
  exact Filter.Eventually.of_forall fun r => by
    symm
    exact ChronologicalGrid.predictableElementaryStrategy_gain
      (LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T))
      H.integrand H.integrand_isStronglyPredictable M T omega

/-- If the absolute sum of the elementary block coefficients is uniformly
bounded, the same concrete chronological gains converge to the original
gain in terminal `L²` for every square-integrable right-continuous
martingale. -/
theorem horizonLeftStepStrategy_gain_tendsto_eLpNorm_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (C : NNReal) (hCoefficient : ∀ omega,
      H.coefficientAbsSum omega ≤ C) :
    Tendsto
      (fun r => eLpNorm
        (ElementaryStrategy.gain M
            (H.horizonLeftStepStrategy r T).toElementary T -
          ElementaryStrategy.gain M H.toElementary T)
        (2 : ENNReal) mu)
      atTop (nhds 0) := by
  let gain : Nat → Omega → Real := fun r =>
    ElementaryStrategy.gain M
      (H.horizonLeftStepStrategy r T).toElementary T
  let target : Omega → Real :=
    ElementaryStrategy.gain M H.toElementary T
  let envelope : Omega → Real :=
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope M T
  let bound : Omega → Real := fun omega =>
    4 * (C : Real) * envelope omega
  have hProgressive : IsStronglyProgressive F M :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hM.stronglyAdapted hMRight
  have hGainMeas : ∀ r, AEStronglyMeasurable (gain r) mu := by
    intro r
    exact ((((H.horizonLeftStepStrategy r T).stronglyAdapted_gain
      M hProgressive) T).mono (F.le T)).aestronglyMeasurable
  have hTargetMeas : AEStronglyMeasurable target mu :=
    (((H.stronglyAdapted_gain M hProgressive) T).mono
      (F.le T)).aestronglyMeasurable
  have hEnvelopeMem : MemLp envelope (2 : ENNReal) mu :=
    FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hM T hMT
  have hBoundMem : MemLp bound (2 : ENNReal) mu := by
    exact hEnvelopeMem.const_mul (4 * (C : Real))
  have hEnvelopeDominates : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ‖M t omega‖ ≤ envelope omega :=
    FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hM T hMT hMRight
  have hBound : ∀ r, ∀ᵐ omega ∂mu,
      ‖gain r omega - target omega‖ ≤ ‖bound omega‖ := by
    intro r
    filter_upwards [hEnvelopeDominates] with omega homega
    have hApprox := H.norm_horizonGrid_martingaleIntegralProcess_le
      M T omega (envelope omega) homega r
    have hApproxGain : ‖gain r omega‖ ≤
        2 * H.coefficientAbsSum omega * envelope omega := by
      change ‖ElementaryStrategy.gain M
        (PredictableElementaryStrategy.toElementary
          (ChronologicalGrid.predictableElementaryStrategy
            (LeftContinuousPredictable.finiteGrid r
              (LeftContinuousPredictable.horizonCellCount r T))
            H.integrand H.integrand_isStronglyPredictable)) T omega‖ ≤ _
      rw [ChronologicalGrid.predictableElementaryStrategy_gain]
      exact hApprox
    have hTarget := H.norm_gain_le_coefficientAbsSum_mul
      M T omega (envelope omega) homega
    have hEnvelopeNonnegative : 0 ≤ envelope omega :=
      Real.sqrt_nonneg _
    have hRealCoefficient : H.coefficientAbsSum omega ≤ (C : Real) := by
      exact_mod_cast hCoefficient omega
    have hRaw : ‖gain r omega - target omega‖ ≤
        4 * (C : Real) * envelope omega := by
      calc
        ‖gain r omega - target omega‖ ≤
            ‖gain r omega‖ + ‖target omega‖ := norm_sub_le _ _
        _ ≤ 2 * H.coefficientAbsSum omega * envelope omega +
            2 * H.coefficientAbsSum omega * envelope omega :=
          add_le_add hApproxGain hTarget
        _ ≤ 4 * (C : Real) * envelope omega := by
          nlinarith [H.coefficientAbsSum_nonneg omega]
    apply hRaw.trans_eq
    change 4 * (C : Real) * envelope omega =
      ‖4 * (C : Real) * envelope omega‖
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (NNReal.coe_nonneg C))
      hEnvelopeNonnegative
  have hTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun r => gain r omega) atTop (nhds (target omega)) :=
    Filter.Eventually.of_forall fun omega =>
      H.horizonLeftStepStrategy_gain_tendsto M hMRight T omega
  exact tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    hGainMeas hTargetMeas hBoundMem hBound hTendsto

end PredictableElementaryStrategy

end FTAPTheorem42
