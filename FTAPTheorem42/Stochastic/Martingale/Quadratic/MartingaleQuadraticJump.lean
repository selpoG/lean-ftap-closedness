/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernel
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepApproximation
import FTAPTheorem42.Stochastic.Process.UniformLimits

/-!
# Jumps of the quadratic-energy process

This module identifies the atoms of the finite-horizon martingale energy
kernel.  The finite-grid martingale transforms have the expected left-jump
formula.  Their forward-convex uniform limit therefore has jump
`2 M_- ΔM`, and the exact square decomposition shows that the increasing
quadratic process has jump `(ΔM)²`.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- Multiplication by a sample-dependent coefficient which is constant in
time preserves pathwise left limits. -/
theorem ProcessHasLeftLimits.samplewise_const_mul
    {X : Process Omega} (hX : ProcessHasLeftLimits X) (c : Omega → Real) :
    ProcessHasLeftLimits fun t omega => c omega * X t omega := by
  intro omega t
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simp [hbot]
  · have hmul := (hX omega t).const_mul (c omega)
    rw [leftLim_eq_of_tendsto hmul]
    exact hmul

omit [MeasurableSpace Omega] in
/-- Left jumps commute with multiplication by a sample-dependent coefficient
which is constant in time. -/
theorem processLeftJump_samplewise_const_mul
    {X : Process Omega} (hX : ProcessHasLeftLimits X) (c : Omega → Real)
    (t : NNReal) (omega : Omega) :
    processLeftJump (fun s omega' => c omega' * X s omega') t omega =
      c omega * processLeftJump X t omega := by
  have hmul := (hX omega t).const_mul (c omega)
  unfold processLeftJump
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · rw [leftLim_eq_of_eq_bot _ hbot, leftLim_eq_of_eq_bot _ hbot]
    ring
  · rw [show Function.leftLim (fun s => c omega * X s omega) t =
        c omega * Function.leftLim (fun s => X s omega) t by
      exact leftLim_eq_of_tendsto hmul]
    ring

omit [MeasurableSpace Omega] in
/-- A finite sum of processes with left limits has left limits. -/
theorem ProcessHasLeftLimits.finset_sum
    {ι : Type*} (s : Finset ι) {X : ι → Process Omega}
    (hX : ∀ i ∈ s, ProcessHasLeftLimits (X i)) :
    ProcessHasLeftLimits (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change ProcessHasLeftLimits (fun _ _ => 0)
      intro omega t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : NNReal => (0 : Real)) (a := t)
        ⟨0, tendsto_const_nhds⟩
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hX i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hX j (Finset.mem_insert_of_mem hj))

omit [MeasurableSpace Omega] in
/-- Left jumps commute with a finite sum of processes with left limits. -/
theorem processLeftJump_finset_sum
    {ι : Type*} (s : Finset ι) {X : ι → Process Omega}
    (hX : ∀ i ∈ s, ProcessHasLeftLimits (X i))
    (t : NNReal) (omega : Omega) :
    processLeftJump (∑ i ∈ s, X i) t omega =
      ∑ i ∈ s, processLeftJump (X i) t omega := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change processLeftJump (fun _ _ => 0) t omega = 0
      unfold processLeftJump
      rcases eq_or_neBot (𝓝[<] t) with hbot | hne
      · simp [leftLim_eq_of_eq_bot _ hbot]
      · rw [leftLim_eq_of_tendsto tendsto_const_nhds]
        simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change processLeftJump (fun u omega' =>
          X i u omega' + (∑ j ∈ s, X j) u omega') t omega = _
      rw [processLeftJump_add
        (hX i (Finset.mem_insert_self i s))
        ((ProcessHasLeftLimits.finset_sum s)
          fun j hj => hX j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))]

omit [MeasurableSpace Omega] in
/-- One deterministic interval transform inherits left limits from its
integrator. -/
theorem deterministicIntervalMartingaleTransform_hasLeftLimits
    (K M : Process Omega) (hM : ProcessHasLeftLimits M) (s u : NNReal) :
    ProcessHasLeftLimits
      (deterministicIntervalMartingaleTransform K M s u) := by
  exact ProcessHasLeftLimits.samplewise_const_mul
    ((hM.stoppedProcess fun _ : Omega => (u : WithTop NNReal)).sub
      (hM.stoppedProcess fun _ : Omega => (s : WithTop NNReal))) (K s)

omit [MeasurableSpace Omega] in
/-- The jump of one deterministic interval transform is the active
left-endpoint coefficient times the source jump. -/
theorem processLeftJump_deterministicIntervalMartingaleTransform
    (K M : Process Omega) (hM : ProcessHasLeftLimits M)
    {s u : NNReal} (hsu : s ≤ u) (t : NNReal) (omega : Omega) :
    processLeftJump (deterministicIntervalMartingaleTransform K M s u)
        t omega =
      ChronologicalGrid.deterministicIntervalCoefficient K s u t omega *
        processLeftJump M t omega := by
  let Mu := MeasureTheory.stoppedProcess M
    (fun _ : Omega => (u : WithTop NNReal))
  let Ms := MeasureTheory.stoppedProcess M
    (fun _ : Omega => (s : WithTop NNReal))
  have hMu : ProcessHasLeftLimits Mu :=
    hM.stoppedProcess fun _ : Omega => (u : WithTop NNReal)
  have hMs : ProcessHasLeftLimits Ms :=
    hM.stoppedProcess fun _ : Omega => (s : WithTop NNReal)
  change processLeftJump (fun v omega' =>
      K s omega' * (Mu v omega' - Ms v omega')) t omega = _
  rw [processLeftJump_samplewise_const_mul (hMu.sub hMs) (K s),
    processLeftJump_sub hMu hMs]
  unfold ChronologicalGrid.deterministicIntervalCoefficient
  by_cases htu : t ≤ u
  · rw [processLeftJump_stoppedProcess_eq_of_le M hM _ t omega
      (WithTop.coe_le_coe.mpr htu)]
    by_cases hst : s < t
    · rw [processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
          (WithTop.coe_lt_coe.mpr hst)]
      simp [Set.mem_Ioc, hst, htu]
    · have hts : t ≤ s := le_of_not_gt hst
      rw [processLeftJump_stoppedProcess_eq_of_le M hM _ t omega
          (WithTop.coe_le_coe.mpr hts)]
      simp [Set.mem_Ioc, hst]
  · have hut : u < t := lt_of_not_ge htu
    have hst : s < t := hsu.trans_lt hut
    rw [processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
        (WithTop.coe_lt_coe.mpr hut),
      processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
        (WithTop.coe_lt_coe.mpr hst)]
    simp [Set.mem_Ioc, htu]

private theorem predictableElementaryInterval_gain_hasLeftLimits
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (hM : ProcessHasLeftLimits M) :
    ProcessHasLeftLimits (B.interval.gain M) := by
  let Mu := MeasureTheory.stoppedProcess M
    (fun omega => (B.interval.stopTime omega : WithTop NNReal))
  let Ms := MeasureTheory.stoppedProcess M
    (fun omega => (B.interval.startTime omega : WithTop NNReal))
  have hMu : ProcessHasLeftLimits Mu :=
    hM.stoppedProcess fun omega =>
      (B.interval.stopTime omega : WithTop NNReal)
  have hMs : ProcessHasLeftLimits Ms :=
    hM.stoppedProcess fun omega =>
      (B.interval.startTime omega : WithTop NNReal)
  have hGain : B.interval.gain M = fun s omega =>
      B.interval.coefficient omega * (Mu s omega - Ms s omega) := by
    funext s omega
    simp only [ElementaryInterval.gain, Mu, Ms,
      MeasureTheory.stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hGain]
  exact ProcessHasLeftLimits.samplewise_const_mul
    (hMu.sub hMs) B.interval.coefficient

private theorem predictableElementaryStrategy_gain_hasLeftLimits
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hM : ProcessHasLeftLimits M) :
    ProcessHasLeftLimits (ElementaryStrategy.gain M
      (PredictableElementaryStrategy.toElementary H)) := by
  induction H with
  | nil =>
      change ProcessHasLeftLimits (fun _ _ => 0)
      intro omega t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : NNReal => (0 : Real)) (a := t)
        ⟨0, tendsto_const_nhds⟩
  | cons B H ih =>
      change ProcessHasLeftLimits (fun s omega =>
        B.interval.gain M s omega +
          ElementaryStrategy.gain M
            (PredictableElementaryStrategy.toElementary H) s omega)
      exact (predictableElementaryInterval_gain_hasLeftLimits B M hM).add ih

/-- The jump of one predictable elementary gain is its active coefficient
times the source jump. -/
theorem PredictableElementaryInterval.processLeftJump_gain
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (hM : ProcessHasLeftLimits M) (t : NNReal) (omega : Omega) :
    processLeftJump (B.interval.gain M) t omega =
      B.integrand t omega * processLeftJump M t omega := by
  let Mu := MeasureTheory.stoppedProcess M
    (fun omega' => (B.interval.stopTime omega' : WithTop NNReal))
  let Ms := MeasureTheory.stoppedProcess M
    (fun omega' => (B.interval.startTime omega' : WithTop NNReal))
  have hMu : ProcessHasLeftLimits Mu :=
    hM.stoppedProcess fun omega' =>
      (B.interval.stopTime omega' : WithTop NNReal)
  have hMs : ProcessHasLeftLimits Ms :=
    hM.stoppedProcess fun omega' =>
      (B.interval.startTime omega' : WithTop NNReal)
  have hGain : B.interval.gain M = fun s omega' =>
      B.interval.coefficient omega' * (Mu s omega' - Ms s omega') := by
    funext s omega'
    simp only [ElementaryInterval.gain, Mu, Ms,
      MeasureTheory.stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hGain,
    processLeftJump_samplewise_const_mul
      (hMu.sub hMs) B.interval.coefficient,
    processLeftJump_sub hMu hMs]
  by_cases htu : t ≤ B.interval.stopTime omega
  · rw [processLeftJump_stoppedProcess_eq_of_le M hM _ t omega
      (WithTop.coe_le_coe.mpr htu)]
    by_cases hst : B.interval.startTime omega < t
    · rw [processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
          (WithTop.coe_lt_coe.mpr hst)]
      simp [PredictableElementaryInterval.integrand, hst, htu]
    · have hts : t ≤ B.interval.startTime omega := le_of_not_gt hst
      rw [processLeftJump_stoppedProcess_eq_of_le M hM _ t omega
          (WithTop.coe_le_coe.mpr hts)]
      simp [PredictableElementaryInterval.integrand, hst]
  · have hut : B.interval.stopTime omega < t := lt_of_not_ge htu
    have hst : B.interval.startTime omega < t :=
      (B.interval.start_le_stop omega).trans_lt hut
    rw [processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
        (WithTop.coe_lt_coe.mpr hut),
      processLeftJump_stoppedProcess_eq_zero_of_lt M _ t omega
        (WithTop.coe_lt_coe.mpr hst)]
    simp [PredictableElementaryInterval.integrand, htu]

/-- The jump formula extends from one block to a finite predictable
elementary strategy. -/
theorem PredictableElementaryStrategy.processLeftJump_gain
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hM : ProcessHasLeftLimits M) (t : NNReal) (omega : Omega) :
    processLeftJump (ElementaryStrategy.gain M
      (PredictableElementaryStrategy.toElementary H)) t omega =
      PredictableElementaryStrategy.integrand H t omega *
        processLeftJump M t omega := by
  induction H with
  | nil =>
      change processLeftJump (fun _ _ => 0) t omega =
        0 * processLeftJump M t omega
      unfold processLeftJump
      rcases eq_or_neBot (𝓝[<] t) with hbot | hne
      · simp [leftLim_eq_of_eq_bot _ hbot]
      · rw [leftLim_eq_of_tendsto tendsto_const_nhds]
        simp
  | cons B H ih =>
      change processLeftJump (fun s omega' =>
          B.interval.gain M s omega' +
            ElementaryStrategy.gain M
              (PredictableElementaryStrategy.toElementary H) s omega')
          t omega =
        (B.integrand t omega +
          PredictableElementaryStrategy.integrand H t omega) *
          processLeftJump M t omega
      rw [processLeftJump_add
        (predictableElementaryInterval_gain_hasLeftLimits B M hM)
        (predictableElementaryStrategy_gain_hasLeftLimits H M hM),
        B.processLeftJump_gain M hM t omega, ih]
      ring

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

omit [MeasurableSpace Omega] in
/-- A finite-grid martingale transform inherits left limits from its
integrator. -/
theorem martingaleIntegralProcess_hasLeftLimits
    (K M : Process Omega) (hM : ProcessHasLeftLimits M) :
    ProcessHasLeftLimits (G.martingaleIntegralProcess K M) := by
  unfold martingaleIntegralProcess
  exact ProcessHasLeftLimits.finset_sum (Finset.range N) fun k _ =>
    deterministicIntervalMartingaleTransform_hasLeftLimits K M hM
      (G.sampledTime k) (G.sampledTime (k + 1))

omit [MeasurableSpace Omega] in
/-- The finite-grid martingale transform has the expected predictable
left-step jump. -/
theorem processLeftJump_martingaleIntegralProcess
    (K M : Process Omega) (hM : ProcessHasLeftLimits M)
    (t : NNReal) (omega : Omega) :
    processLeftJump (G.martingaleIntegralProcess K M) t omega =
      G.predictableStepProcess K t omega * processLeftJump M t omega := by
  unfold martingaleIntegralProcess predictableStepProcess
  rw [processLeftJump_finset_sum (Finset.range N)
      (fun k _ => deterministicIntervalMartingaleTransform_hasLeftLimits
        K M hM (G.sampledTime k) (G.sampledTime (k + 1)))]
  simp only [Finset.sum_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _hk
  exact processLeftJump_deterministicIntervalMartingaleTransform
    K M hM (G.sampledTime_mono (Nat.le_succ k)) t omega

end ChronologicalGrid

namespace BoundedMartingaleQuadraticApproximation

private theorem level_pred_tendsto_atTop (T : NNReal) :
    Tendsto (fun n => level T n - 1) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnLevel : n ≤ level T n := self_le_level T n
  omega

omit [MeasurableSpace Omega] in
/-- Before the horizon and away from time zero, the stopped factorial-grid
left step is the canonical strict-left factorial approximation at the same
mesh. -/
theorem grid_predictableStepProcess_eq_leftApprox
    (K : Process Omega) (T : NNReal) {n : Nat} (hn : 0 < n)
    {t : NNReal} (ht0 : t ≠ 0) (htT : t ≤ T) :
    (grid T n).predictableStepProcess K t =
      K (LeftContinuousPredictable.approx (level T n - 1) t) := by
  let q := level T n
  have hqPos : 0 < q := hn.trans_le (self_le_level T n)
  have hdenominator :
      LeftContinuousPredictable.denominator (q - 1) = q.factorial := by
    simp only [LeftContinuousPredictable.denominator,
      Nat.sub_add_cancel hqPos]
  obtain ⟨k, hk⟩ :=
    LeftContinuousPredictable.exists_mem_Ioc_gridPoint ht0 (q - 1)
  have hTq : T ≤ (q : NNReal) := by
    exact (Nat.le_ceil T).trans (by
      exact_mod_cast ceil_le_level T n)
  have hkN : k < q * q.factorial := by
    have hfactorial : (0 : NNReal) < (q.factorial : NNReal) := by positivity
    have hkCast : (k : NNReal) < (q * q.factorial : Nat) := by
      calc
        (k : NNReal) < t * (q.factorial : NNReal) := by
          have hGrid : (k : NNReal) / (q.factorial : NNReal) < t := by
            simpa only [LeftContinuousPredictable.gridPoint,
              hdenominator] using hk.1
          exact (div_lt_iff₀ hfactorial).mp hGrid
        _ ≤ (q : NNReal) * (q.factorial : NNReal) :=
          mul_le_mul_of_nonneg_right (htT.trans hTq) hfactorial.le
        _ = (q * q.factorial : Nat) := by norm_num
    exact_mod_cast hkCast
  have hStart : (grid T n).sampledTime k =
      LeftContinuousPredictable.gridPoint (q - 1) k := by
    simp only [grid, ChronologicalGrid.sampledTime,
      ChronologicalGrid.natIndex, FactorialChronologicalGrid.stoppedGrid_time,
      FactorialChronologicalGrid.grid]
    rw [min_eq_left hkN.le]
    change min ((k : NNReal) / (q.factorial : NNReal)) T = _
    have hGridLeT : (k : NNReal) / (q.factorial : NNReal) ≤ T := by
      simpa only [LeftContinuousPredictable.gridPoint,
        hdenominator] using hk.1.le.trans htT
    rw [min_eq_left hGridLeT]
    simp only [LeftContinuousPredictable.gridPoint, hdenominator]
  have hStop : (grid T n).sampledTime (k + 1) =
      min (LeftContinuousPredictable.gridPoint (q - 1) (k + 1)) T := by
    have hkSucc : k + 1 ≤ q * q.factorial := hkN
    simp only [grid, ChronologicalGrid.sampledTime,
      ChronologicalGrid.natIndex, FactorialChronologicalGrid.stoppedGrid_time,
      FactorialChronologicalGrid.grid]
    rw [min_eq_left hkSucc]
    change min (((k + 1 : Nat) : NNReal) /
      (q.factorial : NNReal)) T = _
    simp only [LeftContinuousPredictable.gridPoint, hdenominator]
  have hBlock :
      (grid T n).predictableStepProcess K t =
        K ((grid T n).sampledTime k) := by
    apply ChronologicalGrid.predictableStepProcess_eq_of_mem_Ioc
      (grid T n) K hkN
    rw [hStart, hStop]
    exact ⟨hk.1, le_min hk.2 htT⟩
  rw [hBlock, hStart,
    LeftContinuousPredictable.approx_eq_gridPoint_of_mem_Ioc hk]

omit [MeasurableSpace Omega] in
/-- The stopped-source values sampled immediately to the left by the
quadratic factorial grids converge to the selected source left limit. -/
theorem tendsto_grid_predictableStepProcess_stoppedSource
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M)
    (T : NNReal) {t : NNReal} (ht0 : t ≠ 0) (htT : t ≤ T)
    (omega : Omega) :
    Tendsto (fun n =>
      (grid T n).predictableStepProcess (deterministicallyStoppedProcess M T) t omega)
      atTop
      (𝓝 (Function.leftLim (fun s => deterministicallyStoppedProcess M T s omega) t)) := by
  let q : Nat → Nat := fun n => level T n - 1
  have hq : Tendsto q atTop atTop := level_pred_tendsto_atTop T
  have hApprox : Tendsto
      (fun n => LeftContinuousPredictable.approx (q n) t)
      atTop (𝓝 t) :=
    LeftContinuousPredictable.tendsto_approx t |>.comp hq
  have hApproxLeft : ∀ᶠ n in atTop,
      LeftContinuousPredictable.approx (q n) t < t :=
    Filter.Eventually.of_forall fun n =>
      LeftContinuousPredictable.approx_lt ht0 (q n)
  have hSourceLeft :=
    (hMLeft.stoppedProcess fun _ : Omega => (T : WithTop NNReal)) omega t
  have hValue : Tendsto (fun n => deterministicallyStoppedProcess M T
      (LeftContinuousPredictable.approx (q n) t) omega) atTop
      (𝓝 (Function.leftLim (fun s => deterministicallyStoppedProcess M T s omega) t)) :=
    hSourceLeft.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hApprox, hApproxLeft⟩)
  apply hValue.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [grid_predictableStepProcess_eq_leftApprox
    (deterministicallyStoppedProcess M T) T (lt_of_lt_of_le Nat.zero_lt_one hn) ht0 htT]

omit [MeasurableSpace Omega] in
/-- Each quadratic martingale approximation inherits left limits from the
source. -/
theorem martingalePart_hasLeftLimits
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M)
    (T : NNReal) (n : Nat) :
    ProcessHasLeftLimits (martingalePart M T n) := by
  have hXLeft : ProcessHasLeftLimits (deterministicallyStoppedProcess M T) :=
    hMLeft.stoppedProcess fun _ : Omega => (T : WithTop NNReal)
  change ProcessHasLeftLimits (fun t omega =>
    2 * (grid T n).martingaleIntegralProcess
      (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) t omega)
  exact ((grid T n).martingaleIntegralProcess_hasLeftLimits
    (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) hXLeft).const_mul 2

omit [MeasurableSpace Omega] in
/-- The jump of a quadratic martingale approximation is twice the
left-grid source value times the stopped-source jump. -/
theorem processLeftJump_martingalePart
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M)
    (T : NNReal) (n : Nat) (t : NNReal) (omega : Omega) :
    processLeftJump (martingalePart M T n) t omega =
      2 * (grid T n).predictableStepProcess (deterministicallyStoppedProcess M T) t omega *
        processLeftJump (deterministicallyStoppedProcess M T) t omega := by
  have hXLeft : ProcessHasLeftLimits (deterministicallyStoppedProcess M T) :=
    hMLeft.stoppedProcess fun _ : Omega => (T : WithTop NNReal)
  rw [show martingalePart M T n = fun s omega' =>
      2 * (grid T n).martingaleIntegralProcess
        (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) s omega' by rfl,
    processLeftJump_const_mul
      ((grid T n).martingaleIntegralProcess_hasLeftLimits
        (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) hXLeft) 2,
    (grid T n).processLeftJump_martingaleIntegralProcess
      (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) hXLeft]
  ring

end BoundedMartingaleQuadraticApproximation

namespace BoundedMartingaleQuadraticConvexification

omit [MeasurableSpace Omega] in
/-- A convexified quadratic martingale approximation inherits source left
limits. -/
theorem martingalePart_hasLeftLimits
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M)
    (T : NNReal) {n : Nat} (w : TailConvexWeights n) :
    ProcessHasLeftLimits (martingalePart M T w) := by
  unfold martingalePart
  exact ProcessHasLeftLimits.finset_sum w.support fun i hi =>
    (BoundedMartingaleQuadraticApproximation.martingalePart_hasLeftLimits
      M hMLeft T i).const_mul (w.weight i)

omit [MeasurableSpace Omega] in
/-- Left jumps commute with the finite-tail convexification of quadratic
martingale approximations. -/
theorem processLeftJump_martingalePart
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M)
    (T : NNReal) {n : Nat} (w : TailConvexWeights n)
    (t : NNReal) (omega : Omega) :
    processLeftJump (martingalePart M T w) t omega =
      w.apply (fun i omega' =>
        processLeftJump
          (BoundedMartingaleQuadraticApproximation.martingalePart M T i)
          t omega') omega := by
  unfold martingalePart TailConvexWeights.apply
  change processLeftJump
      (∑ i ∈ w.support, fun s omega' =>
        w.weight i *
          BoundedMartingaleQuadraticApproximation.martingalePart
            M T i s omega') t omega = _
  rw [processLeftJump_finset_sum w.support (fun i hi =>
      (BoundedMartingaleQuadraticApproximation.martingalePart_hasLeftLimits
        M hMLeft T i).const_mul (w.weight i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact processLeftJump_const_mul
    (BoundedMartingaleQuadraticApproximation.martingalePart_hasLeftLimits
      M hMLeft T i) (w.weight i) t omega

end BoundedMartingaleQuadraticConvexification

namespace BoundedMartingaleQuadraticKernel.Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} {M : Process Omega} {T : NNReal}

open BoundedMartingaleQuadraticApproximation

/-- On one common full-measure set, the martingale part of the quadratic
construction has jump `2 M_- ΔM` up to the deterministic horizon. -/
theorem processLeftJump_martingalePart_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMLeft : ProcessHasLeftLimits M) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      processLeftJump D.martingalePart t omega =
        2 * Function.leftLim
            (fun s => deterministicallyStoppedProcess
              M T s omega) t *
          processLeftJump
            (deterministicallyStoppedProcess M T)
            t omega := by
  filter_upwards [D.martingalePart_uniform] with omega hUniform
  intro t htT
  by_cases ht0 : t = 0
  · subst t
    unfold processLeftJump
    rw [show Function.leftLim (fun s => D.martingalePart s omega) 0 =
          D.martingalePart 0 omega from
        leftLim_eq_of_isBot isBot_bot,
      show Function.leftLim (fun s =>
          deterministicallyStoppedProcess
            M T s omega) 0 =
          deterministicallyStoppedProcess
            M T 0 omega from
        leftLim_eq_of_isBot isBot_bot]
    ring
  let A : Nat → NNReal → Real := fun k s =>
    BoundedMartingaleQuadraticConvexification.martingalePart
      M T (D.weights (D.cutoff k)) s omega
  let Y : NNReal → Real := fun s => D.martingalePart s omega
  have hALeft : ∀ k s, Tendsto (A k) (𝓝[<] s)
      (𝓝 (Function.leftLim (A k) s)) := by
    intro k s
    exact (BoundedMartingaleQuadraticConvexification.martingalePart_hasLeftLimits
        M hMLeft T (D.weights (D.cutoff k))) omega s
  have hLeftLimit : Tendsto (fun k => Function.leftLim (A k) t)
      atTop (𝓝 (Function.leftLim Y t)) :=
    tendsto_leftLim_of_tendstoUniformly A Y hUniform hALeft t
  have hJumpLimit : Tendsto (fun k =>
      processLeftJump
        (BoundedMartingaleQuadraticConvexification.martingalePart
          M T (D.weights (D.cutoff k))) t omega)
      atTop (𝓝 (processLeftJump D.martingalePart t omega)) := by
    simpa only [processLeftJump, A, Y] using
      (hUniform.tendsto_at t).sub hLeftLimit
  let X := deterministicallyStoppedProcess M T
  let jump : Real := processLeftJump X t omega
  have hStep :=
    tendsto_grid_predictableStepProcess_stoppedSource
      M hMLeft T ht0 htT omega
  have hBase : Tendsto (fun i =>
      processLeftJump
        (BoundedMartingaleQuadraticApproximation.martingalePart M T i)
        t omega) atTop
      (𝓝 (2 * Function.leftLim (fun s => X s omega) t * jump)) := by
    have hProduct : Tendsto (fun i =>
        2 * (BoundedMartingaleQuadraticApproximation.grid T i).predictableStepProcess
          X t omega * jump) atTop
        (𝓝 (2 * Function.leftLim (fun s => X s omega) t * jump)) := by
      exact (hStep.const_mul 2).mul_const jump
    apply hProduct.congr'
    exact Filter.Eventually.of_forall fun i =>
      (BoundedMartingaleQuadraticApproximation.processLeftJump_martingalePart
        M hMLeft T i t omega).symm
  let W : ForwardConvexWeights := TailConvexWeights.toForwardReindex
    D.cutoff D.cutoff_strictMono D.weights
  have hConvex := W.tendsto_apply_real hBase
  have hConvex' : Tendsto (fun k =>
      processLeftJump
        (BoundedMartingaleQuadraticConvexification.martingalePart
          M T (D.weights (D.cutoff k))) t omega) atTop
      (𝓝 (2 * Function.leftLim (fun s => X s omega) t * jump)) := by
    apply hConvex.congr'
    exact Filter.Eventually.of_forall fun k => by
      change (∑ i ∈ W.support k, W.weight k i *
          processLeftJump
            (BoundedMartingaleQuadraticApproximation.martingalePart M T i)
            t omega) =
        processLeftJump
          (BoundedMartingaleQuadraticConvexification.martingalePart
            M T (D.weights (D.cutoff k))) t omega
      rw [BoundedMartingaleQuadraticConvexification.processLeftJump_martingalePart
        M hMLeft T
          (D.weights (D.cutoff k)) t omega]
      rfl
  have hEq := tendsto_nhds_unique hJumpLimit hConvex'
  simpa only [X, jump] using hEq

/-- On one common full-measure set, every jump of the regularized increasing
quadratic process is the square of the corresponding stopped-source jump. -/
theorem processLeftJump_variation_eq_sq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMLeft : ProcessHasLeftLimits M) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump D.variation t omega =
        processLeftJump
          (deterministicallyStoppedProcess M T)
          t omega ^ 2 := by
  have hRaw : ∀ᵐ omega ∂mu, ∀ t,
      D.variation t omega =
        BoundedMartingaleQuadraticKernel.rawVariation
          M T D.martingalePart t omega :=
    ae_iff.mp D.variation_indistinguishable_raw
  filter_upwards [D.martingalePart_uniform, hRaw,
    D.processLeftJump_martingalePart_eq hMLeft]
      with omega hUniform hRawOmega hMartingaleJump
  let X := deterministicallyStoppedProcess M T
  let A : Nat → NNReal → Real := fun k s =>
    BoundedMartingaleQuadraticConvexification.martingalePart
      M T (D.weights (D.cutoff k)) s omega
  let Y : NNReal → Real := fun s => D.martingalePart s omega
  have hALeft : ∀ k s, Tendsto (A k) (𝓝[<] s)
      (𝓝 (Function.leftLim (A k) s)) := by
    intro k s
    exact (BoundedMartingaleQuadraticConvexification.martingalePart_hasLeftLimits
      M hMLeft T (D.weights (D.cutoff k))) omega s
  have hYLeft : ∀ t, Tendsto Y (𝓝[<] t)
      (𝓝 (Function.leftLim Y t)) :=
    leftLimits_of_tendstoUniformly A Y hUniform hALeft
  have hXLeft : ProcessHasLeftLimits X :=
    hMLeft.stoppedProcess fun _ : Omega => (T : WithTop NNReal)
  intro t
  by_cases ht0 : t = 0
  · subst t
    unfold processLeftJump
    rw [show Function.leftLim (fun s => D.variation s omega) 0 =
          D.variation 0 omega from
        leftLim_eq_of_isBot isBot_bot,
      show Function.leftLim (fun s => X s omega) 0 = X 0 omega from
        leftLim_eq_of_isBot isBot_bot]
    ring
  by_cases htT : t ≤ T
  · have htPos : (0 : NNReal) < t := pos_iff_ne_zero.mpr ht0
    let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htPos⟩
    have hRawPath : (fun s => D.variation s omega) = fun s =>
        X s omega ^ 2 - X 0 omega ^ 2 - Y s := by
      funext s
      simpa only [X, Y,
        BoundedMartingaleQuadraticKernel.rawVariation_apply] using
        hRawOmega s
    have hRawLeft : Tendsto
        (fun s => X s omega ^ 2 - X 0 omega ^ 2 - Y s)
        (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s => X s omega) t ^ 2 -
          X 0 omega ^ 2 - Function.leftLim Y t)) :=
      ((hXLeft omega t).pow 2).sub tendsto_const_nhds |>.sub (hYLeft t)
    have hVariationLeft :
        Function.leftLim (fun s => D.variation s omega) t =
          Function.leftLim (fun s => X s omega) t ^ 2 -
            X 0 omega ^ 2 - Function.leftLim Y t := by
      rw [hRawPath]
      exact leftLim_eq_of_tendsto hRawLeft
    have hRawAt : D.variation t omega =
        X t omega ^ 2 - X 0 omega ^ 2 - Y t := by
      simpa only [X, Y,
        BoundedMartingaleQuadraticKernel.rawVariation_apply] using
        hRawOmega t
    have hMartingaleJumpAt :
        D.martingalePart t omega - Function.leftLim Y t =
          2 * Function.leftLim (fun s => X s omega) t *
            (X t omega - Function.leftLim (fun s => X s omega) t) := by
      simpa only [processLeftJump, X, Y] using
        hMartingaleJump t htT
    unfold processLeftJump
    rw [hRawAt, hVariationLeft]
    change X t omega ^ 2 - X 0 omega ^ 2 - Y t -
        (Function.leftLim (fun s => X s omega) t ^ 2 -
          X 0 omega ^ 2 - Function.leftLim Y t) =
      (X t omega - Function.leftLim (fun s => X s omega) t) ^ 2
    rw [show Y t = D.martingalePart t omega from rfl]
    nlinarith [hMartingaleJumpAt]
  · have hTt : T < t := lt_of_not_ge htT
    let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨T, hTt⟩
    have hEventuallyVariation :
        (fun s => D.variation s omega) =ᶠ[𝓝[<] t]
          fun _ => D.variation T omega := by
      filter_upwards [Ico_mem_nhdsLT hTt] with s hs
      exact D.variation_constantAfter omega s hs.1
    have hVariationLeft :
        Function.leftLim (fun s => D.variation s omega) t =
          D.variation T omega := by
      apply leftLim_eq_of_tendsto
      exact tendsto_const_nhds.congr' hEventuallyVariation.symm
    have hVariationAt : D.variation t omega = D.variation T omega :=
      D.variation_constantAfter omega t hTt.le
    have hXJump : processLeftJump X t omega = 0 := by
      exact processLeftJump_stoppedProcess_eq_zero_of_lt M
        (fun _ : Omega => (T : WithTop NNReal)) t omega
        (WithTop.coe_lt_coe.mpr hTt)
    have hVariationJump : processLeftJump D.variation t omega = 0 := by
      unfold processLeftJump
      rw [hVariationAt, hVariationLeft, sub_self]
    rw [hVariationJump, hXJump]
    norm_num

/-- On one common full-measure set, the atom of the pathwise quadratic
Stieltjes kernel at every time is the squared stopped-source jump. -/
theorem stieltjesKernel_singleton_eq_jump_sq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMLeft : ProcessHasLeftLimits M) :
    ∀ᵐ omega ∂mu, ∀ t,
      D.stieltjesKernel omega {t} =
        ENNReal.ofReal
          (processLeftJump
            (deterministicallyStoppedProcess M T)
            t omega ^ 2) := by
  filter_upwards [D.processLeftJump_variation_eq_sq hMLeft]
      with omega hJump
  intro t
  rw [D.stieltjesKernel_apply,
    IncreasingProcessStieltjesKernel.pathMeasure,
    StieltjesFunction.measure_singleton]
  change ENNReal.ofReal (processLeftJump D.variation t omega) = _
  rw [hJump t]

end BoundedMartingaleQuadraticKernel.Data

end FTAPTheorem42
