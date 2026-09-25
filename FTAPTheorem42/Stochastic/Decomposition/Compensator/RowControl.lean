/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ResidualMartingale
import FTAPTheorem42.Stochastic.Decomposition.Compensator.RowControlCore
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling

/-!
# Finite-grid compensator row control

This module records the elementary process-level consequences of a finite-grid
predictable compensator row.  The left-endpoint activation convention is kept:
`P t = ∑ k, d k * 1_{t_k < t}`.  Thus every finite row is left-continuous;
no right-continuous version is introduced here.

The terminal estimate is an ordinary second-moment estimate.  In particular,
the process is never claimed to satisfy the false pathwise bound `P T ≤ C`.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

namespace BoundedIncreasingProcessData

/-! ## Pointwise `L²` control -/

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_value_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    MemLp (predictableCompensatorProcess V F mu T C r t)
      (2 : ENNReal) mu := by
  exact process_value_memLp_two_of_terminal
    (P := predictableCompensatorProcess V F mu T C r)
    (hRows.process_predictable r) (hRows.process_nonneg r)
    (hRows.process_mono r) (hRows.process_constant_after r)
    (hRows.terminal_memLp_two r) t

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_value_eLpNorm_le_terminal
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    eLpNorm (predictableCompensatorProcess V F mu T C r t)
        (2 : ENNReal) mu ≤
    eLpNorm (predictableCompensatorProcess V F mu T C r T)
        (2 : ENNReal) mu := by
  exact process_value_eLpNorm_le_terminal (hRows.process_predictable r)
    (hRows.process_nonneg r) (hRows.process_mono r)
    (hRows.process_constant_after r) t

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_value_sq_integral_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    (∫ omega,
      (predictableCompensatorProcess V F mu T C r t omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2 := by
  exact process_value_sq_integral_le_terminal
    (P := predictableCompensatorProcess V F mu T C r)
    (hRows.process_predictable r) (hRows.process_nonneg r)
    (hRows.process_mono r) (hRows.process_constant_after r)
    (hRows.terminal_memLp_two r) (hRows.terminal_L2_bound r) t

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_value_eLpNorm_toReal_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    (eLpNorm (predictableCompensatorProcess V F mu T C r t)
      (2 : ENNReal) mu).toReal ≤
      Real.sqrt (8 * (C : Real) ^ 2) := by
  exact process_value_eLpNorm_toReal_le
    (P := predictableCompensatorProcess V F mu T C r)
    (hRows.process_predictable r) (hRows.process_nonneg r)
    (hRows.process_mono r) (hRows.process_constant_after r)
    (hRows.terminal_memLp_two r) (hRows.terminal_L2_bound r) t

/-! ## Left continuity of the finite rows -/

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_continuousWithinAt_Iic
    (r : Nat) (omega : Ω) (t : NNReal) :
    ContinuousWithinAt
      (predictableCompensatorProcess V F mu T C r · omega)
      (Iic t) t := by
  change ContinuousWithinAt
    (finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r · omega)
    (Iic t) t
  exact finiteGridPredictableCompensatorProcess_continuousWithinAt_Iic
    T (fun k => compensatorIncrement V F mu T C r k) r omega t

/-! ## Interval testing -/

theorem grid_interval_indicator_testing_identity
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r i j : Nat) (hij : i ≤ j) (hj : j ≤ size T r)
    {B : Set Ω} (hB : MeasurableSet[F ((grid T r).sampledTime i)] B) :
    (∫ omega in B,
      V ((grid T r).sampledTime j) omega -
        V ((grid T r).sampledTime i) omega ∂mu) =
      ∫ omega in B,
      predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime j) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime i) omega ∂mu := by
  have hBambient : MeasurableSet B :=
    (F.le ((grid T r).sampledTime i)) B hB
  let K : Nat → Ω → Real := fun k omega =>
    if i ≤ k then B.indicator (fun _ => (1 : Real)) omega else 0
  have hK : StronglyAdapted ((grid T r).sampledFiltration F) K := by
    intro k
    by_cases hik : i ≤ k
    · have htime : (grid T r).sampledTime i ≤
          (grid T r).sampledTime k :=
        (grid T r).sampledTime_mono hik
      have hB_k : MeasurableSet[F ((grid T r).sampledTime k)] B :=
        (F.mono htime) B hB
      have hInd : StronglyMeasurable[F ((grid T r).sampledTime k)]
          (B.indicator (fun _ : Ω => (1 : Real))) :=
        stronglyMeasurable_const.indicator hB_k
      change StronglyMeasurable[F ((grid T r).sampledTime k)] (K k)
      simpa [K, hik] using hInd
    · change StronglyMeasurable[F ((grid T r).sampledTime k)] (K k)
      simpa [K, hik] using
        (stronglyMeasurable_const :
          StronglyMeasurable[F ((grid T r).sampledTime k)]
            (fun _ : Ω => (0 : Real)))
  have hSourceInt : ∀ k, Integrable
      (K k * ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k)) mu := by
    intro k
    by_cases hik : i ≤ k
    · by_cases hk : k < size T r
      · have hInt := hV.integrable_gridIncrement (mu := mu) r k hk
        have hIndInt := hInt.indicator hBambient
        have hEq : K k * ((grid T r).natSample V (k + 1) -
            (grid T r).natSample V k) =
            B.indicator (gridIncrement V T r k) := by
          funext omega
          by_cases hω : omega ∈ B <;>
            simp [K, hik, ChronologicalGrid.natSample, gridIncrement, hω]
        rw [hEq]
        exact hIndInt
      · have hks : size T r ≤ k := Nat.le_of_not_gt hk
        have htk : (grid T r).sampledTime k = T :=
          sampledTime_eq_terminal_of_le (T := T) r k hks
        have htk1 : (grid T r).sampledTime (k + 1) = T :=
          sampledTime_eq_terminal_of_le (T := T) r (k + 1)
            (hks.trans (Nat.le_succ k))
        have hzero : (grid T r).natSample V (k + 1) -
            (grid T r).natSample V k = 0 := by
          funext omega
          simp [ChronologicalGrid.natSample, htk, htk1]
        rw [hzero]
        simp
    · have hzero : K k = 0 := by
        funext omega
        simp [K, hik]
      rw [hzero]
      simp
  have hCompInt : ∀ k, Integrable
      (K k * compensatorIncrement V F mu T C r k) mu := by
    intro k
    by_cases hik : i ≤ k
    · have hInt := hV.compensatorIncrement_integrable
        (F := F) (mu := mu) r k
      have hIndInt := hInt.indicator hBambient
      have hEq : K k * compensatorIncrement V F mu T C r k =
          B.indicator (compensatorIncrement V F mu T C r k) := by
        funext omega
        by_cases hω : omega ∈ B <;> simp [K, hik, hω]
      rw [hEq]
      exact hIndInt
    · have hzero : K k = 0 := by
        funext omega
        simp [K, hik]
      rw [hzero]
      simp
  have hTestJ := hRows.testing_identity r j hj K hK hSourceInt hCompInt
  have hTestI := hRows.testing_identity r i (hij.trans hj) K hK hSourceInt hCompInt
  let sourceIntegral : Nat → Ω → Real := fun n omega =>
    ∑ k ∈ Finset.range n,
      K k omega * (((grid T r).natSample V (k + 1)) omega -
        ((grid T r).natSample V k) omega)
  let compensatorIntegral : Nat → Ω → Real := fun n omega =>
    ∑ k ∈ Finset.range n,
      K k omega * compensatorIncrement V F mu T C r k omega
  have hSourceIntAt : ∀ n, Integrable (sourceIntegral n) mu := by
    intro n
    change Integrable (fun omega => ∑ k ∈ Finset.range n,
      K k omega * (((grid T r).natSample V (k + 1)) omega -
        ((grid T r).natSample V k) omega)) mu
    exact integrable_finsetSum (Finset.range n)
      (fun k hk => hSourceInt k)
  have hCompIntAt : ∀ n, Integrable (compensatorIntegral n) mu := by
    intro n
    change Integrable (fun omega => ∑ k ∈ Finset.range n,
      K k omega * compensatorIncrement V F mu T C r k omega) mu
    exact integrable_finsetSum (Finset.range n)
      (fun k hk => hCompInt k)
  have hSourceDifference : ∀ omega,
      sourceIntegral j omega - sourceIntegral i omega =
        B.indicator (fun omega =>
          V ((grid T r).sampledTime j) omega -
            V ((grid T r).sampledTime i) omega) omega := by
    intro omega
    have hsum : ∀ k, K k omega *
        (((grid T r).natSample V (k + 1)) omega -
          ((grid T r).natSample V k) omega) =
        if i ≤ k then
          B.indicator (fun _ => (1 : Real)) omega *
            (V ((grid T r).sampledTime (k + 1)) omega -
              V ((grid T r).sampledTime k) omega)
        else 0 := by
      intro k
      by_cases hik : i ≤ k <;>
        simp [K, ChronologicalGrid.natSample, hik]
    change ((∑ k ∈ Finset.range j,
      K k omega * (((grid T r).natSample V (k + 1)) omega -
        ((grid T r).natSample V k) omega)) -
      (∑ k ∈ Finset.range i,
        K k omega * (((grid T r).natSample V (k + 1)) omega -
          ((grid T r).natSample V k) omega))) = _
    rw [← Finset.sum_Ico_eq_sub (fun k =>
      K k omega *
        (((grid T r).natSample V (k + 1)) omega -
          ((grid T r).natSample V k) omega)) hij]
    calc
      (∑ k ∈ Finset.Ico i j,
          K k omega *
            (((grid T r).natSample V (k + 1)) omega -
              ((grid T r).natSample V k) omega)) =
          ∑ k ∈ Finset.Ico i j,
            B.indicator (fun _ => (1 : Real)) omega *
              (V ((grid T r).sampledTime (k + 1)) omega -
                V ((grid T r).sampledTime k) omega) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hik' : i ≤ k := Finset.mem_Ico.mp hk |>.1
        rw [hsum k]
        simp [hik']
      _ = B.indicator (fun _ => (1 : Real)) omega *
          (V ((grid T r).sampledTime j) omega -
            V ((grid T r).sampledTime i) omega) := by
        rw [← Finset.mul_sum]
        have hTel :
            (∑ k ∈ Finset.Ico i j,
              (V ((grid T r).sampledTime (k + 1)) omega -
                V ((grid T r).sampledTime k) omega)) =
              V ((grid T r).sampledTime j) omega -
                V ((grid T r).sampledTime i) omega := by
          rw [Finset.sum_Ico_eq_sum_range]
          simpa [Nat.add_assoc, Nat.add_sub_of_le hij] using
            (Finset.sum_range_sub
              (fun k => V ((grid T r).sampledTime (i + k)) omega)
              (j - i))
        rw [hTel]
      _ = B.indicator (fun omega =>
          V ((grid T r).sampledTime j) omega -
            V ((grid T r).sampledTime i) omega) omega := by
        by_cases hω : omega ∈ B <;> simp [hω]
  have hCompDifference : ∀ omega,
      compensatorIntegral j omega - compensatorIntegral i omega =
        B.indicator (fun omega =>
          predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime j) omega -
            predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime i) omega) omega := by
    intro omega
    unfold compensatorIntegral
    rw [← Finset.sum_Ico_eq_sub (fun k =>
      K k omega * compensatorIncrement V F mu T C r k omega) hij]
    calc
      (∑ k ∈ Finset.Ico i j,
          K k omega * compensatorIncrement V F mu T C r k omega) =
          ∑ k ∈ Finset.Ico i j,
            B.indicator (fun _ => (1 : Real)) omega *
              (predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime (k + 1)) omega -
                predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime k) omega) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hik' : i ≤ k := Finset.mem_Ico.mp hk |>.1
        have hkl : k < size T r := (Finset.mem_Ico.mp hk).2.trans_le hj
        rw [show K k omega = B.indicator (fun _ => (1 : Real)) omega by
          simp [K, hik']]
        rw [← congrFun (hRows.process_sampled_increment r k hkl) omega]
      _ = B.indicator (fun _ => (1 : Real)) omega *
          (predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime j) omega -
            predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime i) omega) := by
        rw [← Finset.mul_sum]
        have hTel :
            (∑ k ∈ Finset.Ico i j,
              (predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime (k + 1)) omega -
                predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime k) omega)) =
              predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime j) omega -
                predictableCompensatorProcess V F mu T C r
                  ((grid T r).sampledTime i) omega := by
          rw [Finset.sum_Ico_eq_sum_range]
          simpa [Nat.add_assoc, Nat.add_sub_of_le hij] using
            (Finset.sum_range_sub
              (fun k => predictableCompensatorProcess V F mu T C r
                ((grid T r).sampledTime (i + k)) omega) (j - i))
        rw [hTel]
      _ = B.indicator (fun omega =>
          predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime j) omega -
            predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime i) omega) omega := by
        by_cases hω : omega ∈ B <;> simp [hω]
  have hSourceDiffEq : sourceIntegral j - sourceIntegral i =
      B.indicator (fun omega =>
        V ((grid T r).sampledTime j) omega -
          V ((grid T r).sampledTime i) omega) := by
    funext omega
    exact hSourceDifference omega
  have hCompDiffEq : compensatorIntegral j - compensatorIntegral i =
      B.indicator (fun omega =>
        predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime j) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime i) omega) := by
    funext omega
    exact hCompDifference omega
  have hTestJ' : (∫ omega, sourceIntegral j omega ∂mu) =
      ∫ omega, compensatorIntegral j omega ∂mu := by
    simpa only [sourceIntegral, compensatorIntegral,
      discretePredictableIntegral, Finset.sum_apply] using hTestJ
  have hTestI' : (∫ omega, sourceIntegral i omega ∂mu) =
      ∫ omega, compensatorIntegral i omega ∂mu := by
    simpa only [sourceIntegral, compensatorIntegral,
      discretePredictableIntegral, Finset.sum_apply] using hTestI
  have hIntegralDiff :
      (∫ omega, sourceIntegral j omega ∂mu) -
          ∫ omega, sourceIntegral i omega ∂mu =
        (∫ omega, compensatorIntegral j omega ∂mu) -
          ∫ omega, compensatorIntegral i omega ∂mu := by
    rw [hTestJ', hTestI']
  calc
    (∫ omega in B,
        V ((grid T r).sampledTime j) omega -
          V ((grid T r).sampledTime i) omega ∂mu) =
        ∫ omega, B.indicator (fun omega =>
          V ((grid T r).sampledTime j) omega -
            V ((grid T r).sampledTime i) omega) omega ∂mu := by
      rw [integral_indicator hBambient]
    _ = ∫ omega, (sourceIntegral j omega - sourceIntegral i omega) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega =>
        (hSourceDifference omega).symm)
    _ = (∫ omega, sourceIntegral j omega ∂mu) -
          ∫ omega, sourceIntegral i omega ∂mu :=
      integral_sub (hSourceIntAt j) (hSourceIntAt i)
    _ = (∫ omega, compensatorIntegral j omega ∂mu) -
          ∫ omega, compensatorIntegral i omega ∂mu := hIntegralDiff
    _ = ∫ omega, (compensatorIntegral j omega -
          compensatorIntegral i omega) ∂mu :=
      (integral_sub (hCompIntAt j) (hCompIntAt i)).symm
    _ = ∫ omega, B.indicator (fun omega =>
          predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime j) omega -
            predictableCompensatorProcess V F mu T C r
              ((grid T r).sampledTime i) omega) omega ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega =>
        hCompDifference omega)
    _ = ∫ omega in B,
        predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime j) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime i) omega ∂mu := by
      rw [integral_indicator hBambient]

/-! ## Public 7B certificate -/

structure FactorialGridPredictableCompensatorRowControlData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) where
  value_memLp_two : ∀ r t,
    MemLp (predictableCompensatorProcess V F mu T C r t)
      (2 : ENNReal) mu
  value_eLpNorm_le_terminal : ∀ r t,
    eLpNorm (predictableCompensatorProcess V F mu T C r t)
      (2 : ENNReal) mu ≤
      eLpNorm (predictableCompensatorProcess V F mu T C r T)
        (2 : ENNReal) mu
  value_sq_integral_le : ∀ r t,
    (∫ omega,
      (predictableCompensatorProcess V F mu T C r t omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2
  value_eLpNorm_toReal_le : ∀ r t,
    (eLpNorm (predictableCompensatorProcess V F mu T C r t)
      (2 : ENNReal) mu).toReal ≤
      Real.sqrt (8 * (C : Real) ^ 2)
  interval_testing_identity : ∀ r i j, i ≤ j → j ≤ size T r →
    ∀ {B : Set Ω}, MeasurableSet[F ((grid T r).sampledTime i)] B →
    (∫ omega in B,
      V ((grid T r).sampledTime j) omega -
        V ((grid T r).sampledTime i) omega ∂mu) =
      ∫ omega in B,
        predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime j) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime i) omega ∂mu
  leftContinuous : ∀ r omega t,
    ContinuousWithinAt
      (predictableCompensatorProcess V F mu T C r · omega)
      (Iic t) t

theorem factorialGridPredictableCompensatorRowControl_producer
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) :
    Nonempty (FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) := by
  exact ⟨{
    value_memLp_two := fun r t =>
      predictableCompensatorProcess_value_memLp_two
        (F := F) (mu := mu) hV hRows r t
    value_eLpNorm_le_terminal := fun r t =>
      predictableCompensatorProcess_value_eLpNorm_le_terminal
        (F := F) (mu := mu) hV hRows r t
    value_sq_integral_le := fun r t =>
      predictableCompensatorProcess_value_sq_integral_le
        (F := F) (mu := mu) hV hRows r t
    value_eLpNorm_toReal_le := fun r t =>
      predictableCompensatorProcess_value_eLpNorm_toReal_le
        (F := F) (mu := mu) hV hRows r t
    interval_testing_identity := fun r i j hij hj B hB =>
      grid_interval_indicator_testing_identity
        (F := F) (mu := mu) hV hRows r i j hij hj hB
    leftContinuous := fun r omega t =>
      predictableCompensatorProcess_continuousWithinAt_Iic
        (F := F) (mu := mu) r omega t }⟩

end BoundedIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
