/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal
import FTAPTheorem42.Stochastic.Decomposition.Source.CompensatorKernel

/-!
# Source-independent `L²` control for finite rows

The finite-grid compensator rows in the bounded and deterministic-bound-free
constructions share the same process-level argument: a nonnegative monotone
row is dominated by its terminal value on the horizon, and is constant after
the horizon.  This module records that argument without referring to either
source-specific row structure.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {P : Process Ω} {T : NNReal}

omit [IsProbabilityMeasure mu] in
theorem process_value_memLp_two_of_terminal
    (hPredictable : IsStronglyPredictable F P)
    (hNonneg : ∀ t omega, 0 ≤ P t omega)
    (hMono : ∀ omega, Monotone (P · omega))
    (hConstantAfter : ∀ omega t, T ≤ t → P t omega = P T omega)
    (hTerminal : MemLp (P T) (2 : ENNReal) mu)
    (t : NNReal) :
    MemLp (P t) (2 : ENNReal) mu := by
  by_cases ht : T ≤ t
  · have hEq : P t = P T := by
      funext omega
      exact hConstantAfter omega t ht
    rw [hEq]
    exact hTerminal
  · have htT : t ≤ T := le_of_not_ge ht
    have hMeas : AEStronglyMeasurable (P t) mu :=
      ((hPredictable.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    have hBound : ∀ᵐ omega ∂mu, ‖P t omega‖ ≤ ‖P T omega‖ := by
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg t omega),
        Real.norm_eq_abs, abs_of_nonneg (hNonneg T omega)]
      exact hMono omega htT
    exact MemLp.of_le hTerminal hMeas hBound

omit [IsProbabilityMeasure mu] in
theorem process_value_eLpNorm_le_terminal
    (hPredictable : IsStronglyPredictable F P)
    (hNonneg : ∀ t omega, 0 ≤ P t omega)
    (hMono : ∀ omega, Monotone (P · omega))
    (hConstantAfter : ∀ omega t, T ≤ t → P t omega = P T omega)
    (t : NNReal) :
    eLpNorm (P t) (2 : ENNReal) mu ≤ eLpNorm (P T) (2 : ENNReal) mu := by
  by_cases ht : T ≤ t
  · have hEq : P t = P T := by
      funext omega
      exact hConstantAfter omega t ht
    rw [hEq]
  · have htT : t ≤ T := le_of_not_ge ht
    apply eLpNorm_mono_ae
      ((hPredictable.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg t omega),
      Real.norm_eq_abs, abs_of_nonneg (hNonneg T omega)]
    exact hMono omega htT

omit [IsProbabilityMeasure mu] in
theorem process_value_sq_integral_le_terminal
    (hPredictable : IsStronglyPredictable F P)
    (hNonneg : ∀ t omega, 0 ≤ P t omega)
    (hMono : ∀ omega, Monotone (P · omega))
    (hConstantAfter : ∀ omega t, T ≤ t → P t omega = P T omega)
    (hTerminal : MemLp (P T) (2 : ENNReal) mu)
    {B : Real} (hTerminalBound :
      (∫ omega, (P T omega) ^ 2 ∂mu) ≤ B)
    (t : NNReal) :
    (∫ omega, (P t omega) ^ 2 ∂mu) ≤ B := by
  have hPt : MemLp (P t) (2 : ENNReal) mu :=
    process_value_memLp_two_of_terminal hPredictable hNonneg hMono
      hConstantAfter hTerminal t
  have hPT : MemLp (P T) (2 : ENNReal) mu := hTerminal
  have hPtInt : Integrable (fun omega => (P t omega) ^ 2) mu := by
    convert hPt.integrable_norm_pow (p := 2) (by norm_num) using 1
    funext omega
    rw [Real.norm_eq_abs, sq_abs]
  have hPTInt : Integrable (fun omega => (P T omega) ^ 2) mu := by
    convert hPT.integrable_norm_pow (p := 2) (by norm_num) using 1
    funext omega
    rw [Real.norm_eq_abs, sq_abs]
  have hSq : (fun omega => (P t omega) ^ 2) ≤ᵐ[mu]
      (fun omega => (P T omega) ^ 2) := by
    by_cases ht : T ≤ t
    · filter_upwards with omega
      rw [hConstantAfter omega t ht]
    · have htT : t ≤ T := le_of_not_ge ht
      filter_upwards with omega
      have hmono : P t omega ≤ P T omega := hMono omega htT
      nlinarith [hNonneg t omega, hNonneg T omega]
  exact (integral_mono_ae hPtInt hPTInt hSq).trans hTerminalBound

omit [IsProbabilityMeasure mu] in
theorem process_value_eLpNorm_toReal_le
    (hPredictable : IsStronglyPredictable F P)
    (hNonneg : ∀ t omega, 0 ≤ P t omega)
    (hMono : ∀ omega, Monotone (P · omega))
    (hConstantAfter : ∀ omega t, T ≤ t → P t omega = P T omega)
    (hTerminal : MemLp (P T) (2 : ENNReal) mu)
    {B : Real} (hTerminalBound :
      (∫ omega, (P T omega) ^ 2 ∂mu) ≤ B)
    (t : NNReal) :
    (eLpNorm (P t) (2 : ENNReal) mu).toReal ≤ Real.sqrt B := by
  have hMem := process_value_memLp_two_of_terminal hPredictable hNonneg hMono
    hConstantAfter hTerminal t
  have hSq := process_value_sq_integral_le_terminal hPredictable hNonneg hMono
    hConstantAfter hTerminal hTerminalBound t
  have hSq' :
      (∫ omega, ‖P t omega‖ ^ 2 ∂mu) ≤ B := by
    simpa only [Real.norm_eq_abs, sq_abs] using hSq
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hMem]
  exact Real.sqrt_le_sqrt hSq'

/-! ## Left continuity of finite-grid rows -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure mu] in
private theorem finiteGridCompensatorStepTerm_continuousWithinAt_Iic
    (T : NNReal) (D : Nat → Ω → Real) (r k : Nat)
    (omega : Ω) (t : NNReal) :
    ContinuousWithinAt
      (finiteGridCompensatorStepTerm T D r k · omega)
      (Iic t) t := by
  by_cases hActive : (grid T r).sampledTime k < t
  · have hEventually : ∀ᶠ u in 𝓝[Iic t] t,
        finiteGridCompensatorStepTerm T D r k u omega = D k omega := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hActive),
        self_mem_nhdsWithin] with u hu _hu
      simp only [finiteGridCompensatorStepTerm]
      exact ite_eq_left hu
    apply continuousWithinAt_const.congr_of_eventuallyEq hEventually
    simp only [finiteGridCompensatorStepTerm, ite_eq_left hActive]
  · have hEventually : ∀ᶠ u in 𝓝[Iic t] t,
        finiteGridCompensatorStepTerm T D r k u omega = 0 := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [finiteGridCompensatorStepTerm]
      exact ite_eq_right (fun hku => hActive (hku.trans_le hu))
    apply continuousWithinAt_const.congr_of_eventuallyEq hEventually
    simp only [finiteGridCompensatorStepTerm, ite_eq_right hActive]

omit [MeasurableSpace Ω] [IsProbabilityMeasure mu] in
theorem finiteGridPredictableCompensatorProcess_continuousWithinAt_Iic
    (T : NNReal) (D : Nat → Ω → Real) (r : Nat)
    (omega : Ω) (t : NNReal) :
    ContinuousWithinAt
      (finiteGridPredictableCompensatorProcess T D r · omega)
      (Iic t) t := by
  unfold finiteGridPredictableCompensatorProcess
  have hSum : ∀ n : Nat,
      ContinuousWithinAt
        (fun x => ∑ k ∈ Finset.range n,
          finiteGridCompensatorStepTerm T D r k x omega)
        (Iic t) t := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact continuousWithinAt_const
    | succ n ih =>
        simp only [Finset.sum_range_succ]
        convert ih.add (finiteGridCompensatorStepTerm_continuousWithinAt_Iic
          T D r n omega t) using 1
  simpa only [Finset.sum_apply] using hSum (size T r)

end HorizonFactorialGrid

end FTAPTheorem42
