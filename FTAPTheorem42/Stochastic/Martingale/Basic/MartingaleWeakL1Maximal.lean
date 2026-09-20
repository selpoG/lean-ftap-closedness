/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope

/-!
# Doob's weak `L¹` estimate on continuous-time factorial grids

The terminal-`L¹` completion of right-continuous martingales needs a
maximal estimate which remains available without a square-integrable
envelope.  We first apply mathlib's discrete weak maximal inequality to one
stopped factorial grid.  Monotone exhaustion of the factorial grids and
right continuity then control the event that the process crosses a fixed
level at any time before the deterministic horizon.  If the process is
constant after that horizon, the same estimate controls all times.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace FactorialChronologicalGrid

/-- Doob's weak `L¹` inequality on one sufficiently fine stopped
factorial grid. -/
theorem Martingale.measure_factorialRunningMax_abs_ge_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) {r : Nat} (hr : Nat.ceil T <= r)
    {epsilon : NNReal} (hepsilon : epsilon ≠ 0) :
    mu {omega | (epsilon : Real) <=
        factorialRunningMax (fun t omega => |M t omega|) T r omega} <=
      (epsilon : ENNReal)⁻¹ * eLpNorm (M T) 1 mu := by
  let G := stoppedGrid T r
  let f : NNReal -> Omega -> Real := fun t omega => |M t omega|
  have hf : Submartingale f F mu := Martingale.abs_submartingale hM
  have hsample : Submartingale (G.natSample f)
      (G.sampledFiltration F) mu :=
    ChronologicalGrid.Submartingale.natSample (G := G) hf
  have hsampleNonnegative : 0 <= G.natSample f :=
    G.natSample_nonneg (fun _ _ => abs_nonneg _)
  let event : Set Omega := {omega | (epsilon : Real) <=
    factorialRunningMax f T r omega}
  have hMaximal := MeasureTheory.maximal_ineq hsample
    hsampleNonnegative (ε := epsilon) (r * r.factorial)
  have hLast := stoppedGrid_last_time T hr
  have hEvent :
      {omega | (epsilon : Real) <=
        (Finset.range (r * r.factorial + 1)).sup'
          Finset.nonempty_range_add_one fun k => G.natSample f k omega} =
        event := by
    rfl
  rw [hEvent] at hMaximal
  have hTerminal : Integrable (fun omega => |M T omega|) mu :=
    (hM.integrable T).abs
  have hRightHand :
      ENNReal.ofReal
          (∫ omega in event,
            G.natSample f (r * r.factorial) omega ∂mu) <=
        eLpNorm (M T) 1 mu := by
    have hSampleLast : G.natSample f (r * r.factorial) =
        fun omega => |M T omega| := by
      funext omega
      simp only [G, ChronologicalGrid.natSample,
        ChronologicalGrid.sampledTime,
        ChronologicalGrid.natIndex_last, f, hLast]
    rw [hSampleLast]
    calc
      ENNReal.ofReal (∫ omega in event, |M T omega| ∂mu) <=
          ENNReal.ofReal (∫ omega, |M T omega| ∂mu) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral hTerminal
          (Filter.Eventually.of_forall fun omega => abs_nonneg (M T omega))
      _ = ∫⁻ omega, ENNReal.ofReal |M T omega| ∂mu := by
        exact ofReal_integral_eq_lintegral_ofReal hTerminal
          (Filter.Eventually.of_forall fun omega => abs_nonneg (M T omega))
      _ = eLpNorm (M T) 1 mu := by
        rw [eLpNorm_one_eq_lintegral_enorm (hM.integrable T).aestronglyMeasurable]
        congr 1
        funext omega
        exact (Real.enorm_eq_ofReal_abs (M T omega)).symm
  apply (ENNReal.mul_le_iff_le_inv
    (ENNReal.coe_ne_zero.mpr hepsilon) ENNReal.coe_ne_top).mp
  exact hMaximal.trans hRightHand

/-- A right-continuous martingale satisfies the weak `L¹` maximal
estimate on a deterministic finite horizon.  The half-level avoids any
attainment issue when the factorial maxima increase to their supremum. -/
theorem Martingale.measure_exists_abs_ge_before_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) {epsilon : NNReal} (hepsilon : epsilon ≠ 0) :
    mu {omega | exists t, t <= T /\
        (epsilon : Real) <= |M t omega|} <=
      ((epsilon / 2 : NNReal) : ENNReal)⁻¹ *
        eLpNorm (M T) 1 mu := by
  let c := Nat.ceil T
  let half : NNReal := epsilon / 2
  let event : Nat -> Set Omega := fun q =>
    {omega | (half : Real) <=
      factorialRunningMax (fun t omega => |M t omega|) T (q + c) omega}
  have hhalf : half ≠ 0 := by
    exact div_ne_zero hepsilon (by norm_num)
  have hEventMonotone : Monotone event := by
    intro q p hqp omega homega
    exact homega.trans
      (factorialRunningMax_mono (fun t omega => |M t omega|) T
        (Nat.add_le_add_right hqp c) omega)
  have hEventBound : forall q,
      mu (event q) <= (half : ENNReal)⁻¹ * eLpNorm (M T) 1 mu := by
    intro q
    exact Martingale.measure_factorialRunningMax_abs_ge_le
      hM T (show Nat.ceil T <= q + c by
        exact Nat.le_add_left c q) hhalf
  have hUnionBound :
      mu (⋃ q, event q) <=
        (half : ENNReal)⁻¹ * eLpNorm (M T) 1 mu := by
    apply le_of_tendsto (tendsto_measure_iUnion_atTop hEventMonotone)
    exact Filter.Eventually.of_forall hEventBound
  apply (measure_mono ?_).trans hUnionBound
  intro omega homega
  obtain ⟨t, htT, ht⟩ := homega
  have hHalfLtValue : (half : ENNReal) <
      ENNReal.ofReal |M t omega| := by
    rw [show (half : ENNReal) = ENNReal.ofReal (half : Real) by
      exact (ENNReal.ofReal_eq_coe_nnreal half.2).symm]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg half.2).2
    have hHalfLt : (half : Real) < (epsilon : Real) := by
      dsimp only [half]
      exact div_lt_self (show (0 : Real) < epsilon by
        exact_mod_cast (pos_iff_ne_zero.mpr hepsilon)) (by norm_num)
    exact hHalfLt.trans_le ht
  have hValueEnvelope : ENNReal.ofReal |M t omega| <=
      eFactorialRunningMaxEnvelope
        (fun s omega' => |M s omega'|) T omega :=
    ofReal_le_eFactorialRunningMaxEnvelope
      (fun s omega' => |M s omega'|) T
      (fun omega' s => (hMRight omega' s).abs) omega htT
  obtain ⟨r, hr⟩ := (lt_iSup_iff.mp
    (hHalfLtValue.trans_le hValueEnvelope))
  refine Set.mem_iUnion.mpr ⟨r, ?_⟩
  have hrReal : (half : Real) <
      factorialRunningMax (fun s omega' => |M s omega'|) T r omega := by
    have hr' : ENNReal.ofReal (half : Real) <
        ENNReal.ofReal
          (factorialRunningMax
            (fun s omega' => |M s omega'|) T r omega) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hr
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg half.2).1
    exact hr'
  exact hrReal.le.trans
    (factorialRunningMax_mono (fun s omega' => |M s omega'|) T
      (Nat.le_add_right r c) omega)

/-- If all paths are constant after `T`, the finite-horizon weak estimate
controls the maximal event over the whole time axis. -/
theorem Martingale.measure_exists_abs_ge_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMConstant : forall t, T <= t -> M t = M T)
    {epsilon : NNReal} (hepsilon : epsilon ≠ 0) :
    mu {omega | exists t, (epsilon : Real) <= |M t omega|} <=
      ((epsilon / 2 : NNReal) : ENNReal)⁻¹ *
        eLpNorm (M T) 1 mu := by
  apply (measure_mono ?_).trans
    (Martingale.measure_exists_abs_ge_before_le
      hM hMRight T hepsilon)
  intro omega homega
  obtain ⟨t, ht⟩ := homega
  by_cases htT : t <= T
  · exact ⟨t, htT, ht⟩
  · refine ⟨T, le_rfl, ?_⟩
    rw [← hMConstant t (le_of_not_ge htT)]
    exact ht

end FactorialChronologicalGrid

end FTAPTheorem42
