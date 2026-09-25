/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Compactness.CountableInMeasureDiagonal
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexificationCore

/-!
# A common almost-everywhere subsequence for the Hilbert rows

This module contains the diagonal step which is independent of the particular
construction of the compensator rows.  The input is the common Hilbert
convexification from `CommonHilbertRowsData`; the terminal residual and every
coordinate on the canonical right-dense skeleton are treated as one countable
family.  Consequently one strictly increasing cutoff works for all of them.

No càdlàg candidate, predictable limsup, optional sampling, or process-level
bridge is constructed here.  Those are consumers of this certificate.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

omit [IsProbabilityMeasure mu] in
/-- Dense-skeleton limits bound a monotone row sequence and make its limsup nonnegative. -/
theorem limsup_nonnegative_of_monotone_skeleton_convergence
    {mu : Measure Ω} {T : NNReal} {rows : Nat → Process Ω} {Preg : Process Ω}
    (hDense : ∀ s : Set.Iic T,
      s ∈ closure (Set.range (stoppedLimitSkeleton T) ∩ Set.Ici s))
    (hMono : ∀ n omega, Monotone (rows n · omega))
    (hConstant : ∀ n omega t, T ≤ t → rows n t omega = rows n T omega)
    (hNonnegative : ∀ n t omega, 0 ≤ rows n t omega)
    (hConvergence : ∀ᵐ omega ∂mu, ∀ j,
      Tendsto (fun n => rows n (stoppedLimitSkeleton T j).1 omega) atTop
        (𝓝 (Preg (stoppedLimitSkeleton T j).1 omega))) :
    ∀ᵐ omega ∂mu, ∀ t, 0 ≤ limsup (fun n => rows n t omega) atTop := by
  filter_upwards [hConvergence] with omega hConv
  intro t
  have hBound_le (s : NNReal) (hs : s ≤ T) :
      IsBoundedUnder (· ≤ ·) atTop
        (fun n => rows n s omega) := by
    let Ds : Set (Set.Iic T) :=
      Set.range (stoppedLimitSkeleton T) ∩ Set.Ici ⟨s, hs⟩
    have hN : NeBot (𝓝[Ds] ⟨s, hs⟩) := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      simpa only [Ds] using hDense ⟨s, hs⟩
    obtain ⟨q, ⟨hqD, hqs⟩⟩ :=
      hN.nonempty_of_mem self_mem_nhdsWithin
    rcases hqD with ⟨j, rfl⟩
    have hqUpper : ∀ᶠ n in atTop,
        rows n (stoppedLimitSkeleton T j).1 omega ≤
          Preg (stoppedLimitSkeleton T j).1 omega + 1 :=
      ((tendsto_order.1 (hConv j)).2
        (Preg (stoppedLimitSkeleton T j).1 omega + 1) (by linarith)).mono
          (fun _ h => h.le)
    have hsUpper : ∀ᶠ n in atTop,
        rows n s omega ≤
          Preg (stoppedLimitSkeleton T j).1 omega + 1 := by
      filter_upwards [hqUpper] with n hn
      exact (hMono n omega hqs).trans hn
    exact isBoundedUnder_of_eventually_le hsUpper
  have hBound : IsBoundedUnder (· ≤ ·) atTop
      (fun n => rows n t omega) := by
    by_cases ht : t ≤ T
    · exact hBound_le t ht
    · have hTt : T ≤ t := le_of_not_ge ht
      have hBoundT := hBound_le T le_rfl
      rcases hBoundT with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have hb' : ∀ᶠ n in atTop,
          rows n T omega ≤ b :=
        Filter.eventually_map.1 hb
      exact Filter.eventually_map.2 (by
        filter_upwards [hb'] with n hn
        rw [hConstant n omega t hTt]
        exact hn)
  exact le_limsup_of_frequently_le
    (Frequently.of_forall fun n => hNonnegative n t omega) hBound

namespace CommonHilbertRowsData

/-! ## Raw coordinates and their limits -/

noncomputable def commonAECoordinateRaw
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n) (i n : Nat) : Ω → Real :=
  match i with
  | 0 => h.residualConvexRow (w n)
  | j + 1 => h.convexRow (w n) (stoppedLimitSkeleton T j).1

noncomputable def commonAECoordinateLimitRaw
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (i : Nat) : Ω → Real :=
  (h.coordinateLimit y i : Ω → Real)

omit [IsProbabilityMeasure mu] in
theorem commonAECoordinateRaw_tendstoInMeasure
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y) :
    ∀ i, TendstoInMeasure mu
      (fun n => commonAECoordinateRaw h w i n) atTop
      (commonAECoordinateLimitRaw h y i) := by
  intro i
  cases i with
  | zero =>
      have hLp := MeasureTheory.tendstoInMeasure_of_tendsto_Lp
        hCommon.residual_coordinate_tendsto
      refine TendstoInMeasure.congr_left ?_ hLp
      intro n
      exact hCommon.residual_coordinate_coeFn_ae n
  | succ j =>
      have hLp := MeasureTheory.tendstoInMeasure_of_tendsto_Lp
        (hCommon.skeleton_coordinate_tendsto j)
      refine TendstoInMeasure.congr_left ?_ hLp
      intro n
      exact hCommon.skeleton_coordinate_coeFn_ae n j

/-! ## The common-a.e. certificate -/

structure CommonAESubsequenceData
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (cutoff : Nat → Nat) : Prop where
  cutoff_strictMono : StrictMono cutoff
  coordinate_tendstoAE : ∀ i, TendstoAE mu
    (fun n => commonAECoordinateRaw h w i (cutoff n))
    (commonAECoordinateLimitRaw h y i)
  residual_tendstoAE : TendstoAE mu
    (fun n => h.residualConvexRow (w (cutoff n)))
    (h.coordinateLimit y 0 : Ω → Real)
  skeleton_tendstoAE : ∀ j, TendstoAE mu
    (fun n => h.convexRow (w (cutoff n)) (stoppedLimitSkeleton T j).1)
    (h.coordinateLimit y (j + 1) : Ω → Real)
  weights_tail : ∀ n i, i ∈ (w (cutoff n)).support → cutoff n ≤ i
  weights_nonnegative : ∀ n i, i ∈ (w (cutoff n)).support →
    0 ≤ (w (cutoff n)).weight i
  weights_sum_eq_one : ∀ n,
    ∑ i ∈ (w (cutoff n)).support, (w (cutoff n)).weight i = 1
  row_isStronglyPredictable : ∀ n,
    IsStronglyPredictable F (h.convexRow (w (cutoff n)))
  row_zero : ∀ n, h.convexRow (w (cutoff n)) 0 = 0
  row_nonnegative : ∀ n t omega,
    0 ≤ h.convexRow (w (cutoff n)) t omega
  row_mono : ∀ n omega,
    Monotone (h.convexRow (w (cutoff n)) · omega)
  row_leftContinuous : ∀ n omega t,
    ContinuousWithinAt (h.convexRow (w (cutoff n)) · omega) (Iic t) t
  row_constant_after : ∀ n omega t, T ≤ t →
    h.convexRow (w (cutoff n)) t omega = h.convexRow (w (cutoff n)) T omega
  row_terminal_memLp_two : ∀ n,
    MemLp (h.convexRow (w (cutoff n)) T) (2 : ENNReal) mu
  row_terminal_L2_bound : ∀ n,
    (∫ omega, (h.convexRow (w (cutoff n)) T omega) ^ 2 ∂mu) ≤ rowBound ^ 2
  row_terminal_expectation : ∀ n,
    (∫ omega, h.convexRow (w (cutoff n)) T omega ∂mu) =
      ∫ omega, source omega ∂mu
  residual_row_memLp_two : ∀ n,
    MemLp (h.residualConvexRow (w (cutoff n))) (2 : ENNReal) mu
  residual_row_eq_source_sub_compensator : ∀ n,
    h.residualConvexRow (w (cutoff n)) =
      fun omega => source omega - h.convexRow (w (cutoff n)) T omega

omit [IsProbabilityMeasure mu] in
theorem commonAESubsequence_producer
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y) :
    ∃ cutoff : Nat → Nat, CommonAESubsequenceData h w y hCommon cutoff := by
  obtain ⟨cutoff, hCutoff, hAE⟩ :=
    exists_strictMono_tendstoAE_of_countable_tendstoInMeasure
      (commonAECoordinateRaw_tendstoInMeasure h w y hCommon)
  refine ⟨cutoff, ?_⟩
  refine {
    cutoff_strictMono := hCutoff
    coordinate_tendstoAE := hAE
    residual_tendstoAE := ?_
    skeleton_tendstoAE := ?_
    weights_tail := ?_
    weights_nonnegative := ?_
    weights_sum_eq_one := ?_
    row_isStronglyPredictable := ?_
    row_zero := ?_
    row_nonnegative := ?_
    row_mono := ?_
    row_leftContinuous := ?_
    row_constant_after := ?_
    row_terminal_memLp_two := ?_
    row_terminal_L2_bound := ?_
    row_terminal_expectation := ?_
    residual_row_memLp_two := ?_
    residual_row_eq_source_sub_compensator := ?_ }
  · simpa only [commonAECoordinateRaw, commonAECoordinateLimitRaw] using hAE 0
  · intro j
    simpa only [commonAECoordinateRaw, commonAECoordinateLimitRaw] using hAE (j + 1)
  · intro n i hi
    exact hCommon.weights_tail (cutoff n) i hi
  · intro n i hi
    exact hCommon.weights_nonneg (cutoff n) i hi
  · intro n
    exact hCommon.weights_sum_eq_one (cutoff n)
  · intro n
    exact hCommon.row_isStronglyPredictable (cutoff n)
  · intro n
    exact hCommon.row_zero (cutoff n)
  · intro n t omega
    exact hCommon.row_nonnegative (cutoff n) t omega
  · intro n omega
    exact hCommon.row_mono (cutoff n) omega
  · intro n omega t
    exact hCommon.row_leftContinuous (cutoff n) omega t
  · intro n omega t ht
    exact hCommon.row_constant_after (cutoff n) omega t ht
  · intro n
    exact hCommon.row_terminal_memLp_two (cutoff n)
  · intro n
    exact hCommon.row_terminal_L2_bound (cutoff n)
  · intro n
    exact hCommon.row_terminal_expectation (cutoff n)
  · intro n
    exact hCommon.residual_row_memLp_two (cutoff n)
  · intro n
    exact hCommon.residual_row_eq_source_sub_compensator (cutoff n)

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
