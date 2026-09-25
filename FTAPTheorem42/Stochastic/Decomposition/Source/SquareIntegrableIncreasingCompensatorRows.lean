/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridPredictableElementaryStrategy
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal
import FTAPTheorem42.Stochastic.Decomposition.Source.CompensatorKernel
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticRegularization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Finite-grid compensators for square-integrable increasing processes

This module is the deterministic-bound-free companion of the bounded finite-grid
compensator construction.  Conditional expectations are clipped only at zero,
so that the everywhere-defined representative is nonnegative; there is no
upper clipping.  The terminal estimate is obtained from the finite-grid square
identity, conditional-expectation contraction, and the increasing-source
telescoping estimate.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

/-! ## Increasing input and finite-grid functions -/

structure SquareIntegrableIncreasingProcessData
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (V : Process Ω) (T : NNReal) (mu : Measure Ω)
    [IsProbabilityMeasure mu] : Prop where
  stronglyAdapted : StronglyAdapted F V
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (V · omega) (Ici t) t
  monotone : ∀ omega, Monotone (V · omega)
  zero : V 0 = 0
  constant_after : ∀ omega t, T ≤ t → V t omega = V T omega
  terminal_memLp_two : MemLp (V T) (2 : ENNReal) mu

namespace SquareIntegrableIncreasingProcessData

theorem value_nonneg
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    {t : NNReal} (_ht : t ≤ T) (omega : Ω) :
    0 ≤ V t omega := by
  have hmono := hV.monotone omega (show (0 : NNReal) ≤ t from bot_le)
  have hzero : V 0 omega = 0 := congrFun hV.zero omega
  linarith

theorem value_le_terminal
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    {t : NNReal} (ht : t ≤ T) (omega : Ω) :
    V t omega ≤ V T omega :=
  hV.monotone omega ht

theorem value_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    {t : NNReal} (ht : t ≤ T) :
    MemLp (V t) (2 : ENNReal) mu := by
  apply MemLp.of_le hV.terminal_memLp_two
    ((hV.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
  filter_upwards with omega
  calc
    ‖V t omega‖ = V t omega := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV.value_nonneg ht omega)]
    _ ≤ V T omega := hV.value_le_terminal ht omega
    _ = ‖V T omega‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (hV.value_nonneg (t := T) le_rfl omega)]

end SquareIntegrableIncreasingProcessData

noncomputable def squareIntegrableCompensatorIncrement
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r k : Nat) : Ω → Real :=
  if (grid T r).sampledTime k < (grid T r).sampledTime (k + 1) then
    fun omega => max 0
      (rawCompensatorIncrement V F mu T r k omega)
  else 0

noncomputable def squareIntegrableCompensatorCumulative
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r n : Nat) : Ω → Real :=
  finiteGridCompensatorCumulative T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r n

noncomputable def squareIntegrablePredictableCompensatorProcess
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r : Nat) : Process Ω :=
  finiteGridPredictableCompensatorProcess T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r

namespace SquareIntegrableIncreasingProcessData

theorem grid_increment_nonneg
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) (omega : Ω) :
    0 ≤ gridIncrement V T r k omega := by
  exact sub_nonneg.mpr (hV.monotone omega
    ((grid T r).sampledTime_mono (Nat.le_succ k)))

theorem grid_increment_eq_zero_of_grid_time_eq
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat)
    (h : (grid T r).sampledTime k =
      (grid T r).sampledTime (k + 1)) :
    gridIncrement V T r k = 0 := by
  funext omega
  simp [gridIncrement, h]

theorem grid_increment_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    MemLp (gridIncrement V T r k) (2 : ENNReal) mu := by
  by_cases hk : k < size T r
  · have hk0 : (grid T r).sampledTime k ≤ T := sampledTime_le_horizon r k
    have hk1 : (grid T r).sampledTime (k + 1) ≤ T := sampledTime_le_horizon r (k + 1)
    exact (hV.value_memLp_two hk1).sub (hV.value_memLp_two hk0)
  · have hkT : size T r ≤ k := le_of_not_gt hk
    have heq : (grid T r).sampledTime k =
        (grid T r).sampledTime (k + 1) := by
      rw [sampledTime_eq_terminal_of_le r k hkT,
        sampledTime_eq_terminal_of_le r (k + 1) (hkT.trans (Nat.le_succ _))]
    rw [hV.grid_increment_eq_zero_of_grid_time_eq r k heq]
    exact MemLp.zero

theorem grid_increment_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (gridIncrement V T r k) mu :=
  (hV.grid_increment_memLp_two r k).integrable (by norm_num)

theorem raw_compensator_increment_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    MemLp (rawCompensatorIncrement V F mu T r k)
      (2 : ENNReal) mu := by
  unfold rawCompensatorIncrement
  exact (hV.grid_increment_memLp_two r k).condExp (by norm_num)

theorem ae_raw_compensator_increment_nonneg
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    0 ≤ᵐ[mu] rawCompensatorIncrement V F mu T r k := by
  unfold rawCompensatorIncrement
  apply condExp_nonneg
  exact ae_of_all mu (hV.grid_increment_nonneg r k)

theorem compensator_increment_nonneg
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) (omega : Ω) :
    0 ≤ squareIntegrableCompensatorIncrement V F mu T r k omega := by
  classical
  unfold squareIntegrableCompensatorIncrement
  split_ifs
  · exact le_max_left _ _
  · simp

omit [IsProbabilityMeasure mu] in
@[simp] theorem squareIntegrableCompensatorIncrement_eq_zero_of_grid_time_eq
    (r k : Nat)
    (h : (grid T r).sampledTime k =
      (grid T r).sampledTime (k + 1)) :
    squareIntegrableCompensatorIncrement V F mu T r k = 0 := by
  simp [squareIntegrableCompensatorIncrement, h]

theorem compensator_increment_eq_raw_ae
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
      rawCompensatorIncrement V F mu T r k := by
  classical
  have htime :
      (grid T r).sampledTime k < (grid T r).sampledTime (k + 1) ∨
        (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) :=
    le_iff_lt_or_eq.mp ((grid T r).sampledTime_mono (Nat.le_succ k))
  cases htime with
  | inl hlt =>
      filter_upwards [hV.ae_raw_compensator_increment_nonneg r k] with omega h0
      simp only [squareIntegrableCompensatorIncrement, hlt, ↓reduceIte]
      exact max_eq_right h0
  | inr heq =>
      have hz := hV.grid_increment_eq_zero_of_grid_time_eq r k heq
      have hcond : rawCompensatorIncrement V F mu T r k =ᵐ[mu] 0 := by
        rw [show rawCompensatorIncrement V F mu T r k =
          mu[gridIncrement V T r k |
            F ((grid T r).sampledTime k)] by rfl]
        rw [show gridIncrement V T r k = 0 by exact hz]
        simp
      filter_upwards [hcond] with omega hzero
      change rawCompensatorIncrement V F mu T r k omega = 0 at hzero
      simp [squareIntegrableCompensatorIncrement, heq, hzero]

theorem compensator_increment_measurable
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    StronglyMeasurable[F ((grid T r).sampledTime k)]
      (squareIntegrableCompensatorIncrement V F mu T r k) := by
  classical
  unfold squareIntegrableCompensatorIncrement
  split_ifs with htime
  · have hcond : StronglyMeasurable[F ((grid T r).sampledTime k)]
        (rawCompensatorIncrement V F mu T r k) :=
      stronglyMeasurable_condExp
    exact ((stronglyMeasurable_const :
      StronglyMeasurable[F ((grid T r).sampledTime k)]
        (fun _ : Ω => (0 : Real))).measurable.max hcond.measurable).stronglyMeasurable
  · exact stronglyMeasurable_const

theorem compensator_increment_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    MemLp (squareIntegrableCompensatorIncrement V F mu T r k)
      (2 : ENNReal) mu := by
  have hRaw := hV.raw_compensator_increment_memLp_two r k
  classical
  unfold squareIntegrableCompensatorIncrement
  split_ifs with htime
  · simpa [max_comm] using hRaw.pos_part
  · exact MemLp.zero

theorem compensator_increment_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (squareIntegrableCompensatorIncrement V F mu T r k) mu :=
  (hV.compensator_increment_memLp_two r k).integrable (by norm_num)

theorem compensator_increment_sq_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (fun omega =>
      squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2) mu := by
  convert (hV.compensator_increment_memLp_two r k).integrable_norm_pow
    (p := 2) (by norm_num) using 1
  funext omega
  rw [Real.norm_eq_abs, sq_abs]

/-! ## Finite rows -/

theorem predictable_compensator_process_isStronglyPredictable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    IsStronglyPredictable F
      (squareIntegrablePredictableCompensatorProcess V F mu T r) := by
  change IsStronglyPredictable F
    (finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r)
  apply finiteGridCompensatorProcess_isStronglyPredictable
  intro k
  exact hV.compensator_increment_measurable r k

@[simp] theorem predictable_compensator_process_zero
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    squareIntegrablePredictableCompensatorProcess V F mu T r 0 = 0 := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r 0 = 0
  exact finiteGridPredictableCompensatorProcess_zero T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r

theorem predictable_compensator_process_nonneg
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (t : NNReal) (omega : Ω) :
    0 ≤ squareIntegrablePredictableCompensatorProcess V F mu T r t omega := by
  change 0 ≤ finiteGridPredictableCompensatorProcess T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r t omega
  apply finiteGridPredictableCompensatorProcess_nonneg
  intro k omega
  exact _hV.compensator_increment_nonneg r k omega

theorem predictable_compensator_process_mono
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (omega : Ω) :
    Monotone (squareIntegrablePredictableCompensatorProcess V F mu T r · omega) := by
  change Monotone (finiteGridPredictableCompensatorProcess T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r · omega)
  apply finiteGridPredictableCompensatorProcess_mono
  intro k omega
  exact _hV.compensator_increment_nonneg r k omega

theorem predictable_compensator_process_constant_after
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (omega : Ω) (t : NNReal) (ht : T ≤ t) :
    squareIntegrablePredictableCompensatorProcess V F mu T r t omega =
      squareIntegrablePredictableCompensatorProcess V F mu T r T omega := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r t omega =
    finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r T omega
  refine finiteGridPredictableCompensatorProcess_constant_after T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r ?_ omega t ht
  intro k hklt heq
  exact squareIntegrableCompensatorIncrement_eq_zero_of_grid_time_eq
    (V := V) (F := F) (mu := mu) r k heq

theorem predictable_compensator_process_terminal_eq_cumulative
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    squareIntegrablePredictableCompensatorProcess V F mu T r T =
      squareIntegrableCompensatorCumulative V F mu T r (size T r) := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r T =
    finiteGridCompensatorCumulative T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r (size T r)
  apply finiteGridPredictableCompensatorProcess_terminal_eq_cumulative
  intro k hklt heq
  exact squareIntegrableCompensatorIncrement_eq_zero_of_grid_time_eq
    (V := V) (F := F) (mu := mu) r k heq

theorem compensator_cumulative_mono
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r m n : Nat) (hmn : m ≤ n) (omega : Ω) :
    squareIntegrableCompensatorCumulative V F mu T r m omega ≤
      squareIntegrableCompensatorCumulative V F mu T r n omega := by
  change finiteGridCompensatorCumulative T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r m omega ≤
    finiteGridCompensatorCumulative T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r n omega
  apply finiteGridCompensatorCumulative_mono
  · exact hmn
  · intro k omega
    exact _hV.compensator_increment_nonneg r k omega

theorem compensator_cumulative_stronglyMeasurable
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r n : Nat) :
    StronglyMeasurable[F ((grid T r).sampledTime n)]
      (squareIntegrableCompensatorCumulative V F mu T r n) := by
  change StronglyMeasurable[F ((grid T r).sampledTime n)]
    (finiteGridCompensatorCumulative T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r n)
  apply finiteGridCompensatorCumulative_stronglyMeasurable
  intro k
  exact _hV.compensator_increment_measurable r k

theorem compensator_cumulative_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r n : Nat) :
    MemLp (squareIntegrableCompensatorCumulative V F mu T r n)
      (2 : ENNReal) mu := by
  unfold squareIntegrableCompensatorCumulative finiteGridCompensatorCumulative
  apply memLp_finsetSum
  intro k hk
  exact hV.compensator_increment_memLp_two r k

theorem predictable_compensator_process_terminal_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    MemLp (squareIntegrablePredictableCompensatorProcess V F mu T r T)
      (2 : ENNReal) mu := by
  rw [hV.predictable_compensator_process_terminal_eq_cumulative r]
  exact hV.compensator_cumulative_memLp_two r (size T r)

theorem grid_increment_sum_eq_terminal
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (omega : Ω) :
    (∑ k ∈ Finset.range (size T r),
      gridIncrement V T r k omega) = V T omega := by
  have hTel := Finset.sum_range_sub
    (fun k => V ((grid T r).sampledTime k) omega) (size T r)
  calc
    (∑ k ∈ Finset.range (size T r),
        gridIncrement V T r k omega) =
        ∑ k ∈ Finset.range (size T r),
          (V ((grid T r).sampledTime (k + 1)) omega -
            V ((grid T r).sampledTime k) omega) := by rfl
    _ = V ((grid T r).sampledTime (size T r)) omega -
        V ((grid T r).sampledTime 0) omega := hTel
    _ = V T omega - V 0 omega := by
      rw [sampledTime_size]
      have hz : (grid T r).sampledTime 0 = 0 := by
        simp [ChronologicalGrid.sampledTime,
          ChronologicalGrid.natIndex, grid_time]
      rw [hz]
    _ = V T omega := by simp [hV.zero]

theorem integral_compensator_increment_eq_integral_grid_increment
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    (∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
      ∫ omega, gridIncrement V T r k omega ∂mu := by
  calc
    (∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
        ∫ omega, rawCompensatorIncrement V F mu T r k omega ∂mu :=
      integral_congr_ae (hV.compensator_increment_eq_raw_ae r k)
    _ = ∫ omega, gridIncrement V T r k omega ∂mu :=
      integral_condExp (F.le ((grid T r).sampledTime k))

theorem predictable_compensator_process_terminal_expectation
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (∫ omega, squareIntegrablePredictableCompensatorProcess V F mu T r T omega ∂mu) =
      ∫ omega, V T omega ∂mu := by
  rw [hV.predictable_compensator_process_terminal_eq_cumulative r]
  unfold squareIntegrableCompensatorCumulative finiteGridCompensatorCumulative
  rw [integral_finsetSum]
  · have hSum :
        (∑ k ∈ Finset.range (size T r),
          ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
        ∑ k ∈ Finset.range (size T r),
          ∫ omega, gridIncrement V T r k omega ∂mu := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hV.integral_compensator_increment_eq_integral_grid_increment r k
    rw [hSum, ← integral_finsetSum]
    · apply integral_congr_ae
      filter_upwards with omega
      rw [hV.grid_increment_sum_eq_terminal r omega]
    · intro k hk
      exact hV.grid_increment_integrable r k
  · intro k hk
    exact hV.compensator_increment_integrable r k

theorem compensator_cumulative_terminal_sq_identity
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (fun omega =>
      squareIntegrableCompensatorCumulative V F mu T r (size T r) omega ^ 2) =
      (fun omega => ∑ k ∈ Finset.range (size T r),
        (2 * squareIntegrableCompensatorCumulative V F mu T r k omega *
            squareIntegrableCompensatorIncrement V F mu T r k omega +
          squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2)) := by
  change (fun omega =>
      finiteGridCompensatorCumulative T
        (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r
          (size T r) omega ^ 2) =
    (fun omega => ∑ k ∈ Finset.range (size T r),
      (2 * finiteGridCompensatorCumulative T
          (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r k omega *
        squareIntegrableCompensatorIncrement V F mu T r k omega +
        squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2))
  exact finiteGridCompensatorCumulative_terminal_sq_identity T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r

theorem cumulative_mul_compensator_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (fun omega =>
      squareIntegrableCompensatorCumulative V F mu T r k omega *
        squareIntegrableCompensatorIncrement V F mu T r k omega) mu := by
  exact (hV.compensator_cumulative_memLp_two r k).integrable_mul
    (hV.compensator_increment_memLp_two r k)

theorem cumulative_mul_grid_increment_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (fun omega =>
      squareIntegrableCompensatorCumulative V F mu T r k omega *
        gridIncrement V T r k omega) mu := by
  exact (hV.compensator_cumulative_memLp_two r k).integrable_mul
    (hV.grid_increment_memLp_two r k)

theorem cumulative_mul_compensator_eq_grid_increment
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    (∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
      squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
      ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
        gridIncrement V T r k omega ∂mu := by
  have hPMeas := hV.compensator_cumulative_stronglyMeasurable r k
  have hDeltaInt := hV.grid_increment_integrable r k
  have hPDeltaInt := hV.cumulative_mul_grid_increment_integrable r k
  have hRawEq : squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
      mu[((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) |
          F ((grid T r).sampledTime k)] := by
    change squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
      mu[gridIncrement V T r k |
        F ((grid T r).sampledTime k)]
    exact hV.compensator_increment_eq_raw_ae r k
  change (∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
      squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
    ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
      ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) omega ∂mu
  exact finiteGrid_predictable_cross_term_identity T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k)
    ((grid T r).natSample V)
    (squareIntegrableCompensatorCumulative V F mu T r k) r k
    hRawEq hPMeas hDeltaInt hPDeltaInt

theorem cumulative_grid_increment_sum_le_terminal_product
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (omega : Ω) :
    (∑ k ∈ Finset.range (size T r),
      squareIntegrableCompensatorCumulative V F mu T r k omega *
        gridIncrement V T r k omega) ≤
      squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
        V T omega := by
  have hTerm : ∀ k ∈ Finset.range (size T r),
      squareIntegrableCompensatorCumulative V F mu T r k omega *
          gridIncrement V T r k omega ≤
        squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
          gridIncrement V T r k omega := by
    intro k hk
    have hklt : k < size T r := Finset.mem_range.mp hk
    have hP := hV.compensator_cumulative_mono r k (size T r) hklt.le omega
    have hDelta := hV.grid_increment_nonneg r k omega
    exact mul_le_mul_of_nonneg_right hP hDelta
  calc
    (∑ k ∈ Finset.range (size T r),
      squareIntegrableCompensatorCumulative V F mu T r k omega *
        gridIncrement V T r k omega) ≤
      ∑ k ∈ Finset.range (size T r),
        squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
          gridIncrement V T r k omega :=
      Finset.sum_le_sum hTerm
    _ = squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
        (∑ k ∈ Finset.range (size T r),
          gridIncrement V T r k omega) := by
      rw [Finset.mul_sum]
    _ = squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
        V T omega := by rw [hV.grid_increment_sum_eq_terminal r omega]

theorem cumulative_terminal_mul_value_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    Integrable (fun omega =>
      squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
        V T omega) mu := by
  exact (hV.compensator_cumulative_memLp_two r (size T r)).integrable_mul
    hV.terminal_memLp_two

theorem integral_cumulative_grid_increment_sum_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (∫ omega, ∑ k ∈ Finset.range (size T r),
      squareIntegrableCompensatorCumulative V F mu T r k omega *
        gridIncrement V T r k omega ∂mu) ≤
      ∫ omega, squareIntegrableCompensatorCumulative V F mu T r (size T r) omega *
        V T omega ∂mu := by
  apply integral_mono_ae
  · apply integrable_finsetSum
    intro k hk
    exact hV.cumulative_mul_grid_increment_integrable r k
  · exact hV.cumulative_terminal_mul_value_integrable r
  · exact ae_of_all mu (hV.cumulative_grid_increment_sum_le_terminal_product r)

/-! ## The source-independent `L²` estimate -/

theorem integral_compensator_increment_sq_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    (∫ omega,
      squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) ≤
      ∫ omega, gridIncrement V T r k omega ^ 2 ∂mu := by
  have hRaw := hV.raw_compensator_increment_memLp_two r k
  have hDelta := hV.grid_increment_memLp_two r k
  have hContraction :
      eLpNorm (rawCompensatorIncrement V F mu T r k)
          (2 : ENNReal) mu ≤
        eLpNorm (gridIncrement V T r k)
          (2 : ENNReal) mu := by
    unfold rawCompensatorIncrement
    exact eLpNorm_condExp_le_eLpNorm
      (μ := mu) (m := F ((grid T r).sampledTime k))
      (p := (2 : ENNReal)) (gridIncrement V T r k) (by norm_num)
  have hSq := integral_norm_sq_le_of_eLpNorm_two_le hRaw hDelta hContraction
  have hSq' :
      (∫ omega, rawCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) ≤
        ∫ omega, gridIncrement V T r k omega ^ 2 ∂mu := by
    simpa only [Real.norm_eq_abs, sq_abs] using hSq
  calc
    (∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) =
        ∫ omega, rawCompensatorIncrement V F mu T r k omega ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [hV.compensator_increment_eq_raw_ae r k] with omega hEq
      rw [hEq]
    _ ≤ _ := hSq'

theorem grid_increment_sq_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r k : Nat) :
    Integrable (fun omega => gridIncrement V T r k omega ^ 2) mu := by
  convert (hV.grid_increment_memLp_two r k).integrable_norm_pow
    (p := 2) (by norm_num) using 1
  funext omega
  rw [Real.norm_eq_abs, sq_abs]

theorem grid_sum_sq_le_terminal_sq
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) (omega : Ω) :
    (∑ k ∈ Finset.range (size T r),
      gridIncrement V T r k omega ^ 2) ≤
      (V T omega) ^ 2 := by
  let N := size T r
  have hnonneg : ∀ k,
      0 ≤ gridIncrement V T r k omega :=
    fun k => hV.grid_increment_nonneg r k omega
  have hsum_sq : ∀ n : Nat,
      (∑ k ∈ Finset.range n,
        gridIncrement V T r k omega ^ 2) ≤
      (∑ k ∈ Finset.range n,
        gridIncrement V T r k omega) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hnon : 0 ≤ gridIncrement V T r n omega :=
          hnonneg n
        have hsum : 0 ≤ ∑ k ∈ Finset.range n,
            gridIncrement V T r k omega :=
          Finset.sum_nonneg (fun k hk => hnonneg k)
        nlinarith [ih]
  calc
    (∑ k ∈ Finset.range (size T r),
        gridIncrement V T r k omega ^ 2) ≤
      (∑ k ∈ Finset.range (size T r),
        gridIncrement V T r k omega) ^ 2 := by
          simpa [N] using hsum_sq N
    _ = (V T omega) ^ 2 := by rw [hV.grid_increment_sum_eq_terminal r omega]

theorem integral_sum_compensator_increment_sq_le_terminal_sq
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (∑ k ∈ Finset.range (size T r),
      ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) ≤
      ∫ omega, (V T omega) ^ 2 ∂mu := by
  calc
    (∑ k ∈ Finset.range (size T r),
        ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) ≤
      ∑ k ∈ Finset.range (size T r),
        ∫ omega, gridIncrement V T r k omega ^ 2 ∂mu := by
      apply Finset.sum_le_sum
      intro k hk
      exact hV.integral_compensator_increment_sq_le r k
    _ = ∫ omega, ∑ k ∈ Finset.range (size T r),
        gridIncrement V T r k omega ^ 2 ∂mu := by
      rw [integral_finsetSum]
      intro k hk
      exact hV.grid_increment_sq_integrable r k
    _ ≤ ∫ omega, (V T omega) ^ 2 ∂mu := by
      apply integral_mono_ae
      · apply integrable_finsetSum
        intro k hk
        exact hV.grid_increment_sq_integrable r k
      · exact hV.terminal_memLp_two.integrable_sq
      · exact ae_of_all mu (hV.grid_sum_sq_le_terminal_sq r)

theorem cumulative_terminal_sq_integral_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (∫ omega,
      squareIntegrableCompensatorCumulative V F mu T r (size T r) omega ^ 2 ∂mu) ≤
      6 * ∫ omega, (V T omega) ^ 2 ∂mu := by
  let N := size T r
  have hSqEq := hV.compensator_cumulative_terminal_sq_identity r
  have hTermInt : ∀ k ∈ Finset.range N, Integrable (fun omega =>
      2 * squareIntegrableCompensatorCumulative V F mu T r k omega *
          squareIntegrableCompensatorIncrement V F mu T r k omega +
        squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2) mu := by
    intro k hk
    have h1 := (hV.cumulative_mul_compensator_integrable r k).const_mul 2
    have h2 := hV.compensator_increment_sq_integrable r k
    have h := h1.add h2
    apply h.congr
    filter_upwards [] with omega
    change 2 * (squareIntegrableCompensatorCumulative V F mu T r k omega *
        squareIntegrableCompensatorIncrement V F mu T r k omega) +
      squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 = _
    ring
  have hSqSplit :
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) =
      2 * (∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
          squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) +
      ∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu := by
    rw [show (fun omega =>
      squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2) = _ by
      simpa [N] using hSqEq]
    rw [integral_finsetSum]
    · rw [show (∑ x ∈ Finset.range N,
        ∫ omega, (2 * squareIntegrableCompensatorCumulative V F mu T r x omega *
            squareIntegrableCompensatorIncrement V F mu T r x omega +
          squareIntegrableCompensatorIncrement V F mu T r x omega ^ 2) ∂mu) =
        ∑ x ∈ Finset.range N,
          (2 * (∫ omega, squareIntegrableCompensatorCumulative V F mu T r x omega *
              squareIntegrableCompensatorIncrement V F mu T r x omega ∂mu) +
            ∫ omega, squareIntegrableCompensatorIncrement V F mu T r x omega ^ 2 ∂mu) by
          apply Finset.sum_congr rfl
          intro k hk
          calc
            (∫ omega, (2 * squareIntegrableCompensatorCumulative V F mu T r k omega *
                squareIntegrableCompensatorIncrement V F mu T r k omega +
              squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2) ∂mu) =
                ∫ omega, 2 * (squareIntegrableCompensatorCumulative V F mu T r k omega *
                  squareIntegrableCompensatorIncrement V F mu T r k omega) +
                squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu := by
              apply integral_congr_ae
              exact ae_of_all mu (fun omega => by ring)
            _ = (∫ omega, 2 * (squareIntegrableCompensatorCumulative V F mu T r k omega *
                  squareIntegrableCompensatorIncrement V F mu T r k omega) ∂mu) +
                ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu :=
              integral_add (hV.cumulative_mul_compensator_integrable r k |>.const_mul 2)
                (hV.compensator_increment_sq_integrable r k)
            _ = _ := by rw [integral_const_mul]]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    · exact hTermInt
  have hCrossReplace :
      (∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
          squareIntegrableCompensatorIncrement V F mu T r k omega ∂mu) =
      ∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
          gridIncrement V T r k omega ∂mu := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hV.cumulative_mul_compensator_eq_grid_increment r k
  have hCrossIntegral :
      (∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
          gridIncrement V T r k omega ∂mu) =
      ∫ omega, ∑ k ∈ Finset.range N,
        squareIntegrableCompensatorCumulative V F mu T r k omega *
          gridIncrement V T r k omega ∂mu := by
    exact (integral_finsetSum (Finset.range N) (fun k hk =>
      hV.cumulative_mul_grid_increment_integrable r k)).symm
  have hCrossBound :
      (∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorCumulative V F mu T r k omega *
          gridIncrement V T r k omega ∂mu) ≤
      ∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega *
        V T omega ∂mu := by
    rw [hCrossIntegral]
    exact hV.integral_cumulative_grid_increment_sum_le r
  have hDsqBound :
      (∑ k ∈ Finset.range N,
        ∫ omega, squareIntegrableCompensatorIncrement V F mu T r k omega ^ 2 ∂mu) ≤
      ∫ omega, (V T omega) ^ 2 ∂mu := by
    exact hV.integral_sum_compensator_increment_sq_le_terminal_sq r
  have hMain :
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) ≤
      2 * (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega *
        V T omega ∂mu) + ∫ omega, (V T omega) ^ 2 ∂mu := by
    rw [hSqSplit, hCrossReplace]
    exact add_le_add (mul_le_mul_of_nonneg_left hCrossBound (by norm_num)) hDsqBound
  have hPmem := hV.compensator_cumulative_memLp_two r N
  have hPTerm := hV.terminal_memLp_two
  have hYoung :
      2 * (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega *
        V T omega ∂mu) ≤
      (1 / 2 : Real) * (∫ omega,
        squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) +
      2 * (∫ omega, (V T omega) ^ 2 ∂mu) := by
    have hInt := integral_mono_ae
      ((hPmem.integrable_mul hPTerm).const_mul 2)
      ((hPmem.integrable_sq.const_mul (1 / 2 : Real)).add
        (hPTerm.integrable_sq.const_mul 2))
      (ae_of_all mu (fun omega => by
        change 2 * (squareIntegrableCompensatorCumulative V F mu T r N omega *
            V T omega) ≤
          (1 / 2 : Real) * squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 +
            2 * (V T omega) ^ 2
        nlinarith [sq_nonneg
          (squareIntegrableCompensatorCumulative V F mu T r N omega -
            2 * V T omega)]))
    calc
      2 * (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega *
          V T omega ∂mu) =
          ∫ omega, 2 * (squareIntegrableCompensatorCumulative V F mu T r N omega *
            V T omega) ∂mu := by rw [integral_const_mul]
      _ ≤ ∫ omega, (1 / 2 : Real) *
          squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 +
          2 * (V T omega) ^ 2 ∂mu := hInt
      _ = _ := by
        rw [integral_add (hPmem.integrable_sq.const_mul (1 / 2 : Real))
          (hPTerm.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul]
  have hMain' :
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) ≤
      (1 / 2 : Real) * (∫ omega,
        squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) +
      3 * (∫ omega, (V T omega) ^ 2 ∂mu) := by
    calc
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) ≤
          2 * (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega *
            V T omega ∂mu) + ∫ omega, (V T omega) ^ 2 ∂mu := hMain
      _ ≤ ((1 / 2 : Real) * (∫ omega,
            squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) +
          2 * (∫ omega, (V T omega) ^ 2 ∂mu)) +
          ∫ omega, (V T omega) ^ 2 ∂mu := add_le_add hYoung (le_refl _)
      _ = _ := by ring
  have hBound :
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu) ≤
      6 * ∫ omega, (V T omega) ^ 2 ∂mu := by
    nlinarith [hMain', sq_nonneg
      (∫ omega, squareIntegrableCompensatorCumulative V F mu T r N omega ^ 2 ∂mu),
      integral_nonneg_of_ae (μ := mu) (Filter.Eventually.of_forall fun omega =>
        sq_nonneg (V T omega))]
  simpa [N] using hBound

theorem predictable_compensator_process_terminal_sq_integral_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r : Nat) :
    (∫ omega,
      squareIntegrablePredictableCompensatorProcess V F mu T r T omega ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
  rw [hV.predictable_compensator_process_terminal_eq_cumulative r]
  have hnonneg : 0 ≤ ∫ omega, (V T omega) ^ 2 ∂mu :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun omega => sq_nonneg (V T omega))
  calc
    (∫ omega,
        squareIntegrableCompensatorCumulative V F mu T r (size T r) omega ^ 2 ∂mu) ≤
        6 * ∫ omega, (V T omega) ^ 2 ∂mu :=
      hV.cumulative_terminal_sq_integral_le r
    _ ≤ 8 * ∫ omega, (V T omega) ^ 2 ∂mu := by nlinarith

/-! ## Public certificate and the Jordan consumer -/

structure SquareIntegrableIncreasingProcessCompensatorRowsData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) where
  increment_nonneg : ∀ r k omega,
    0 ≤ squareIntegrableCompensatorIncrement V F mu T r k omega
  increment_measurable : ∀ r k,
    StronglyMeasurable[F ((grid T r).sampledTime k)]
      (squareIntegrableCompensatorIncrement V F mu T r k)
  increment_eq_raw_ae : ∀ r k,
    squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
      rawCompensatorIncrement V F mu T r k
  process_predictable : ∀ r,
    IsStronglyPredictable F
      (squareIntegrablePredictableCompensatorProcess V F mu T r)
  process_zero : ∀ r,
    squareIntegrablePredictableCompensatorProcess V F mu T r 0 = 0
  process_nonneg : ∀ r t omega,
    0 ≤ squareIntegrablePredictableCompensatorProcess V F mu T r t omega
  process_mono : ∀ r omega,
    Monotone (squareIntegrablePredictableCompensatorProcess V F mu T r · omega)
  process_constant_after : ∀ r omega t, T ≤ t →
    squareIntegrablePredictableCompensatorProcess V F mu T r t omega =
      squareIntegrablePredictableCompensatorProcess V F mu T r T omega
  process_terminal_eq_cumulative : ∀ r,
    squareIntegrablePredictableCompensatorProcess V F mu T r T =
      squareIntegrableCompensatorCumulative V F mu T r (size T r)
  process_sampled_increment : ∀ r i, i < size T r →
    (fun omega =>
      squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime (i + 1)) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime i) omega) =
      squareIntegrableCompensatorIncrement V F mu T r i
  residual_grid_condExp_law : ∀ r i, i < size T r →
    mu[(fun omega =>
      (V ((grid T r).sampledTime (i + 1)) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime i) omega)) |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0
  terminal_expectation : ∀ r,
    (∫ omega, squareIntegrablePredictableCompensatorProcess V F mu T r T omega ∂mu) =
      ∫ omega, V T omega ∂mu
  testing_identity : ∀ (r N : Nat), N ≤ size T r →
    ∀ (K : Nat → Ω → Real),
      StronglyAdapted ((grid T r).sampledFiltration F) K →
      (∀ k, Integrable
        (K k * ((grid T r).natSample V (k + 1) -
          (grid T r).natSample V k)) mu) →
      (∀ k, Integrable
        (K k * squareIntegrableCompensatorIncrement V F mu T r k) mu) →
      (∫ omega, discretePredictableIntegral K
        ((grid T r).natSample V) N omega ∂mu) =
        ∫ omega, (∑ k ∈ Finset.range N,
          K k omega * squareIntegrableCompensatorIncrement V F mu T r k omega) ∂mu
  terminal_memLp_two : ∀ r,
    MemLp (squareIntegrablePredictableCompensatorProcess V F mu T r T)
      (2 : ENNReal) mu
  terminal_L2_bound : ∀ r,
    (∫ omega,
      squareIntegrablePredictableCompensatorProcess V F mu T r T omega ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu

theorem predictable_compensator_process_sampled_increment
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r i : Nat) (hi : i < size T r) :
    (fun omega =>
      squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime (i + 1)) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime i) omega) =
      squareIntegrableCompensatorIncrement V F mu T r i := by
  change (fun omega =>
      finiteGridPredictableCompensatorProcess T
          (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r
          ((grid T r).sampledTime (i + 1)) omega -
        finiteGridPredictableCompensatorProcess T
          (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r
          ((grid T r).sampledTime i) omega) =
    squareIntegrableCompensatorIncrement V F mu T r i
  refine finiteGridPredictableCompensatorProcess_sampled_increment T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r i hi ?_
  intro k hk heq
  exact squareIntegrableCompensatorIncrement_eq_zero_of_grid_time_eq
    (V := V) (F := F) (mu := mu) r k heq

theorem compensator_grid_condExp_law
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r i : Nat) :
    mu[gridIncrement V T r i -
      squareIntegrableCompensatorIncrement V F mu T r i |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0 := by
  have hGridInt := hV.grid_increment_integrable r i
  have hCompInt := hV.compensator_increment_integrable r i
  have hSub := condExp_sub hGridInt hCompInt
    (F ((grid T r).sampledTime i))
  have hRaw := hV.compensator_increment_eq_raw_ae r i
  have hCompMeas := hV.compensator_increment_measurable r i
  have hCompCE :
      mu[squareIntegrableCompensatorIncrement V F mu T r i |
          F ((grid T r).sampledTime i)] =
        squareIntegrableCompensatorIncrement V F mu T r i :=
    condExp_of_stronglyMeasurable (F.le _) hCompMeas hCompInt
  filter_upwards [hSub, hRaw] with omega hSub hRaw
  rw [hCompCE] at hSub
  rw [hSub]
  change rawCompensatorIncrement V F mu T r i omega -
    squareIntegrableCompensatorIncrement V F mu T r i omega = 0
  rw [hRaw]
  ring

theorem grid_predictable_testing_identity
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (r N : Nat) (_hN : N ≤ size T r) (K : Nat → Ω → Real)
    (hK : StronglyAdapted ((grid T r).sampledFiltration F) K)
    (hSourceInt : ∀ k, Integrable
      (K k * ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k)) mu)
    (hCompInt : ∀ k, Integrable
      (K k * squareIntegrableCompensatorIncrement V F mu T r k) mu) :
    (∫ omega, discretePredictableIntegral K
        ((grid T r).natSample V) N omega ∂mu) =
      ∫ omega, (∑ k ∈ Finset.range N,
        K k omega * squareIntegrableCompensatorIncrement V F mu T r k omega) ∂mu := by
  have hD_raw : ∀ k, k < N →
      squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
        mu[(grid T r).natSample V (k + 1) -
          (grid T r).natSample V k |
            F ((grid T r).sampledTime k)] := by
    intro k hk
    change squareIntegrableCompensatorIncrement V F mu T r k =ᵐ[mu]
      mu[gridIncrement V T r k |
        F ((grid T r).sampledTime k)]
    exact hV.compensator_increment_eq_raw_ae r k
  have hMInt : ∀ k, k < N →
      Integrable ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) mu := by
    intro k hk
    change Integrable (gridIncrement V T r k) mu
    exact hV.grid_increment_integrable r k
  exact finiteGrid_predictable_testing_identity T
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k)
    ((grid T r).natSample V) r N hD_raw K hK hMInt hSourceInt hCompInt

theorem factorialGridSquareIntegrableIncreasingCompensatorRows_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    Nonempty (SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) := by
  refine ⟨{
    increment_nonneg := ?_,
    increment_measurable := ?_,
    increment_eq_raw_ae := ?_,
    process_predictable := ?_,
    process_zero := ?_,
    process_nonneg := ?_,
    process_mono := ?_,
    process_constant_after := ?_,
    process_terminal_eq_cumulative := ?_,
    process_sampled_increment := ?_,
    residual_grid_condExp_law := ?_,
    terminal_expectation := ?_,
    testing_identity := ?_,
    terminal_memLp_two := ?_,
    terminal_L2_bound := ?_ }⟩
  · intro r k omega
    exact hV.compensator_increment_nonneg r k omega
  · intro r k
    exact hV.compensator_increment_measurable r k
  · intro r k; exact hV.compensator_increment_eq_raw_ae r k
  · intro r; exact hV.predictable_compensator_process_isStronglyPredictable r
  · intro r
    exact hV.predictable_compensator_process_zero r
  · intro r t omega; exact hV.predictable_compensator_process_nonneg r t omega
  · intro r omega; exact hV.predictable_compensator_process_mono r omega
  · intro r omega t ht; exact hV.predictable_compensator_process_constant_after r omega t ht
  · intro r
    exact hV.predictable_compensator_process_terminal_eq_cumulative r
  · intro r i hi
    exact hV.predictable_compensator_process_sampled_increment r i hi
  · intro r i hi
    have hLaw := hV.compensator_grid_condExp_law r i
    have hEq := hV.predictable_compensator_process_sampled_increment r i hi
    have hResidualEq :
        (fun omega =>
          (V ((grid T r).sampledTime (i + 1)) omega -
            squareIntegrablePredictableCompensatorProcess V F mu T r
              ((grid T r).sampledTime (i + 1)) omega) -
          (V ((grid T r).sampledTime i) omega -
            squareIntegrablePredictableCompensatorProcess V F mu T r
              ((grid T r).sampledTime i) omega)) =
        gridIncrement V T r i -
          squareIntegrableCompensatorIncrement V F mu T r i := by
      funext omega
      have hP := congrFun hEq omega
      change (V ((grid T r).sampledTime (i + 1)) omega -
          squareIntegrablePredictableCompensatorProcess V F mu T r
            ((grid T r).sampledTime (i + 1)) omega) -
        (V ((grid T r).sampledTime i) omega -
          squareIntegrablePredictableCompensatorProcess V F mu T r
            ((grid T r).sampledTime i) omega) =
        (V ((grid T r).sampledTime (i + 1)) omega -
          V ((grid T r).sampledTime i) omega) -
          squareIntegrableCompensatorIncrement V F mu T r i omega
      rw [sub_eq_iff_eq_add] at hP
      linarith
    rw [hResidualEq]
    exact hLaw
  · intro r; exact hV.predictable_compensator_process_terminal_expectation r
  · intro r N hN K hK hSourceInt hCompInt
    exact hV.grid_predictable_testing_identity r N hN K hK hSourceInt hCompInt
  · intro r; exact hV.predictable_compensator_process_terminal_memLp_two r
  · intro r; exact hV.predictable_compensator_process_terminal_sq_integral_le r

theorem exists_factorialGridSquareIntegrableIncreasingCompensatorRows
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    Nonempty (SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) :=
  factorialGridSquareIntegrableIncreasingCompensatorRows_producer
    (F := F) (mu := mu) hV

/-! The Jordan components supplied by the generic regularization endpoint are
consumed directly; no deterministic source wrapper is introduced. -/

theorem exists_factorialGridSquareIntegrableIncreasingCompensatorRows_of_commonStopJordanComponents
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Ω → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Ω}
    {Vbound : Ω → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B Vbound L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω} {cutoff : Nat → Nat}
    {A : Process Ω}
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff)
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
      hNested A bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ hPlus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aplus T,
      ∃ hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T,
        Nonempty (SquareIntegrableIncreasingProcessCompensatorRowsData
          (F := F) (mu := mu) hPlus) ∧
        Nonempty (SquareIntegrableIncreasingProcessCompensatorRowsData
          (F := F) (mu := mu) hMinus) := by
  let hPlus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aplus T := {
    stronglyAdapted := hReg.jordanPositive_stronglyAdapted
    rightContinuous := hReg.jordanPositive_rightContinuous
    monotone := hReg.jordanPositive_monotone
    zero := hReg.jordanPositive_zero
    constant_after := hReg.jordanPositive_constant_after
    terminal_memLp_two := hReg.jordanPositive_terminal_memLp }
  let hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T := {
    stronglyAdapted := hReg.jordanNegative_stronglyAdapted
    rightContinuous := hReg.jordanNegative_rightContinuous
    monotone := hReg.jordanNegative_monotone
    zero := hReg.jordanNegative_zero
    constant_after := hReg.jordanNegative_constant_after
    terminal_memLp_two := hReg.jordanNegative_terminal_memLp }
  exact ⟨hPlus, hMinus,
    factorialGridSquareIntegrableIncreasingCompensatorRows_producer hPlus,
    factorialGridSquareIntegrableIncreasingCompensatorRows_producer hMinus⟩

end SquareIntegrableIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
