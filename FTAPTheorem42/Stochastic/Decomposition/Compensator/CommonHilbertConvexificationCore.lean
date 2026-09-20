/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedSkeletonLimit

/-!
# Source-independent common Hilbert convexification of compensator rows

This file contains the part of the finite-grid Hilbert argument which only
uses the row-level API.  In particular, it does not mention the bounded
compensator construction or the square-integrable construction.  A single
`TailConvexWeights` family is selected for the terminal residual coordinate
and every value on the stopped right-dense skeleton.

The source-specific files only provide an instance of
`CommonHilbertRowsData`; they do not repeat the direct-sum compactness or the
finite convex-row calculus.
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

open DirectSumCoordinateControl

/-! ## The source-independent row interface -/

structure CommonHilbertRowsData
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal)
    (source : Ω → Real)
    (row : Nat → Process Ω)
    (residual : Nat → Ω → Real)
    (sourceBound rowBound : Real) where
  sourceToLp : Lp Real (2 : ENNReal) mu
  rowToLp : Nat → NNReal → Lp Real (2 : ENNReal) mu
  residualToLp : Nat → Lp Real (2 : ENNReal) mu
  sourceToLp_coeFn_ae : ⇑sourceToLp =ᵐ[mu] source
  rowToLp_coeFn_ae : ∀ r t, ⇑(rowToLp r t) =ᵐ[mu] row r t
  residualToLp_coeFn_ae : ∀ r, ⇑(residualToLp r) =ᵐ[mu] residual r
  sourceBound_nonneg : 0 ≤ sourceBound
  rowBound_nonneg : 0 ≤ rowBound
  sourceToLp_norm_le : ‖sourceToLp‖ ≤ sourceBound
  rowToLp_norm_le : ∀ r t, ‖rowToLp r t‖ ≤ rowBound
  residualToLp_norm_le : ∀ r, ‖residualToLp r‖ ≤ sourceBound + rowBound
  row_value_memLp_two : ∀ r t, MemLp (row r t) (2 : ENNReal) mu
  residual_memLp_two : ∀ r, MemLp (residual r) (2 : ENNReal) mu
  row_isStronglyPredictable : ∀ r, IsStronglyPredictable F (row r)
  row_zero : ∀ r, row r 0 = 0
  row_nonnegative : ∀ r t omega, 0 ≤ row r t omega
  row_mono : ∀ r omega, Monotone (row r · omega)
  row_leftContinuous : ∀ r omega t,
    ContinuousWithinAt (row r · omega) (Iic t) t
  row_constant_after : ∀ r omega t, T ≤ t → row r t omega = row r T omega
  row_terminal_L2_bound : ∀ r,
    (∫ omega, (row r T omega) ^ 2 ∂mu) ≤ rowBound ^ 2
  row_terminal_expectation : ∀ r,
    (∫ omega, row r T omega ∂mu) = ∫ omega, source omega ∂mu
  residual_eq_source_sub_row : ∀ r,
    residual r = fun omega => source omega - row r T omega

namespace CommonHilbertRowsData

noncomputable def coordinateBound
    (_h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (i : Nat) : Real :=
  match i with
  | 0 => sourceBound + rowBound
  | _ => rowBound

omit [IsProbabilityMeasure mu] in
theorem coordinateBound_nonneg
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (i : Nat) : 0 ≤ h.coordinateBound i := by
  cases i with
  | zero => exact add_nonneg h.sourceBound_nonneg h.rowBound_nonneg
  | succ j => exact h.rowBound_nonneg

noncomputable def coordinateSequence
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound) :
    Nat → ∀ _i : Nat, Lp Real (2 : ENNReal) mu :=
  fun r i => match i with
  | 0 => h.residualToLp r
  | j + 1 => h.rowToLp r (stoppedLimitSkeleton T j).1

omit [IsProbabilityMeasure mu] in
theorem coordinateSequence_norm_bound
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound) :
  ∀ r i, ‖h.coordinateSequence r i‖ ≤ h.coordinateBound i := by
  intro r i
  cases i with
  | zero =>
      change ‖h.residualToLp r‖ ≤ sourceBound + rowBound
      exact h.residualToLp_norm_le r
  | succ j => exact h.rowToLp_norm_le r (stoppedLimitSkeleton T j).1

noncomputable def normalizedCoordinateSequence
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound) :
    Nat → lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal) :=
  coordinateToLp geometricLpEnvelope
    (normalizeCoordinates h.coordinateBound
      h.coordinateSequence)
    (fun r i => by
      exact
        normalizeCoordinates_norm_le
          h.coordinateBound h.coordinateSequence
          h.coordinateBound_nonneg h.coordinateSequence_norm_bound r i)

noncomputable def coordinateLimit
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (i : Nat) : Lp Real (2 : ENNReal) mu :=
  (DirectSumCoordinateControl.geometricNormalization h.coordinateBound i)⁻¹ • y i

omit [IsProbabilityMeasure mu] in
theorem exists_common_coordinate_convexification
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)),
      Tendsto (fun n => (w n).applyVector h.normalizedCoordinateSequence)
        atTop (𝓝 y) ∧
      ∀ i : Nat,
        Tendsto (fun n => (w n).applyVector (fun r => h.coordinateSequence r i))
          atTop (𝓝 (h.coordinateLimit y i)) := by
  obtain ⟨w, y, hDirect, hCoord⟩ :=
    DirectSumCoordinateControl.exists_common_tailConvexification_of_finite_coordinateBounds
      (B := h.coordinateBound) (Z := h.coordinateSequence)
      h.coordinateBound_nonneg h.coordinateSequence_norm_bound
  refine ⟨w, y, ?_, ?_⟩
  · simpa only [normalizedCoordinateSequence] using hDirect
  · intro i
    simpa only [coordinateLimit] using hCoord i

/-! ## Generic raw rows and their convex combinations -/

noncomputable def convexRow
    (_h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) : Process Ω :=
  fun t omega => w.apply (fun r => row r t) omega

noncomputable def residualConvexRow
    (_h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) : Ω → Real :=
  w.apply residual

noncomputable def convexCoordinateToLp
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (j : Nat) : Lp Real (2 : ENNReal) mu :=
  w.applyVector (fun r => h.rowToLp r (stoppedLimitSkeleton T j).1)

noncomputable def convexTerminalCoordinateToLp
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) : Lp Real (2 : ENNReal) mu :=
  w.applyVector (fun r => h.rowToLp r T)

noncomputable def residualConvexCoordinateToLp
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) : Lp Real (2 : ENNReal) mu :=
  w.applyVector (fun r => h.residualToLp r)

omit [IsProbabilityMeasure mu] in
theorem convexRow_eq_finset_sum
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    h.convexRow w = fun t omega => ∑ r ∈ w.support, w.weight r * row r t omega :=
  rfl

omit [IsProbabilityMeasure mu] in
theorem residualConvexRow_eq_finset_sum
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    h.residualConvexRow w = fun omega =>
      ∑ r ∈ w.support, w.weight r * residual r omega :=
  rfl

omit [IsProbabilityMeasure mu] in
theorem convexCoordinateToLp_coeFn_ae
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (j : Nat) :
    ⇑(h.convexCoordinateToLp w j) =ᵐ[mu]
      h.convexRow w (stoppedLimitSkeleton T j).1 := by
  exact w.applyVector_coeFn_ae
    (fun r => h.rowToLp r (stoppedLimitSkeleton T j).1)
    (fun r => row r (stoppedLimitSkeleton T j).1)
    (fun r => h.rowToLp_coeFn_ae r (stoppedLimitSkeleton T j).1)

omit [IsProbabilityMeasure mu] in
theorem convexTerminalCoordinateToLp_coeFn_ae
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    ⇑(h.convexTerminalCoordinateToLp w) =ᵐ[mu] h.convexRow w T := by
  exact w.applyVector_coeFn_ae (fun r => h.rowToLp r T) (fun r => row r T)
    (fun r => h.rowToLp_coeFn_ae r T)

omit [IsProbabilityMeasure mu] in
theorem residualConvexCoordinateToLp_coeFn_ae
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    ⇑(h.residualConvexCoordinateToLp w) =ᵐ[mu] h.residualConvexRow w := by
  exact w.applyVector_coeFn_ae (fun r => h.residualToLp r) residual
    h.residualToLp_coeFn_ae

theorem stronglyPredictable_finset_sum
    (c : Nat → Real) (P : Nat → Process Ω) (s : Finset Nat)
    (hP : ∀ r ∈ s, IsStronglyPredictable F (P r)) :
    IsStronglyPredictable F
      (fun t omega => ∑ r ∈ s, c r * P r t omega) := by
  unfold IsStronglyPredictable
  induction s using Finset.induction_on with
  | empty =>
      change StronglyMeasurable[F.predictable]
        (fun _ : NNReal × Ω => (0 : Real))
      exact stronglyMeasurable_const
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      change StronglyMeasurable[F.predictable]
        (Function.uncurry (fun t omega =>
          c r * P r t omega + ∑ j ∈ s, c j * P j t omega))
      exact ((hP r (Finset.mem_insert_self r s)).const_mul (c r)).add
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

omit [IsProbabilityMeasure mu] in
theorem convexRow_isStronglyPredictable
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    IsStronglyPredictable F (h.convexRow w) := by
  rw [h.convexRow_eq_finset_sum]
  apply stronglyPredictable_finset_sum
  intro r hr
  exact h.row_isStronglyPredictable r

omit [IsProbabilityMeasure mu] in
theorem convexRow_zero
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) : h.convexRow w 0 = 0 := by
  funext omega
  rw [h.convexRow_eq_finset_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [h.row_zero r]
  simp

omit [IsProbabilityMeasure mu] in
theorem convexRow_nonnegative
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (t : NNReal) (omega : Ω) :
    0 ≤ h.convexRow w t omega := by
  rw [h.convexRow_eq_finset_sum]
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (w.nonneg r hr) (h.row_nonnegative r t omega)

omit [IsProbabilityMeasure mu] in
theorem convexRow_mono
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (omega : Ω) :
    Monotone (h.convexRow w · omega) := by
  intro s t hst
  rw [h.convexRow_eq_finset_sum]
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (h.row_mono r omega hst) (w.nonneg r hr)

omit [IsProbabilityMeasure mu] in
theorem convexRow_constant_after
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) {t : NNReal} (ht : T ≤ t) :
    h.convexRow w t = h.convexRow w T := by
  funext omega
  rw [h.convexRow_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [h.row_constant_after r omega t ht]

omit [IsProbabilityMeasure mu] in
theorem convexRow_leftContinuous
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (omega : Ω) (t : NNReal) :
    ContinuousWithinAt (h.convexRow w · omega) (Iic t) t := by
  rw [h.convexRow_eq_finset_sum]
  change ContinuousWithinAt
    (fun u => ∑ r ∈ w.support, w.weight r * row r u omega) (Iic t) t
  induction w.support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Iic t) t)
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact ((h.row_leftContinuous r omega t).const_mul (w.weight r)).add ih

omit [IsProbabilityMeasure mu] in
theorem convexRow_value_memLp_two
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (t : NNReal) :
    MemLp (h.convexRow w t) (2 : ENNReal) mu := by
  rw [h.convexRow_eq_finset_sum]
  apply memLp_finsetSum
  intro r hr
  exact (h.row_value_memLp_two r t).const_smul (w.weight r)

omit [IsProbabilityMeasure mu] in
theorem residualConvexRow_memLp_two
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    MemLp (h.residualConvexRow w) (2 : ENNReal) mu := by
  rw [h.residualConvexRow_eq_finset_sum]
  apply memLp_finsetSum
  intro r hr
  exact (h.residual_memLp_two r).const_smul (w.weight r)

omit [IsProbabilityMeasure mu] in
theorem residualConvexRow_eq_source_sub_compensator
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    h.residualConvexRow w = fun omega => source omega - h.convexRow w T omega := by
  funext omega
  rw [h.residualConvexRow_eq_finset_sum, h.convexRow_eq_finset_sum]
  calc
    (∑ r ∈ w.support, w.weight r * residual r omega) =
        ∑ r ∈ w.support, (w.weight r * source omega -
          w.weight r * row r T omega) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [h.residual_eq_source_sub_row r]
      ring
    _ = (∑ r ∈ w.support, w.weight r * source omega) -
          ∑ r ∈ w.support, w.weight r * row r T omega := by
      rw [Finset.sum_sub_distrib]
    _ = source omega - ∑ r ∈ w.support, w.weight r * row r T omega := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

theorem convexRow_terminal_expectation
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    (∫ omega, h.convexRow w T omega ∂mu) = ∫ omega, source omega ∂mu := by
  rw [h.convexRow_eq_finset_sum, integral_finsetSum]
  · calc
      (∑ r ∈ w.support, ∫ omega, w.weight r * row r T omega ∂mu) =
          ∑ r ∈ w.support, w.weight r * ∫ omega, row r T omega ∂mu := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [integral_const_mul]
      _ = ∑ r ∈ w.support, w.weight r * ∫ omega, source omega ∂mu := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [h.row_terminal_expectation r]
      _ = ∫ omega, source omega ∂mu := by
        rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
  · intro r hr
    exact Integrable.const_mul
      ((h.row_value_memLp_two r T).integrable (by norm_num)) (w.weight r)

theorem applyVector_norm_le_of_norm_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (w : TailConvexWeights n) (x : Nat → E) (K : Real)
    (hx : ∀ i ∈ w.support, ‖x i‖ ≤ K) : ‖w.applyVector x‖ ≤ K := by
  unfold TailConvexWeights.applyVector
  calc
    ‖∑ i ∈ w.support, w.weight i • x i‖ ≤
        ∑ i ∈ w.support, ‖w.weight i • x i‖ := norm_sum_le _ _
    _ = ∑ i ∈ w.support, w.weight i * ‖x i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i hi)]
    _ ≤ ∑ i ∈ w.support, w.weight i * K := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i hi) (w.nonneg i hi)
    _ = K := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

omit [IsProbabilityMeasure mu] in
theorem convexTerminalCoordinate_norm_le_at
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) (t : NNReal) :
    ‖w.applyVector (fun r => h.rowToLp r t)‖ ≤ rowBound := by
  apply applyVector_norm_le_of_norm_le
  intro r hr
  exact h.rowToLp_norm_le r t

omit [IsProbabilityMeasure mu] in
theorem convexRow_terminal_L2_bound
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : TailConvexWeights n) :
    (∫ omega, (h.convexRow w T omega) ^ 2 ∂mu) ≤ rowBound ^ 2 := by
  let hMem := h.convexRow_value_memLp_two w T
  let hRep := (h.convexRow_value_memLp_two w T).toLp (h.convexRow w T)
  have hNormEq : ‖hRep‖ = Real.sqrt (∫ omega,
      (h.convexRow w T omega) ^ 2 ∂mu) := by
    dsimp [hRep]
    rw [Lp.norm_toLp]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hMem)
  have hEq : hRep = h.convexTerminalCoordinateToLp (w := w) := by
    apply Lp.ext
    have hraw := hMem.coeFn_toLp
    have hvec := h.convexTerminalCoordinateToLp_coeFn_ae w
    filter_upwards [hraw, hvec] with omega hraw hvec
    exact hraw.trans hvec.symm
  have hBound : ‖hRep‖ ≤ rowBound := by
    rw [hEq]
    exact h.convexTerminalCoordinate_norm_le_at w T
  have hSqrtBound : Real.sqrt (∫ omega,
      (h.convexRow w T omega) ^ 2 ∂mu) ≤ rowBound := by
    rw [← hNormEq]
    exact hBound
  have hIntegralNonneg : 0 ≤ ∫ omega, (h.convexRow w T omega) ^ 2 ∂mu :=
    integral_nonneg (fun omega => sq_nonneg _)
  have hSquared := (sq_le_sq₀ (Real.sqrt_nonneg _) h.rowBound_nonneg).2 hSqrtBound
  rw [Real.sq_sqrt hIntegralNonneg] at hSquared
  exact hSquared

/-! ## A package carrying one shared weight sequence -/

structure CommonHilbertConvexificationData
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)) : Prop where
  weights_tail : ∀ n i, i ∈ (w n).support → n ≤ i
  weights_nonneg : ∀ n i, i ∈ (w n).support → 0 ≤ (w n).weight i
  weights_sum_eq_one : ∀ n, ∑ i ∈ (w n).support, (w n).weight i = 1
  skeleton_rightDense : ∀ t : Set.Iic T,
    t ∈ closure (Set.range (stoppedLimitSkeleton T) ∩ Set.Ici t)
  normalized_tendsto :
    Tendsto (fun n => (w n).applyVector h.normalizedCoordinateSequence)
      atTop (𝓝 y)
  coordinate_tendsto : ∀ i,
    Tendsto (fun n => (w n).applyVector (fun r => h.coordinateSequence r i))
      atTop (𝓝 (h.coordinateLimit y i))
  residual_coordinate_tendsto :
    Tendsto (fun n => h.residualConvexCoordinateToLp (w n))
      atTop (𝓝 (h.coordinateLimit y 0))
  skeleton_coordinate_tendsto : ∀ j,
    Tendsto (fun n => h.convexCoordinateToLp (w n) j)
      atTop (𝓝 (h.coordinateLimit y (j + 1)))
  residual_coordinate_coeFn_ae : ∀ n,
    ⇑(h.residualConvexCoordinateToLp (w n)) =ᵐ[mu]
      h.residualConvexRow (w n)
  skeleton_coordinate_coeFn_ae : ∀ n j,
    ⇑(h.convexCoordinateToLp (w n) j) =ᵐ[mu]
      h.convexRow (w n) (stoppedLimitSkeleton T j).1
  row_isStronglyPredictable : ∀ n,
    IsStronglyPredictable F (h.convexRow (w n))
  row_zero : ∀ n, h.convexRow (w n) 0 = 0
  row_nonnegative : ∀ n t omega, 0 ≤ h.convexRow (w n) t omega
  row_mono : ∀ n omega, Monotone (h.convexRow (w n) · omega)
  row_leftContinuous : ∀ n omega t,
    ContinuousWithinAt (h.convexRow (w n) · omega) (Iic t) t
  row_constant_after : ∀ n omega t, T ≤ t →
    h.convexRow (w n) t omega = h.convexRow (w n) T omega
  row_terminal_memLp_two : ∀ n,
    MemLp (h.convexRow (w n) T) (2 : ENNReal) mu
  row_terminal_L2_bound : ∀ n,
    (∫ omega, (h.convexRow (w n) T omega) ^ 2 ∂mu) ≤ rowBound ^ 2
  row_terminal_expectation : ∀ n,
    (∫ omega, h.convexRow (w n) T omega ∂mu) = ∫ omega, source omega ∂mu
  residual_row_memLp_two : ∀ n,
    MemLp (h.residualConvexRow (w n)) (2 : ENNReal) mu
  residual_row_eq_source_sub_compensator : ∀ n,
    h.residualConvexRow (w n) =
      fun omega => source omega - h.convexRow (w n) T omega

theorem commonHilbertConvexification_producer
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)),
      CommonHilbertConvexificationData h w y := by
  obtain ⟨w, y, hDirect, hCoord⟩ := h.exists_common_coordinate_convexification
  refine ⟨w, y, ?_⟩
  refine {
    weights_tail := fun n i hi => (w n).tail i hi
    weights_nonneg := fun n i hi => (w n).nonneg i hi
    weights_sum_eq_one := fun n => (w n).sum_eq_one
    skeleton_rightDense := stoppedLimitSkeleton_rightDense T
    normalized_tendsto := hDirect
    coordinate_tendsto := hCoord
    residual_coordinate_tendsto := ?_
    skeleton_coordinate_tendsto := ?_
    residual_coordinate_coeFn_ae := ?_
    skeleton_coordinate_coeFn_ae := ?_
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
  · simpa only [residualConvexCoordinateToLp, coordinateSequence] using hCoord 0
  · intro j
    simpa only [convexCoordinateToLp, coordinateSequence] using hCoord (j + 1)
  · intro n
    exact h.residualConvexCoordinateToLp_coeFn_ae (w n)
  · intro n j
    exact h.convexCoordinateToLp_coeFn_ae (w n) j
  · intro n
    exact h.convexRow_isStronglyPredictable (w n)
  · intro n
    exact h.convexRow_zero (w n)
  · intro n t omega
    exact h.convexRow_nonnegative (w n) t omega
  · intro n omega
    exact h.convexRow_mono (w n) omega
  · intro n omega t
    exact h.convexRow_leftContinuous (w n) omega t
  · intro n omega t ht
    exact congrFun (h.convexRow_constant_after (w n) ht) omega
  · intro n
    exact h.convexRow_value_memLp_two (w n) T
  · intro n
    exact h.convexRow_terminal_L2_bound (w n)
  · intro n
    exact h.convexRow_terminal_expectation (w n)
  · intro n
    exact h.residualConvexRow_memLp_two (w n)
  · intro n
    exact h.residualConvexRow_eq_source_sub_compensator (w n)

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
