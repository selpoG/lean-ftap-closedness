/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.RowControl
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedSkeletonLimit
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexificationCore

/-!
# One Hilbert convexification for finite-grid compensator rows

The finite-grid compensator rows are indexed by the factorial level.  This
module puts their terminal residual and all values on the canonical dense
skeleton into one `L²` direct sum.  The resulting `TailConvexWeights` are
shared by every coordinate and are also used for the raw finite convex
combination of the process rows.

Only deterministic skeleton coordinates are compactified here.  In
particular, this file does not identify a predictable raw limit with a
càdlàg version, and it does not claim process-level indistinguishability or
ucp convergence.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData
open DirectSumCoordinateControl

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

/-! ## Canonical `L²` coordinates -/

noncomputable def compensatorRowValueToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) (t : NNReal) : Lp Real (2 : ENNReal) mu :=
  (hControl.value_memLp_two r t).toLp
    (predictableCompensatorProcess V F mu T C r t)

noncomputable def terminalResidualToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) : Lp Real (2 : ENNReal) mu :=
  (hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T) -
    (hControl.value_memLp_two r T).toLp
      (predictableCompensatorProcess V F mu T C r T)

noncomputable def compensatorSkeletonCoordinateToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r j : Nat) : Lp Real (2 : ENNReal) mu :=
  compensatorRowValueToLp hV hRows hControl r (stoppedLimitSkeleton T j).1

noncomputable def commonCoordinateToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r i : Nat) : Lp Real (2 : ENNReal) mu :=
  match i with
  | 0 => terminalResidualToLp hV hRows hControl r
  | j + 1 => compensatorSkeletonCoordinateToLp hV hRows hControl r j

noncomputable def commonCoordinateBound (C K : Real) (i : Nat) : Real :=
  match i with
  | 0 => C + K
  | _ => K

noncomputable def commonCoordinateSequence
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) :
    Nat → ∀ _i : Nat, Lp Real (2 : ENNReal) mu :=
  fun r i => commonCoordinateToLp hV hRows hControl r i

noncomputable def commonCoordinateBounds : Nat → Real :=
  commonCoordinateBound (C : Real) (Real.sqrt (8 * (C : Real) ^ 2))

omit [IsProbabilityMeasure mu] in
theorem compensatorRowValueToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) (t : NNReal) :
    ⇑(compensatorRowValueToLp hV hRows hControl r t) =ᵐ[mu]
      predictableCompensatorProcess V F mu T C r t := by
  exact MemLp.coeFn_toLp (hControl.value_memLp_two r t)

theorem terminalResidualToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (r : Nat) :
    ⇑(terminalResidualToLp hV hRows hControl r) =ᵐ[mu]
      factorialGridSampledResidual V F mu T C r (size T r) := by
  have hVae := MemLp.coeFn_toLp
    (hV.value_memLp_two (mu := mu) (t := T) le_rfl)
  have hPae := MemLp.coeFn_toLp (hControl.value_memLp_two r T)
  have hSub := Lp.coeFn_sub
    ((hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T))
    ((hControl.value_memLp_two r T).toLp
      (predictableCompensatorProcess V F mu T C r T))
  have hTerminal := (hResidual r).terminal_eq
  change
    ⇑((hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T) -
      (hControl.value_memLp_two r T).toLp
        (predictableCompensatorProcess V F mu T C r T)) =ᵐ[mu]
      factorialGridSampledResidual V F mu T C r (size T r)
  filter_upwards [hSub, hVae, hPae] with omega hsub hv hp
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hv, hp]
  exact congrFun hTerminal.symm omega

omit [IsProbabilityMeasure mu] in
theorem compensatorSkeletonCoordinateToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r j : Nat) :
    ⇑(compensatorSkeletonCoordinateToLp hV hRows hControl r j) =ᵐ[mu]
      predictableCompensatorProcess V F mu T C r
        (stoppedLimitSkeleton T j).1 := by
  exact compensatorRowValueToLp_coeFn_ae hV hRows hControl r
    (stoppedLimitSkeleton T j).1

theorem commonCoordinateBound_nonnegative (i : Nat) :
    0 ≤ commonCoordinateBounds (C := C) i := by
  cases i with
  | zero =>
      dsimp [commonCoordinateBounds, commonCoordinateBound]
      exact add_nonneg (by positivity) (Real.sqrt_nonneg _)
  | succ j =>
      dsimp [commonCoordinateBounds, commonCoordinateBound]
      exact Real.sqrt_nonneg _

private theorem terminalValueToLp_norm_le
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    ‖(hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T)‖ ≤
      (C : Real) := by
  rw [Lp.norm_toLp]
  have hBound : ∀ᵐ omega ∂mu, ‖V T omega‖ ≤ (C : Real) := by
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.terminal_bound omega).1]
    exact hV.terminal_bound omega |>.2
  have hNorm := eLpNorm_le_of_ae_bound
    (p := (2 : ENNReal)) (f := V T) (C := (C : Real))
    (hV.value_memLp_two (mu := mu) (t := T) le_rfl).aestronglyMeasurable hBound
  calc
    (eLpNorm (V T) (2 : ENNReal) mu).toReal ≤
        (mu Set.univ ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal (C : Real)).toReal :=
      ENNReal.toReal_mono (by simp) hNorm
    _ = (C : Real) := by
      simp

omit [IsProbabilityMeasure mu] in
theorem compensatorRowValueToLp_norm_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) (t : NNReal) :
    ‖compensatorRowValueToLp hV hRows hControl r t‖ ≤
      Real.sqrt (8 * (C : Real) ^ 2) := by
  rw [compensatorRowValueToLp, Lp.norm_toLp]
  exact hControl.value_eLpNorm_toReal_le r t

theorem terminalResidualToLp_norm_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) :
    ‖terminalResidualToLp hV hRows hControl r‖ ≤
      commonCoordinateBounds (C := C) 0 := by
  have hVnorm := terminalValueToLp_norm_le (F := F) (mu := mu) hV
  have hPnorm := compensatorRowValueToLp_norm_le
    (F := F) (mu := mu) hV hRows hControl r T
  dsimp [terminalResidualToLp, commonCoordinateBounds,
    commonCoordinateBound]
  exact (norm_sub_le _ _).trans (add_le_add hVnorm hPnorm)

theorem commonCoordinateToLp_norm_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r i : Nat) :
    ‖commonCoordinateToLp hV hRows hControl r i‖ ≤
      commonCoordinateBounds (C := C) i := by
  cases i with
  | zero =>
      exact terminalResidualToLp_norm_le (F := F) (mu := mu) hV hRows hControl r
  | succ j =>
      exact compensatorRowValueToLp_norm_le (F := F) (mu := mu)
        hV hRows hControl r (stoppedLimitSkeleton T j).1

theorem commonCoordinateSequence_norm_bound
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) :
    ∀ r i, ‖commonCoordinateSequence hV hRows hControl r i‖ ≤
      commonCoordinateBounds (C := C) i := by
  intro r i
  exact commonCoordinateToLp_norm_le (F := F) (mu := mu) hV hRows hControl r i

/-! ## Raw convex rows -/

noncomputable def compensatorConvexRow
    (w : TailConvexWeights n) : Process Ω :=
  fun t omega => w.apply (fun r =>
    predictableCompensatorProcess V F mu T C r t) omega

noncomputable def residualConvexRow
    (w : TailConvexWeights n) : Ω → Real :=
  w.apply (fun r => fun omega =>
    V T omega - predictableCompensatorProcess V F mu T C r T omega)

noncomputable def compensatorConvexCoordinateToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (j : Nat) : Lp Real (2 : ENNReal) mu :=
  w.applyVector (fun r => compensatorSkeletonCoordinateToLp
    hV hRows hControl r j)

noncomputable def residualConvexCoordinateToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) : Lp Real (2 : ENNReal) mu :=
  w.applyVector (fun r => terminalResidualToLp hV hRows hControl r)

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_value_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
  (w : TailConvexWeights n) (t : NNReal) :
    MemLp
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w t)
      (2 : ENNReal) mu := by
  change MemLp (fun omega => ∑ r ∈ w.support,
    w.weight r * predictableCompensatorProcess V F mu T C r t omega)
    (2 : ENNReal) mu
  apply memLp_finsetSum
  intro r hr
  exact (hControl.value_memLp_two r t).const_smul (w.weight r)

noncomputable def compensatorConvexRowValueToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (t : NNReal) : Lp Real (2 : ENNReal) mu :=
  (compensatorConvexRow_value_memLp_two hV hRows hControl w t).toLp
    (compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) w t)

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRowValueToLp_eq_applyVector
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (t : NNReal) :
    compensatorConvexRowValueToLp hV hRows hControl w t =
      w.applyVector (fun r => compensatorRowValueToLp
        hV hRows hControl r t) := by
  apply Lp.ext
  have hraw := (compensatorConvexRow_value_memLp_two
    (F := F) (mu := mu) hV hRows hControl w t).coeFn_toLp
  have hvec := (w.applyVector_coeFn_ae
    (fun r => compensatorRowValueToLp hV hRows hControl r t)
    (fun r => predictableCompensatorProcess V F mu T C r t)
    (fun r => compensatorRowValueToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl r t))
  filter_upwards [hraw, hvec] with omega hraw hvec
  exact hraw.trans hvec.symm

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexCoordinateToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (j : Nat) :
    ⇑(compensatorConvexCoordinateToLp hV hRows hControl w j) =ᵐ[mu]
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w (stoppedLimitSkeleton T j).1 := by
  have hvec := (w.applyVector_coeFn_ae
    (fun r => compensatorSkeletonCoordinateToLp hV hRows hControl r j)
    (fun r => predictableCompensatorProcess V F mu T C r
      (stoppedLimitSkeleton T j).1)
    (fun r => compensatorSkeletonCoordinateToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl r j))
  change ⇑(w.applyVector (fun r =>
    compensatorSkeletonCoordinateToLp hV hRows hControl r j)) =ᵐ[mu]
      w.apply (fun r => predictableCompensatorProcess V F mu T C r
        (stoppedLimitSkeleton T j).1)
  exact hvec

theorem residualConvexCoordinateToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : TailConvexWeights n) :
    ⇑(residualConvexCoordinateToLp hV hRows hControl w) =ᵐ[mu]
      residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w := by
  have hvec := (w.applyVector_coeFn_ae
    (fun r => terminalResidualToLp hV hRows hControl r)
    (fun r => fun omega =>
      V T omega - predictableCompensatorProcess V F mu T C r T omega)
    (fun r => terminalResidualToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl hResidual r |>.trans
        (Eventually.of_forall (fun omega =>
          congrFun (hResidual r).terminal_eq omega))))
  simpa only [residualConvexCoordinateToLp, residualConvexRow] using hvec

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRowValueToLp_norm_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (t : NNReal) :
    ‖compensatorConvexRowValueToLp hV hRows hControl w t‖ ≤
      Real.sqrt (8 * (C : Real) ^ 2) := by
  rw [compensatorConvexRowValueToLp_eq_applyVector
    (F := F) (mu := mu) hV hRows hControl w t]
  apply CommonHilbertRowsData.applyVector_norm_le_of_norm_le
  intro i hi
  exact compensatorRowValueToLp_norm_le
    (F := F) (mu := mu) hV hRows hControl i t

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_terminal_L2_bound
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2 := by
  let hMem := compensatorConvexRow_value_memLp_two
    (F := F) (mu := mu) hV hRows hControl w T
  let hRep := compensatorConvexRowValueToLp hV hRows hControl w T
  have hNormEq : ‖hRep‖ = Real.sqrt (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T omega) ^ 2 ∂mu) := by
    dsimp [hRep, compensatorConvexRowValueToLp]
    rw [Lp.norm_toLp]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hMem)
  have hBound : ‖hRep‖ ≤ Real.sqrt (8 * (C : Real) ^ 2) := by
    exact compensatorConvexRowValueToLp_norm_le
      (F := F) (mu := mu) hV hRows hControl w T
  have hSqrtBound : Real.sqrt (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T omega) ^ 2 ∂mu) ≤
      Real.sqrt (8 * (C : Real) ^ 2) := by
    rw [← hNormEq]
    exact hBound
  have hIntegralNonneg : 0 ≤ ∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T omega) ^ 2 ∂mu := by
    exact integral_nonneg (fun omega => sq_nonneg _)
  have hSquared := (sq_le_sq₀
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hSqrtBound
  rw [Real.sq_sqrt hIntegralNonneg,
    Real.sq_sqrt (by positivity : 0 ≤ 8 * (C : Real) ^ 2)] at hSquared
  exact hSquared

/-! ## The one common direct-sum sequence -/

noncomputable def commonNormalizedCoordinateSequence
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) :
    Nat → lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal) :=
  coordinateToLp geometricLpEnvelope
    (normalizeCoordinates commonCoordinateBounds
      (commonCoordinateSequence hV hRows hControl))
    (fun r i => by
      exact
        normalizeCoordinates_norm_le commonCoordinateBounds
          (commonCoordinateSequence hV hRows hControl)
          (fun j => commonCoordinateBound_nonnegative (C := C) j)
          (commonCoordinateSequence_norm_bound hV hRows hControl) r i)

noncomputable def commonCoordinateLimit
    (C : NNReal)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)) (i : Nat) : Lp Real (2 : ENNReal) mu :=
  (geometricNormalization (commonCoordinateBounds (C := C)) i)⁻¹ • y i

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_eq_finset_sum
    (w : TailConvexWeights n) :
    compensatorConvexRow (V := V) (F := F) (mu := mu) (T := T) (C := C) w =
      fun t omega => ∑ r ∈ w.support,
        w.weight r * predictableCompensatorProcess V F mu T C r t omega := by
  rfl

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_isStronglyPredictable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    IsStronglyPredictable F
      (compensatorConvexRow (V := V) (F := F) (mu := mu) (T := T) (C := C) w) := by
  rw [compensatorConvexRow_eq_finset_sum]
  apply CommonHilbertRowsData.stronglyPredictable_finset_sum
  intro r hr
  exact hRows.process_predictable r

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_zero
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    compensatorConvexRow (V := V) (F := F) (mu := mu) (T := T) (C := C) w 0 = 0 := by
  funext omega
  rw [compensatorConvexRow_eq_finset_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [hRows.process_zero r]
  simp

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_mono
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (omega : Ω) :
    Monotone
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w · omega) := by
  intro s t hst
  rw [compensatorConvexRow_eq_finset_sum]
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left
    (hRows.process_mono r omega hst) ((w).nonneg r hr)

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_constant_after
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) {t : NNReal} (ht : T ≤ t) :
    compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w t =
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T := by
  funext omega
  change (∑ r ∈ w.support,
      w.weight r * predictableCompensatorProcess V F mu T C r t omega) =
    ∑ r ∈ w.support,
      w.weight r * predictableCompensatorProcess V F mu T C r T omega
  apply Finset.sum_congr rfl
  intro r hr
  rw [hRows.process_constant_after r omega t ht]

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_leftContinuous
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (omega : Ω) (t : NNReal) :
    ContinuousWithinAt
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w · omega)
      (Iic t) t := by
  rw [compensatorConvexRow_eq_finset_sum]
  change ContinuousWithinAt
    (fun u => ∑ r ∈ w.support,
      w.weight r * predictableCompensatorProcess V F mu T C r u omega)
    (Iic t) t
  induction w.support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Iic t) t)
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      exact ((hControl.leftContinuous r omega t).const_mul (w.weight r)).add ih

omit [IsProbabilityMeasure mu] in
theorem compensatorConvexRow_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) (t : NNReal) (omega : Ω) :
    0 ≤ compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) w t omega := by
  change 0 ≤ ∑ r ∈ w.support,
    w.weight r * predictableCompensatorProcess V F mu T C r t omega
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (w.nonneg r hr) (hRows.process_nonneg r t omega)

theorem residualConvexRow_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    MemLp
      (residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w) (2 : ENNReal) mu := by
  change MemLp (fun omega => ∑ r ∈ w.support,
    w.weight r * (V T omega -
      predictableCompensatorProcess V F mu T C r T omega))
    (2 : ENNReal) mu
  apply memLp_finsetSum
  intro r hr
  exact ((hV.value_memLp_two (mu := mu) (t := T) le_rfl).sub
    (hControl.value_memLp_two r T)).const_smul (w.weight r)

omit [IsProbabilityMeasure mu] in
theorem residualConvexRow_eq_source_sub_compensator
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (_hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w =
      fun omega => V T omega -
        compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) w T omega := by
  funext omega
  change (∑ r ∈ w.support, w.weight r *
      (V T omega - predictableCompensatorProcess V F mu T C r T omega)) =
    V T omega - ∑ r ∈ w.support, w.weight r *
      predictableCompensatorProcess V F mu T C r T omega
  calc
    (∑ r ∈ w.support, w.weight r *
        (V T omega - predictableCompensatorProcess V F mu T C r T omega)) =
        ∑ r ∈ w.support, (w.weight r * V T omega -
          w.weight r * predictableCompensatorProcess V F mu T C r T omega) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (∑ r ∈ w.support, w.weight r * V T omega) -
          ∑ r ∈ w.support, w.weight r *
            predictableCompensatorProcess V F mu T C r T omega := by
      rw [Finset.sum_sub_distrib]
    _ = V T omega - ∑ r ∈ w.support, w.weight r *
          predictableCompensatorProcess V F mu T C r T omega := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

theorem compensatorConvexRow_terminal_expectation
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    (∫ omega,
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w T omega ∂mu) =
      ∫ omega, V T omega ∂mu := by
  rw [compensatorConvexRow_eq_finset_sum]
  rw [integral_finsetSum]
  · calc
      (∑ r ∈ w.support,
          ∫ omega, w.weight r *
            predictableCompensatorProcess V F mu T C r T omega ∂mu) =
          ∑ r ∈ w.support, w.weight r *
            ∫ omega, predictableCompensatorProcess V F mu T C r T omega ∂mu := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [integral_const_mul]
      _ = ∑ r ∈ w.support, w.weight r *
            ∫ omega, V T omega ∂mu := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hRows.terminal_expectation r]
      _ = ∫ omega, V T omega ∂mu := by
        rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
  · intro r hr
    exact Integrable.const_mul
      ((hControl.value_memLp_two r T).integrable (by norm_num)) (w.weight r)

/-! The bounded route is an adapter for the source-independent row core.  Its
residual coordinate is the terminal source minus the terminal row; the
separate sampled-residual certificate is only needed by the public martingale
field below. -/

noncomputable def boundedCommonHilbertRowsData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) :
    CommonHilbertRowsData F mu T (V T)
      (fun r => predictableCompensatorProcess V F mu T C r)
      (fun r omega => V T omega - predictableCompensatorProcess V F mu T C r T omega)
      (C : Real) (Real.sqrt (8 * (C : Real) ^ 2)) := {
  sourceToLp := (hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T)
  rowToLp := fun r t => compensatorRowValueToLp hV hRows hControl r t
  residualToLp := fun r => terminalResidualToLp hV hRows hControl r
  sourceToLp_coeFn_ae := MemLp.coeFn_toLp
    (hV.value_memLp_two (mu := mu) (t := T) le_rfl)
  rowToLp_coeFn_ae := fun r t => compensatorRowValueToLp_coeFn_ae
    (F := F) (mu := mu) hV hRows hControl r t
  residualToLp_coeFn_ae := fun r => by
    have hVae := MemLp.coeFn_toLp
      (hV.value_memLp_two (mu := mu) (t := T) le_rfl)
    have hPmem := hControl.value_memLp_two r T
    have hPae := MemLp.coeFn_toLp hPmem
    have hSub := Lp.coeFn_sub
      ((hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T))
      (hPmem.toLp (predictableCompensatorProcess V F mu T C r T))
    change ⇑((hV.value_memLp_two (mu := mu) (t := T) le_rfl).toLp (V T) -
      hPmem.toLp (predictableCompensatorProcess V F mu T C r T)) =ᵐ[mu]
      fun omega => V T omega - predictableCompensatorProcess V F mu T C r T omega
    filter_upwards [hSub, hVae, hPae] with omega hsub hv hp
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hv, hp]
  sourceBound_nonneg := by positivity
  rowBound_nonneg := Real.sqrt_nonneg _
  sourceToLp_norm_le := terminalValueToLp_norm_le (F := F) (mu := mu) hV
  rowToLp_norm_le := fun r t => compensatorRowValueToLp_norm_le
    (F := F) (mu := mu) hV hRows hControl r t
  residualToLp_norm_le := fun r => terminalResidualToLp_norm_le
    (F := F) (mu := mu) hV hRows hControl r
  row_value_memLp_two := fun r t => hControl.value_memLp_two r t
  residual_memLp_two := fun r => (hV.value_memLp_two
    (mu := mu) (t := T) le_rfl).sub (hControl.value_memLp_two r T)
  row_isStronglyPredictable := fun r => hRows.process_predictable r
  row_zero := fun r => hRows.process_zero r
  row_nonnegative := fun r t omega => hRows.process_nonneg r t omega
  row_mono := fun r omega => hRows.process_mono r omega
  row_leftContinuous := fun r omega t => hControl.leftContinuous r omega t
  row_constant_after := fun r omega t ht => hRows.process_constant_after r omega t ht
  row_terminal_L2_bound := fun r => by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 8 * (C : Real) ^ 2)]
    exact hRows.terminal_L2_bound r
  row_terminal_expectation := fun r => hRows.terminal_expectation r
  residual_eq_source_sub_row := fun r => rfl }

/-! ## Public 7C certificate -/

structure FactorialGridPredictableCompensatorCommonHilbertConvexificationData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)) : Prop where
  residual_martingale : ∀ r,
    FactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows r
  weights_tail : ∀ n i, i ∈ (w n).support → n ≤ i
  weights_nonneg : ∀ n i, i ∈ (w n).support → 0 ≤ (w n).weight i
  weights_sum_eq_one : ∀ n, ∑ i ∈ (w n).support, (w n).weight i = 1
  skeleton_rightDense :
    ∀ t : Set.Iic T,
      t ∈ closure (Set.range (stoppedLimitSkeleton T) ∩ Set.Ici t)
  normalized_tendsto :
    Tendsto
      (fun n => (w n).applyVector
        (commonNormalizedCoordinateSequence hV hRows hControl))
      atTop (𝓝 y)
  coordinate_tendsto : ∀ i : Nat,
    Tendsto
      (fun n => (w n).applyVector
        (fun r => commonCoordinateSequence hV hRows hControl r i))
      atTop (𝓝 (commonCoordinateLimit C y i))
  residual_coordinate_tendsto :
    Tendsto
      (fun n => residualConvexCoordinateToLp hV hRows hControl (w n))
      atTop (𝓝 (commonCoordinateLimit C y 0))
  skeleton_coordinate_tendsto : ∀ j : Nat,
    Tendsto
      (fun n => compensatorConvexCoordinateToLp
        hV hRows hControl (w n) j)
      atTop (𝓝 (commonCoordinateLimit C y (j + 1)))
  residual_coordinate_coeFn_ae : ∀ n,
    ⇑(residualConvexCoordinateToLp hV hRows hControl (w n)) =ᵐ[mu]
      residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n)
  skeleton_coordinate_coeFn_ae : ∀ n j,
    ⇑(compensatorConvexCoordinateToLp
      hV hRows hControl (w n) j) =ᵐ[mu]
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n)
        (stoppedLimitSkeleton T j).1
  row_isStronglyPredictable : ∀ n,
    IsStronglyPredictable F
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n))
  row_zero : ∀ n,
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w n) 0 = 0
  row_nonnegative : ∀ n t omega,
    0 ≤ compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w n) t omega
  row_mono : ∀ n omega,
    Monotone
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) · omega)
  row_leftContinuous : ∀ n omega t,
    ContinuousWithinAt
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) · omega)
      (Iic t) t
  row_constant_after : ∀ n omega t, T ≤ t →
    compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) t omega =
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) T omega
  row_terminal_memLp_two : ∀ n,
    MemLp
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) T)
      (2 : ENNReal) mu
  row_terminal_L2_bound : ∀ n,
    (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2
  row_terminal_expectation : ∀ n,
    (∫ omega,
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) T omega ∂mu) =
      ∫ omega, V T omega ∂mu
  residual_row_memLp_two : ∀ n,
    MemLp
      (residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n)) (2 : ENNReal) mu
  residual_row_eq_source_sub_compensator : ∀ n,
    residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w n) =
      fun omega => V T omega -
        compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w n) T omega

theorem factorialGridPredictableCompensatorCommonHilbertConvexification_producer
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)),
      FactorialGridPredictableCompensatorCommonHilbertConvexificationData
        hV hRows hControl hResidual w y := by
  let hCommon := boundedCommonHilbertRowsData (F := F) (mu := mu) hV hRows hControl
  obtain ⟨w, y, hCore⟩ :=
    CommonHilbertRowsData.commonHilbertConvexification_producer
      (h := hCommon)
  have hBoundEq : hCommon.coordinateBound = commonCoordinateBounds (C := C) := by
    funext i
    cases i <;> rfl
  refine ⟨w, y, ?_⟩
  refine {
    residual_martingale := hResidual
    weights_tail := fun n i hi => (w n).tail i hi
    weights_nonneg := fun n i hi => (w n).nonneg i hi
    weights_sum_eq_one := fun n => (w n).sum_eq_one
    skeleton_rightDense := stoppedLimitSkeleton_rightDense T
    normalized_tendsto := hCore.normalized_tendsto
    coordinate_tendsto := hCore.coordinate_tendsto
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
  · have h := hCore.residual_coordinate_tendsto
    change Tendsto (fun n => (w n).applyVector
        (fun r => terminalResidualToLp hV hRows hControl r)) atTop
      (𝓝 ((geometricNormalization hCommon.coordinateBound 0)⁻¹ • y 0)) at h
    have hNormEq := congrArg geometricNormalization hBoundEq
    have hLimit :
        (geometricNormalization hCommon.coordinateBound 0)⁻¹ • y 0 =
          (geometricNormalization (commonCoordinateBounds (C := C)) 0)⁻¹ • y 0 := by
      rw [congrFun hNormEq 0]
    rw [hLimit] at h
    simpa only [residualConvexCoordinateToLp, commonCoordinateLimit] using h
  · intro j
    have h := hCore.skeleton_coordinate_tendsto j
    change Tendsto (fun n => (w n).applyVector
        (fun r => compensatorSkeletonCoordinateToLp hV hRows hControl r j)) atTop
      (𝓝 ((geometricNormalization hCommon.coordinateBound (j + 1))⁻¹ • y (j + 1))) at h
    have hNormEq := congrArg geometricNormalization hBoundEq
    have hLimit :
        (geometricNormalization hCommon.coordinateBound (j + 1))⁻¹ • y (j + 1) =
          (geometricNormalization (commonCoordinateBounds (C := C)) (j + 1))⁻¹ • y (j + 1) := by
      rw [congrFun hNormEq (j + 1)]
    rw [hLimit] at h
    simpa only [compensatorConvexCoordinateToLp, commonCoordinateLimit] using h
  · intro n
    exact residualConvexCoordinateToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl hResidual (w n)
  · intro n j
    exact compensatorConvexCoordinateToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl (w n) j
  · intro n
    exact compensatorConvexRow_isStronglyPredictable
      (F := F) (mu := mu) hV hRows hControl (w n)
  · intro n
    exact compensatorConvexRow_zero
      (F := F) (mu := mu) hV hRows hControl (w n)
  · intro n t omega
    exact compensatorConvexRow_nonneg
      (F := F) (mu := mu) hV hRows hControl (w n) t omega
  · intro n omega
    exact compensatorConvexRow_mono
      (F := F) (mu := mu) hV hRows hControl (w n) omega
  · intro n omega t
    exact compensatorConvexRow_leftContinuous
      (F := F) (mu := mu) hV hRows hControl (w n) omega t
  · intro n omega t ht
    exact congrFun (compensatorConvexRow_constant_after
      (F := F) (mu := mu) hV hRows hControl (w n) ht) omega
  · intro n
    exact compensatorConvexRow_value_memLp_two
      (F := F) (mu := mu) hV hRows hControl (w n) T
  · intro n
    exact compensatorConvexRow_terminal_L2_bound
      (F := F) (mu := mu) hV hRows hControl (w n)
  · intro n
    exact compensatorConvexRow_terminal_expectation
      (F := F) (mu := mu) hV hRows hControl (w n)
  · intro n
    exact residualConvexRow_memLp_two
      (F := F) (mu := mu) hV hRows hControl (w n)
  · intro n
    exact residualConvexRow_eq_source_sub_compensator
      (F := F) (mu := mu) hV hRows hControl (w n)

/-! The regularized common-stop Jordan components are concrete consumers of
the complete 7C package.  The positive and negative components deliberately
receive separate row, residual, control, and Hilbert-convexification data;
this endpoint does not claim that their two weight sequences coincide.
-/

theorem exists_commonHilbertConvexifications_of_commonStopJordanComponents
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Ω → WithTop NNReal}
    {alpha : Ω → WithTop NNReal} {R : Ω → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ hPlus : BoundedIncreasingProcessData (F := F) Aplus T
        (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
      ∃ hRowsPlus : FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hPlus,
        ∃ hControlPlus : FactorialGridPredictableCompensatorRowControlData
            (F := F) (mu := mu) hPlus hRowsPlus,
          ∃ hResidualPlus : ∀ r,
              FactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hPlus hRowsPlus r,
            ∃ (wPlus : ∀ n, TailConvexWeights n)
              (yPlus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              FactorialGridPredictableCompensatorCommonHilbertConvexificationData
                  hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus ∧
    ∃ hMinus : BoundedIncreasingProcessData (F := F) Aminus T
        (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
      ∃ hRowsMinus : FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hMinus,
        ∃ hControlMinus : FactorialGridPredictableCompensatorRowControlData
            (F := F) (mu := mu) hMinus hRowsMinus,
          ∃ hResidualMinus : ∀ r,
              FactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hMinus hRowsMinus r,
            ∃ (wMinus : ∀ n, TailConvexWeights n)
              (yMinus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              FactorialGridPredictableCompensatorCommonHilbertConvexificationData
                hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus := by
  obtain ⟨hPlus, hMinus, hRowsPlus, hRowsMinus⟩ :=
    exists_factorialGridPredictableCompensatorRows_of_commonStopJordanComponents
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus
        cumulativeVariation hReg
  rcases hRowsPlus with ⟨hRowsPlus⟩
  rcases hRowsMinus with ⟨hRowsMinus⟩
  obtain ⟨hControlPlus⟩ :=
    factorialGridPredictableCompensatorRowControl_producer
      (F := F) (mu := mu) hPlus hRowsPlus
  obtain ⟨hControlMinus⟩ :=
    factorialGridPredictableCompensatorRowControl_producer
      (F := F) (mu := mu) hMinus hRowsMinus
  let hResidualPlus : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hPlus hRowsPlus r := fun r =>
    Classical.choice (factorialGridSampledResidualMartingale_producer
      (F := F) (mu := mu) hPlus hRowsPlus r)
  let hResidualMinus : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hMinus hRowsMinus r := fun r =>
    Classical.choice (factorialGridSampledResidualMartingale_producer
      (F := F) (mu := mu) hMinus hRowsMinus r)
  obtain ⟨wPlus, yPlus, hPlusData⟩ :=
    factorialGridPredictableCompensatorCommonHilbertConvexification_producer
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus
  obtain ⟨wMinus, yMinus, hMinusData⟩ :=
    factorialGridPredictableCompensatorCommonHilbertConvexification_producer
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus
  refine ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hPlusData, hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus,
    yMinus, hMinusData⟩

theorem boundedCommonHilbertConvexificationCoreData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y) :
    CommonHilbertRowsData.CommonHilbertConvexificationData
      (boundedCommonHilbertRowsData hV hRows hControl) w y := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu) hV hRows hControl
  have hNormSeqEq : h.normalizedCoordinateSequence =
      commonNormalizedCoordinateSequence hV hRows hControl := by
    rfl
  have hCoordinateEq : h.coordinateSequence =
      commonCoordinateSequence hV hRows hControl := by
    rfl
  have hBoundEq : h.coordinateBound = commonCoordinateBounds (C := C) := by
    rfl
  have hLimitEq (i : Nat) : h.coordinateLimit y i =
      commonCoordinateLimit C y i := by
    rfl
  have hConvexRowEq : ∀ {n : Nat} (ww : TailConvexWeights n),
      h.convexRow ww = compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) ww := by
    intro n ww
    rfl
  have hResidualConvexRowEq : ∀ {n : Nat} (ww : TailConvexWeights n),
      h.residualConvexRow ww = residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) ww := by
    intro n ww
    rfl
  have hConvexCoordinateEq : ∀ {n : Nat} (ww : TailConvexWeights n) (j : Nat),
      h.convexCoordinateToLp ww j = compensatorConvexCoordinateToLp
        hV hRows hControl ww j := by
    intro n ww j
    rfl
  have hResidualCoordinateEq : ∀ {n : Nat} (ww : TailConvexWeights n),
      h.residualConvexCoordinateToLp ww = residualConvexCoordinateToLp
        hV hRows hControl ww := by
    intro n ww
    rfl
  refine {
    weights_tail := hCommon.weights_tail
    weights_nonneg := hCommon.weights_nonneg
    weights_sum_eq_one := hCommon.weights_sum_eq_one
    skeleton_rightDense := hCommon.skeleton_rightDense
    normalized_tendsto := ?_
    coordinate_tendsto := ?_
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
  · change Tendsto (fun n => (w n).applyVector h.normalizedCoordinateSequence)
      atTop (𝓝 y)
    rw [hNormSeqEq]
    exact hCommon.normalized_tendsto
  · intro i
    change Tendsto (fun n => (w n).applyVector (fun r =>
      h.coordinateSequence r i)) atTop (𝓝 (h.coordinateLimit y i))
    rw [hCoordinateEq, hLimitEq]
    exact hCommon.coordinate_tendsto i
  · change Tendsto (fun n => (w n).applyVector
      (fun r => h.residualToLp r)) atTop (𝓝 (h.coordinateLimit y 0))
    rw [hLimitEq]
    exact hCommon.residual_coordinate_tendsto
  · intro j
    change Tendsto (fun n => (w n).applyVector (fun r =>
      h.rowToLp r (stoppedLimitSkeleton T j).1)) atTop
        (𝓝 (h.coordinateLimit y (j + 1)))
    rw [hLimitEq]
    exact hCommon.skeleton_coordinate_tendsto j
  · intro n
    rw [hResidualCoordinateEq, hResidualConvexRowEq]
    exact hCommon.residual_coordinate_coeFn_ae n
  · intro n j
    rw [hConvexCoordinateEq, hConvexRowEq]
    exact hCommon.skeleton_coordinate_coeFn_ae n j
  · intro n
    rw [hConvexRowEq]
    exact hCommon.row_isStronglyPredictable n
  · intro n
    rw [hConvexRowEq]
    exact hCommon.row_zero n
  · intro n t omega
    rw [hConvexRowEq]
    exact hCommon.row_nonnegative n t omega
  · intro n omega
    rw [hConvexRowEq]
    exact hCommon.row_mono n omega
  · intro n omega t
    rw [hConvexRowEq]
    exact hCommon.row_leftContinuous n omega t
  · intro n omega t ht
    rw [hConvexRowEq]
    exact hCommon.row_constant_after n omega t ht
  · intro n
    rw [hConvexRowEq]
    exact hCommon.row_terminal_memLp_two n
  · intro n
    rw [hConvexRowEq]
    rw [Real.sq_sqrt (by positivity)]
    exact hCommon.row_terminal_L2_bound n
  · intro n
    rw [hConvexRowEq]
    exact hCommon.row_terminal_expectation n
  · intro n
    rw [hResidualConvexRowEq]
    exact hCommon.residual_row_memLp_two n
  · intro n
    rw [hResidualConvexRowEq, hConvexRowEq]
    exact hCommon.residual_row_eq_source_sub_compensator n

end HorizonFactorialGrid

end FTAPTheorem42
