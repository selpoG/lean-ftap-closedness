/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.RowControlCore
import FTAPTheorem42.Stochastic.Decomposition.Source.SquareIntegrableIncreasingCompensatorRows

/-!
# `L²` row control without a deterministic source bound

The terminal estimate in the square-integrable increasing-process rows is
uniform in the factorial level.  Monotonicity then gives the same estimate
for every process value, with the deterministic constant
`K = sqrt (8 * integral (V T)^2)`.  This is the control needed to put row
values into a common Hilbert direct sum.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

namespace SquareIntegrableIncreasingProcessData

/-! ## Pointwise process control -/

structure SquareIntegrableIncreasingProcessCompensatorRowControlData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) where
  value_memLp_two : ∀ r t,
    MemLp (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu
  value_eLpNorm_le_terminal : ∀ r t,
    eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu ≤
      eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r T)
        (2 : ENNReal) mu
  value_sq_integral_le : ∀ r t,
    (∫ omega,
      (squareIntegrablePredictableCompensatorProcess V F mu T r t omega) ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu
  value_eLpNorm_toReal_le : ∀ r t,
    (eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu).toReal ≤
      Real.sqrt (8 * ∫ omega, (V T omega) ^ 2 ∂mu)
  leftContinuous : ∀ r omega t,
    ContinuousWithinAt
      (squareIntegrablePredictableCompensatorProcess V F mu T r · omega)
      (Iic t) t

theorem predictable_compensator_process_value_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    MemLp (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu := by
  apply process_value_memLp_two_of_terminal
    (P := squareIntegrablePredictableCompensatorProcess V F mu T r)
  · exact hRows.process_predictable r
  · exact hRows.process_nonneg r
  · exact hRows.process_mono r
  · exact hRows.process_constant_after r
  · exact hRows.terminal_memLp_two r

theorem predictable_compensator_process_value_eLpNorm_le_terminal
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) _hV)
    (r : Nat) (t : NNReal) :
    eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu ≤
      eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r T)
        (2 : ENNReal) mu := by
  exact process_value_eLpNorm_le_terminal (hRows.process_predictable r)
    (hRows.process_nonneg r) (hRows.process_mono r)
    (hRows.process_constant_after r) t

theorem predictable_compensator_process_value_sq_integral_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    (∫ omega,
      (squareIntegrablePredictableCompensatorProcess V F mu T r t omega) ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
  exact process_value_sq_integral_le_terminal
    (hRows.process_predictable r) (hRows.process_nonneg r)
    (hRows.process_mono r) (hRows.process_constant_after r)
    (hRows.terminal_memLp_two r)
    (hRows.terminal_L2_bound r) t

theorem predictable_compensator_process_value_eLpNorm_toReal_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat) (t : NNReal) :
    (eLpNorm (squareIntegrablePredictableCompensatorProcess V F mu T r t)
      (2 : ENNReal) mu).toReal ≤
      Real.sqrt (8 * ∫ omega, (V T omega) ^ 2 ∂mu) := by
  exact process_value_eLpNorm_toReal_le
    (hRows.process_predictable r) (hRows.process_nonneg r)
    (hRows.process_mono r) (hRows.process_constant_after r)
    (hRows.terminal_memLp_two r) (hRows.terminal_L2_bound r) t

/-! ## Producer and the regularized Jordan consumer -/

theorem squareIntegrableIncreasingProcessCompensatorRowControl_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) :
    Nonempty (SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) := by
  exact ⟨{
    value_memLp_two := fun r t =>
      predictable_compensator_process_value_memLp_two
        (F := F) (mu := mu) hV hRows r t
    value_eLpNorm_le_terminal := fun r t =>
      predictable_compensator_process_value_eLpNorm_le_terminal
        (F := F) (mu := mu) hV hRows r t
    value_sq_integral_le := fun r t =>
      predictable_compensator_process_value_sq_integral_le
        (F := F) (mu := mu) hV hRows r t
    value_eLpNorm_toReal_le := fun r t =>
      predictable_compensator_process_value_eLpNorm_toReal_le
        (F := F) (mu := mu) hV hRows r t
    leftContinuous := fun r omega t => by
      exact finiteGridPredictableCompensatorProcess_continuousWithinAt_Iic
        T (fun k => squareIntegrableCompensatorIncrement V F mu T r k)
        r omega t }⟩

theorem exists_squareIntegrableIncreasingProcessCompensatorRowControl
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) :
    Nonempty (SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) :=
  squareIntegrableIncreasingProcessCompensatorRowControl_producer
    (F := F) (mu := mu) hV hRows

theorem exists_squareIntegrableIncreasingProcessCompensatorRowControls_of_commonStopJordanComponents
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
        ∃ hRowsPlus : SquareIntegrableIncreasingProcessCompensatorRowsData
            (F := F) (mu := mu) hPlus,
          ∃ hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
              (F := F) (mu := mu) hMinus,
            Nonempty (SquareIntegrableIncreasingProcessCompensatorRowControlData
              (F := F) (mu := mu) hPlus hRowsPlus) ∧
            Nonempty (SquareIntegrableIncreasingProcessCompensatorRowControlData
              (F := F) (mu := mu) hMinus hRowsMinus) := by
  obtain ⟨hPlus, hMinus, hRowsPlus, hRowsMinus⟩ :=
    exists_factorialGridSquareIntegrableIncreasingCompensatorRows_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  rcases hRowsPlus with ⟨hRowsPlus⟩
  rcases hRowsMinus with ⟨hRowsMinus⟩
  refine ⟨hPlus, hMinus, hRowsPlus, hRowsMinus, ?_⟩
  exact ⟨squareIntegrableIncreasingProcessCompensatorRowControl_producer
      (F := F) (mu := mu) hPlus hRowsPlus,
    squareIntegrableIncreasingProcessCompensatorRowControl_producer
      (F := F) (mu := mu) hMinus hRowsMinus⟩

end SquareIntegrableIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
