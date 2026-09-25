/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingConvexExpectationCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingTimeRoundingCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.ResidualMartingale

/-!
# Optional sampling for square-integrable compensator rows

This is the `L²` adapter for the source-independent finite-grid
optional-sampling core.  A square-integrable row supplies the rounded source
and residual integrability, while its discrete residual martingale supplies
the stopped zero-expectation identity.  Only the finite-grid, data-level
endpoint is recorded; no convexification or predictable-process bridge is
claimed here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T : NNReal}

open SquareIntegrableIncreasingProcessData

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableStoppingConvexSourceData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    StoppingConvexSourceData F V T := {
  stronglyAdapted := hV.stronglyAdapted
  rightContinuous := hV.rightContinuous
  monotone := hV.monotone
  value_nonnegative := hV.value_nonneg }

/-! ## Integrability of the rounded residual -/

omit [SigmaFiniteFiltration mu F] in
theorem integrable_squareIntegrableFactorialGridSampledResidual_at_rightRoundedIndex
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    Integrable (fun omega => squareIntegrableFactorialGridSampledResidual
      V F mu T r (rightRoundedIndex T τ r omega) omega) mu := by
  let q : Ω → WithTop Nat := fun omega =>
    (rightRoundedIndex T τ r omega : WithTop Nat)
  have hq : IsStoppingTime ((grid T r).sampledFiltration F) q := by
    simpa only [q] using
      rightRoundedIndex_isStoppingTime (T := T) (τ := τ) hτ hτT r
  have hq_le : ∀ omega, q omega ≤ (size T r : WithTop Nat) := by
    intro omega
    change (rightRoundedIndex T τ r omega : WithTop Nat) ≤
      (size T r : WithTop Nat)
    exact WithTop.coe_le_coe.mpr
      (rightRoundedIndex_le_size (T := T) (τ := τ) r omega)
  have hstop : Integrable
      (MeasureTheory.stoppedValue
        (squareIntegrableFactorialGridSampledResidual V F mu T r) q) mu := by
    exact integrable_stoppedValue_of_memLp_two
      (R := squareIntegrableFactorialGridSampledResidual V F mu T r)
      (fun i => squareIntegrableFactorialGridSampledResidual_value_memLp_two
        (F := F) (mu := mu) hV hRows hControl r i)
      q hq (size T r) hq_le
  rw [← stoppedValue_at_nat_stoppingIndex
    (R := squareIntegrableFactorialGridSampledResidual V F mu T r)
    (q := rightRoundedIndex T τ r)]
  exact hstop

/-! ## Integrability of the rounded source -/

omit [SigmaFiniteFiltration mu F] in
theorem integrable_squareIntegrableSource_at_rightRoundedTime
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    Integrable (fun omega =>
      V (rightRoundedTime T τ r omega) omega) mu := by
  exact integrable_source_at_rightRoundedTime_core
    (squareIntegrableStoppingConvexSourceData hV) hV.terminal_memLp_two hτ hτT r

/-! ## The stopped residual has zero expectation -/

omit [SigmaFiniteFiltration mu F] in
theorem integral_squareIntegrableFactorialGridSampledResidual_at_rightRoundedIndex_eq_zero
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat)
    (hResidual : SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    (∫ omega, squareIntegrableFactorialGridSampledResidual V F mu T r
      (rightRoundedIndex T τ r omega) omega ∂mu) = 0 := by
  let q : Ω → WithTop Nat := fun omega =>
    (rightRoundedIndex T τ r omega : WithTop Nat)
  have hq : IsStoppingTime ((grid T r).sampledFiltration F) q := by
    simpa only [q] using
      rightRoundedIndex_isStoppingTime (T := T) (τ := τ) hτ hτT r
  have hq_le : ∀ omega, q omega ≤ (size T r : WithTop Nat) := by
    intro omega
    change (rightRoundedIndex T τ r omega : WithTop Nat) ≤
      (size T r : WithTop Nat)
    exact WithTop.coe_le_coe.mpr
      (rightRoundedIndex_le_size (T := T) (τ := τ) r omega)
  have hResidualTerminalIntegral :
      (∫ omega, squareIntegrableFactorialGridSampledResidual V F mu T r
        (size T r) omega ∂mu) = 0 := by
    rw [hResidual.terminal_eq]
    have hVTerminalInt : Integrable (V T) mu :=
      hV.terminal_memLp_two.integrable (by norm_num)
    have hPTerminalInt : Integrable
        (squareIntegrablePredictableCompensatorProcess V F mu T r T) mu :=
      (hRows.terminal_memLp_two r).integrable (by norm_num)
    rw [integral_sub hVTerminalInt hPTerminalInt]
    rw [hRows.terminal_expectation r]
    ring
  have hIntegralStopZero :
      (∫ omega, MeasureTheory.stoppedValue
        (squareIntegrableFactorialGridSampledResidual V F mu T r) q omega ∂mu) = 0 :=
    integral_stoppedValue_eq_zero_of_martingale
      hResidual.martingale (size T r) hResidualTerminalIntegral q hq hq_le
  calc
    (∫ omega, squareIntegrableFactorialGridSampledResidual V F mu T r
        (rightRoundedIndex T τ r omega) omega ∂mu) =
        ∫ omega, MeasureTheory.stoppedValue
          (squareIntegrableFactorialGridSampledResidual V F mu T r) q omega ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega => by
        change squareIntegrableFactorialGridSampledResidual V F mu T r
            (rightRoundedIndex T τ r omega) omega =
          MeasureTheory.stoppedValue
            (squareIntegrableFactorialGridSampledResidual V F mu T r) q omega
        rw [stoppedValue_at_nat_stoppingIndex]
        )
    _ = 0 := hIntegralStopZero

/-! ## Left-endpoint activation -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem squareIntegrablePredictableCompensatorProcess_at_tau_eq_at_rightRoundedTime
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    squareIntegrablePredictableCompensatorProcess V F mu T r
        (τ omega) omega =
      squareIntegrablePredictableCompensatorProcess V F mu T r
        (rightRoundedTime T τ r omega) omega := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r
      (τ omega) omega =
    finiteGridPredictableCompensatorProcess T
      (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r
      (rightRoundedTime T τ r omega) omega
  exact finiteGridPredictableCompensatorProcess_at_tau_eq_at_gridTime
    T τ (rightRoundedTime T τ r) (rightRoundedIndex T τ r)
    (fun k => squareIntegrableCompensatorIncrement V F mu T r k) r omega
    (fun omega => rightRoundedTime_eq_sampledTime_index
      (T := T) (τ := τ) hτT r omega)
    (fun omega => by
      rw [← rightRoundedTime_eq_sampledTime_index
        (T := T) (τ := τ) hτT r omega]
      exact (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).1)
    (fun omega => rightRoundedIndex_le_size (T := T) (τ := τ) r omega)
    (fun omega => by
      have hceil : Nat.ceil (τ omega * (r.factorial : NNReal)) ≤ size T r := by
        exact Nat.le_of_lt_succ
          (approxIndex T (τ omega) (hτT omega) r).isLt
      dsimp [rightRoundedIndex]
      rw [min_eq_left hceil])
    (fun k _hk hGridEq =>
      squareIntegrableCompensatorIncrement_eq_zero_of_grid_time_eq
        (V := V) (F := F) (mu := mu) (T := T) r k hGridEq)

/-! ## The `L²` stopped expectation identity -/

omit [SigmaFiniteFiltration mu F] in
theorem integral_squareIntegrableCompensator_at_tau_eq_integral_source_at_rightRoundedTime
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat)
    (hResidual : SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Integrable (fun omega =>
      squareIntegrablePredictableCompensatorProcess V F mu T r
        (τ omega) omega) mu ∧
    Integrable (fun omega => V (rightRoundedTime T τ r omega) omega) mu ∧
    (∫ omega, squareIntegrablePredictableCompensatorProcess V F mu T r
      (τ omega) omega ∂mu) =
      ∫ omega, V (rightRoundedTime T τ r omega) omega ∂mu := by
  have hResidualInt :=
    integrable_squareIntegrableFactorialGridSampledResidual_at_rightRoundedIndex
      (F := F) (mu := mu) hV hRows hControl hτ hτT r
  have hSourceInt := integrable_squareIntegrableSource_at_rightRoundedTime
    (F := F) (mu := mu) hV hτ hτT r
  have hResidualZero :=
    integral_squareIntegrableFactorialGridSampledResidual_at_rightRoundedIndex_eq_zero
      (F := F) (mu := mu) hV hRows hControl r hResidual hτ hτT
  have hActivation : ∀ omega,
      squareIntegrablePredictableCompensatorProcess V F mu T r
          (τ omega) omega =
        squareIntegrablePredictableCompensatorProcess V F mu T r
          (rightRoundedTime T τ r omega) omega := by
    intro omega
    exact squareIntegrablePredictableCompensatorProcess_at_tau_eq_at_rightRoundedTime
      (V := V) (F := F) (mu := mu) (T := T) hτT r omega
  have hSigmaGrid : ∀ omega,
      rightRoundedTime T τ r omega =
        (grid T r).sampledTime (rightRoundedIndex T τ r omega) := fun omega =>
    rightRoundedTime_eq_sampledTime_index (T := T) (τ := τ) hτT r omega
  have hResidualPointwise : ∀ omega,
      squareIntegrableFactorialGridSampledResidual V F mu T r
          (rightRoundedIndex T τ r omega) omega =
        V (rightRoundedTime T τ r omega) omega -
          squareIntegrablePredictableCompensatorProcess V F mu T r
            (rightRoundedTime T τ r omega) omega := by
    intro omega
    rw [squareIntegrableFactorialGridSampledResidual_apply, hSigmaGrid omega]
  have hCore := integrable_and_integral_eq_of_activation
    (mu := mu)
    (pTau := fun omega =>
      squareIntegrablePredictableCompensatorProcess V F mu T r
        (τ omega) omega)
    (pSigma := fun omega =>
      squareIntegrablePredictableCompensatorProcess V F mu T r
        (rightRoundedTime T τ r omega) omega)
    (sourceSigma := fun omega => V (rightRoundedTime T τ r omega) omega)
    (residualSigma := fun omega => squareIntegrableFactorialGridSampledResidual
      V F mu T r (rightRoundedIndex T τ r omega) omega)
    hResidualInt hSourceInt hResidualZero
    (funext hActivation) (funext hResidualPointwise)
  exact ⟨hCore.1, hSourceInt, hCore.2⟩

/-! ## Public `L²` data certificate -/

structure SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat)
    (hResidual : SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) : Prop where
  residual_integrable : Integrable (fun omega =>
    squareIntegrableFactorialGridSampledResidual V F mu T r
      (rightRoundedIndex T τ r omega) omega) mu
  source_integrable : Integrable (fun omega =>
    V (rightRoundedTime T τ r omega) omega) mu
  compensator_integrable : Integrable (fun omega =>
    squareIntegrablePredictableCompensatorProcess V F mu T r
      (τ omega) omega) mu
  integral_compensator_eq_source :
    (∫ omega, squareIntegrablePredictableCompensatorProcess V F mu T r
      (τ omega) omega ∂mu) =
      ∫ omega, V (rightRoundedTime T τ r omega) omega ∂mu

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSampling_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat)
    (hResidual : SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
      (F := F) (mu := mu) hV hRows hControl r hResidual τ hτ hτT) := by
  rcases integral_squareIntegrableCompensator_at_tau_eq_integral_source_at_rightRoundedTime
      (F := F) (mu := mu) hV hRows hControl r hResidual hτ hτT with
    ⟨hPInt, hSourceInt, hIntegral⟩
  exact ⟨{
    residual_integrable :=
      integrable_squareIntegrableFactorialGridSampledResidual_at_rightRoundedIndex
        (F := F) (mu := mu) hV hRows hControl hτ hτT r
    source_integrable := hSourceInt
    compensator_integrable := hPInt
    integral_compensator_eq_source := hIntegral }⟩

end HorizonFactorialGrid

end FTAPTheorem42
