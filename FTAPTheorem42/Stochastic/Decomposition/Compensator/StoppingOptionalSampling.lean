/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingTimeRoundingCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingOptionalSamplingCore
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Stopping

/-!
# Finite-grid residual optional sampling

For a bounded stopping time, the right-rounded factorial-grid index is a
bounded discrete stopping time.  Optional sampling for the finite-grid
residual martingale identifies its expectation with the terminal residual.
The left-endpoint activation identity then gives the expectation of the row at
the original stopping time as the expectation of the source at the rounded
time.  No convex combination or process-level identification is used here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T C : NNReal}

/-! ## Pointwise stopped-value bridge -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem factorialGridSampledResidual_at_rightRoundedIndex
    (r : Nat) :
    MeasureTheory.stoppedValue
        (factorialGridSampledResidual V F mu T C r)
        (fun omega =>
          (rightRoundedIndex T τ r omega : WithTop Nat)) =
      (fun omega => factorialGridSampledResidual V F mu T C r
        (rightRoundedIndex T τ r omega) omega) := by
  exact stoppedValue_at_nat_stoppingIndex
    (R := factorialGridSampledResidual V F mu T C r)
    (q := rightRoundedIndex T τ r)

/-! ## Integrability of the rounded source and residual -/

omit [SigmaFiniteFiltration mu F] in
theorem integrable_factorialGridSampledResidual_at_rightRoundedIndex
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    Integrable (fun omega => factorialGridSampledResidual V F mu T C r
      (rightRoundedIndex T τ r omega) omega) mu := by
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
        (factorialGridSampledResidual V F mu T C r) q) mu := by
    exact integrable_stoppedValue_of_memLp_two
      (R := factorialGridSampledResidual V F mu T C r)
      (fun i => factorialGridSampledResidual_value_memLp_two
        (F := F) (mu := mu) hV hRows r i)
      q hq (size T r) hq_le
  rw [← factorialGridSampledResidual_at_rightRoundedIndex
    (T := T) (τ := τ) r]
  exact hstop

omit [SigmaFiniteFiltration mu F] in
theorem integrable_source_at_rightRoundedTime
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    Integrable (fun omega =>
      V (rightRoundedTime T τ r omega) omega) mu := by
  let sigma : Ω → WithTop NNReal := fun omega =>
    (rightRoundedTime T τ r omega : WithTop NNReal)
  have hsigma : IsStoppingTime F sigma := by
    simpa only [sigma] using
      rightRoundedTime_isStoppingTime (T := T) (τ := τ) hτ r
  have hsigma_le : ∀ omega, sigma omega ≤ (T : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr
      ((rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).2)
  have hProgressive : IsStronglyProgressive F V :=
    FTAPTheorem42.StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hV.stronglyAdapted hV.rightContinuous
  have hMeas : StronglyMeasurable[hsigma.measurableSpace]
      (MeasureTheory.stoppedValue V sigma) :=
    MeasureTheory.measurable_stoppedValue hProgressive hsigma |>.stronglyMeasurable
  have hMem : MemLp (MeasureTheory.stoppedValue V sigma)
      (2 : ENNReal) mu := by
    apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
      (hMeas.mono hsigma.measurableSpace_le).aestronglyMeasurable
      (C : Real)
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hV.value_le_bound (WithTop.coe_le_coe.mp (hsigma_le omega)) omega
    · exact hV.value_nonneg (WithTop.coe_le_coe.mp (hsigma_le omega)) omega
  have hEq : MeasureTheory.stoppedValue V sigma =
      (fun omega => V (rightRoundedTime T τ r omega) omega) := by
    funext omega
    change V (sigma omega).untopA omega = V (rightRoundedTime T τ r omega) omega
    have hne : sigma omega ≠ ⊤ := WithTop.coe_ne_top
    have htime : (sigma omega).untopA = rightRoundedTime T τ r omega := by
      rw [show sigma omega = (rightRoundedTime T τ r omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    rw [htime]
  rw [← hEq]
  exact hMem.integrable (by norm_num)

/-! ## The finite-grid residual has zero terminal expectation -/

omit [SigmaFiniteFiltration mu F] in
theorem integral_factorialGridSampledResidual_at_rightRoundedIndex_eq_zero
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat)
    (hResidual : FactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows r)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    (∫ omega, factorialGridSampledResidual V F mu T C r
      (rightRoundedIndex T τ r omega) omega ∂mu) = 0 := by
  let q : Ω → WithTop Nat := fun omega =>
    (rightRoundedIndex T τ r omega : WithTop Nat)
  let N : Nat := size T r
  have hq : IsStoppingTime ((grid T r).sampledFiltration F) q := by
    simpa only [q] using
      rightRoundedIndex_isStoppingTime (T := T) (τ := τ) hτ hτT r
  have hq_le : ∀ omega, q omega ≤ (N : WithTop Nat) := by
    intro omega
    change (rightRoundedIndex T τ r omega : WithTop Nat) ≤
      (size T r : WithTop Nat)
    exact WithTop.coe_le_coe.mpr
      (rightRoundedIndex_le_size (T := T) (τ := τ) r omega)
  have hTerminalEq := hResidual.terminal_eq
  have hVTerminalInt : Integrable (V T) mu :=
    (hV.value_memLp_two (mu := mu) le_rfl).integrable (by norm_num)
  have hPTerminalInt : Integrable
      (predictableCompensatorProcess V F mu T C r T) mu :=
    (hRows.terminal_memLp_two r).integrable (by norm_num)
  have hResidualTerminalIntegral :
      (∫ omega, factorialGridSampledResidual V F mu T C r N omega ∂mu) = 0 := by
    rw [show N = size T r from rfl, hTerminalEq]
    rw [integral_sub hVTerminalInt hPTerminalInt]
    rw [hRows.terminal_expectation r]
    ring
  have hIntegralStopZero :
      (∫ omega, MeasureTheory.stoppedValue
        (factorialGridSampledResidual V F mu T C r) q omega ∂mu) = 0 := by
    exact integral_stoppedValue_eq_zero_of_martingale
      hResidual.martingale (size T r) hResidualTerminalIntegral q hq hq_le
  have hSampleEq : (fun omega => factorialGridSampledResidual V F mu T C r
      (rightRoundedIndex T τ r omega) omega) =
      MeasureTheory.stoppedValue
        (factorialGridSampledResidual V F mu T C r) q := by
      simpa [q] using
      (factorialGridSampledResidual_at_rightRoundedIndex
        (T := T) (τ := τ) r).symm
  calc
    (∫ omega, factorialGridSampledResidual V F mu T C r
        (rightRoundedIndex T τ r omega) omega ∂mu) =
        ∫ omega, MeasureTheory.stoppedValue
          (factorialGridSampledResidual V F mu T C r) q omega ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun omega =>
        congrFun hSampleEq omega)
    _ = 0 := hIntegralStopZero

/-! ## Main finite-grid stopped expectation identity -/

omit [SigmaFiniteFiltration mu F] in
theorem integral_predictableCompensatorProcess_at_tau_eq_integral_source_at_rightRoundedTime
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r : Nat)
    (hResidual : FactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows r)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Integrable (fun omega =>
      predictableCompensatorProcess V F mu T C r (τ omega) omega) mu ∧
    Integrable (fun omega => V (rightRoundedTime T τ r omega) omega) mu ∧
    (∫ omega, predictableCompensatorProcess V F mu T C r
      (τ omega) omega ∂mu) =
      ∫ omega, V (rightRoundedTime T τ r omega) omega ∂mu := by
  have hResidualInt := integrable_factorialGridSampledResidual_at_rightRoundedIndex
    (F := F) (mu := mu) hV hRows hτ hτT r
  have hSourceInt := integrable_source_at_rightRoundedTime
    (F := F) (mu := mu) hV hτ hτT r
  have hResidualZero := integral_factorialGridSampledResidual_at_rightRoundedIndex_eq_zero
    (F := F) (mu := mu) hV hRows r hResidual hτ hτT
  have hActivation : ∀ omega,
      predictableCompensatorProcess V F mu T C r (τ omega) omega =
        predictableCompensatorProcess V F mu T C r
          (rightRoundedTime T τ r omega) omega := by
    intro omega
    exact predictableCompensatorProcess_at_tau_eq_at_rightRoundedTime
      (V := V) (F := F) (mu := mu) (T := T) (C := C) hτT r omega
  have hSigmaGrid : ∀ omega,
      rightRoundedTime T τ r omega =
        (grid T r).sampledTime (rightRoundedIndex T τ r omega) := fun omega =>
    rightRoundedTime_eq_sampledTime_index (T := T) (τ := τ) hτT r omega
  have hResidualPointwise : ∀ omega,
      factorialGridSampledResidual V F mu T C r
          (rightRoundedIndex T τ r omega) omega =
        V (rightRoundedTime T τ r omega) omega -
          predictableCompensatorProcess V F mu T C r
            (rightRoundedTime T τ r omega) omega := by
    intro omega
    rw [factorialGridSampledResidual_apply, hSigmaGrid omega]
  have hCore := integrable_and_integral_eq_of_activation
    (mu := mu)
    (pTau := fun omega =>
      predictableCompensatorProcess V F mu T C r (τ omega) omega)
    (pSigma := fun omega =>
      predictableCompensatorProcess V F mu T C r
        (rightRoundedTime T τ r omega) omega)
    (sourceSigma := fun omega => V (rightRoundedTime T τ r omega) omega)
    (residualSigma := fun omega => factorialGridSampledResidual V F mu T C r
      (rightRoundedIndex T τ r omega) omega)
    hResidualInt hSourceInt hResidualZero
    (funext hActivation) (funext hResidualPointwise)
  exact ⟨hCore.1, hSourceInt, hCore.2⟩

end HorizonFactorialGrid

end FTAPTheorem42
