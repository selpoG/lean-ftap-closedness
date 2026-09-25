/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingOptionalSampling
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequence
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingConvexExpectationCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convexified compensator rows at a bounded stopping time

The common tail weights can be used at a bounded stopping time without any
new choice of coefficients.  For each row, the preceding finite-grid
optional-sampling result identifies the row integral with the source at the
right-rounded time.  The source convex combination is then squeezed by the
uniform factorial mesh.  The upper time is clamped at the fixed horizon, so
all uses of the bounded source estimate remain within its controlled range.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

/-! The bounded source is only an adapter for the source-independent stopping
convex-expectation algebra. -/

theorem boundedStoppingConvexSourceData
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    StoppingConvexSourceData F V T := {
  stronglyAdapted := hV.stronglyAdapted
  rightContinuous := hV.rightContinuous
  monotone := hV.monotone
  value_nonnegative := hV.value_nonneg }

/-! ## The rounded source convex combination -/

theorem roundedSourceConvexSample_squeeze
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (w : TailConvexWeights n) (τ : Ω → NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (omega : Ω) :
    V (τ omega) omega ≤ roundedSourceConvexSampleCore (V := V) (T := T) τ w omega ∧
      roundedSourceConvexSampleCore (V := V) (T := T) τ w omega ≤
        V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ∧
      V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ≤ V T omega := by
  exact roundedSourceConvexSampleCore_squeeze
    (F := F) (boundedStoppingConvexSourceData hV) w τ hτT omega

theorem tendsto_roundedSourceConvexSample
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    {w : ∀ n, TailConvexWeights n}
    (τ : Ω → NNReal) (hτT : ∀ omega, τ omega ≤ T)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) (omega : Ω) :
    Tendsto
      (fun n => roundedSourceConvexSampleCore (V := V) (T := T) τ
        (w (cutoff n)) omega) atTop
      (𝓝 (V (τ omega) omega)) := by
  exact tendsto_roundedSourceConvexSampleCore
    (F := F) (boundedStoppingConvexSourceData hV)
    τ hτT hCutoff omega

/-! ## Finite-sum integrability and row/source integral identity -/

private theorem roundedSourceConvexSample_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (w : TailConvexWeights n) :
    Integrable (roundedSourceConvexSampleCore (V := V) (T := T) τ w) mu := by
  exact roundedSourceConvexSampleCore_integrable
    (F := F) (mu := mu) (boundedStoppingConvexSourceData hV)
    (hV.value_memLp_two (mu := mu) le_rfl)
    hτ hτT w

private theorem boundedStoppingRowExpectationCertificate
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    StoppingRowExpectationCertificate (mu := mu)
      (fun r => predictableCompensatorProcess V F mu T C r)
      (fun r omega => V (rightRoundedTime T τ r omega) omega) τ := {
  row_integrable := fun r =>
    (integral_predictableCompensatorProcess_at_tau_eq_integral_source_at_rightRoundedTime
      (F := F) (mu := mu) hV hRows r (hResidual r) hτ hτT).1
  source_integrable := fun r =>
    (integral_predictableCompensatorProcess_at_tau_eq_integral_source_at_rightRoundedTime
      (F := F) (mu := mu) hV hRows r (hResidual r) hτ hτT).2.1
  integral_row_eq_source := fun r =>
    (integral_predictableCompensatorProcess_at_tau_eq_integral_source_at_rightRoundedTime
      (F := F) (mu := mu) hV hRows r (hResidual r) hτ hτT).2.2 }

private theorem compensatorConvexRow_at_tau_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (w : TailConvexWeights n) :
    Integrable (fun omega =>
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) w (τ omega) omega) mu := by
  change Integrable (processConvexSampleCore
    (fun r => predictableCompensatorProcess V F mu T C r) τ w) mu
  exact processConvexSampleCore_integrable
    (mu := mu) (fun r => predictableCompensatorProcess V F mu T C r) τ
    (boundedStoppingRowExpectationCertificate
      (F := F) (mu := mu) hV hRows hResidual τ hτ hτT) w

theorem compensatorConvexRow_at_tau_integral_eq_roundedSourceConvexSample_integral
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (w : TailConvexWeights n) :
    (∫ omega, compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) w (τ omega) omega ∂mu) =
      ∫ omega, roundedSourceConvexSampleCore (V := V) (T := T) τ w omega ∂mu := by
  change (∫ omega, processConvexSampleCore
      (fun r => predictableCompensatorProcess V F mu T C r) τ w omega ∂mu) =
    ∫ omega, roundedSourceConvexSampleCore V T τ w omega ∂mu
  exact processConvexSampleCore_integral_eq_roundedSourceConvexSampleCore_integral
    (mu := mu) (fun r => predictableCompensatorProcess V F mu T C r) τ
    (boundedStoppingRowExpectationCertificate
      (F := F) (mu := mu) hV hRows hResidual τ hτ hτT) w

/-! ## The endpoint along the common subsequence -/

structure FactorialGridPredictableCompensatorStoppingConvexExpectationData
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
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) : Prop where
  rounded_source_integrable : ∀ n, Integrable
    (roundedSourceConvexSampleCore (V := V) (T := T) τ (w (cutoff n))) mu
  rounded_source_squeeze : ∀ n omega,
    V (τ omega) omega ≤ roundedSourceConvexSampleCore (V := V) (T := T) τ
        (w (cutoff n)) omega ∧
      roundedSourceConvexSampleCore (V := V) (T := T) τ (w (cutoff n)) omega ≤
        V (min (τ omega + ((cutoff n).factorial : NNReal)⁻¹) T) omega ∧
      V (min (τ omega + ((cutoff n).factorial : NNReal)⁻¹) T) omega ≤ V T omega
  compensator_integrable : ∀ n, Integrable (fun omega =>
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) (τ omega) omega) mu
  finite_sum_identity : ∀ n,
    (∫ omega, compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) (τ omega) omega ∂mu) =
      ∫ omega, roundedSourceConvexSampleCore (V := V) (T := T) τ
        (w (cutoff n)) omega ∂mu
  rounded_source_tendsto_ae : ∀ᵐ omega ∂mu,
    Tendsto (fun n => roundedSourceConvexSampleCore (V := V) (T := T) τ
      (w (cutoff n)) omega) atTop (𝓝 (V (τ omega) omega))
  integral_tendsto : Tendsto (fun n =>
      ∫ omega, compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) (τ omega) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu))

theorem integral_compensatorConvexRow_at_stoppingTime_tendsto
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
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) :
    Tendsto (fun n =>
      ∫ omega, compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) (τ omega) omega ∂mu) atTop
    (𝓝 (∫ omega, V (τ omega) omega ∂mu)) := by
  change Tendsto (fun n =>
      ∫ omega, processConvexSampleCore
        (fun r => predictableCompensatorProcess V F mu T C r) τ
        (w (cutoff n)) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu))
  exact integral_processConvexSampleCore_at_stopping_tendsto
    (F := F) (mu := mu) (boundedStoppingConvexSourceData hV)
    (hV.value_memLp_two (mu := mu) le_rfl)
    (fun r => predictableCompensatorProcess V F mu T C r) τ hτ hτT
    (boundedStoppingRowExpectationCertificate
      (F := F) (mu := mu) hV hRows hResidual τ hτ hτT)
    w cutoff hData.cutoff_strictMono

theorem factorialGridPredictableCompensatorStoppingConvexExpectation_producer
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
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (FactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT) := by
  refine ⟨{
    rounded_source_integrable := ?_
    rounded_source_squeeze := ?_
    compensator_integrable := ?_
    finite_sum_identity := ?_
    rounded_source_tendsto_ae := ?_
    integral_tendsto := ?_ }⟩
  · intro n
    exact roundedSourceConvexSample_integrable
      (F := F) (mu := mu) hV τ hτ hτT (w (cutoff n))
  · intro n omega
    exact roundedSourceConvexSample_squeeze
      (F := F) (V := V) (T := T) (C := C) hV
      (w (cutoff n)) τ hτT omega
  · intro n
    exact compensatorConvexRow_at_tau_integrable
      (F := F) (mu := mu) hV hRows hResidual τ hτ hτT (w (cutoff n))
  · intro n
    exact compensatorConvexRow_at_tau_integral_eq_roundedSourceConvexSample_integral
      (F := F) (mu := mu) hV hRows hResidual τ hτ hτT (w (cutoff n))
  · filter_upwards [] with omega
    exact tendsto_roundedSourceConvexSample
      (F := F) (V := V) (T := T) (C := C) hV τ hτT
      hData.cutoff_strictMono omega
  · exact integral_compensatorConvexRow_at_stoppingTime_tendsto
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
      cutoff hData τ hτ hτT

theorem exists_factorialGridPredictableCompensatorStoppingConvexExpectation
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
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (FactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT) :=
  factorialGridPredictableCompensatorStoppingConvexExpectation_producer
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT

end HorizonFactorialGrid

end FTAPTheorem42
