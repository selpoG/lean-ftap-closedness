/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingConvexExpectationCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingOptionalSampling
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CommonAESubsequence

/-!
# Stopping-time convex expectations for square-integrable rows

This is the square-integrable adapter for the source-independent stopping-time
convex-expectation algebra.  The rows, weights, and cutoff are supplied by the
common Hilbert/A.E. package and are not reselected at the stopping time.  The
terminal value `V T` is the dominator; no deterministic source bound is used.
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

/-! ## Adapters for the source and row stopping certificates -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableStoppingOptionalSamplingCertificates
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    ∀ r, Nonempty
      (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
        (F := F) (mu := mu) hV hRows hControl r (hResidual r) τ hτ hτT) := by
  intro r
  exact squareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSampling_producer
    (F := F) (mu := mu) hV hRows hControl r (hResidual r) hτ hτT

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableStoppingRowExpectationCertificate
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : ∀ r, Nonempty
      (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
        (F := F) (mu := mu) hV hRows hControl r (hResidual r) τ hτ hτT)) :
    StoppingRowExpectationCertificate (mu := mu)
      (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r)
      (fun r omega => V (rightRoundedTime T τ r omega) omega) τ := by
  let hChoice := fun r => Classical.choice (hStop r)
  exact {
    row_integrable := fun r => (hChoice r).compensator_integrable
    source_integrable := fun r => (hChoice r).source_integrable
    integral_row_eq_source := fun r => (hChoice r).integral_compensator_eq_source }

/-! ## Rounded source rows and the finite-sum identity -/

noncomputable def squareIntegrableRoundedSourceConvexSample
    (τ : Ω → NNReal) (w : TailConvexWeights n) : Ω → Real :=
  roundedSourceConvexSampleCore V T τ w

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableRoundedSourceConvexSample_squeeze
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (w : TailConvexWeights n) (τ : Ω → NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (omega : Ω) :
    V (τ omega) omega ≤
        squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ w omega ∧
      squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ w omega ≤
        V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ∧
      V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ≤ V T omega := by
  change V (τ omega) omega ≤ roundedSourceConvexSampleCore V T τ w omega ∧
    roundedSourceConvexSampleCore V T τ w omega ≤
      V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ∧
    V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ≤ V T omega
  exact roundedSourceConvexSampleCore_squeeze
    (F := F) (squareIntegrableStoppingConvexSourceData
      (F := F) (mu := mu) hV) w τ hτT omega

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableTendstoRoundedSourceConvexSample
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    {w : ∀ n, TailConvexWeights n}
    (τ : Ω → NNReal) (hτT : ∀ omega, τ omega ≤ T)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) (omega : Ω) :
    Tendsto
      (fun n => squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
        (w (cutoff n)) omega) atTop
      (𝓝 (V (τ omega) omega)) := by
  change Tendsto
      (fun n => roundedSourceConvexSampleCore V T τ
        (w (cutoff n)) omega) atTop
      (𝓝 (V (τ omega) omega))
  exact tendsto_roundedSourceConvexSampleCore
    (F := F) (squareIntegrableStoppingConvexSourceData
      (F := F) (mu := mu) hV) τ hτT hCutoff omega

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableRoundedSourceConvexSample_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (w : TailConvexWeights n) :
    Integrable
      (squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ w) mu := by
  change Integrable (roundedSourceConvexSampleCore V T τ w) mu
  exact roundedSourceConvexSampleCore_integrable
    (F := F) (mu := mu)
    (squareIntegrableStoppingConvexSourceData (F := F) (mu := mu) hV)
    hV.terminal_memLp_two hτ hτT w

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableCompensatorConvexRow_at_tau_integrable
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : ∀ r, Nonempty
      (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
        (F := F) (mu := mu) hV hRows hControl r (hResidual r) τ hτ hτT))
    (w : TailConvexWeights n) :
    Integrable (fun omega =>
      squareIntegrableCompensatorConvexRow hV hRows hControl hResidual w
        (τ omega) omega) mu := by
  change Integrable (processConvexSampleCore
    (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r) τ w) mu
  exact processConvexSampleCore_integrable
    (mu := mu) (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r)
    τ (squareIntegrableStoppingRowExpectationCertificate
      (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT hStop) w

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableCompensatorConvexRow_at_tau_integral_eq_roundedSourceConvexSample_integral
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : ∀ r, Nonempty
      (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
        (F := F) (mu := mu) hV hRows hControl r (hResidual r) τ hτ hτT))
    (w : TailConvexWeights n) :
    (∫ omega, squareIntegrableCompensatorConvexRow hV hRows hControl hResidual w
      (τ omega) omega ∂mu) =
      ∫ omega, squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ w
        omega ∂mu := by
  change (∫ omega, processConvexSampleCore
      (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r) τ w
      omega ∂mu) =
    ∫ omega, roundedSourceConvexSampleCore V T τ w omega ∂mu
  exact processConvexSampleCore_integral_eq_roundedSourceConvexSampleCore_integral
    (mu := mu) (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r)
    τ (squareIntegrableStoppingRowExpectationCertificate
      (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT hStop) w

/-! ## The common subsequence endpoint -/

structure SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) : Prop where
  optional_sampling : ∀ r, Nonempty
    (SquareIntegrableFactorialGridPredictableCompensatorStoppingOptionalSamplingData
      (F := F) (mu := mu) hV hRows hControl r (hResidual r) τ hτ hτT)
  rounded_source_integrable : ∀ n, Integrable
    (squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
      (w (cutoff n))) mu
  rounded_source_squeeze : ∀ n omega,
    V (τ omega) omega ≤ squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
        (w (cutoff n)) omega ∧
      squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
          (w (cutoff n)) omega ≤
        V (min (τ omega + ((cutoff n).factorial : NNReal)⁻¹) T) omega ∧
      V (min (τ omega + ((cutoff n).factorial : NNReal)⁻¹) T) omega ≤ V T omega
  compensator_integrable : ∀ n, Integrable (fun omega =>
    squareIntegrableCompensatorConvexRow hV hRows hControl hResidual
      (w (cutoff n)) (τ omega) omega) mu
  finite_sum_identity : ∀ n,
    (∫ omega, squareIntegrableCompensatorConvexRow hV hRows hControl hResidual
      (w (cutoff n)) (τ omega) omega ∂mu) =
      ∫ omega, squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
        (w (cutoff n)) omega ∂mu
  rounded_source_tendsto_ae : ∀ᵐ omega ∂mu,
    Tendsto (fun n => squareIntegrableRoundedSourceConvexSample (V := V) (T := T) τ
      (w (cutoff n)) omega) atTop (𝓝 (V (τ omega) omega))
  integral_tendsto : Tendsto (fun n =>
      ∫ omega, squareIntegrableCompensatorConvexRow hV hRows hControl hResidual
        (w (cutoff n)) (τ omega) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu))

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectation_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal))) (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT) := by
  let hStop := squareIntegrableStoppingOptionalSamplingCertificates
    (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT
  refine ⟨{
    optional_sampling := hStop
    rounded_source_integrable := ?_
    rounded_source_squeeze := ?_
    compensator_integrable := ?_
    finite_sum_identity := ?_
    rounded_source_tendsto_ae := ?_
    integral_tendsto := ?__ }⟩
  · intro n
    exact squareIntegrableRoundedSourceConvexSample_integrable
      (F := F) (mu := mu) hV τ hτ hτT (w (cutoff n))
  · intro n omega
    exact squareIntegrableRoundedSourceConvexSample_squeeze
      (F := F) (mu := mu) hV (w (cutoff n)) τ hτT omega
  · intro n
    exact squareIntegrableCompensatorConvexRow_at_tau_integrable
      (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT hStop
      (w (cutoff n))
  · intro n
    exact squareIntegrableCompensatorConvexRow_at_tau_integral_eq_roundedSourceConvexSample_integral
      (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT hStop
      (w (cutoff n))
  · filter_upwards [] with omega
    exact squareIntegrableTendstoRoundedSourceConvexSample
      (F := F) (mu := mu) hV τ hτT hData.cutoff_strictMono omega
  · change Tendsto (fun n =>
      ∫ omega, processConvexSampleCore
        (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r) τ
        (w (cutoff n)) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu))
    exact integral_processConvexSampleCore_at_stopping_tendsto
      (F := F) (mu := mu)
      (squareIntegrableStoppingConvexSourceData (F := F) (mu := mu) hV)
      hV.terminal_memLp_two
      (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r) τ hτ hτT
      (squareIntegrableStoppingRowExpectationCertificate
        (F := F) (mu := mu) hV hRows hControl hResidual τ hτ hτT hStop)
      w cutoff hData.cutoff_strictMono

end HorizonFactorialGrid

end FTAPTheorem42
