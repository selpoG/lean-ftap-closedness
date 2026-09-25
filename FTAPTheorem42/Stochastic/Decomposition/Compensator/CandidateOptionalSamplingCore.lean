/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Foundations.ProcessIndistinguishable

/-!
# Source-independent optional sampling for a càdlàg candidate

The candidate optional-sampling argument only needs the integrability of the
source at the stopping time.  The source-specific bounded and square-
integrable adapters provide that input; the martingale and process-version
part is shared here.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V M Pcad Preg : Process Ω} {T : NNReal}

/-! ## The source-independent certificate -/

structure CandidateOptionalSamplingData
    (V M Preg : Process Ω) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) : Prop where
  source_sample_integrable : Integrable
    (fun omega => V (τ omega) omega) mu
  martingale_sample_integrable : Integrable
    (fun omega => M (τ omega) omega) mu
  candidate_sample_integrable : Integrable
    (fun omega => Preg (τ omega) omega) mu
  martingale_sample_integral_eq_zero :
    (∫ omega, M (τ omega) omega ∂mu) = 0
  candidate_sample_integral_eq_source :
    (∫ omega, Preg (τ omega) omega ∂mu) =
      ∫ omega, V (τ omega) omega ∂mu

/-! The integral of the stopped martingale is its zero-time integral. -/

omit [SigmaFiniteFiltration mu F] in
theorem martingale_sample_integral_eq_zero_of_ae_zero
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMZero : M 0 =ᵐ[mu] 0)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    (∫ omega, M (τ omega) omega ∂mu) = 0 := by
  have hMInt : Integrable (fun omega => M (τ omega) omega) mu :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hSampleTerminal :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hSampleTerminalIntegral :
      (∫ omega, M (τ omega) omega ∂mu) =
        ∫ omega, M (T + 1) omega ∂mu := by
    calc
      (∫ omega, M (τ omega) omega ∂mu) =
          ∫ omega, mu[M (T + 1) | hτ.measurableSpace] omega ∂mu :=
        integral_congr_ae hSampleTerminal
      _ = ∫ omega, M (T + 1) omega ∂mu :=
        integral_condExp hτ.measurableSpace_le
  have hMZeroIntegral : (∫ omega, M 0 omega ∂mu) = 0 := by
    calc
      (∫ omega, M 0 omega ∂mu) = ∫ omega, (0 : Real) ∂mu :=
        integral_congr_ae hMZero
      _ = 0 := by simp
  have hMZeroTerminal :
      (∫ omega, M 0 omega ∂mu) = ∫ omega, M (T + 1) omega ∂mu := by
    simpa only [setIntegral_univ] using
      (hM.setIntegral_eq
        (i := (0 : NNReal)) (j := T + 1) (by positivity)
        MeasurableSet.univ)
  calc
    (∫ omega, M (τ omega) omega ∂mu) =
        ∫ omega, M (T + 1) omega ∂mu := hSampleTerminalIntegral
    _ = ∫ omega, M 0 omega ∂mu := hMZeroTerminal.symm
    _ = 0 := hMZeroIntegral

/-! The full candidate expectation endpoint.  The process equality is used
only through one common full-measure set supplied by
`ProcessIndistinguishable`; in particular, the random-time substitution is
not assembled from separate fixed-time a.e. equalities. -/

omit [SigmaFiniteFiltration mu F] in
theorem candidateOptionalSampling_producer
    {τ : Ω → NNReal}
    (hSourceInt : Integrable (fun omega => V (τ omega) omega) mu)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMZero : M 0 =ᵐ[mu] 0)
    (hPcad : Pcad = fun t omega => V t omega - M t omega)
    (hPreg : ProcessIndistinguishable mu Preg Pcad)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (CandidateOptionalSamplingData (F := F) (mu := mu)
      V M Preg τ hτ hτT) := by
  have hMInt : Integrable (fun omega => M (τ omega) omega) mu :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hMIntegral : (∫ omega, M (τ omega) omega ∂mu) = 0 :=
    martingale_sample_integral_eq_zero_of_ae_zero
      (F := F) (mu := mu) hM hMRight hMZero hτ hτT
  have hPregEq : (fun omega => Preg (τ omega) omega) =ᵐ[mu]
      (fun omega => V (τ omega) omega - M (τ omega) omega) := by
    filter_upwards [hPreg] with omega hPregOmega
    have hPcadOmega := hPregOmega (τ omega)
    have hDefinition := congrFun hPcad (τ omega)
    have hDefinitionOmega := congrFun hDefinition omega
    exact hPcadOmega.trans (by simpa using hDefinitionOmega)
  have hPregInt : Integrable (fun omega => Preg (τ omega) omega) mu := by
    exact (hSourceInt.sub hMInt).congr hPregEq.symm
  have hPregIntegral :
      (∫ omega, Preg (τ omega) omega ∂mu) =
        ∫ omega, V (τ omega) omega ∂mu := by
    calc
      (∫ omega, Preg (τ omega) omega ∂mu) =
          ∫ omega, (V (τ omega) omega - M (τ omega) omega) ∂mu :=
        integral_congr_ae hPregEq
      _ = (∫ omega, V (τ omega) omega ∂mu) -
          ∫ omega, M (τ omega) omega ∂mu :=
        integral_sub hSourceInt hMInt
      _ = ∫ omega, V (τ omega) omega ∂mu := by
        rw [hMIntegral, sub_zero]
  exact ⟨{
    source_sample_integrable := hSourceInt
    martingale_sample_integrable := hMInt
    candidate_sample_integrable := hPregInt
    martingale_sample_integral_eq_zero := hMIntegral
    candidate_sample_integral_eq_source := hPregIntegral }⟩

end HorizonFactorialGrid

end FTAPTheorem42
