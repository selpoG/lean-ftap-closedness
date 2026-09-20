/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagMonotoneRegularization
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CandidateOptionalSamplingCore
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bounded optional sampling for the càdlàg compensator candidate

The regularized increasing candidate is indistinguishable from the càdlàg
candidate `Pcad = V - M`.  Continuous-time bounded optional sampling for the
martingale `M` therefore identifies the candidate's expectation at every
bounded stopping time with the source expectation.  This module records only
that stopping-time endpoint; it does not identify the predictable limsup.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T C : NNReal}

omit [SigmaFiniteFiltration mu F] in
private theorem integrable_source_at_boundedStoppingTime
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Integrable (fun omega => V (τ omega) omega) mu := by
  let sigma : Ω → WithTop NNReal := fun omega =>
    (τ omega : WithTop NNReal)
  have hsigma : IsStoppingTime F sigma := by
    simpa only [sigma] using hτ
  have hsigma_le : ∀ omega, sigma omega ≤ (T : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr (hτT omega)
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
    change ‖V (sigma omega).untopA omega‖ ≤ (C : Real)
    have hne : sigma omega ≠ ⊤ := by
      exact WithTop.coe_ne_top
    have htime : (sigma omega).untopA = τ omega := by
      rw [show sigma omega = (τ omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    rw [htime, Real.norm_eq_abs,
      abs_of_nonneg (hV.value_nonneg (hτT omega) omega)]
    exact hV.value_le_bound (hτT omega) omega
  have hEq : MeasureTheory.stoppedValue V sigma =
      (fun omega => V (τ omega) omega) := by
    funext omega
    change V (sigma omega).untopA omega = V (τ omega) omega
    have hne : sigma omega ≠ ⊤ := by
      exact WithTop.coe_ne_top
    have htime : (sigma omega).untopA = τ omega := by
      rw [show sigma omega = (τ omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    rw [htime]
  rw [← hEq]
  exact hMem.integrable (by norm_num)

/-! ## The bounded-stopping certificate -/

structure FactorialGridPredictableCompensatorCandidateOptionalSamplingData
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      (F := F) (mu := mu) (T := T) (C := C)
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      (T := T) (C := C) hCad bad Preg)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
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

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridPredictableCompensatorCandidateOptionalSampling_producer
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      (T := T) (C := C) hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      (T := T) (C := C) hCad bad Preg)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (FactorialGridPredictableCompensatorCandidateOptionalSamplingData
      (T := T) (C := C) hV hRows hControl hResidual w y hCommon Z M Pcad
      hCad bad Preg hReg τ hτ hτT) := by
  have hVInt : Integrable (fun omega => V (τ omega) omega) mu :=
    integrable_source_at_boundedStoppingTime (F := F) (mu := mu) hV hτ hτT
  have hMZero : M 0 =ᵐ[mu] 0 := by
    have hDef := congrFun hCad.Pcad_definition (0 : NNReal)
    filter_upwards [hCad.Pcad_zero] with omega hP
    have hDefOmega := congrFun hDef omega
    have hVZero := congrFun hV.zero omega
    change Pcad 0 omega = 0 at hP
    change V 0 omega = 0 at hVZero
    change Pcad 0 omega = V 0 omega - M 0 omega at hDefOmega
    rw [hDefOmega, hVZero] at hP
    have hNeg : -M 0 omega = 0 := by simpa using hP
    exact neg_eq_zero.mp hNeg
  have hCore := candidateOptionalSampling_producer
    (F := F) (mu := mu) (V := V) (M := M) (Pcad := Pcad) (Preg := Preg)
    (T := T) hVInt hCad.M_martingale hCad.M_rightContinuous hMZero
    hCad.Pcad_definition hReg.Preg_indistinguishable hτ hτT
  rcases hCore with ⟨hCore⟩
  exact ⟨{
    source_sample_integrable := hCore.source_sample_integrable
    martingale_sample_integrable := hCore.martingale_sample_integrable
    candidate_sample_integrable := hCore.candidate_sample_integrable
    martingale_sample_integral_eq_zero := hCore.martingale_sample_integral_eq_zero
    candidate_sample_integral_eq_source := hCore.candidate_sample_integral_eq_source }⟩

omit [SigmaFiniteFiltration mu F] in
theorem exists_factorialGridPredictableCompensatorCandidateOptionalSampling
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      (T := T) (C := C) hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      (T := T) (C := C) hCad bad Preg)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (FactorialGridPredictableCompensatorCandidateOptionalSamplingData
      (T := T) (C := C) hV hRows hControl hResidual w y hCommon Z M Pcad
      hCad bad Preg hReg τ hτ hτT) := by
  exact factorialGridPredictableCompensatorCandidateOptionalSampling_producer
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon Z M Pcad
    hCad bad Preg hReg τ hτ hτT

end HorizonFactorialGrid

end FTAPTheorem42
