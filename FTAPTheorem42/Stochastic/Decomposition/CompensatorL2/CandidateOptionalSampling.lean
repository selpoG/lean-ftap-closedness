/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CandidateOptionalSamplingCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CadlagCandidate

/-!
# Continuous-time optional sampling for the square-integrable candidate

The source sample is controlled by the terminal random envelope.  This file
therefore supplies only the `L²` adapter to the source-independent candidate
optional-sampling core; no deterministic source bound is introduced.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T : NNReal}

open SquareIntegrableIncreasingProcessData

/-! ## The `L²` source-sample adapter -/

omit [SigmaFiniteFiltration mu F] in
theorem integrable_squareIntegrableSource_at_boundedStoppingTime
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
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
    apply MemLp.of_le hV.terminal_memLp_two
      (hMeas.mono hsigma.measurableSpace_le).aestronglyMeasurable
    filter_upwards with omega
    change ‖V (sigma omega).untopA omega‖ ≤ ‖V T omega‖
    have hne : sigma omega ≠ ⊤ := WithTop.coe_ne_top
    have htime : (sigma omega).untopA = τ omega := by
      rw [show sigma omega = (τ omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    have htime_le : (sigma omega).untopA ≤ T := by
      rw [htime]
      exact hτT omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.value_nonneg htime_le omega),
      Real.norm_eq_abs, abs_of_nonneg
        (hV.value_nonneg (t := T) le_rfl omega)]
    exact hV.value_le_terminal htime_le omega
  have hEq : MeasureTheory.stoppedValue V sigma =
      (fun omega => V (τ omega) omega) := by
    funext omega
    change V (sigma omega).untopA omega = V (τ omega) omega
    have hne : sigma omega ≠ ⊤ := WithTop.coe_ne_top
    have htime : (sigma omega).untopA = τ omega := by
      rw [show sigma omega = (τ omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    rw [htime]
  rw [← hEq]
  exact hMem.integrable (by norm_num)

/-! ## The specialized output certificate -/

abbrev SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
      hV hRows hControl hResidual w y hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (_hReg : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) : Prop :=
  CandidateOptionalSamplingData (F := F) (mu := mu)
    V M Preg τ hτ hτT

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableIncreasingProcessCandidateOptionalSampling_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
      hV hRows hControl hResidual w y hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty (SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg
        τ hτ hτT) := by
  have hSourceInt : Integrable (fun omega => V (τ omega) omega) mu :=
    integrable_squareIntegrableSource_at_boundedStoppingTime
      (F := F) (mu := mu) hV hτ hτT
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
  exact candidateOptionalSampling_producer
    (F := F) (mu := mu) (V := V) (M := M) (Pcad := Pcad) (Preg := Preg)
    (T := T) hSourceInt hCad.M_martingale hCad.M_rightContinuous hMZero
    hCad.Pcad_definition hReg.Preg_indistinguishable hτ hτT

end HorizonFactorialGrid

end FTAPTheorem42
