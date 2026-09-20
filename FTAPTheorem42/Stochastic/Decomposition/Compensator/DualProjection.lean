/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequence
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableVersionCore
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The completed predictable compensator certificate

The preceding modules identify a predictable limsup with a regularized
càdlàg increasing candidate.  This file records the next consumer boundary.
The terminal `L²` estimate is transferred from the convexified terminal rows,
and the residual is identified with the already constructed martingale by
process indistinguishability.  Thus martingale testing is not reconstructed by
taking limits of the finite-grid testing identities.
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

/-! ## The completed projection certificate -/

structure FactorialGridPredictableCompensatorDualProjectionData
    {hV : BoundedIncreasingProcessData (F := F) V T C}
    {hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV}
    {hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows}
    {hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)}
    {hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y}
    {cutoff : Nat → Nat}
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (badPred : Set Ω)
    {Ppred Vp : Process Ω} : Prop where
  regularized_data :
    FactorialGridPredictableCompensatorCommonAESubsequenceRegularizedData
      hV hRows hControl hResidual w y hCommon cutoff hData Z M Pcad hCad bad Preg hReg
  predictable_version :
    FactorialGridPredictableCompensatorPredictableVersionData
      (F := F) (mu := mu) (T := T) badPred Ppred Preg Vp
  Vp_terminal_memLp_two : MemLp (Vp T) (2 : ENNReal) mu
  Vp_terminal_L2_bound :
    (∫ omega, (Vp T omega) ^ 2 ∂mu) ≤ 8 * (C : Real) ^ 2
  residual_stronglyAdapted :
    StronglyAdapted F (fun t omega => V t omega - Vp t omega)
  residual_martingale :
    Martingale (fun t omega => V t omega - Vp t omega) F mu
  residual_integrable : ∀ t, Integrable
    (fun omega => V t omega - Vp t omega) mu
  residual_indistinguishable_martingale :
    ProcessIndistinguishable mu
      (fun t omega => V t omega - Vp t omega) M
  interval_testing_identity :
    ∀ {s t : NNReal}, s ≤ t →
      ∀ {B : Set Ω}, MeasurableSet[F s] B →
        (∫ omega in B,
          ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) = 0

/-! ## Transfer of the terminal `L²` estimate -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_dualPredictableProjection_boundedIncreasing
    {hV : BoundedIncreasingProcessData (F := F) V T C}
    {hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV}
    {hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows}
    {hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)}
    {hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y}
    {cutoff : Nat → Nat}
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (badPred : Set Ω)
    (hRegularized : FactorialGridPredictableCompensatorCommonAESubsequenceRegularizedData
      hV hRows hControl hResidual w y hCommon cutoff hData Z M Pcad hCad bad Preg hReg)
    {Ppred Vp : Process Ω}
    (hVersion : FactorialGridPredictableCompensatorPredictableVersionData
      (F := F) (mu := mu) (T := T) badPred Ppred Preg Vp) :
    FactorialGridPredictableCompensatorDualProjectionData
      (F := F) (mu := mu) (T := T) (C := C)
      (Ppred := Ppred) (Vp := Vp) hData hCad bad Preg hReg badPred := by
  let B : Real := Real.sqrt (8 * (C : Real) ^ 2)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hVpMem : MemLp (Vp T) (2 : ENNReal) mu := by
    apply (memLp_congr_ae
      (hVersion.Vp_indistinguishable_Preg.eventuallyEq_at T)).mpr
    exact hRegularized.preg_terminal_memLp_two
  have hRowNorm : ∀ n,
      ‖compensatorConvexRowValueToLp hV hRows hControl
        (w (cutoff n)) T‖ ≤ B := by
    intro n
    dsimp [B]
    exact compensatorConvexRowValueToLp_norm_le
      (F := F) (mu := mu) hV hRows hControl (w (cutoff n)) T
  have hLimitNorm : Tendsto
      (fun n => ‖compensatorConvexRowValueToLp hV hRows hControl
        (w (cutoff n)) T‖) atTop
      (𝓝 ‖hRegularized.preg_terminal_memLp_two.toLp (Preg T)‖) := by
    exact hRegularized.terminal_compensator_tendsto_Lp.norm
  have hPregNorm :
      ‖hRegularized.preg_terminal_memLp_two.toLp (Preg T)‖ ≤ B := by
    exact le_of_tendsto hLimitNorm
      (Filter.Eventually.of_forall hRowNorm)
  have hPregNormEq :
      ‖hRegularized.preg_terminal_memLp_two.toLp (Preg T)‖ =
        Real.sqrt (∫ omega, (Preg T omega) ^ 2 ∂mu) := by
    rw [Lp.norm_toLp]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (FTAPTheorem42.eLpNorm_two_toReal_eq_sqrt_integral_norm_sq
        hRegularized.preg_terminal_memLp_two)
  have hPregSqNonneg : 0 ≤ ∫ omega, (Preg T omega) ^ 2 ∂mu := by
    exact integral_nonneg (fun omega => sq_nonneg _)
  have hBoundPreg :
      (∫ omega, (Preg T omega) ^ 2 ∂mu) ≤ 8 * (C : Real) ^ 2 := by
    have hSqrt := hPregNorm
    rw [hPregNormEq] at hSqrt
    have hSq := (sq_le_sq₀ (Real.sqrt_nonneg _) hB).2 hSqrt
    rw [Real.sq_sqrt hPregSqNonneg, Real.sq_sqrt (by
      positivity : 0 ≤ 8 * (C : Real) ^ 2)] at hSq
    exact hSq
  have hVpSqEq :
      (∫ omega, (Vp T omega) ^ 2 ∂mu) =
        ∫ omega, (Preg T omega) ^ 2 ∂mu := by
    apply integral_congr_ae
    filter_upwards [hVersion.Vp_indistinguishable_Preg.eventuallyEq_at T]
      with omega hω
    rw [hω]
  have hBoundVp :
      (∫ omega, (Vp T omega) ^ 2 ∂mu) ≤ 8 * (C : Real) ^ 2 := by
    rw [hVpSqEq]
    exact hBoundPreg
  have hVPreg : ProcessIndistinguishable mu
      (fun t omega => V t omega - Vp t omega)
      (fun t omega => V t omega - Preg t omega) :=
    ProcessIndistinguishable.sub (ProcessIndistinguishable.refl mu V)
      hVersion.Vp_indistinguishable_Preg
  have hPregPcad : ProcessIndistinguishable mu
      (fun t omega => V t omega - Preg t omega)
      (fun t omega => V t omega - Pcad t omega) :=
    ProcessIndistinguishable.sub (ProcessIndistinguishable.refl mu V)
      hReg.Preg_indistinguishable
  have hPcadM : ProcessIndistinguishable mu
      (fun t omega => V t omega - Pcad t omega) M := by
    filter_upwards [] with omega
    intro t
    have hDef := congrFun hCad.Pcad_definition t
    have hDefOmega := congrFun hDef omega
    rw [hDefOmega]
    ring
  have hResidualM : ProcessIndistinguishable mu
      (fun t omega => V t omega - Vp t omega) M :=
    hVPreg.trans (hPregPcad.trans hPcadM)
  have hResidualAdapted : StronglyAdapted F
      (fun t omega => V t omega - Vp t omega) :=
    hV.stronglyAdapted.sub hVersion.Vp_isStronglyPredictable.stronglyAdapted
  have hResidualMartingale : Martingale
      (fun t omega => V t omega - Vp t omega) F mu :=
    hCad.M_martingale.congr hResidualAdapted
      (fun t => (hResidualM.eventuallyEq_at t).symm)
  have hResidualIntegrable : ∀ t, Integrable
      (fun omega => V t omega - Vp t omega) mu := by
    intro t
    exact hResidualMartingale.integrable t
  have hInterval : ∀ {s t : NNReal}, s ≤ t →
      ∀ {B : Set Ω}, MeasurableSet[F s] B →
        (∫ omega in B,
          ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) = 0 := by
    intro s t hst B hB
    have hSet := hResidualMartingale.setIntegral_eq hst hB
    calc
      (∫ omega in B,
          ((V t omega - Vp t omega) - (V s omega - Vp s omega)) ∂mu) =
          (∫ omega in B, V t omega - Vp t omega ∂mu) -
            ∫ omega in B, V s omega - Vp s omega ∂mu := by
        exact integral_sub (hResidualIntegrable t).restrict
          (hResidualIntegrable s).restrict
      _ = 0 := by
        rw [hSet]
        ring
  exact {
    regularized_data := hRegularized
    predictable_version := hVersion
    Vp_terminal_memLp_two := hVpMem
    Vp_terminal_L2_bound := hBoundVp
    residual_stronglyAdapted := hResidualAdapted
    residual_martingale := hResidualMartingale
    residual_integrable := hResidualIntegrable
    residual_indistinguishable_martingale := hResidualM
    interval_testing_identity := hInterval }

/-! ## Direct consumer for a common-stop Jordan component -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_dualPredictableProjection_of_commonAEJordanComponent
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
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (component : FactorialGridPredictableCompensatorCommonAEJordanComponentData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ bad' : Set Ω, ∃ Vp : Process Ω,
      FactorialGridPredictableCompensatorDualProjectionData
        (F := F) (mu := mu) (T := T) (C := C)
        (Ppred := predictableCompensatorLimsup w component.cutoff V F mu T C)
        (Vp := Vp)
        component.common_subsequence hCad bad Preg hReg bad' := by
  obtain ⟨bad', Vp, hVersion⟩ :=
    exists_predictableCompensatorVersion_of_commonAEJordanComponent
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
      hCad bad Preg hReg component hUsual
  exact ⟨bad', Vp,
    exists_dualPredictableProjection_boundedIncreasing
      (F := F) (mu := mu)
      (Ppred := predictableCompensatorLimsup w component.cutoff V F mu T C)
      (Vp := Vp)
      component.common_subsequence hCad bad Preg hReg bad' component.regularized
      hVersion⟩

end HorizonFactorialGrid

end FTAPTheorem42
