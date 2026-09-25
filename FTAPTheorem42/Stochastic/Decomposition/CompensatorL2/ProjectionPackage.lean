/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingConvexExpectation
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CandidateOptionalSampling
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.PredictableLimsup
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingLimsupFoundation
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingLimsupEquality
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ProcessBridgeCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableVersionCore

/-!
# Coherent square-integrable projection packages

The rows, convex coefficients, cutoff, càdlàg candidate, regularized version,
and predictable limsup must be selected once and then shared by every later
stopping-time consumer.  This module records that data-level invariant.  The
optional-sampling conclusions remain methods of the package rather than
structure fields, so the package is still a primitive construction witness.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

open SquareIntegrableIncreasingProcessData

/-! ## One component -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorComponentPackage
    (V : Process Ω) (T : NNReal) where
  hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T
  hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
    (F := F) (mu := mu) hV
  hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
    (F := F) (mu := mu) hV hRows
  hResidual : ∀ r,
    SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r
  w : ∀ n, TailConvexWeights n
  y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)
  hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
    hV hRows hControl hResidual w y
  cutoff : Nat → Nat
  hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
    hV hRows hControl hResidual w y hCommon cutoff
  Z : Lp Real 2 mu
  M : Process Ω
  Pcad : Process Ω
  hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
    hV hRows hControl hResidual w y hCommon Z M Pcad
  bad : Set Ω
  Preg : Process Ω
  hReg : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
    hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg
  Ppred : Process Ω
  hLimsup : SquareIntegrableIncreasingProcessPredictableLimsupData
    hV hRows hControl hResidual w y hCommon cutoff hData Z M Pcad hCad
      bad Preg hReg Ppred

/-! A Jordan pair allows independent positive and negative row systems while
keeping each component coherent internally. -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorJordanPackage
    (VPlus VMinus : Process Ω) (T : NNReal) where
  plus : SquareIntegrablePredictableCompensatorComponentPackage
    (F := F) (mu := mu) VPlus T
  minus : SquareIntegrablePredictableCompensatorComponentPackage
    (F := F) (mu := mu) VMinus T

/-! ## Projection-ready data for one fixed component -/

omit [SigmaFiniteFiltration mu F] in
structure SquareIntegrablePredictableCompensatorProjectionReadyData
    {V : Process Ω} {T : NNReal}
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (badPred : Set Ω) (Vp : Process Ω) : Prop where
  predictable_version :
    FactorialGridPredictableCompensatorPredictableVersionData
      (F := F) (mu := mu) (T := T) badPred pkg.Ppred pkg.Preg Vp
  Vp_terminal_memLp_two : MemLp (Vp T) (2 : ENNReal) mu
  Vp_terminal_integrable : Integrable (Vp T) mu
  terminal_row_tendstoAE : TendstoAE mu
      (fun n => squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T) (Vp T)
  terminal_row_L2_bound : ∀ n,
      (∫ omega, (squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T omega) ^ 2 ∂mu) ≤
        8 * ∫ omega, (V T omega) ^ 2 ∂mu
  Vp_indistinguishable_Ppred :
    ProcessIndistinguishable mu Vp pkg.Ppred
  Vp_indistinguishable_Preg :
    ProcessIndistinguishable mu Vp pkg.Preg

/-! ## Projection-ready data for an independent Jordan pair -/

namespace SquareIntegrablePredictableCompensatorComponentPackage

variable {V : Process Ω} {T : NNReal}

/-! ## Package methods -/

omit [SigmaFiniteFiltration mu F] in
theorem stoppingConvexExpectation
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty
      (SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
          pkg.cutoff pkg.hData τ hτ hτT) := by
  exact squareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectation_producer
    (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y
      pkg.hCommon pkg.cutoff pkg.hData τ hτ hτT

omit [SigmaFiniteFiltration mu F] in
theorem candidateOptionalSampling
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    Nonempty
      (SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
          pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg pkg.hReg τ hτ hτT) := by
  exact squareIntegrableIncreasingProcessCandidateOptionalSampling_producer
    (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y
      pkg.hCommon pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg pkg.hReg hτ hτT

omit [SigmaFiniteFiltration mu F] in
theorem stoppingLimsupFoundation
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    ∃ hStop :
        SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
          pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
            pkg.cutoff pkg.hData τ hτ hτT,
      ∃ hCandidate :
          SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
            pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
              pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg pkg.hReg τ hτ hτT,
        Nonempty
          (SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
            pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
              pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
              pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate) := by
  obtain ⟨hStop⟩ := pkg.stoppingConvexExpectation hτ hτT
  obtain ⟨hCandidate⟩ := pkg.candidateOptionalSampling hτ hτT
  refine ⟨hStop, hCandidate, ?_⟩
  exact ⟨squareIntegrablePredictableCompensatorStoppingLimsupFoundation_producer
    (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y
      pkg.hCommon pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
      pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate⟩

omit [SigmaFiniteFiltration mu F] in
theorem stoppingLimsupEquality
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) :
    ∃ hStop :
        SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
          pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
            pkg.cutoff pkg.hData τ hτ hτT,
      ∃ hCandidate :
          SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
            pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
              pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg pkg.hReg τ hτ hτT,
        ∃ hFoundation :
            SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
              pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
                pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
                pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate,
          Nonempty
            (SquareIntegrablePredictableCompensatorStoppingLimsupEqualityData
              pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
                pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
                pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate
                hFoundation) := by
  obtain ⟨hStop, hCandidate, ⟨hFoundation⟩⟩ :=
    pkg.stoppingLimsupFoundation hτ hτT
  obtain ⟨hTerminalCandidate⟩ :=
    pkg.candidateOptionalSampling
      (τ := fun _ : Ω => T) (isStoppingTime_const F T) (fun _ => le_rfl)
  refine ⟨hStop, hCandidate, hFoundation, ?_⟩
  exact ⟨squareIntegrablePredictableCompensatorStoppingLimsupEquality_producer
    (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y
      pkg.hCommon pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
      pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate hTerminalCandidate
      hFoundation⟩

omit [SigmaFiniteFiltration mu F] in
theorem stoppingLimsupEquality_all
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T) :
    ∀ (τ : Ω → NNReal)
      (hτ : IsStoppingTime F (fun omega =>
        (τ omega : WithTop NNReal)))
      (hτT : ∀ omega, τ omega ≤ T),
      ∃ hStop :
          SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
            pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
              pkg.cutoff pkg.hData τ hτ hτT,
        ∃ hCandidate :
            SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
              pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
                pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg pkg.hReg τ hτ hτT,
          ∃ hFoundation :
              SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
                pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
                  pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
                  pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate,
            Nonempty
              (SquareIntegrablePredictableCompensatorStoppingLimsupEqualityData
                pkg.hV pkg.hRows pkg.hControl pkg.hResidual pkg.w pkg.y pkg.hCommon
                  pkg.cutoff pkg.hData pkg.Z pkg.M pkg.Pcad pkg.hCad pkg.bad pkg.Preg
                  pkg.hReg pkg.Ppred pkg.hLimsup τ hτ hτT hStop hCandidate
                  hFoundation) := by
  intro τ hτ hτT
  exact pkg.stoppingLimsupEquality hτ hτT

omit [SigmaFiniteFiltration mu F] in
theorem processIndistinguishable
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    ProcessIndistinguishable mu pkg.Ppred pkg.Preg := by
  apply processIndistinguishable_of_boundedStoppingTime_ae_eq_core
    (T := T) (hRightContinuous := hUsual.rightContinuous)
    (Preg := pkg.Preg) (Ppred := pkg.Ppred)
    (hPregStronglyAdapted := pkg.hReg.Preg_stronglyAdapted)
    (hPregRightContinuous := pkg.hReg.Preg_rightContinuous)
    (hPregLeftLimits := pkg.hReg.Preg_leftLimits)
    (hPregNonnegative := pkg.hReg.Preg_nonnegative)
    (hPregMonotone := pkg.hReg.Preg_monotone)
    (hPregZero := pkg.hReg.Preg_zero)
    (hPregConstantAfter := pkg.hReg.Preg_constant_after)
    (hPpredZero := pkg.hLimsup.Ppred_zero)
    (hPpredConstantAfter := pkg.hLimsup.Ppred_constant_after)
    (hPpredEqPregAtContinuity := pkg.hLimsup.Ppred_eq_Preg_at_continuity)
    (fun τ hτ hτT => by
      obtain ⟨_, _, _, hEquality⟩ := pkg.stoppingLimsupEquality_all τ hτ hτT
      exact hEquality.some.stopped_sample_ae_eq)

/-! The process bridge is consumed only after the component package has fixed
its predictable limsup and regularized candidate. -/

omit [SigmaFiniteFiltration mu F] in
theorem predictableVersion
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ badPred : Set Ω, ∃ Vp : Process Ω,
      FactorialGridPredictableCompensatorPredictableVersionData
        (F := F) (mu := mu) (T := T) badPred pkg.Ppred pkg.Preg Vp := by
  exact exists_predictableCompensatorVersion_of_processBridge
    (F := F) (mu := mu) (T := T)
    pkg.hLimsup.Ppred_isStronglyPredictable pkg.hLimsup.Ppred_zero
    pkg.hReg.Preg_rightContinuous pkg.hReg.Preg_leftLimits
    pkg.hReg.Preg_nonnegative pkg.hReg.Preg_monotone
    pkg.hReg.Preg_constant_after (pkg.processIndistinguishable hUsual) hUsual

/-! The terminal row limit is obtained from the existing stopping-limsup
foundation at the deterministic stopping time `T`; no new rows, weights, or
subsequence is selected here. -/

omit [SigmaFiniteFiltration mu F] in
theorem projectionReady
    (pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ badPred : Set Ω, ∃ Vp : Process Ω,
      SquareIntegrablePredictableCompensatorProjectionReadyData
        pkg badPred Vp := by
  obtain ⟨badPred, Vp, hVersion⟩ := pkg.predictableVersion hUsual
  obtain ⟨_, _, ⟨hFoundation⟩⟩ :=
    pkg.stoppingLimsupFoundation
      (τ := fun _ : Ω => T) (isStoppingTime_const F T)
      (fun _ => le_rfl)
  have hVpMem : MemLp (Vp T) (2 : ENNReal) mu := by
    apply (memLp_congr_ae
      (hVersion.Vp_indistinguishable_Preg.eventuallyEq_at T)).mpr
    exact hFoundation.Preg_terminal_memLp_two
  have hRowsPreg : TendstoAE mu
      (fun n => squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T) (pkg.Preg T) := by
    simpa only [squareIntegrableCompensatorConvexRow] using
      hFoundation.terminal_row_tendstoAE
  have hRowsVp : TendstoAE mu
      (fun n => squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T) (Vp T) := by
    filter_upwards [hRowsPreg,
      hVersion.Vp_indistinguishable_Preg.eventuallyEq_at T] with omega hRows hEq
    simpa only [hEq] using hRows
  have hRowsBound : ∀ n,
      (∫ omega, (squareIntegrableCompensatorConvexRow
        pkg.hV pkg.hRows pkg.hControl pkg.hResidual
        (pkg.w (pkg.cutoff n)) T omega) ^ 2 ∂mu) ≤
        8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
    intro n
    exact squareIntegrableCompensatorConvexRow_terminal_L2_bound
      (F := F) (mu := mu) pkg.hV pkg.hRows pkg.hControl pkg.hResidual
      (pkg.w (pkg.cutoff n))
  refine ⟨badPred, Vp, {
    predictable_version := hVersion
    Vp_terminal_memLp_two := hVpMem
    Vp_terminal_integrable := hVpMem.integrable (by norm_num)
    terminal_row_tendstoAE := hRowsVp
    terminal_row_L2_bound := hRowsBound
    Vp_indistinguishable_Ppred := hVersion.Vp_indistinguishable_Ppred
    Vp_indistinguishable_Preg := hVersion.Vp_indistinguishable_Preg }⟩

end SquareIntegrablePredictableCompensatorComponentPackage

/-! ## Package construction from the common stopped Jordan data -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrablePredictableCompensatorJordanPackage_of_commonStopJordanComponents
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
    Nonempty
      (SquareIntegrablePredictableCompensatorJordanPackage
        (F := F) (mu := mu) Aplus Aminus T) := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, cutoffPlus, hDataPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
      badPlus, PregPlus, hRegPlus, hMinus, hRowsMinus, hControlMinus,
      hResidualMinus, wMinus, yMinus, hCommonMinus, cutoffMinus, hDataMinus,
      ZMinus, MMinus, PcadMinus, hCadMinus, badMinus, PregMinus, hRegMinus⟩ :=
    exists_squareIntegrableMonotoneRegularizedCadlagCandidates_of_commonStopJordanComponents
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨PpredPlus, hLimsupPlus, PpredMinus, hLimsupMinus⟩ :=
    exists_squareIntegrablePredictableLimsups_of_monotoneRegularizedCadlagCandidates
      hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        cutoffPlus hDataPlus ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus hRegPlus
      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
        cutoffMinus hDataMinus ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus hRegMinus
  exact ⟨{
    plus := {
      hV := hPlus
      hRows := hRowsPlus
      hControl := hControlPlus
      hResidual := hResidualPlus
      w := wPlus
      y := yPlus
      hCommon := hCommonPlus
      cutoff := cutoffPlus
      hData := hDataPlus
      Z := ZPlus
      M := MPlus
      Pcad := PcadPlus
      hCad := hCadPlus
      bad := badPlus
      Preg := PregPlus
      hReg := hRegPlus
      Ppred := PpredPlus
      hLimsup := hLimsupPlus }
    minus := {
      hV := hMinus
      hRows := hRowsMinus
      hControl := hControlMinus
      hResidual := hResidualMinus
      w := wMinus
      y := yMinus
      hCommon := hCommonMinus
      cutoff := cutoffMinus
      hData := hDataMinus
      Z := ZMinus
      M := MMinus
      Pcad := PcadMinus
      hCad := hCadMinus
      bad := badMinus
      Preg := PregMinus
      hReg := hRegMinus
      Ppred := PpredMinus
      hLimsup := hLimsupMinus }}⟩

end HorizonFactorialGrid

end FTAPTheorem42
