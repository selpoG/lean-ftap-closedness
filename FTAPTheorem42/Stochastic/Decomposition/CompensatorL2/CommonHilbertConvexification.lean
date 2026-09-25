/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexificationCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.ResidualMartingale

/-!
# Common Hilbert convexification for the square-integrable rows

The square-integrable compensator rows have no deterministic pathwise source
bound.  This adapter supplies the source-independent Hilbert core with
`J = sqrt (integral (V T)^2)` for the terminal coordinate and
`K = sqrt (8 * integral (V T)^2)` for every row coordinate.  The same
`TailConvexWeights` are therefore used for the terminal residual and all
stopped-limit-skeleton values.

Only the finite-grid raw rows and their `L²` certificates are produced here.
Predictable limsups, process bridges, optional sampling, and projection are
deliberately outside this module.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

open SquareIntegrableIncreasingProcessData
open CommonHilbertRowsData

/-! ## The two deterministic `L²` bounds -/

noncomputable def squareIntegrableSourceL2Bound
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) : Real :=
  Real.sqrt (∫ omega, (V T omega) ^ 2 ∂mu)

noncomputable def squareIntegrableRowL2Bound
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) : Real :=
  Real.sqrt (8 * ∫ omega, (V T omega) ^ 2 ∂mu)

theorem squareIntegrableSourceL2Bound_nonneg
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    0 ≤ squareIntegrableSourceL2Bound (F := F) (mu := mu) hV := by
  exact Real.sqrt_nonneg _

theorem squareIntegrableRowL2Bound_nonneg
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    0 ≤ squareIntegrableRowL2Bound (F := F) (mu := mu) hV := by
  exact Real.sqrt_nonneg _

private theorem source_integral_nonneg
    (_hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    0 ≤ ∫ omega, (V T omega) ^ 2 ∂mu := by
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun omega => sq_nonneg (V T omega))

/-! ## Canonical coordinates and the source-independent input -/

noncomputable def squareIntegrableCompensatorRowValueToLp
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) (t : NNReal) : Lp Real (2 : ENNReal) mu :=
  (hControl.value_memLp_two r t).toLp
    (squareIntegrablePredictableCompensatorProcess V F mu T r t)

noncomputable def squareIntegrableTerminalResidualToLp
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) : Lp Real (2 : ENNReal) mu :=
  (hV.terminal_memLp_two.toLp (V T)) -
    (hControl.value_memLp_two r T).toLp
      (squareIntegrablePredictableCompensatorProcess V F mu T r T)

noncomputable def squareIntegrableCommonCoordinateBound
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (i : Nat) : Real :=
  match i with
  | 0 => squareIntegrableSourceL2Bound (F := F) (mu := mu) hV +
      squareIntegrableRowL2Bound (F := F) (mu := mu) hV
  | _ => squareIntegrableRowL2Bound (F := F) (mu := mu) hV

theorem squareIntegrableCompensatorRowValueToLp_coeFn_ae
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r : Nat) (t : NNReal) :
    ⇑(squareIntegrableCompensatorRowValueToLp hV hRows hControl r t) =ᵐ[mu]
      squareIntegrablePredictableCompensatorProcess V F mu T r t := by
  exact MemLp.coeFn_toLp (hControl.value_memLp_two r t)

theorem squareIntegrableTerminalResidualToLp_coeFn_ae
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (r : Nat) :
    ⇑(squareIntegrableTerminalResidualToLp hV hRows hControl r) =ᵐ[mu]
      squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) := by
  have hVae := MemLp.coeFn_toLp hV.terminal_memLp_two
  have hPmem := hControl.value_memLp_two r T
  have hPae := MemLp.coeFn_toLp hPmem
  have hSub := Lp.coeFn_sub hV.terminal_memLp_two.toLp (hPmem.toLp
    (squareIntegrablePredictableCompensatorProcess V F mu T r T))
  have hTerminal := (hResidual r).terminal_eq
  change ⇑(hV.terminal_memLp_two.toLp (V T) - hPmem.toLp
      (squareIntegrablePredictableCompensatorProcess V F mu T r T)) =ᵐ[mu]
    squareIntegrableFactorialGridSampledResidual V F mu T r (size T r)
  filter_upwards [hSub, hVae, hPae] with omega hsub hv hp
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hv, hp]
  exact congrFun hTerminal.symm omega

private theorem squareIntegrableSourceToLp_norm_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    ‖hV.terminal_memLp_two.toLp (V T)‖ ≤
      squareIntegrableSourceL2Bound (F := F) (mu := mu) hV := by
  rw [Lp.norm_toLp]
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hV.terminal_memLp_two]
  apply Real.sqrt_le_sqrt
  exact le_of_eq (integral_congr_ae
    (Filter.Eventually.of_forall (fun omega => by
      change ‖V T omega‖ ^ 2 = (V T omega) ^ 2
      rw [Real.norm_eq_abs, sq_abs])))

theorem squareIntegrableCompensatorRowValueToLp_norm_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) (t : NNReal) :
    ‖squareIntegrableCompensatorRowValueToLp hV hRows hControl r t‖ ≤
      squareIntegrableRowL2Bound (F := F) (mu := mu) hV := by
  rw [squareIntegrableCompensatorRowValueToLp, Lp.norm_toLp]
  exact hControl.value_eLpNorm_toReal_le r t

theorem squareIntegrableTerminalResidualToLp_norm_le
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) :
    ‖squareIntegrableTerminalResidualToLp hV hRows hControl r‖ ≤
      squareIntegrableCommonCoordinateBound (F := F) (mu := mu) hV 0 := by
  have hVnorm := squareIntegrableSourceToLp_norm_le (F := F) (mu := mu) hV
  have hPnorm := squareIntegrableCompensatorRowValueToLp_norm_le
    (F := F) (mu := mu) hV hRows hControl r T
  dsimp [squareIntegrableTerminalResidualToLp,
    squareIntegrableCommonCoordinateBound]
  exact (norm_sub_le _ _).trans (add_le_add hVnorm hPnorm)

/-! ## The source-independent input instance -/

noncomputable def squareIntegrableCommonHilbertRowsData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r) :
    CommonHilbertRowsData F mu T (V T)
      (fun r => squareIntegrablePredictableCompensatorProcess V F mu T r)
      (fun r => squareIntegrableFactorialGridSampledResidual V F mu T r
        (size T r))
      (squareIntegrableSourceL2Bound (F := F) (mu := mu) hV)
      (squareIntegrableRowL2Bound (F := F) (mu := mu) hV) := {
  sourceToLp := hV.terminal_memLp_two.toLp (V T)
  rowToLp := fun r t => squareIntegrableCompensatorRowValueToLp
    hV hRows hControl r t
  residualToLp := fun r => squareIntegrableTerminalResidualToLp hV hRows hControl r
  sourceToLp_coeFn_ae := MemLp.coeFn_toLp hV.terminal_memLp_two
  rowToLp_coeFn_ae := fun r t => squareIntegrableCompensatorRowValueToLp_coeFn_ae
    hV hRows hControl r t
  residualToLp_coeFn_ae := fun r => squareIntegrableTerminalResidualToLp_coeFn_ae
    hV hRows hControl hResidual r
  sourceBound_nonneg := squareIntegrableSourceL2Bound_nonneg (F := F) (mu := mu) hV
  rowBound_nonneg := squareIntegrableRowL2Bound_nonneg (F := F) (mu := mu) hV
  sourceToLp_norm_le := squareIntegrableSourceToLp_norm_le (F := F) (mu := mu) hV
  rowToLp_norm_le := fun r t => squareIntegrableCompensatorRowValueToLp_norm_le
    hV hRows hControl r t
  residualToLp_norm_le := fun r => squareIntegrableTerminalResidualToLp_norm_le
    hV hRows hControl r
  row_value_memLp_two := fun r t => hControl.value_memLp_two r t
  residual_memLp_two := fun r => (hResidual r).terminal_memLp_two
  row_isStronglyPredictable := fun r => hRows.process_predictable r
  row_zero := fun r => hRows.process_zero r
  row_nonnegative := fun r t omega => hRows.process_nonneg r t omega
  row_mono := fun r omega => hRows.process_mono r omega
  row_leftContinuous := fun r omega t => hControl.leftContinuous r omega t
  row_constant_after := fun r omega t ht => hRows.process_constant_after r omega t ht
  row_terminal_L2_bound := fun r => by
    have hI := source_integral_nonneg (F := F) (mu := mu) hV
    have hKsq : (squareIntegrableRowL2Bound (F := F) (mu := mu) hV) ^ 2 =
        8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
      dsimp [squareIntegrableRowL2Bound]
      rw [Real.sq_sqrt]
      exact mul_nonneg (by norm_num) hI
    rw [hKsq]
    exact hRows.terminal_L2_bound r
  , row_terminal_expectation := fun r => hRows.terminal_expectation r
  , residual_eq_source_sub_row := fun r => by
    exact (hResidual r).terminal_eq
}

/-! ## Raw convex rows and the shared weight sequence -/

noncomputable def squareIntegrableCompensatorConvexRow
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) : Process Ω :=
  (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual).convexRow w

noncomputable def squareIntegrableCompensatorConvexCoordinateToLp
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) (j : Nat) : Lp Real (2 : ENNReal) mu :=
  (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual).convexCoordinateToLp w j

noncomputable def squareIntegrableResidualConvexCoordinateToLp
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) : Lp Real (2 : ENNReal) mu :=
  (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual).residualConvexCoordinateToLp w

abbrev SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)) : Prop :=
  CommonHilbertRowsData.CommonHilbertConvexificationData
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w y

theorem squareIntegrableIncreasingProcessCommonHilbertConvexification_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)),
      SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
        hV hRows hControl hResidual w y := by
  exact CommonHilbertRowsData.commonHilbertConvexification_producer
    (h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)

/-! ## Raw-row certificates supplied by the generic package -/

theorem squareIntegrableCompensatorConvexCoordinateToLp_coeFn_ae
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) (j : Nat) :
    ⇑(squareIntegrableCompensatorConvexCoordinateToLp
      hV hRows hControl hResidual w j) =ᵐ[mu]
      squareIntegrableCompensatorConvexRow hV hRows hControl hResidual w
        (stoppedLimitSkeleton T j).1 := by
  exact CommonHilbertRowsData.convexCoordinateToLp_coeFn_ae
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w j

theorem squareIntegrableCompensatorConvexRow_terminal_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) :
    MemLp
      (squareIntegrableCompensatorConvexRow hV hRows hControl hResidual w T)
      (2 : ENNReal) mu := by
  exact CommonHilbertRowsData.convexRow_value_memLp_two
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w T

theorem squareIntegrableCompensatorConvexRow_terminal_L2_bound
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : TailConvexWeights n) :
    (∫ omega,
      (squareIntegrableCompensatorConvexRow hV hRows hControl hResidual w T omega) ^ 2 ∂mu) ≤
      8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
  have hI := source_integral_nonneg (F := F) (mu := mu) hV
  have hKsq : (squareIntegrableRowL2Bound (F := F) (mu := mu) hV) ^ 2 =
      8 * ∫ omega, (V T omega) ^ 2 ∂mu := by
    dsimp [squareIntegrableRowL2Bound]
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hI
  have hBound := CommonHilbertRowsData.convexRow_terminal_L2_bound
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w
  rw [hKsq] at hBound
  exact hBound

/-! The regularized Jordan components are direct consumers of the L²
finite-grid rows and of the single source-independent Hilbert producer. -/

theorem exists_squareIntegrableCommonHilbertConvexifications_of_commonStopJordanComponents
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
      ∃ hRowsPlus : SquareIntegrableIncreasingProcessCompensatorRowsData
          (F := F) (mu := mu) hPlus,
        ∃ hControlPlus : SquareIntegrableIncreasingProcessCompensatorRowControlData
            (F := F) (mu := mu) hPlus hRowsPlus,
          ∃ hResidualPlus : ∀ r,
              SquareIntegrableFactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hPlus hRowsPlus hControlPlus r,
            ∃ (wPlus : ∀ n, TailConvexWeights n)
              (yPlus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
                  hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus ∧
    ∃ hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T,
      ∃ hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
          (F := F) (mu := mu) hMinus,
        ∃ hControlMinus : SquareIntegrableIncreasingProcessCompensatorRowControlData
            (F := F) (mu := mu) hMinus hRowsMinus,
          ∃ hResidualMinus : ∀ r,
              SquareIntegrableFactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r,
            ∃ (wMinus : ∀ n, TailConvexWeights n)
              (yMinus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
                hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus := by
  obtain ⟨hPlus, hMinus, hRowsPlus, hRowsMinus, hControlPlus, hControlMinus,
      hResiduals⟩ :=
    exists_squareIntegrableFactorialGridSampledResidualMartingales_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  let hResidualPlus : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hPlus hRowsPlus hControlPlus r := fun r =>
    Classical.choice (hResiduals r).1
  let hResidualMinus : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r := fun r =>
    Classical.choice (hResiduals r).2
  obtain ⟨wPlus, yPlus, hPlusData⟩ :=
    squareIntegrableIncreasingProcessCommonHilbertConvexification_producer
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus
  obtain ⟨wMinus, yMinus, hMinusData⟩ :=
    squareIntegrableIncreasingProcessCommonHilbertConvexification_producer
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus, hPlusData,
    hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus, hMinusData⟩

end HorizonFactorialGrid

end FTAPTheorem42
