/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ResidualMartingale
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.RowControl

/-!
# Finite-grid residual martingales for `L²` increasing processes

The sampled residual of a square-integrable increasing-process row is a
genuine discrete martingale.  Its terminal value is square integrable, and
every earlier sampled value is the conditional expectation of that terminal
value.  The discrete martingale argument is shared with the bounded route;
only the row-specific `L²` membership and conditional-expectation law are
provided here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

namespace SquareIntegrableIncreasingProcessData

/-! ## The sampled residual -/

noncomputable def squareIntegrableFactorialGridSampledResidual
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r : Nat) : Nat → Ω → Real :=
  fun i omega =>
    V ((grid T r).sampledTime i) omega -
      squareIntegrablePredictableCompensatorProcess V F mu T r
        ((grid T r).sampledTime i) omega

@[simp] theorem squareIntegrableFactorialGridSampledResidual_apply
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T : NNReal) (r i : Nat) (omega : Ω) :
    squareIntegrableFactorialGridSampledResidual V F mu T r i omega =
      V ((grid T r).sampledTime i) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime i) omega :=
  rfl

omit [IsProbabilityMeasure mu] in
theorem squareIntegrableFactorialGridSampledResidual_terminal_eq
    (r : Nat) :
    squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) =
      fun omega => V T omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r T omega := by
  funext omega
  simp [squareIntegrableFactorialGridSampledResidual, sampledTime_size]

/-! ## Integrability and adaptedness -/

theorem squareIntegrableFactorialGridSampledResidual_value_memLp_two
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r i : Nat) :
    MemLp (squareIntegrableFactorialGridSampledResidual V F mu T r i)
      (2 : ENNReal) mu := by
  have hTime : (grid T r).sampledTime i ≤ T :=
    sampledTime_le_horizon (T := T) r i
  have hVmem : MemLp (V ((grid T r).sampledTime i))
      (2 : ENNReal) mu := hV.value_memLp_two hTime
  have hPmem : MemLp
      (squareIntegrablePredictableCompensatorProcess V F mu T r
        ((grid T r).sampledTime i)) (2 : ENNReal) mu :=
    hControl.value_memLp_two r ((grid T r).sampledTime i)
  change MemLp
    (fun omega => V ((grid T r).sampledTime i) omega -
      squareIntegrablePredictableCompensatorProcess V F mu T r
        ((grid T r).sampledTime i) omega) (2 : ENNReal) mu
  exact hVmem.sub hPmem

theorem squareIntegrableFactorialGridSampledResidual_stronglyAdapted
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) (r : Nat) :
    StronglyAdapted ((grid T r).sampledFiltration F)
      (squareIntegrableFactorialGridSampledResidual V F mu T r) := by
  intro i
  change StronglyMeasurable[F ((grid T r).sampledTime i)]
    (fun omega => V ((grid T r).sampledTime i) omega -
      squareIntegrablePredictableCompensatorProcess V F mu T r
        ((grid T r).sampledTime i) omega)
  exact ((hV.stronglyAdapted ((grid T r).sampledTime i)).sub
    ((hRows.process_predictable r).stronglyAdapted
      ((grid T r).sampledTime i)))

/-! ## Discrete martingale law -/

theorem squareIntegrableFactorialGridSampledResidual_condExp_sub_eq_zero
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV) (r i : Nat) :
    mu[squareIntegrableFactorialGridSampledResidual V F mu T r (i + 1) -
      squareIntegrableFactorialGridSampledResidual V F mu T r i |
        (grid T r).sampledFiltration F i] =ᵐ[mu] 0 := by
  by_cases hi : i < size T r
  · change mu[(fun omega =>
      (V ((grid T r).sampledTime (i + 1)) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime i) omega)) |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0
    exact hRows.residual_grid_condExp_law r i hi
  · have hNi : size T r ≤ i := Nat.le_of_not_gt hi
    have hTi : (grid T r).sampledTime i = T :=
      sampledTime_eq_terminal_of_le (T := T) r i hNi
    have hTi1 : (grid T r).sampledTime (i + 1) = T :=
      sampledTime_eq_terminal_of_le (T := T) r (i + 1)
        (hNi.trans (Nat.le_succ i))
    have hres :
        squareIntegrableFactorialGridSampledResidual V F mu T r (i + 1) =
          squareIntegrableFactorialGridSampledResidual V F mu T r i := by
      funext omega
      simp [squareIntegrableFactorialGridSampledResidual, hTi, hTi1]
    rw [hres]
    simp

theorem squareIntegrableFactorialGridSampledResidual_isMartingale
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) :
    Martingale (squareIntegrableFactorialGridSampledResidual V F mu T r)
      ((grid T r).sampledFiltration F) mu := by
  apply sampledResidual_isMartingale_of_condExp_sub_eq_zero
    (squareIntegrableFactorialGridSampledResidual_stronglyAdapted
      (F := F) (mu := mu) hV hRows r)
  · intro i
    exact squareIntegrableFactorialGridSampledResidual_value_memLp_two
      (F := F) (mu := mu) hV hRows hControl r i
  · intro i
    exact squareIntegrableFactorialGridSampledResidual_condExp_sub_eq_zero
      (F := F) (mu := mu) hV hRows r i

/-! ## Terminal conditional-expectation representation -/

theorem squareIntegrableFactorialGridSampledResidual_eq_condExp_terminal
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (r i : Nat) (hi : i ≤ size T r) :
    squareIntegrableFactorialGridSampledResidual V F mu T r i =ᵐ[mu]
      mu[squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) |
        (grid T r).sampledFiltration F i] := by
  exact sampledResidual_eq_condExp_terminal_of_martingale
    (squareIntegrableFactorialGridSampledResidual_isMartingale
      (F := F) (mu := mu) hV hRows hControl r) hi

/-! ## Public certificate -/

structure SquareIntegrableFactorialGridSampledResidualMartingaleData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) where
  stronglyAdapted : StronglyAdapted ((grid T r).sampledFiltration F)
    (squareIntegrableFactorialGridSampledResidual V F mu T r)
  value_memLp_two : ∀ i,
    MemLp (squareIntegrableFactorialGridSampledResidual V F mu T r i)
      (2 : ENNReal) mu
  value_integrable : ∀ i,
    Integrable (squareIntegrableFactorialGridSampledResidual V F mu T r i) mu
  martingale : Martingale (squareIntegrableFactorialGridSampledResidual V F mu T r)
    ((grid T r).sampledFiltration F) mu
  terminal_condExp : ∀ i, i ≤ size T r →
    squareIntegrableFactorialGridSampledResidual V F mu T r i =ᵐ[mu]
      mu[squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) |
        (grid T r).sampledFiltration F i]
  terminal_memLp_two :
    MemLp (squareIntegrableFactorialGridSampledResidual V F mu T r (size T r))
      (2 : ENNReal) mu
  terminal_eq :
    squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) =
      fun omega => V T omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r T omega

theorem squareIntegrableFactorialGridSampledResidualMartingale_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) :
    Nonempty (SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r) := by
  let hAdapted := squareIntegrableFactorialGridSampledResidual_stronglyAdapted
    (F := F) (mu := mu) hV hRows r
  let hMem := squareIntegrableFactorialGridSampledResidual_value_memLp_two
    (F := F) (mu := mu) hV hRows hControl r
  let hMart := squareIntegrableFactorialGridSampledResidual_isMartingale
    (F := F) (mu := mu) hV hRows hControl r
  refine ⟨{
    stronglyAdapted := hAdapted
    value_memLp_two := hMem
    value_integrable := fun i => (hMem i).integrable (by norm_num)
    martingale := hMart
    terminal_condExp := fun i hi =>
      squareIntegrableFactorialGridSampledResidual_eq_condExp_terminal
        (F := F) (mu := mu) hV hRows hControl r i hi
    terminal_memLp_two := hMem (size T r)
    terminal_eq := squareIntegrableFactorialGridSampledResidual_terminal_eq
      (F := F) (mu := mu) (V := V) (T := T) r }⟩

theorem exists_squareIntegrableFactorialGridSampledResidualMartingale
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows) (r : Nat) :
    Nonempty (SquareIntegrableFactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows hControl r) :=
  squareIntegrableFactorialGridSampledResidualMartingale_producer
    (F := F) (mu := mu) hV hRows hControl r

/-! The regularized common-stop Jordan components are consumed directly. -/

theorem exists_squareIntegrableFactorialGridSampledResidualMartingales_of_commonStopJordanComponents
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
      ∃ hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T,
        ∃ hRowsPlus : SquareIntegrableIncreasingProcessCompensatorRowsData
            (F := F) (mu := mu) hPlus,
          ∃ hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
              (F := F) (mu := mu) hMinus,
            ∃ hControlPlus : SquareIntegrableIncreasingProcessCompensatorRowControlData
                (F := F) (mu := mu) hPlus hRowsPlus,
              ∃ hControlMinus : SquareIntegrableIncreasingProcessCompensatorRowControlData
                  (F := F) (mu := mu) hMinus hRowsMinus,
                ∀ r, Nonempty
                    (SquareIntegrableFactorialGridSampledResidualMartingaleData
                      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus r) ∧
                  Nonempty
                    (SquareIntegrableFactorialGridSampledResidualMartingaleData
                      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r) := by
  obtain ⟨hPlus, hMinus, hRowsPlus, hRowsMinus, hControlPlus, hControlMinus⟩ :=
    exists_squareIntegrableIncreasingProcessCompensatorRowControls_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  rcases hControlPlus with ⟨hControlPlus⟩
  rcases hControlMinus with ⟨hControlMinus⟩
  refine ⟨hPlus, hMinus, hRowsPlus, hRowsMinus, hControlPlus, hControlMinus, ?_⟩
  intro r
  exact ⟨squareIntegrableFactorialGridSampledResidualMartingale_producer
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus r,
    squareIntegrableFactorialGridSampledResidualMartingale_producer
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r⟩

end SquareIntegrableIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
