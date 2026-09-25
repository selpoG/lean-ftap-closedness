/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.Probability.Martingale.Basic
import FTAPTheorem42.Stochastic.Decomposition.Compensator.Rows

/-!
# Source-independent finite-grid residual martingale core

Both compensator constructions package a sampled residual by the same
discrete-time argument.  The source-specific work is only the conditional
expectation identity and the `L²` membership of each sampled value.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {mu : Measure Ω} [IsFiniteMeasure mu]
  {ℱ : Filtration Nat (inferInstance : MeasurableSpace Ω)}
  {R : Nat → Ω → Real}

theorem sampledResidual_isMartingale_of_condExp_sub_eq_zero
    (hAdapted : StronglyAdapted ℱ R)
    (hMem : ∀ i, MemLp (R i) (2 : ENNReal) mu)
    (hCond : ∀ i, mu[R (i + 1) - R i | ℱ i] =ᵐ[mu] 0) :
    Martingale R ℱ mu := by
  apply martingale_of_condExp_sub_eq_zero_nat hAdapted
  · intro i
    exact (hMem i).integrable (by norm_num)
  · exact hCond

omit [IsFiniteMeasure mu] in
theorem sampledResidual_eq_condExp_terminal_of_martingale
    (hMart : Martingale R ℱ mu)
    {N i : Nat} (hi : i ≤ N) :
    R i =ᵐ[mu] mu[R N | ℱ i] := by
  exact (hMart.condExp_ae_eq hi).symm

end HorizonFactorialGrid

/-!
## Finite-grid residual martingales

The predictable compensator rows are left-endpoint step processes.  This section
packages their sampled residuals as genuine discrete-time martingales.  The
conditional-expectation law on every nontrivial grid block is consumed
directly from the row certificate; after the final index the chronological
grid is clamped at `T`, so the residual is constant and its conditional
expectation law is trivial.  No continuous-time martingale or predictable
version is asserted here.
-/

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

namespace BoundedIncreasingProcessData

/-! ## The sampled residual -/

/-- The residual sampled at the constantly extended level-`r` grid. -/
noncomputable def factorialGridSampledResidual
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r : Nat) : Nat → Ω → Real :=
  fun i omega =>
    V ((grid T r).sampledTime i) omega -
      predictableCompensatorProcess V F mu T C r
        ((grid T r).sampledTime i) omega

@[simp] theorem factorialGridSampledResidual_apply
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r i : Nat) (omega : Ω) :
    factorialGridSampledResidual V F mu T C r i omega =
      V ((grid T r).sampledTime i) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega :=
  rfl

omit [IsProbabilityMeasure mu] in
theorem factorialGridSampledResidual_terminal_eq
    (r : Nat) :
    factorialGridSampledResidual V F mu T C r (size T r) =
      fun omega => V T omega -
        predictableCompensatorProcess V F mu T C r T omega := by
  funext omega
  simp [factorialGridSampledResidual, sampledTime_size]

/-! ## Integrability and adaptedness -/

theorem factorialGridSampledResidual_value_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (r i : Nat) :
    MemLp (factorialGridSampledResidual V F mu T C r i)
      (2 : ENNReal) mu := by
  have hTime : (grid T r).sampledTime i ≤ T :=
    sampledTime_le_horizon (T := T) r i
  have hVmem : MemLp (V ((grid T r).sampledTime i))
      (2 : ENNReal) mu :=
    hV.value_memLp_two (mu := mu) hTime
  have hPmeas : AEStronglyMeasurable
      (predictableCompensatorProcess V F mu T C r
        ((grid T r).sampledTime i)) mu :=
    ((hRows.process_predictable r).stronglyAdapted
      ((grid T r).sampledTime i)).mono
        (F.le ((grid T r).sampledTime i)) |>.aestronglyMeasurable
  have hPterminal : MemLp
      (predictableCompensatorProcess V F mu T C r T)
      (2 : ENNReal) mu := hRows.terminal_memLp_two r
  have hPbound : ∀ᵐ omega ∂mu,
      ‖predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega‖ ≤
        ‖predictableCompensatorProcess V F mu T C r T omega‖ := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hRows.process_nonneg r
        ((grid T r).sampledTime i) omega),
      Real.norm_eq_abs, abs_of_nonneg
        (hRows.process_nonneg r T omega)]
    exact hRows.process_mono r omega
      (sampledTime_le_horizon (T := T) r i)
  have hPmem : MemLp
      (predictableCompensatorProcess V F mu T C r
        ((grid T r).sampledTime i)) (2 : ENNReal) mu :=
    MemLp.of_le hPterminal hPmeas hPbound
  change MemLp
    (fun omega => V ((grid T r).sampledTime i) omega -
      predictableCompensatorProcess V F mu T C r
        ((grid T r).sampledTime i) omega) (2 : ENNReal) mu
  exact hVmem.sub hPmem

omit [IsProbabilityMeasure mu] in
theorem factorialGridSampledResidual_stronglyAdapted
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r : Nat) :
    StronglyAdapted ((grid T r).sampledFiltration F)
      (factorialGridSampledResidual V F mu T C r) := by
  intro i
  change StronglyMeasurable[F ((grid T r).sampledTime i)]
    (fun omega => V ((grid T r).sampledTime i) omega -
      predictableCompensatorProcess V F mu T C r
        ((grid T r).sampledTime i) omega)
  exact ((hV.stronglyAdapted ((grid T r).sampledTime i)).sub
    ((hRows.process_predictable r).stronglyAdapted
      ((grid T r).sampledTime i)))

/-! ## Discrete martingale law -/

omit [IsProbabilityMeasure mu] in
theorem factorialGridSampledResidual_condExp_sub_eq_zero
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r i : Nat) :
    mu[factorialGridSampledResidual V F mu T C r (i + 1) -
      factorialGridSampledResidual V F mu T C r i |
        (grid T r).sampledFiltration F i] =ᵐ[mu] 0 := by
  by_cases hi : i < size T r
  · change mu[(fun omega =>
      (V ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        predictableCompensatorProcess V F mu T C r
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
        factorialGridSampledResidual V F mu T C r (i + 1) =
          factorialGridSampledResidual V F mu T C r i := by
      funext omega
      simp [factorialGridSampledResidual, hTi, hTi1]
    rw [hres]
    simp

theorem factorialGridSampledResidual_isMartingale
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r : Nat) :
    Martingale (factorialGridSampledResidual V F mu T C r)
      ((grid T r).sampledFiltration F) mu := by
  apply sampledResidual_isMartingale_of_condExp_sub_eq_zero
    (factorialGridSampledResidual_stronglyAdapted
      (F := F) (mu := mu) hV hRows r)
  · intro i
    exact factorialGridSampledResidual_value_memLp_two
      (F := F) (mu := mu) hV hRows r i
  · intro i
    exact factorialGridSampledResidual_condExp_sub_eq_zero
      (F := F) (mu := mu) hV hRows r i

/-! ## Terminal conditional-expectation representation -/

theorem factorialGridSampledResidual_eq_condExp_terminal
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r i : Nat) (hi : i ≤ size T r) :
    factorialGridSampledResidual V F mu T C r i =ᵐ[mu]
      mu[factorialGridSampledResidual V F mu T C r (size T r) |
        (grid T r).sampledFiltration F i] := by
  exact sampledResidual_eq_condExp_terminal_of_martingale
    (factorialGridSampledResidual_isMartingale
      (F := F) (mu := mu) hV hRows r) hi

/-! ## Public 7A certificate -/

structure FactorialGridSampledResidualMartingaleData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r : Nat) where
  stronglyAdapted : StronglyAdapted ((grid T r).sampledFiltration F)
    (factorialGridSampledResidual V F mu T C r)
  value_memLp_two : ∀ i,
    MemLp (factorialGridSampledResidual V F mu T C r i)
      (2 : ENNReal) mu
  value_integrable : ∀ i,
    Integrable (factorialGridSampledResidual V F mu T C r i) mu
  martingale : Martingale (factorialGridSampledResidual V F mu T C r)
    ((grid T r).sampledFiltration F) mu
  terminal_condExp : ∀ i, i ≤ size T r →
    factorialGridSampledResidual V F mu T C r i =ᵐ[mu]
      mu[factorialGridSampledResidual V F mu T C r (size T r) |
        (grid T r).sampledFiltration F i]
  terminal_eq : factorialGridSampledResidual V F mu T C r (size T r) =
    fun omega => V T omega -
      predictableCompensatorProcess V F mu T C r T omega

theorem factorialGridSampledResidualMartingale_producer
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) (r : Nat) :
    Nonempty (FactorialGridSampledResidualMartingaleData
      (F := F) (mu := mu) hV hRows r) := by
  let hAdapted := factorialGridSampledResidual_stronglyAdapted
    (F := F) (mu := mu) hV hRows r
  let hMart := factorialGridSampledResidual_isMartingale
    (F := F) (mu := mu) hV hRows r
  refine ⟨{
    stronglyAdapted := hAdapted
    value_memLp_two := factorialGridSampledResidual_value_memLp_two
      (F := F) (mu := mu) hV hRows r
    value_integrable := fun i =>
      (factorialGridSampledResidual_value_memLp_two
        (F := F) (mu := mu) hV hRows r i).integrable (by norm_num)
    martingale := hMart
    terminal_condExp := fun i hi =>
      factorialGridSampledResidual_eq_condExp_terminal
        (F := F) (mu := mu) hV hRows r i hi
    terminal_eq := factorialGridSampledResidual_terminal_eq
      (F := F) (mu := mu) r }⟩

end BoundedIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
