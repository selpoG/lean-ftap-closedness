/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.PredictableIndicatorRing
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization

/-!
# The unit source graph in the intrinsic local-completed carrier

An exhaustive completed schedule for a zero-based source already realizes
every positive deterministic stop of its unit-integrand graph.  At a fixed
schedule coordinate the coefficient is the elementary horizon block
`1_(0,T]`.  Elementary/completed agreement identifies its completed gain,
while the schedule's source-prefix identity and the zero initial gain identify
that elementary gain with the doubly stopped source.

This supplies an actual local source for the intrinsic carrier; it does not
assume source actuality as an additional capability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

attribute [local instance] Classical.propDecidable

open FiniteHorizonPredictableIndicatorRing
open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The one-block elementary coefficient `1_(0,T]`. -/
noncomputable def unitHorizonElementaryStrategy (T : NNReal) :
    PredictableElementaryStrategy F :=
  [BoundedIndicatorRepresentation.horizonBlock T]

@[simp]
theorem unitHorizonElementaryStrategy_coefficientAbsSum
    (T : NNReal) (omega : Omega) :
    (unitHorizonElementaryStrategy (F := F) T).coefficientAbsSum omega = 1 := by
  simp [unitHorizonElementaryStrategy,
    BoundedIndicatorRepresentation.horizonBlock, PredictableElementaryStrategy.coefficientAbsSum]

theorem unitHorizonElementaryStrategy_coefficientAbsSum_le_one
    (T : NNReal) (omega : Omega) :
    (unitHorizonElementaryStrategy (F := F) T).coefficientAbsSum omega ≤
      ((1 : NNReal) : Real) := by
  rw [unitHorizonElementaryStrategy_coefficientAbsSum]
  exact le_rfl

/-- The one-block coefficient is exactly the predictable restriction of the
unit process to `(0,T]`. -/
theorem unitHorizonElementaryStrategy_integrand
    (T : NNReal) :
    (unitHorizonElementaryStrategy (F := F) T).integrand =
      PredictableProcess.restrict
        (stochasticIntervalIocZero (fun _ : Omega => T))
          PredictableProcess.unit := by
  funext t omega
  simp only [unitHorizonElementaryStrategy,
    PredictableElementaryStrategy.integrand, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero,
    PredictableElementaryInterval.integrand,
    BoundedIndicatorRepresentation.horizonBlock]
  change (if 0 < t ∧ t ≤ T then 1 else 0) =
    (if (t, omega) ∈ stochasticIntervalIocZero (fun _ : Omega => T)
      then 1 else 0)
  rw [mem_stochasticIntervalIocZero_iff]
  by_cases h : 0 < t ∧ t ≤ T <;> simp [h]

/-- The horizon block integrates a path from its time-zero value up to the
minimum of the running time and its horizon. -/
theorem unitHorizonElementaryStrategy_finiteHorizonGain_apply
    (X : Process Omega) (T U t : NNReal) (omega : Omega) :
    (unitHorizonElementaryStrategy (F := F) T).finiteHorizonGain X U t omega =
      X (min (min t U) T) omega - X 0 omega := by
  simp [unitHorizonElementaryStrategy,
    BoundedIndicatorRepresentation.horizonBlock,
    PredictableElementaryStrategy.finiteHorizonGain_apply,
    PredictableElementaryStrategy.toElementary, ElementaryStrategy.gain,
    ElementaryInterval.gain]

/-- A unit-integrand, zero-based local source is an actual local graph in its
intrinsic completed carrier, using one supplied exhaustive source schedule. -/
noncomputable def actualUnitSource
    (schedule : LocalCompletedM2ASchedule G)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hZero : G.stochasticIntegral 0 =ᵐ[mu] 0) :
    ActualLocallySIntegrableStrategy (realizationModel G) where
  val := G
  deterministicallyStopped_isRealized := fun T hT => by
    refine ⟨{
      schedule := schedule
      coefficient := fun n =>
        finiteHorizonM2ACoefficientOfElementary
          (schedule.variationBridge n) (schedule.quadraticKernel n)
            (unitHorizonElementaryStrategy (F := F) T) 1
              (unitHorizonElementaryStrategy_coefficientAbsSum_le_one T)
      coefficient_eq := fun n => ?_
      stoppedGain_eq := fun n => ?_ }⟩
    · change Function.uncurry
          (unitHorizonElementaryStrategy (F := F) T).integrand =
        Function.uncurry (G.deterministicallyStopped T hT).integrand
      rw [unitHorizonElementaryStrategy_integrand]
      change Function.uncurry
          (PredictableProcess.restrict
            (stochasticIntervalIocZero (fun _ : Omega => T))
              PredictableProcess.unit) =
        Function.uncurry (G.stoppedIntegrand T)
      rw [LocallySIntegrableStrategy.stoppedIntegrand, hUnit]
    · let K := unitHorizonElementaryStrategy (F := F) T
      let P := schedule.sourcePrefix n
      let U := schedule.horizon n
      let c := finiteHorizonM2ACoefficientOfElementary
        (schedule.variationBridge n) (schedule.quadraticKernel n) K 1
          (unitHorizonElementaryStrategy_coefficientAbsSum_le_one T)
      have hCompleted : ProcessIndistinguishable mu
          (finiteHorizonCompletedM2AGain schedule.usualConditions U
            (schedule.quadraticKernel n) (schedule.variationBridge n)
              (schedule.martingale n) (schedule.terminal_memLp n) c)
          (K.finiteHorizonGain P.stochasticIntegral U) := by
        exact finiteHorizonCompletedM2AGain_indistinguishable_elementary
          schedule.usualConditions (schedule.variationBridge n)
            (schedule.quadraticKernel n) (schedule.martingale n)
              (schedule.terminal_memLp n) K 1
                (unitHorizonElementaryStrategy_coefficientAbsSum_le_one T)
      have hElementary : ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess
            (G.deterministicallyStopped T hT).stochasticIntegral
              (schedule.localizer n))
          (K.finiteHorizonGain P.stochasticIntegral U) := by
        filter_upwards [schedule.sourcePrefix_stochasticIntegral n, hZero]
          with omega hPrefix hZeroOmega
        intro t
        rw [unitHorizonElementaryStrategy_finiteHorizonGain_apply]
        rw [hPrefix (min (min t U) T), hPrefix 0]
        have hFinite : schedule.localizer n omega ≠ ⊤ :=
          ne_top_of_le_ne_top (WithTop.coe_ne_top)
            (schedule.localizer_le_horizon n omega)
        lift schedule.localizer n omega to NNReal using hFinite with tau hTau
        have hTauU : tau ≤ U := by
          exact WithTop.coe_le_coe.mp
            (hTau ▸ schedule.localizer_le_horizon n omega)
        simp only [MeasureTheory.stoppedProcess]
        rw [← hTau]
        simp only [← WithTop.coe_min,
          WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        simp only [LocallySIntegrableStrategy.deterministicallyStopped]
        rw [show min (0 : NNReal) tau = 0 by exact min_eq_left bot_le,
          show min (0 : NNReal) (schedule.horizon n) = 0 by
            exact min_eq_left bot_le]
        change G.stochasticIntegral (min (min t tau) T) omega =
          G.stochasticIntegral
              (min (min (min (min t U) T) tau) (schedule.horizon n)) omega -
            G.stochasticIntegral 0 omega
        rw [hZeroOmega, Pi.zero_apply, sub_zero]
        congr 1
        have hLeftLeU : min (min t tau) T ≤ U :=
          (min_le_left (min t tau) T).trans
            ((min_le_right t tau).trans hTauU)
        symm
        calc
          min (min (min (min t U) T) tau) (schedule.horizon n) =
              min (min (min t tau) T) (min U U) := by
            dsimp only [U]
            ac_rfl
          _ = min (min (min t tau) T) U := by rw [min_self]
          _ = min (min t tau) T := min_eq_left hLeftLeU
      exact hElementary.trans hCompleted.symm

end LocalCompletedM2A

end FTAPTheorem42
