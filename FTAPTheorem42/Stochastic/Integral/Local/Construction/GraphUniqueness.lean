/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairRefinement

/-!
# Uniqueness of intrinsic local-completed graphs

Two actual graphs may initially use different localizing schedules.  After
pairwise refinement, equality of their predictable integrands makes every
finite-horizon completed coefficient equal.  Exhaustion of the common
schedule then identifies the two global gain processes up to
indistinguishability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- In the intrinsic local-completed carrier, the predictable integrand
determines the realized gain process up to indistinguishability. -/
theorem stochasticIntegral_indistinguishable_of_integrand_eq
    (H K : ActualSIntegrableStrategy (realizationModel G))
    (hIntegrand : H.val.integrand = K.val.integrand) :
    ProcessIndistinguishable mu H.val.stochasticIntegral
      K.val.stochasticIntegral := by
  let hH := (Classical.choice H.property).toScheduleGraphRepresentation
  let hK := (Classical.choice K.property).toScheduleGraphRepresentation
  obtain ⟨schedule, hHCommon, hKCommon⟩ :=
    exists_pairCommonScheduleRepresentations hH hK
  let left := Classical.choice hHCommon
  let right := Classical.choice hKCommon
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence
    schedule.isLocalizingSequence
  intro n
  have hCoefficient : left.coefficient n = right.coefficient n := by
    apply FiniteHorizonM2ACoefficient.ext
    calc
      (left.coefficient n).coefficient = Function.uncurry H.val.integrand :=
        left.coefficient_eq n
      _ = Function.uncurry K.val.integrand :=
        congrArg Function.uncurry hIntegrand
      _ = (right.coefficient n).coefficient :=
        (right.coefficient_eq n).symm
  exact (left.stoppedGain_eq n).trans <| by
    rw [hCoefficient]
    exact (right.stoppedGain_eq n).symm

/-- Equality of predictable integrands also identifies two actual local
strategies.  The proof applies the global graph uniqueness theorem to every
positive deterministic stop and then exhausts the deterministic horizons. -/
theorem stochasticIntegral_indistinguishable_of_integrand_eq_of_actualLocal
    (H K : ActualLocallySIntegrableStrategy (realizationModel G))
    (hIntegrand : H.val.integrand = K.val.integrand) :
    ProcessIndistinguishable mu H.val.stochasticIntegral
      K.val.stochasticIntegral := by
  let tau : ℕ → Omega → WithTop NNReal := fun n _ =>
    (((n + 1 : ℕ) : NNReal) : WithTop NNReal)
  have hTau : ProbabilityTheory.IsLocalizingSequence F tau mu := by
    refine { isStoppingTime := ?_, tendsto_top := ?_, mono := ?_ }
    · intro n
      exact isStoppingTime_const F ((n + 1 : ℕ) : NNReal)
    · exact Filter.Eventually.of_forall fun _ => by
        dsimp [tau]
        apply WithTop.tendsto_coe_atTop.comp
        exact tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 1)
    · exact Filter.Eventually.of_forall fun _ n m hnm => by
        dsimp [tau]
        exact_mod_cast Nat.add_le_add_right hnm 1
  apply ProcessIndistinguishable.of_stoppedProcess_localizingSequence hTau
  intro n
  let T : NNReal := (n + 1 : ℕ)
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast Nat.zero_lt_succ n
  let HStopped := H.deterministicallyStopped T hT
  let KStopped := K.deterministicallyStopped T hT
  have hStoppedIntegrand : HStopped.val.integrand = KStopped.val.integrand := by
    change H.val.stoppedIntegrand T = K.val.stoppedIntegrand T
    unfold LocallySIntegrableStrategy.stoppedIntegrand
    rw [hIntegrand]
  have hStopped :=
    stochasticIntegral_indistinguishable_of_integrand_eq HStopped KStopped hStoppedIntegrand
  have hHStoppedEq :
      (fun t omega => H.val.stochasticIntegral (min t T) omega) =
        MeasureTheory.stoppedProcess H.val.stochasticIntegral (tau n) := by
    funext t omega
    by_cases ht : t ≤ T
    · have hle : (t : WithTop NNReal) ≤ tau n omega := by
        dsimp [tau]
        exact WithTop.coe_le_coe.mpr ht
      rw [MeasureTheory.stoppedProcess_eq_of_le hle, min_eq_left ht]
    · have hTt : T ≤ t := le_of_not_ge ht
      have hge : tau n omega ≤ (t : WithTop NNReal) := by
        dsimp [tau]
        exact WithTop.coe_le_coe.mpr hTt
      rw [MeasureTheory.stoppedProcess_eq_of_ge hge, min_eq_right hTt]
      rfl
  have hKStoppedEq :
      (fun t omega => K.val.stochasticIntegral (min t T) omega) =
        MeasureTheory.stoppedProcess K.val.stochasticIntegral (tau n) := by
    funext t omega
    by_cases ht : t ≤ T
    · have hle : (t : WithTop NNReal) ≤ tau n omega := by
        dsimp [tau]
        exact WithTop.coe_le_coe.mpr ht
      rw [MeasureTheory.stoppedProcess_eq_of_le hle, min_eq_left ht]
    · have hTt : T ≤ t := le_of_not_ge ht
      have hge : tau n omega ≤ (t : WithTop NNReal) := by
        dsimp [tau]
        exact WithTop.coe_le_coe.mpr hTt
      rw [MeasureTheory.stoppedProcess_eq_of_ge hge, min_eq_right hTt]
      rfl
  rw [← hHStoppedEq, ← hKStoppedEq]
  exact hStopped

end LocalCompletedM2A

end FTAPTheorem42
