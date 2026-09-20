/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.General.BoundedPredictableIntegralGraph
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessLocalization
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.ControlConvergence

/-! # Global integral certificates supply convergent bounded truncations

The completed energy and variation controls yield uniform elementary-test
convergence on each schedule coordinate. Removing that common localizing
sequence includes unbounded global actual graphs in the general truncation
graph, without an input stopping or predictable restriction calculus.
-/

namespace FTAPTheorem42.LocalCompletedM2A

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

/-- The original graph supplies bounded-cut rows and their full uniform test
convergence. The supplied regular representative is used only for measurable
test errors; its indistinguishability preserves the original gain. -/
theorem GraphWitness.exists_convergent_coefficientTruncation_rows
    {H : SIntegrableStrategy D} (w : GraphWitness G H)
    {X : Process Ω} (hX : IsStronglyProgressive F X)
    (hXH : ProcessIndistinguishable μ X H.stochasticIntegral) :
    ∃ R : Nat → ActualLocallySIntegrableStrategy (realizationModel G),
      (∀ n, (R n).val.integrand = integralCoefficientTruncation H.integrand n) ∧
      ElementaryEmeryConverges μ F (fun n => (R n).val.stochasticIntegral) X := by
  classical
  let c := fun n k => (w.coefficient k).truncationCut n
  have hc n k : (c n k).coefficient =
      Function.uncurry (integralCoefficientTruncation H.integrand n) := by
    change ({p | |(w.coefficient k).coefficient p| ≤ (n : Real) + 1}.indicator
      (w.coefficient k).coefficient) = _
    rw [w.coefficient_eq k]
    rfl
  have hRows n := exists_actualLocal_of_commonSchedule w.schedule (c n) (hc n)
  choose R hRI hRG hRM hRA using hRows
  refine ⟨R, hRI, ?_⟩
  apply ElementaryEmeryConverges.of_localizingSequence
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (R n).val.stochasticIntegral_isStronglyAdapted
      (R n).val.stochasticIntegral_isRightContinuous)
    hX w.schedule.isLocalizingSequence.toIsPreLocalizingSequence
  intro k
  have hConv := finiteHorizonCompletedM2AGain_truncationCut_emery
    w.schedule.usualConditions (w.schedule.quadraticKernel k)
    (w.schedule.martingale k) (w.schedule.terminal_memLp k) (w.coefficient k)
  have hSeq := hConv.congr_sequence (fun n => (hRG n k).symm)
  exact hSeq.congr_limit ((w.stoppedGain_eq k).symm.trans
    (hXH.symm.stoppedProcess (w.schedule.localizer k)))

/-- No coefficient bound is needed for a global actual graph: its completed
coordinate integrability supplies the entire bounded truncation certificate. -/
theorem IsTruncatedIntegralGraph.of_globalActual
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G)) :
    IsTruncatedIntegralGraph G H.val.integrand H.val.stochasticIntegral := by
  obtain ⟨w⟩ := H.property
  obtain ⟨X, hXA, hXR, hXL, hXH⟩ := w.exists_cadlagGain hGLeft
  obtain ⟨R, hR, hConv⟩ := w.exists_convergent_coefficientTruncation_rows
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR) hXH
  exact ⟨{
    integrand_predictable := H.val.integrand_isPredictable
    approximant := R
    approximant_integrand := hR
    regularGain := X
    regularGain_adapted := hXA
    regularGain_right := hXR
    regularGain_left := hXL
    regularGain_zero := (hXH.eventuallyEq_at 0).trans w.stochasticIntegral_zero
    gain_indistinguishable := hXH
    convergence := hConv }⟩

/-! ## Reading completed coefficient approximations on the original source -/

omit [SigmaFiniteFiltration μ F] in
/-- Finite-horizon elementary gains on a schedule prefix are stopped gains
of the original integrator, with no change of its initial value. -/
theorem LocalCompletedM2ASchedule.elementaryGain_sourcePrefix
    (schedule : LocalCompletedM2ASchedule G) (k : Nat) (J : PredictableElementaryStrategy F) :
    ProcessIndistinguishable μ
      (J.finiteHorizonGain (schedule.sourcePrefix k).stochasticIntegral (schedule.horizon k))
      (stoppedProcess (ElementaryStrategy.gain G.stochasticIntegral J.toElementary)
        (schedule.localizer k)) := by
  let τ := scheduleFiniteLocalizer schedule k
  have hτ : (fun w => (τ w : WithTop NNReal)) = schedule.localizer k := by
    funext w
    exact coe_scheduleFiniteLocalizer schedule k w
  have hPrice := schedule.sourcePrefix_stochasticIntegral k
  change ProcessIndistinguishable μ (schedule.sourcePrefix k).stochasticIntegral
    (stoppedProcess (stoppedProcess G.stochasticIntegral
      (fun _ : Ω => (schedule.horizon k : WithTop NNReal))) (schedule.localizer k)) at hPrice
  rw [stoppedProcess_stoppedProcess_of_le_right (schedule.localizer_le_horizon k)] at hPrice
  filter_upwards [hPrice] with w hw
  intro t
  change ElementaryStrategy.gain (schedule.sourcePrefix k).stochasticIntegral J.toElementary
    (min t (schedule.horizon k)) w = _
  rw [J.toElementary.gain_congr_price _ w hw, ← hτ,
    ElementaryStrategy.gain_finiteStoppedProcess]
  change ElementaryStrategy.gain G.stochasticIntegral J.toElementary
    (min (min t (schedule.horizon k)) (τ w)) w =
    ElementaryStrategy.gain G.stochasticIntegral J.toElementary (min t (τ w)) w
  rw [min_assoc, min_eq_right (scheduleFiniteLocalizer_le_horizon schedule k w)]

end FTAPTheorem42.LocalCompletedM2A
