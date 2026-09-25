/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer
import FTAPTheorem42.Interface.IntegralClosure

/-! # Original-market terminal properties and equivalent-measure maximality -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery EquivalentMeasureTransfer
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F]

omit [SigmaFiniteFiltration μ F] in
/-- The general integral market has measurable terminal claims and preserves
running lower bounds at its own terminal limit. -/
theorem generalMarket_terminal_properties
    (source : BoundedSemimartingaleSource S F μ) :
    ClaimSetStronglyMeasurable ((generalMarket source).K0OfGainProcessModel μ) ∧
      (generalMarket source).TerminalGainRespectsAdmissibleLowerBound μ := by
  let _ := source.usualConditions.measure_isComplete
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  refine ⟨?_, terminalGainProcessModel_terminalGainRespectsAdmissibleLowerBound S hS⟩
  intro f hf
  have hAE := terminalGainProcessModel_K0_aestronglyMeasurable S hS f hf
  exact (aemeasurable_iff_measurable.mp hAE.aemeasurable).stronglyMeasurable

end FTAPTheorem42.BoundedSourceIntegralMarket
