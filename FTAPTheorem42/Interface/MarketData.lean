/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.GainData

/-! # Regular paths and finite event switching in the original market

This record contains the integration rules used in the main market
arguments. It has no NFLVR, compactness, maximality or closedness field.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The pathwise rules needed by lower-bound control and chronological pasting. -/
structure OriginalMarketOperations (source : BoundedSemimartingaleSource S F μ) where
  adapted : ∀ H : (generalMarket source).Strategy, StronglyAdapted F ((generalMarket source).gain H)
  rightContinuous : ∀ (H : (generalMarket source).Strategy) ω t,
    ContinuousWithinAt ((generalMarket source).gain H · ω) (Ici t) t
  leftLimits : ∀ H : (generalMarket source).Strategy,
    ProcessHasLeftLimits ((generalMarket source).gain H)
  zero : ∀ H : (generalMarket source).Strategy, (generalMarket source).gain H 0 =ᵐ[μ] 0
  terminal : ∀ H : (generalMarket source).Strategy, ∀ᵐ ω ∂μ,
    Tendsto ((generalMarket source).gain H · ω) atTop (𝓝 ((generalMarket source).terminalGain H ω))
  gainGraph : ∀ H : (generalMarket source).Strategy,
    ∃ K : Process Ω, GeneralIntegralGraph source K ((generalMarket source).gain H)
  replaceTerminal : ∀ (H : (generalMarket source).Strategy) (f : Ω → Real),
    (generalMarket source).terminalGain H =ᵐ[μ] f →
      ∃ K : (generalMarket source).Strategy,
        (generalMarket source).gain K = (generalMarket source).gain H ∧
        (generalMarket source).terminalGain K = f
  switchAfter : ∀ (_ _ : (generalMarket source).Strategy)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (s : Set Ω), MeasurableSet[hτ.measurableSpace] s →
    ∀ T : NNReal, (∀ ω, τ ω ≤ T) → (generalMarket source).Strategy
  gain_switch : ∀ (H K : (generalMarket source).Strategy)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : NNReal) (hτT : ∀ ω, τ ω ≤ T) (t : NNReal) (ω : Ω),
    (generalMarket source).gain (switchAfter H K τ hτ s hs T hτT) t ω =
      if ω ∈ s then (generalMarket source).gain H (min t (τ ω)) ω +
        (generalMarket source).gain K t ω - (generalMarket source).gain K (min t (τ ω)) ω
      else (generalMarket source).gain H t ω
  terminal_switch : ∀ (H K : (generalMarket source).Strategy)
    (τ : Ω → NNReal) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : NNReal) (hτT : ∀ ω, τ ω ≤ T) (ω : Ω),
    (generalMarket source).terminalGain (switchAfter H K τ hτ s hs T hτT) ω =
      if ω ∈ s then (generalMarket source).terminalGain K ω +
        (generalMarket source).gain H (τ ω) ω - (generalMarket source).gain K (τ ω) ω
      else (generalMarket source).terminalGain H ω

end FTAPTheorem42.BoundedSourceIntegralMarket
