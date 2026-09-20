/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Interface.MarketData
import FTAPTheorem42.Stochastic.Topology.Emery.TerminalSwitching
import FTAPTheorem42.Stochastic.Topology.Emery.RealizedComposition

/-! # The general integral supplies the original-market path operations -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal
open PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Integral linearity and finite predictable switching supply the main
proof's operations, without any no-arbitrage or maximality premise. -/
theorem generalMarket_operations (source : BoundedSemimartingaleSource S F μ) :
    Nonempty (OriginalMarketOperations source) := by
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  refine ⟨{
    adapted := fun H => H.realized.gain_stronglyAdapted
    rightContinuous := fun H => H.realized.gain_rightContinuous
    leftLimits := fun H => H.realized.gain_hasLeftLimits
    zero := fun H => H.realized.gain_initial_eq_zero S source.rightContinuous
    terminal := fun H => H.terminalWitness
    gainGraph := fun H => exists_realized_truncatedGraph source H.realized
    replaceTerminal := fun H f hf => ⟨H.replaceTerminalGain f hf, rfl, rfl⟩
    switchAfter := fun H K τ hτ s hs T hτT =>
      TerminalStrategy.switchAfter S hS source.rightContinuous H K τ hτ s hs T hτT
    gain_switch := fun H K τ hτ s hs T hτT t ω =>
      TerminalStrategy.switchAfter_gain_apply S hS source.rightContinuous H K τ hτ s hs T hτT t ω
    terminal_switch := fun H K τ hτ s hs T hτT ω =>
      congrFun (TerminalStrategy.switchAfter_terminalGain S hS source.rightContinuous
        H K τ hτ s hs T hτT) ω }⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
