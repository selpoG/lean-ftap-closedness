/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcess
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval

/-!
# Stopping locality of the pathwise finite-variation integral

Restricting a predictable coefficient to `(0,tau]` restricts the pathwise
Stieltjes integral to the same stochastic interval.  The resulting cumulative
integral is therefore the stopped original cumulative integral, pointwise on
every path.
-/

open MeasureTheory Set
open scoped NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

/-- The oriented pathwise density of a stopped coefficient is the interval
indicator of the original density. -/
theorem finiteVariationIntegralDensity_restrict_stochasticInterval
    (E : SIntegrableFiniteVariationBridge G)
    (K : Process Omega) (tau : Omega -> NNReal)
    (u : NNReal) (omega : Omega) :
    finiteVariationIntegralDensity E
        (PredictableProcess.restrict (stochasticIntervalIocZero tau) K)
        (u, omega) =
      (Ioc 0 (tau omega)).indicator
        (fun v => finiteVariationIntegralDensity E K (v, omega)) u := by
  unfold finiteVariationIntegralDensity
  by_cases hMem : (u, omega) ∈ stochasticIntervalIocZero tau
  · have hIoc : u ∈ Ioc 0 (tau omega) :=
      (mem_stochasticIntervalIocZero_iff tau u omega).1 hMem
    rw [PredictableProcess.restrict_apply_of_mem hMem,
      Set.indicator_of_mem hIoc]
  · have hNotIoc : u ∉ Ioc 0 (tau omega) := by
      intro hIoc
      exact hMem ((mem_stochasticIntervalIocZero_iff tau u omega).2 hIoc)
    rw [PredictableProcess.restrict_apply_of_notMem hMem,
      Set.indicator_of_notMem hNotIoc]
    simp

/-- The pathwise finite-variation integral of a coefficient restricted to
`(0,tau]` is the stopped original integral. -/
theorem finiteVariationIntegralProcess_restrict_stochasticInterval
    (E : SIntegrableFiniteVariationBridge G)
    (K : Process Omega) (tau : Omega -> NNReal) :
    finiteVariationIntegralProcess E
        (PredictableProcess.restrict (stochasticIntervalIocZero tau) K) =
      MeasureTheory.stoppedProcess (finiteVariationIntegralProcess E K)
        (fun omega => (tau omega : WithTop NNReal)) := by
  funext t omega
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  change (∫ u, finiteVariationIntegralDensity E
          (PredictableProcess.restrict (stochasticIntervalIocZero tau) K)
          (u, omega) ∂nu.restrict (Ioc 0 t)) = _
  rw [show (fun u => finiteVariationIntegralDensity E
      (PredictableProcess.restrict (stochasticIntervalIocZero tau) K)
      (u, omega)) =
      (Ioc 0 (tau omega)).indicator
        (fun u => finiteVariationIntegralDensity E K (u, omega)) by
    funext u
    exact finiteVariationIntegralDensity_restrict_stochasticInterval
      E K tau u omega]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hInter : Ioc 0 (tau omega) ∩ Ioc 0 t =
      Ioc 0 (min (tau omega) t) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨hZero, hTau⟩, ⟨-, ht⟩⟩
      exact ⟨hZero, le_min hTau ht⟩
    · rintro ⟨hZero, hMin⟩
      exact ⟨⟨hZero, hMin.trans (min_le_left _ _)⟩,
        ⟨hZero, hMin.trans (min_le_right _ _)⟩⟩
  rw [hInter]
  simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [min_comm]
  rfl

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
