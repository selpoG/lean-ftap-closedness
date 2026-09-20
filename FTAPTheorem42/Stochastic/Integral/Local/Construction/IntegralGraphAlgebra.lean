/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualConvexCombination
import FTAPTheorem42.Stochastic.Integral.Local.Construction.IntegralGraph
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategyAlgebra

/-!
# Linear closure of fixed-source integral graphs

The local-completed carrier is closed under componentwise addition and
deterministic scalar multiplication.  The proof checks actuality after every
positive deterministic stop, using pair refinement for addition and the
intrinsic scalar calculus for multiplication.  The resulting operations then
descend to the decomposition-hidden integral-graph relation.
-/

open Filter MeasureTheory
open scoped NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

namespace ActualLocal

/-- Addition preserves the intrinsic actual-local carrier. -/
noncomputable def add
    (H K : ActualLocallySIntegrableStrategy (realizationModel G)) :
    ActualLocallySIntegrableStrategy (realizationModel G) where
  val := H.val.add K.val
  deterministicallyStopped_isRealized := by
    intro T hT
    let HStopped := H.deterministicallyStopped T hT
    let KStopped := K.deterministicallyStopped T hT
    let sum := actualAddOfPairRefinement HStopped KStopped
    apply (realizationModel G).isRealized_congr
      (H := sum.val)
      (K := (H.val.add K.val).deterministicallyStopped T hT)
      _ _ sum.property
    · funext t omega
      change
        PredictableProcess.restrict
            (stochasticIntervalIocZero (fun _ : Omega => T)) H.val.integrand
            t omega +
          PredictableProcess.restrict
            (stochasticIntervalIocZero (fun _ : Omega => T)) K.val.integrand
            t omega =
        PredictableProcess.restrict
          (stochasticIntervalIocZero (fun _ : Omega => T))
          (fun u eta => H.val.integrand u eta + K.val.integrand u eta) t omega
      by_cases hPoint :
          (t, omega) ∈ stochasticIntervalIocZero (fun _ : Omega => T)
      · rw [PredictableProcess.restrict_apply_of_mem hPoint,
          PredictableProcess.restrict_apply_of_mem hPoint,
          PredictableProcess.restrict_apply_of_mem hPoint]
      · rw [PredictableProcess.restrict_apply_of_notMem hPoint,
          PredictableProcess.restrict_apply_of_notMem hPoint,
          PredictableProcess.restrict_apply_of_notMem hPoint]
        exact add_zero 0
    · exact ProcessIndistinguishable.refl mu _

/-- Deterministic scalar multiplication preserves the intrinsic actual-local
carrier. -/
noncomputable def smul
    (c : Real)
    (H : ActualLocallySIntegrableStrategy (realizationModel G)) :
    ActualLocallySIntegrableStrategy (realizationModel G) where
  val := H.val.smul c
  deterministicallyStopped_isRealized := by
    intro T hT
    let HStopped := H.deterministicallyStopped T hT
    let scaled := (actualScalarCalculus G).smul c HStopped
    apply (realizationModel G).isRealized_congr
      (H := scaled.val)
      (K := (H.val.smul c).deterministicallyStopped T hT)
      _ _ scaled.property
    · funext t omega
      change c * PredictableProcess.restrict
          (stochasticIntervalIocZero (fun _ : Omega => T)) H.val.integrand
          t omega =
        PredictableProcess.restrict
          (stochasticIntervalIocZero (fun _ : Omega => T))
          (c • H.val.integrand) t omega
      by_cases hPoint :
          (t, omega) ∈ stochasticIntervalIocZero (fun _ : Omega => T)
      · rw [PredictableProcess.restrict_apply_of_mem hPoint,
          PredictableProcess.restrict_apply_of_mem hPoint]
        rfl
      · rw [PredictableProcess.restrict_apply_of_notMem hPoint,
          PredictableProcess.restrict_apply_of_notMem hPoint]
        exact mul_zero c
    · exact ProcessIndistinguishable.refl mu _

end ActualLocal

namespace IsIntegralGraph

omit [SigmaFiniteFiltration mu F] in
/-- Fixed-source integral graphs are closed under addition. -/
theorem add
    {integrandH gainH integrandK gainK : Process Omega}
    (hH : IsIntegralGraph G integrandH gainH)
    (hK : IsIntegralGraph G integrandK gainK) :
    IsIntegralGraph G
      (fun t omega => integrandH t omega + integrandK t omega)
      (fun t omega => gainH t omega + gainK t omega) := by
  let H := hH.representative
  let K := hK.representative
  refine ⟨{
    actual := ActualLocal.add H K
    integrand_eq := ?_
    gain_indistinguishable := ?_ }⟩
  · change (fun t omega => H.val.integrand t omega + K.val.integrand t omega) = _
    rw [hH.representative_integrand, hK.representative_integrand]
  · exact hH.representative_gain.add hK.representative_gain

omit [SigmaFiniteFiltration mu F] in
/-- Fixed-source integral graphs are closed under deterministic scalar
multiplication. -/
theorem smul
    (c : Real)
    {integrand gain : Process Omega}
    (h : IsIntegralGraph G integrand gain) :
    IsIntegralGraph G (c • integrand) (c • gain) := by
  let H := h.representative
  refine ⟨{
    actual := ActualLocal.smul c H
    integrand_eq := ?_
    gain_indistinguishable := h.representative_gain.smul c }⟩
  change c • H.val.integrand = c • integrand
  rw [h.representative_integrand]

end IsIntegralGraph

end LocalCompletedM2A

end FTAPTheorem42
