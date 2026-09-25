/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARestriction
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessStopping

/-!
# Stopping locality of the completed finite-variation integral

Restricting a completed finite-horizon coefficient to the predictable
stochastic interval `(0,tau]` gives the stopped completed finite-variation
process.  The proof passes through the raw pathwise Stieltjes integral, whose
stopping identity is pointwise, and then uses the established raw/completed
agreement on both coefficients.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
/-- The completed finite-variation operator is local under restriction to a
finite stochastic interval. -/
theorem
    finiteHorizonCompletedFiniteVariationPart_restrict_stochasticInterval
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal))) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E
        (K.restrictPredictable (stochasticIntervalIocZero tau)
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau)))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedFiniteVariationPart hUsual T Q E K)
        (fun omega => (tau omega : WithTop NNReal))) := by
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  have hRestricted :=
    finiteHorizonCompletedFiniteVariationPart_restrictPredictable
      hUsual Q E B hB K
  have hRaw : finiteVariationIntegralProcess E
      (PredictableProcess.restrict B K.integrand) =
        MeasureTheory.stoppedProcess
          (finiteVariationIntegralProcess E K.integrand)
          (fun omega => (tau omega : WithTop NNReal)) :=
    finiteVariationIntegralProcess_restrict_stochasticInterval
      E K.integrand tau
  have hRawIndistinguishable : ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E
        (PredictableProcess.restrict B K.integrand))
      (MeasureTheory.stoppedProcess
        (finiteVariationIntegralProcess E K.integrand)
        (fun omega => (tau omega : WithTop NNReal))) :=
    Filter.Eventually.of_forall fun omega t =>
      congrFun (congrFun hRaw t) omega
  have hOriginal :=
    finiteHorizonCompletedFiniteVariationPart_indistinguishable
      hUsual E Q K
  exact hRestricted.trans (hRawIndistinguishable.trans
    (hOriginal.symm.stoppedProcess
      (fun omega => (tau omega : WithTop NNReal))))

omit [SigmaFiniteFiltration mu F] in
/-- The completed finite-variation process is indistinguishable from its
deterministic stop at the coefficient horizon. -/
theorem
    finiteHorizonCompletedFiniteVariationPart_indistinguishable_stop_horizon
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (K : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E K)
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedFiniteVariationPart hUsual T Q E K)
        (fun _ : Omega => (T : WithTop NNReal))) := by
  have hCompleted :=
    finiteHorizonCompletedFiniteVariationPart_indistinguishable
      hUsual E Q K
  have hRaw : finiteVariationIntegralProcess E K.integrand =
      MeasureTheory.stoppedProcess
        (finiteVariationIntegralProcess E K.integrand)
        (fun _ : Omega => (T : WithTop NNReal)) := by
    funext t omega
    unfold FiniteHorizonM2ACoefficient.integrand
    rw [finiteVariationIntegralProcess_finiteHorizonCoefficient]
    simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [finiteVariationIntegralProcess_finiteHorizonCoefficient, min_assoc,
      min_self]
  have hRawIndistinguishable : ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E K.integrand)
      (MeasureTheory.stoppedProcess
        (finiteVariationIntegralProcess E K.integrand)
        (fun _ : Omega => (T : WithTop NNReal))) :=
    Filter.Eventually.of_forall fun omega t =>
      congrFun (congrFun hRaw t) omega
  exact hCompleted.trans (hRawIndistinguishable.trans
    (hCompleted.symm.stoppedProcess
      (fun _ : Omega => (T : WithTop NNReal))))

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
