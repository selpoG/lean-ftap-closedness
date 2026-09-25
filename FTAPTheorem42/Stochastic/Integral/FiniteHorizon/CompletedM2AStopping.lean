/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedFiniteVariationStopping
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralStopping

/-!
# Stopping locality of the completed finite-horizon M2A gain

The completed martingale and finite-variation operators are both local under
restriction to a finite stochastic interval.  Their sum therefore has the
same locality.  This is the concrete semantic bridge used to stop an
intrinsic local completed graph without replacing its exhaustive schedule.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

/-- Restriction to `(0,tau]` commutes with the completed finite-horizon
`M2 + A1` gain. -/
theorem finiteHorizonCompletedM2AGain_restrict_stochasticInterval
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.restrictPredictable (stochasticIntervalIocZero tau)
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau)))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain
          hUsual T Q E hGMartingale hGMTerminal K)
        (fun omega => (tau omega : WithTop NNReal))) := by
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  have hIntegrand :=
    FiniteHorizonM2ACoefficient.restrictPredictable_integrand B hB K
  have hUncurry : Function.uncurry (K.restrictPredictable B hB).integrand =
      B.indicator (Function.uncurry K.integrand) := by
    rw [hIntegrand]
    rfl
  have hMartingaleRaw :=
    finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
        hUsual Q hGMartingale G.martingalePart_isRightContinuous
          hGMTerminal tau hTau hTauT (Function.uncurry K.integrand)
            K.integrand_isStronglyPredictable K.integrand_memLp_energy
  have hMartingaleCongruence :=
    finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry (K.restrictPredictable B hB).integrand)
      (K.restrictPredictable B hB).integrand_isStronglyPredictable
      (K.restrictPredictable B hB).integrand_memLp_energy
      (B.indicator (Function.uncurry K.integrand))
      (K.integrand_isStronglyPredictable.indicator hB)
      (K.integrand_memLp_energy.indicator hB)
      (Filter.Eventually.of_forall fun point => congrFun hUncurry point)
  have hMartingale : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal (K.restrictPredictable B hB))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K) (fun omega => (tau omega : WithTop NNReal))) := by
    exact hMartingaleCongruence.trans hMartingaleRaw
  have hFiniteVariation :=
    finiteHorizonCompletedFiniteVariationPart_restrict_stochasticInterval
      hUsual Q E K tau hTau
  exact hMartingale.add hFiniteVariation

omit [SigmaFiniteFiltration mu F] in
/-- On a coefficient already cut off at `T`, restriction to `(0,tau]` is
the same as restriction to the bounded finite time `min T tau`. -/
theorem finiteHorizonM2ACoefficient_restrict_stochasticIntervalTop_eq_bounded
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> WithTop NNReal) (hTau : IsStoppingTime F tau) :
    (K.restrictPredictable (stochasticIntervalIocZeroTop tau)
        (IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hTau)
      ).integrand =
      (K.restrictPredictable
        (stochasticIntervalIocZero
          (RightContinuousStoppedMartingale.boundedTime T tau))
        (IsStoppingTime.measurableSet_stochasticIntervalIocZero
          (RightContinuousStoppedMartingale.boundedTime_isStoppingTime
            hTau T))).integrand := by
  rw [FiniteHorizonM2ACoefficient.restrictPredictable_integrand,
    FiniteHorizonM2ACoefficient.restrictPredictable_integrand]
  funext t omega
  by_cases hWithin : t <= T
  · by_cases hPos : 0 < t
    · by_cases hTauLe : (t : WithTop NNReal) <= tau omega
      · rw [PredictableProcess.restrict_apply_of_mem,
          PredictableProcess.restrict_apply_of_mem]
        · exact (mem_stochasticIntervalIocZero_iff _ t omega).2
            ⟨hPos, WithTop.coe_le_coe.mp <| by
              rw [RightContinuousStoppedMartingale.coe_boundedTime,
                le_min_iff]
              exact ⟨WithTop.coe_le_coe.mpr hWithin, hTauLe⟩⟩
        · exact (mem_stochasticIntervalIocZeroTop_iff tau t omega).2
            ⟨hPos, hTauLe⟩
      · rw [PredictableProcess.restrict_apply_of_notMem,
          PredictableProcess.restrict_apply_of_notMem]
        · intro hMem
          have hBounded :=
            ((mem_stochasticIntervalIocZero_iff _ t omega).1 hMem).2
          exact hTauLe <| by
            have hCoe := WithTop.coe_le_coe.mpr hBounded
            rw [RightContinuousStoppedMartingale.coe_boundedTime,
              le_min_iff] at hCoe
            exact hCoe.2
        · intro hMem
          exact hTauLe
            ((mem_stochasticIntervalIocZeroTop_iff tau t omega).1 hMem).2
    · have hZero : t = 0 := le_antisymm (not_lt.mp hPos) bot_le
      subst t
      rw [PredictableProcess.restrict_apply_of_notMem,
        PredictableProcess.restrict_apply_of_notMem]
      · exact fun hMem =>
          (not_lt_of_ge bot_le)
            ((mem_stochasticIntervalIocZero_iff _ 0 omega).1 hMem).1
      · exact fun hMem =>
          (not_lt_of_ge bot_le)
            ((mem_stochasticIntervalIocZeroTop_iff tau 0 omega).1 hMem).1
  · have hIntegrandZero : K.integrand t omega = 0 := by
      unfold FiniteHorizonM2ACoefficient.integrand
      rw [finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_notMem]
      intro hMem
      exact hWithin
        ((mem_stochasticIntervalIocZero_iff
          (fun _ : Omega => T) t omega).1 hMem).2
    by_cases hTopMem : (t, omega) ∈ stochasticIntervalIocZeroTop tau
    · rw [PredictableProcess.restrict_apply_of_mem hTopMem,
        hIntegrandZero]
      by_cases hBoundedMem : (t, omega) ∈ stochasticIntervalIocZero
          (RightContinuousStoppedMartingale.boundedTime T tau)
      · rw [PredictableProcess.restrict_apply_of_mem hBoundedMem,
          hIntegrandZero]
      · rw [PredictableProcess.restrict_apply_of_notMem hBoundedMem]
    · rw [PredictableProcess.restrict_apply_of_notMem hTopMem]
      by_cases hBoundedMem : (t, omega) ∈ stochasticIntervalIocZero
          (RightContinuousStoppedMartingale.boundedTime T tau)
      · rw [PredictableProcess.restrict_apply_of_mem hBoundedMem,
          hIntegrandZero]
      · rw [PredictableProcess.restrict_apply_of_notMem hBoundedMem]

/-- A completed finite-horizon gain is indistinguishable from its
deterministic stop at the horizon. -/
theorem finiteHorizonCompletedM2AGain_indistinguishable_stop_horizon
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain
        hUsual T Q E hGMartingale hGMTerminal K)
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain
          hUsual T Q E hGMartingale hGMTerminal K)
        (fun _ : Omega => (T : WithTop NNReal))) := by
  exact
    (finiteHorizonMartingaleIntegralProcess_indistinguishable_stop_horizon
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
        (Function.uncurry K.integrand) K.integrand_isStronglyPredictable
          K.integrand_memLp_energy).add
    (finiteHorizonCompletedFiniteVariationPart_indistinguishable_stop_horizon
      hUsual Q E K)

/-- Stopping a finite-horizon completed gain at a possibly infinite time is
the same as stopping it at the bounded finite time `min T tau`. -/
theorem finiteHorizonCompletedM2AGain_stopTop_indistinguishable_boundedTime
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> WithTop NNReal) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain
          hUsual T Q E hGMartingale hGMTerminal K) tau)
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain
          hUsual T Q E hGMartingale hGMTerminal K)
        (fun omega =>
          (RightContinuousStoppedMartingale.boundedTime T tau omega :
            WithTop NNReal))) := by
  let gain := finiteHorizonCompletedM2AGain
    hUsual T Q E hGMartingale hGMTerminal K
  have hHorizon :=
    finiteHorizonCompletedM2AGain_indistinguishable_stop_horizon
      hUsual Q E hGMartingale hGMTerminal K
  have hStopped := hHorizon.stoppedProcess tau
  have hTimes : (fun omega => min (tau omega) (T : WithTop NNReal)) =
      fun omega =>
        (RightContinuousStoppedMartingale.boundedTime T tau omega :
          WithTop NNReal) := by
    funext omega
    rw [RightContinuousStoppedMartingale.coe_boundedTime, min_comm]
  simpa only [gain, MeasureTheory.stoppedProcess_stoppedProcess', hTimes]
    using hStopped

/-- The two restricted coefficients above produce the same completed graph,
because their horizon-cut integrands agree exactly. -/
theorem finiteHorizonCompletedM2AGain_restrictTop_indistinguishable_bounded
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> WithTop NNReal) (hTau : IsStoppingTime F tau) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.restrictPredictable (stochasticIntervalIocZeroTop tau)
          (IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hTau)))
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.restrictPredictable
          (stochasticIntervalIocZero
            (RightContinuousStoppedMartingale.boundedTime T tau))
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero
            (RightContinuousStoppedMartingale.boundedTime_isStoppingTime
              hTau T)))) := by
  let Ktop := K.restrictPredictable (stochasticIntervalIocZeroTop tau)
    (IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hTau)
  let Kfin := K.restrictPredictable
    (stochasticIntervalIocZero
      (RightContinuousStoppedMartingale.boundedTime T tau))
    (IsStoppingTime.measurableSet_stochasticIntervalIocZero
      (RightContinuousStoppedMartingale.boundedTime_isStoppingTime hTau T))
  have hIntegrand : Ktop.integrand = Kfin.integrand :=
    finiteHorizonM2ACoefficient_restrict_stochasticIntervalTop_eq_bounded
      Q E K tau hTau
  have hM := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
    (Function.uncurry Ktop.integrand) Ktop.integrand_isStronglyPredictable
      Ktop.integrand_memLp_energy
    (Function.uncurry Kfin.integrand) Kfin.integrand_isStronglyPredictable
      Kfin.integrand_memLp_energy
    (Filter.Eventually.of_forall fun point =>
      congrFun (congrArg Function.uncurry hIntegrand) point)
  have hATop := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q Ktop
  have hAFin := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q Kfin
  have hRawEq : ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E Ktop.integrand)
      (finiteVariationIntegralProcess E Kfin.integrand) :=
    Filter.Eventually.of_forall fun omega t =>
      congrFun (congrFun
        (congrArg (finiteVariationIntegralProcess E) hIntegrand) t) omega
  have hA : ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E Ktop)
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E Kfin) :=
    hATop.trans (hRawEq.trans hAFin.symm)
  exact hM.add hA

/-- Full stopping locality for a completed finite-horizon gain at an
arbitrary possibly infinite stopping time. -/
theorem finiteHorizonCompletedM2AGain_restrict_stochasticIntervalTop
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q)
    (tau : Omega -> WithTop NNReal) (hTau : IsStoppingTime F tau) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale hGMTerminal
        (K.restrictPredictable (stochasticIntervalIocZeroTop tau)
          (IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hTau)))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain
          hUsual T Q E hGMartingale hGMTerminal K) tau) := by
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau
  have hSigma :=
    RightContinuousStoppedMartingale.boundedTime_isStoppingTime hTau T
  exact (finiteHorizonCompletedM2AGain_restrictTop_indistinguishable_bounded
    hUsual Q E hGMartingale hGMTerminal K tau hTau).trans
      ((finiteHorizonCompletedM2AGain_restrict_stochasticInterval
        hUsual Q E hGMartingale hGMTerminal K sigma hSigma
          (RightContinuousStoppedMartingale.boundedTime_le T tau)).trans
        (finiteHorizonCompletedM2AGain_stopTop_indistinguishable_boundedTime
          hUsual Q E hGMartingale hGMTerminal K tau).symm)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
