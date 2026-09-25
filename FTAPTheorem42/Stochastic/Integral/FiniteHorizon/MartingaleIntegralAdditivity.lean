/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralAlgebra

/-!
# Additivity of the completed finite-horizon martingale integral

Two independently selected elementary approximations are appended.  Their
integrands converge to the sum in the predictable energy `L2` space, while
their gains are the sum of the two terminal approximations.  Exact energy
isometry identifies the resulting terminal limit, and martingale uniqueness
upgrades terminal additivity to process indistinguishability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy
namespace Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Process Omega} {T : NNReal}

/-- Additivity of the terminal `L2` completion. -/
theorem finiteHorizonMartingaleTerminalIntegralLp_add
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f g : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure)
    (hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure) :
    finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
        (f + g) (hfMeas.add hgMeas) (hf.add hg) =
      finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT f hfMeas hf +
        finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT g hgMeas hg := by
  let H : Nat -> PredictableElementaryStrategy F := fun n =>
    (elementaryApproximation Q f hfMeas hf n).strategy
  let K : Nat -> PredictableElementaryStrategy F := fun n =>
    (elementaryApproximation Q g hgMeas hg n).strategy
  let L : Nat -> PredictableElementaryStrategy F := fun n => H n ++ K n
  let C : Nat -> NNReal := fun n =>
    (elementaryApproximation Q f hfMeas hf n).coefficientBound +
      (elementaryApproximation Q g hgMeas hg n).coefficientBound
  have hLBound : forall n omega, (L n).coefficientAbsSum omega <= C n := by
    intro n omega
    rw [PredictableElementaryStrategy.coefficientAbsSum_append]
    exact add_le_add
      ((elementaryApproximation Q f hfMeas hf n).coefficientAbsSum_le omega)
      ((elementaryApproximation Q g hgMeas hg n).coefficientAbsSum_le omega)
  let terminalL : Nat -> Lp Real (2 : ENNReal) mu := fun n =>
    ((L n).gain_memLp_two M hM hMRight T hMT (C n) (hLBound n)).toLp
      (ElementaryStrategy.gain M (L n).toElementary T)
  let integrandL : Nat -> Lp Real (2 : ENNReal)
      Q.predictableEnergyMeasure := fun n =>
    (elementaryIntegrand_memLp_two Q (L n) (C n) (hLBound n)).toLp
      (Function.uncurry (L n).integrand)
  have hIntegrandLEq : forall n, integrandL n =
      (elementaryApproximationIntegrand_memLp Q f hfMeas hf n).toLp
          (elementaryApproximationIntegrand Q f hfMeas hf n) +
        (elementaryApproximationIntegrand_memLp Q g hgMeas hg n).toLp
          (elementaryApproximationIntegrand Q g hgMeas hg n) := by
    intro n
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards with point
    exact congrFun (congrArg Function.uncurry
      (PredictableElementaryStrategy.append_integrand (H n) (K n))) point
  have hTerminalLEq : forall n, terminalL n =
      (terminalApproximation_memLp Q hM hMRight hMT
          f hfMeas hf n).toLp (terminalApproximation Q f hfMeas hf n) +
        (terminalApproximation_memLp Q hM hMRight hMT
          g hgMeas hg n).toLp (terminalApproximation Q g hgMeas hg n) := by
    intro n
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards with omega
    simpa only [L, H, K, terminalApproximation,
      PredictableElementaryStrategy.toElementary_append, Pi.add_apply] using
        ElementaryStrategy.gain_append M (H n).toElementary
          (K n).toElementary T omega
  have hIntegrandL : Tendsto integrandL atTop
      (nhds ((hf.add hg).toLp (f + g))) := by
    have hSum := (elementaryApproximationIntegrand_tendsto
      Q f hfMeas hf).add
        (elementaryApproximationIntegrand_tendsto Q g hgMeas hg)
    rw [← MemLp.toLp_add hf hg] at hSum
    exact hSum.congr' (Filter.Eventually.of_forall fun n =>
      (hIntegrandLEq n).symm)
  have hTerminalL : Tendsto terminalL atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT f hfMeas hf +
        finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT g hgMeas hg)) := by
    have hSum := (terminalApproximation_tendsto
      Q hM hMRight hMT f hfMeas hf).add
        (terminalApproximation_tendsto Q hM hMRight hMT g hgMeas hg)
    exact hSum.congr' (Filter.Eventually.of_forall fun n =>
      (hTerminalLEq n).symm)
  have hTerminalCompleted : Tendsto terminalL atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
        (f + g) (hfMeas.add hgMeas) (hf.add hg))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hIntegrandL
    exact hDistance.congr' (Filter.Eventually.of_forall fun n => by
      have hElementary := finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
        Q hM hMRight hMT (L n) (C n) (hLBound n)
      calc
        dist (integrandL n) ((hf.add hg).toLp (f + g)) =
            dist
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (Function.uncurry (L n).integrand)
                (L n).integrand_isStronglyPredictable
                (elementaryIntegrand_memLp_two Q (L n) (C n) (hLBound n)))
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (f + g) (hfMeas.add hgMeas) (hf.add hg)) := by
          symm
          exact dist_finiteHorizonMartingaleTerminalIntegralLp_eq
            Q hM hMRight hMT
              (Function.uncurry (L n).integrand)
              (L n).integrand_isStronglyPredictable
              (elementaryIntegrand_memLp_two Q (L n) (C n) (hLBound n))
              (f + g) (hfMeas.add hgMeas) (hf.add hg)
        _ = dist (terminalL n)
            (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
              (f + g) (hfMeas.add hgMeas) (hf.add hg)) := by
          rw [hElementary])
  exact tendsto_nhds_unique hTerminalCompleted hTerminalL

/-- Additivity of the process-valued completed martingale integral. -/
theorem finiteHorizonMartingaleIntegralProcess_add
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f g : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure)
    (hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess hUsual Q hM hMRight hMT
        (f + g) (hfMeas.add hgMeas) (hf.add hg))
      (finiteHorizonMartingaleIntegralProcess
          hUsual Q hM hMRight hMT f hfMeas hf +
        finiteHorizonMartingaleIntegralProcess
          hUsual Q hM hMRight hMT g hgMeas hg) := by
  let I := finiteHorizonMartingaleIntegralProcess hUsual Q hM hMRight hMT
    (f + g) (hfMeas.add hgMeas) (hf.add hg)
  let J := finiteHorizonMartingaleIntegralProcess
      hUsual Q hM hMRight hMT f hfMeas hf +
    finiteHorizonMartingaleIntegralProcess
      hUsual Q hM hMRight hMT g hgMeas hg
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT (f + g) (hfMeas.add hgMeas) (hf.add hg)
  have hJ : Martingale J F mu :=
    (finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT f hfMeas hf).add
      (finiteHorizonMartingaleIntegralProcess_isMartingale
        hUsual Q hM hMRight hMT g hgMeas hg)
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT (f + g) (hfMeas.add hgMeas) (hf.add hg)
  let hFTerminal : MemLp
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT f hfMeas hf
  let hGTerminal : MemLp
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT g hgMeas hg T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT g hgMeas hg
  let hJTerminal : MemLp (J T) (2 : ENNReal) mu := hFTerminal.add hGTerminal
  have hTerminalLp : hITerminal.toLp (I T) = hJTerminal.toLp (J T) := by
    calc
      hITerminal.toLp (I T) =
          finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
            (f + g) (hfMeas.add hgMeas) (hf.add hg) :=
        finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual Q hM hMRight hMT (f + g)
            (hfMeas.add hgMeas) (hf.add hg)
      _ = finiteHorizonMartingaleTerminalIntegralLp
            Q hM hMRight hMT f hfMeas hf +
          finiteHorizonMartingaleTerminalIntegralLp
            Q hM hMRight hMT g hgMeas hg :=
        finiteHorizonMartingaleTerminalIntegralLp_add
          Q hM hMRight hMT f g hfMeas hgMeas hf hg
      _ = hFTerminal.toLp
            (finiteHorizonMartingaleIntegralProcess
              hUsual Q hM hMRight hMT f hfMeas hf T) +
          hGTerminal.toLp
            (finiteHorizonMartingaleIntegralProcess
              hUsual Q hM hMRight hMT g hgMeas hg T) := by
        rw [finiteHorizonMartingaleIntegralProcess_terminal_toLp,
          finiteHorizonMartingaleIntegralProcess_terminal_toLp]
      _ = hJTerminal.toLp (J T) :=
        (MemLp.toLp_add hFTerminal hGTerminal).symm
  have hTerminalAE : I T =ᵐ[mu] J T :=
    (MemLp.toLp_eq_toLp_iff hITerminal hJTerminal).mp hTerminalLp
  have hEqAt : forall t, I t =ᵐ[mu] J t := by
    intro t
    by_cases ht : t <= T
    · exact (hI.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hJ.condExp_ae_eq ht))
    · have hTt : T <= t := le_of_not_ge ht
      have hIConstant := finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual Q hM hMRight hMT (f + g)
          (hfMeas.add hgMeas) (hf.add hg) t hTt
      have hFConstant := finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual Q hM hMRight hMT f hfMeas hf t hTt
      have hGConstant := finiteHorizonMartingaleIntegralProcess_constantAfter
        hUsual Q hM hMRight hMT g hgMeas hg t hTt
      have hJConstant : J t =ᵐ[mu] J T := by
        filter_upwards [hFConstant, hGConstant]
          with omega hFOmega hGOmega
        exact congrArg₂ (fun x y => x + y) hFOmega hGOmega
      exact hIConstant.trans (hTerminalAE.trans hJConstant.symm)
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT (f + g) (hfMeas.add hgMeas) (hf.add hg)
  have hJRight : forall omega t,
      ContinuousWithinAt (J · omega) (Ici t) t := by
    intro omega t
    exact (finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT f hfMeas hf omega t).add
        (finiteHorizonMartingaleIntegralProcess_rightContinuous
          hUsual Q hM hMRight hMT g hgMeas hg omega t)
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hIRight)
    (Filter.Eventually.of_forall hJRight)
    (fun n => hEqAt _)

end Data
end BoundedMartingaleQuadraticEnergy

end FTAPTheorem42
