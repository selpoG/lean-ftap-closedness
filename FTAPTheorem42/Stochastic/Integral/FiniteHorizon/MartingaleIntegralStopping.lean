/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryStoppingIntegrand
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedMartingaleIntegralProcess

/-!
# Stopping the completed finite-horizon martingale integral

Restricting an energy-`L2` coefficient to the predictable stochastic
interval `(0,tau]` commutes with the completed martingale integral.  The
proof stops the same elementary approximations used by the completion.
Optional sampling identifies their stopped terminal gains with conditional
expectations, while predictable restriction contracts the energy distance.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy
namespace Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
/-- Indicator restriction is contractive on raw representatives of an
`Lp` distance. -/
private theorem dist_toLp_indicator_le
    {alpha : Type*} [MeasurableSpace alpha]
    {nu : Measure alpha} (B : Set alpha)
    (f g : alpha -> Real)
    (hf : MemLp f (2 : ENNReal) nu) (hg : MemLp g (2 : ENNReal) nu)
    (hBf : MemLp (B.indicator f) (2 : ENNReal) nu)
    (hBg : MemLp (B.indicator g) (2 : ENNReal) nu) :
    dist (hBf.toLp (B.indicator f)) (hBg.toLp (B.indicator g)) <=
      dist (hf.toLp f) (hg.toLp g) := by
  classical
  have hNorm : eLpNorm (B.indicator f - B.indicator g) 2 nu <=
      eLpNorm (f - g) 2 nu := by
    apply eLpNorm_mono_ae (hBf.sub hBg).aestronglyMeasurable
    filter_upwards with point
    by_cases hp : point ∈ B
    · simp [hp]
    · simp [hp]
  calc
    dist (hBf.toLp (B.indicator f)) (hBg.toLp (B.indicator g)) =
      (eLpNorm (B.indicator f - B.indicator g) 2 nu).toReal := by
        rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    _ <= (eLpNorm (f - g) 2 nu).toReal :=
      ENNReal.toReal_mono (hf.sub hg).eLpNorm_ne_top hNorm
    _ = dist (hf.toLp f) (hg.toLp g) := by
      rw [Lp.dist_edist, Lp.edist_toLp_toLp]

/-- The completed terminal integral of a coefficient restricted to
`(0,tau]` is the `L2` conditional expectation, at `tau`, of the original
completed terminal integral. -/
theorem finiteHorizonMartingaleTerminalIntegralLp_stopAt
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
        ((stochasticIntervalIocZero tau).indicator f)
        (hfMeas.indicator
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau))
        (hf.indicator
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau)) =
      ((condExpL2 Real Real hTau.measurableSpace_le
        (finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT f hfMeas hf) :
          lpMeas Real Real hTau.measurableSpace 2 mu) :
        Lp Real 2 mu) := by
  classical
  let B : Set (NNReal × Omega) := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  let g : NNReal × Omega -> Real := B.indicator f
  let hgMeas : StronglyMeasurable[F.predictable] g := hfMeas.indicator hB
  let hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure :=
    hf.indicator hB
  let U : Lp Real 2 mu :=
    finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
      f hfMeas hf
  let V : Lp Real 2 mu :=
    finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
      g hgMeas hg
  let H : Nat -> PredictableElementaryStrategy F := fun n =>
    (elementaryApproximation Q f hfMeas hf n).strategy
  let K : Nat -> PredictableElementaryStrategy F := fun n =>
    (H n).stopAt tau hTau
  let C : Nat -> NNReal := fun n =>
    2 * (elementaryApproximation Q f hfMeas hf n).coefficientBound
  have hKBound : forall n omega,
      (K n).coefficientAbsSum omega <= C n := by
    intro n omega
    change ((H n).stopAt tau hTau).coefficientAbsSum omega <= C n
    rw [PredictableElementaryStrategy.coefficientAbsSum_stopAt]
    dsimp only [C, H]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      mul_le_mul_of_nonneg_left
        (elementaryApproximation Q f hfMeas hf n
          |>.coefficientAbsSum_le omega) (by norm_num : (0 : Real) <= 2)
  have hKIntegrand : forall n,
      Function.uncurry (K n).integrand =
        B.indicator (elementaryApproximationIntegrand
          Q f hfMeas hf n) := by
    intro n
    funext point
    rcases point with ⟨t, omega⟩
    simp only [K, H, elementaryApproximationIntegrand,
      Function.uncurry_apply_pair,
      PredictableElementaryStrategy.stopAt_integrand_apply]
    rw [Set.indicator_apply]
    by_cases h : 0 < t ∧ t <= tau omega
    · rw [ite_eq_left h, ite_eq_left
        ((mem_stochasticIntervalIocZero_iff tau t omega).2 h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right (fun hmem => h
        ((mem_stochasticIntervalIocZero_iff tau t omega).1 hmem))]
  let hKMem : forall n, MemLp
      (Function.uncurry (K n).integrand) (2 : ENNReal)
        Q.predictableEnergyMeasure := fun n =>
    elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n)
  let hKGain : forall n, MemLp
      (ElementaryStrategy.gain M (K n).toElementary T)
        (2 : ENNReal) mu := fun n =>
    (K n).gain_memLp_two M hM hMRight T hMT (C n) (hKBound n)
  let Z : Nat -> Lp Real 2 mu := fun n =>
    (hKGain n).toLp (ElementaryStrategy.gain M (K n).toElementary T)
  have hBaseIntegrand := elementaryApproximationIntegrand_tendsto
    Q f hfMeas hf
  have hBaseDistance : Tendsto (fun n => dist
      ((elementaryApproximationIntegrand_memLp Q f hfMeas hf n).toLp
        (elementaryApproximationIntegrand Q f hfMeas hf n))
      (hf.toLp f)) atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hBaseIntegrand
  have hRestrictedDistanceLe : forall n,
      dist ((hKMem n).toLp (Function.uncurry (K n).integrand))
          (hg.toLp g) <=
        dist
          ((elementaryApproximationIntegrand_memLp
            Q f hfMeas hf n).toLp
              (elementaryApproximationIntegrand Q f hfMeas hf n))
          (hf.toLp f) := by
    intro n
    let hn := elementaryApproximationIntegrand_memLp Q f hfMeas hf n
    have hKLp : (hKMem n).toLp (Function.uncurry (K n).integrand) =
        (hn.indicator hB).toLp
          (B.indicator (elementaryApproximationIntegrand
            Q f hfMeas hf n)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun point =>
        congrFun (hKIntegrand n) point
    have hgLp : hg.toLp g = (hf.indicator hB).toLp (B.indicator f) := by
      rfl
    rw [hKLp, hgLp]
    let _ : MeasurableSpace (NNReal × Omega) := F.predictable
    exact dist_toLp_indicator_le B
      (elementaryApproximationIntegrand Q f hfMeas hf n) f hn hf
      (hn.indicator hB) (hf.indicator hB)
  have hRestrictedIntegrand : Tendsto (fun n =>
      (hKMem n).toLp (Function.uncurry (K n).integrand)) atTop
      (nhds (hg.toLp g)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg)
      hRestrictedDistanceLe hBaseDistance
  have hZToV : Tendsto Z atTop (nhds V) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hRestrictedIntegrand
    have hDistanceEq : (fun n => dist (Z n) V) = fun n =>
        dist ((hKMem n).toLp (Function.uncurry (K n).integrand))
          (hg.toLp g) := by
      funext n
      have hElementary :=
        finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
          Q hM hMRight hMT (K n) (C n) (hKBound n)
      calc
        dist (Z n) V =
            dist
              (finiteHorizonMartingaleTerminalIntegralLp
                Q hM hMRight hMT
                (Function.uncurry (K n).integrand)
                (K n).integrand_isStronglyPredictable (hKMem n)) V :=
          congrArg (fun x => dist x V) hElementary.symm
        _ = dist ((hKMem n).toLp (Function.uncurry (K n).integrand))
            (hg.toLp g) := by
          simpa only [V] using
            (dist_finiteHorizonMartingaleTerminalIntegralLp_eq
            Q hM hMRight hMT
            (Function.uncurry (K n).integrand)
            (K n).integrand_isStronglyPredictable (hKMem n)
            g hgMeas hg)
    rw [hDistanceEq]
    exact hDistance
  let terminal : Nat -> Lp Real 2 mu := fun n =>
    (terminalApproximation_memLp Q hM hMRight hMT
      f hfMeas hf n).toLp
        (terminalApproximation Q f hfMeas hf n)
  have hTerminal : Tendsto terminal atTop (nhds U) :=
    terminalApproximation_tendsto Q hM hMRight hMT f hfMeas hf
  have hCondTerminal : Tendsto (fun n =>
      ((condExpL2 Real Real hTau.measurableSpace_le (terminal n) :
        lpMeas Real Real hTau.measurableSpace 2 mu) : Lp Real 2 mu))
      atTop (nhds
        (((condExpL2 Real Real hTau.measurableSpace_le U :
          lpMeas Real Real hTau.measurableSpace 2 mu) : Lp Real 2 mu))) := by
    have hSub : Tendsto (fun n =>
        condExpL2 Real Real hTau.measurableSpace_le (terminal n))
        atTop (nhds
          (condExpL2 Real Real hTau.measurableSpace_le U)) :=
      (condExpL2 Real Real hTau.measurableSpace_le).continuous.continuousAt
        |>.tendsto.comp hTerminal
    exact continuous_subtype_val.continuousAt.tendsto.comp hSub
  have hZCond : forall n, Z n =
      ((condExpL2 Real Real hTau.measurableSpace_le (terminal n) :
        lpMeas Real Real hTau.measurableSpace 2 mu) : Lp Real 2 mu) := by
    intro n
    let X : Process Omega := processApproximation Q f hfMeas hf n
    have hX : Martingale X F mu :=
      processApproximation_isMartingale Q hM hMRight hMT f hfMeas hf n
    have hXRight : forall omega t,
        ContinuousWithinAt (X · omega) (Ici t) t :=
      processApproximation_rightContinuous Q hMRight f hfMeas hf n
    have hOptional :=
      Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
        hX hTau hTauT hXRight
    have hXAtTau : (fun omega => X (tau omega) omega) =
        ElementaryStrategy.gain M (K n).toElementary T := by
      funext omega
      change X (tau omega) omega =
        ElementaryStrategy.gain M
          ((elementaryApproximation Q f hfMeas hf n).strategy.stopAt
            tau hTau).toElementary T omega
      rw [PredictableElementaryStrategy.gain_stopAt]
      simp only [X, processApproximation, stoppedProcess_const_apply]
      rw [min_eq_left (hTauT omega), min_eq_right (hTauT omega)]
    have hXAfter : X (T + 1) =
        terminalApproximation Q f hfMeas hf n := by
      exact (processApproximation_constantAfter Q f hfMeas hf n
        (T + 1) (by exact le_add_right (le_refl T))).trans
          (processApproximation_terminal Q f hfMeas hf n)
    have hSample : ElementaryStrategy.gain M (K n).toElementary T =ᵐ[mu]
        mu[terminalApproximation Q f hfMeas hf n |
          hTau.measurableSpace] := by
      rw [← hXAtTau, ← hXAfter]
      exact hOptional
    apply Lp.ext
    filter_upwards [
      (hKGain n).coeFn_toLp,
      hSample,
      (terminalApproximation_memLp Q hM hMRight hMT
        f hfMeas hf n).condExpL2_ae_eq_condExp
          (𝕜 := Real) hTau.measurableSpace_le] with omega hZ hSample hCond
    rw [hZ, hSample, hCond]
  have hZToCond : Tendsto Z atTop (nhds
      (((condExpL2 Real Real hTau.measurableSpace_le U :
        lpMeas Real Real hTau.measurableSpace 2 mu) : Lp Real 2 mu))) :=
    hCondTerminal.congr' (Filter.Eventually.of_forall fun n =>
      (hZCond n).symm)
  have hEq := tendsto_nhds_unique hZToV hZToCond
  simpa only [B, g, hgMeas, hg, U, V, hB] using hEq

/-- Restricting a completed coefficient to `(0,tau]` gives the stopped
completed martingale integral process. -/
theorem finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (tau : Omega -> NNReal)
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : forall omega, tau omega <= T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess hUsual Q hM hMRight hMT
        ((stochasticIntervalIocZero tau).indicator f)
        (hfMeas.indicator
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau))
        (hf.indicator
          (IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau)))
      (MeasureTheory.stoppedProcess
        (finiteHorizonMartingaleIntegralProcess
          hUsual Q hM hMRight hMT f hfMeas hf)
        (fun omega => (tau omega : WithTop NNReal))) := by
  let B := stochasticIntervalIocZero tau
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero hTau
  let g : NNReal × Omega -> Real := B.indicator f
  let hgMeas : StronglyMeasurable[F.predictable] g := hfMeas.indicator hB
  let hg : MemLp g (2 : ENNReal) Q.predictableEnergyMeasure :=
    hf.indicator hB
  let I : Process Omega := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT f hfMeas hf
  let J : Process Omega := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT g hgMeas hg
  let rho : Omega -> WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  let K : Process Omega := MeasureTheory.stoppedProcess I rho
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJ : Martingale J F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT g hgMeas hg
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJRight : forall omega t,
      ContinuousWithinAt (J · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT g hgMeas hg
  have hK : Martingale K F mu :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hI hTau hIRight
  have hKRight : forall omega t,
      ContinuousWithinAt (K · omega) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous I hIRight
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT f hfMeas hf
  let hJTerminal : MemLp (J T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT g hgMeas hg
  have hITerminalLp : hITerminal.toLp (I T) =
      finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT f hfMeas hf :=
    finiteHorizonMartingaleIntegralProcess_terminal_toLp
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJTerminalLp : hJTerminal.toLp (J T) =
      finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT g hgMeas hg :=
    finiteHorizonMartingaleIntegralProcess_terminal_toLp
      hUsual Q hM hMRight hMT g hgMeas hg
  have hTerminalOperator := finiteHorizonMartingaleTerminalIntegralLp_stopAt
    Q hM hMRight hMT tau hTau hTauT f hfMeas hf
  have hLp : hJTerminal.toLp (J T) =
      ((condExpL2 Real Real hTau.measurableSpace_le
        (hITerminal.toLp (I T)) :
          lpMeas Real Real hTau.measurableSpace 2 mu) : Lp Real 2 mu) := by
    rw [hJTerminalLp, hITerminalLp]
    simpa only [B, g, hgMeas, hg, hB] using hTerminalOperator
  have hJCond : J T =ᵐ[mu] mu[I T | hTau.measurableSpace] := by
    filter_upwards [hJTerminal.coeFn_toLp,
      hITerminal.condExpL2_ae_eq_condExp
        (𝕜 := Real) hTau.measurableSpace_le] with omega hJToLp hCond
    calc
      J T omega = (hJTerminal.toLp (J T)) omega := hJToLp.symm
      _ = ((condExpL2 Real Real hTau.measurableSpace_le
          (hITerminal.toLp (I T)) :
            lpMeas Real Real hTau.measurableSpace 2 mu) :
              Lp Real 2 mu) omega :=
        congrArg (fun z : Lp Real 2 mu => z omega) hLp
      _ = mu[I T | hTau.measurableSpace] omega := hCond
  have hIConstant : I (T + 1) =ᵐ[mu] I T :=
    finiteHorizonMartingaleIntegralProcess_constantAfter
      hUsual Q hM hMRight hMT f hfMeas hf (T + 1)
        (le_add_right (le_refl T))
  have hOptional :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hI hTau hTauT hIRight
  have hSample : (fun omega => I (tau omega) omega) =ᵐ[mu]
      mu[I T | hTau.measurableSpace] :=
    hOptional.trans (condExp_congr_ae hIConstant)
  have hKT : K T = fun omega => I (tau omega) omega := by
    funext omega
    exact MeasureTheory.stoppedProcess_eq_of_ge
      (show rho omega <= (T : WithTop NNReal) by
        exact WithTop.coe_le_coe.mpr (hTauT omega))
  have hTerminalAE : J T =ᵐ[mu] K T :=
    hJCond.trans (hSample.symm.trans
      (Filter.Eventually.of_forall fun omega => (congrFun hKT omega).symm))
  have hEqAt : forall t, J t =ᵐ[mu] K t := by
    intro t
    by_cases ht : t <= T
    · exact (hJ.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hK.condExp_ae_eq ht))
    · have hTt : T <= t := le_of_not_ge ht
      have hJConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual Q hM hMRight hMT g hgMeas hg t hTt
      have hKConstant : K t = K T := by
        funext omega
        rw [show K t omega = I (tau omega) omega by
          exact MeasureTheory.stoppedProcess_eq_of_ge
            (show rho omega <= (t : WithTop NNReal) by
              exact WithTop.coe_le_coe.mpr ((hTauT omega).trans hTt)),
          hKT]
      exact hJConstant.trans (hTerminalAE.trans
        (Filter.Eventually.of_forall fun omega =>
          (congrFun hKConstant omega).symm))
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    J K NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hJRight)
    (Filter.Eventually.of_forall hKRight)
    (fun n => hEqAt _)

/-- The completed finite-horizon martingale integral is indistinguishable
from its deterministic stop at the horizon. -/
theorem
    finiteHorizonMartingaleIntegralProcess_indistinguishable_stop_horizon
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf)
      (MeasureTheory.stoppedProcess
        (finiteHorizonMartingaleIntegralProcess
          hUsual Q hM hMRight hMT f hfMeas hf)
        (fun _ : Omega => (T : WithTop NNReal))) := by
  let I := finiteHorizonMartingaleIntegralProcess
    hUsual Q hM hMRight hMT f hfMeas hf
  let J := MeasureTheory.stoppedProcess I
    (fun _ : Omega => (T : WithTop NNReal))
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJRight : forall omega t,
      ContinuousWithinAt (J · omega) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous I hIRight
  have hEqAt : forall t, I t =ᵐ[mu] J t := by
    intro t
    by_cases ht : t <= T
    · exact Filter.Eventually.of_forall fun omega => by
        change I t omega = MeasureTheory.stoppedProcess I
          (fun _ : Omega => (T : WithTop NNReal)) t omega
        simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
          min_eq_left ht, WithTop.untopA_eq_untop WithTop.coe_ne_top,
          WithTop.untop_coe]
    · have hTt : T <= t := le_of_not_ge ht
      have hConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual Q hM hMRight hMT f hfMeas hf t hTt
      filter_upwards [hConstant] with omega hConstantOmega
      change I t omega = MeasureTheory.stoppedProcess I
        (fun _ : Omega => (T : WithTop NNReal)) t omega
      simpa only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
        min_eq_right hTt, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe] using hConstantOmega
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hIRight)
    (Filter.Eventually.of_forall hJRight)
    (fun n => hEqAt _)

end Data
end BoundedMartingaleQuadraticEnergy
end FTAPTheorem42
