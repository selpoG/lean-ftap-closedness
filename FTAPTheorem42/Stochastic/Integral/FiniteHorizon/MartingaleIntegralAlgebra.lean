/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement

/-!
# Algebra of the completed finite-horizon martingale integral

The process-valued martingale integral is selected nonconstructively from an
`L²` completion.  Consequently scalar homogeneity is not definitional.  This
file proves it from the concrete elementary integral, density in the
predictable energy space, and uniqueness of right-continuous martingales with
the same terminal value.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryStrategy

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

/-- Multiply every coefficient of a predictable elementary strategy by an
arbitrary real scalar. -/
noncomputable def realSMul (c : Real) (H : PredictableElementaryStrategy F) :
    PredictableElementaryStrategy F :=
  H.map fun B =>
    { interval := B.interval.mulCoefficient (fun _ => c)
      startStopping := B.startStopping
      stopStopping := B.stopStopping
      coefficient_measurable := B.coefficient_measurable.const_mul c }

@[simp]
theorem toElementary_realSMul (c : Real)
    (H : PredictableElementaryStrategy F) :
    PredictableElementaryStrategy.toElementary (realSMul c H) =
      ElementaryStrategy.mulCoefficient (fun _ => c)
        (PredictableElementaryStrategy.toElementary H) := by
  classical
  induction H with
  | nil => simp [realSMul, PredictableElementaryStrategy.toElementary,
      ElementaryStrategy.mulCoefficient]
  | cons B H ih =>
      change B.interval.mulCoefficient (fun _ => c) ::
          PredictableElementaryStrategy.toElementary (realSMul c H) =
        B.interval.mulCoefficient (fun _ => c) ::
          ElementaryStrategy.mulCoefficient (fun _ => c)
            (PredictableElementaryStrategy.toElementary H)
      rw [ih]

@[simp]
theorem realSMul_integrand (c : Real)
    (H : PredictableElementaryStrategy F) :
    PredictableElementaryStrategy.integrand (realSMul c H) =
      c • PredictableElementaryStrategy.integrand H := by
  induction H with
  | nil => simp [realSMul, PredictableElementaryStrategy.integrand]
  | cons B H ih =>
      funext t omega
      change
        (if B.interval.startTime omega < t ∧
            t ≤ B.interval.stopTime omega then
          c * B.interval.coefficient omega else 0) +
            PredictableElementaryStrategy.integrand (realSMul c H) t omega =
          c * (B.integrand t omega +
            PredictableElementaryStrategy.integrand H t omega)
      rw [congrFun (congrFun ih t) omega]
      simp only [Pi.smul_apply, smul_eq_mul,
        PredictableElementaryInterval.integrand]
      split_ifs <;> ring

@[simp]
theorem gain_realSMul (c : Real)
    (H : PredictableElementaryStrategy F) (M : Process Omega) (t : NNReal) :
    ElementaryStrategy.gain M
        (PredictableElementaryStrategy.toElementary (realSMul c H)) t =
      c • ElementaryStrategy.gain M
        (PredictableElementaryStrategy.toElementary H) t := by
  funext omega
  rw [toElementary_realSMul,
    ElementaryStrategy.gain_mulCoefficient]
  rfl

/-- A deterministic coefficient-sum bound after real scalar
multiplication. -/
noncomputable def realSMulCoefficientBound (c : Real) (C : NNReal) : NNReal :=
  ⟨|c| * C, mul_nonneg (abs_nonneg c) C.2⟩

@[simp]
theorem coefficientAbsSum_realSMul (c : Real)
    (H : PredictableElementaryStrategy F) (omega : Omega) :
    coefficientAbsSum (realSMul c H) omega =
      |c| * coefficientAbsSum H omega := by
  classical
  induction H with
  | nil => simp [realSMul, coefficientAbsSum]
  | cons B H ih =>
      change |c * B.interval.coefficient omega| +
          coefficientAbsSum (realSMul c H) omega =
        |c| * (|B.interval.coefficient omega| +
          coefficientAbsSum H omega)
      rw [abs_mul, ih]
      ring

theorem coefficientAbsSum_realSMul_le (c : Real)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega ≤ C) :
    forall omega,
      (H.realSMul c).coefficientAbsSum omega ≤
        realSMulCoefficientBound c C := by
  intro omega
  rw [coefficientAbsSum_realSMul]
  exact mul_le_mul_of_nonneg_left (hH omega) (abs_nonneg c)

end PredictableElementaryStrategy

namespace BoundedMartingaleQuadraticEnergy
namespace Data

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Process Omega} {T : NNReal}

/-- Scalar homogeneity of the terminal `L²` completion. -/
theorem finiteHorizonMartingaleTerminalIntegralLp_smul
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure)
    (c : Real) :
    finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c) =
      c • finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT f hfMeas hf := by
  let H : Nat -> PredictableElementaryStrategy F := fun n =>
    (elementaryApproximation Q f hfMeas hf n).strategy
  let K : Nat -> PredictableElementaryStrategy F := fun n =>
    (H n).realSMul c
  let C : Nat -> NNReal := fun n =>
    PredictableElementaryStrategy.realSMulCoefficientBound c
      (elementaryApproximation Q f hfMeas hf n).coefficientBound
  have hKBound : forall n omega,
      (K n).coefficientAbsSum omega ≤ C n := by
    intro n
    exact PredictableElementaryStrategy.coefficientAbsSum_realSMul_le
      c (H n) (elementaryApproximation Q f hfMeas hf n).coefficientBound
      (elementaryApproximation Q f hfMeas hf n).coefficientAbsSum_le
  let scaledTerminal : Nat -> Lp Real (2 : ENNReal) mu := fun n =>
    ((K n).gain_memLp_two M hM hMRight T hMT (C n) (hKBound n)).toLp
      (ElementaryStrategy.gain M (K n).toElementary T)
  have hScaledTerminalEq : forall n,
      scaledTerminal n = c •
        (terminalApproximation_memLp Q hM hMRight hMT
          f hfMeas hf n).toLp
            (terminalApproximation Q f hfMeas hf n) := by
    intro n
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun omega => by
      change ElementaryStrategy.gain M (K n).toElementary T omega =
        c * terminalApproximation Q f hfMeas hf n omega
      simpa only [K, H, terminalApproximation, Pi.smul_apply,
        smul_eq_mul] using congrFun
          (PredictableElementaryStrategy.gain_realSMul c
            ((elementaryApproximation Q f hfMeas hf n).strategy) M T) omega
  have hScaledToBase : Tendsto scaledTerminal atTop
      (nhds (c • finiteHorizonMartingaleTerminalIntegralLp
        Q hM hMRight hMT f hfMeas hf)) := by
    refine ((terminalApproximation_tendsto
      Q hM hMRight hMT f hfMeas hf).const_smul c).congr' ?_
    exact Filter.Eventually.of_forall fun n => (hScaledTerminalEq n).symm
  have hIntegrandScaled : Tendsto (fun n =>
      (elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n)).toLp
        (Function.uncurry (K n).integrand)) atTop
      (nhds ((hf.const_smul c).toLp (c • f))) := by
    have hBase := (elementaryApproximationIntegrand_tendsto
      Q f hfMeas hf).const_smul c
    refine hBase.congr' (Filter.Eventually.of_forall fun n => ?_)
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun point => by
      change c * elementaryApproximationIntegrand Q f hfMeas hf n point =
        (K n).integrand point.1 point.2
      exact (congrFun (congrFun
        (PredictableElementaryStrategy.realSMul_integrand c (H n))
          point.1) point.2).symm
  have hScaledToCompleted : Tendsto scaledTerminal atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hIntegrandScaled
    exact hDistance.congr' (Filter.Eventually.of_forall fun n => (by
      have hRewrite :
          dist (scaledTerminal n)
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (c • f) (hfMeas.const_smul c) (hf.const_smul c)) =
            dist
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (Function.uncurry (K n).integrand)
                (K n).integrand_isStronglyPredictable
                (elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n)))
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (c • f) (hfMeas.const_smul c) (hf.const_smul c)) := by
        change dist
            (((K n).gain_memLp_two M hM hMRight T hMT (C n)
              (hKBound n)).toLp
                (ElementaryStrategy.gain M (K n).toElementary T))
            (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
              (c • f) (hfMeas.const_smul c) (hf.const_smul c)) = _
        rw [finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
          Q hM hMRight hMT (K n) (C n) (hKBound n)]
      have hIso :
          dist
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (Function.uncurry (K n).integrand)
                (K n).integrand_isStronglyPredictable
                (elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n)))
              (finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
                (c • f) (hfMeas.const_smul c) (hf.const_smul c)) =
            dist
              ((elementaryIntegrand_memLp_two Q (K n) (C n)
                (hKBound n)).toLp (Function.uncurry (K n).integrand))
              ((hf.const_smul c).toLp (c • f)) :=
        dist_finiteHorizonMartingaleTerminalIntegralLp_eq
          Q hM hMRight hMT
          (Function.uncurry (K n).integrand)
          (K n).integrand_isStronglyPredictable
          (elementaryIntegrand_memLp_two Q (K n) (C n) (hKBound n))
          (c • f) (hfMeas.const_smul c) (hf.const_smul c)
      exact (hRewrite.trans hIso).symm))
  exact tendsto_nhds_unique hScaledToCompleted hScaledToBase

/-- Scalar homogeneity of the selected process-valued finite-horizon
martingale integral. -/
theorem finiteHorizonMartingaleIntegralProcess_smul
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) Q.predictableEnergyMeasure)
    (c : Real) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess hUsual Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c))
      (c • finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf) := by
  let I : Process Omega :=
    finiteHorizonMartingaleIntegralProcess hUsual Q hM hMRight hMT
      (c • f) (hfMeas.const_smul c) (hf.const_smul c)
  let J : Process Omega := c •
    finiteHorizonMartingaleIntegralProcess
      hUsual Q hM hMRight hMT f hfMeas hf
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c)
  have hBase : Martingale
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf) F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual Q hM hMRight hMT f hfMeas hf
  have hJ : Martingale J F mu := hBase.smul c
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c)
  let hBaseTerminal : MemLp
      (finiteHorizonMartingaleIntegralProcess
        hUsual Q hM hMRight hMT f hfMeas hf T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual Q hM hMRight hMT f hfMeas hf
  let hJTerminal : MemLp (J T) (2 : ENNReal) mu :=
    hBaseTerminal.const_smul c
  have hTerminalLp : hITerminal.toLp (I T) = hJTerminal.toLp (J T) := by
    calc
      hITerminal.toLp (I T) =
          finiteHorizonMartingaleTerminalIntegralLp Q hM hMRight hMT
            (c • f) (hfMeas.const_smul c) (hf.const_smul c) :=
        finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual Q hM hMRight hMT
            (c • f) (hfMeas.const_smul c) (hf.const_smul c)
      _ = c • finiteHorizonMartingaleTerminalIntegralLp
          Q hM hMRight hMT f hfMeas hf :=
        finiteHorizonMartingaleTerminalIntegralLp_smul
          Q hM hMRight hMT f hfMeas hf c
      _ = c • hBaseTerminal.toLp
          (finiteHorizonMartingaleIntegralProcess
            hUsual Q hM hMRight hMT f hfMeas hf T) := by
        rw [finiteHorizonMartingaleIntegralProcess_terminal_toLp]
      _ = hJTerminal.toLp (J T) := by
        change c • hBaseTerminal.toLp
            (finiteHorizonMartingaleIntegralProcess
              hUsual Q hM hMRight hMT f hfMeas hf T) =
          (hBaseTerminal.const_smul c).toLp
            (c • finiteHorizonMartingaleIntegralProcess
              hUsual Q hM hMRight hMT f hfMeas hf T)
        exact (MemLp.toLp_const_smul c hBaseTerminal).symm
  have hTerminalAE : I T =ᵐ[mu] J T :=
    (MemLp.toLp_eq_toLp_iff hITerminal hJTerminal).mp hTerminalLp
  have hEqAt : forall t, I t =ᵐ[mu] J t := by
    intro t
    by_cases ht : t ≤ T
    · exact (hI.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hJ.condExp_ae_eq ht))
    · have hTt : T ≤ t := le_of_not_ge ht
      have hIConstant : I t =ᵐ[mu] I T :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual Q hM hMRight hMT
            (c • f) (hfMeas.const_smul c) (hf.const_smul c) t hTt
      have hBaseConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual Q hM hMRight hMT f hfMeas hf t hTt
      have hJConstant : J t =ᵐ[mu] J T := by
        filter_upwards [hBaseConstant] with omega homega
        exact congrArg (c * ·) homega
      exact hIConstant.trans (hTerminalAE.trans hJConstant.symm)
  have hIRight : forall omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT
        (c • f) (hfMeas.const_smul c) (hf.const_smul c)
  have hJRight : forall omega t,
      ContinuousWithinAt (J · omega) (Ici t) t := by
    intro omega t
    exact (finiteHorizonMartingaleIntegralProcess_rightContinuous
      hUsual Q hM hMRight hMT f hfMeas hf omega t).const_smul c
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall hIRight)
    (Filter.Eventually.of_forall hJRight)
    (fun n => hEqAt _)

end Data
end BoundedMartingaleQuadraticEnergy

end FTAPTheorem42
