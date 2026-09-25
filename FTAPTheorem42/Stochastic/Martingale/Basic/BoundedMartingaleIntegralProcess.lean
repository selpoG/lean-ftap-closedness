/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedMartingaleTerminalIntegral
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcessCompletion
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryMartingaleIntegral

/-!
# Completing bounded-martingale integral processes

The grid-independent energy isometry first completes the terminal integral
in `L²`.  Here the same actual elementary approximations are viewed as
stopped true martingales.  Their terminal Cauchy property and Doob control
produce a right-continuous process limit, constant after the fixed horizon,
whose terminal `Lp` class is the completed terminal operator.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy
namespace Data

open BoundedMartingaleQuadraticKernel

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

/-- The stopped actual martingale gain of one chosen elementary
approximation. -/
noncomputable def processApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) : Process Omega :=
  stoppedProcess
    (ElementaryStrategy.gain M
      (elementaryApproximation D f hfMeas hf n).strategy.toElementary)
    (fun _ : Omega => (T : WithTop NNReal))

/-- Every elementary process approximation is a true martingale. -/
theorem processApproximation_isMartingale
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    Martingale (processApproximation D f hfMeas hf n) F mu :=
  (elementaryApproximation D f hfMeas hf n).strategy.stoppedGain_isMartingale
    M hM hMRight T hMT
    (elementaryApproximation D f hfMeas hf n).coefficientBound
    (elementaryApproximation D f hfMeas hf n).coefficientAbsSum_le

omit [SigmaFiniteFiltration mu F] in
/-- Every elementary process approximation has right-continuous paths. -/
theorem processApproximation_rightContinuous
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    forall omega t, ContinuousWithinAt
      (processApproximation D f hfMeas hf n · omega) (Ici t) t := by
  simpa only [processApproximation] using
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (τ := fun _ : Omega => (T : WithTop NNReal))
      (ElementaryStrategy.gain M
        (elementaryApproximation D f hfMeas hf n).strategy.toElementary)
      ((elementaryApproximation D f hfMeas hf n).strategy.rightContinuous_gain
        M hMRight))

omit [SigmaFiniteFiltration mu F] in
/-- Every elementary process approximation is constant after the fixed
horizon. -/
theorem processApproximation_constantAfter
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) (t : NNReal) (ht : T <= t) :
    processApproximation D f hfMeas hf n t =
      processApproximation D f hfMeas hf n T := by
  funext omega
  simp only [processApproximation, stoppedProcess_const_apply]
  rw [min_eq_right ht, min_self]

omit [SigmaFiniteFiltration mu F] in
/-- The terminal value of the process approximation is the raw terminal
gain used by the Hilbert-space completion. -/
theorem processApproximation_terminal
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    processApproximation D f hfMeas hf n T =
      terminalApproximation D f hfMeas hf n := by
  funext omega
  rw [processApproximation, stoppedProcess_const_apply, min_self]
  rfl

/-- The actual approximation sequence has a right-continuous martingale
limit whose terminal value is the completed energy-space integral. -/
theorem exists_finiteHorizonMartingaleIntegralProcess
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ∃ I : Process Omega,
      Martingale I F mu ∧
        (forall omega t,
          ContinuousWithinAt (I · omega) (Ici t) t) ∧
        (forall t, T <= t -> I t =ᵐ[mu] I T) ∧
        I 0 =ᵐ[mu] 0 ∧
        ∃ hITerminal : MemLp (I T) (2 : ENNReal) mu,
          hITerminal.toLp (I T) =
            finiteHorizonMartingaleTerminalIntegralLp
              D hM hMRight hMT f hfMeas hf := by
  let X : Nat -> Process Omega := fun n =>
    processApproximation D f hfMeas hf n
  let hTerminal : forall n,
      MemLp (X n T) (2 : ENNReal) mu := fun n => by
    rw [show X n T = terminalApproximation D f hfMeas hf n by
      exact processApproximation_terminal D f hfMeas hf n]
    exact terminalApproximation_memLp D hM hMRight hMT f hfMeas hf n
  have hTerminalToLp : forall n,
      (hTerminal n).toLp (X n T) =
        (terminalApproximation_memLp D hM hMRight hMT
          f hfMeas hf n).toLp
            (terminalApproximation D f hfMeas hf n) := by
    intro n
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (processApproximation_terminal D f hfMeas hf n) omega
  have hTerminalCauchy : CauchySeq (fun n =>
      (hTerminal n).toLp (X n T)) := by
    rw [show (fun n => (hTerminal n).toLp (X n T)) = fun n =>
      (terminalApproximation_memLp D hM hMRight hMT
        f hfMeas hf n).toLp
          (terminalApproximation D f hfMeas hf n) by
      funext n
      exact hTerminalToLp n]
    exact terminalApproximation_cauchySeq
      D hM hMRight hMT f hfMeas hf
  obtain ⟨cutoff, _hCutoff, I, hIMartingale, hIRight,
      hIConstant, hUniform, hITerminal, hITerminalEq⟩ :=
    ChronologicalGrid.exists_rightContinuous_martingale_of_terminalLp_cauchy
      hUsual X T
      (fun n => processApproximation_isMartingale
        D hM hMRight hMT f hfMeas hf n)
      (fun n => processApproximation_rightContinuous
        D hMRight f hfMeas hf n)
      (fun n t ht => processApproximation_constantAfter
        D f hfMeas hf n t ht)
      hTerminal hTerminalCauchy
  have hIzero : I 0 =ᵐ[mu] 0 := by
    filter_upwards [hUniform] with omega hUniformOmega
    have hAtZero := hUniformOmega.tendsto_at 0
    have hApproximationZero : ∀ n, X (cutoff n) 0 omega = 0 := by
      intro n
      have hStoppedZero :
          (min ((0 : NNReal) : WithTop NNReal)
            (T : WithTop NNReal)).untopA = 0 := by
        have hZeroLe : ((0 : NNReal) : WithTop NNReal) ≤
            (T : WithTop NNReal) := by
          exact_mod_cast (zero_le : (0 : NNReal) ≤ T)
        rw [min_eq_left hZeroLe]
        rfl
      simp only [X, processApproximation, MeasureTheory.stoppedProcess,
        ElementaryStrategy.gain, ElementaryInterval.gain]
      rw [hStoppedZero]
      simp
    exact tendsto_nhds_unique
      (hAtZero.congr' (Filter.Eventually.of_forall fun n =>
        hApproximationZero n)) tendsto_const_nhds
  refine ⟨I, hIMartingale, hIRight, hIConstant, hIzero,
    hITerminal, ?_⟩
  rw [hITerminalEq]
  unfold finiteHorizonMartingaleTerminalIntegralLp
  apply congrArg (limUnder atTop)
  funext n
  exact hTerminalToLp n

/-- The completed process-valued finite-horizon martingale integral. -/
noncomputable def finiteHorizonMartingaleIntegralProcess
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Process Omega :=
  Classical.choose
    (exists_finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf)

/-- The completed finite-horizon integral process is a true martingale. -/
theorem finiteHorizonMartingaleIntegralProcess_isMartingale
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Martingale (finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf) F mu :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf)).1

/-- The completed finite-horizon integral has right-continuous paths. -/
theorem finiteHorizonMartingaleIntegralProcess_rightContinuous
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    forall omega t, ContinuousWithinAt
      (finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf · omega) (Ici t) t :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf)).2.1

/-- The completed finite-horizon integral is constant after the horizon. -/
theorem finiteHorizonMartingaleIntegralProcess_constantAfter
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (t : NNReal) (ht : T <= t) :
    finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf t =ᵐ[mu]
      finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf T :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf)).2.2.1 t ht

/-- The completed finite-horizon martingale integral starts at zero. -/
theorem finiteHorizonMartingaleIntegralProcess_zero
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf 0 =ᵐ[mu] 0 :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf)).2.2.2.1

/-- The terminal value of the completed process is square integrable. -/
theorem finiteHorizonMartingaleIntegralProcess_terminal_memLp
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    MemLp (finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf T) (2 : ENNReal) mu :=
  Classical.choose
    ((Classical.choose_spec
      (exists_finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf)).2.2.2.2)

/-- Process completion and terminal Hilbert-space completion have the same
terminal `Lp` element. -/
theorem finiteHorizonMartingaleIntegralProcess_terminal_toLp
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    (finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual D hM hMRight hMT f hfMeas hf).toLp
        (finiteHorizonMartingaleIntegralProcess
          hUsual D hM hMRight hMT f hfMeas hf T) =
      finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f hfMeas hf :=
  Classical.choose_spec
    ((Classical.choose_spec
      (exists_finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf)).2.2.2.2)

/-- Terminal differences of completed processes retain the exact
predictable-energy isometry. -/
theorem finiteHorizonMartingaleIntegralProcess_terminalDifference_eLpNorm_eq
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (g : NNReal × Omega -> Real)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hg : MemLp g (2 : ENNReal) D.predictableEnergyMeasure) :
    eLpNorm (fun omega =>
      finiteHorizonMartingaleIntegralProcess
          hUsual D hM hMRight hMT f hfMeas hf T omega -
        finiteHorizonMartingaleIntegralProcess
          hUsual D hM hMRight hMT g hgMeas hg T omega)
        (2 : ENNReal) mu =
      eLpNorm (f - g) (2 : ENNReal) D.predictableEnergyMeasure := by
  let hF := finiteHorizonMartingaleIntegralProcess_terminal_memLp
    hUsual D hM hMRight hMT f hfMeas hf
  let hG := finiteHorizonMartingaleIntegralProcess_terminal_memLp
    hUsual D hM hMRight hMT g hgMeas hg
  calc
    eLpNorm (fun omega =>
        finiteHorizonMartingaleIntegralProcess
            hUsual D hM hMRight hMT f hfMeas hf T omega -
          finiteHorizonMartingaleIntegralProcess
            hUsual D hM hMRight hMT g hgMeas hg T omega)
          (2 : ENNReal) mu =
        edist
          (hF.toLp (finiteHorizonMartingaleIntegralProcess
            hUsual D hM hMRight hMT f hfMeas hf T))
          (hG.toLp (finiteHorizonMartingaleIntegralProcess
            hUsual D hM hMRight hMT g hgMeas hg T)) :=
      (Lp.edist_toLp_toLp _ _ hF hG).symm
    _ = edist
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT f hfMeas hf)
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT g hgMeas hg) := by
      rw [finiteHorizonMartingaleIntegralProcess_terminal_toLp
        hUsual D hM hMRight hMT f hfMeas hf,
        finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual D hM hMRight hMT g hgMeas hg]
    _ = eLpNorm (f - g) (2 : ENNReal)
        D.predictableEnergyMeasure :=
      edist_finiteHorizonMartingaleTerminalIntegralLp_eq_eLpNorm
        D hM hMRight hMT f hfMeas hf g hgMeas hg

/-- On a bounded elementary integrand, the completed process agrees up to
indistinguishability with the original stopped elementary gain. -/
theorem finiteHorizonMartingaleIntegralProcess_indistinguishable_elementary
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega <= C) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess hUsual D hM hMRight hMT
        (Function.uncurry H.integrand)
        H.integrand_isStronglyPredictable
        (elementaryIntegrand_memLp_two D H C hH))
      (stoppedProcess (ElementaryStrategy.gain M H.toElementary)
        (fun _ : Omega => (T : WithTop NNReal))) := by
  let f : NNReal × Omega -> Real := Function.uncurry H.integrand
  let hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure :=
    elementaryIntegrand_memLp_two D H C hH
  let I : Process Omega :=
    finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable hf
  let J : Process Omega :=
    stoppedProcess (ElementaryStrategy.gain M H.toElementary)
      (fun _ : Omega => (T : WithTop NNReal))
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable hf
  have hJ : Martingale J F mu :=
    H.stoppedGain_isMartingale M hM hMRight T hMT C hH
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable hf
  let hGain : MemLp (ElementaryStrategy.gain M H.toElementary T)
      (2 : ENNReal) mu := H.gain_memLp_two M hM hMRight T hMT C hH
  have hJTerminalEq : J T =
      ElementaryStrategy.gain M H.toElementary T := by
    funext omega
    change stoppedProcess (ElementaryStrategy.gain M H.toElementary)
      (fun _ : Omega => (T : WithTop NNReal)) T omega = _
    rw [stoppedProcess_const_apply, min_self]
  have hJTerminal : MemLp (J T) (2 : ENNReal) mu := by
    rw [hJTerminalEq]
    exact hGain
  have hITerminalLp : hITerminal.toLp (I T) =
      finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f H.integrand_isStronglyPredictable hf :=
    finiteHorizonMartingaleIntegralProcess_terminal_toLp
      hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable hf
  have hCompletedElementary :
      finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT f H.integrand_isStronglyPredictable hf =
        hGain.toLp (ElementaryStrategy.gain M H.toElementary T) :=
    finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
      D hM hMRight hMT H C hH
  have hGainToJ : hGain.toLp
      (ElementaryStrategy.gain M H.toElementary T) =
        hJTerminal.toLp (J T) := by
    symm
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun omega =>
      congrFun hJTerminalEq omega
  have hTerminalAE : I T =ᵐ[mu] J T :=
    (MemLp.toLp_eq_toLp_iff hITerminal hJTerminal).mp
      (hITerminalLp.trans (hCompletedElementary.trans hGainToJ))
  have hEqAt : forall t, I t =ᵐ[mu] J t := by
    intro t
    by_cases ht : t <= T
    · exact (hI.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hJ.condExp_ae_eq ht))
    · have hTt : T <= t := le_of_not_ge ht
      have hIConstant :=
        finiteHorizonMartingaleIntegralProcess_constantAfter
          hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable
            hf t hTt
      have hJConstant : J t = J T := by
        funext omega
        simp only [J, stoppedProcess_const_apply]
        rw [min_eq_right hTt, min_self]
      exact hIConstant.trans
        (hTerminalAE.trans (Filter.Eventually.of_forall fun omega =>
          (congrFun hJConstant omega).symm))
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    I J NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall
      (finiteHorizonMartingaleIntegralProcess_rightContinuous
        hUsual D hM hMRight hMT f H.integrand_isStronglyPredictable hf))
    (Filter.Eventually.of_forall
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
        (τ := fun _ : Omega => (T : WithTop NNReal))
        (ElementaryStrategy.gain M H.toElementary)
        (H.rightContinuous_gain M hMRight)))
    (fun n => hEqAt _)

/-- The completed integral of the zero coefficient is the zero process. -/
theorem finiteHorizonMartingaleIntegralProcess_indistinguishable_zero
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess hUsual D hM hMRight hMT
        (fun _ : NNReal × Omega => (0 : Real))
        stronglyMeasurable_const MemLp.zero)
      0 := by
  change ProcessIndistinguishable mu
    (finiteHorizonMartingaleIntegralProcess hUsual D hM hMRight hMT
      (Function.uncurry
        (PredictableElementaryStrategy.integrand
          ([] : PredictableElementaryStrategy F)))
      (PredictableElementaryStrategy.integrand_isStronglyPredictable
        ([] : PredictableElementaryStrategy F))
      (elementaryIntegrand_memLp_two D
        ([] : PredictableElementaryStrategy F) 0
          (by simp [PredictableElementaryStrategy.coefficientAbsSum]))) 0
  refine (finiteHorizonMartingaleIntegralProcess_indistinguishable_elementary
      hUsual D hM hMRight hMT
        ([] : PredictableElementaryStrategy F) 0
          (by simp [PredictableElementaryStrategy.coefficientAbsSum])).trans ?_
  exact Filter.Eventually.of_forall fun omega t => by
    simp only [PredictableElementaryStrategy.toElementary,
      List.map_nil, List.sum_nil, ElementaryStrategy.gain,
      MeasureTheory.stoppedProcess, Pi.zero_apply]

/-- The terminal norm of a completed integral is exactly the predictable
energy norm of its coefficient. -/
theorem finiteHorizonMartingaleIntegralProcess_terminal_eLpNorm_eq
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    eLpNorm
        (finiteHorizonMartingaleIntegralProcess
          hUsual D hM hMRight hMT f hfMeas hf T)
        (2 : ENNReal) mu =
      eLpNorm f (2 : ENNReal) D.predictableEnergyMeasure := by
  let I0 := finiteHorizonMartingaleIntegralProcess hUsual D hM hMRight hMT
    (fun _ : NNReal × Omega => (0 : Real))
      stronglyMeasurable_const MemLp.zero
  have hI0 := finiteHorizonMartingaleIntegralProcess_indistinguishable_zero
    hUsual D hM hMRight hMT
  calc
    eLpNorm
        (finiteHorizonMartingaleIntegralProcess
          hUsual D hM hMRight hMT f hfMeas hf T)
        (2 : ENNReal) mu =
      eLpNorm (fun omega =>
        finiteHorizonMartingaleIntegralProcess
            hUsual D hM hMRight hMT f hfMeas hf T omega -
          I0 T omega) (2 : ENNReal) mu := by
            apply eLpNorm_congr_ae
            filter_upwards [hI0.eventuallyEq_at T] with omega homega
            change I0 T omega = 0 at homega
            rw [homega, sub_zero]
    _ = eLpNorm (f - 0) (2 : ENNReal)
        D.predictableEnergyMeasure :=
      finiteHorizonMartingaleIntegralProcess_terminalDifference_eLpNorm_eq
        hUsual D hM hMRight hMT f hfMeas hf
          0 stronglyMeasurable_const MemLp.zero
    _ = eLpNorm f (2 : ENNReal) D.predictableEnergyMeasure := by
      rw [sub_zero]

end Data
end BoundedMartingaleQuadraticEnergy
end FTAPTheorem42
