/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedMartingaleIntegralProcess
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Càdlàg versions of completed finite-horizon martingale integrals

The terminal-energy completion initially supplies a right-continuous
martingale process.  When the source martingale has left limits, every
elementary approximation has left limits as well.  Uniform process
completion therefore gives a version that has left limits on every path.
This module constructs that version and identifies it with the existing
completed integral up to indistinguishability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- The running gain of one elementary interval inherits left limits from
the integrator. -/
theorem ElementaryInterval.gain_hasLeftLimits
    (S : Process Omega) (hS : ProcessHasLeftLimits S)
    (B : ElementaryInterval Omega NNReal) :
    ProcessHasLeftLimits (B.gain S) := by
  intro omega t
  have hStop :=
    (hS.stoppedProcess
      (fun _ : Omega => (B.stopTime omega : WithTop NNReal))) omega t
  have hStart :=
    (hS.stoppedProcess
      (fun _ : Omega => (B.startTime omega : WithTop NNReal))) omega t
  simp only [stoppedProcess_const_apply] at hStop hStart
  have hGain := (hStop.sub hStart).const_mul (B.coefficient omega)
  apply tendsto_leftLim_of_tendsto
  refine ⟨B.coefficient omega *
    (Function.leftLim
        (fun s => S (min s (B.stopTime omega)) omega) t -
      Function.leftLim
        (fun s => S (min s (B.startTime omega)) omega) t), ?_⟩
  simpa only [ElementaryInterval.gain] using hGain

omit [MeasurableSpace Omega] in
/-- A finite elementary gain inherits left limits from the integrator. -/
theorem ElementaryStrategy.gain_hasLeftLimits
    (S : Process Omega) (hS : ProcessHasLeftLimits S)
    (H : ElementaryStrategy Omega NNReal) :
    ProcessHasLeftLimits (ElementaryStrategy.gain S H) := by
  induction H with
  | nil =>
      change ProcessHasLeftLimits (fun _ _ => 0)
      intro omega t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : NNReal => (0 : Real)) (a := t)
        ⟨0, tendsto_const_nhds⟩
  | cons B H ih =>
      change ProcessHasLeftLimits (fun t omega =>
        B.gain S t omega + ElementaryStrategy.gain S H t omega)
      exact (B.gain_hasLeftLimits S hS).add ih

namespace BoundedMartingaleQuadraticEnergy
namespace Data

open BoundedMartingaleQuadraticKernel

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
/-- Every elementary process approximation has left limits whenever the
source martingale does. -/
theorem processApproximation_hasLeftLimits
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMLeft : ProcessHasLeftLimits M)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    ProcessHasLeftLimits (processApproximation D f hfMeas hf n) := by
  simpa only [processApproximation] using
    (ElementaryStrategy.gain_hasLeftLimits M hMLeft
      (elementaryApproximation D f hfMeas hf n).strategy.toElementary).stoppedProcess
        (fun _ : Omega => (T : WithTop NNReal))

/-- The elementary approximation sequence has a martingale completion whose
every path is right-continuous and has left limits. -/
theorem exists_finiteHorizonMartingaleIntegralCadlagProcess
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ∃ I : Process Omega,
      Martingale I F mu ∧
        (∀ omega t,
          ContinuousWithinAt (I · omega) (Ici t) t) ∧
        ProcessHasLeftLimits I ∧
        (∀ t, T ≤ t → I t =ᵐ[mu] I T) ∧
        I 0 =ᵐ[mu] 0 ∧
        (∃ cutoff : Nat → Nat, StrictMono cutoff ∧
          ∀ᵐ omega ∂mu, TendstoUniformly
            (fun n t => processApproximation D f hfMeas hf (cutoff n) t omega)
            (fun t => I t omega) atTop) ∧
        ∃ hITerminal : MemLp (I T) (2 : ENNReal) mu,
          hITerminal.toLp (I T) =
            finiteHorizonMartingaleTerminalIntegralLp
              D hM hMRight hMT f hfMeas hf := by
  let X : Nat → Process Omega := fun n =>
    processApproximation D f hfMeas hf n
  let hTerminal : ∀ n,
      MemLp (X n T) (2 : ENNReal) mu := fun n => by
    rw [show X n T = terminalApproximation D f hfMeas hf n by
      exact processApproximation_terminal D f hfMeas hf n]
    exact terminalApproximation_memLp D hM hMRight hMT f hfMeas hf n
  have hTerminalToLp : ∀ n,
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
  obtain ⟨cutoff, _hCutoff, I, hIMartingale, hIRight, hILeft,
      hIConstant, hUniform, hITerminal, hITerminalEq⟩ :=
    ChronologicalGrid.exists_cadlag_martingale_of_terminalLp_cauchy
      hUsual X T
      (fun n => processApproximation_isMartingale
        D hM hMRight hMT f hfMeas hf n)
      (fun n => processApproximation_rightContinuous
        D hMRight f hfMeas hf n)
      (fun n => processApproximation_hasLeftLimits
        D hMLeft f hfMeas hf n)
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
  refine ⟨I, hIMartingale, hIRight, hILeft, hIConstant, hIzero,
    ⟨cutoff, _hCutoff, ?_⟩, hITerminal, ?_⟩
  · simpa only [X] using hUniform
  rw [hITerminalEq]
  unfold finiteHorizonMartingaleTerminalIntegralLp
  apply congrArg (limUnder atTop)
  funext n
  exact hTerminalToLp n

/-- A selected càdlàg version of the completed finite-horizon martingale
integral. -/
noncomputable def finiteHorizonMartingaleIntegralCadlagProcess
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Process Omega :=
  Classical.choose
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)

/-- The selected càdlàg integral is a true martingale. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_isMartingale
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Martingale (finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf) F mu :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)).1

/-- The selected càdlàg integral has right-continuous paths. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_rightContinuous
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ∀ omega t, ContinuousWithinAt
      (finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf · omega)
      (Ici t) t :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.1

/-- The selected càdlàg integral has left limits on every path. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_hasLeftLimits
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ProcessHasLeftLimits
      (finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf) :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.2.1

/-- The selected càdlàg integral is constant after the horizon. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_constantAfter
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (t : NNReal) (ht : T ≤ t) :
    finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf t =ᵐ[mu]
      finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf T :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.2.2.1 t ht

/-- A strict subsequence of the elementary process approximations converges
pathwise uniformly to the selected càdlàg integral outside one null set. -/
theorem exists_processApproximation_tendstoUniformly_cadlagProcess
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ∃ cutoff : Nat → Nat, StrictMono cutoff ∧
      ∀ᵐ omega ∂mu, TendstoUniformly
        (fun n t => processApproximation D f hfMeas hf (cutoff n) t omega)
        (fun t => finiteHorizonMartingaleIntegralCadlagProcess
          hUsual D hM hMRight hMLeft hMT f hfMeas hf t omega) atTop :=
  (Classical.choose_spec
    (exists_finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.2.2.2.2.1

/-- The terminal value of the selected càdlàg integral is square
integrable. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_terminal_memLp
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    MemLp (finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf T)
      (2 : ENNReal) mu :=
  Classical.choose
    (Classical.choose_spec
      (exists_finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.2.2.2.2.2

/-- The terminal `Lp` class of the selected càdlàg process is the same
completed energy-space integral as before. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_terminal_toLp
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    (finiteHorizonMartingaleIntegralCadlagProcess_terminal_memLp
      hUsual D hM hMRight hMLeft hMT f hfMeas hf).toLp
        (finiteHorizonMartingaleIntegralCadlagProcess
          hUsual D hM hMRight hMLeft hMT f hfMeas hf T) =
      finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f hfMeas hf :=
  Classical.choose_spec
    (Classical.choose_spec
      (exists_finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf)).2.2.2.2.2.2

/-- The càdlàg completion is a version of the previously constructed
completed martingale integral process. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_indistinguishable
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralCadlagProcess
        hUsual D hM hMRight hMLeft hMT f hfMeas hf)
      (finiteHorizonMartingaleIntegralProcess
        hUsual D hM hMRight hMT f hfMeas hf) := by
  let J : Process Omega :=
    finiteHorizonMartingaleIntegralCadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf
  let I : Process Omega :=
    finiteHorizonMartingaleIntegralProcess
      hUsual D hM hMRight hMT f hfMeas hf
  have hJ : Martingale J F mu :=
    finiteHorizonMartingaleIntegralCadlagProcess_isMartingale
      hUsual D hM hMRight hMLeft hMT f hfMeas hf
  have hI : Martingale I F mu :=
    finiteHorizonMartingaleIntegralProcess_isMartingale
      hUsual D hM hMRight hMT f hfMeas hf
  let hJTerminal : MemLp (J T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralCadlagProcess_terminal_memLp
      hUsual D hM hMRight hMLeft hMT f hfMeas hf
  let hITerminal : MemLp (I T) (2 : ENNReal) mu :=
    finiteHorizonMartingaleIntegralProcess_terminal_memLp
      hUsual D hM hMRight hMT f hfMeas hf
  have hTerminalAE : J T =ᵐ[mu] I T :=
    (MemLp.toLp_eq_toLp_iff hJTerminal hITerminal).mp
      ((finiteHorizonMartingaleIntegralCadlagProcess_terminal_toLp
          hUsual D hM hMRight hMLeft hMT f hfMeas hf).trans
        (finiteHorizonMartingaleIntegralProcess_terminal_toLp
          hUsual D hM hMRight hMT f hfMeas hf).symm)
  have hEqAt : ∀ t, J t =ᵐ[mu] I t := by
    intro t
    by_cases ht : t ≤ T
    · exact (hJ.condExp_ae_eq ht).symm.trans
        ((condExp_congr_ae hTerminalAE).trans (hI.condExp_ae_eq ht))
    · have hTt : T ≤ t := le_of_not_ge ht
      exact (finiteHorizonMartingaleIntegralCadlagProcess_constantAfter
        hUsual D hM hMRight hMLeft hMT f hfMeas hf t hTt).trans
          (hTerminalAE.trans
            (finiteHorizonMartingaleIntegralProcess_constantAfter
              hUsual D hM hMRight hMT f hfMeas hf t hTt).symm)
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense
    J I NNRealRightDenseSkeleton.skeleton
    NNRealRightDenseSkeleton.skeleton_rightDense
    (Filter.Eventually.of_forall
      (finiteHorizonMartingaleIntegralCadlagProcess_rightContinuous
        hUsual D hM hMRight hMLeft hMT f hfMeas hf))
    (Filter.Eventually.of_forall
      (finiteHorizonMartingaleIntegralProcess_rightContinuous
        hUsual D hM hMRight hMT f hfMeas hf))
    (fun n => hEqAt _)

end Data
end BoundedMartingaleQuadraticEnergy

end FTAPTheorem42
