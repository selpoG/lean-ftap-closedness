/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageConvexification
import FTAPTheorem42.Stochastic.Memin.SummableL2Limit
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness

/-!
# Identifying the intrinsic joint-passage martingale limit

The common Hilbert convexification gives actual strategies whose stopped
martingale terminals are `L²`-Cauchy on every intrinsic joint-passage
coordinate.  The completed finite-horizon isometry transfers this Cauchy
property back to their predictable integrands.  A single strict subsequence
therefore has one predictable `L²` limit for every coordinate.

This module then identifies the completed martingale integral of that limit
with the corresponding stop of the Mémín martingale component limit.  The
proof compares both processes with the same actual convexified coordinates;
no local-integral range membership is assumed.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The raw predictable integrand of one actual Hilbert convexification. -/
noncomputable def intrinsicJointPassageConvexifiedIntegrandSequence
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (n : Nat) : NNReal × Omega -> Real :=
  Function.uncurry
    (intrinsicJointPassageConvexifiedSequence data w n).val.integrand

/-- The energy-space witness supplied by the concrete bounded-coordinate
semantics for one convexified strategy and one joint coordinate. -/
theorem intrinsicJointPassageConvexifiedEnergyMemLp
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (n r : Nat) :
    MemLp (intrinsicJointPassageConvexifiedIntegrandSequence data w n)
      (2 : ENNReal)
      ((intrinsicJointPassageSchedule base data).quadraticKernel r
        ).predictableEnergyMeasure :=
  by
    exact Classical.choose
      (intrinsicJointPassageConvexified_martingaleSemantics
        base data (w n) r)

/-- The square-integrability witness restated for the sequence wrapper. -/
theorem intrinsicJointPassageConvexifiedSequence_terminal_memLp
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (n r : Nat) :
    MemLp (actualLocalL2TerminalCoordinate
      ((intrinsicJointPassageSchedule base data).localizer r)
      ((intrinsicJointPassageSchedule base data).horizon r)
      (intrinsicJointPassageConvexifiedSequence data w n))
      (2 : ENNReal) mu := by
  simpa only [intrinsicJointPassageConvexifiedSequence] using
    intrinsicJointPassageConvexified_terminal_memLp base data (w n) r

/-- The actual stopped coordinate agrees with the completed integral attached
to its canonical energy witness. -/
theorem intrinsicJointPassageConvexified_integralProcess_indistinguishable
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (n r : Nat) :
    let target := intrinsicJointPassageSchedule base data
    ProcessIndistinguishable mu
      (actualLocalL2CoordinateProcess
        (target.localizer r) (target.horizon r)
        (intrinsicJointPassageConvexifiedSequence data w n))
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (target.quadraticKernel r) (target.martingale r)
        (target.sourcePrefix r).martingalePart_isRightContinuous
        (target.terminal_memLp r)
        (intrinsicJointPassageConvexifiedIntegrandSequence data w n)
        (intrinsicJointPassageConvexifiedSequence data w n
          ).val.integrand_isPredictable
        (intrinsicJointPassageConvexifiedEnergyMemLp base data w n r)) :=
  Classical.choose_spec
    (intrinsicJointPassageConvexified_martingaleSemantics
      base data (w n) r)

/-- On a fixed joint coordinate, the predictable-energy distance of two
actual convexifications is exactly the distance of their stopped terminals. -/
theorem intrinsicJointPassageConvexified_integrand_dist_eq_terminal_dist
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (r m n : Nat) :
    dist
      ((intrinsicJointPassageConvexifiedEnergyMemLp base data w m r).toLp
        (intrinsicJointPassageConvexifiedIntegrandSequence data w m))
      ((intrinsicJointPassageConvexifiedEnergyMemLp base data w n r).toLp
        (intrinsicJointPassageConvexifiedIntegrandSequence data w n)) =
    dist
      ((intrinsicJointPassageConvexifiedSequence_terminal_memLp
        base data w m r).toLp
        (actualLocalL2TerminalCoordinate
          ((intrinsicJointPassageSchedule base data).localizer r)
          ((intrinsicJointPassageSchedule base data).horizon r)
          (intrinsicJointPassageConvexifiedSequence data w m)))
      ((intrinsicJointPassageConvexifiedSequence_terminal_memLp
        base data w n r).toLp
        (actualLocalL2TerminalCoordinate
          ((intrinsicJointPassageSchedule base data).localizer r)
          ((intrinsicJointPassageSchedule base data).horizon r)
          (intrinsicJointPassageConvexifiedSequence data w n))) := by
  let target := intrinsicJointPassageSchedule base data
  let fm := intrinsicJointPassageConvexifiedIntegrandSequence data w m
  let fn := intrinsicJointPassageConvexifiedIntegrandSequence data w n
  let hm := intrinsicJointPassageConvexifiedEnergyMemLp base data w m r
  let hn := intrinsicJointPassageConvexifiedEnergyMemLp base data w n r
  let Im := finiteHorizonMartingaleIntegralProcess target.usualConditions
    (target.quadraticKernel r) (target.martingale r)
    (target.sourcePrefix r).martingalePart_isRightContinuous
    (target.terminal_memLp r) fm
    (intrinsicJointPassageConvexifiedSequence data w m
      ).val.integrand_isPredictable hm
  let In := finiteHorizonMartingaleIntegralProcess target.usualConditions
    (target.quadraticKernel r) (target.martingale r)
    (target.sourcePrefix r).martingalePart_isRightContinuous
    (target.terminal_memLp r) fn
    (intrinsicJointPassageConvexifiedSequence data w n
      ).val.integrand_isPredictable hn
  have hIm :=
    intrinsicJointPassageConvexified_integralProcess_indistinguishable
      base data w m r |>.eventuallyEq_at (target.horizon r)
  have hIn :=
    intrinsicJointPassageConvexified_integralProcess_indistinguishable
      base data w n r |>.eventuallyEq_at (target.horizon r)
  rw [actualLocalL2CoordinateProcess_horizon] at hIm hIn
  calc
    dist (hm.toLp fm) (hn.toLp fn) =
        (eLpNorm (fm - fn) (2 : ENNReal)
          (target.quadraticKernel r).predictableEnergyMeasure).toReal := by
      rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    _ = (eLpNorm (fun omega =>
          Im (target.horizon r) omega - In (target.horizon r) omega)
          (2 : ENNReal) mu).toReal := by
      apply congrArg ENNReal.toReal
      exact (finiteHorizonMartingaleIntegralProcess_terminalDifference_eLpNorm_eq
        target.usualConditions (target.quadraticKernel r)
        (target.martingale r)
        (target.sourcePrefix r).martingalePart_isRightContinuous
        (target.terminal_memLp r) fm
        (intrinsicJointPassageConvexifiedSequence data w m
          ).val.integrand_isPredictable hm fn
        (intrinsicJointPassageConvexifiedSequence data w n
          ).val.integrand_isPredictable hn).symm
    _ = (eLpNorm
          (actualLocalL2TerminalCoordinate
              (target.localizer r) (target.horizon r)
              (intrinsicJointPassageConvexifiedSequence data w m) -
            actualLocalL2TerminalCoordinate
              (target.localizer r) (target.horizon r)
              (intrinsicJointPassageConvexifiedSequence data w n))
          (2 : ENNReal) mu).toReal := by
      apply congrArg ENNReal.toReal
      exact eLpNorm_congr_ae (hIm.sub hIn).symm
    _ = dist
        ((intrinsicJointPassageConvexifiedSequence_terminal_memLp
          base data w m r).toLp
          (actualLocalL2TerminalCoordinate
            (target.localizer r) (target.horizon r)
            (intrinsicJointPassageConvexifiedSequence data w m)))
        ((intrinsicJointPassageConvexifiedSequence_terminal_memLp
          base data w n r).toLp
          (actualLocalL2TerminalCoordinate
            (target.localizer r) (target.horizon r)
            (intrinsicJointPassageConvexifiedSequence data w n))) := by
      rw [Lp.dist_edist, Lp.edist_toLp_toLp]

/-- Terminal `L²`-Cauchy convergence transfers to the raw predictable
integrands under every joint energy control. -/
theorem intrinsicJointPassageConvexified_integrand_cauchy
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (hTerminalCauchy : forall r, CauchySeq (fun n =>
      (intrinsicJointPassageConvexifiedSequence_terminal_memLp
        base data w n r).toLp
        (actualLocalL2TerminalCoordinate
          ((intrinsicJointPassageSchedule base data).localizer r)
          ((intrinsicJointPassageSchedule base data).horizon r)
          (intrinsicJointPassageConvexifiedSequence data w n))))
    (r : Nat) :
    CauchySeq (fun n =>
      (intrinsicJointPassageConvexifiedEnergyMemLp
        base data w n r).toLp
        (intrinsicJointPassageConvexifiedIntegrandSequence data w n)) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hEpsilon
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff.mp (hTerminalCauchy r)) epsilon hEpsilon
  exact ⟨N, fun m hm n hn => by
    rw [intrinsicJointPassageConvexified_integrand_dist_eq_terminal_dist]
    exact hN m hm n hn⟩

/-- The pointwise representative selected from the actual Hilbert
convexifications. -/
noncomputable def intrinsicJointPassageSelectedIntegrand
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat) :
    NNReal × Omega -> Real := fun p =>
  limUnder atTop (fun n =>
    intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p)

omit [F.IsRightContinuous] in
/-- A pointwise limit of the convexified predictable integrands is again
strongly predictable. -/
theorem intrinsicJointPassageSelectedIntegrand_isStronglyPredictable
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat) :
    StronglyMeasurable[F.predictable]
      (intrinsicJointPassageSelectedIntegrand data w cutoff) := by
  change StronglyMeasurable[F.predictable]
    (Function.uncurry (meminLimitIntegrand (fun n =>
      (intrinsicJointPassageConvexifiedSequence data w (cutoff n)).val)))
  exact meminLimitIntegrand_isStronglyPredictable _

/-- One strict subsequence of the actual convexifications selects a common
predictable `L²` limit on all intrinsic joint coordinates. -/
theorem exists_intrinsicJointPassage_selectedIntegrand
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n)
      (cutoff : Nat -> Nat), StrictMono cutoff ∧ forall r,
      MemLp (intrinsicJointPassageSelectedIntegrand data w cutoff)
          (2 : ENNReal)
          ((intrinsicJointPassageSchedule base data).quadraticKernel r
            ).predictableEnergyMeasure ∧
        (∀ᵐ p ∂((intrinsicJointPassageSchedule base data).quadraticKernel r
            ).predictableEnergyMeasure,
          Tendsto (fun n =>
            intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p) atTop
            (nhds (intrinsicJointPassageSelectedIntegrand data w cutoff p))) ∧
        Tendsto (fun n => eLpNorm (fun p =>
          intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p -
            intrinsicJointPassageSelectedIntegrand data w cutoff p)
          (2 : ENNReal)
          ((intrinsicJointPassageSchedule base data).quadraticKernel r
            ).predictableEnergyMeasure) atTop (nhds 0) := by
  obtain ⟨w, hTerminalCauchy⟩ :=
    exists_intrinsicJointPassage_actualTerminalCauchy base data
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let control : Nat -> MeminPredictableControlMeasure F := fun r =>
    ((intrinsicJointPassageSchedule base data).quadraticKernel r
      ).predictableEnergyMeasure
  let f : Nat -> NNReal × Omega -> Real :=
    intrinsicJointPassageConvexifiedIntegrandSequence data w
  let hf : forall r n, MemLp (f n) (2 : ENNReal) (control r) := fun r n => by
    simpa only [f, control] using
      intrinsicJointPassageConvexifiedEnergyMemLp base data w n r
  have hCauchy : forall r, CauchySeq (fun n =>
      (hf r n).toLp (f n)) := fun r =>
    by
      simpa only [f, hf, control] using
        intrinsicJointPassageConvexified_integrand_cauchy
          base data w hTerminalCauchy r
  obtain ⟨cutoff, hCutoff, hLimit⟩ :=
    MeminL2.exists_common_subsequence_memLp_two_limit_of_cauchy
      control f hf hCauchy
  refine ⟨w, cutoff, hCutoff, fun r => ?_⟩
  change MemLp (fun p => limUnder atTop (fun n =>
      intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p)) (2 : ENNReal)
        ((intrinsicJointPassageSchedule base data).quadraticKernel r
          ).predictableEnergyMeasure ∧ _
  simpa only [control, f, intrinsicJointPassageSelectedIntegrand] using
    hLimit r

/-- Forward convexification preserves the already constructed pointwise
martingale-component limit, and so does every strict subsequence. -/
theorem intrinsicJointPassageConvexified_coordinate_tendsto_ae_limit
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (r : Nat) (t : NNReal) :
    ∀ᵐ omega ∂mu, Tendsto (fun n =>
      actualLocalL2CoordinateProcess
        ((intrinsicJointPassageSchedule base data).localizer r)
        ((intrinsicJointPassageSchedule base data).horizon r)
        (intrinsicJointPassageConvexifiedSequence data w (cutoff n))
        t omega) atTop
      (nhds (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          ((intrinsicJointPassageSchedule base data).localizer r))
        (fun _ => ((intrinsicJointPassageSchedule base data).horizon r :
          WithTop NNReal)) t omega)) := by
  let target := intrinsicJointPassageSchedule base data
  filter_upwards [ae_all_iff.2 data.approximant_martingaleZero,
      data.martingaleTendsto] with omega hZero hTendsto
  let u : NNReal :=
    (min (t : WithTop NNReal) (target.horizon r : WithTop NNReal)).untopA
  let v : NNReal :=
    (min (u : WithTop NNReal) (target.localizer r omega)).untopA
  have hRaw : Tendsto (fun k =>
      (data.approximant k).val.martingalePart v omega)
      atTop (nhds (data.martingaleLimit v omega)) := hTendsto v
  have hConvex :=
    (TailConvexWeights.toForward w).tendsto_apply_real hRaw
  have hSubsequence := hConvex.comp hCutoff.tendsto_atTop
  apply hSubsequence.congr'
  filter_upwards with n
  rw [show actualLocalL2CoordinateProcess
      (target.localizer r) (target.horizon r)
      (intrinsicJointPassageConvexifiedSequence data w (cutoff n))
      t omega =
      (w (cutoff n)).apply (fun k =>
        actualLocalL2CoordinateProcess
          (target.localizer r) (target.horizon r)
          (data.approximant k) t) omega by
    exact congrFun (congrFun
      (intrinsicJointPassageConvexified_coordinateProcess_eq_apply data (w (cutoff n))
        (target.localizer r) (target.horizon r)) t) omega]
  simp only [TailConvexWeights.toForward, TailConvexWeights.apply,
    actualLocalL2CoordinateProcess, MeasureTheory.stoppedProcess,
    SIntegrableStrategy.centeredMartingalePart, hZero, Pi.zero_apply,
    sub_zero, target, u, v, Function.comp_apply]

/-- The completed martingale integral of the selected predictable limit is
the corresponding stop of the existing Mémín martingale component limit. -/
theorem intrinsicJointPassageSelectedIntegrand_martingaleIntegral
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (hLimit : forall r,
      MemLp (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (2 : ENNReal)
        ((intrinsicJointPassageSchedule base data).quadraticKernel r
          ).predictableEnergyMeasure ∧
      Tendsto (fun n => eLpNorm (fun p =>
        intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p -
          intrinsicJointPassageSelectedIntegrand data w cutoff p)
        (2 : ENNReal)
        ((intrinsicJointPassageSchedule base data).quadraticKernel r
          ).predictableEnergyMeasure) atTop (nhds 0))
    (r : Nat) :
    let target := intrinsicJointPassageSchedule base data
    ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess target.usualConditions
        (target.quadraticKernel r) (target.martingale r)
        (target.sourcePrefix r).martingalePart_isRightContinuous
        (target.terminal_memLp r)
        (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hLimit r).1)
      (MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess data.martingaleLimit
          (target.localizer r))
        (fun _ => (target.horizon r : WithTop NNReal))) := by
  let target := intrinsicJointPassageSchedule base data
  let f : Nat -> NNReal × Omega -> Real := fun n =>
    intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n)
  let hf : forall n, MemLp (f n) (2 : ENNReal)
      (target.quadraticKernel r).predictableEnergyMeasure := fun n =>
    intrinsicJointPassageConvexifiedEnergyMemLp
      base data w (cutoff n) r
  let limit := intrinsicJointPassageSelectedIntegrand data w cutoff
  let hLimitMem : MemLp limit (2 : ENNReal)
      (target.quadraticKernel r).predictableEnergyMeasure := (hLimit r).1
  let I : (g : NNReal × Omega -> Real) ->
      StronglyMeasurable[F.predictable] g ->
      MemLp g (2 : ENNReal)
        (target.quadraticKernel r).predictableEnergyMeasure -> Process Omega :=
    fun g hg hgp => finiteHorizonMartingaleIntegralProcess
      target.usualConditions (target.quadraticKernel r) (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) g hg hgp
  have hIntegralNorm : forall t, Tendsto (fun n => eLpNorm (fun omega =>
      I (f n)
          (intrinsicJointPassageConvexifiedSequence data w (cutoff
            n)).val.integrand_isPredictable (hf n) t omega -
        I limit
          (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
            hLimitMem t omega)
      (2 : ENNReal) mu) atTop (nhds 0) := by
    intro t
    have hDifference : forall n,
        eLpNorm (fun omega =>
          I (f n)
              (intrinsicJointPassageConvexifiedSequence data w (cutoff
                n)).val.integrand_isPredictable (hf n)
              (target.horizon r) omega -
            I limit
              (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
                hLimitMem (target.horizon r) omega)
          (2 : ENNReal) mu =
        eLpNorm (f n - limit) (2 : ENNReal)
          (target.quadraticKernel r).predictableEnergyMeasure := fun n =>
      finiteHorizonMartingaleIntegralProcess_terminalDifference_eLpNorm_eq
        target.usualConditions (target.quadraticKernel r)
        (target.martingale r)
        (target.sourcePrefix r).martingalePart_isRightContinuous
        (target.terminal_memLp r) (f n)
        (intrinsicJointPassageConvexifiedSequence data w (cutoff
          n)).val.integrand_isPredictable (hf n)
        limit
        (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) hLimitMem
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal))
        atTop (nhds 0))
      (by simpa only [f, limit] using (hLimit r).2)
      (fun _ => bot_le)
      (fun n => by
        let X : Process Omega := fun s omega =>
          I (f n)
              (intrinsicJointPassageConvexifiedSequence data w (cutoff
                n)).val.integrand_isPredictable (hf n)
              s omega -
            I limit
              (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
                hLimitMem s omega
        have hX : Martingale X F mu :=
          (finiteHorizonMartingaleIntegralProcess_isMartingale
            target.usualConditions (target.quadraticKernel r)
            (target.martingale r)
            (target.sourcePrefix r).martingalePart_isRightContinuous
            (target.terminal_memLp r) (f n)
            (intrinsicJointPassageConvexifiedSequence data w (cutoff
              n)).val.integrand_isPredictable (hf n)).sub
          (finiteHorizonMartingaleIntegralProcess_isMartingale
            target.usualConditions (target.quadraticKernel r)
            (target.martingale r)
            (target.sourcePrefix r).martingalePart_isRightContinuous
            (target.terminal_memLp r) limit
            (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) hLimitMem)
        have hXT : MemLp (X (target.horizon r)) (2 : ENNReal) mu := by
          exact (finiteHorizonMartingaleIntegralProcess_terminal_memLp
              target.usualConditions (target.quadraticKernel r)
              (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) (f n)
              (intrinsicJointPassageConvexifiedSequence data w (cutoff
                n)).val.integrand_isPredictable (hf n)).sub
            (finiteHorizonMartingaleIntegralProcess_terminal_memLp
              target.usualConditions (target.quadraticKernel r)
              (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) limit
              (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
                hLimitMem)
        by_cases ht : t <= target.horizon r
        · exact (MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
            hX ht hXT).2.trans_eq (hDifference n)
        · have hTt : target.horizon r <= t := le_of_not_ge ht
          have hConstant : X t =ᵐ[mu] X (target.horizon r) :=
            (finiteHorizonMartingaleIntegralProcess_constantAfter
              target.usualConditions (target.quadraticKernel r)
              (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) (f n)
              (intrinsicJointPassageConvexifiedSequence data w (cutoff
                n)).val.integrand_isPredictable (hf n)
              t hTt).sub
            (finiteHorizonMartingaleIntegralProcess_constantAfter
              target.usualConditions (target.quadraticKernel r)
              (target.martingale r)
              (target.sourcePrefix r).martingalePart_isRightContinuous
              (target.terminal_memLp r) limit
              (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
                hLimitMem t hTt)
          rw [eLpNorm_congr_ae hConstant, hDifference n]
          exact le_rfl)
  apply ProcessIndistinguishable.of_common_tendstoInMeasure_nnreal
    (fun n => actualLocalL2CoordinateProcess
      (target.localizer r) (target.horizon r)
      (intrinsicJointPassageConvexifiedSequence data w (cutoff n)))
    (I limit
      (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) hLimitMem)
    (MeasureTheory.stoppedProcess
      (MeasureTheory.stoppedProcess data.martingaleLimit (target.localizer r))
      (fun _ => (target.horizon r : WithTop NNReal)))
  · exact finiteHorizonMartingaleIntegralProcess_rightContinuous
      target.usualConditions (target.quadraticKernel r)
      (target.martingale r)
      (target.sourcePrefix r).martingalePart_isRightContinuous
      (target.terminal_memLp r) limit
      (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) hLimitMem
  · intro omega t
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (MeasureTheory.stoppedProcess data.martingaleLimit (target.localizer r))
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
        data.martingaleLimit data.martingaleLimit_rightContinuous) omega t
  · intro t
    have hIntegral : TendstoInMeasure mu (fun n =>
        I (f n)
          (intrinsicJointPassageConvexifiedSequence data w (cutoff
            n)).val.integrand_isPredictable (hf n) t)
        atTop
        (I limit
          (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff)
            hLimitMem t) :=
      tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
        (hIntegralNorm t)
    refine TendstoInMeasure.congr_left ?_ hIntegral
    intro n
    exact (intrinsicJointPassageConvexified_integralProcess_indistinguishable
      base data w (cutoff n) r).eventuallyEq_at t |>.symm
  · intro t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((intrinsicJointPassageConvexified_coordinate_martingale
        base data (w (cutoff n)) r).stronglyMeasurable t).mono (F.le t)
        |>.aestronglyMeasurable
    exact intrinsicJointPassageConvexified_coordinate_tendsto_ae_limit
      base data w cutoff hCutoff r t

/-- The actual Hilbert convexification therefore supplies, without an
abstract local-integral calculus, one common predictable limit and the exact
completed martingale identities on all joint coordinates. -/
theorem exists_intrinsicJointPassage_selectedMartingaleIntegral
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n)
      (cutoff : Nat -> Nat)
      (hEnergy : forall r, MemLp
        (intrinsicJointPassageSelectedIntegrand data w cutoff)
        (2 : ENNReal)
        ((intrinsicJointPassageSchedule base data).quadraticKernel r
          ).predictableEnergyMeasure),
      StrictMono cutoff ∧ forall r,
      ProcessIndistinguishable mu
        (finiteHorizonMartingaleIntegralProcess
          (intrinsicJointPassageSchedule base data).usualConditions
          ((intrinsicJointPassageSchedule base data).quadraticKernel r)
          ((intrinsicJointPassageSchedule base data).martingale r)
          ((intrinsicJointPassageSchedule base data).sourcePrefix r
            ).martingalePart_isRightContinuous
          ((intrinsicJointPassageSchedule base data).terminal_memLp r)
          (intrinsicJointPassageSelectedIntegrand data w cutoff)
          (intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff) (hEnergy r))
        (MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess data.martingaleLimit
            ((intrinsicJointPassageSchedule base data).localizer r))
          (fun _ => ((intrinsicJointPassageSchedule base data).horizon r :
            WithTop NNReal))) := by
  obtain ⟨w, cutoff, hCutoff, hLimit⟩ :=
    exists_intrinsicJointPassage_selectedIntegrand base data
  let hEnergy : forall r, MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageSchedule base data).quadraticKernel r
        ).predictableEnergyMeasure := fun r => (hLimit r).1
  refine ⟨w, cutoff, hEnergy, hCutoff, fun r => ?_⟩
  exact intrinsicJointPassageSelectedIntegrand_martingaleIntegral
    base data w cutoff hCutoff (fun r => ⟨(hLimit r).1, (hLimit r).2.2⟩) r

end LocalCompletedM2A

end FTAPTheorem42
