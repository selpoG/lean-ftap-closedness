/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualConvexCombination
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageSchedule

/-!
# Common Hilbert convexification on the intrinsic joint passages

The Mémín joint-passage schedule places every approximant martingale terminal
in the same countable family of `L²` spaces, with one finite bound per
coordinate.  Apply the existing Hilbert direct-sum convexification once to
these terminals.  The selected weights are then realized by the intrinsic
actual convex-combination calculus.

The final endpoint identifies each actual convexified stopped terminal with
the corresponding Hilbert-space convex combination.  Consequently one family
of actual forward convex combinations is strongly `L²`-Cauchy on every joint
coordinate.  No range realization of the limit is assumed.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The canonical `L²` representative of one approximant terminal on one
intrinsic joint-passage coordinate. -/
noncomputable def intrinsicJointPassageTerminalToLp
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (k n : Nat) : Lp Real 2 mu :=
  let target := intrinsicJointPassageSchedule base data
  let X := actualLocalL2CoordinateProcess
    (target.localizer n) (target.horizon n) (data.approximant k)
  let hX := (intrinsicJointPassage_approximantCoordinate_martingale_l2
    base data n k).2.1
  let hTerminal : MemLp (actualLocalL2TerminalCoordinate
      (target.localizer n) (target.horizon n) (data.approximant k))
      (2 : ENNReal) mu := by
    rw [<- actualLocalL2CoordinateProcess_horizon]
    exact hX
  hTerminal.toLp (actualLocalL2TerminalCoordinate
    (target.localizer n) (target.horizon n) (data.approximant k))

/-- The finite real terminal bound at one joint-passage coordinate. -/
noncomputable def intrinsicJointPassageTerminalBound
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) : Real :=
  (ENNReal.ofReal (cadlagPassageLevel n) +
    6 * eLpNorm data.gainEnvelope (2 : ENNReal) mu).toReal

/-- The canonical `Lp` representative agrees with the raw stopped terminal. -/
theorem intrinsicJointPassageTerminalToLp_coeFn_ae
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (k n : Nat) :
    ⇑(intrinsicJointPassageTerminalToLp base data k n) =ᵐ[mu]
      actualLocalL2TerminalCoordinate
        ((intrinsicJointPassageSchedule base data).localizer n)
        ((intrinsicJointPassageSchedule base data).horizon n)
        (data.approximant k) := by
  rw [intrinsicJointPassageTerminalToLp]
  exact MemLp.coeFn_toLp _

omit [F.IsRightContinuous] in
theorem intrinsicJointPassageTerminalBound_nonnegative
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) :
    0 <= intrinsicJointPassageTerminalBound data n :=
  ENNReal.toReal_nonneg

/-- The common Corollary 2.4 estimate becomes a norm bound on the canonical
terminal representatives. -/
theorem intrinsicJointPassageTerminalToLp_norm_le
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (k n : Nat) :
    ‖intrinsicJointPassageTerminalToLp base data k n‖ <=
      intrinsicJointPassageTerminalBound data n := by
  let target := intrinsicJointPassageSchedule base data
  let X := actualLocalL2CoordinateProcess
    (target.localizer n) (target.horizon n) (data.approximant k)
  let hX := (intrinsicJointPassage_approximantCoordinate_martingale_l2
    base data n k).2.1
  rw [intrinsicJointPassageTerminalToLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono
    (by
      rw [ENNReal.add_ne_top]
      exact ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top (by norm_num) data.gainEnvelope_memLp.eLpNorm_ne_top⟩)
    (by
      rw [<- actualLocalL2CoordinateProcess_horizon]
      exact (intrinsicJointPassage_approximantCoordinate_martingale_l2
        base data n k).2.2)

/-- A single family of tail weights makes the original approximant terminals
converge strongly in `L²` on every intrinsic joint-passage coordinate. -/
theorem exists_intrinsicJointPassage_commonTerminalConvexification
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n)
      (terminalLimit : Nat -> Lp Real 2 mu),
      forall r,
        Tendsto (fun n => (w n).applyVector (fun k =>
          intrinsicJointPassageTerminalToLp base data k r))
          atTop (nhds (terminalLimit r)) := by
  let B : Nat -> Real := intrinsicJointPassageTerminalBound data
  let Z : Nat -> forall r : Nat, Lp Real 2 mu := fun k r =>
    intrinsicJointPassageTerminalToLp base data k r
  obtain ⟨w, y, _hNormalized, hCoordinate⟩ :=
    DirectSumCoordinateControl.exists_common_tailConvexification_of_finite_coordinateBounds
      B Z
      (intrinsicJointPassageTerminalBound_nonnegative data)
      (intrinsicJointPassageTerminalToLp_norm_le base data)
  let terminalLimit : Nat -> Lp Real 2 mu := fun r =>
    (DirectSumCoordinateControl.geometricNormalization B r)⁻¹ • y r
  exact ⟨w, terminalLimit, fun r => by
    simpa only [B, Z, terminalLimit] using hCoordinate r⟩

/-- Realize one Hilbert weight row as an actual intrinsic strategy. -/
noncomputable def intrinsicJointPassageConvexifiedApproximant
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m) :
    ActualSIntegrableStrategy (realizationModel G) :=
  (actualConvexCombinationCalculus G).tailConvexCombination
    data.approximant w

omit [F.IsRightContinuous] in
/-- Centering and stopping commute pointwise with one finite convex row. -/
theorem intrinsicJointPassageConvexified_terminalCoordinate_eq_apply
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m)
    (tau : Omega -> WithTop NNReal) (T : NNReal) :
    actualLocalL2TerminalCoordinate tau T
        (intrinsicJointPassageConvexifiedApproximant data w) =
      w.apply (fun k => actualLocalL2TerminalCoordinate tau T
        (data.approximant k)) := by
  funext omega
  simp only [intrinsicJointPassageConvexifiedApproximant,
    SIntegrableActualConvexCombinationCalculus.tailConvexCombination,
    actualLocalL2TerminalCoordinate,
    MeasureTheory.stoppedProcess,
    SIntegrableStrategy.centeredMartingalePart,
    SIntegrableStrategy.tailConvexCombination_martingalePart_apply,
    TailConvexWeights.apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

omit [F.IsRightContinuous] in
/-- Centering and both stops commute pointwise with one finite convex row. -/
theorem intrinsicJointPassageConvexified_coordinateProcess_eq_apply
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m)
    (tau : Omega -> WithTop NNReal) (T : NNReal) :
    actualLocalL2CoordinateProcess tau T
        (intrinsicJointPassageConvexifiedApproximant data w) =
      fun t => w.apply (fun k =>
        actualLocalL2CoordinateProcess tau T (data.approximant k) t) := by
  funext t omega
  simp only [intrinsicJointPassageConvexifiedApproximant,
    SIntegrableActualConvexCombinationCalculus.tailConvexCombination,
    actualLocalL2CoordinateProcess,
    MeasureTheory.stoppedProcess,
    SIntegrableStrategy.centeredMartingalePart,
    SIntegrableStrategy.tailConvexCombination_martingalePart_apply,
    TailConvexWeights.apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The terminal of an actual convexified approximant is square-integrable
on every coordinate of the fixed joint-passage schedule. -/
theorem intrinsicJointPassageConvexified_terminal_memLp
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m) (n : Nat) :
    MemLp (actualLocalL2TerminalCoordinate
      ((intrinsicJointPassageSchedule base data).localizer n)
      ((intrinsicJointPassageSchedule base data).horizon n)
      (intrinsicJointPassageConvexifiedApproximant data w))
      (2 : ENNReal) mu := by
  let target := intrinsicJointPassageSchedule base data
  let Z : Nat -> Lp Real 2 mu := fun k =>
    intrinsicJointPassageTerminalToLp base data k n
  let f : Nat -> Omega -> Real := fun k =>
    actualLocalL2TerminalCoordinate
      (target.localizer n) (target.horizon n) (data.approximant k)
  have hCoe : ⇑(w.applyVector Z) =ᵐ[mu] w.apply f :=
    w.applyVector_coeFn_ae Z f fun k =>
      intrinsicJointPassageTerminalToLp_coeFn_ae base data k n
  have hConvex :=
    intrinsicJointPassageConvexified_terminalCoordinate_eq_apply data w (target.localizer n)
      (target.horizon n)
  apply MemLp.ae_eq _ (MeasureTheory.Lp.memLp (w.applyVector Z))
  filter_upwards [hCoe] with omega hCoeOmega
  rw [hCoeOmega]
  exact (congrFun hConvex omega).symm

/-- The canonical `Lp` terminal of the actual convexified strategy is the
Hilbert-space convex combination selected from the original terminals. -/
theorem intrinsicJointPassageConvexified_terminalToLp_eq_applyVector
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m) (n : Nat) :
    (intrinsicJointPassageConvexified_terminal_memLp base data w n).toLp
        (actualLocalL2TerminalCoordinate
          ((intrinsicJointPassageSchedule base data).localizer n)
          ((intrinsicJointPassageSchedule base data).horizon n)
          (intrinsicJointPassageConvexifiedApproximant data w)) =
      w.applyVector (fun k =>
        intrinsicJointPassageTerminalToLp base data k n) := by
  let target := intrinsicJointPassageSchedule base data
  let Z : Nat -> Lp Real 2 mu := fun k =>
    intrinsicJointPassageTerminalToLp base data k n
  let f : Nat -> Omega -> Real := fun k =>
    actualLocalL2TerminalCoordinate
      (target.localizer n) (target.horizon n) (data.approximant k)
  have hCoe : ⇑(w.applyVector Z) =ᵐ[mu] w.apply f :=
    w.applyVector_coeFn_ae Z f fun k =>
      intrinsicJointPassageTerminalToLp_coeFn_ae base data k n
  have hConvex :=
    intrinsicJointPassageConvexified_terminalCoordinate_eq_apply data w (target.localizer n)
      (target.horizon n)
  apply Lp.ext
  filter_upwards [
    (intrinsicJointPassageConvexified_terminal_memLp
      base data w n).coeFn_toLp,
    hCoe] with omega hTerminalOmega hCoeOmega
  rw [hTerminalOmega, hCoeOmega]
  exact congrFun hConvex omega

/-- An actual convexified approximant still has a true martingale coordinate
on the fixed joint-passage schedule. -/
theorem intrinsicJointPassageConvexified_coordinate_martingale
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m) (n : Nat) :
    Martingale
      (actualLocalL2CoordinateProcess
        ((intrinsicJointPassageSchedule base data).localizer n)
        ((intrinsicJointPassageSchedule base data).horizon n)
        (intrinsicJointPassageConvexifiedApproximant data w)) F mu := by
  let target := intrinsicJointPassageSchedule base data
  let X : Nat -> Process Omega := fun k =>
    actualLocalL2CoordinateProcess
      (target.localizer n) (target.horizon n) (data.approximant k)
  rw [intrinsicJointPassageConvexified_coordinateProcess_eq_apply]
  change Martingale (fun t omega =>
    ∑ k ∈ w.support, w.weight k * X k t omega) F mu
  induction w.support using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      convert martingale_zero Real F mu using 1
  | @insert k support hk ih =>
      have hTerm : Martingale (fun t omega => w.weight k * X k t omega)
          F mu := by
        have hTerm' :=
          (intrinsicJointPassage_approximantCoordinate_martingale_l2
            base data n k).1.smul (w.weight k)
        convert hTerm' using 1
      simp only [Finset.sum_insert hk]
      have hAdd := hTerm.add ih
      convert hAdd using 1

/-- Every actual Hilbert convexification retains the target energy
membership and completed martingale process semantics. -/
theorem intrinsicJointPassageConvexified_martingaleSemantics
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    {m : Nat} (w : TailConvexWeights m) (n : Nat) :
    let target := intrinsicJointPassageSchedule base data
    exists hEnergy : MemLp
        (Function.uncurry
          (intrinsicJointPassageConvexifiedApproximant data w).val.integrand)
        (2 : ENNReal) (target.quadraticKernel n).predictableEnergyMeasure,
      ProcessIndistinguishable mu
        (actualLocalL2CoordinateProcess
          (target.localizer n) (target.horizon n)
          (intrinsicJointPassageConvexifiedApproximant data w))
        (BoundedMartingaleQuadraticEnergy.Data.finiteHorizonMartingaleIntegralProcess
          target.usualConditions (target.quadraticKernel n)
          (target.martingale n)
          (target.sourcePrefix n).martingalePart_isRightContinuous
          (target.terminal_memLp n)
          (Function.uncurry
            (intrinsicJointPassageConvexifiedApproximant data w).val.integrand)
          (intrinsicJointPassageConvexifiedApproximant data w).val.integrand_isPredictable
            hEnergy) := by
  let target := intrinsicJointPassageSchedule base data
  have hTerminal : MemLp
      (actualLocalL2CoordinateProcess
        (target.localizer n) (target.horizon n)
        (intrinsicJointPassageConvexifiedApproximant data w)
        (target.horizon n)) (2 : ENNReal) mu := by
    rw [actualLocalL2CoordinateProcess_horizon]
    exact intrinsicJointPassageConvexified_terminal_memLp base data w n
  exact actual_boundedCoordinate_martingaleSemantics  target n
    (intrinsicJointPassageConvexifiedApproximant data w)
    (intrinsicJointPassageConvexified_coordinate_martingale
      base data w n)
    hTerminal

/-- The actual strategy sequence associated with one family of Hilbert tail
weights. -/
noncomputable def intrinsicJointPassageConvexifiedSequence
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n) (n : Nat) :
    ActualSIntegrableStrategy (realizationModel G) :=
  intrinsicJointPassageConvexifiedApproximant data (w n)

/-- The common Hilbert weights are realized by actual intrinsic strategies,
and their stopped terminals converge strongly in `L²` on every joint
coordinate. -/
theorem exists_intrinsicJointPassage_actualTerminalConvexification
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists (w : forall n, TailConvexWeights n)
      (terminalLimit : Nat -> Lp Real 2 mu),
      forall r,
        Tendsto (fun n =>
          (intrinsicJointPassageConvexified_terminal_memLp
            base data (w n) r).toLp
              (actualLocalL2TerminalCoordinate
                ((intrinsicJointPassageSchedule base data).localizer r)
                ((intrinsicJointPassageSchedule base data).horizon r)
                (intrinsicJointPassageConvexifiedSequence data w n)))
          atTop (nhds (terminalLimit r)) := by
  obtain ⟨w, terminalLimit, hTerminal⟩ :=
    exists_intrinsicJointPassage_commonTerminalConvexification base data
  refine ⟨w, terminalLimit, fun r => ?_⟩
  simpa only [intrinsicJointPassageConvexifiedSequence,
    intrinsicJointPassageConvexified_terminalToLp_eq_applyVector] using
      hTerminal r

/-- In particular, the actual convexified terminals are `L²`-Cauchy on all
joint coordinates under the same weights. -/
theorem exists_intrinsicJointPassage_actualTerminalCauchy
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    exists w : forall n, TailConvexWeights n,
      forall r, CauchySeq (fun n =>
        (intrinsicJointPassageConvexified_terminal_memLp
          base data (w n) r).toLp
            (actualLocalL2TerminalCoordinate
              ((intrinsicJointPassageSchedule base data).localizer r)
              ((intrinsicJointPassageSchedule base data).horizon r)
              (intrinsicJointPassageConvexifiedSequence data w n))) := by
  obtain ⟨w, terminalLimit, hTerminal⟩ :=
    exists_intrinsicJointPassage_actualTerminalConvexification base data
  exact ⟨w, fun r => (hTerminal r).cauchySeq⟩

end LocalCompletedM2A

end FTAPTheorem42
