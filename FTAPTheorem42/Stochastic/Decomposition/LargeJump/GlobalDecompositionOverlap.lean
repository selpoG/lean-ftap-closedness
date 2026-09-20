/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.GlobalDecomposition

/-! # Horizon consistency of the finite-large-jump source -/

namespace FTAPTheorem42.FiniteLargeJumpProcess

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

variable {Ω : Type*}

/-- Stopping the larger-horizon large-jump process at the smaller horizon
gives exactly the smaller-horizon process. The proof compares the finite
sets of jump times, independently of their enumerations. -/
theorem process_min_horizon
    {X : Process Ω} {c : Real} {U T : NNReal}
    (hRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (hUT : U ≤ T) :
    (fun t omega => process X c T (min t U) omega) = process X c U := by
  classical
  funext t omega
  rw [process_eq_path hRight hLeft hc, process_eq_path hRight hLeft hc]
  let DT := pathData X c T hRight hLeft hc omega
  let DU := pathData X c U hRight hLeft hc omega
  have hSub : DU.times ⊆ DT.times := by
    intro s hs
    have h := (DU.times_mem s).mp hs
    exact (DT.times_mem s).mpr ⟨⟨h.1.1, h.1.2.trans hUT⟩, h.2⟩
  change (∑ s ∈ DT.times, if s ≤ min t U then cadlagLeftJump (X · omega) s else 0) =
    ∑ s ∈ DU.times, if s ≤ t then cadlagLeftJump (X · omega) s else 0
  calc
    _ = ∑ s ∈ DU.times, if s ≤ min t U then cadlagLeftJump (X · omega) s else 0 := by
      symm
      apply Finset.sum_subset hSub
      intro s hsT hsU
      have hNot : ¬s ≤ U := by
        intro hs
        have h := (DT.times_mem s).mp hsT
        exact hsU ((DU.times_mem s).mpr ⟨⟨h.1.1, hs⟩, h.2⟩)
      exact ite_eq_right (fun h => hNot (le_min_iff.mp h).2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsU := ((DU.times_mem s).mp hs).1.2
      simp only [le_min_iff, hsU, and_true]

end FTAPTheorem42.FiniteLargeJumpProcess

namespace FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily

/-!
## Horizon overlap of the global large-jump decomposition

Both projections are stopped at the smaller horizon, so their difference
has globally bounded variation. Source consistency makes this predictable
difference a local martingale. Source-free rigidity and the exact zero
initial values identify the projections, then the exact residuals and the
bounded-jump components, on a common full-measure set.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

open PredictableFiniteVariationLocalMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real} {U T : NNReal}
  {hX : LocalMartingale X F mu}
  {familyU : FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu) X c U}
  {familyT : FiniteLargeJumpValueTruncationFamily (F := F) (mu := mu) X c T}
  {closedU : FiniteLargeJumpClosedStopFamily hX familyU}
  {closedT : FiniteLargeJumpClosedStopFamily hX familyT}
  {hUsual : Filtration.UsualConditions mu F}

/-- All three components from two independently constructed global
large-jump decompositions agree after stopping at the smaller horizon.
No compatibility of their internal localizing schedules is assumed. -/
theorem GlobalDecompositionData.stopped_components_overlap
    (dU : GlobalDecompositionData hX familyU closedU hUsual)
    (dT : GlobalDecompositionData hX familyT closedT hUsual)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hc : 0 < c) (hUT : U ≤ T) :
    ∀ᵐ omega ∂mu, ∀ t,
      dT.P (min t U) omega = dU.P (min t U) omega ∧
      dT.Q (min t U) omega = dU.Q (min t U) omega ∧
      X (min t U) omega - dT.Q (min t U) omega =
        X (min t U) omega - dU.Q (min t U) omega := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  by_cases hU : 0 < U
  swap
  · have hUZero : U = 0 := le_antisymm (le_of_not_gt hU) bot_le
    apply Eventually.of_forall
    intro omega t
    have hMin : min t U = 0 := by rw [hUZero]; exact min_eq_right bot_le
    rw [hMin]
    simp only [dT.P_zero, dU.P_zero, dT.Q_zero, dU.Q_zero, Pi.zero_apply,
      and_self]
  let A : Process Ω := fun t omega => dT.P (min t U) omega - dU.P (min t U) omega
  let M : Process Ω := fun t omega => dU.Q (min t U) omega - dT.Q (min t U) omega
  have hSource : ∀ t omega,
      FiniteLargeJumpProcess.process X c T (min t U) omega =
        FiniteLargeJumpProcess.process X c U (min t U) omega := by
    intro t omega
    have hBig := congrFun (congrFun
      (FiniteLargeJumpProcess.process_min_horizon hXRight hXLeft hc hUT) t) omega
    have hSmall := congrFun (congrFun
      (FiniteLargeJumpProcess.process_min_horizon hXRight hXLeft hc (le_refl U)) t) omega
    exact hBig.trans hSmall.symm
  have hAM : ProcessIndistinguishable mu M A := by
    apply Eventually.of_forall
    intro omega t
    dsimp [M, A]
    rw [dU.Q_definition, dT.Q_definition]
    dsimp only
    rw [hSource t omega]
    ring
  have hAPred : IsStronglyPredictable F A :=
    (IsStronglyPredictable.deterministicallyStopped_of_pos dT.P_isStronglyPredictable U hU).sub
      (IsStronglyPredictable.deterministicallyStopped_of_pos dU.P_isStronglyPredictable U hU)
  have hARight : ∀ omega t, ContinuousWithinAt (A · omega) (Ici t) t := by
    intro omega t
    exact (FiniteVariationStoppedPath.rightContinuous_stopAt
      (dT.P · omega) (dT.P_rightContinuous omega) U t).sub
      (FiniteVariationStoppedPath.rightContinuous_stopAt
        (dU.P · omega) (dU.P_rightContinuous omega) U t)
  have hAVar : ∀ omega, BoundedVariationOn (A · omega) univ := by
    intro omega
    simpa only [A, sub_eq_add_neg, FiniteVariationStoppedPath.stopAt] using boundedVariationOn_add
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (dT.P_locallyBoundedVariation omega) U)
      (boundedVariationOn_neg
        (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
          (dU.P_locallyBoundedVariation omega) U))
  have hMLocal : LocalMartingale M F mu := by
    have hUStopped := dU.Q_isLocalMartingale.deterministicallyStopped dU.Q_rightContinuous U
    have hTStopped := dT.Q_isLocalMartingale.deterministicallyStopped dT.Q_rightContinuous U
    simpa only [M, sub_eq_add_neg] using
      hUStopped.add_of_rightContinuous hTStopped.neg
          (fun omega t => FiniteVariationStoppedPath.rightContinuous_stopAt
            (dU.Q · omega) (dU.Q_rightContinuous omega) U t)
          (fun omega t => (FiniteVariationStoppedPath.rightContinuous_stopAt
            (dT.Q · omega) (dT.Q_rightContinuous omega) U t).neg)
  have hALocal : LocalMartingale A F mu :=
    hMLocal.congr_indistinguishable hAPred.stronglyAdapted hARight hAM
  have hAZero : A 0 = 0 := by
    funext omega
    change dT.P (min (0 : NNReal) U) omega - dU.P (min (0 : NNReal) U) omega = 0
    rw [show min (0 : NNReal) U = 0 from min_eq_left bot_le]
    simp only [dT.P_zero, dU.P_zero, Pi.zero_apply, sub_self]
  have hZero :=
    indistinguishable_zero_of_predictableFiniteVariationLocalMartingale
      hUsual A hALocal hAPred hARight hAVar hAZero
  filter_upwards [hZero, hAM] with omega hZeroOmega hAMOmega
  intro t
  have hP := hZeroOmega t
  have hQ := hAMOmega t
  change dT.P (min t U) omega - dU.P (min t U) omega = 0 at hP
  change dU.Q (min t U) omega - dT.Q (min t U) omega =
    dT.P (min t U) omega - dU.P (min t U) omega at hQ
  refine ⟨sub_eq_zero.mp hP, ?_, ?_⟩ <;> linarith

end FTAPTheorem42.HorizonFactorialGrid.FiniteLargeJumpClosedStopFamily
