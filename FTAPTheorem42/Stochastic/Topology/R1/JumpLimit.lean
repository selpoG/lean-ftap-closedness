/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.Triangle

/-! # Fatou control of the stopping-jump coordinate under locally uniform convergence -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

theorem J1Decomposition.jumpCost_le_liminf_of_locallyUniform
    {Z : Nat → Process Ω} (D : ∀ n, J1Decomposition (Z n) F mu)
    {X : Process Ω} (hLeft : ProcessHasLeftLimits X)
    (hU : ∀ᵐ w ∂mu, ∀ T : NNReal, TendstoUniformlyOn
      (fun n t => (D n).N t w) (X · w) atTop (Icc 0 T)) :
    boundedStoppingJumpCost X F mu ≤
      liminf (fun n => boundedStoppingJumpCost (D n).N F mu) atTop := by
  apply iSup_le
  intro T
  apply iSup_le
  intro tau
  apply iSup_le
  intro hTau
  apply iSup_le
  intro hTauT
  let J := fun n w => ENNReal.ofReal |processLeftJump (D n).N (tau w) w|
  have hJ : ∀ n, Measurable (J n) := fun n => (D n).measurable_sampledJump hTau hTauT
  have hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => J n w) atTop
      (𝓝 (ENNReal.ofReal |processLeftJump X (tau w) w|)) := by
    filter_upwards [hU] with w hw
    let P := fun n => stoppedProcess (D n).N (fun _ => (T : WithTop NNReal))
    let Y := stoppedProcess X (fun _ => (T : WithTop NNReal))
    have hUniform : TendstoUniformly (fun n t => P n t w) (Y · w) atTop := by
      have h := ((hw T).comp (fun t => min t T)).mono
        (show univ ⊆ (fun t => min t T) ⁻¹' Icc 0 T from
          fun _ _ => ⟨bot_le, min_le_right _ _⟩)
      simpa only [tendstoUniformlyOn_univ, Function.comp_def, P, Y, stoppedProcess_const_apply]
        using h
    have hL := tendsto_leftLim_of_tendstoUniformly (fun n t => P n t w) (Y · w) hUniform
      (fun n => ((D n).leftN.stoppedProcess _) w) (tau w)
    have h := ENNReal.tendsto_ofReal (((hUniform.tendsto_at (tau w)).sub hL).abs)
    change Tendsto (fun n => ENNReal.ofReal |processLeftJump (P n) (tau w) w|) atTop
      (𝓝 (ENNReal.ofReal |processLeftJump Y (tau w) w|)) at h
    simpa only [P, Y, J, processLeftJump_stoppedProcess_eq_of_le (D _).N (D _).leftN
      (fun _ => (T : WithTop NNReal)) (tau w) w (WithTop.coe_le_coe.mpr (hTauT w)),
      processLeftJump_stoppedProcess_eq_of_le X hLeft (fun _ => (T : WithTop NNReal)) (tau w) w
        (WithTop.coe_le_coe.mpr (hTauT w))] using h
  calc
    _ = ∫⁻ w, liminf (fun n => J n w) atTop ∂mu :=
      lintegral_congr_ae (hLimit.mono (fun _ h => h.liminf_eq.symm))
    _ ≤ liminf (fun n => ∫⁻ w, J n w ∂mu) atTop :=
      lintegral_liminf_le' (fun n => (hJ n).aemeasurable)
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall
      (fun _ => lintegral_jump_le_boundedStoppingJumpCost hTau hTauT))

theorem J1Decomposition.jumpCost_series_le
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    {X : Process Ω} (hLeft : ProcessHasLeftLimits X)
    (hU : ∀ᵐ w ∂mu, ∀ T : NNReal, TendstoUniformlyOn
      (fun n t => ∑ k ∈ Finset.range n, (D k).N t w) (X · w) atTop (Icc 0 T)) :
    boundedStoppingJumpCost X F mu ≤ ∑' k, boundedStoppingJumpCost (D k).N F mu := by
  let P : Nat → (Σ Y : Process Ω, J1Decomposition Y F mu) :=
    Nat.rec ⟨Z 0, D 0⟩ (fun n p => ⟨p.1 + Z (n + 1), p.2.add (D (n + 1))⟩)
  have hN : ∀ n t w, (P n).2.N t w = ∑ k ∈ Finset.range (n + 1), (D k).N t w := by
    intro n t w
    induction n with
    | zero => simp [P]
    | succ n ih =>
      change (P n).2.N t w + (D (n + 1)).N t w = _
      rw [Finset.sum_range_succ _ (n + 1), ih]
  have hCost : ∀ n, boundedStoppingJumpCost (P n).2.N F mu ≤
      ∑ k ∈ Finset.range (n + 1), boundedStoppingJumpCost (D k).N F mu := by
    intro n
    induction n with
    | zero => simp [P]
    | succ n ih =>
      apply ((P n).2.add_jumpCost_le (D (n + 1))).trans
      rw [Finset.sum_range_succ]
      exact add_le_add ih le_rfl
  apply (J1Decomposition.jumpCost_le_liminf_of_locallyUniform (fun n => (P n).2) hLeft ?_).trans
  · exact liminf_le_of_frequently_le' (Eventually.of_forall
      (fun n => (hCost n).trans (ENNReal.sum_le_tsum _))).frequently
  · filter_upwards [hU] with w hw
    intro T
    have h : TendstoUniformlyOn (fun n t => ∑ k ∈ Finset.range (n + 1), (D k).N t w)
        (X · w) atTop (Icc 0 T) := by
      intro u hu
      exact (tendsto_add_atTop_nat 1).eventually (hw T u hu)
    exact h.congr (Eventually.of_forall (fun n t _ => (hN n t w).symm))

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Stopping-jump control of the tails of a martingale series -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.jumpCost_series_tail_le
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    {X : Process Ω} (hLeft : ProcessHasLeftLimits X)
    (hU : ∀ᵐ w ∂mu, ∀ T : NNReal, TendstoUniformlyOn
      (fun n t => ∑ k ∈ Finset.range n, (D k).N t w) (X · w) atTop (Icc 0 T))
    (n : Nat) :
    boundedStoppingJumpCost (fun t w => X t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu ≤
      ∑' k, boundedStoppingJumpCost (D (k + n)).N F mu := by
  have hPartialLeft : ∀ n, ProcessHasLeftLimits
      (fun t w => ∑ k ∈ Finset.range n, (D k).N t w) := by
    intro n
    induction n with
    | zero =>
      intro w t
      simp only [Finset.range_zero, Finset.sum_empty]
      exact tendsto_leftLim_of_tendsto ⟨0, tendsto_const_nhds⟩
    | succ n ih =>
      simpa only [Finset.sum_range_succ] using ih.add (D n).leftN
  apply J1Decomposition.jumpCost_series_le (fun k => D (k + n))
    (hLeft.sub (hPartialLeft n))
  filter_upwards [hU] with w hw
  intro T
  have hShift : TendstoUniformlyOn
      (fun m t => ∑ k ∈ Finset.range (m + n), (D k).N t w) (X · w) atTop (Icc 0 T) := by
    intro u hu
    exact (tendsto_add_atTop_nat n).eventually (hw T u hu)
  have hConst : TendstoUniformlyOn
      (fun (_ : Nat) t => ∑ k ∈ Finset.range n, (D k).N t w)
      (fun t => ∑ k ∈ Finset.range n, (D k).N t w) atTop (Icc 0 T) := by
    intro u hu
    exact Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hu)
  apply (hShift.sub hConst).congr
  apply Eventually.of_forall
  intro m t _
  dsimp only [Pi.sub_apply]
  rw [Nat.add_comm m n, Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm n k])

end FTAPTheorem42
