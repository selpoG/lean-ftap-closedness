/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.Witness
import FTAPTheorem42.Stochastic.Topology.J1.CommonCost

/-! # Summable exact representatives from summable strict-prefix j1 costs -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Nat → Process Ω} {tau : Ω → NNReal} {T : NNReal}

theorem exists_summable_prelocalSupExactRepresentations
    (hUsual : Filtration.UsualConditions mu F)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T)
    (hSum : (∑' k, prelocalSemimartingaleJ1 (X k) F mu
      (fun w => (tau w : WithTop NNReal))) ≠ ∞) :
    ∃ R : ∀ k, EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu) (X k) tau T,
      (∑' k, prelocalH1SupWitnessCost (R k).witness) ≤
        6 * ((∑' k, prelocalSemimartingaleJ1 (X k) F mu
          (fun w => (tau w : WithTop NNReal))) + 1) ∧
      (∑' k, prelocalH1SupWitnessCost (R k).witness) ≠ ∞ := by
  let c : Nat → ENNReal := fun k =>
    prelocalSemimartingaleJ1 (X k) F mu (fun w => (tau w : WithTop NNReal))
  let e : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have he : ∀ k, 0 < e k := fun _ =>
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  have hc : ∀ k, c k ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hSum (ENNReal.le_tsum (f := c) k)
  have hChoice : ∀ k, ∃ R : EmeryPrelocalH1SupExactRepresentation
      (F := F) (mu := mu) (X k) tau T,
      prelocalH1SupWitnessCost R.witness < 6 * (c k + e k) := fun k =>
    exists_prelocalSupExactRepresentation_of_prelocalJ1_lt hUsual hTau hTauT
      (ENNReal.lt_add_right (hc k) (he k).ne')
  choose R hR using hChoice
  have heSum : (∑' k, e k) = 1 := by
    simp only [e]
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hBound : (∑' k, prelocalH1SupWitnessCost (R k).witness) ≤
      6 * ((∑' k, c k) + 1) := by
    calc
      _ ≤ ∑' k, 6 * (c k + e k) := ENNReal.tsum_le_tsum (fun k => (hR k).le)
      _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, heSum]
  exact ⟨R, hBound, ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hSum, by norm_num⟩)) hBound⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Common summable witnesses from clock and stopping-jump control -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

/-- The jump cost ranges over all bounded stopping times, not just deterministic times. -/
noncomputable def boundedStoppingJumpCost (N : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) : ENNReal :=
  ⨆ (T : NNReal) (tau : Ω → NNReal)
    (_ : IsStoppingTime F (fun w => (tau w : WithTop NNReal))) (_ : ∀ w, tau w ≤ T),
      ∫⁻ w, ENNReal.ofReal |processLeftJump N (tau w) w| ∂mu

theorem lintegral_jump_le_boundedStoppingJumpCost {N : Process Ω}
    {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    (∫⁻ w, ENNReal.ofReal |processLeftJump N (tau w) w| ∂mu) ≤
      boundedStoppingJumpCost N F mu :=
  le_iSup_of_le T (le_iSup_of_le tau (le_iSup_of_le hTau (le_iSup_of_le hTauT le_rfl)))

theorem J1Decomposition.exists_common_summable_prelocalSupExactRepresentations
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞)
    (hJump : (∑' k, boundedStoppingJumpCost (D k).N F mu) ≠ ∞) :
    ∃ tau : Nat → Ω → NNReal,
      IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
      (∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
        (fun w => (tau r w : WithTop NNReal))) ≤
          (r + 1 : Nat) + ∑' k, boundedStoppingJumpCost (D k).N F mu ∧
        ∃ R : ∀ k, EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu)
            (Z k) (tau r) ((r + 1 : Nat) : NNReal),
          (∑' k, prelocalH1SupWitnessCost (R k).witness) ≤
            6 * ((r + 1 : Nat) + (∑' k, boundedStoppingJumpCost (D k).N F mu) + 1) ∧
          (∑' k, prelocalH1SupWitnessCost (R k).witness) ≠ ∞ := by
  obtain ⟨tau, hLoc, hT, hBound⟩ :=
    J1Decomposition.exists_common_localizers_prelocal_cost_bound hUsual D Q hCap
  refine ⟨tau, hLoc, hT, ?_⟩
  intro r
  have hCost : (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
      (fun w => (tau r w : WithTop NNReal))) ≤
      (r + 1 : Nat) + ∑' k, boundedStoppingJumpCost (D k).N F mu := by
    apply (hBound r).trans
    exact add_le_add le_rfl (ENNReal.tsum_le_tsum (fun _ =>
      lintegral_jump_le_boundedStoppingJumpCost (hLoc.isStoppingTime r) (hT r)))
  have hFinite : (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
      (fun w => (tau r w : WithTop NNReal))) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hJump⟩) hCost
  obtain ⟨R, hR, hRFinite⟩ := exists_summable_prelocalSupExactRepresentations
    hUsual (hLoc.isStoppingTime r) (hT r) hFinite
  exact ⟨hCost, R, hR.trans
    (mul_le_mul le_rfl (add_le_add hCost le_rfl) bot_le bot_le), hRFinite⟩

end FTAPTheorem42
