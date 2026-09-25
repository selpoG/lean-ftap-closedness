/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableDebut
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Foretelling predictable stopping-time graphs

This module proves the predictable section theorem in the form needed for
Lemma 4.7: under the usual conditions, a finite stopping time whose graph is
predictable has a foretelling sequence.  The graph is approximated from
inside by countable intersections of the interval algebra.  Their debuts are
then combined by a summable-error argument.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableGraphForetelling

/-- Summable error budget for the predictable-section approximations. -/
noncomputable def errorBudget (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (n + 1)

theorem errorBudget_pos (n : ℕ) : 0 < errorBudget n := by
  unfold errorBudget
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _

theorem tsum_errorBudget_lt_top :
    ∑' n, errorBudget n < ⊤ := by
  unfold errorBudget
  rw [ENNReal.tsum_geometric_add_one]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (by norm_num)
  · rw [ENNReal.inv_lt_top]
    exact tsub_pos_of_lt ENNReal.one_half_lt_one

omit [MeasurableSpace Ω] in
theorem runningMinTarget_le
    {τ : ℕ → Ω → WithTop ℝ≥0} {n k : ℕ} (hkn : k ≤ n) (ω : Ω) :
    StoppingTimeForetelling.runningMinTarget τ n ω ≤ τ k ω := by
  induction n with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      exact le_rfl
  | succ n ih =>
      rw [StoppingTimeForetelling.runningMinTarget]
      by_cases hk : k = n + 1
      · subst k
        exact min_le_right _ _
      · exact (min_le_left _ _).trans
          (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hkn hk)))

omit [MeasurableSpace Ω] in
theorem le_runningMinTarget
    {τ : ℕ → Ω → WithTop ℝ≥0} {s : WithTop ℝ≥0}
    (hs : ∀ n, s ≤ τ n ω) (n : ℕ) :
    s ≤ StoppingTimeForetelling.runningMinTarget τ n ω := by
  induction n with
  | zero => exact hs 0
  | succ n ih =>
      rw [StoppingTimeForetelling.runningMinTarget]
      exact le_min ih (hs (n + 1))

/-- A genuinely predictable finite stopping time is foretold. -/
noncomputable def IsPredictableStoppingTime.foretelling
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {τ : Ω → ℝ≥0} (hτ : IsPredictableStoppingTime ℱ τ) :
    StoppingTimeForetelling ℱ (fun ω => (τ ω : WithTop ℝ≥0)) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let graphMeasure : Measure (ℝ≥0 × Ω) :=
    Measure.map (stoppingGraphMap τ) μ
  letI : IsFiniteMeasure graphMeasure :=
    Measure.isFiniteMeasure_map μ (stoppingGraphMap τ)
  have hGraphMap : Measurable (stoppingGraphMap τ) :=
    IsStoppingTime.measurable_stoppingGraphMap_predictable hτ.isStoppingTime
  have hGraphMeas : MeasurableSet (finiteStoppingTimeGraph τ) :=
    hτ.measurableSet_graph
  have hApprox : ∀ n, ∃ B : Set (ℝ≥0 × Ω),
      SetAlgebraInnerApproximation.IsCountableInter
          (PredictableIntervalAlgebra.sets ℱ) B ∧
        B ⊆ finiteStoppingTimeGraph τ ∧
        graphMeasure (finiteStoppingTimeGraph τ \ B) < errorBudget n := by
    intro n
    exact SetAlgebraInnerApproximation.exists_countableInter_subset_measure_sdiff_lt
      graphMeasure
        (PredictableIntervalAlgebra.isSetAlgebra_sets ℱ)
        (PredictableIntervalAlgebra.generateFrom_sets ℱ).symm
        hGraphMeas (errorBudget_pos n)
  choose B hBCount hBGraph hBError using hApprox
  choose C hCSets hBC using fun n => hBCount n
  choose L hL using fun n k => hCSets n k
  have hBEq : ∀ n, B n =
      ⋂ k, PredictableIntervalAlgebra.carrier (L n k) := by
    intro n
    rw [hBC n]
    congr with k
    simp only [hL n k]
  have hBMeas : ∀ n, MeasurableSet (B n) := by
    intro n
    rw [hBEq n]
    apply MeasurableSet.iInter
    intro k
    exact PredictableIntervalAlgebra.measurableSet_of_mem_sets
      ⟨L n k, rfl⟩
  let data : ∀ n, PredictableDebut.CountableIntersectionDebutData
      μ ℱ (L n) := fun n =>
    PredictableDebut.countableIntersectionDebutData hUsual (L n)
  let S : ℕ → Ω → WithTop ℝ≥0 := fun n =>
    PredictableIntervalAlgebra.debut
      (⋂ k, PredictableIntervalAlgebra.carrier (L n k))
  let R : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
    if stoppingGraphMap τ ω ∈ B n then
      (τ ω : WithTop ℝ≥0) else ⊤
  have hSEqR : ∀ n, S n =ᵐ[μ] R n := by
    intro n
    filter_upwards [(data n).attained] with ω hattained
    by_cases hmem : stoppingGraphMap τ ω ∈ B n
    · have hmem' : (τ ω, ω) ∈
          ⋂ k, PredictableIntervalAlgebra.carrier (L n k) := by
        rwa [← hBEq n]
      have hSLe : S n ω ≤ (τ ω : WithTop ℝ≥0) :=
        PredictableIntervalAlgebra.debut_le_of_mem hmem'
      have hSFinite : S n ω ≠ ⊤ := by
        intro htop
        rw [htop] at hSLe
        exact (not_le_of_gt (WithTop.coe_lt_top (τ ω))) hSLe
      have hdebutMem := hattained hSFinite
      have hdebutB : ((S n ω).untop hSFinite, ω) ∈ B n := by
        rwa [hBEq n]
      have hdebutGraph := hBGraph n hdebutB
      have hcoord : (S n ω).untop hSFinite = τ ω := hdebutGraph
      simp only [R, ite_eq_left hmem]
      calc
        S n ω = ((S n ω).untop hSFinite : WithTop ℝ≥0) :=
          (WithTop.coe_untop _ hSFinite).symm
        _ = (τ ω : WithTop ℝ≥0) := congrArg WithTop.some hcoord
    · have hSTop : S n ω = ⊤ := by
        by_contra hSFinite
        have hdebutMem := hattained hSFinite
        have hdebutB : ((S n ω).untop hSFinite, ω) ∈ B n := by
          rwa [hBEq n]
        have hdebutGraph := hBGraph n hdebutB
        have hcoord : (S n ω).untop hSFinite = τ ω := hdebutGraph
        apply hmem
        change (τ ω, ω) ∈ B n
        rw [← hcoord]
        exact hdebutB
      simp only [R, ite_eq_right hmem]
      exact hSTop
  have hRForetelling : ∀ n, StoppingTimeForetelling ℱ (R n) := fun n =>
    StoppingTimeForetelling.congr_ae hUsual (data n).foretelling (hSEqR n)
  let failure : ℕ → Set Ω := fun n => {ω | R n ω = ⊤}
  have hFailureEq : ∀ n, failure n =
      stoppingGraphMap τ ⁻¹' (finiteStoppingTimeGraph τ \ B n) := by
    intro n
    ext ω
    simp only [failure, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff]
    have hgraph : stoppingGraphMap τ ω ∈ finiteStoppingTimeGraph τ := by
      simp [stoppingGraphMap, finiteStoppingTimeGraph]
    simp only [hgraph, true_and]
    by_cases hmem : stoppingGraphMap τ ω ∈ B n
    · simp only [R, ite_eq_left hmem, WithTop.coe_ne_top, hmem, not_true_eq_false]
    · simp only [R, ite_eq_right hmem, hmem, not_false_eq_true, eq_self]
  have hFailureBound : ∀ n, μ (failure n) ≤ errorBudget n := by
    intro n
    calc
      μ (failure n) =
          μ (stoppingGraphMap τ ⁻¹'
            (finiteStoppingTimeGraph τ \ B n)) := by rw [hFailureEq n]
      _ = graphMeasure (finiteStoppingTimeGraph τ \ B n) := by
        change μ (stoppingGraphMap τ ⁻¹'
            (finiteStoppingTimeGraph τ \ B n)) =
          Measure.map (stoppingGraphMap τ) μ
            (finiteStoppingTimeGraph τ \ B n)
        exact (Measure.map_apply hGraphMap
          (hGraphMeas.diff (hBMeas n))).symm
      _ ≤ errorBudget n := (hBError n).le
  have hFailureSum : (∑' n, μ (failure n)) ≠ ⊤ := by
    have hle : (∑' n, μ (failure n)) ≤ ∑' n, errorBudget n :=
      ENNReal.tsum_le_tsum hFailureBound
    exact (hle.trans_lt tsum_errorBudget_lt_top).ne
  have hEventuallySuccess : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      R n ω = (τ ω : WithTop ℝ≥0) := by
    filter_upwards [ae_eventually_notMem hFailureSum] with ω hω
    filter_upwards [hω] with n hn
    by_cases hmem : stoppingGraphMap τ ω ∈ B n
    · simp only [R, ite_eq_left hmem]
    · have : R n ω = ⊤ := by simp only [R, ite_eq_right hmem]
      exact (hn this).elim
  let running : ℕ → Ω → WithTop ℝ≥0 :=
    StoppingTimeForetelling.runningMinTarget R
  let U : Ω → WithTop ℝ≥0 := fun ω =>
    if ∃ n, R n ω = (τ ω : WithTop ℝ≥0) then
      (τ ω : WithTop ℝ≥0) else ⊤
  have hRLower : ∀ n ω, (τ ω : WithTop ℝ≥0) ≤ R n ω := by
    intro n ω
    by_cases hmem : stoppingGraphMap τ ω ∈ B n
    · simpa only [R, ite_eq_left hmem] using
        (le_refl (τ ω : WithTop ℝ≥0))
    · simp only [R, ite_eq_right hmem, le_top]
  have hRunningStable : ∀ ω, ∃ N, ∀ n ≥ N, running n ω = U ω := by
    intro ω
    by_cases hhit : ∃ k, R k ω = (τ ω : WithTop ℝ≥0)
    · obtain ⟨k, hk⟩ := hhit
      refine ⟨k, fun n hkn => ?_⟩
      have hlower : (τ ω : WithTop ℝ≥0) ≤ running n ω :=
        le_runningMinTarget (hRLower · ω) n
      have hupper : running n ω ≤ (τ ω : WithTop ℝ≥0) :=
        (runningMinTarget_le hkn ω).trans_eq hk
      have heq := le_antisymm hupper hlower
      have hhit' : ∃ j, R j ω = (τ ω : WithTop ℝ≥0) := ⟨k, hk⟩
      change StoppingTimeForetelling.runningMinTarget R n ω =
        if ∃ j, R j ω = (τ ω : WithTop ℝ≥0) then
          (τ ω : WithTop ℝ≥0) else ⊤
      rw [ite_eq_left hhit']
      exact heq
    · refine ⟨0, fun n _ => ?_⟩
      have hRTop : ∀ k, R k ω = ⊤ := by
        intro k
        by_cases hmem : stoppingGraphMap τ ω ∈ B k
        · exact (hhit ⟨k, by simp only [R, ite_eq_left hmem]⟩).elim
        · simp only [R, ite_eq_right hmem]
      have hrunningTop : running n ω = ⊤ := by
        apply top_unique
        apply le_runningMinTarget
        intro k
        simpa only [hRTop k] using
          (le_refl (⊤ : WithTop ℝ≥0))
      simpa only [U, ite_eq_right hhit] using hrunningTop
  have hRunningForetelling : ∀ n,
      StoppingTimeForetelling ℱ (running n) := by
    intro n
    exact StoppingTimeForetelling.runningMin hRForetelling n
  have hUForetelling : StoppingTimeForetelling ℱ U :=
    StoppingTimeForetelling.of_eventuallyEq hUsual hRunningForetelling
      hRunningStable
  have hUEq : U =ᵐ[μ] fun ω => (τ ω : WithTop ℝ≥0) := by
    filter_upwards [hEventuallySuccess] with ω hω
    obtain ⟨n, hn⟩ := hω.exists
    have hhit : ∃ k, R k ω = (τ ω : WithTop ℝ≥0) := ⟨n, hn⟩
    change (if ∃ k, R k ω = (τ ω : WithTop ℝ≥0) then
      (τ ω : WithTop ℝ≥0) else ⊤) = (τ ω : WithTop ℝ≥0)
    rw [ite_eq_left hhit]
  exact StoppingTimeForetelling.congr_ae hUsual hUForetelling hUEq

/-- A strictly positive predictable finite stopping time has an ordinary
strict announcing sequence. -/
noncomputable def IsPredictableStoppingTime.announcement
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {τ : Ω → ℝ≥0} (hτ : IsPredictableStoppingTime ℱ τ)
    (hτpos : ∀ ω, 0 < τ ω) :
    StoppingTimeAnnouncement ℱ τ :=
  (PredictableGraphForetelling.IsPredictableStoppingTime.foretelling
    hUsual hτ).toStoppingTimeAnnouncement hτpos

end PredictableGraphForetelling

end FTAPTheorem42
