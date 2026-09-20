/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Interface.MarketData
import FTAPTheorem42.Foundations.ChronologicalGridOrientation
import FTAPTheorem42.Trading.MaximalClaims

/-! # DS Lemma 4.5: maximality and chronological first-gap pasting

The integral theory supplies only finite switching identities. The main
proof chooses the first-gap event, proves admissibility and contradicts
maximality of the terminal claim.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {S : Process Ω}
  {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}

theorem oneAdmissible_switchAfter_of_nonnegative_increment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (source : BoundedSemimartingaleSource S ℱ μ)
    (O : OriginalMarketOperations source)
    (H K : (generalMarket source).Strategy)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hH : (generalMarket source).OneAdmissible μ H)
    (hK : (generalMarket source).OneAdmissible μ K)
    (hgap : ∀ᵐ ω ∂μ, ω ∈ s →
      0 ≤ ((generalMarket source).gain H) (τ ω) ω - ((generalMarket source).gain K) (τ ω) ω) :
    (generalMarket source).OneAdmissible μ
      (O.switchAfter H K τ hτ s hs T hτT) := by
  classical
  refine ⟨zero_lt_one, ?_⟩
  intro t
  filter_upwards [hH.2 t, hK.2 t, hgap] with ω hHω hKω hgapω
  change (-1 : ℝ) ≤ ((generalMarket source).gain H) t ω at hHω
  change (-1 : ℝ) ≤ ((generalMarket source).gain K) t ω at hKω
  rw [O.gain_switch]
  by_cases hsω : ω ∈ s
  · simp only [hsω, ite_true]
    by_cases hbefore : t ≤ τ ω
    · rw [min_eq_left hbefore]
      ring_nf
      exact hHω
    · have hafter : τ ω ≤ t := le_of_not_ge hbefore
      rw [min_eq_right hafter]
      linarith [hKω, hgapω hsω]
  · simp only [hsω, ite_false]
    exact hHω

private theorem aestronglyMeasurable_piecewise_of_measurableSet
    {μ : Measure Ω} {s : Set Ω} {f g : Ω → ℝ}
    (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (s.piecewise f g) μ := by
  exact AEStronglyMeasurable.piecewise hs hf.restrict hg.restrict

/-! ### Finite chronological first-gap contradiction -/

theorem not_persistent_allTimeGap_of_terminal_chronological_pasting
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (source : BoundedSemimartingaleSource S ℱ μ)
    (O : OriginalMarketOperations source)
    {H : ℕ → (generalMarket source).Strategy}
    {h : Ω → ℝ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hH_one : ∀ n,
      (generalMarket source).OneAdmissible μ
        (H n))
    (hH_adapted : ∀ n,
      StronglyAdapted ℱ ((generalMarket source).gain (H n)))
    (hH_lim : TendstoAE μ (fun n => ((generalMarket source).terminalGain (H n))) h)
    (hpersistent : ∀ N : ℕ, ∃ n m : ℕ,
      N ≤ n ∧ N ≤ m ∧
        ENNReal.ofReal δ <
          μ (allTimeGapEvent
            ((generalMarket source).gain (H n)) ((generalMarket source).gain (H m)) ε))
    (hK1_meas : ∀ q,
      q ∈
          (generalMarket source).K1OfGainProcessModel μ →
        AEStronglyMeasurable q μ)
    (hCandidate :
      TerminalGainHasAEForwardConvexCandidate μ
        ((generalMarket source).K1OfGainProcessModel μ))
    (hmax :
      AEMaximalIn μ
        (InMeasureSequentialClosure μ
          ((generalMarket source).K1OfGainProcessModel μ)) h) :
    False := by
  classical
  let A := generalMarket source
  let X : ℕ → ℝ≥0 → Ω → ℝ :=
    fun n t => ((generalMarket source).gain (H n)) t
  have hXadapted : ∀ n, StronglyAdapted ℱ (X n) := by
    intro n
    exact hH_adapted n
  have hXrc : ∀ n ω t,
      ContinuousWithinAt (X n · ω) (Set.Ici t) t := by
    intro n ω t
    exact O.rightContinuous (H n) ω t
  have hpersistentX : ∀ N : ℕ, ∃ n m : ℕ,
      N ≤ n ∧ N ≤ m ∧
        ENNReal.ofReal δ < μ (allTimeGapEvent (X n) (X m) ε) := by
    intro N
    simpa [X] using hpersistent N
  obtain ⟨first, second, level, hfirst, hsecond, hmass⟩ :=
    FactorialChronologicalGrid.exists_oriented_pair_grid_sequences_of_persistent_allTimeGap
      X hXrc (by exact hε) (by exact hδ) hpersistentX
  let η : ℝ := ε / 2
  let tau : ℕ → Ω → ℝ≥0 := fun k ω =>
    (FactorialChronologicalGrid.grid (level k)).firstGapTime
      (X (first k)) (X (second k)) η ω
  have htau : ∀ k,
      IsStoppingTime ℱ (fun ω => (tau k ω : WithTop ℝ≥0)) := by
    intro k
    dsimp [tau]
    exact (FactorialChronologicalGrid.grid (level k)).isStoppingTime_firstGapTime
      (hXadapted (first k)) (hXadapted (second k)) η
  let s : ℕ → Set Ω := fun k =>
    (FactorialChronologicalGrid.grid (level k)).positiveFirstGapEvent
      (X (first k)) (X (second k)) η
  have hs : ∀ k, MeasurableSet[(htau k).measurableSpace] (s k) := by
    intro k
    have hs' :=
      (FactorialChronologicalGrid.grid (level k)).measurableSet_positiveFirstGapEvent
        (hXadapted (first k)) (hXadapted (second k)) η
    have hs'' :=
      (FactorialChronologicalGrid.grid (level k)).measurableSet_firstGapTime_of_firstGapIndex
        (hXadapted (first k)) (hXadapted (second k)) η
        (s k) hs'
    simpa [s, tau] using hs''
  have hs_mass : ∀ k, ENNReal.ofReal (δ / 2) ≤ μ (s k) := by
    intro k
    simpa [s, η] using hmass k
  let T : ℕ → ℝ≥0 := fun k =>
    (FactorialChronologicalGrid.grid (level k)).time (Fin.last _)
  have hτT : ∀ k ω, tau k ω ≤ T k := by
    intro k ω
    dsimp [tau, T, ChronologicalGrid.firstGapTime]
    exact (FactorialChronologicalGrid.grid (level k)).monotone_time
      (Fin.le_last _)
  have hstop_gap : ∀ k ω, ω ∈ s k →
      η ≤
        ((generalMarket source).gain (H (first k))) (tau k ω) ω -
          ((generalMarket source).gain (H (second k))) (tau k ω) ω := by
    intro k ω hω
    change η ≤
      (FactorialChronologicalGrid.grid (level k)).stoppedAtFirstGap
          (X (first k)) (X (second k)) η (X (first k)) ω -
        (FactorialChronologicalGrid.grid (level k)).stoppedAtFirstGap
          (X (first k)) (X (second k)) η (X (second k)) ω at hω
    simpa [ChronologicalGrid.stoppedAtFirstGap_eq, X, tau] using hω
  have hstop_gap_nonneg : ∀ k, ∀ᵐ ω ∂μ, ω ∈ s k →
      0 ≤
        ((generalMarket source).gain (H (first k))) (tau k ω) ω -
          ((generalMarket source).gain (H (second k))) (tau k ω) ω := by
    intro k
    filter_upwards [] with ω hω
    exact (le_of_lt (half_pos (by exact hε))).trans (hstop_gap k ω hω)
  let L : ℕ → (generalMarket source).Strategy := fun k =>
    O.switchAfter (H (first k)) (H (second k))
      (tau k) (htau k) (s k) (hs k) (T k) (hτT k)
  have hL_one : ∀ k, A.OneAdmissible μ (L k) := by
    intro k
    dsimp [A, L]
    exact oneAdmissible_switchAfter_of_nonnegative_increment
      source O (H (first k)) (H (second k))
      (tau k) (htau k) (s k) (hs k) (T k) (hτT k)
      (hH_one (first k)) (hH_one (second k)) (hstop_gap_nonneg k)
  let f : ℕ → Ω → ℝ := fun k =>
    (s k).piecewise ((generalMarket source).terminalGain (H (second k))) ((generalMarket
      source).terminalGain (H (first k)))
  let g : ℕ → Ω → ℝ := fun k => ((generalMarket source).terminalGain (L k))
  have hterminal_formula : ∀ k ω,
      g k ω =
        if ω ∈ s k then
          ((generalMarket source).terminalGain (H (second k))) ω +
            ((generalMarket source).gain (H (first k))) (tau k ω) ω -
              ((generalMarket source).gain (H (second k))) (tau k ω) ω
        else ((generalMarket source).terminalGain (H (first k))) ω := by
    intro k ω
    exact O.terminal_switch _ _ _ _ _ _ _ _ _
  have hdom : ∀ k, AEDominatedBy μ (f k) (g k) := by
    intro k
    filter_upwards [hstop_gap_nonneg k] with ω hω
    rw [hterminal_formula]
    by_cases hωs : ω ∈ s k
    · simp only [f, Set.piecewise, ite_eq_left hωs]
      linarith [hω hωs]
    · simp only [f, Set.piecewise, ite_eq_right hωs]
      exact le_rfl
  have hsgap : ∀ k, ∀ᵐ ω ∂μ, ω ∈ s k →
      η ≤ g k ω - f k ω := by
    intro k
    filter_upwards [] with ω hω
    rw [hterminal_formula]
    simp only [f, Set.piecewise, ite_eq_left hω]
    linarith [hstop_gap k ω hω]
  have hfirst_lim :
      TendstoAE μ (fun k => ((generalMarket source).terminalGain (H (first k)))) h := by
    filter_upwards [hH_lim] with ω hω
    exact hω.comp hfirst
  have hsecond_lim :
      TendstoAE μ (fun k => ((generalMarket source).terminalGain (H (second k)))) h := by
    filter_upwards [hH_lim] with ω hω
    exact hω.comp hsecond
  have hf : TendstoAE μ f h := by
    dsimp [f]
    exact GainProcessModel.piecewise_tendstoAE_of_tendstoAE
      hfirst_lim hsecond_lim
  have hterminal_meas : ∀ n,
      AEStronglyMeasurable ((generalMarket source).terminalGain (H n)) μ := by
    intro n
    exact hK1_meas _ ⟨H n, hH_one n, rfl⟩
  have hs_underlying : ∀ k, MeasurableSet (s k) := by
    intro k
    exact (htau k).measurableSpace_le _ (hs k)
  have hf_meas : ∀ k, AEStronglyMeasurable (f k) μ := by
    intro k
    dsimp [f]
    exact aestronglyMeasurable_piecewise_of_measurableSet
      (hs_underlying k) (hterminal_meas (second k))
      (hterminal_meas (first k))
  have hg_meas : ∀ k, AEStronglyMeasurable (g k) μ := by
    intro k
    exact hK1_meas _ ⟨L k, hL_one k, rfl⟩
  have hgap_meas : ∀ k,
      AEStronglyMeasurable (fun ω => g k ω - f k ω) μ := by
    intro k
    exact (hg_meas k).sub (hf_meas k)
  have hgap_nonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ g k ω - f k ω := by
    intro k
    filter_upwards [hdom k] with ω hω
    linarith
  exact not_persistent_terminalGain_improvement_of_forwardConvexCandidate
    (A := A) (μ := μ) (h := h) (f := f) (g := g) (s := s)
    (ε := η) (δ := δ / 2) (half_pos (by exact hε)) (half_pos (by exact hδ))
    hK1_meas hCandidate (fun k => ⟨L k, hL_one k, rfl⟩)
    hmax hf hdom hgap_meas hgap_nonneg
    (fun k => (hs_underlying k).nullMeasurableSet) hs_mass hsgap

theorem pairwise_allTimeGap_cauchyInMeasure_of_terminal_chronological_pasting
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (source : BoundedSemimartingaleSource S ℱ μ)
    (O : OriginalMarketOperations source)
    {H : ℕ → (generalMarket source).Strategy}
    {h : Ω → ℝ}
    (hH_one : ∀ n,
      (generalMarket source).OneAdmissible μ
        (H n))
    (hH_adapted : ∀ n,
      StronglyAdapted ℱ ((generalMarket source).gain (H n)))
    (hH_lim : TendstoAE μ (fun n => ((generalMarket source).terminalGain (H n))) h)
    (hK1_meas : ∀ q,
      q ∈
          (generalMarket source).K1OfGainProcessModel μ →
        AEStronglyMeasurable q μ)
    (hCandidate :
      TerminalGainHasAEForwardConvexCandidate μ
        ((generalMarket source).K1OfGainProcessModel μ))
    (hmax :
      AEMaximalIn μ
        (InMeasureSequentialClosure μ
          ((generalMarket source).K1OfGainProcessModel μ)) h) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        μ (allTimeGapEvent ((generalMarket source).gain (H n)) ((generalMarket source).gain (H
          m)) ε) ≤
          ENNReal.ofReal δ := by
  intro ε hε δ hδ
  by_contra hnot
  push Not at hnot
  have hpersistent : ∀ N : ℕ, ∃ n m : ℕ,
      N ≤ n ∧ N ≤ m ∧
        ENNReal.ofReal δ <
          μ (allTimeGapEvent ((generalMarket source).gain (H n)) ((generalMarket source).gain
            (H m)) ε) := by
    intro N
    simpa only [not_forall, not_le, allTimeGapEvent] using hnot N
  exact not_persistent_allTimeGap_of_terminal_chronological_pasting
    source O hε hδ hH_one hH_adapted hH_lim hpersistent hK1_meas hCandidate hmax

end FTAPTheorem42.BoundedSourceIntegralMarket
