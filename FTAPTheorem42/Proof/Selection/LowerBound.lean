/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Interface.MarketOperations
import FTAPTheorem42.Interface.TerminalMarket
import FTAPTheorem42.Trading.MaximalClaims

/-! # Terminal lower bounds control running gains

Only finite event switching is supplied by the integral theory. The bounded
loss event, admissibility of its tail and the no-arbitrage contradiction
are constructed in the main proof.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- NFLVR promotes a terminal lower bound to the same running lower bound. -/
theorem generalMarket_terminalLowerBoundControlsGain
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source)))) :
    (generalMarket source).TerminalLowerBoundControlsGain μ := by
  classical
  let A := generalMarket source
  let O := Classical.choice (generalMarket_operations source)
  rw [generalTerminalClaims_eq_generalMarket_K0] at hNFLVR
  have hNA := GainProcessModel.noArbitrage_of_linfyNFLVR
    (fun f hf => ((generalMarket_terminal_properties source).1 f hf).aestronglyMeasurable) hNFLVR
  change ∀ ⦃H : A.Strategy⦄ ⦃a : Real⦄, 0 < a →
    A.Admissible μ H → AELowerBoundedBy μ (-a) (A.terminalGain H) →
      ∀ t, AELowerBoundedBy μ (-a) ((A.gain H) t)
  intro H a ha hAdm hTerminal t
  obtain ⟨b, hb, hLower⟩ := hAdm
  change ∀ t, AELowerBoundedBy μ (-b) ((A.gain H) t) at hLower
  by_contra hNot
  let bad := {ω | (A.gain H) t ω < -a}
  have hBad : 0 < μ bad := by
    apply pos_iff_ne_zero.mpr
    simpa only [AELowerBoundedBy, ae_iff, not_le, bad] using hNot
  let B := {ω | (A.gain H) t ω < -a ∧ -b ≤ (A.gain H) t ω}
  have hBpos : 0 < μ B :=
    GainProcessModel.eventually_and_of_measure_pos_of_ae hBad (hLower t)
  have hBmeas : MeasurableSet[F t] B :=
    (((O.adapted H) t).measurableSet_lt stronglyMeasurable_const).inter
      (stronglyMeasurable_const.measurableSet_le ((O.adapted H) t))
  let τ : Ω → NNReal := fun _ => t
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop NNReal)) := isStoppingTime_const F t
  have hBτ : MeasurableSet[hτ.measurableSpace] B := by
    change MeasurableSet[(isStoppingTime_const F t).measurableSpace] B
    rw [IsStoppingTime.measurableSpace_const]
    exact hBmeas
  let L := O.switchAfter A.zeroStrategy H τ hτ B hBτ t (fun _ => le_rfl)
  have hGain u ω : A.gain L u ω =
      if ω ∈ B then A.gain H u ω - A.gain H (min u t) ω else 0 := by
    rw [O.gain_switch]
    simp only [τ, show (generalMarket source).gain A.zeroStrategy = 0 from funext A.gain_zero,
      Pi.zero_apply, zero_add]
    split_ifs <;> rfl
  have hTerm ω : A.terminalGain L ω =
      if ω ∈ B then A.terminalGain H ω - A.gain H t ω else 0 := by
    rw [O.terminal_switch]
    simp only [τ, show (generalMarket source).gain A.zeroStrategy = 0 from funext A.gain_zero,
      show (generalMarket source).terminalGain A.zeroStrategy = 0 from A.terminalGain_zero,
      Pi.zero_apply, add_zero]
    split_ifs <;> rfl
  have hL : A.Admissible μ L := by
    refine ⟨b, hb, ?_⟩
    intro u
    filter_upwards [hLower u] with ω hω
    rw [hGain]
    by_cases hωB : ω ∈ B
    · rw [ite_eq_left hωB]
      by_cases hut : u ≤ t
      · rw [min_eq_left hut, sub_self]
        exact neg_nonpos.mpr hb.le
      · rw [min_eq_right (le_of_lt (lt_of_not_ge hut))]
        have htLoss := hωB.1
        change -b ≤ (A.gain H) u ω at hω
        linarith
    · rw [ite_eq_right hωB]
      exact neg_nonpos.mpr hb.le
  have hNonnegative : AENonnegative μ (A.terminalGain L) := by
    filter_upwards [hTerminal] with ω hω
    rw [hTerm]
    by_cases hωB : ω ∈ B
    · rw [ite_eq_left hωB]
      have htLoss := hωB.1
      change -a ≤ (A.terminalGain H) ω at hω
      linarith
    · rw [ite_eq_right hωB]
  have hPositive : 0 < μ {ω | 0 < (A.terminalGain L) ω} := by
    have hPos := GainProcessModel.eventually_and_of_measure_pos_of_ae hBpos hTerminal
    apply hPos.trans_le (measure_mono ?_)
    intro ω hω
    change ω ∈ B ∧ -a ≤ (A.terminalGain H) ω at hω
    change 0 < (A.terminalGain L) ω
    rw [hTerm, ite_eq_left hω.1]
    have htLoss := hω.1.1
    have hTerminalω : -a ≤ (A.terminalGain H) ω := hω.2
    linarith
  exact hNA ⟨(A.terminalGain L), ⟨L, hL, rfl⟩, hNonnegative, hPositive⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
