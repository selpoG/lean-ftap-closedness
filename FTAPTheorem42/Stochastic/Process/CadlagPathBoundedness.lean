/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Bornology

/-!
# Pathwise boundedness of càdlàg paths

A real-valued path on `ℝ≥0` which is right-continuous and has left limits is
locally bounded.  If it also converges at `atTop`, the local bounds on a
compact initial interval and the tail bound supplied by convergence combine
to give a global bound for its norm.  The terminal convergence in this file
is pathwise; convergence in measure is deliberately not used.
-/

open Filter MeasureTheory Set Topology Bornology
open scoped NNReal Topology

namespace FTAPTheorem42

/-! ## Local compact-interval boundedness -/

theorem bddAbove_norm_image_Icc_of_rightContinuous_leftLimits
    {f : ℝ≥0 → ℝ}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t)
      (𝓝 (Function.leftLim f t)))
    (a b : ℝ≥0) :
    BddAbove ((fun t => ‖f t‖) '' Icc a b) := by
  have hLocal : ∀ t, ∃ u ∈ 𝓝 t,
      IsBounded ((fun s => ‖f s‖) '' u) := by
    intro t
    let c : ℝ := max (‖f t‖ + 1)
      (‖Function.leftLim f t‖ + 1)
    have hRightBall : ∀ᶠ s in 𝓝[Ici t] t,
        f s ∈ Metric.ball (f t) 1 := by
      exact (hRight t).eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity)))
    have hRightBound : ∀ᶠ s in 𝓝[Ici t] t, ‖f s‖ ≤ c := by
      filter_upwards [hRightBall] with s hs
      have hs' : dist (f s) (f t) < 1 := Metric.mem_ball.mp hs
      have hnorm : ‖f s‖ ≤ dist (f s) (f t) + ‖f t‖ := by
        calc
          ‖f s‖ = dist (f s) 0 := by simp
          _ ≤ dist (f s) (f t) + dist (f t) 0 := dist_triangle _ _ _
          _ = dist (f s) (f t) + ‖f t‖ := by simp
      calc
        ‖f s‖ ≤ dist (f s) (f t) + ‖f t‖ := hnorm
        _ ≤ 1 + ‖f t‖ := add_le_add_left hs'.le _
        _ = ‖f t‖ + 1 := by ring
        _ ≤ c := le_max_left _ _
    have hLeftBall : ∀ᶠ s in 𝓝[<] t,
        f s ∈ Metric.ball (Function.leftLim f t) 1 := by
      exact (hLeft t).eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity)))
    have hLeftBound : ∀ᶠ s in 𝓝[<] t, ‖f s‖ ≤ c := by
      filter_upwards [hLeftBall] with s hs
      have hs' : dist (f s) (Function.leftLim f t) < 1 :=
        Metric.mem_ball.mp hs
      have hnorm : ‖f s‖ ≤ dist (f s) (Function.leftLim f t) +
          ‖Function.leftLim f t‖ := by
        calc
          ‖f s‖ = dist (f s) 0 := by simp
          _ ≤ dist (f s) (Function.leftLim f t) +
              dist (Function.leftLim f t) 0 := dist_triangle _ _ _
          _ = dist (f s) (Function.leftLim f t) +
              ‖Function.leftLim f t‖ := by simp
      calc
        ‖f s‖ ≤ dist (f s) (Function.leftLim f t) +
            ‖Function.leftLim f t‖ := hnorm
        _ ≤ 1 + ‖Function.leftLim f t‖ := add_le_add_left hs'.le _
        _ = ‖Function.leftLim f t‖ + 1 := by ring
        _ ≤ c := le_max_right _ _
    have hBound : ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ c := by
      have hBound' : {s | ‖f s‖ ≤ c} ∈ 𝓝[<] t ⊔ 𝓝[≥] t := by
        rw [Filter.mem_sup]
        exact ⟨hLeftBound, hRightBound⟩
      rw [nhdsLT_sup_nhdsGE] at hBound'
      change {s | ‖f s‖ ≤ c} ∈ 𝓝 t
      exact hBound'
    refine ⟨{s | ‖f s‖ ≤ c}, hBound, ?_⟩
    apply Metric.isBounded_Icc (0 : ℝ) c |>.subset
    rintro _ ⟨s, hs, rfl⟩
    exact mem_Icc.mpr ⟨norm_nonneg _, hs⟩
  have hImageBound : IsBounded
      ((fun t => ‖f t‖) '' Icc a b) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
      isCompact_Icc hLocal
  exact hImageBound.bddAbove

/-! ## Global boundedness after an `atTop` terminal limit -/

theorem bddAbove_range_norm_of_cadlag_of_tendsto
    {f : ℝ≥0 → ℝ} {z : ℝ}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t)
      (𝓝 (Function.leftLim f t)))
    (hTerminal : Tendsto f atTop (𝓝 z)) :
    BddAbove (Set.range fun t => ‖f t‖) := by
  have hNormTerminal : Tendsto (fun t => ‖f t‖) atTop (𝓝 ‖z‖) :=
    hTerminal.norm
  obtain ⟨cTail, hTail⟩ := hNormTerminal.isBoundedUnder_le.eventually_le
  obtain ⟨T, hT⟩ := (eventually_atTop.1 hTail)
  obtain ⟨cInitial, hcInitial⟩ :=
    bddAbove_norm_image_Icc_of_rightContinuous_leftLimits
      hRight hLeft 0 T
  refine ⟨max cInitial cTail, ?_⟩
  rintro _ ⟨t, rfl⟩
  by_cases ht : t ≤ T
  · exact (hcInitial ⟨t, ⟨zero_le, ht⟩, rfl⟩).trans
      (le_max_left _ _)
  · exact (hT t (le_of_not_ge ht)).trans (le_max_right _ _)

end FTAPTheorem42
