/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Process
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Interchanging a uniform path limit with its terminal limit -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

/-! ## Continuous-time terminal interchange -/

/-- Uniform convergence in the time variable permits passage of a continuous-time
terminal limit through the approximating sequence. -/
theorem tendsto_atTop_of_tendstoUniformly_terminal
    {ι : Type*} {X : ι → ℝ≥0 → ℝ} {Xlim : ℝ≥0 → ℝ}
    {terminal : ι → ℝ} {terminalLimit : ℝ}
    {l : Filter ι} [NeBot l]
    (hUniform : TendstoUniformly X Xlim l)
    (hX : ∀ i, Tendsto (X i) atTop (𝓝 (terminal i)))
    (hTerminal : Tendsto terminal l (𝓝 terminalLimit)) :
    Tendsto Xlim atTop (𝓝 terminalLimit) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεThird : 0 < ε / 3 := by positivity
  have hTerminalEventually : ∀ᶠ i in l,
      terminal i ∈ Metric.ball terminalLimit (ε / 3) :=
    hTerminal (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hεThird))
  have hUniformEventually : ∀ᶠ i in l, ∀ t,
      dist (Xlim t) (X i t) < ε / 3 :=
    (Metric.tendstoUniformly_iff.mp hUniform) (ε / 3) hεThird
  obtain ⟨i, hiTerminal, hiUniform⟩ :=
    (hTerminalEventually.and hUniformEventually).exists
  have hTerminalDistance : dist (terminal i) terminalLimit < ε / 3 :=
    Metric.mem_ball.mp hiTerminal
  have hXEventually : ∀ᶠ t in atTop,
      X i t ∈ Metric.ball (terminal i) (ε / 3) :=
    hX i (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hεThird))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hXEventually
  refine ⟨N, fun t ht => ?_⟩
  have hXDistance : dist (X i t) (terminal i) < ε / 3 := by
    exact Metric.mem_ball.mp (hN t ht)
  calc
    dist (Xlim t) terminalLimit ≤
        dist (Xlim t) (X i t) + dist (X i t) (terminal i) +
          dist (terminal i) terminalLimit := by
      exact dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      exact add_lt_add (add_lt_add (hiUniform t) hXDistance)
        hTerminalDistance
    _ = ε := by ring

end FTAPTheorem42
