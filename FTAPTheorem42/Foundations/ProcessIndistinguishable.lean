/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Skeleton
import Mathlib.Probability.Process.LocalProperty

/-!
# Indistinguishability of real-valued processes

Continuous-time stochastic decompositions are identities up to one null set
on which equality holds at every time.  They should therefore not be recorded
as literal equalities of raw functions.

This file defines that process-level relation, proves its elementary algebra
and transfer across absolutely continuous measures, and shows that
right-continuous processes are indistinguishable once they agree almost
everywhere on one countable right-dense skeleton.
-/

open Filter MeasureTheory Topology

namespace FTAPTheorem42

variable {Time Ω : Type*} [MeasurableSpace Ω]

/--
Two processes are indistinguishable under `μ` when, outside one `μ`-null set,
their values agree at every time.
-/
def ProcessIndistinguishable
    (μ : Measure Ω) (X Y : Time → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω

namespace ProcessIndistinguishable

theorem refl (μ : Measure Ω) (X : Time → Ω → ℝ) :
    ProcessIndistinguishable μ X X :=
  Filter.Eventually.of_forall fun _ _ => rfl

theorem symm {μ : Measure Ω} {X Y : Time → Ω → ℝ}
    (h : ProcessIndistinguishable μ X Y) :
    ProcessIndistinguishable μ Y X := by
  filter_upwards [h] with ω hω
  exact fun t => (hω t).symm

theorem trans {μ : Measure Ω} {X Y Z : Time → Ω → ℝ}
    (hXY : ProcessIndistinguishable μ X Y)
    (hYZ : ProcessIndistinguishable μ Y Z) :
    ProcessIndistinguishable μ X Z := by
  filter_upwards [hXY, hYZ] with ω hXYω hYZω
  exact fun t => (hXYω t).trans (hYZω t)

theorem eventuallyEq_at {μ : Measure Ω} {X Y : Time → Ω → ℝ}
    (h : ProcessIndistinguishable μ X Y) (t : Time) :
    X t =ᵐ[μ] Y t := by
  filter_upwards [h] with ω hω
  exact hω t

/-- Indistinguishable processes remain indistinguishable after the same
random-time stop. -/
theorem stoppedProcess [Nonempty Time] [LinearOrder Time]
    {μ : Measure Ω} {X Y : Time → Ω → ℝ}
    (h : ProcessIndistinguishable μ X Y)
    (τ : Ω → WithTop Time) :
    ProcessIndistinguishable μ
      (MeasureTheory.stoppedProcess X τ)
      (MeasureTheory.stoppedProcess Y τ) := by
  filter_upwards [h] with ω hω
  intro t
  exact hω _

theorem add {μ : Measure Ω}
    {X Y X' Y' : Time → Ω → ℝ}
    (hXY : ProcessIndistinguishable μ X Y)
    (hX'Y' : ProcessIndistinguishable μ X' Y') :
    ProcessIndistinguishable μ
      (fun t ω => X t ω + X' t ω)
      (fun t ω => Y t ω + Y' t ω) := by
  filter_upwards [hXY, hX'Y'] with ω hXYω hX'Y'ω
  intro t
  rw [hXYω t, hX'Y'ω t]

theorem sub {μ : Measure Ω}
    {X Y X' Y' : Time → Ω → ℝ}
    (hXY : ProcessIndistinguishable μ X Y)
    (hX'Y' : ProcessIndistinguishable μ X' Y') :
    ProcessIndistinguishable μ
      (fun t ω => X t ω - X' t ω)
      (fun t ω => Y t ω - Y' t ω) := by
  filter_upwards [hXY, hX'Y'] with ω hXYω hX'Y'ω
  intro t
  rw [hXYω t, hX'Y'ω t]

theorem smul (c : ℝ) {μ : Measure Ω}
    {X Y : Time → Ω → ℝ}
    (h : ProcessIndistinguishable μ X Y) :
    ProcessIndistinguishable μ
      (fun t ω => c * X t ω) (fun t ω => c * Y t ω) := by
  filter_upwards [h] with ω hω
  intro t
  rw [hω t]

/-- If two processes have indistinguishable stops along one localizing
sequence, then the original processes are indistinguishable. -/
theorem of_stoppedProcess_localizingSequence
    [LinearOrder Time] [TopologicalSpace Time] [OrderTopology Time]
    [OrderBot Time]
    {μ : Measure Ω} {X Y : Time → Ω → ℝ}
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → WithTop Time}
    (hτ : ProbabilityTheory.IsLocalizingSequence ℱ τ μ)
    (hStopped : ∀ n, ProcessIndistinguishable μ
      (MeasureTheory.stoppedProcess X (τ n))
      (MeasureTheory.stoppedProcess Y (τ n))) :
    ProcessIndistinguishable μ X Y := by
  have hStoppedAll : ∀ᵐ ω ∂μ, ∀ n t,
      MeasureTheory.stoppedProcess X (τ n) t ω =
        MeasureTheory.stoppedProcess Y (τ n) t ω := by
    filter_upwards [ae_all_iff.2 hStopped] with ω hω n t
    exact hω n t
  filter_upwards [hτ.tendsto_top, hStoppedAll] with ω hTop hEq
  intro t
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  obtain ⟨n, hn⟩ := (hTop t).exists
  have htn : (t : WithTop Time) ≤ τ n ω := hn.le
  calc
    X t ω = MeasureTheory.stoppedProcess X (τ n) t ω :=
      (MeasureTheory.stoppedProcess_eq_of_le htn).symm
    _ = MeasureTheory.stoppedProcess Y (τ n) t ω := hEq n t
    _ = Y t ω := MeasureTheory.stoppedProcess_eq_of_le htn

/--
Right-continuous real-valued processes which agree almost everywhere at every
point of one countable right-dense skeleton are indistinguishable.

The countability of the skeleton supplies one common full-measure set.  On
that set, right continuity propagates equality from the skeleton to all
times.
-/
theorem of_ae_eq_on_rightDense
    [TopologicalSpace Time] [LinearOrder Time] [OrderTopology Time]
    (X Y : Time → Ω → ℝ) (skeleton : ℕ → Time)
    (hRightDense : ∀ t,
      t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hX : ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hY : ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    (hEq : ∀ k, X (skeleton k) =ᵐ[μ] Y (skeleton k)) :
    ProcessIndistinguishable μ X Y := by
  have hEqAll : ∀ᵐ ω ∂μ, ∀ k,
      X (skeleton k) ω = Y (skeleton k) ω := by
    rw [ae_all_iff]
    exact hEq
  filter_upwards [hX, hY, hEqAll] with ω hXω hYω hEqω
  intro t
  have hnorm : ∀ s,
      ‖X s ω - Y s ω‖ ≤ 0 := by
    apply norm_le_of_rightDense_skeleton skeleton hRightDense
      (fun s => X s ω - Y s ω)
      (fun s => (hXω s).sub (hYω s))
    intro k
    rw [hEqω k, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (hnorm t) (norm_nonneg _)))

end ProcessIndistinguishable

end FTAPTheorem42
