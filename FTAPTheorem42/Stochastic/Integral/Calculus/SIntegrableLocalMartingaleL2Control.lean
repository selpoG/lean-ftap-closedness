/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.SummableL2Limit
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel

/-!
# Local `L²` controls for realized martingale integrals

A local square-integrable source martingale supplies predictable control
measures for which the stochastic-integral isometry identifies integrand
`L²` distances with terminal distances of stopped martingale components.
This module records precisely that primitive on the actual realization
carrier and consumes it to obtain one canonical Mémín integrand across a
countable family of controls.

No limit stochastic integral or range-closedness conclusion is a field of
the calculus.
-/

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The centered martingale component of an actual strategy, first stopped at
a localizer and then at a deterministic horizon.  This process-level
definition needs no strategy-valued stopping operation: local `L²` controls
only observe the canonical martingale coordinate. -/
noncomputable def actualLocalL2CoordinateProcess
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    {R : SIntegrableRealizationModel D}
    (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (H : ActualSIntegrableStrategy R) : Process Ω :=
  MeasureTheory.stoppedProcess
    (MeasureTheory.stoppedProcess H.val.centeredMartingalePart τ)
      (fun _ => (T : WithTop ℝ≥0))

/-- The centered stopped coordinate is strongly adapted for arbitrary
stopping-time and deterministic-horizon inputs. -/
theorem actualLocalL2CoordinateProcess_stronglyAdapted
    {S : Process Ω} {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    {R : SIntegrableRealizationModel D}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (T : ℝ≥0) (H : ActualSIntegrableStrategy R) :
    StronglyAdapted ℱ (actualLocalL2CoordinateProcess τ T H) := by
  have hInitial : StronglyAdapted ℱ
      (fun _ => H.val.martingalePart 0) := fun s =>
    (H.val.martingalePart_isStronglyAdapted 0).mono (ℱ.mono bot_le)
  have hCentered : StronglyAdapted ℱ H.val.centeredMartingalePart :=
    H.val.martingalePart_isStronglyAdapted.sub hInitial
  have hCenteredRight : ∀ ω s,
      ContinuousWithinAt (H.val.centeredMartingalePart · ω)
        (Set.Ici s) s := by
    intro ω s
    exact (H.val.martingalePart_isRightContinuous ω s).sub
      continuousWithinAt_const
  have hFirst : StronglyAdapted ℱ
      (MeasureTheory.stoppedProcess H.val.centeredMartingalePart τ) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hCentered hτ hCenteredRight
  have hFirstRight : ∀ ω s, ContinuousWithinAt
      (MeasureTheory.stoppedProcess H.val.centeredMartingalePart τ · ω)
        (Set.Ici s) s :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      H.val.centeredMartingalePart hCenteredRight
  exact
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hFirst (isStoppingTime_const ℱ T) hFirstRight

/-- The terminal value of one centered actual localized martingale
coordinate. -/
noncomputable def actualLocalL2TerminalCoordinate
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    {R : SIntegrableRealizationModel D}
    (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (H : ActualSIntegrableStrategy R) : Ω → ℝ :=
  MeasureTheory.stoppedProcess H.val.centeredMartingalePart τ T

/-- At its deterministic horizon, the process-valued coordinate is the
terminal coordinate used by the control isometry. -/
theorem actualLocalL2CoordinateProcess_horizon
    {S : Process Ω} {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    {R : SIntegrableRealizationModel D}
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0)
    (H : ActualSIntegrableStrategy R) :
    actualLocalL2CoordinateProcess τ T H T =
      actualLocalL2TerminalCoordinate τ T H := by
  funext ω
  simp only [actualLocalL2CoordinateProcess,
    actualLocalL2TerminalCoordinate, MeasureTheory.stoppedProcess, min_self]
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

end FTAPTheorem42
