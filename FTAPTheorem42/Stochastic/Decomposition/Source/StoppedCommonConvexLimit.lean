/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Compactness.CountableInMeasureDiagonal
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedComponents

/-!
# Common convex limits of variation-stopped factorial Doob components

At one fixed variation level, every stopped predictable and martingale
coordinate has a deterministic `L²` bound.  We put both component families in
one countable Hilbert direct sum.  A single family of tail convex weights then
makes both components converge strongly in `L²` at every prescribed time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- One countable family containing both stopped Doob components.  Pairing
`(0,j)` selects the predictable component at `time j`; every other first
coordinate selects the martingale component. -/
noncomputable def stoppedComponentCoordinateToLp
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (time : Nat → Set.Iic T)
    (r j : Nat) : Lp Real 2 mu :=
  if (Nat.unpair j).1 = 0 then
    stoppedPredictableApproximationToLp source ha T
      (time (Nat.unpair j).2).1 (time (Nat.unpair j).2).2 r
  else
    stoppedMartingaleApproximationToLp source ha T
      (time (Nat.unpair j).2).1 (time (Nat.unpair j).2).2 r

/-- The coordinatewise deterministic bound used for the common Hilbert
convexification. -/
noncomputable def stoppedComponentCoordinateBound
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real) (j : Nat) : Real :=
  if (Nat.unpair j).1 = 0 then
    a + 2 * max source.bound 0
  else
    a + 4 * max source.bound 0

theorem stoppedComponentCoordinateBound_nonnegative
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (j : Nat) :
    0 ≤ stoppedComponentCoordinateBound source a j := by
  unfold stoppedComponentCoordinateBound
  split_ifs <;> linarith [le_max_right source.bound 0]

theorem stoppedComponentCoordinateToLp_norm_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (time : Nat → Set.Iic T)
    (r j : Nat) :
    ‖stoppedComponentCoordinateToLp source ha T time r j‖ ≤
      stoppedComponentCoordinateBound source a j := by
  unfold stoppedComponentCoordinateToLp stoppedComponentCoordinateBound
  split_ifs with h
  · exact stoppedPredictableApproximationToLp_norm_le source ha T
      (time (Nat.unpair j).2).1 (time (Nat.unpair j).2).2 r
  · exact stoppedMartingaleApproximationToLp_norm_le source ha T
      (time (Nat.unpair j).2).1 (time (Nat.unpair j).2).2 r

/-- One family of tail weights gives strong `L²` convergence of both stopped
components at every time in the prescribed countable family. -/
theorem exists_common_stoppedComponentConvexification
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (time : Nat → Set.Iic T) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (predictableLimit martingaleLimit : Nat → Lp Real 2 mu),
      (∀ j, Tendsto
        (fun n => (w n).applyVector (fun r =>
          stoppedPredictableApproximationToLp source ha T
            (time j).1 (time j).2 r))
        atTop (𝓝 (predictableLimit j))) ∧
      ∀ j, Tendsto
        (fun n => (w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (time j).1 (time j).2 r))
        atTop (𝓝 (martingaleLimit j)) := by
  let B : Nat → Real := stoppedComponentCoordinateBound source a
  let Z : Nat → Nat → Lp Real 2 mu := fun r j =>
    stoppedComponentCoordinateToLp source ha T time r j
  obtain ⟨w, y, _hNormalized, hCoordinate⟩ :=
    DirectSumCoordinateControl.exists_common_tailConvexification_of_finite_coordinateBounds
      B Z
      (stoppedComponentCoordinateBound_nonnegative source ha)
      (stoppedComponentCoordinateToLp_norm_le source ha T time)
  let predictableLimit : Nat → Lp Real 2 mu := fun j =>
    (DirectSumCoordinateControl.geometricNormalization B (Nat.pair 0 j))⁻¹ •
      y (Nat.pair 0 j)
  let martingaleLimit : Nat → Lp Real 2 mu := fun j =>
    (DirectSumCoordinateControl.geometricNormalization B (Nat.pair 1 j))⁻¹ •
      y (Nat.pair 1 j)
  refine ⟨w, predictableLimit, martingaleLimit, ?_, ?_⟩
  · intro j
    simpa only [Z, stoppedComponentCoordinateToLp, Nat.unpair_pair,
      Prod.fst_zero, Prod.snd_zero, ite_eq_left] using hCoordinate (Nat.pair 0 j)
  · intro j
    simpa only [Z, stoppedComponentCoordinateToLp, Nat.unpair_pair,
      Prod.fst_one, Prod.snd_one, one_ne_zero, ite_false] using
      hCoordinate (Nat.pair 1 j)

end HorizonFactorialGrid

end FTAPTheorem42
