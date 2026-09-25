/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.ElementaryPredictable
import FTAPTheorem42.Foundations.ProcessIndistinguishable
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Trading.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure

/-!
# Finite-variation integrals for predictable elementary strategies

The finite-variation component of a predictable elementary gain is identified
with the pathwise integral against the associated signed Stieltjes measure.
This is a concrete bridge: it uses the interval integral itself and does not
postulate a general stochastic-integral closedness theorem.
-/

open MeasureTheory Set
open scoped ENNReal Topology

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]
  [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]

namespace ElementaryInterval

noncomputable def finiteVariationIntegral
    (A : Time → Ω → ℝ)
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω) : ℝ :=
  FiniteVariationPath.integral (hA ω)
    ((Ioc (B.startTime ω) (min t (B.stopTime ω))).indicator
      (fun _ => B.coefficient ω))

omit [MeasurableSpace Ω] in
theorem finiteVariationIntegral_eq_gain
    (A : Time → Ω → ℝ)
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => A u ω) (Set.Ici t) t)
    (B : ElementaryInterval Ω Time) (t : Time) (ω : Ω) :
    B.finiteVariationIntegral A hA t ω = B.gain A t ω := by
  unfold finiteVariationIntegral
  by_cases hstart : B.startTime ω ≤ t
  · have hmin : B.startTime ω ≤ min t (B.stopTime ω) :=
      le_min hstart (B.start_le_stop ω)
    rw [FiniteVariationPath.integral_indicator (hA ω) measurableSet_Ioc,
      FiniteVariationPath.setIntegral_const_Ioc (hA ω) (hRight ω)
        hmin (B.coefficient ω)]
    simp [ElementaryInterval.gain, min_eq_right hstart]
  · have ht : t < B.startTime ω := lt_of_not_ge hstart
    have htstop : t ≤ B.stopTime ω :=
      (le_of_lt ht).trans (B.start_le_stop ω)
    have hmin : min t (B.stopTime ω) ≤ B.startTime ω := by
      exact (min_le_left t (B.stopTime ω)).trans (le_of_lt ht)
    have hempty : Ioc (B.startTime ω) (min t (B.stopTime ω)) = ∅ := by
      exact Ioc_eq_empty_of_le hmin
    rw [hempty]
    simp only [Set.indicator_empty, FiniteVariationPath.integral]
    simp [ElementaryInterval.gain, min_eq_left htstop,
      min_eq_left (le_of_lt ht)]

end ElementaryInterval

namespace PredictableElementaryStrategy

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

noncomputable def finiteVariationIntegral
    (A : Time → Ω → ℝ)
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (H : PredictableElementaryStrategy ℱ) (t : Time) (ω : Ω) : ℝ :=
  (H.map (fun B => B.interval.finiteVariationIntegral A hA t ω)).sum

theorem finiteVariationIntegral_eq_gain
    (A : Time → Ω → ℝ)
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => A u ω) (Set.Ici t) t)
    (H : PredictableElementaryStrategy ℱ) (t : Time) (ω : Ω) :
    H.finiteVariationIntegral A hA t ω =
      ElementaryStrategy.gain A (toElementary H) t ω := by
  induction H with
  | nil =>
      rfl
  | cons B H ih =>
      change
        B.interval.finiteVariationIntegral A hA t ω +
            finiteVariationIntegral A hA H t ω =
          B.interval.gain A t ω +
            ElementaryStrategy.gain A (toElementary H) t ω
      rw [B.interval.finiteVariationIntegral_eq_gain A hA hRight t ω,
        ih]

end PredictableElementaryStrategy

end FTAPTheorem42
