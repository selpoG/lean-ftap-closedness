/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnDecomposition
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import FTAPTheorem42.Foundations.SignedMeasureVariation

/-!
# Predictable signed-measure integrals

The finite-variation part of the stochastic argument integrates predictable
integrands against a signed measure on the predictable sigma-algebra.  This
file records the actual restriction identity and the integral of the Hahn
sign density against that measure.
-/

namespace FTAPTheorem42

open MeasureTheory
open MeasureTheory.VectorMeasure
open scoped ENNReal

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [Preorder Time] [OrderBot Time]

namespace PredictableSignedMeasure

noncomputable def integral
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    (ν : Measure ℱ) (H : Time → Ω → ℝ) : ℝ :=
  ∫ᵛ p, Function.uncurry H p ∂•ν

theorem vectorIntegral_toSignedMeasure
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [IsFiniteMeasure μ]
    {f : X → ℝ} :
    (∫ᵛ x, f x ∂•(μ.toSignedMeasure : VectorMeasure X ℝ)) =
      ∫ x, f x ∂μ := by
  have hpair : (ContinuousLinearMap.lsmul ℝ ℝ) =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    apply ContinuousLinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro x
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  have h := VectorMeasure.integral_toSignedMeasure (μ := μ) (f := f)
  rw [← hpair] at h
  exact h

end PredictableSignedMeasure

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Total variation recovered by a predictable Hahn split

The positive restriction and the negated complementary restriction of a
signed predictable measure recover its whole total-variation measure, not
only its total mass.  This is the measure-level fact used by the Lemma 4.7
Hahn-selected strategy consumer.
-/

open MeasureTheory Set
open scoped ENNReal

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [Preorder Time] [OrderBot Time]

namespace PredictableSignedMeasure

/-- The positive real signed measure associated with the Jordan total
variation.  This is the real-valued counterpart of `totalVariation`. -/
noncomputable def totalVariationSignedMeasure
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    (ν : Measure ℱ) : Measure ℱ := by
  let : MeasurableSpace (Time × Ω) := ℱ.predictable
  exact signedMeasureTotalVariation ν

/-- Evaluation of the real signed version of total variation. -/
theorem totalVariationSignedMeasure_apply
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    (ν : Measure ℱ) {B : Set (Time × Ω)}
    (hB : MeasurableSet[ℱ.predictable] B) :
    totalVariationSignedMeasure ν B = (totalVariation ν).real B := by
  let : MeasurableSpace (Time × Ω) := ℱ.predictable
  exact signedMeasureTotalVariation_apply ν hB

namespace HahnDecomposition

/-- Hahn sign selection turns the whole signed measure into its Jordan total
variation.  In particular, the identity holds on every predictable set. -/
theorem restrict_pos_sub_compl_eq_totalVariationSignedMeasure
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {ν : Measure ℱ} (D : HahnDecomposition ℱ ν) :
    ν.restrict D.positiveSet + -(ν.restrict D.positiveSetᶜ) =
      totalVariationSignedMeasure ν := by
  let : MeasurableSpace (Time × Ω) := ℱ.predictable
  change ν.restrict D.positiveSet + -(ν.restrict D.positiveSetᶜ) =
    signedMeasureTotalVariation ν
  exact signedMeasure_hahnSplit_eq_totalVariation ν
    D.measurableSet_positiveSet D.posPart_compl D.negPart_positiveSet

end HahnDecomposition

end PredictableSignedMeasure

theorem PredictableSignedMeasure.HahnDecomposition.restrict_pos_sub_compl_univ_eq_totalVariation
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {ν : PredictableSignedMeasure.Measure ℱ}
    (D : PredictableSignedMeasure.HahnDecomposition ℱ ν) :
    (ν.restrict D.positiveSet +
      -(ν.restrict D.positiveSetᶜ)) Set.univ =
      (PredictableSignedMeasure.totalVariation ν).real Set.univ := by
  rw [D.restrict_pos_sub_compl_eq_totalVariationSignedMeasure]
  exact PredictableSignedMeasure.totalVariationSignedMeasure_apply
    ν MeasurableSet.univ

end FTAPTheorem42
