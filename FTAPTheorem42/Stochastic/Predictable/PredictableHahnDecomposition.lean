/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableRestriction
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Hahn decomposition on the predictable sigma algebra

The finite-variation argument in Lemma 4.7 selects the positive part of a
signed measure on predictable time--sample space.  This file packages the
Hahn decomposition directly on mathlib's predictable sigma algebra and turns
its positive set into a predictable sign process.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [Preorder Time] [OrderBot Time]

namespace PredictableSignedMeasure

/-- A signed measure carried by the predictable sigma algebra of a filtration. -/
abbrev Measure
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) :=
  @SignedMeasure (Time × Ω) ℱ.predictable

/-- The Jordan decomposition in the predictable measurable space. -/
noncomputable def jordanDecomposition
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    (ν : Measure ℱ) : @JordanDecomposition (Time × Ω) ℱ.predictable :=
  @SignedMeasure.toJordanDecomposition (Time × Ω) ℱ.predictable ν

/-- The total variation measure in the predictable measurable space. -/
noncomputable def totalVariation
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    (ν : Measure ℱ) : @MeasureTheory.Measure (Time × Ω) ℱ.predictable :=
  @SignedMeasure.totalVariation (Time × Ω) ℱ.predictable ν

section HahnData

variable (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))

/-- A Hahn decomposition of a signed measure on predictable time--sample space. -/
structure HahnDecomposition (ν : Measure ℱ) where
  /-- The predictable positive set. -/
  positiveSet : Set (Time × Ω)
  measurableSet_positiveSet : MeasurableSet[ℱ.predictable] positiveSet
  nonnegative_on : ∀ B, MeasurableSet[ℱ.predictable] B →
    B ⊆ positiveSet → 0 ≤ ν B
  nonpositive_on_compl : ∀ B, MeasurableSet[ℱ.predictable] B →
    B ⊆ positiveSetᶜ → ν B ≤ 0
  posPart_compl_eq_zero :
    (@JordanDecomposition.posPart (Time × Ω) ℱ.predictable
      (jordanDecomposition ν)) positiveSetᶜ = 0
  negPart_positiveSet_eq_zero :
    (@JordanDecomposition.negPart (Time × Ω) ℱ.predictable
      (jordanDecomposition ν)) positiveSet = 0

end HahnData

/-- Every signed measure on predictable time--sample space has a predictable
Hahn decomposition. -/
noncomputable def hahnDecomposition
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))
    (ν : Measure ℱ) : HahnDecomposition ℱ ν := by
  classical
  let : MeasurableSpace (Time × Ω) := ℱ.predictable
  let j := jordanDecomposition ν
  let hex := j.exists_compl_positive_negative
  let N := Classical.choose hex
  obtain ⟨hN, hneg, hpos, hjpos, hjneg⟩ := Classical.choose_spec hex
  have hj : j.toSignedMeasure = ν :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition ν
  have hneg' : ν ≤[N] 0 := by
    dsimp only [N]
    simpa only [hj] using hneg
  have hpos' : 0 ≤[Nᶜ] ν := by
    dsimp only [N]
    simpa only [hj] using hpos
  refine ⟨Nᶜ, hN.compl, ?_, ?_, ?_, hjneg⟩
  · intro B hB hsub
    exact (VectorMeasure.restrict_le_restrict_iff 0 ν hN.compl).1 hpos' hB hsub
  · intro B hB hsub
    apply (VectorMeasure.restrict_le_restrict_iff ν 0 hN).1 hneg' hB
    simpa only [compl_compl] using hsub
  · simpa only [N, j, jordanDecomposition, compl_compl] using hjpos

namespace HahnDecomposition

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
  {ν : Measure ℱ}

/-- The positive Jordan measure is concentrated on the positive Hahn set. -/
theorem posPart_compl (D : HahnDecomposition ℱ ν) :
    (@JordanDecomposition.posPart (Time × Ω) ℱ.predictable
      (jordanDecomposition ν)) D.positiveSetᶜ = 0 :=
  D.posPart_compl_eq_zero

/-- The negative Jordan measure vanishes on the positive Hahn set. -/
theorem negPart_positiveSet (D : HahnDecomposition ℱ ν) :
    (@JordanDecomposition.negPart (Time × Ω) ℱ.predictable
      (jordanDecomposition ν)) D.positiveSet = 0 :=
  D.negPart_positiveSet_eq_zero

end HahnDecomposition

end PredictableSignedMeasure

end FTAPTheorem42
