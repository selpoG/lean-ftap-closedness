/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableKernelHahnSeparation
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationIntegral
import Mathlib.Probability.Kernel.RadonNikodym
import FTAPTheorem42.Stochastic.FiniteVariation.CumulativeVariationJumpEnumeration

/-!
# Predictable Hahn selection on finite-variation paths

This file compares the predictable Hahn decomposition of the integrated
finite-variation measure with the Jordan decomposition on individual sample
paths.  Equality of their total masses forces the predictable time sections
to be pathwise Hahn separators almost surely.  Consequently the same
predictable sign used by a restricted trading strategy recovers the complete
pathwise variation and dominates every chronological increment.
-/

namespace FTAPTheorem42

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The predictable Hahn decomposition of the canonical integrated path
measure. -/
noncomputable def predictableHahnDecomposition
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableSignedMeasure.HahnDecomposition ℱ E.canonicalMeasure :=
  PredictableSignedMeasure.hahnDecomposition ℱ E.canonicalMeasure

/-- Equality of predictable and integrated pathwise total-variation masses
forces the predictable Hahn sections to separate the canonical Jordan
kernels almost surely. -/
theorem predictableHahnDecomposition_separates_canonicalKernels_ae
    (E : SIntegrableFiniteVariationBridge H)
    (hMass :
      (PredictableSignedMeasure.totalVariation E.canonicalMeasure).real
          Set.univ =
        (PredictableKernelMeasure.predictableMeasure ℱ μ
          (canonicalPositiveKernel E)).real Set.univ +
        (PredictableKernelMeasure.predictableMeasure ℱ μ
          (canonicalNegativeKernel E)).real Set.univ) :
    ∀ᵐ ω ∂μ,
      canonicalNegativeKernel E ω
          (PredictableFiniteVariationRestriction.timeSection
            E.predictableHahnDecomposition.positiveSet ω) = 0 ∧
        canonicalPositiveKernel E ω
          (PredictableFiniteVariationRestriction.timeSection
            E.predictableHahnDecomposition.positiveSet ω)ᶜ = 0 := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  change ∀ᵐ ω ∂μ,
    canonicalNegativeKernel E ω
        ((fun t => (t, ω)) ⁻¹'
          E.predictableHahnDecomposition.positiveSet) = 0 ∧
      canonicalPositiveKernel E ω
        ((fun t => (t, ω)) ⁻¹'
          E.predictableHahnDecomposition.positiveSetᶜ) = 0
  exact PredictableKernelMeasure.hahnDecomposition_separates_kernels_ae_of_totalVariationMass_eq
      E.predictableHahnDecomposition hMass

/-!
## Predictable Hahn separation of finite-variation jumps

The rational crossings of cumulative variation form a predictable countable
cover of all nonzero left jumps.  Splitting that cover according to the sign
of the predictable left-jump process therefore separates the atomic parts of
the pathwise Jordan measures.  This leaves only the continuous
finite-variation part in the predictable/pathwise Hahn gluing problem.
-/

/-- The predictable countable union of all rational cumulative-variation
jump crossings. -/
noncomputable def predictableJumpSupport
    (_E : SIntegrableFiniteVariationBridge H) : Set (ℝ≥0 × Ω) :=
  ⋃ n, CumulativeVariationJumpEnumeration.jumpCrossingSet H n

/-- On the jump support, retain the points where the left jump is
nonnegative. -/
noncomputable def predictablePositiveJumpSet
    (E : SIntegrableFiniteVariationBridge H) : Set (ℝ≥0 × Ω) :=
  predictableJumpSupport E ∩
    {p | 0 ≤ processLeftJump H.finiteVariationPart p.1 p.2}

/-- On the jump support, retain the points where the left jump is negative. -/
noncomputable def predictableNegativeJumpSet
    (E : SIntegrableFiniteVariationBridge H) : Set (ℝ≥0 × Ω) :=
  predictableJumpSupport E ∩
    {p | processLeftJump H.finiteVariationPart p.1 p.2 < 0}

/-- The rational jump support is predictable. -/
theorem measurableSet_predictableJumpSupport
    (E : SIntegrableFiniteVariationBridge H) :
    MeasurableSet[ℱ.predictable] (predictableJumpSupport E) := by
  apply MeasurableSet.iUnion
  intro n
  exact CumulativeVariationJumpEnumeration.measurableSet_jumpCrossingSet
    H E.rightContinuous n

/-- The nonnegative part of the predictable jump support is predictable. -/
theorem measurableSet_predictablePositiveJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    MeasurableSet[ℱ.predictable] (predictablePositiveJumpSet E) := by
  apply (measurableSet_predictableJumpSupport E).inter
  exact stronglyMeasurable_const.measurableSet_le
    H.processLeftJump_finiteVariationPart_isPredictable

/-- The negative part of the predictable jump support is predictable. -/
theorem measurableSet_predictableNegativeJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    MeasurableSet[ℱ.predictable] (predictableNegativeJumpSet E) := by
  apply (measurableSet_predictableJumpSupport E).inter
  exact H.processLeftJump_finiteVariationPart_isPredictable.measurableSet_lt
    stronglyMeasurable_const

/-- Every nonzero left jump belongs to the predictable rational support. -/
theorem mem_predictableJumpSupport_of_leftJump_ne_zero
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) (t : ℝ≥0)
    (ht : processLeftJump H.finiteVariationPart t ω ≠ 0) :
    (t, ω) ∈ predictableJumpSupport E := by
  obtain ⟨n, hn⟩ :=
    CumulativeVariationJumpEnumeration.coversLeftJumpsUpTo_jumpCrossingSetUpTo
        H E.rightContinuous t ω t le_rfl ht
  exact Set.mem_iUnion.2 ⟨n, hn.1⟩

private theorem negativePathMeasure_nonnegativeJumpSection_eq_zero
    (E : SIntegrableFiniteVariationBridge H) (n : ℕ) (ω : Ω) :
    FiniteVariationKernel.negativePathMeasure
        H.finiteVariationPart_isBoundedVariation ω
        {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          0 ≤ processLeftJump H.finiteVariationPart t ω} = 0 := by
  let B : Set ℝ≥0 :=
    {t | (t, ω) ∈
        CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
      0 ≤ processLeftJump H.finiteVariationPart t ω}
  have hB : B.Subsingleton :=
    (CumulativeVariationJumpEnumeration.jumpCrossingSet_section_subsingleton
      H E.rightContinuous n ω).anti
      (by intro t ht; exact ht.1)
  change FiniteVariationKernel.negativePathMeasure
    H.finiteVariationPart_isBoundedVariation ω B = 0
  rcases hB.eq_empty_or_singleton with hEmpty | ⟨t, ht⟩
  · rw [show B = ∅ from hEmpty]
    simp
  · rw [show B = {t} from ht]
    unfold FiniteVariationKernel.negativePathMeasure
    apply FiniteVariationKernel.negPart_singleton_eq_zero_of_nonneg
    rw [FiniteVariationPath.signedMeasure_singleton
      (H.finiteVariationPart_isBoundedVariation ω) (E.rightContinuous ω)]
    have htB : t ∈ B := by rw [ht]; exact Set.mem_singleton t
    exact htB.2

private theorem positivePathMeasure_negativeJumpSection_eq_zero
    (E : SIntegrableFiniteVariationBridge H) (n : ℕ) (ω : Ω) :
    FiniteVariationKernel.positivePathMeasure
        H.finiteVariationPart_isBoundedVariation ω
        {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          processLeftJump H.finiteVariationPart t ω < 0} = 0 := by
  let B : Set ℝ≥0 :=
    {t | (t, ω) ∈
        CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
      processLeftJump H.finiteVariationPart t ω < 0}
  have hB : B.Subsingleton :=
    (CumulativeVariationJumpEnumeration.jumpCrossingSet_section_subsingleton
      H E.rightContinuous n ω).anti
      (by intro t ht; exact ht.1)
  change FiniteVariationKernel.positivePathMeasure
    H.finiteVariationPart_isBoundedVariation ω B = 0
  rcases hB.eq_empty_or_singleton with hEmpty | ⟨t, ht⟩
  · rw [show B = ∅ from hEmpty]
    simp
  · rw [show B = {t} from ht]
    unfold FiniteVariationKernel.positivePathMeasure
    apply FiniteVariationKernel.posPart_singleton_eq_zero_of_nonpos
    rw [FiniteVariationPath.signedMeasure_singleton
      (H.finiteVariationPart_isBoundedVariation ω) (E.rightContinuous ω)]
    have htB : t ∈ B := by rw [ht]; exact Set.mem_singleton t
    exact htB.2.le

/-- The negative Jordan kernel vanishes on the predictable nonnegative-jump
section, path by path. -/
theorem canonicalNegativeKernel_predictablePositiveJumpSet_eq_zero
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    canonicalNegativeKernel E ω
      (PredictableFiniteVariationRestriction.timeSection
        (predictablePositiveJumpSet E) ω) = 0 := by
  rw [canonicalNegativeKernel_apply E ω]
  have hSection :
      PredictableFiniteVariationRestriction.timeSection
          (predictablePositiveJumpSet E) ω =
        ⋃ n, {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          0 ≤ processLeftJump H.finiteVariationPart t ω} := by
    ext t
    simp [PredictableFiniteVariationRestriction.timeSection,
      predictablePositiveJumpSet, predictableJumpSupport]
  have hzero : FiniteVariationKernel.negativePathMeasure
      H.finiteVariationPart_isBoundedVariation ω
        (⋃ n, {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          0 ≤ processLeftJump H.finiteVariationPart t ω}) = 0 :=
    measure_iUnion_null fun n =>
      negativePathMeasure_nonnegativeJumpSection_eq_zero E n ω
  rw [Measure.smul_apply, hSection, hzero, smul_zero]

/-- The positive Jordan kernel vanishes on the predictable negative-jump
section, path by path. -/
theorem canonicalPositiveKernel_predictableNegativeJumpSet_eq_zero
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    canonicalPositiveKernel E ω
      (PredictableFiniteVariationRestriction.timeSection
        (predictableNegativeJumpSet E) ω) = 0 := by
  rw [canonicalPositiveKernel_apply E ω]
  have hSection :
      PredictableFiniteVariationRestriction.timeSection
          (predictableNegativeJumpSet E) ω =
        ⋃ n, {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          processLeftJump H.finiteVariationPart t ω < 0} := by
    ext t
    simp [PredictableFiniteVariationRestriction.timeSection,
      predictableNegativeJumpSet, predictableJumpSupport]
  have hzero : FiniteVariationKernel.positivePathMeasure
      H.finiteVariationPart_isBoundedVariation ω
        (⋃ n, {t | (t, ω) ∈
            CumulativeVariationJumpEnumeration.jumpCrossingSet H n ∧
          processLeftJump H.finiteVariationPart t ω < 0}) = 0 :=
    measure_iUnion_null fun n =>
      positivePathMeasure_negativeJumpSection_eq_zero E n ω
  rw [Measure.smul_apply, hSection, hzero, smul_zero]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
