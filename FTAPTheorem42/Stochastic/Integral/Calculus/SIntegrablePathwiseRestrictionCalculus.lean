/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Predictable.PredictablePathwiseHahnSeparator
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStoppingCalculus

/-!
# Pathwise predictable restriction calculus

Predictable-set restriction of a stochastic integral restricts its
finite-variation Stieltjes measure on every path and multiplies its jumps by
the predictable indicator.  This file records those concrete integration
identities and immediately consumes them at the positive set of the
predictable Hahn decomposition.

The resulting positive restriction has increasing finite-variation part and
its increments dominate those of the original strategy.  This is the
pathwise strategy realization used in the finite aggregation step of Lemma
4.7.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The left jump selected by a time--sample set. -/
noncomputable def predictableRestrictedLeftJump
    (B : Set (ℝ≥0 × Ω)) (X : Process Ω) : Process Ω := by
  classical
  exact fun t ω =>
    if (t, ω) ∈ B then processLeftJump X t ω else 0

namespace SIntegrablePathwiseRestrictionCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- A predictable set has a Borel time section at every sample point. -/
theorem measurableSet_timeSection
    (B : Set (ℝ≥0 × Ω)) (hB : MeasurableSet[ℱ.predictable] B)
    (ω : Ω) :
    MeasurableSet (PredictableFiniteVariationRestriction.timeSection B ω) := by
  have hBprod : MeasurableSet B :=
    (PredictableKernelMeasure.predictable_le_prod ℱ) B hB
  change MeasurableSet ((fun t : ℝ≥0 => (t, ω)) ⁻¹' B)
  exact hBprod.preimage measurable_prodMk_right

namespace HahnPositive

variable {L : SIntegrableStrategy D}

theorem positive_mass_nonnegative_and_dominates_ae
    (P : PredictablePathwiseHahnSeparator L) :
    ∀ᵐ ω ∂μ, ∀ a b : ℝ≥0, a ≤ b →
      let B := PredictableFiniteVariationRestriction.timeSection P.positiveSet ω
      let ν := FiniteVariationPath.signedMeasure
        (L.finiteVariationPart_isBoundedVariation ω)
      0 ≤ ν (B ∩ Set.Ioc a b) ∧
        L.finiteVariationPart b ω - L.finiteVariationPart a ω ≤
          ν (B ∩ Set.Ioc a b) := by
  filter_upwards [P.separatesJordan_ae] with ω hω
  intro a b hab
  let ν := FiniteVariationPath.signedMeasure
    (L.finiteVariationPart_isBoundedVariation ω)
  let νp := ν.toJordanDecomposition.posPart
  let νn := ν.toJordanDecomposition.negPart
  let B := PredictableFiniteVariationRestriction.timeSection P.positiveSet ω
  let I := Set.Ioc a b
  have hB : MeasurableSet B :=
    measurableSet_timeSection P.positiveSet P.measurableSet_positiveSet ω
  have hI : MeasurableSet I := measurableSet_Ioc
  have hBI : MeasurableSet (B ∩ I) := hB.inter hI
  have hnegB : νn B = 0 := hω.1
  have hposBc : νp Bᶜ = 0 := hω.2
  have hnegBI : νn (B ∩ I) = 0 :=
    measure_mono_null inter_subset_left hnegB
  have hposRestrict : νp.restrict B = νp := by
    have hsum := Measure.restrict_add_restrict_compl (μ := νp) hB
    have hzero : νp.restrict Bᶜ = 0 := Measure.restrict_zero_set hposBc
    rw [hzero, add_zero] at hsum
    exact hsum
  have hposBI : νp.real (B ∩ I) = νp.real I := by
    apply congrArg ENNReal.toReal
    calc
      νp (B ∩ I) = νp (I ∩ B) := by rw [inter_comm]
      _ = νp.restrict B I := (Measure.restrict_apply hI).symm
      _ = νp I := by rw [hposRestrict]
  have hsignedBI : ν (B ∩ I) = νp.real (B ∩ I) := by
    have hdecomp : νp.real (B ∩ I) - νn.real (B ∩ I) =
        ν (B ∩ I) := by
      rw [← Measure.toSignedMeasure_sub_apply hBI,
        ← JordanDecomposition.toSignedMeasure,
        SignedMeasure.toSignedMeasure_toJordanDecomposition]
    have hnegReal : νn.real (B ∩ I) = 0 :=
      (measureReal_eq_zero_iff (μ := νn) (s := B ∩ I)).2 hnegBI
    linarith
  have hsignedI : ν I = νp.real I - νn.real I := by
    rw [← Measure.toSignedMeasure_sub_apply hI,
      ← JordanDecomposition.toSignedMeasure,
      SignedMeasure.toSignedMeasure_toJordanDecomposition]
  dsimp only
  constructor
  · rw [hsignedBI]
    exact measureReal_nonneg
  · rw [← FiniteVariationPath.signedMeasure_Ioc
      (L.finiteVariationPart_isBoundedVariation ω)
      (L.finiteVariationPart_isRightContinuous ω) hab]
    change ν I ≤ ν (B ∩ I)
    rw [hsignedBI, hsignedI, hposBI]
    exact sub_le_self _ measureReal_nonneg

end HahnPositive

end SIntegrablePathwiseRestrictionCalculus

end FTAPTheorem42
