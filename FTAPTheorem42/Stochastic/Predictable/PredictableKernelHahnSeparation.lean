/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnVariationMass
import FTAPTheorem42.Stochastic.Predictable.PredictableKernelMeasure

/-!
# Pathwise separation from predictable total-variation mass

For two finite kernels, their difference on predictable time--sample space
always has total variation at most the sum of their integrated masses.  If
equality holds, the predictable Hahn set loses no pathwise Jordan mass: its
time sections separate the two kernels almost surely.

This is the measure-theoretic reduction needed for the finite-variation part
of Lemma 4.7.  The remaining stochastic input is precisely the equality of
the predictable total-variation mass with the integrated pathwise variation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Time] [LinearOrder Time] [OrderBot Time]
  [TopologicalSpace Time] [OpensMeasurableSpace Time]
  [OrderClosedTopology Time]

namespace PredictableKernelMeasure

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {κp κn : Kernel Ω Time} [IsFiniteKernel κp] [IsFiniteKernel κn]

private theorem hahn_badMass_real_eq_zero_of_totalVariationMass_eq
    (D : PredictableSignedMeasure.HahnDecomposition ℱ
      (signedMeasure ℱ μ κp κn))
    (hMass :
      (PredictableSignedMeasure.totalVariation
        (signedMeasure ℱ μ κp κn)).real Set.univ =
        (predictableMeasure ℱ μ κp).real Set.univ +
          (predictableMeasure ℱ μ κn).real Set.univ) :
    (predictableMeasure ℱ μ κn).real D.positiveSet = 0 ∧
      (predictableMeasure ℱ μ κp).real D.positiveSetᶜ = 0 := by
  let ν := signedMeasure ℱ μ κp κn
  let νp := predictableMeasure ℱ μ κp
  let νn := predictableMeasure ℱ μ κn
  have hP := D.measurableSet_positiveSet
  have hHahn :=
    D.restrict_pos_sub_compl_univ_eq_totalVariation
  have hVariation :
      (PredictableSignedMeasure.totalVariation ν).real Set.univ =
        ν D.positiveSet - ν D.positiveSetᶜ := by
    rw [← hHahn]
    rw [add_apply, neg_apply,
      VectorMeasure.restrict_apply _ hP MeasurableSet.univ,
      VectorMeasure.restrict_apply _ hP.compl MeasurableSet.univ]
    simp only [univ_inter, sub_eq_add_neg]
    rfl
  have hSignedP : ν D.positiveSet =
      νp.real D.positiveSet - νn.real D.positiveSet := by
    exact Measure.toSignedMeasure_sub_apply hP
  have hSignedN : ν D.positiveSetᶜ =
      νp.real D.positiveSetᶜ - νn.real D.positiveSetᶜ := by
    exact Measure.toSignedMeasure_sub_apply hP.compl
  have hνp : νp.real D.positiveSet + νp.real D.positiveSetᶜ =
      νp.real Set.univ :=
    measureReal_add_measureReal_compl hP
  have hνn : νn.real D.positiveSet + νn.real D.positiveSetᶜ =
      νn.real Set.univ :=
    measureReal_add_measureReal_compl hP
  have hzero :
      2 * (νn.real D.positiveSet + νp.real D.positiveSetᶜ) = 0 := by
    rw [hVariation, hSignedP, hSignedN] at hMass
    dsimp only [νp, νn] at hMass
    linarith
  have hsum : νn.real D.positiveSet + νp.real D.positiveSetᶜ = 0 := by
    linarith
  exact (add_eq_zero_iff_of_nonneg measureReal_nonneg measureReal_nonneg).mp hsum

/-- If the predictable total variation has the full integrated kernel mass,
the positive Hahn set separates the negative and positive kernel measures. -/
theorem hahnDecomposition_separates_predictableMeasures_of_totalVariationMass_eq
    (D : PredictableSignedMeasure.HahnDecomposition ℱ
      (signedMeasure ℱ μ κp κn))
    (hMass :
      (PredictableSignedMeasure.totalVariation
        (signedMeasure ℱ μ κp κn)).real Set.univ =
        (predictableMeasure ℱ μ κp).real Set.univ +
          (predictableMeasure ℱ μ κn).real Set.univ) :
    predictableMeasure ℱ μ κn D.positiveSet = 0 ∧
      predictableMeasure ℱ μ κp D.positiveSetᶜ = 0 := by
  have hreal :=
    hahn_badMass_real_eq_zero_of_totalVariationMass_eq D hMass
  constructor
  · exact ((ENNReal.toReal_eq_zero_iff _).mp hreal.1).resolve_right
      (measure_ne_top _ _)
  · exact ((ENNReal.toReal_eq_zero_iff _).mp hreal.2).resolve_right
      (measure_ne_top _ _)

/-- Under the same mass identity, almost every time section of the
predictable Hahn set separates the original kernels. -/
theorem hahnDecomposition_separates_kernels_ae_of_totalVariationMass_eq
    (D : PredictableSignedMeasure.HahnDecomposition ℱ
      (signedMeasure ℱ μ κp κn))
    (hMass :
      (PredictableSignedMeasure.totalVariation
        (signedMeasure ℱ μ κp κn)).real Set.univ =
        (predictableMeasure ℱ μ κp).real Set.univ +
          (predictableMeasure ℱ μ κn).real Set.univ) :
    ∀ᵐ ω ∂μ,
      κn ω ((fun t => (t, ω)) ⁻¹' D.positiveSet) = 0 ∧
        κp ω ((fun t => (t, ω)) ⁻¹' D.positiveSetᶜ) = 0 := by
  have hzero :=
    hahnDecomposition_separates_predictableMeasures_of_totalVariationMass_eq
      D hMass
  have hnegIntegral :
      ∫⁻ ω, κn ω ((fun t => (t, ω)) ⁻¹' D.positiveSet) ∂μ = 0 := by
    rw [← predictableMeasure_apply D.measurableSet_positiveSet]
    exact hzero.1
  have hposIntegral :
      ∫⁻ ω, κp ω ((fun t => (t, ω)) ⁻¹' D.positiveSetᶜ) ∂μ = 0 := by
    rw [← predictableMeasure_apply D.measurableSet_positiveSet.compl]
    exact hzero.2
  have hPprod : MeasurableSet D.positiveSet :=
    PredictableKernelMeasure.predictable_le_prod ℱ D.positiveSet
      D.measurableSet_positiveSet
  filter_upwards [
    (lintegral_eq_zero_iff
      (Kernel.measurable_kernel_prodMk_right hPprod)).mp hnegIntegral,
    (lintegral_eq_zero_iff
      (Kernel.measurable_kernel_prodMk_right hPprod.compl)).mp hposIntegral]
      with ω hneg hpos
  exact ⟨hneg, hpos⟩

end PredictableKernelMeasure

end FTAPTheorem42
