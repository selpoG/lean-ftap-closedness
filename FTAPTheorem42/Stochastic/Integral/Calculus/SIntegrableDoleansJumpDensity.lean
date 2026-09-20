/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansDensity
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePredictableJumpHahn

/-!
# Jump-corrected predictable Doléans density

The predictable Radon--Nikodym density of the integrated signed measure is
only specified up to integrated-variation null sets.  For the pathwise
construction it is useful to choose a version which is exact at every
nonzero jump.  On the predictable jump support the backward-ratio density
has precisely this property.  The Jordan kernels are already separated
there, so Radon--Nikodym uniqueness shows that this replacement does not
change the represented signed measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- Use the concrete backward density on the predictable jump support and
the clipped Radon--Nikodym density elsewhere. -/
noncomputable def jumpCorrectedCanonicalVariationDensity
    (E : SIntegrableFiniteVariationBridge H) : ℝ≥0 × Ω → ℝ :=
  by
    classical
    exact fun p => if p ∈ predictableJumpSupport E then
      variationBackwardDensity H p.1 p.2
    else clippedCanonicalVariationDensity E p

/-- The jump-corrected density remains predictable. -/
theorem jumpCorrectedCanonicalVariationDensity_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H) :
    StronglyMeasurable[ℱ.predictable]
      (jumpCorrectedCanonicalVariationDensity E) := by
  exact StronglyMeasurable.ite
    (measurableSet_predictableJumpSupport E)
    (variationBackwardDensity_isStronglyPredictable E)
    (clippedCanonicalVariationDensity_stronglyMeasurable E)

/-- The jump-corrected density is bounded by one pointwise. -/
theorem abs_jumpCorrectedCanonicalVariationDensity_le_one
    (E : SIntegrableFiniteVariationBridge H) (p : ℝ≥0 × Ω) :
    |jumpCorrectedCanonicalVariationDensity E p| ≤ 1 := by
  by_cases hp : p ∈ predictableJumpSupport E
  · rw [jumpCorrectedCanonicalVariationDensity, ite_eq_left hp]
    exact abs_variationBackwardDensity_le_one E p.1 p.2
  · rw [jumpCorrectedCanonicalVariationDensity, ite_eq_right hp]
    exact abs_clippedCanonicalVariationDensity_le_one E p

/-- At every nonzero left jump, the corrected density is the exact pathwise
polar sign. -/
theorem jumpCorrectedCanonicalVariationDensity_eq_leftJump_div_abs
    (E : SIntegrableFiniteVariationBridge H) {t : ℝ≥0} {ω : Ω}
    (hJump : processLeftJump H.finiteVariationPart t ω ≠ 0) :
    jumpCorrectedCanonicalVariationDensity E (t, ω) =
      processLeftJump H.finiteVariationPart t ω /
        |processLeftJump H.finiteVariationPart t ω| := by
  rw [jumpCorrectedCanonicalVariationDensity,
    ite_eq_left (mem_predictableJumpSupport_of_leftJump_ne_zero E ω t hJump)]
  exact variationBackwardDensity_eq_leftJump_div_abs E hJump

private theorem predictableNegativeMeasure_positiveJumpSet_eq_zero
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableKernelMeasure.predictableMeasure ℱ μ
      (canonicalNegativeKernel E) (predictablePositiveJumpSet E) = 0 := by
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  rw [PredictableKernelMeasure.predictableMeasure_apply
    (measurableSet_predictablePositiveJumpSet E)]
  change (∫⁻ ω, canonicalNegativeKernel E ω
    (PredictableFiniteVariationRestriction.timeSection
      (predictablePositiveJumpSet E) ω) ∂μ) = 0
  simp_rw [canonicalNegativeKernel_predictablePositiveJumpSet_eq_zero E]
  simp

private theorem predictablePositiveMeasure_negativeJumpSet_eq_zero
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableKernelMeasure.predictableMeasure ℱ μ
      (canonicalPositiveKernel E) (predictableNegativeJumpSet E) = 0 := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  rw [PredictableKernelMeasure.predictableMeasure_apply
    (measurableSet_predictableNegativeJumpSet E)]
  change (∫⁻ ω, canonicalPositiveKernel E ω
    (PredictableFiniteVariationRestriction.timeSection
      (predictableNegativeJumpSet E) ω) ∂μ) = 0
  simp_rw [canonicalPositiveKernel_predictableNegativeJumpSet_eq_zero E]
  simp

private theorem canonicalMeasure_restrict_positiveJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    E.canonicalMeasure.restrict (predictablePositiveJumpSet E) =
      ((canonicalVariationMeasure E).restrict
        (predictablePositiveJumpSet E)).toSignedMeasure := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  let νp := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalPositiveKernel E)
  let νn := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalNegativeKernel E)
  let P := predictablePositiveJumpSet E
  have hP : MeasurableSet P := measurableSet_predictablePositiveJumpSet E
  have hνn : νn.restrict P = 0 := Measure.restrict_zero_set
    (predictableNegativeMeasure_positiveJumpSet_eq_zero E)
  change (νp.toSignedMeasure - νn.toSignedMeasure).restrict P =
    ((νp + νn).restrict P).toSignedMeasure
  rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hP,
    VectorMeasure.restrict_toSignedMeasure hP]
  have hνnSigned : (νn.restrict P).toSignedMeasure = 0 :=
    (Measure.toSignedMeasure_congr hνn).trans Measure.toSignedMeasure_zero
  have hρ : (νp + νn).restrict P = νp.restrict P := by
    rw [Measure.restrict_add, hνn, add_zero]
  have hρSigned : ((νp + νn).restrict P).toSignedMeasure =
      (νp.restrict P).toSignedMeasure :=
    Measure.toSignedMeasure_congr hρ
  rw [hνnSigned, hρSigned, sub_zero]

private theorem canonicalMeasure_restrict_negativeJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    E.canonicalMeasure.restrict (predictableNegativeJumpSet E) =
      -((canonicalVariationMeasure E).restrict
        (predictableNegativeJumpSet E)).toSignedMeasure := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  let νp := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalPositiveKernel E)
  let νn := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalNegativeKernel E)
  let N := predictableNegativeJumpSet E
  have hN : MeasurableSet N := measurableSet_predictableNegativeJumpSet E
  have hνp : νp.restrict N = 0 := Measure.restrict_zero_set
    (predictablePositiveMeasure_negativeJumpSet_eq_zero E)
  change (νp.toSignedMeasure - νn.toSignedMeasure).restrict N =
    -((νp + νn).restrict N).toSignedMeasure
  rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hN,
    VectorMeasure.restrict_toSignedMeasure hN]
  have hνpSigned : (νp.restrict N).toSignedMeasure = 0 :=
    (Measure.toSignedMeasure_congr hνp).trans Measure.toSignedMeasure_zero
  have hρ : (νp + νn).restrict N = νn.restrict N := by
    rw [Measure.restrict_add, hνp, zero_add]
  have hρSigned : ((νp + νn).restrict N).toSignedMeasure =
      (νn.restrict N).toSignedMeasure :=
    Measure.toSignedMeasure_congr hρ
  rw [hνpSigned, hρSigned, zero_sub]

private theorem restrict_measureWithDensityᵥ
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) (f : X → ℝ)
    {B : Set X} (hB : MeasurableSet B) (hf : Integrable f ρ) :
    (ρ.withDensityᵥ f).restrict B =
      (ρ.restrict B).withDensityᵥ f := by
  ext C hC
  rw [VectorMeasure.restrict_apply _ hB hC,
    withDensityᵥ_apply hf (hC.inter hB),
    withDensityᵥ_apply hf.restrict hC]
  rw [Measure.restrict_restrict hC]

private theorem withDensityᵥ_one_eq_toSignedMeasure
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ] :
    ρ.withDensityᵥ (fun _ => (1 : ℝ)) = ρ.toSignedMeasure := by
  ext B hB
  rw [withDensityᵥ_apply (integrable_const (1 : ℝ)) hB,
    Measure.toSignedMeasure_apply_measurable hB,
    setIntegral_one_eq_measureReal]

private theorem withDensityᵥ_negOne_eq_neg_toSignedMeasure
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ] :
    ρ.withDensityᵥ (fun _ => (-1 : ℝ)) = -ρ.toSignedMeasure := by
  rw [show (fun _ : X => (-1 : ℝ)) = -(fun _ => (1 : ℝ)) by funext x; simp]
  rw [withDensityᵥ_neg, withDensityᵥ_one_eq_toSignedMeasure]

/-- The clipped Radon--Nikodym density equals `1` on the positive jump
piece, almost everywhere for integrated path variation restricted there. -/
theorem clippedCanonicalVariationDensity_ae_eq_one_on_positiveJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    clippedCanonicalVariationDensity E =ᵐ[
      (canonicalVariationMeasure E).restrict (predictablePositiveJumpSet E)]
        (fun _ => (1 : ℝ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let ρ := canonicalVariationMeasure E
  let h := clippedCanonicalVariationDensity E
  let P := predictablePositiveJumpSet E
  have hInt : Integrable h ρ :=
    (SignedMeasure.integrable_rnDeriv E.canonicalMeasure ρ).congr
      (clippedCanonicalVariationDensity_ae_eq E).symm
  have hRestricted := congrArg
    (fun ν : @VectorMeasure (ℝ≥0 × Ω) ℱ.predictable ℝ _ _ => ν.restrict P)
    (withDensity_clippedCanonicalVariationDensity_eq_canonicalMeasure E)
  have hDensity : (ρ.restrict P).withDensityᵥ h =
      (ρ.restrict P).withDensityᵥ (fun _ => (1 : ℝ)) := by
    rw [← restrict_measureWithDensityᵥ ρ h
      (measurableSet_predictablePositiveJumpSet E) hInt,
      hRestricted, canonicalMeasure_restrict_positiveJumpSet E,
      withDensityᵥ_one_eq_toSignedMeasure]
  exact hInt.restrict.ae_eq_of_withDensityᵥ_eq
    (integrable_const (1 : ℝ)) hDensity

/-- The clipped Radon--Nikodym density equals `-1` on the negative jump
piece, almost everywhere for integrated path variation restricted there. -/
theorem clippedCanonicalVariationDensity_ae_eq_negOne_on_negativeJumpSet
    (E : SIntegrableFiniteVariationBridge H) :
    clippedCanonicalVariationDensity E =ᵐ[
      (canonicalVariationMeasure E).restrict (predictableNegativeJumpSet E)]
        (fun _ => (-1 : ℝ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let ρ := canonicalVariationMeasure E
  let h := clippedCanonicalVariationDensity E
  let N := predictableNegativeJumpSet E
  have hInt : Integrable h ρ :=
    (SignedMeasure.integrable_rnDeriv E.canonicalMeasure ρ).congr
      (clippedCanonicalVariationDensity_ae_eq E).symm
  have hRestricted := congrArg
    (fun ν : @VectorMeasure (ℝ≥0 × Ω) ℱ.predictable ℝ _ _ => ν.restrict N)
    (withDensity_clippedCanonicalVariationDensity_eq_canonicalMeasure E)
  have hDensity : (ρ.restrict N).withDensityᵥ h =
      (ρ.restrict N).withDensityᵥ (fun _ => (-1 : ℝ)) := by
    rw [← restrict_measureWithDensityᵥ ρ h
      (measurableSet_predictableNegativeJumpSet E) hInt,
      hRestricted, canonicalMeasure_restrict_negativeJumpSet E,
      withDensityᵥ_negOne_eq_neg_toSignedMeasure]
  exact hInt.restrict.ae_eq_of_withDensityᵥ_eq
    (integrable_const (-1 : ℝ)) hDensity

private theorem leftJump_ne_zero_of_mem_predictableJumpSupport
    (E : SIntegrableFiniteVariationBridge H) {p : ℝ≥0 × Ω}
    (hp : p ∈ predictableJumpSupport E) :
    processLeftJump H.finiteVariationPart p.1 p.2 ≠ 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hp
  have hVJump : 0 < processLeftJump (cumulativeVariation H) p.1 p.2 := by
    unfold processLeftJump
    exact sub_pos.mpr (hn.1.trans hn.2)
  rw [CumulativeVariationJumpEnumeration.processLeftJump_cumulativeVariation_eq_abs
    H E.rightContinuous] at hVJump
  exact abs_pos.mp hVJump

private theorem variationBackwardDensity_eq_one_on_positiveJumpSet
    (E : SIntegrableFiniteVariationBridge H) {p : ℝ≥0 × Ω}
    (hp : p ∈ predictablePositiveJumpSet E) :
    variationBackwardDensity H p.1 p.2 = 1 := by
  have hJump := leftJump_ne_zero_of_mem_predictableJumpSupport E hp.1
  rw [variationBackwardDensity_eq_leftJump_div_abs E hJump,
    abs_of_nonneg hp.2, div_self hJump]

private theorem variationBackwardDensity_eq_negOne_on_negativeJumpSet
    (E : SIntegrableFiniteVariationBridge H) {p : ℝ≥0 × Ω}
    (hp : p ∈ predictableNegativeJumpSet E) :
    variationBackwardDensity H p.1 p.2 = -1 := by
  have hJump := leftJump_ne_zero_of_mem_predictableJumpSupport E hp.1
  rw [variationBackwardDensity_eq_leftJump_div_abs E hJump,
    abs_of_neg hp.2]
  exact div_neg_self hJump

/-- Correcting the density on the jump support changes it only on an
integrated-variation null set. -/
theorem jumpCorrectedCanonicalVariationDensity_ae_eq
    (E : SIntegrableFiniteVariationBridge H) :
    jumpCorrectedCanonicalVariationDensity E =ᵐ[canonicalVariationMeasure E]
      clippedCanonicalVariationDensity E := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hPos : ∀ᵐ p ∂canonicalVariationMeasure E,
      p ∈ predictablePositiveJumpSet E →
        clippedCanonicalVariationDensity E p = 1 :=
    (ae_restrict_iff' (measurableSet_predictablePositiveJumpSet E)).1
      (clippedCanonicalVariationDensity_ae_eq_one_on_positiveJumpSet E)
  have hNeg : ∀ᵐ p ∂canonicalVariationMeasure E,
      p ∈ predictableNegativeJumpSet E →
        clippedCanonicalVariationDensity E p = -1 :=
    (ae_restrict_iff' (measurableSet_predictableNegativeJumpSet E)).1
      (clippedCanonicalVariationDensity_ae_eq_negOne_on_negativeJumpSet E)
  filter_upwards [hPos, hNeg] with p hpPos hpNeg
  by_cases hp : p ∈ predictableJumpSupport E
  · rw [jumpCorrectedCanonicalVariationDensity, ite_eq_left hp]
    rcases le_or_gt 0
        (processLeftJump H.finiteVariationPart p.1 p.2) with hnonneg | hneg
    · have hp' : p ∈ predictablePositiveJumpSet E := ⟨hp, hnonneg⟩
      rw [variationBackwardDensity_eq_one_on_positiveJumpSet E hp', hpPos hp']
    · have hp' : p ∈ predictableNegativeJumpSet E := ⟨hp, hneg⟩
      rw [variationBackwardDensity_eq_negOne_on_negativeJumpSet E hp', hpNeg hp']
  · rw [jumpCorrectedCanonicalVariationDensity, ite_eq_right hp]

/-- The jump-corrected bounded predictable density represents the original
canonical signed measure. -/
theorem withDensity_jumpCorrectedCanonicalVariationDensity_eq_canonicalMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    (canonicalVariationMeasure E).withDensityᵥ
        (jumpCorrectedCanonicalVariationDensity E) = E.canonicalMeasure := by
  rw [← withDensity_clippedCanonicalVariationDensity_eq_canonicalMeasure E]
  exact WithDensityᵥEq.congr_ae
    (jumpCorrectedCanonicalVariationDensity_ae_eq E)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
