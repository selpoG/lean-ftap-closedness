/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessTerminal
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationTerminalCompletion
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryFiniteVariationIntegral

/-!
# Cumulative finite-variation integrals of elementary strategies

The cumulative process constructed from the predictable Doléans density is
identified here with the actual running gain of a predictable elementary
strategy against the finite-variation component.  The identity holds outside
one null set simultaneously at every time.

The proof first rewrites the elementary pathwise integral up to `T` as the
signed Stieltjes integral of the raw elementary integrand restricted to
`(0,T]`.  The Doléans signed-measure identity then changes this integral to
the cumulative density integral already used by the process completion.
-/

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableElementaryInterval

/-- Restricting one raw elementary integrand to `(0,T]` gives exactly the
clamped interval integrand used by its pathwise finite-variation integral. -/
theorem indicator_Ioc_zero_integrand_eq_clamped
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (T : NNReal) (omega : Omega) :
    (Ioc 0 T).indicator (fun t => B.integrand t omega) =
      (Ioc (B.interval.startTime omega)
        (min T (B.interval.stopTime omega))).indicator
          (fun _ => B.interval.coefficient omega) := by
  funext t
  by_cases hLeft : 0 < t
  · by_cases hT : t ≤ T
    · by_cases hStart : B.interval.startTime omega < t
      · by_cases hStop : t ≤ B.interval.stopTime omega
        · simp [PredictableElementaryInterval.integrand, hLeft, hT,
            hStart, hStop]
        · have hMin : ¬ t ≤ min T (B.interval.stopTime omega) := by
            exact fun ht => hStop (ht.trans (min_le_right _ _))
          simp [PredictableElementaryInterval.integrand, hLeft, hT,
            hStart, hStop, hMin]
      · simp [PredictableElementaryInterval.integrand, hLeft, hT, hStart]
    · have hMin : ¬ t ≤ min T (B.interval.stopTime omega) := by
        exact fun ht => hT (ht.trans (min_le_left _ _))
      simp [PredictableElementaryInterval.integrand, hLeft, hT, hMin]
  · have hStart : ¬ B.interval.startTime omega < t := by
      exact fun h => hLeft (bot_le.trans_lt h)
    simp [PredictableElementaryInterval.integrand, hLeft, hStart]

/-- One raw elementary integrand is integrable against every pathwise Jordan
variation measure. -/
theorem integrable_integrand_section_totalVariation
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F)
    (A : Process Omega)
    (hA : ∀ omega, BoundedVariationOn (fun t => A t omega) Set.univ)
    (omega : Omega) :
    Integrable (fun t => B.integrand t omega)
      (FiniteVariationPath.signedMeasure (hA omega)).totalVariation := by
  let nu := (FiniteVariationPath.signedMeasure (hA omega)).totalVariation
  let : IsFiniteMeasure nu := by
    dsimp only [nu]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hSection : StronglyMeasurable (fun t => B.integrand t omega) :=
    (B.integrand_isStronglyPredictable.mono
      (PredictableKernelMeasure.predictable_le_prod F))
      |>.comp_measurable measurable_prodMk_right
  apply (integrable_const |B.interval.coefficient omega|).mono'
    hSection.aestronglyMeasurable
  filter_upwards with t
  by_cases ht : B.interval.startTime omega < t ∧
      t ≤ B.interval.stopTime omega <;>
    simp [PredictableElementaryInterval.integrand, ht]

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

/-- A raw elementary integrand is integrable against every pathwise Jordan
variation measure. -/
theorem integrable_integrand_section_totalVariation
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (K : PredictableElementaryStrategy F)
    (A : Process Omega)
    (hA : ∀ omega, BoundedVariationOn (fun t => A t omega) Set.univ)
    (omega : Omega) :
    Integrable (fun t => K.integrand t omega)
      (FiniteVariationPath.signedMeasure (hA omega)).totalVariation := by
  induction K with
  | nil =>
      simp [PredictableElementaryStrategy.integrand]
  | cons B K ih =>
      change Integrable
        (fun t => B.integrand t omega +
          PredictableElementaryStrategy.integrand K t omega)
        (FiniteVariationPath.signedMeasure (hA omega)).totalVariation
      exact (B.integrable_integrand_section_totalVariation A hA omega).add ih

/-- The pathwise elementary integral up to `T` is the signed Stieltjes
integral of the raw integrand restricted to `(0,T]`. -/
theorem finiteVariationIntegral_eq_integral_indicator_integrand
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (K : PredictableElementaryStrategy F)
    (A : Process Omega)
    (hA : ∀ omega, BoundedVariationOn (fun t => A t omega) Set.univ)
    (T : NNReal) (omega : Omega) :
    K.finiteVariationIntegral A hA T omega =
      FiniteVariationPath.integral (hA omega)
        ((Ioc 0 T).indicator (fun t => K.integrand t omega)) := by
  induction K with
  | nil =>
      simp [PredictableElementaryStrategy.finiteVariationIntegral,
        PredictableElementaryStrategy.integrand,
        FiniteVariationPath.integral]
  | cons B K ih =>
      let eta := FiniteVariationPath.signedMeasure (hA omega)
      have hBVector : (eta : VectorMeasure NNReal Real).Integrable
          ((Ioc 0 T).indicator (fun t => B.integrand t omega)) := by
        change Integrable
          ((Ioc 0 T).indicator (fun t => B.integrand t omega))
          (eta : VectorMeasure NNReal Real).variation
        rw [← signedMeasure_totalVariation_eq_variation]
        exact (B.integrable_integrand_section_totalVariation A hA omega)
          |>.indicator measurableSet_Ioc
      have hKVector : (eta : VectorMeasure NNReal Real).Integrable
          ((Ioc 0 T).indicator (fun t =>
            PredictableElementaryStrategy.integrand K t omega)) := by
        change Integrable
          ((Ioc 0 T).indicator (fun t =>
            PredictableElementaryStrategy.integrand K t omega))
          (eta : VectorMeasure NNReal Real).variation
        rw [← signedMeasure_totalVariation_eq_variation]
        exact (integrable_integrand_section_totalVariation K A hA omega)
          |>.indicator measurableSet_Ioc
      change
        B.interval.finiteVariationIntegral A hA T omega +
            PredictableElementaryStrategy.finiteVariationIntegral
              A hA K T omega =
          FiniteVariationPath.integral (hA omega)
            ((Ioc 0 T).indicator (fun t =>
              B.integrand t omega +
                PredictableElementaryStrategy.integrand K t omega))
      rw [ih]
      rw [show (Ioc 0 T).indicator (fun t =>
          B.integrand t omega +
            PredictableElementaryStrategy.integrand K t omega) =
        (Ioc 0 T).indicator (fun t => B.integrand t omega) +
          (Ioc 0 T).indicator (fun t =>
            PredictableElementaryStrategy.integrand K t omega) by
        funext t
        by_cases ht : t ∈ Ioc (0 : NNReal) T <;> simp [ht]]
      unfold FiniteVariationPath.integral
      rw [VectorMeasure.integral_add hBVector hKVector]
      rw [B.indicator_Ioc_zero_integrand_eq_clamped T omega]
      unfold ElementaryInterval.finiteVariationIntegral
        FiniteVariationPath.integral
      rfl

end PredictableElementaryStrategy

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {H : SIntegrableStrategy D}

/-- Outside the Doléans full-measure set, the cumulative density integral
at every time is the pathwise elementary Stieltjes integral at that time. -/
theorem finiteVariationIntegralProcess_eq_elementaryIntegral_ae
    (E : SIntegrableFiniteVariationBridge H)
    (K : PredictableElementaryStrategy F)
    {C : Real} (hKBound : ∀ t omega, |K.integrand t omega| ≤ C) :
    ∀ᵐ omega ∂mu, ∀ T,
      finiteVariationIntegralProcess E K.integrand T omega =
        K.finiteVariationIntegral H.finiteVariationPart
          H.finiteVariationPart_isBoundedVariation T omega := by
  filter_upwards [signedMeasure_finiteVariationPart_eq_withDensity_ae E]
      with omega hMeasure
  intro T
  let kSection : NNReal → Real := fun t => K.integrand t omega
  let restricted : NNReal → Real := (Ioc 0 T).indicator kSection
  have hRestrictedMeas : StronglyMeasurable restricted := by
    exact ((K.integrand_isStronglyPredictable.mono
      (PredictableKernelMeasure.predictable_le_prod F))
        |>.comp_measurable measurable_prodMk_right)
      |>.indicator measurableSet_Ioc
  have hCNonnegative : 0 ≤ C :=
    (abs_nonneg (K.integrand 0 omega)).trans (hKBound 0 omega)
  have hRestrictedBound : ∀ t, |restricted t| ≤ C := by
    intro t
    by_cases ht : t ∈ Ioc (0 : NNReal) T
    · simpa [restricted, kSection, Set.indicator_of_mem ht] using
        hKBound t omega
    · simp [restricted, Set.indicator_of_notMem ht, hCNonnegative]
  have hIntegralEq :=
    FiniteVariationPath.integral_eq_integral_density_mul_of_bounded
      (H.finiteVariationPart_isBoundedVariation omega)
      (integrable_jumpCorrectedCanonicalVariationDensity_section E omega)
      (fun t => abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, omega))
      hMeasure hRestrictedMeas hRestrictedBound
  rw [K.finiteVariationIntegral_eq_integral_indicator_integrand
    H.finiteVariationPart H.finiteVariationPart_isBoundedVariation T omega]
  rw [hIntegralEq]
  rw [finiteVariationIntegralProcess, pathVariationMeasureUpTo]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioc (0 : NNReal) T
  · simp [restricted, kSection, finiteVariationIntegralDensity, ht]
  · simp [restricted, ht]

/-- The cumulative Doléans construction is the actual running elementary
gain against the finite-variation component, with one null set valid at all
times. -/
theorem finiteVariationIntegralProcess_indistinguishable_elementaryGain
    (E : SIntegrableFiniteVariationBridge H)
    (K : PredictableElementaryStrategy F)
    {C : Real} (hKBound : ∀ t omega, |K.integrand t omega| ≤ C) :
    ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E K.integrand)
      (ElementaryStrategy.gain H.finiteVariationPart K.toElementary) := by
  filter_upwards [finiteVariationIntegralProcess_eq_elementaryIntegral_ae
    E K hKBound] with omega homega
  intro T
  rw [homega T]
  exact K.finiteVariationIntegral_eq_gain H.finiteVariationPart
    H.finiteVariationPart_isBoundedVariation E.rightContinuous T omega

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
