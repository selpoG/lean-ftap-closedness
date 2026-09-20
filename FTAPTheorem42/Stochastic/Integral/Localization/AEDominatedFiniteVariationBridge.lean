/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.StoppedSourceBridge
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl

/-!
# Finite-variation bridges from almost-everywhere domination

A common Mémin normalizer usually dominates the intended path variation only
outside a null set, whereas `SIntegrableFiniteVariationBridge` stores an
everywhere pathwise bound.  This file repairs one term of the normalizing
sequence by its maximum with the actual path variation.  The repair is equal
to the original sequence almost everywhere, so it preserves the common
reference measure while supplying the required everywhere bound.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {H : SIntegrableStrategy D}

/-- Replace one normalizing term by its maximum with the actual whole-path
variation. -/
noncomputable def aeDominationRepairSequence
    (H : SIntegrableStrategy D) (V : Nat -> Omega -> Real) (n : Nat) :
    Nat -> Omega -> Real :=
  fun k omega => if k = n then
    max (V k omega)
      ((FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ)
  else V k omega

omit [IsFiniteMeasure mu] in
theorem aeDominationRepairSequence_measurable
    (V : Nat -> Omega -> Real) (hV : ∀ k, Measurable (V k)) (n k : Nat) :
    Measurable (aeDominationRepairSequence H V n k) := by
  classical
  change Measurable (fun omega => if k = n then
    max (V k omega)
      ((FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ)
    else V k omega)
  by_cases hk : k = n
  · simpa [hk] using
      (hV k).max (measurable_totalVariation_univ_of_cumulativeVariation
        H.finiteVariationPart_isRightContinuous)
  · simpa [hk] using hV k

omit [IsFiniteMeasure mu] in
theorem aeDominationRepairSequence_nonnegative
    (V : Nat -> Omega -> Real) (hVNonnegative : ∀ k omega, 0 <= V k omega)
    (n k : Nat) (omega : Omega) :
    0 <= aeDominationRepairSequence H V n k omega := by
  classical
  change 0 <= if k = n then
    max (V k omega)
      ((FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ)
    else V k omega
  by_cases hk : k = n
  · rw [ite_eq_left hk]
    exact (hVNonnegative k omega).trans (le_max_left _ _)
  · rw [ite_eq_right hk]
    exact hVNonnegative k omega

omit [IsFiniteMeasure mu] in
theorem totalVariation_le_aeDominationRepairSequence
    (V : Nat -> Omega -> Real) (n : Nat) (omega : Omega) :
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
        Set.univ <= aeDominationRepairSequence H V n n omega := by
  simp only [aeDominationRepairSequence, ite_eq_left]
  exact le_max_right _ _

omit [IsFiniteMeasure mu] in
theorem aeDominationRepairSequence_ae_eq
    (V : Nat -> Omega -> Real) (n : Nat)
    (hDominates : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ <= V n omega) :
    ∀ᵐ omega ∂mu,
      (fun k => aeDominationRepairSequence H V n k omega) = fun k => V k omega := by
  filter_upwards [hDominates] with omega hDom
  funext k
  classical
  by_cases hk : k = n
  · subst k
    simp only [aeDominationRepairSequence, ite_eq_left, max_eq_left hDom]
  · simp only [aeDominationRepairSequence, ite_eq_right hk]

omit [IsFiniteMeasure mu] in
theorem aeDominationRepairSequence_summable
    (V : Nat -> Omega -> Real) (n : Nat)
    (hSummable : ∀ᵐ omega ∂mu, Summable (fun k => V k omega))
    (hDominates : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ <= V n omega) :
    ∀ᵐ omega ∂mu,
      Summable (fun k => aeDominationRepairSequence H V n k omega) := by
  filter_upwards [hSummable,
      aeDominationRepairSequence_ae_eq V n hDominates]
      with omega hSum hEq
  rw [hEq]
  exact hSum

/-- An almost-everywhere dominating term suffices to construct a bridge.
Only the exceptional set is repaired; the induced reference measure remains
the one defined by the original common sequence. -/
noncomputable def ofAEDominatedSummableSequence
    (V : Nat -> Omega -> Real) (hV : ∀ k, Measurable (V k))
    (hVNonnegative : ∀ k omega, 0 <= V k omega)
    (hSummable : ∀ᵐ omega ∂mu, Summable (fun k => V k omega))
    (n : Nat)
    (hDominates : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ <= V n omega) :
    SIntegrableFiniteVariationBridge H :=
  ofDominatedSummableSequence
    (aeDominationRepairSequence H V n)
    (aeDominationRepairSequence_measurable V hV n)
    (aeDominationRepairSequence_nonnegative V hVNonnegative n)
    (aeDominationRepairSequence_summable V n hSummable hDominates)
    n (totalVariation_le_aeDominationRepairSequence V n)

theorem ofAEDominatedSummableSequence_referenceDensity_ae_eq
    (V : Nat -> Omega -> Real) (hV : ∀ k, Measurable (V k))
    (hVNonnegative : ∀ k omega, 0 <= V k omega)
    (hSummable : ∀ᵐ omega ∂mu, Summable (fun k => V k omega))
    (n : Nat)
    (hDominates : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ <= V n omega) :
    (fun omega =>
      ((ofAEDominatedSummableSequence V hV hVNonnegative hSummable n
        hDominates).referenceDensity omega : ENNReal)) =ᵐ[mu]
      MeminEquivalentFiniteVariationMeasure.referenceDensity V := by
  let repaired := aeDominationRepairSequence H V n
  have hRepairSummable :=
    aeDominationRepairSequence_summable V n hSummable hDominates
  have hRepairEq := aeDominationRepairSequence_ae_eq V n hDominates
  change (fun omega =>
    (MeminEquivalentFiniteVariationMeasure.repairedReferenceDensity
      repaired n omega : ENNReal)) =ᵐ[mu]
        MeminEquivalentFiniteVariationMeasure.referenceDensity V
  refine
    (MeminEquivalentFiniteVariationMeasure.coe_repairedReferenceDensity_ae_eq_referenceDensity
      hRepairSummable n).trans ?_
  filter_upwards [hRepairEq] with omega hEq
  unfold MeminEquivalentFiniteVariationMeasure.referenceDensity
    MeminEquivalentFiniteVariationMeasure.summableEnvelope
  have hTsum :
      (∑' k, ENNReal.ofReal (aeDominationRepairSequence H V n k omega)) =
        ∑' k, ENNReal.ofReal (V k omega) := by
    apply tsum_congr
    intro k
    rw [congrFun hEq k]
  rw [hTsum]

theorem ofAEDominatedSummableSequence_referenceMeasure_eq
    (V : Nat -> Omega -> Real) (hV : ∀ k, Measurable (V k))
    (hVNonnegative : ∀ k omega, 0 <= V k omega)
    (hSummable : ∀ᵐ omega ∂mu, Summable (fun k => V k omega))
    (n : Nat)
    (hDominates : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ <= V n omega) :
    (ofAEDominatedSummableSequence V hV hVNonnegative hSummable n
      hDominates).referenceMeasure =
        MeminEquivalentFiniteVariationMeasure.referenceMeasure mu V := by
  unfold referenceMeasure MeminEquivalentFiniteVariationMeasure.referenceMeasure
  exact withDensity_congr_ae
    (ofAEDominatedSummableSequence_referenceDensity_ae_eq
      V hV hVNonnegative hSummable n hDominates)

/-- Canonical variation `L1` membership descends along an almost-everywhere
path-variation domination when the two bridges use the same sample-space
reference measure. -/
theorem memLp_one_of_referenceMeasure_eq_of_pathVariation_le
    {K : SIntegrableStrategy D}
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (hReferenceMeasure : E.referenceMeasure = E'.referenceMeasure)
    (hPathVariation : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        (K.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hMemLp : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E')) :
    MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E) := by
  have hDensityMeasure :
      mu.withDensity (fun omega => (E.referenceDensity omega : ENNReal)) =
        mu.withDensity (fun omega => (E'.referenceDensity omega : ENNReal)) := by
    simpa only [referenceMeasure] using hReferenceMeasure
  have hDensity :
      (fun omega => (E.referenceDensity omega : ENNReal)) =ᵐ[mu]
        fun omega => (E'.referenceDensity omega : ENNReal) :=
    (withDensity_eq_iff_of_sigmaFinite
      E.referenceDensity_measurable.coe_nnreal_ennreal.aemeasurable
      E'.referenceDensity_measurable.coe_nnreal_ennreal.aemeasurable).mp
        hDensityMeasure
  apply memLp_one_iff_integrable.mpr
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hGlobal :
      (∫⁻ p, ‖Function.uncurry f p‖ₑ
        ∂canonicalVariationMeasure E') < ∞ := by
    rw [← hasFiniteIntegral_iff_enorm]
    exact (memLp_one_iff_integrable.mp hMemLp).2
  apply lt_of_le_of_lt _ hGlobal
  rw [lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
      E hf.enorm,
    lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
      E' hf.enorm]
  apply lintegral_mono_ae
  filter_upwards [hDensity, hPathVariation] with omega hDensityOmega hPathOmega
  rw [hDensityOmega]
  exact mul_le_mul_right (lintegral_mono' hPathOmega le_rfl) _

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
