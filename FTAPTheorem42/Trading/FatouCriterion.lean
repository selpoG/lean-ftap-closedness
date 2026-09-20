import FTAPTheorem42.PositiveTail

/-!
# Proposition 3.1 wrappers

This module packages the positive-tail free-lunch construction into the
bounded-in-probability conclusions used by the Theorem 4.2 assembly.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

theorem ClaimSetBoundedInProbability.of_linftyNFLVR_and_subsetUnboundedCertificate
    {μ : Measure Ω} {D K0 : Set (Ω → ℝ)}
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0)))
    (hCert : ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch μ D K0) :
    ClaimSetBoundedInProbability μ D := by
  classical
  by_contra hnot
  rcases hCert hnot with ⟨F, hFcl, hFpos, hFne⟩
  exact hFne ((linftyNFLVR_iff.mp hNFLVR) F hFcl hFpos)

theorem ClaimSetBoundedInProbability.of_linftyNFLVR_positiveTailKomlosLite
    {μ : Measure Ω} [IsFiniteMeasure μ] {D K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hKomlos : KomlosLiteVanishingRiskPositiveMass μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ D :=
  ClaimSetBoundedInProbability.of_linftyNFLVR_and_subsetUnboundedCertificate
    hNFLVR
    (claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosLite
      hK hKmeas hSub hLower hKomlos)

theorem ClaimSetBoundedInProbability.of_linftyNFLVR_positiveTailKomlosAELimitExtraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {D K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hExtract : KomlosLiteAELimitExtractionStrong μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ D :=
  ClaimSetBoundedInProbability.of_linftyNFLVR_and_subsetUnboundedCertificate
    hNFLVR
    (claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosAELimitExtraction
      hK hKmeas hSub hLower hExtract)

theorem ClaimSetWithAELowerBound.bddInProb_one_of_NFLVR_komlosAELimitExtraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hExtract : KomlosLiteAELimitExtractionStrong μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ (ClaimSetWithAELowerBound μ 1 K0) :=
  ClaimSetBoundedInProbability.of_linftyNFLVR_positiveTailKomlosAELimitExtraction
    hK hKmeas ClaimSetWithAELowerBound_subset
    ClaimSetWithAELowerBound_lowerBound hExtract hNFLVR

/--
Delbaen--Schachermayer Proposition 3.1, general finite-measure form reduced to
the bounded/truncated Komlós-lite a.e.-limit input used in the paper.

The underlying measurable space is arbitrary. The analytic input is
forward-convex a.e.-limit extraction for sequences with vanishing lower
risk and upper bound `1`.
-/
theorem proposition31_of_komlosAELimitExtraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hExtract : KomlosLiteAELimitExtractionStrong μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ (ClaimSetWithAELowerBound μ 1 K0) :=
  ClaimSetWithAELowerBound.bddInProb_one_of_NFLVR_komlosAELimitExtraction
    hK hKmeas hExtract hNFLVR

/--
Delbaen--Schachermayer Proposition 3.1, general finite-measure form.

The bounded/truncated Komlós-lite extraction input is supplied by
`KomlosLiteAELimitExtractionStrong.of_finiteMeasure`, so this statement only
assumes the terminal-gain cone algebra/measurability and `L∞`-NFLVR.
-/
theorem proposition31_generalFinite
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ (ClaimSetWithAELowerBound μ 1 K0) :=
  proposition31_of_komlosAELimitExtraction
    hK hKmeas
    (KomlosLiteAELimitExtractionStrong.of_finiteMeasure (μ := μ))
    hNFLVR

/-- Proposition 3.1 for raw claim sets whose members are only a.e. strongly
measurable.  The finite-measure Komlós theorem supplies exactly this version
after selecting strongly measurable representatives internally. -/
theorem proposition31_generalFinite_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ (ClaimSetWithAELowerBound μ 1 K0) :=
  ClaimSetBoundedInProbability.of_linftyNFLVR_positiveTailKomlosLite
    hK hKmeas (fun _ hf => hf.1)
    (fun _ hf => hf.2)
    (KomlosLiteVanishingRiskPositiveMass.of_strong
      (KomlosLiteVanishingRiskPositiveMassStrong.of_finiteMeasure
        (μ := μ)))
    hNFLVR

/--
Proposition 3.1 boundedness transferred to a source class contained in the
`1`-admissible part of the terminal-gain cone.  This is the main route for
`K1`: boundedness is proved for the one-admissible source, not for all `K0`.
-/
theorem claimSetBoundedInProbability_of_NFLVR_generalFinite_subsetLowerBound
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 Ksrc : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hsub : Ksrc ⊆ ClaimSetWithAELowerBound μ 1 K0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ K0))) :
    ClaimSetBoundedInProbability μ Ksrc :=
  (proposition31_generalFinite hK hKmeas hNFLVR).mono hsub

end FTAPTheorem42
