/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.PositiveTail.Komlos

/-!
# Positive-tail free-lunch assembly

This module assembles the positive-tail truncation, bounded/truncated
Komlós-lite extraction, and Egorov-to-`L∞` bridge into the Proposition 3.1
free-lunch certificates.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The Egorov/`L∞` lifting step left after Komlós-lite: a vanishing-risk sequence
in `C0` with a nonzero nonnegative a.e. limit yields the norm-convergent
`L∞` free-lunch certificate.
-/
def EgorovVanishingRiskToLinftyNormLimit
    (μ : Measure Ω) (C0 : Set (Ω → ℝ)) : Prop :=
  ∀ gseq : ℕ → Ω → ℝ,
    ∀ g : Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, gseq n ∈ C0) →
          (∀ n, AEStronglyMeasurable (gseq n) μ) →
            AEStronglyMeasurable g μ →
              (∀ n, AELowerBoundedBy μ (-(δ n)) (gseq n)) →
                (∀ n, ∀ᵐ ω ∂μ, gseq n ω ≤ 1) →
                  Tendsto δ atTop (nhds 0) →
                    TendstoAE μ gseq g →
                      (∀ᵐ ω ∂μ, 0 ≤ g ω) →
                        (∀ᵐ ω ∂μ, g ω ≤ 1) →
                          0 < μ {ω | 0 < g ω} →
                            ∃ U : ℕ → Linfty (Ω := Ω) μ,
                              ∃ F : Linfty (Ω := Ω) μ,
                                (∀ n, U n ∈ LinftyClaims μ C0) ∧
                                Tendsto U atTop (nhds F) ∧
                                F ∈ LinftyNonnegative μ ∧
                                F ≠ 0

theorem egorovVanishingRiskToLinftyNormLimit_of_core
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hSolid : Solid μ C0) :
    EgorovVanishingRiskToLinftyNormLimit μ C0 := by
  intro gseq g δ hgseqMem hgseqMeas hgMeas hlower _hgupper hδtendsto
    hlim hgnonneg hgle_one hgpos
  let gseq' : ℕ → Ω → ℝ := fun n => (hgseqMeas n).mk (gseq n)
  let g' : Ω → ℝ := hgMeas.mk g
  let δ' : ℕ → ℝ := fun n => max (δ n) 0
  have hseqEq : ∀ n, gseq n =ᵐ[μ] gseq' n := fun n =>
    (hgseqMeas n).ae_eq_mk
  have hgEq : g =ᵐ[μ] g' := hgMeas.ae_eq_mk
  have hgseqMem' : ∀ n, gseq' n ∈ C0 := by
    intro n
    refine hSolid (hgseqMem n) ?_
    filter_upwards [hseqEq n] with ω hω
    rw [← hω]
  have hδnonneg : ∀ n, 0 ≤ δ' n := by
    intro n
    exact le_max_right (δ n) 0
  have hgseqStrong : ∀ n, StronglyMeasurable (gseq' n) := fun n =>
    (hgseqMeas n).stronglyMeasurable_mk
  have hgStrong : StronglyMeasurable g' := hgMeas.stronglyMeasurable_mk
  have hlower' : ∀ n, AELowerBoundedBy μ (-(δ' n)) (gseq' n) := by
    intro n
    filter_upwards [hlower n, hseqEq n] with ω hlow hω
    have hδle : δ n ≤ δ' n := by
      exact le_max_left (δ n) 0
    have hneg : -(δ' n) ≤ -(δ n) := neg_le_neg hδle
    rw [← hω]
    exact le_trans hneg hlow
  have hδ'tendsto : Tendsto δ' atTop (nhds 0) := by
    have h := hδtendsto.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa [δ'] using h
  have hlim' : TendstoAE μ gseq' g' := by
    have hseqEq_all : ∀ᵐ ω ∂μ, ∀ n, gseq n ω = gseq' n ω :=
      ae_all_iff.mpr hseqEq
    filter_upwards [hlim, hseqEq_all, hgEq] with ω hlimω hseqω hgω
    have hfun : (fun n => gseq' n ω) = fun n => gseq n ω := by
      funext n
      exact (hseqω n).symm
    rw [hfun, ← hgω]
    exact hlimω
  have hgnonneg' : ∀ᵐ ω ∂μ, 0 ≤ g' ω := by
    filter_upwards [hgnonneg, hgEq] with ω hnonneg hω
    rw [← hω]
    exact hnonneg
  have hgle_one' : ∀ᵐ ω ∂μ, g' ω ≤ 1 := by
    filter_upwards [hgle_one, hgEq] with ω hle hω
    rw [← hω]
    exact hle
  have hgpos' : 0 < μ {ω | 0 < g' ω} := by
    have hmono : μ {ω | 0 < g ω} ≤ μ {ω | 0 < g' ω} := by
      exact measure_mono_ae <| hgEq.mono fun ω hω hgω => by
        change 0 < g' ω
        rw [← hω]
        exact hgω
    exact lt_of_lt_of_le hgpos hmono
  exact egorovVanishingRiskToLinftyNormLimit_core
    (μ := μ) (C0 := C0) hSolid hgseqMem' hδnonneg hgseqStrong hgStrong
    hlower' hδ'tendsto hlim' hgnonneg' hgle_one' hgpos'

theorem vanishingRiskPositiveMassSequenceProducesLinftyLimit_of_komlosLite_and_egorov
    {μ : Measure Ω} {C0 : Set (Ω → ℝ)}
    (hC0 : ClaimCone C0)
    (hKomlos : KomlosLiteVanishingRiskPositiveMass μ)
    (hEgorov : EgorovVanishingRiskToLinftyNormLimit μ C0) :
    VanishingRiskPositiveMassSequenceProducesLinftyLimit μ C0 := by
  intro ε hε f δ hfC0 hfmeas hflower hfupper hδmono hδtendsto hmass
  rcases hKomlos ε hε f δ hflower hfmeas hfupper hδmono hδtendsto hmass with
    ⟨W, g, hlim, hgmeas, hglower, hgupper, hgnonneg, hgle_one, hgpos⟩
  have hWmem : ∀ n, W.apply f n ∈ C0 := fun n =>
    W.apply_mem_of_claimCone hC0 hfC0 n
  have hWmeas : ∀ n, AEStronglyMeasurable (W.apply f n) μ := fun n =>
    W.apply_aestronglyMeasurable hfmeas n
  exact hEgorov (W.apply f) g δ hWmem hWmeas hgmeas hglower hgupper
    hδtendsto hlim hgnonneg hgle_one hgpos

/--
Proposition 3.1 oriented form of the unbounded-tail free-lunch construction:
the terminal gains are uniformly a.e. bounded below, and the large tail is on
the positive side.
-/
def TerminalGainPositiveTailLowerBoundSequenceProducesLinftyLimit
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ G : ℕ → Ω → ℝ,
      (∀ n, G n ∈ K0) →
        (∀ n, AELowerBoundedBy μ (-1) (G n)) →
          (∀ n : ℕ, ENNReal.ofReal ε < μ {ω | (n : ℝ) < G n ω}) →
            ∃ U : ℕ → Linfty (Ω := Ω) μ,
              ∃ F : Linfty (Ω := Ω) μ,
                (∀ n, U n ∈ LinftyClaims μ (C0AsDifference μ K0)) ∧
                Tendsto U atTop (nhds F) ∧
                F ∈ LinftyNonnegative μ ∧
                F ≠ 0

theorem positiveTailLowerBoundSequenceProducesLinftyLimit_of_truncation_and_vanishingRisk
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hAnalytic :
      VanishingRiskPositiveMassSequenceProducesLinftyLimit
        μ (C0AsDifference μ K0)) :
    TerminalGainPositiveTailLowerBoundSequenceProducesLinftyLimit μ K0 := by
  intro ε hε G hG hlow htail
  let f : ℕ → Ω → ℝ := positiveTailTrunc G
  let δ : ℕ → ℝ := fun n => (positiveTailScaleDenom n)⁻¹
  have hpack := positiveTailTrunc_mem_C0_meas_bounds_mass
    (μ := μ) (K0 := K0) hK hKmeas hG hlow htail
  have hfC0 : ∀ n, f n ∈ C0AsDifference μ K0 := fun n => (hpack n).1
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    (hpack n).2.1
  have hflower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n) := fun n =>
    (hpack n).2.2.1
  have hfupper : ∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1 := fun n =>
    (hpack n).2.2.2.1
  have hfmass : ∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω} :=
    fun n => (hpack n).2.2.2.2.2
  exact hAnalytic ε hε f δ hfC0 hfmeas hflower hfupper
    (by simpa [δ] using positiveTailScaleInv_antitone)
    (by simpa [δ] using positiveTailScaleInv_tendsto_zero)
    hfmass

theorem positiveTailLowerBoundSequenceProducesLinftyLimit_of_komlosLite_and_egorov
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hKomlos : KomlosLiteVanishingRiskPositiveMass μ)
    (hEgorov :
      EgorovVanishingRiskToLinftyNormLimit μ (C0AsDifference μ K0)) :
    TerminalGainPositiveTailLowerBoundSequenceProducesLinftyLimit μ K0 :=
  positiveTailLowerBoundSequenceProducesLinftyLimit_of_truncation_and_vanishingRisk
    hK hKmeas
    (vanishingRiskPositiveMassSequenceProducesLinftyLimit_of_komlosLite_and_egorov
      (C0AsDifference_claimCone (μ := μ) hK) hKomlos hEgorov)

theorem positiveTailLowerBoundSequenceProducesLinftyLimit_of_komlosLite_and_core
    {μ : Measure Ω} [IsFiniteMeasure μ] {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hKomlos : KomlosLiteVanishingRiskPositiveMass μ) :
    TerminalGainPositiveTailLowerBoundSequenceProducesLinftyLimit μ K0 :=
  positiveTailLowerBoundSequenceProducesLinftyLimit_of_komlosLite_and_egorov
    hK hKmeas hKomlos
    (egorovVanishingRiskToLinftyNormLimit_of_core
      (C0AsDifference_solid μ K0))

/--
Subset version of the same construction.  The lower bound is required only on
the uniformly `1`-admissible class `D`; convex/scalar closure remains attached
to the ambient trading cone `K0`, where the resulting free lunch lives.
-/
theorem ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch.of_positiveTailLowerBound
    {μ : Measure Ω} {D K0 : Set (Ω → ℝ)}
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hLimit : TerminalGainPositiveTailLowerBoundSequenceProducesLinftyLimit μ K0) :
    ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch μ D K0 := by
  intro hnot
  have hAbs := ClaimSetUnboundedInProbabilityWitness.of_not_bounded hnot
  have hPos :
      ClaimSetUnboundedPositiveTailWitness μ D :=
    ClaimSetUnboundedPositiveTailWitness.of_absWitness_of_aeLowerBound
      hLower hAbs
  rcases hPos.exists_sequence with ⟨ε, hεpos, G, hGmem, hGμ⟩
  rcases hLimit ε hεpos G (fun n => hSub (hGmem n))
      (fun n => hLower (G n) (hGmem n)) hGμ with
    ⟨U, F, hU, hTendsto, hFpos, hFne⟩
  exact ⟨F, mem_closure_of_tendsto_atTop hU hTendsto, hFpos, hFne⟩

theorem claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosLite
    {μ : Measure Ω} [IsFiniteMeasure μ] {D K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hKomlos : KomlosLiteVanishingRiskPositiveMass μ) :
    ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch μ D K0 :=
  ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch.of_positiveTailLowerBound
    hSub hLower
    (positiveTailLowerBoundSequenceProducesLinftyLimit_of_komlosLite_and_core
      hK hKmeas hKomlos)

theorem claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosStrong
    {μ : Measure Ω} [IsFiniteMeasure μ] {D K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hKomlos : KomlosLiteVanishingRiskPositiveMassStrong μ) :
    ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch μ D K0 :=
  claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosLite
    hK hKmeas.aestronglyMeasurable hSub hLower
    (KomlosLiteVanishingRiskPositiveMass.of_strong hKomlos)

theorem
    claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosAELimitExtraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {D K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0)
    (hKmeas : ClaimSetStronglyMeasurable K0)
    (hSub : D ⊆ K0)
    (hLower : ClaimSetAELowerBoundedBy μ 1 D)
    (hExtract : KomlosLiteAELimitExtractionStrong μ) :
    ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch μ D K0 :=
  claimSubsetUnboundedInProbabilityProducesLinftyFreeLunch_of_positiveTailKomlosStrong
    hK hKmeas hSub hLower
    (KomlosLiteVanishingRiskPositiveMassStrong.of_aeLimitExtraction hExtract)

end FTAPTheorem42
