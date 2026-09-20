/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Core.WeakStar
import FTAPTheorem42.Core.L1DualRepresentation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Bounded slices of raw claim cones

This file embeds `L∞` into `L¹` over a finite measure and proves norm and weak
closedness of the `L¹` image of a bounded claim slice.  No compactness or
sequentiality assertion about the weak-star topology is used.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def linftyToL1LinearMap
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Linfty (Ω := Ω) μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun F := ⟨F.1, Lp.antitone (by simp) F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_linftyToL1LinearMap_le
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Linfty (Ω := Ω) μ) :
    ‖linftyToL1LinearMap μ F‖ ≤ μ.real Set.univ * ‖F‖ := by
  have hnorm :
      eLpNorm (F : Ω → ℝ) 1 μ ≤
        eLpNorm (F : Ω → ℝ) ∞ μ * μ Set.univ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ) (f := (F : Ω → ℝ)) (show (1 : ℝ≥0∞) ≤ ∞ from le_top)
        (Lp.aestronglyMeasurable F))
  rw [Lp.norm_def, Lp.norm_def]
  change (eLpNorm (F : Ω → ℝ) 1 μ).toReal ≤
    μ.real Set.univ * (eLpNorm (F : Ω → ℝ) ∞ μ).toReal
  calc
    (eLpNorm (F : Ω → ℝ) 1 μ).toReal
        ≤ (eLpNorm (F : Ω → ℝ) ∞ μ * μ Set.univ).toReal := by
          exact ENNReal.toReal_mono
            (ENNReal.mul_lt_top (Lp.eLpNorm_ne_top F).lt_top
              (measure_lt_top μ Set.univ)).ne
            hnorm
    _ = μ.real Set.univ * (eLpNorm (F : Ω → ℝ) ∞ μ).toReal := by
      rw [ENNReal.toReal_mul, mul_comm, measureReal_def]

noncomputable def linftyToL1CLM
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Linfty (Ω := Ω) μ →L[ℝ] Lp ℝ 1 μ :=
  (linftyToL1LinearMap μ).mkContinuous
    (μ.real Set.univ)
    (norm_linftyToL1LinearMap_le μ)

theorem linftyToL1CLM_coeFn_ae
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Linfty (Ω := Ω) μ) :
    (linftyToL1CLM μ F : Ω → ℝ) =ᵐ[μ] (F : Ω → ℝ) :=
  EventuallyEq.rfl

theorem linftyToL1CLM_injective
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Function.Injective (linftyToL1CLM μ) := by
  intro F G hFG
  apply Lp.ext
  have hcoe : (linftyToL1CLM μ F : Ω → ℝ) =ᵐ[μ]
      (linftyToL1CLM μ G : Ω → ℝ) :=
    by rw [hFG]
  filter_upwards [linftyToL1CLM_coeFn_ae μ F,
    linftyToL1CLM_coeFn_ae μ G, hcoe] with ω hF hG h
  rw [← hF, ← hG]
  exact h

theorem l1Dual_apply_linftyToL1CLM_eq_pairing
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ)
    (F : Linfty (Ω := Ω) μ) :
    Λ (linftyToL1CLM μ F) =
      linftyL1Pairing μ F
        (linftyToL1CLM μ (l1DualRepresentative μ Λ)) := by
  calc
    Λ (linftyToL1CLM μ F) =
        linftyL1Pairing μ (l1DualRepresentative μ Λ)
          (linftyToL1CLM μ F) := by
      rw [linftyL1Pairing_apply,
        linftyL1PairingCLM_l1DualRepresentative_eq]
    _ = linftyL1Pairing μ F
        (linftyToL1CLM μ (l1DualRepresentative μ Λ)) := by
      rw [linftyL1Pairing_eq_integral, linftyL1Pairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [linftyToL1CLM_coeFn_ae μ F,
        linftyToL1CLM_coeFn_ae μ (l1DualRepresentative μ Λ)] with ω hF hH
      rw [hF, hH, mul_comm]

noncomputable def linftyWeakStarToWeakL1
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    LinftyWeakStar μ →L[ℝ] WeakSpace ℝ (Lp ℝ 1 μ) where
  __ := linftyToL1LinearMap μ
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    intro Λ
    let q : Lp ℝ 1 μ :=
      linftyToL1CLM μ (l1DualRepresentative μ Λ)
    have heq :
        (fun F : LinftyWeakStar μ =>
          (topDualPairing ℝ (Lp ℝ 1 μ)).flip
            (linftyToL1LinearMap μ F) Λ) =
        fun F : LinftyWeakStar μ => linftyL1Pairing μ F q := by
      funext F
      exact l1Dual_apply_linftyToL1CLM_eq_pairing μ Λ F
    change Continuous (fun F : LinftyWeakStar μ =>
      (topDualPairing ℝ (Lp ℝ 1 μ)).flip
        (linftyToL1LinearMap μ F) Λ)
    exact heq ▸ linftyWeakStar_eval_continuous μ q

theorem linftyWeakStarToWeakL1_injective
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Function.Injective (linftyWeakStarToWeakL1 μ) := by
  intro F G hFG
  exact linftyToL1CLM_injective μ
    ((toWeakSpace ℝ (Lp ℝ 1 μ)).injective hFG)

/-- The norm-bounded part of the concrete `L∞` claim set. -/
def LinftyClaimSlice
    (μ : Measure Ω) (D : Set (Ω → ℝ)) (R : ℝ) :
    Set (Linfty (Ω := Ω) μ) :=
  LinftyClaims μ D ∩ Metric.closedBall 0 R

theorem isClosed_linftyToL1_image_claimSlice
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)}
    (hFatou : FatouClosed μ D)
    (hCone : ClaimCone D)
    (hSolid : Solid μ D)
    {R : ℝ} (hR : 0 ≤ R) :
    IsClosed
      (linftyToL1CLM μ '' LinftyClaimSlice μ D R) := by
  apply IsSeqClosed.isClosed
  intro y v hv hy
  choose u huSlice huEq using hv
  have huClaims : ∀ n, u n ∈ LinftyClaims μ D :=
    fun n => (huSlice n).1
  have huNorm : ∀ n, ‖u n‖ ≤ R := by
    intro n
    exact mem_closedBall_zero_iff.mp (huSlice n).2
  rcases exists_bounded_stronglyMeasurable_representatives
      (μ := μ) (D := D) hSolid.aesaturated huClaims huNorm with
    ⟨f, hfD, hfStrong, hfAbs, hfLp, hfEq⟩
  have hfy : ∀ n, (y n : Ω → ℝ) =ᵐ[μ] f n := by
    intro n
    have hju : (linftyToL1CLM μ (u n) : Ω → ℝ) =ᵐ[μ]
        (u n : Ω → ℝ) :=
      linftyToL1CLM_coeFn_ae μ (u n)
    have hutof : (u n : Ω → ℝ) =ᵐ[μ] f n := by
      rw [← hfEq n]
      exact MemLp.coeFn_toLp (hfLp n)
    rw [← huEq n]
    exact hju.trans hutof
  have hconvMeasure :
      TendstoInMeasure μ f atTop (v : Ω → ℝ) :=
    (tendstoInMeasure_of_tendsto_Lp hy).congr_left hfy
  obtain ⟨ns, hns, hnsAE⟩ := hconvMeasure.exists_seq_tendsto_ae
  have hvAbs : ∀ᵐ ω ∂μ, |v ω| ≤ R := by
    have hfAbsAll : ∀ᵐ ω ∂μ, ∀ n, |f n ω| ≤ R :=
      ae_all_iff.mpr hfAbs
    filter_upwards [hnsAE, hfAbsAll] with ω hlimω hboundω
    have habs :
        Tendsto (fun n => |f (ns n) ω|) atTop (𝓝 |v ω|) :=
      (continuous_abs.tendsto (v ω)).comp hlimω
    exact le_of_tendsto_of_tendsto habs tendsto_const_nhds
      (Eventually.of_forall fun n => hboundω (ns n))
  have hvD : (v : Ω → ℝ) ∈ D := by
    apply hFatou.mem_of_tendstoAE_of_uniform_lower_bound hCone.2.2
      (b := R + 1)
    · linarith
    · exact fun n => hfD (ns n)
    · intro n
      filter_upwards [hfAbs (ns n)] with ω hω
      have := neg_le_of_abs_le hω
      linarith
    · simpa [TendstoAE] using hnsAE
  have hvTop : MemLp (v : Ω → ℝ) ∞ μ := by
    apply memLp_top_of_bound (Lp.aestronglyMeasurable v) R
    simpa [Real.norm_eq_abs] using hvAbs
  let V : Linfty (Ω := Ω) μ := hvTop.toLp (v : Ω → ℝ)
  have hJV : linftyToL1CLM μ V = v := by
    apply Lp.ext
    filter_upwards [linftyToL1CLM_coeFn_ae μ V,
      MemLp.coeFn_toLp hvTop] with ω hJVω hVω
    rw [hJVω, hVω]
  have hVnorm : ‖V‖ ≤ R := by
    dsimp [V]
    rw [Lp.norm_toLp, eLpNorm_exponent_top (Lp.aestronglyMeasurable v)]
    have hEss :
        eLpNormEssSup (v : Ω → ℝ) μ ≤ ENNReal.ofReal R := by
      apply eLpNormEssSup_le_of_ae_bound
      simpa [Real.norm_eq_abs] using hvAbs
    calc
      (eLpNormEssSup (v : Ω → ℝ) μ).toReal
          ≤ (ENNReal.ofReal R).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hEss
      _ = R := ENNReal.toReal_ofReal hR
  refine ⟨V, ⟨⟨v, hvD, hvTop, rfl⟩, ?_⟩, hJV⟩
  exact mem_closedBall_zero_iff.mpr hVnorm

theorem convex_linftyToL1_image_claimSlice
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)}
    (hCone : ClaimCone D)
    (R : ℝ) :
    Convex ℝ (linftyToL1CLM μ '' LinftyClaimSlice μ D R) := by
  apply Convex.linear_image
  exact (LinftyClaims_convex hCone.convex).inter (convex_closedBall 0 R)

theorem isClosed_weakL1_image_claimSlice
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)}
    (hFatou : FatouClosed μ D)
    (hCone : ClaimCone D)
    (hSolid : Solid μ D)
    {R : ℝ} (hR : 0 ≤ R) :
    IsClosed
      ((toWeakSpace ℝ (Lp ℝ 1 μ)) ''
        (linftyToL1CLM μ '' LinftyClaimSlice μ D R)) :=
  isClosed_toWeakSpace_image_of_isClosed_convex
    (convex_linftyToL1_image_claimSlice hCone R)
    (isClosed_linftyToL1_image_claimSlice hFatou hCone hSolid hR)

theorem linftyWeakStarToWeakL1_image_claimSlice
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set (Ω → ℝ)) (R : ℝ) :
    linftyWeakStarToWeakL1 μ ''
        ((toLinftyWeakStar μ) '' LinftyClaimSlice μ D R) =
      (toWeakSpace ℝ (Lp ℝ 1 μ)) ''
        (linftyToL1CLM μ '' LinftyClaimSlice μ D R) := by
  rw [Set.image_image, Set.image_image]
  congr 1

theorem linftyWeakStar_claimSlice_eq_preimage_weakL1_image
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set (Ω → ℝ)) (R : ℝ) :
    (toLinftyWeakStar μ) '' LinftyClaimSlice μ D R =
      linftyWeakStarToWeakL1 μ ⁻¹'
        ((toWeakSpace ℝ (Lp ℝ 1 μ)) ''
          (linftyToL1CLM μ '' LinftyClaimSlice μ D R)) := by
  calc
    (toLinftyWeakStar μ) '' LinftyClaimSlice μ D R =
        linftyWeakStarToWeakL1 μ ⁻¹'
          (linftyWeakStarToWeakL1 μ ''
            ((toLinftyWeakStar μ) '' LinftyClaimSlice μ D R)) :=
      (Set.preimage_image_eq _
        (linftyWeakStarToWeakL1_injective μ)).symm
    _ = linftyWeakStarToWeakL1 μ ⁻¹'
        ((toWeakSpace ℝ (Lp ℝ 1 μ)) ''
          (linftyToL1CLM μ '' LinftyClaimSlice μ D R)) := by
      rw [linftyWeakStarToWeakL1_image_claimSlice]

theorem isClosed_linftyWeakStar_claimSlice
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)}
    (hFatou : FatouClosed μ D)
    (hCone : ClaimCone D)
    (hSolid : Solid μ D)
    {R : ℝ} (hR : 0 ≤ R) :
    IsClosed
      ((toLinftyWeakStar μ) '' LinftyClaimSlice μ D R) := by
  rw [linftyWeakStar_claimSlice_eq_preimage_weakL1_image]
  exact
    (isClosed_weakL1_image_claimSlice hFatou hCone hSolid hR).preimage
      (linftyWeakStarToWeakL1 μ).continuous

end FTAPTheorem42
