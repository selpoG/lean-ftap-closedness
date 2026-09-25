/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Trading.MaximalClaims

/-!
# Transfer across equivalent finite measures

This file contains the measure-theoretic transfer facts needed by the
stochastic part of the development.  The two directions of absolute
continuity are kept explicit.  In particular, the canonical linear isometry
between the two `L∞` spaces transports bounded claims, their norm closures,
and the nonnegative cone, yielding invariance of the concrete `L∞`-NFLVR
condition.
-/

open Filter MeasureTheory Set

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace EquivalentMeasureTransfer

theorem terminalGainHasAEForwardConvexCandidate_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {K : Set (Ω → ℝ)} :
    TerminalGainHasAEForwardConvexCandidate μ K ↔
      TerminalGainHasAEForwardConvexCandidate ν K := by
  constructor
  · intro h G hG
    rcases h G hG with ⟨W, G_lim, hlim⟩
    exact ⟨W, G_lim, hνμ.ae_le hlim⟩
  · intro h G hG
    rcases h G hG with ⟨W, G_lim, hlim⟩
    exact ⟨W, G_lim, hμν.ae_le hlim⟩

theorem tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ) {g : Ω → ℝ} :
    TendstoInMeasure μ f atTop g ↔ TendstoInMeasure ν f atTop g := by
  have hfν : ∀ n, AEStronglyMeasurable (f n) ν := fun n =>
    (hf n).mono_ac hνμ
  rw [exists_seq_tendstoInMeasure_atTop_iff hf,
    exists_seq_tendstoInMeasure_atTop_iff hfν]
  constructor
  · intro h ns hns
    rcases h ns hns with ⟨ns', hns', hAE⟩
    exact ⟨ns', hns', hνμ.ae_le hAE⟩
  · intro h ns hns
    rcases h ns hns with ⟨ns', hns', hAE⟩
    exact ⟨ns', hns', hμν.ae_le hAE⟩

theorem inMeasureSequentialClosure_eq_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {K : Set (Ω → ℝ)} (hK : ClaimSetAEStronglyMeasurable μ K) :
    InMeasureSequentialClosure μ K = InMeasureSequentialClosure ν K := by
  ext g
  constructor
  · rintro ⟨f, hf, hfg⟩
    refine ⟨f, hf, ?_⟩
    exact (tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous hμν hνμ
      (fun n => hK (f n) (hf n))).1 hfg
  · rintro ⟨f, hf, hfg⟩
    refine ⟨f, hf, ?_⟩
    exact (tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous hμν hνμ
      (fun n => hK (f n) (hf n))).2 hfg

theorem ae_lowerBoundedBy_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {c : ℝ} {f : Ω → ℝ} :
    AELowerBoundedBy μ c f ↔ AELowerBoundedBy ν c f := by
  constructor
  · intro h
    exact hνμ.ae_le h
  · intro h
    exact hμν.ae_le h

theorem ae_nonnegative_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : Ω → ℝ} :
    AENonnegative μ f ↔ AENonnegative ν f := by
  constructor
  · intro h
    exact hνμ.ae_le h
  · intro h
    exact hμν.ae_le h

theorem eventuallyEq_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f g : Ω → ℝ} : f =ᵐ[μ] g ↔ f =ᵐ[ν] g := by
  constructor
  · intro h
    exact hνμ.ae_le h
  · intro h
    exact hμν.ae_le h

theorem aEMaximalIn_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {D : Set (Ω → ℝ)} {f : Ω → ℝ} :
    AEMaximalIn μ D f ↔ AEMaximalIn ν D f := by
  constructor
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg hdom
    exact hνμ.ae_le (hmax g hg (hμν.ae_le hdom))
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg hdom
    exact hμν.ae_le (hmax g hg (hνμ.ae_le hdom))

theorem eLpNormEssSup_eq_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : Ω → ℝ} :
    eLpNormEssSup f μ = eLpNormEssSup f ν := by
  apply le_antisymm
  · exact eLpNormEssSup_mono_measure f hμν
  · exact eLpNormEssSup_mono_measure f hνμ

theorem memLp_top_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : Ω → ℝ} : MemLp f ⊤ μ ↔ MemLp f ⊤ ν := by
  constructor
  · intro hf
    change eLpNorm f ⊤ _ < ⊤
    rw [eLpNorm_exponent_top (hf.aestronglyMeasurable.mono_ac hνμ)]
    exact (eLpNormEssSup_mono_measure f hνμ).trans_lt
      (by simpa [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top)
  · intro hf
    change eLpNorm f ⊤ _ < ⊤
    rw [eLpNorm_exponent_top (hf.aestronglyMeasurable.mono_ac hμν)]
    exact (eLpNormEssSup_mono_measure f hμν).trans_lt
      (by simpa [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top)

noncomputable def linftyTransfer
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) : Linfty (Ω := Ω) ν :=
  let hFν : MemLp (F : Ω → ℝ) ⊤ ν :=
    (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1
      (MeasureTheory.Lp.memLp F)
  hFν.toLp (F : Ω → ℝ)

theorem linftyTransfer_ae_eq
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) :
    ∀ᵐ ω ∂ν, linftyTransfer hμν hνμ F ω = F ω := by
  dsimp [linftyTransfer]
  exact (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1
    (MeasureTheory.Lp.memLp F) |>.coeFn_toLp

theorem linftyTransfer_ae_eq_source
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) :
    ∀ᵐ ω ∂μ, linftyTransfer hμν hνμ F ω = F ω := by
  exact hμν.ae_le (linftyTransfer_ae_eq hμν hνμ F)

theorem linftyTransfer_add
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F G : Linfty (Ω := Ω) μ) :
    linftyTransfer hμν hνμ (F + G) =
      linftyTransfer hμν hνμ F + linftyTransfer hμν hνμ G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [linftyTransfer_ae_eq hμν hνμ (F + G),
    linftyTransfer_ae_eq hμν hνμ F,
    linftyTransfer_ae_eq hμν hνμ G,
    hνμ.ae_le (MeasureTheory.Lp.coeFn_add F G),
    MeasureTheory.Lp.coeFn_add
      (linftyTransfer hμν hνμ F) (linftyTransfer hμν hνμ G)]
      with ω hFG hF hG hsource hsum
  calc
    linftyTransfer hμν hνμ (F + G) ω = (F + G) ω := hFG
    _ = F ω + G ω := by simpa using hsource
    _ = linftyTransfer hμν hνμ F ω + linftyTransfer hμν hνμ G ω := by
      rw [hF, hG]
    _ = (linftyTransfer hμν hνμ F + linftyTransfer hμν hνμ G) ω := by
      simpa using hsum.symm

theorem linftyTransfer_smul
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (c : ℝ) (F : Linfty (Ω := Ω) μ) :
    linftyTransfer hμν hνμ (c • F) =
      c • linftyTransfer hμν hνμ F := by
  apply MeasureTheory.Lp.ext
  filter_upwards [linftyTransfer_ae_eq hμν hνμ (c • F),
    linftyTransfer_ae_eq hμν hνμ F,
    hνμ.ae_le (MeasureTheory.Lp.coeFn_smul c F),
    MeasureTheory.Lp.coeFn_smul c (linftyTransfer hμν hνμ F)]
      with ω hsc hF hsource hsmul
  calc
    linftyTransfer hμν hνμ (c • F) ω = (c • F) ω := hsc
    _ = c * F ω := by simpa using hsource
    _ = c * linftyTransfer hμν hνμ F ω := by rw [hF]
    _ = (c • linftyTransfer hμν hνμ F) ω := by simpa using hsmul.symm

theorem linftyTransfer_norm
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) :
    ‖linftyTransfer hμν hνμ F‖ = ‖F‖ := by
  let hFν : MemLp (F : Ω → ℝ) ⊤ ν :=
    (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1
      (MeasureTheory.Lp.memLp F)
  calc
    ‖linftyTransfer hμν hνμ F‖ =
        ENNReal.toReal (eLpNorm (F : Ω → ℝ) ⊤ ν) := by
          dsimp [linftyTransfer]
          exact MeasureTheory.Lp.norm_toLp (F : Ω → ℝ) hFν
    _ = ENNReal.toReal (eLpNormEssSup (F : Ω → ℝ) ν) := by
          rw [eLpNorm_exponent_top hFν.aestronglyMeasurable]
    _ = ENNReal.toReal (eLpNormEssSup (F : Ω → ℝ) μ) := by
          rw [eLpNormEssSup_eq_of_mutuallyAbsolutelyContinuous hμν hνμ]
    _ = ENNReal.toReal (eLpNorm (F : Ω → ℝ) ⊤ μ) := by
          rw [eLpNorm_exponent_top (MeasureTheory.Lp.aestronglyMeasurable F)]
    _ = ‖(MeasureTheory.Lp.memLp F).toLp (F : Ω → ℝ)‖ := by
          exact (MeasureTheory.Lp.norm_toLp (F : Ω → ℝ)
            (MeasureTheory.Lp.memLp F)).symm
    _ = ‖F‖ := by
          rw [MeasureTheory.Lp.toLp_coeFn]

noncomputable def linftyTransferLinear
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Linfty (Ω := Ω) μ →ₗ[ℝ] Linfty (Ω := Ω) ν where
  toFun := linftyTransfer hμν hνμ
  map_add' F G := linftyTransfer_add hμν hνμ F G
  map_smul' c F := linftyTransfer_smul hμν hνμ c F

theorem linftyTransfer_comp_ae
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) :
    ∀ᵐ ω ∂μ,
      linftyTransfer hνμ hμν (linftyTransfer hμν hνμ F) ω = F ω := by
  filter_upwards [linftyTransfer_ae_eq hνμ hμν (linftyTransfer hμν hνμ F),
    hμν.ae_le (linftyTransfer_ae_eq hμν hνμ F)] with ω houter hinner
  exact houter.trans hinner

noncomputable def linftyMeasureEquiv
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Linfty (Ω := Ω) μ ≃ₗᵢ[ℝ] Linfty (Ω := Ω) ν := by
  let f : Linfty (Ω := Ω) μ →ₗᵢ[ℝ] Linfty (Ω := Ω) ν :=
    { linftyTransferLinear hμν hνμ with
      norm_map' := linftyTransfer_norm hμν hνμ }
  let g : Linfty (Ω := Ω) ν →ₗ[ℝ] Linfty (Ω := Ω) μ :=
    linftyTransferLinear hνμ hμν
  apply LinearIsometryEquiv.ofLinearIsometry f g
  · apply LinearMap.ext
    intro F
    change linftyTransfer hμν hνμ (linftyTransfer hνμ hμν F) = F
    apply MeasureTheory.Lp.ext
    filter_upwards [linftyTransfer_comp_ae hνμ hμν F] with ω hω
    exact hω
  · apply LinearMap.ext
    intro F
    change linftyTransfer hνμ hμν (linftyTransfer hμν hνμ F) = F
    apply MeasureTheory.Lp.ext
    filter_upwards [linftyTransfer_comp_ae hμν hνμ F] with ω hω
    exact hω

theorem c0AsDifference_eq_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {K0 : Set (Ω → ℝ)} :
    C0AsDifference μ K0 = C0AsDifference ν K0 := by
  ext f
  constructor
  · rintro ⟨g, hg, h, hh, hsub⟩
    refine ⟨g, hg, h, (ae_nonnegative_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 hh,
      ?_⟩
    exact (eventuallyEq_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 hsub
  · rintro ⟨g, hg, h, hh, hsub⟩
    refine ⟨g, hg, h, (ae_nonnegative_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).2 hh,
      ?_⟩
    exact (eventuallyEq_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).2 hsub

theorem linftyMeasureEquiv_toLp
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : Ω → ℝ} (hfμ : MemLp f ⊤ μ) :
    linftyMeasureEquiv hμν hνμ (hfμ.toLp f) =
      ((memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 hfμ).toLp f := by
  let hfν : MemLp f ⊤ ν :=
    (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 hfμ
  apply MeasureTheory.Lp.ext
  filter_upwards [linftyTransfer_ae_eq hμν hνμ (hfμ.toLp f),
    hνμ.ae_le hfμ.coeFn_toLp, hfν.coeFn_toLp] with ω hmap hsource htarget
  exact hmap.trans (hsource.trans htarget.symm)

theorem linftyMeasureEquiv_image_LinftyClaims
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {D : Set (Ω → ℝ)} :
    linftyMeasureEquiv hμν hνμ '' LinftyClaims μ D = LinftyClaims ν D := by
  apply Set.Subset.antisymm
  · rintro G ⟨F, hF, rfl⟩
    rcases hF with ⟨f, hfD, hfμ, rfl⟩
    let hfν : MemLp f ⊤ ν :=
      (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 hfμ
    refine ⟨f, hfD, hfν, ?_⟩
    exact (linftyMeasureEquiv_toLp hμν hνμ hfμ).symm
  · rintro G ⟨f, hfD, hfν, rfl⟩
    let hfμ : MemLp f ⊤ μ :=
      (memLp_top_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).2 hfν
    refine ⟨hfμ.toLp f, ⟨f, hfD, hfμ, rfl⟩, ?_⟩
    exact linftyMeasureEquiv_toLp hμν hνμ hfμ

theorem linftyMeasureEquiv_mem_LinftyNonnegative_iff
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (F : Linfty (Ω := Ω) μ) :
    linftyMeasureEquiv hμν hνμ F ∈ LinftyNonnegative ν ↔
      F ∈ LinftyNonnegative μ := by
  change linftyTransfer hμν hνμ F ∈ LinftyNonnegative ν ↔
    F ∈ LinftyNonnegative μ
  constructor
  · intro hF
    filter_upwards [linftyTransfer_ae_eq_source hμν hνμ F,
      hμν.ae_le hF] with ω hEq hnonneg
    exact hEq ▸ hnonneg
  · intro hF
    filter_upwards [linftyTransfer_ae_eq hμν hνμ F,
      hνμ.ae_le hF] with ω hEq hnonneg
    exact hEq.symm ▸ hnonneg

theorem linftyNFLVR_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {D : Set (Ω → ℝ)} :
    LinftyNFLVR μ (LinftyClaims μ D) ↔
      LinftyNFLVR ν (LinftyClaims ν D) := by
  let e := linftyMeasureEquiv hμν hνμ
  have hC : e '' LinftyClaims μ D = LinftyClaims ν D :=
    linftyMeasureEquiv_image_LinftyClaims hμν hνμ
  have hClosure : e '' closure (LinftyClaims μ D) =
      closure (LinftyClaims ν D) := by
    calc
      e '' closure (LinftyClaims μ D) =
          closure (e '' LinftyClaims μ D) :=
        e.toContinuousLinearEquiv.image_closure (LinftyClaims μ D)
      _ = closure (LinftyClaims ν D) := by rw [hC]
  have hNonneg : ∀ F : Linfty (Ω := Ω) μ,
      e F ∈ LinftyNonnegative ν ↔ F ∈ LinftyNonnegative μ := by
    intro F
    exact linftyMeasureEquiv_mem_LinftyNonnegative_iff hμν hνμ F
  constructor
  · intro hNFLVR
    rw [linftyNFLVR_iff] at hNFLVR ⊢
    intro F hFcl hFpos
    have hFcl' : e.symm F ∈ closure (LinftyClaims μ D) := by
      have hmem : F ∈ e '' closure (LinftyClaims μ D) := by
        rw [hClosure]
        exact hFcl
      rcases hmem with ⟨G, hGcl, hGF⟩
      have hGeq : G = e.symm F := by
        rw [← hGF, e.symm_apply_apply]
      simpa only [hGeq] using hGcl
    have hFpos' : e.symm F ∈ LinftyNonnegative μ := by
      apply (hNonneg (e.symm F)).mp
      simpa only [e.apply_symm_apply] using hFpos
    have hzero : e.symm F = 0 := hNFLVR (e.symm F) hFcl' hFpos'
    exact e.symm.injective (hzero.trans e.symm.map_zero.symm)
  · intro hNFLVR
    rw [linftyNFLVR_iff] at hNFLVR ⊢
    intro F hFcl hFpos
    have hFcl' : e F ∈ closure (LinftyClaims ν D) := by
      rw [← hClosure]
      exact ⟨F, hFcl, rfl⟩
    have hFpos' : e F ∈ LinftyNonnegative ν := (hNonneg F).mpr hFpos
    have hzero : e F = 0 := hNFLVR (e F) hFcl' hFpos'
    exact e.injective (hzero.trans e.map_zero.symm)

theorem admissibleBy_iff_of_mutuallyAbsolutelyContinuous
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {a : ℝ} {H : A.Strategy} :
    A.AdmissibleBy μ a H ↔ A.AdmissibleBy ν a H := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro t
    exact (ae_lowerBoundedBy_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 (h.2 t)
  · intro h
    refine ⟨h.1, ?_⟩
    intro t
    exact (ae_lowerBoundedBy_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).2 (h.2 t)

theorem oneAdmissible_iff_of_mutuallyAbsolutelyContinuous
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {H : A.Strategy} :
    A.OneAdmissible μ H ↔ A.OneAdmissible ν H := by
  exact admissibleBy_iff_of_mutuallyAbsolutelyContinuous A hμν hνμ

theorem admissible_iff_of_mutuallyAbsolutelyContinuous
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {H : A.Strategy} :
    A.Admissible μ H ↔ A.Admissible ν H := by
  constructor
  · rintro ⟨a, ha, hA⟩
    exact ⟨a, ha, fun t =>
      (ae_lowerBoundedBy_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).1 (hA t)⟩
  · rintro ⟨a, ha, hA⟩
    exact ⟨a, ha, fun t =>
      (ae_lowerBoundedBy_iff_of_mutuallyAbsolutelyContinuous hμν hνμ).2 (hA t)⟩

theorem K0OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    A.K0OfGainProcessModel μ = A.K0OfGainProcessModel ν := by
  ext f
  constructor
  · rintro ⟨H, hH, rfl⟩
    exact ⟨H, (admissible_iff_of_mutuallyAbsolutelyContinuous A hμν hνμ).1 hH, rfl⟩
  · rintro ⟨H, hH, rfl⟩
    exact ⟨H, (admissible_iff_of_mutuallyAbsolutelyContinuous A hμν hνμ).2 hH, rfl⟩

theorem linftyNFLVR_iff_of_mutuallyAbsolutelyContinuous_gainProcessModel
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    LinftyNFLVR μ
        (LinftyClaims μ (C0AsDifference μ (A.K0OfGainProcessModel μ))) ↔
      LinftyNFLVR ν
        (LinftyClaims ν (C0AsDifference ν (A.K0OfGainProcessModel ν))) := by
  have hK := K0OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous A hμν hνμ
  have hD :
      C0AsDifference μ (A.K0OfGainProcessModel μ) =
        C0AsDifference ν (A.K0OfGainProcessModel ν) := by
    calc
      C0AsDifference μ (A.K0OfGainProcessModel μ) =
          C0AsDifference ν (A.K0OfGainProcessModel μ) :=
        c0AsDifference_eq_of_mutuallyAbsolutelyContinuous hμν hνμ
      _ = C0AsDifference ν (A.K0OfGainProcessModel ν) := by rw [hK]
  have hgen :=
    linftyNFLVR_iff_of_mutuallyAbsolutelyContinuous hμν hνμ
      (D := C0AsDifference μ (A.K0OfGainProcessModel μ))
  constructor
  · intro h
    have h' := hgen.mp h
    simpa only [hD] using h'
  · intro h
    apply hgen.mpr
    simpa only [hD] using h

theorem K1OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous
    {Time : Type*} (A : GainProcessModel Ω Time)
    {μ ν : Measure Ω} (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    A.K1OfGainProcessModel μ = A.K1OfGainProcessModel ν := by
  ext f
  constructor
  · rintro ⟨H, hH, rfl⟩
    exact ⟨H, (oneAdmissible_iff_of_mutuallyAbsolutelyContinuous A hμν hνμ).1 hH, rfl⟩
  · rintro ⟨H, hH, rfl⟩
    exact ⟨H, (oneAdmissible_iff_of_mutuallyAbsolutelyContinuous A hμν hνμ).2 hH, rfl⟩

end EquivalentMeasureTransfer
end FTAPTheorem42
