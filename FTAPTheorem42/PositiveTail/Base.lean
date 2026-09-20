import FTAPTheorem42.Core.WeakStar
import FTAPTheorem42.Core.FSpace
import FTAPTheorem42.Core.L1DualRepresentation
import FTAPTheorem42.Core.WeakStarBoundedSlice
import FTAPTheorem42.Core.KreinSmulian
import FTAPTheorem42.Core.KreinSmulianC0
import FTAPTheorem42.Core.KreinSmulianC0Separation
import FTAPTheorem42.Core.C0DualCoefficients
import FTAPTheorem42.Core.KreinSmulianPredualSeparator
import FTAPTheorem42.Core.KreinSmulianCriterion
import FTAPTheorem42.Core.WeakStarFatouClosed
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Positive-tail truncation and Egorov lifting

This module contains the Proposition 3.1 oriented positive-tail truncation,
the bounded/truncated Komlós-lite interfaces, and the Egorov-to-`L∞` bridge.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The positive denominator used for the shifted positive-tail truncation. -/
def positiveTailScaleDenom (n : ℕ) : ℝ :=
  (n.succ : ℝ)

theorem positiveTailScaleDenom_pos (n : ℕ) :
    0 < positiveTailScaleDenom n := by
  unfold positiveTailScaleDenom
  exact_mod_cast Nat.succ_pos n

theorem positiveTailScaleDenom_nonneg (n : ℕ) :
    0 ≤ positiveTailScaleDenom n :=
  le_of_lt (positiveTailScaleDenom_pos n)

theorem positiveTailScaleDenom_inv_nonneg (n : ℕ) :
    0 ≤ (positiveTailScaleDenom n)⁻¹ :=
  inv_nonneg.mpr (positiveTailScaleDenom_nonneg n)

/--
Scale the `n.succ`-th positive-tail witness by the positive denominator
`n.succ`.  The shift keeps the denominator away from zero.
-/
noncomputable def positiveTailScaled (G : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (positiveTailScaleDenom n)⁻¹ * G n.succ ω

/--
The bounded truncation used in Proposition 3.1: `min (Gₙ / n) 1`, with the
index shifted so that the denominator is positive.
-/
noncomputable def positiveTailTrunc (G : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  positiveTailScaled G n ⊓ fun _ => (1 : ℝ)

theorem positiveTailTrunc_le_scaled {μ : Measure Ω}
    (G : ℕ → Ω → ℝ) (n : ℕ) :
    AEDominatedBy μ (positiveTailTrunc G n) (positiveTailScaled G n) := by
  exact Eventually.of_forall fun ω => inf_le_left

theorem positiveTailTrunc_aeUpperBounded {μ : Measure Ω}
    (G : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, positiveTailTrunc G n ω ≤ 1 := by
  exact Eventually.of_forall fun ω => inf_le_right

omit [MeasurableSpace Ω] in
theorem positiveTailScaled_mem_K0
    {K0 : Set (Ω → ℝ)} (hK : ClaimCone K0) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, G n ∈ K0) (n : ℕ) :
    positiveTailScaled G n ∈ K0 := by
  exact hK.nonnegSMulInvariant
    (positiveTailScaleDenom_inv_nonneg n)
    (hG n.succ)

theorem positiveTailScaled_mem_C0AsDifference
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} (hK : ClaimCone K0)
    {G : ℕ → Ω → ℝ} (hG : ∀ n, G n ∈ K0) (n : ℕ) :
    positiveTailScaled G n ∈ C0AsDifference μ K0 := by
  have hscaledK : positiveTailScaled G n ∈ K0 :=
    positiveTailScaled_mem_K0 (Ω := Ω) hK hG n
  have hscaledC0 :
      positiveTailScaled G n ∈ C0FromTerminalGains μ K0 :=
    terminalGain_mem_C0FromTerminalGains μ hscaledK
  simpa [C0AsDifference_eq_C0FromTerminalGains μ K0] using hscaledC0

theorem positiveTailTrunc_mem_C0AsDifference
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} (hK : ClaimCone K0)
    {G : ℕ → Ω → ℝ} (hG : ∀ n, G n ∈ K0) (n : ℕ) :
    positiveTailTrunc G n ∈ C0AsDifference μ K0 :=
  C0AsDifference_solid μ K0
    (positiveTailScaled_mem_C0AsDifference (Ω := Ω) hK hG n)
    (positiveTailTrunc_le_scaled (μ := μ) G n)

theorem positiveTailScaled_aestronglyMeasurable
    {μ : Measure Ω} {G : ℕ → Ω → ℝ}
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) μ) (n : ℕ) :
    AEStronglyMeasurable (positiveTailScaled G n) μ := by
  change AEStronglyMeasurable
    (fun ω => (positiveTailScaleDenom n)⁻¹ * G n.succ ω) μ
  exact (hGmeas n.succ).const_mul (positiveTailScaleDenom n)⁻¹

theorem positiveTailTrunc_aestronglyMeasurable
    {μ : Measure Ω} {G : ℕ → Ω → ℝ}
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) μ) (n : ℕ) :
    AEStronglyMeasurable (positiveTailTrunc G n) μ := by
  simpa [positiveTailTrunc] using
    (positiveTailScaled_aestronglyMeasurable (μ := μ) hGmeas n).inf
      aestronglyMeasurable_const

theorem positiveTailTrunc_aeLowerBounded
    {μ : Measure Ω} {G : ℕ → Ω → ℝ} {n : ℕ}
    (hlow : AELowerBoundedBy μ (-1) (G n.succ)) :
    AELowerBoundedBy μ (-(positiveTailScaleDenom n)⁻¹)
      (positiveTailTrunc G n) := by
  filter_upwards [hlow] with ω hlowω
  have hdpos : 0 < positiveTailScaleDenom n := positiveTailScaleDenom_pos n
  have hinvnonneg : 0 ≤ (positiveTailScaleDenom n)⁻¹ :=
    positiveTailScaleDenom_inv_nonneg n
  have hscaled :
      -(positiveTailScaleDenom n)⁻¹ ≤ positiveTailScaled G n ω := by
    have hmul :
        (positiveTailScaleDenom n)⁻¹ * (-1) ≤
          (positiveTailScaleDenom n)⁻¹ * G n.succ ω :=
      mul_le_mul_of_nonneg_left hlowω hinvnonneg
    calc
      -(positiveTailScaleDenom n)⁻¹ =
          (positiveTailScaleDenom n)⁻¹ * (-1) := by ring
      _ ≤ positiveTailScaled G n ω := by
        simpa [positiveTailScaled] using hmul
  have hone : -(positiveTailScaleDenom n)⁻¹ ≤ (1 : ℝ) := by
    have hnonpos : -(positiveTailScaleDenom n)⁻¹ ≤ 0 := by
      exact neg_nonpos.mpr hinvnonneg
    linarith
  exact le_inf hscaled hone

omit [MeasurableSpace Ω] in
theorem positiveTail_subset_trunc_eq_one
    {G : ℕ → Ω → ℝ} (n : ℕ) :
    {ω | positiveTailScaleDenom n < G n.succ ω} ⊆
      {ω | positiveTailTrunc G n ω = 1} := by
  intro ω hω
  have hdpos : 0 < positiveTailScaleDenom n := positiveTailScaleDenom_pos n
  have hscaled_ge_one :
      1 ≤ positiveTailScaled G n ω := by
    have hmul :
        (positiveTailScaleDenom n)⁻¹ * positiveTailScaleDenom n <
          (positiveTailScaleDenom n)⁻¹ * G n.succ ω :=
      mul_lt_mul_of_pos_left hω (inv_pos.mpr hdpos)
    have hleft :
        (positiveTailScaleDenom n)⁻¹ * positiveTailScaleDenom n = 1 :=
      inv_mul_cancel₀ (ne_of_gt hdpos)
    rw [hleft] at hmul
    exact le_of_lt hmul
  exact inf_eq_right.mpr hscaled_ge_one

omit [MeasurableSpace Ω] in
theorem positiveTail_subset_trunc_gt_half
    {G : ℕ → Ω → ℝ} (n : ℕ) :
    {ω | positiveTailScaleDenom n < G n.succ ω} ⊆
      {ω | (1 / 2 : ℝ) < positiveTailTrunc G n ω} := by
  intro ω hω
  have hone : positiveTailTrunc G n ω = 1 :=
    positiveTail_subset_trunc_eq_one (Ω := Ω) (G := G) n hω
  change (1 / 2 : ℝ) < positiveTailTrunc G n ω
  rw [hone]
  norm_num

theorem positiveTailTrunc_mem_C0_bounds_mass
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} (hK : ClaimCone K0)
    {ε : ℝ} {G : ℕ → Ω → ℝ}
    (hG : ∀ n, G n ∈ K0)
    (hlow : ∀ n, AELowerBoundedBy μ (-1) (G n))
    (htail : ∀ n : ℕ, ENNReal.ofReal ε < μ {ω | (n : ℝ) < G n ω}) :
    ∀ n,
      positiveTailTrunc G n ∈ C0AsDifference μ K0 ∧
      AELowerBoundedBy μ (-(positiveTailScaleDenom n)⁻¹)
        (positiveTailTrunc G n) ∧
      (∀ᵐ ω ∂μ, positiveTailTrunc G n ω ≤ 1) ∧
      ENNReal.ofReal ε < μ {ω | positiveTailTrunc G n ω = 1} ∧
      ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < positiveTailTrunc G n ω} := by
  intro n
  have htail_succ :
      ENNReal.ofReal ε <
        μ {ω | positiveTailScaleDenom n < G n.succ ω} := by
    simpa [positiveTailScaleDenom] using htail n.succ
  refine ⟨
    positiveTailTrunc_mem_C0AsDifference (Ω := Ω) hK hG n,
    positiveTailTrunc_aeLowerBounded (μ := μ) (G := G) (n := n) (hlow n.succ),
    positiveTailTrunc_aeUpperBounded (μ := μ) G n,
    ?_,
    ?_⟩
  · exact lt_of_lt_of_le htail_succ
      (measure_mono (positiveTail_subset_trunc_eq_one (Ω := Ω) (G := G) n))
  · exact lt_of_lt_of_le htail_succ
      (measure_mono (positiveTail_subset_trunc_gt_half (Ω := Ω) (G := G) n))

theorem positiveTailTrunc_mem_C0_meas_bounds_mass
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} (hK : ClaimCone K0)
    (hKmeas : ClaimSetAEStronglyMeasurable μ K0)
    {ε : ℝ} {G : ℕ → Ω → ℝ}
    (hG : ∀ n, G n ∈ K0)
    (hlow : ∀ n, AELowerBoundedBy μ (-1) (G n))
    (htail : ∀ n : ℕ, ENNReal.ofReal ε < μ {ω | (n : ℝ) < G n ω}) :
    ∀ n,
      positiveTailTrunc G n ∈ C0AsDifference μ K0 ∧
      AEStronglyMeasurable (positiveTailTrunc G n) μ ∧
      AELowerBoundedBy μ (-(positiveTailScaleDenom n)⁻¹)
        (positiveTailTrunc G n) ∧
      (∀ᵐ ω ∂μ, positiveTailTrunc G n ω ≤ 1) ∧
      ENNReal.ofReal ε < μ {ω | positiveTailTrunc G n ω = 1} ∧
      ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < positiveTailTrunc G n ω} := by
  intro n
  have hpack := positiveTailTrunc_mem_C0_bounds_mass
    (μ := μ) (K0 := K0) hK hG hlow htail n
  exact ⟨hpack.1,
    positiveTailTrunc_aestronglyMeasurable (μ := μ)
      (fun k => hKmeas (G k) (hG k)) n,
    hpack.2.1,
    hpack.2.2.1,
    hpack.2.2.2.1,
    hpack.2.2.2.2⟩

theorem positiveTailScaleInv_antitone :
    Antitone (fun n : ℕ => (positiveTailScaleDenom n)⁻¹) := by
  intro m n hmn
  have hle : positiveTailScaleDenom m ≤ positiveTailScaleDenom n := by
    unfold positiveTailScaleDenom
    exact_mod_cast Nat.succ_le_succ hmn
  simpa [one_div] using
    one_div_le_one_div_of_le (positiveTailScaleDenom_pos m) hle

theorem positiveTailScaleInv_tendsto_zero :
    Tendsto (fun n : ℕ => (positiveTailScaleDenom n)⁻¹) atTop (nhds 0) := by
  simpa [positiveTailScaleDenom, Nat.cast_add_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem abs_inf_one_sub_le_abs_sub_of_le_one
    {x y : ℝ} (hy : y ≤ 1) :
    |(x ⊓ 1) - y| ≤ |x - y| := by
  by_cases hx : x ≤ 1
  · rw [inf_eq_left.mpr hx]
  · have hxle : 1 ≤ x := le_of_not_ge hx
    rw [inf_eq_right.mpr hxle]
    rw [abs_of_nonneg (sub_nonneg.mpr hy),
      abs_of_nonneg (sub_nonneg.mpr (le_trans hy hxle))]
    linarith

theorem abs_inf_zero_le_of_lower
    {x δ : ℝ} (hδ : 0 ≤ δ) (hlow : -δ ≤ x) :
    |(x ⊓ 0)| ≤ δ := by
  by_cases hx : x ≤ 0
  · rw [inf_eq_left.mpr hx]
    rw [abs_of_nonpos hx]
    linarith
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    rw [inf_eq_right.mpr hx0]
    simpa using hδ

/--
If a real-valued function is positive on a set of positive measure, then it is
bounded away from zero on a set of positive measure.  This is the level-set
selection used before applying Egorov.
-/
theorem exists_pos_level_measure_pos
    {μ : Measure Ω} {g : Ω → ℝ}
    (hpos : 0 < μ {ω | 0 < g ω}) :
    ∃ c : ℝ, 0 < c ∧ 0 < μ {ω | c < g ω} := by
  let s : ℕ → Set Ω := fun n => {ω | (1 / ((n : ℝ) + 1)) < g ω}
  have hs_eq : {ω | 0 < g ω} = ⋃ n, s n := by
    ext ω
    constructor
    · intro hω
      rcases exists_nat_one_div_lt (show 0 < g ω from hω) with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
      have hfrac : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact lt_trans hfrac hn
  have hnot : μ (⋃ n, s n) ≠ 0 := by
    rw [← hs_eq]
    exact ne_of_gt hpos
  rcases exists_measure_pos_of_not_measure_iUnion_null hnot with ⟨n, hn⟩
  exact ⟨1 / ((n : ℝ) + 1), by positivity, by simpa [s] using hn⟩

/--
In a finite measure space, any positive-measure set dominates a positive real
`ofReal` level.  This chooses the Egorov exceptional-measure budget.
-/
theorem exists_ofReal_lt_measure_of_pos
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hspos : 0 < μ s) :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η < μ s := by
  refine ⟨(μ s).toReal / 2, ?_, ?_⟩
  · exact half_pos (ENNReal.toReal_pos (ne_of_gt hspos) (measure_ne_top μ s))
  · have hμpos : 0 < (μ s).toReal :=
      ENNReal.toReal_pos (ne_of_gt hspos) (measure_ne_top μ s)
    have hηnonneg : 0 ≤ (μ s).toReal / 2 := by positivity
    rw [ENNReal.ofReal_lt_iff_lt_toReal hηnonneg (measure_ne_top μ s)]
    linarith

/-- Removing a strictly smaller-measure set leaves positive measure. -/
theorem measure_diff_pos_of_measure_lt
    {μ : Measure Ω} {s t : Set Ω} (hlt : μ t < μ s) :
    0 < μ (s \ t) := by
  by_contra hnot
  have hzero : μ (s \ t) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hsubset : s ⊆ (s \ t) ∪ t := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Or.inr hxt
    · exact Or.inl ⟨hx, hxt⟩
  have hle : μ s ≤ μ t := by
    calc
      μ s ≤ μ ((s \ t) ∪ t) := measure_mono hsubset
      _ ≤ μ (s \ t) + μ t := measure_union_le _ _
      _ = μ t := by rw [hzero, zero_add]
  exact (not_le_of_gt hlt) hle

/-- Egorov's theorem in the finite-measure form used by the `L∞` lifting step. -/
theorem egorov_tendstoUniformlyOn_compl
    {μ : Measure Ω} [IsFiniteMeasure μ] {gseq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hgseq : ∀ n, StronglyMeasurable (gseq n))
    (hg : StronglyMeasurable g)
    (hlim : TendstoAE μ gseq g) {η : ℝ} (hη : 0 < η) :
    ∃ t : Set Ω,
      MeasurableSet t ∧
      μ t ≤ ENNReal.ofReal η ∧
      TendstoUniformlyOn gseq g atTop tᶜ :=
  tendstoUniformlyOn_of_ae_tendsto' hgseq hg hlim (ENNReal.ofReal_pos.mpr hη)

/--
After choosing a positive level set of the a.e. limit, Egorov gives a
positive-measure subset on which convergence is uniform.
-/
theorem egorov_exists_positive_uniform_set
    {μ : Measure Ω} [IsFiniteMeasure μ] {gseq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    {c : ℝ}
    (hgseq : ∀ n, StronglyMeasurable (gseq n))
    (hg : StronglyMeasurable g)
    (hlim : TendstoAE μ gseq g)
    (hlevel : 0 < μ {ω | c < g ω}) :
    ∃ A : Set Ω,
      A ⊆ {ω | c < g ω} ∧
      MeasurableSet A ∧
      0 < μ A ∧
      TendstoUniformlyOn gseq g atTop A := by
  rcases exists_ofReal_lt_measure_of_pos (μ := μ) (s := {ω | c < g ω})
      hlevel with
    ⟨η, hηpos, hηlt⟩
  rcases egorov_tendstoUniformlyOn_compl (μ := μ) hgseq hg hlim hηpos with
    ⟨t, _htmeas, htμ, htendsto⟩
  refine ⟨{ω | c < g ω} \ t, ?_, ?_, ?_, ?_⟩
  · intro ω hω
    exact hω.1
  · exact (stronglyMeasurable_const.measurableSet_lt hg).diff _htmeas
  · exact measure_diff_pos_of_measure_lt (lt_of_le_of_lt htμ hηlt)
  · exact htendsto.mono (by intro ω hω; exact hω.2)

/-- Clip a sequence by the indicator of the Egorov uniform-convergence set. -/
noncomputable def egorovClip (A : Set Ω) (gseq : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  gseq n ⊓ A.indicator (fun _ => (1 : ℝ))

/-- The `L∞` representative targeted by the Egorov-clipped sequence. -/
noncomputable def egorovLimit (A : Set Ω) (g : Ω → ℝ) : Ω → ℝ :=
  A.indicator g

theorem egorovClip_le (A : Set Ω) (gseq : ℕ → Ω → ℝ) (n : ℕ) :
    AEDominatedBy μ (egorovClip A gseq n) (gseq n) := by
  exact Eventually.of_forall fun _ => inf_le_left

theorem egorovClip_mem_of_solid
    {μ : Measure Ω} {C0 : Set (Ω → ℝ)} (hSolid : Solid μ C0)
    {A : Set Ω} {gseq : ℕ → Ω → ℝ}
    (hgseq : ∀ n, gseq n ∈ C0) (n : ℕ) :
    egorovClip A gseq n ∈ C0 :=
  hSolid (hgseq n) (egorovClip_le (μ := μ) A gseq n)

theorem egorovClip_aestronglyMeasurable
    {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A)
    {gseq : ℕ → Ω → ℝ}
    (hgseq : ∀ n, AEStronglyMeasurable (gseq n) μ) (n : ℕ) :
    AEStronglyMeasurable (egorovClip A gseq n) μ := by
  have hInd :
      AEStronglyMeasurable (A.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (aestronglyMeasurable_const (b := (1 : ℝ))).indicator hA
  simpa [egorovClip] using (hgseq n).inf hInd

theorem egorovLimit_aestronglyMeasurable
    {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (egorovLimit A g) μ := by
  simpa [egorovLimit] using hg.indicator hA

theorem egorovClip_aeLowerBounded
    {μ : Measure Ω} {A : Set Ω} {gseq : ℕ → Ω → ℝ}
    {δ : ℕ → ℝ} {n : ℕ}
    (hδnonneg : 0 ≤ δ n)
    (hlower : AELowerBoundedBy μ (-(δ n)) (gseq n)) :
    AELowerBoundedBy μ (-(δ n)) (egorovClip A gseq n) := by
  filter_upwards [hlower] with ω hω
  have hInd : -(δ n) ≤ A.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA]
      linarith
    · rw [Set.indicator_of_notMem hωA]
      exact neg_nonpos.mpr hδnonneg
  exact le_inf hω hInd

theorem egorovClip_aeUpperBounded_one
    {μ : Measure Ω} {A : Set Ω} {gseq : ℕ → Ω → ℝ} (n : ℕ) :
    ∀ᵐ ω ∂μ, egorovClip A gseq n ω ≤ 1 := by
  refine Eventually.of_forall fun ω => ?_
  have hInd : A.indicator (fun _ : Ω => (1 : ℝ)) ω ≤ 1 := by
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA]
    · rw [Set.indicator_of_notMem hωA]
      norm_num
  exact le_trans inf_le_right hInd

theorem egorovClip_memLp_top
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {gseq : ℕ → Ω → ℝ} {δ : ℕ → ℝ} {n : ℕ}
    (hδnonneg : 0 ≤ δ n)
    (hgseqMeas : ∀ n, AEStronglyMeasurable (gseq n) μ)
    (hlower : AELowerBoundedBy μ (-(δ n)) (gseq n)) :
    MemLp (egorovClip A gseq n) ⊤ μ := by
  refine MemLp.of_bound
    (egorovClip_aestronglyMeasurable (μ := μ) hA hgseqMeas n)
    (δ n + 1) ?_
  filter_upwards [
    egorovClip_aeLowerBounded (μ := μ) (A := A) (gseq := gseq)
      (δ := δ) (n := n) hδnonneg hlower,
    egorovClip_aeUpperBounded_one (μ := μ) (A := A) (gseq := gseq) n
  ] with ω hlowω huω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem egorovLimit_memLp_top
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {g : Ω → ℝ}
    (hgMeas : AEStronglyMeasurable g μ)
    (hgnonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1) :
    MemLp (egorovLimit A g) ⊤ μ := by
  refine MemLp.of_bound
    (egorovLimit_aestronglyMeasurable (μ := μ) hA hgMeas) 1 ?_
  filter_upwards [hgnonneg, hgle_one] with ω hg0 hg1
  rw [Real.norm_eq_abs]
  by_cases hωA : ω ∈ A
  · rw [egorovLimit, Set.indicator_of_mem hωA]
    exact abs_le.mpr ⟨by linarith, hg1⟩
  · rw [egorovLimit, Set.indicator_of_notMem hωA]
    norm_num

theorem egorovLimit_toLp_ne_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {g : Ω → ℝ} {c : ℝ}
    (hcpos : 0 < c)
    (hApos : 0 < μ A)
    (hAsub : A ⊆ {ω | c < g ω})
    (hgMeas : AEStronglyMeasurable g μ)
    (hgnonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1) :
    (egorovLimit_memLp_top (μ := μ) (A := A) hA
      (g := g) hgMeas hgnonneg hgle_one).toLp (egorovLimit A g) ≠ 0 := by
  intro hzero
  let hF : MemLp (egorovLimit A g) ⊤ μ :=
    egorovLimit_memLp_top (μ := μ) (A := A) hA
      (g := g) hgMeas hgnonneg hgle_one
  have hzero_toLp :
      hF.toLp (egorovLimit A g) =
        (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ)).toLp (0 : Ω → ℝ) := by
    rw [hzero]
    exact (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ)).toLp_zero.symm
  have hae_zero : egorovLimit A g =ᵐ[μ] (0 : Ω → ℝ) := by
    exact (MemLp.toLp_eq_toLp_iff hF
      (MemLp.zero (α := Ω) (ε := ℝ) (p := ⊤) (μ := μ))).mp hzero_toLp
  have hpos_zero : μ {ω | 0 < egorovLimit A g ω} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae_zero] with ω hωeq hωpos
    rw [hωeq] at hωpos
    exact (lt_irrefl (0 : ℝ)) hωpos
  have hA_subset_pos : A ⊆ {ω | 0 < egorovLimit A g ω} := by
    intro ω hωA
    have hgpos : 0 < g ω := lt_trans hcpos (hAsub hωA)
    change 0 < egorovLimit A g ω
    rw [egorovLimit, Set.indicator_of_mem hωA]
    exact hgpos
  have hA_zero : μ A = 0 :=
    le_antisymm ((measure_mono hA_subset_pos).trans_eq hpos_zero) bot_le
  exact (ne_of_gt hApos) hA_zero

theorem egorovClip_ae_abs_sub_limit_le
    {μ : Measure Ω} {A : Set Ω} {gseq : ℕ → Ω → ℝ} {g : Ω → ℝ}
    {δ : ℕ → ℝ} {n : ℕ} {ε : ℝ}
    (hεnonneg : 0 ≤ ε)
    (hδnonneg : 0 ≤ δ n)
    (hclose : ∀ ω ∈ A, |gseq n ω - g ω| ≤ ε)
    (hlower : AELowerBoundedBy μ (-(δ n)) (gseq n))
    (hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1) :
    ∀ᵐ ω ∂μ,
      |egorovClip A gseq n ω - egorovLimit A g ω| ≤ ε + δ n := by
  filter_upwards [hlower, hgle_one] with ω hlowω hg1ω
  by_cases hωA : ω ∈ A
  · rw [egorovClip, egorovLimit, Pi.inf_apply]
    rw [Set.indicator_of_mem hωA, Set.indicator_of_mem hωA]
    have hmain : |(gseq n ω ⊓ 1) - g ω| ≤ |gseq n ω - g ω| :=
      abs_inf_one_sub_le_abs_sub_of_le_one hg1ω
    exact le_trans hmain (by linarith [hclose ω hωA])
  · rw [egorovClip, egorovLimit, Pi.inf_apply]
    rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωA, sub_zero]
    have hmain : |gseq n ω ⊓ 0| ≤ δ n :=
      abs_inf_zero_le_of_lower hδnonneg hlowω
    exact le_trans hmain (by linarith)

theorem egorovClip_mem_LinftyClaims
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hSolid : Solid μ C0)
    {A : Set Ω} (hA : MeasurableSet A)
    {gseq : ℕ → Ω → ℝ} {δ : ℕ → ℝ} {n : ℕ}
    (hδnonneg : 0 ≤ δ n)
    (hgseqMem : ∀ n, gseq n ∈ C0)
    (hgseqMeas : ∀ n, AEStronglyMeasurable (gseq n) μ)
    (hlower : AELowerBoundedBy μ (-(δ n)) (gseq n)) :
    (egorovClip_memLp_top (μ := μ) (A := A) hA
      (gseq := gseq) (δ := δ) (n := n)
      hδnonneg hgseqMeas hlower).toLp (egorovClip A gseq n) ∈
        LinftyClaims μ C0 :=
  ⟨egorovClip A gseq n,
    egorovClip_mem_of_solid (μ := μ) hSolid hgseqMem n,
    egorovClip_memLp_top (μ := μ) (A := A) hA
      (gseq := gseq) (δ := δ) (n := n)
      hδnonneg hgseqMeas hlower,
    rfl⟩

theorem egorovClip_tendsto_linfy
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {gseq : ℕ → Ω → ℝ} {g : Ω → ℝ} {δ : ℕ → ℝ}
    (hδnonneg : ∀ n, 0 ≤ δ n)
    (hgseqMeas : ∀ n, AEStronglyMeasurable (gseq n) μ)
    (hgMeas : AEStronglyMeasurable g μ)
    (hlower : ∀ n, AELowerBoundedBy μ (-(δ n)) (gseq n))
    (hδtendsto : Tendsto δ atTop (nhds 0))
    (hgnonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1)
    (hunif : TendstoUniformlyOn gseq g atTop A) :
    Tendsto
      (fun n => (egorovClip_memLp_top (μ := μ) (A := A) hA
        (gseq := gseq) (δ := δ) (n := n)
        (hδnonneg n) hgseqMeas (hlower n)).toLp (egorovClip A gseq n))
      atTop
      (nhds ((egorovLimit_memLp_top (μ := μ) (A := A) hA
        (g := g) hgMeas hgnonneg hgle_one).toLp (egorovLimit A g))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hunif' := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / 2) hhalf
  rw [Metric.tendsto_atTop] at hδtendsto
  rcases hδtendsto (ε / 2) hhalf with ⟨Nδ, hNδ⟩
  rcases eventually_atTop.1 hunif' with ⟨Nu, hNu⟩
  refine ⟨max Nδ Nu, ?_⟩
  intro n hn
  have hnδ : Nδ ≤ n := le_trans (le_max_left _ _) hn
  have hnu : Nu ≤ n := le_trans (le_max_right _ _) hn
  have hδlt : δ n < ε / 2 := by
    have hdist := hNδ n hnδ
    rw [Real.dist_eq] at hdist
    have habs : |δ n| < ε / 2 := by simpa using hdist
    exact lt_of_le_of_lt (le_abs_self (δ n)) habs
  have hclose : ∀ ω ∈ A, |gseq n ω - g ω| ≤ ε / 2 := by
    intro ω hωA
    have hdist := hNu n hnu ω hωA
    rw [Real.dist_eq] at hdist
    exact le_of_lt (by simpa [abs_sub_comm] using hdist)
  have hdist_le := Linfty.dist_toLp_le_of_ae_abs_sub_le
    (egorovClip_memLp_top (μ := μ) (A := A) hA
      (gseq := gseq) (δ := δ) (n := n)
      (hδnonneg n) hgseqMeas (hlower n))
    (egorovLimit_memLp_top (μ := μ) (A := A) hA
      (g := g) hgMeas hgnonneg hgle_one)
    (add_nonneg (le_of_lt hhalf) (hδnonneg n))
    (egorovClip_ae_abs_sub_limit_le (μ := μ) (A := A)
      (gseq := gseq) (g := g) (δ := δ) (n := n) (ε := ε / 2)
      (by linarith) (hδnonneg n) hclose (hlower n) hgle_one)
  exact lt_of_le_of_lt hdist_le (by linarith)

theorem egorovVanishingRiskToLinftyNormLimit_core
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hSolid : Solid μ C0)
    {gseq : ℕ → Ω → ℝ} {g : Ω → ℝ} {δ : ℕ → ℝ}
    (hgseqMem : ∀ n, gseq n ∈ C0)
    (hδnonneg : ∀ n, 0 ≤ δ n)
    (hgseqStrong : ∀ n, StronglyMeasurable (gseq n))
    (hgStrong : StronglyMeasurable g)
    (hlower : ∀ n, AELowerBoundedBy μ (-(δ n)) (gseq n))
    (hδtendsto : Tendsto δ atTop (nhds 0))
    (hlim : TendstoAE μ gseq g)
    (hgnonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1)
    (hgpos : 0 < μ {ω | 0 < g ω}) :
    ∃ U : ℕ → Linfty (Ω := Ω) μ,
      ∃ F : Linfty (Ω := Ω) μ,
        (∀ n, U n ∈ LinftyClaims μ C0) ∧
        Tendsto U atTop (nhds F) ∧
        F ∈ LinftyNonnegative μ ∧
        F ≠ 0 := by
  rcases exists_pos_level_measure_pos (μ := μ) (g := g) hgpos with
    ⟨c, hcpos, hcμpos⟩
  rcases egorov_exists_positive_uniform_set (μ := μ)
      (gseq := gseq) (g := g) (c := c)
      hgseqStrong hgStrong hlim hcμpos with
    ⟨A, hAsub, hAmeas, hApos, hAunif⟩
  let U : ℕ → Linfty (Ω := Ω) μ := fun n =>
    (egorovClip_memLp_top (μ := μ) (A := A) hAmeas
      (gseq := gseq) (δ := δ) (n := n)
      (hδnonneg n)
      (fun k => (hgseqStrong k).aestronglyMeasurable)
      (hlower n)).toLp (egorovClip A gseq n)
  let hFLp : MemLp (egorovLimit A g) ⊤ μ :=
    egorovLimit_memLp_top (μ := μ) (A := A) hAmeas
      (g := g) hgStrong.aestronglyMeasurable hgnonneg hgle_one
  let F : Linfty (Ω := Ω) μ := hFLp.toLp (egorovLimit A g)
  refine ⟨U, F, ?_, ?_, ?_, ?_⟩
  · intro n
    exact egorovClip_mem_LinftyClaims (μ := μ) hSolid hAmeas
      (gseq := gseq) (δ := δ) (n := n)
      (hδnonneg n) hgseqMem
      (fun k => (hgseqStrong k).aestronglyMeasurable)
      (hlower n)
  · exact egorovClip_tendsto_linfy (μ := μ) hAmeas
      (gseq := gseq) (g := g) (δ := δ)
      hδnonneg
      (fun k => (hgseqStrong k).aestronglyMeasurable)
      hgStrong.aestronglyMeasurable
      hlower hδtendsto hgnonneg hgle_one hAunif
  · filter_upwards [MemLp.coeFn_toLp hFLp, hgnonneg] with ω hFω hg0ω
    rw [hFω]
    by_cases hωA : ω ∈ A
    · rw [egorovLimit, Set.indicator_of_mem hωA]
      exact hg0ω
    · rw [egorovLimit, Set.indicator_of_notMem hωA]
  · exact egorovLimit_toLp_ne_zero (μ := μ) hAmeas
      (g := g) (c := c) hcpos hApos hAsub
      hgStrong.aestronglyMeasurable hgnonneg hgle_one

/--
The analytic part left after positive-tail truncation.  It starts from claims
already in `C0`, whose downside risk vanishes while a fixed positive-mass set
stays above `1/2`, and returns the `L∞` free-lunch certificate.
-/
def VanishingRiskPositiveMassSequenceProducesLinftyLimit
    (μ : Measure Ω) (C0 : Set (Ω → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ f : ℕ → Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, f n ∈ C0) →
          (∀ n, AEStronglyMeasurable (f n) μ) →
            (∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) →
              (∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) →
                Antitone δ →
                  Tendsto δ atTop (nhds 0) →
                    (∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) →
                      ∃ U : ℕ → Linfty (Ω := Ω) μ,
                        ∃ F : Linfty (Ω := Ω) μ,
                          (∀ n, U n ∈ LinftyClaims μ C0) ∧
                          Tendsto U atTop (nhds F) ∧
                          F ∈ LinftyNonnegative μ ∧
                          F ≠ 0

end FTAPTheorem42
