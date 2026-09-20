import FTAPTheorem42.Core.Extraction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closedness, L-infinity claims, and NFLVR interfaces

This file contains the forward-convex closedness interfaces, `L∞` claim set,
NFLVR, and free-lunch certificate abstractions.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
The following interface is deliberately stated for raw functions.  It uses
mathlib's `TendstoInMeasure` directly, so a set can choose whether its
members carry measurability proofs.  The finite-measure bridges below are the
discharge lemmas for the common a.e.-convergence formulation.
-/

/-- Sequential closedness of a raw function set under convergence in measure. -/
def SequentiallyClosedInMeasure
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ),
    (∀ n, f n ∈ D) →
      MeasureTheory.TendstoInMeasure μ f atTop g →
        g ∈ D

/-- A raw function set is saturated under equality almost everywhere. -/
def AESaturated
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f g : Ω → ℝ⦄, f ∈ D → f =ᵐ[μ] g → g ∈ D

theorem Solid.aesaturated
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : Solid μ D) :
    AESaturated μ D := by
  intro f g hf hfg
  apply hD hf
  filter_upwards [hfg] with ω hω
  exact le_of_eq hω.symm

theorem FatouClosed.mem_of_tendstoAE_of_uniform_lower_bound
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hFatou : FatouClosed μ D)
    (hsmul : PosSMulInvariant D)
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {b : ℝ}
    (hb : 0 < b)
    (hfD : ∀ n, f n ∈ D)
    (hbound : ∀ n, AELowerBoundedBy μ (-b) (f n))
    (hlim : TendstoAE μ f g) :
    g ∈ D := by
  let a : ℝ := b⁻¹
  have ha : 0 < a := inv_pos.mpr hb
  have hafD : ∀ n, (fun ω => a * f n ω) ∈ D := by
    intro n
    exact hsmul ha (hfD n)
  have habound :
      ∀ n, AELowerBoundedBy μ (-1) (fun ω => a * f n ω) := by
    intro n
    filter_upwards [hbound n] with ω hω
    have hscaled := mul_le_mul_of_nonneg_left hω ha.le
    have hab : a * b = 1 := by
      dsimp [a]
      exact inv_mul_cancel₀ hb.ne'
    linarith
  have halim :
      TendstoAE μ (fun n ω => a * f n ω) (fun ω => a * g ω) := by
    filter_upwards [hlim] with ω hω
    exact hω.const_mul a
  have hagD : (fun ω => a * g ω) ∈ D :=
    hFatou hafD habound halim
  have hrescaled : (fun ω => b * (a * g ω)) ∈ D :=
    hsmul hb hagD
  convert hrescaled using 1
  funext ω
  dsimp [a]
  field_simp [hb.ne']

/-- The strongly measurable representatives contained in a raw function set. -/
def StronglyMeasurablePart (D : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {f | f ∈ D ∧ StronglyMeasurable f}

/-- Sequential closedness in measure, restricted to strongly measurable limits. -/
def SequentiallyClosedInMeasureOnStrongLimits
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ),
    (∀ n, f n ∈ D) →
      StronglyMeasurable g →
        MeasureTheory.TendstoInMeasure μ f atTop g →
          g ∈ D

theorem SequentiallyClosedInMeasure.onStrongLimits
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : SequentiallyClosedInMeasure μ D) :
    SequentiallyClosedInMeasureOnStrongLimits μ D := by
  intro f g hf _hg hfg
  exact hD f g hf hfg

theorem stronglyMeasurablePart_subset
    {D : Set (Ω → ℝ)} :
    StronglyMeasurablePart D ⊆ D := by
  intro f hf
  exact hf.1

theorem claimSetStronglyMeasurable_stronglyMeasurablePart
    {D : Set (Ω → ℝ)} :
    ClaimSetStronglyMeasurable (StronglyMeasurablePart D) := by
  intro f hf
  exact hf.2

theorem ConvexInvariant.stronglyMeasurablePart
    {D : Set (Ω → ℝ)} (hD : ConvexInvariant D) :
    ConvexInvariant (StronglyMeasurablePart D) := by
  intro a b ha hb hab f g hf hg
  refine ⟨hD ha hb hab hf.1 hg.1, ?_⟩
  exact (hf.2.const_mul a).add (hg.2.const_mul b)

theorem ClaimSetBoundedInProbability.stronglyMeasurablePart
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : ClaimSetBoundedInProbability μ D) :
    ClaimSetBoundedInProbability μ (StronglyMeasurablePart D) :=
  hD.mono stronglyMeasurablePart_subset

theorem SequentiallyClosedInMeasureOnStrongLimits.stronglyMeasurablePart
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : SequentiallyClosedInMeasureOnStrongLimits μ D) :
    SequentiallyClosedInMeasureOnStrongLimits μ (StronglyMeasurablePart D) := by
  intro f g hf hg hfg
  exact ⟨hD f g (fun n => (hf n).1) hg hfg, hg⟩

/-- The one-step sequential closure of a raw claim set for convergence in measure. -/
def InMeasureSequentialClosure
    (μ : Measure Ω) (K : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {g | ∃ f : ℕ → Ω → ℝ,
      (∀ n, f n ∈ K) ∧ MeasureTheory.TendstoInMeasure μ f atTop g}

theorem tendstoInMeasure_const
    (μ : Measure Ω) (g : Ω → ℝ) :
    MeasureTheory.TendstoInMeasure μ (fun _ : ℕ => g) atTop g := by
  intro ε hε
  have hset : {x : Ω | ε ≤ edist (g x) (g x)} = (∅ : Set Ω) := by
    ext x
    constructor
    · intro hx
      change ε ≤ edist (g x) (g x) at hx
      exact (not_le_of_gt hε) (by simpa only [edist_self] using hx)
    · intro hx
      exact hx.elim
  have hzero :
      (fun i : ℕ => μ {x | ε ≤ edist ((fun _ : ℕ => g) i x) (g x)}) =
        (fun _ => 0) := by
    funext i
    simp only [hset, measure_empty]
  rw [hzero]
  exact tendsto_const_nhds

theorem subset_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)} :
    K ⊆ InMeasureSequentialClosure μ K := by
  intro g hg
  exact ⟨fun _ => g, fun _ => hg, tendstoInMeasure_const μ g⟩

theorem aesaturated_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)} :
    AESaturated μ (InMeasureSequentialClosure μ K) := by
  intro g g' hg hgg'
  rcases hg with ⟨f, hf, hfg⟩
  exact ⟨f, hf, hfg.congr_right hgg'⟩

/-!
### Diagonalization for convergence in measure

The quotient/topological construction of convergence in measure is not part of
mathlib's `AEEqFun` API.  The following direct diagonal lemma is therefore the
raw-function closure interface: it selects one term from each inner sequence,
using an error threshold which tends to zero, and proves convergence by the
triangle inequality and a union bound.
-/

theorem tendstoInMeasure_diagonal
    {μ : Measure Ω} {K : Set (Ω → ℝ)}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hfg : MeasureTheory.TendstoInMeasure μ f atTop g)
    (hinner : ∀ n, ∃ u : ℕ → Ω → ℝ,
      (∀ k, u k ∈ K) ∧
        MeasureTheory.TendstoInMeasure μ u atTop (f n)) :
    ∃ v : ℕ → Ω → ℝ,
      (∀ n, v n ∈ K) ∧ MeasureTheory.TendstoInMeasure μ v atTop g := by
  let ρ : ℕ → ENNReal := fun n => (n : ENNReal)⁻¹
  have hρ_pos : ∀ n, 0 < ρ n := by
    intro n
    dsimp [ρ]
    exact ENNReal.inv_pos.mpr (by finiteness)
  have hρ_tendsto : Tendsto ρ atTop (nhds 0) := by
    simpa [ρ] using ENNReal.tendsto_inv_nat_nhds_zero
  choose u hu h_u using hinner
  have hselect : ∀ n, ∃ k : ℕ,
      μ {ω | ρ n ≤ edist (u n k ω) (f n ω)} ≤ ρ n := by
    intro n
    have hconv := h_u n (ρ n) (hρ_pos n)
    rw [ENNReal.tendsto_atTop_zero] at hconv
    obtain ⟨N, hN⟩ := hconv (ρ n) (hρ_pos n)
    exact ⟨N, hN N le_rfl⟩
  choose κ hκ using hselect
  let v : ℕ → Ω → ℝ := fun n => u n (κ n)
  have hv_mem : ∀ n, v n ∈ K := by
    intro n
    exact hu n (κ n)
  refine ⟨v, hv_mem, ?_⟩
  intro ε hε
  have hεhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hρ_zero := (ENNReal.tendsto_atTop_zero.mp hρ_tendsto)
  obtain ⟨Nε, hNε⟩ := hρ_zero (ε / 2) hεhalf
  obtain ⟨Nδ, hNδ⟩ := hρ_zero (δ / 2) hδhalf
  have hfg_zero := ENNReal.tendsto_atTop_zero.mp (hfg (ε / 2) hεhalf)
  obtain ⟨Nfg, hNfg⟩ := hfg_zero (δ / 2) hδhalf
  refine ⟨max (max Nε Nδ) Nfg, ?_⟩
  intro n hn
  have hnε : Nε ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnδ : Nδ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hnfg : Nfg ≤ n := le_trans (le_max_right _ _) hn
  have hρeps : ρ n ≤ ε / 2 := hNε n hnε
  have hρdelta : ρ n ≤ δ / 2 := hNδ n hnδ
  have hinner_bound :
      μ {ω | ε / 2 ≤ edist (v n ω) (f n ω)} ≤ δ / 2 := by
    calc
      μ {ω | ε / 2 ≤ edist (v n ω) (f n ω)} ≤
          μ {ω | ρ n ≤ edist (v n ω) (f n ω)} := by
            apply measure_mono
            intro ω hω
            exact le_trans hρeps hω
      _ ≤ ρ n := by simpa [v] using hκ n
      _ ≤ δ / 2 := hρdelta
  have hset_union :
      {ω | ε ≤ edist (v n ω) (g ω)} ⊆
        {ω | ε / 2 ≤ edist (v n ω) (f n ω)} ∪
          {ω | ε / 2 ≤ edist (f n ω) (g ω)} := by
    intro ω hω
    by_cases hleft : ε / 2 ≤ edist (v n ω) (f n ω)
    · exact Or.inl hleft
    · right
      by_contra hright
      have hleft' : edist (v n ω) (f n ω) < ε / 2 := lt_of_not_ge hleft
      have hright' : edist (f n ω) (g ω) < ε / 2 := lt_of_not_ge hright
      have hsum :
          edist (v n ω) (f n ω) + edist (f n ω) (g ω) < ε := by
        calc
          edist (v n ω) (f n ω) + edist (f n ω) (g ω) <
              ε / 2 + ε / 2 := ENNReal.add_lt_add hleft' hright'
          _ = ε := ENNReal.add_halves ε
      exact False.elim ((not_lt_of_ge
        (le_trans hω (edist_triangle (v n ω) (f n ω) (g ω)))) hsum)
  calc
    μ {ω | ε ≤ edist (v n ω) (g ω)} ≤
        μ ({ω | ε / 2 ≤ edist (v n ω) (f n ω)} ∪
          {ω | ε / 2 ≤ edist (f n ω) (g ω)}) := measure_mono hset_union
    _ ≤ μ {ω | ε / 2 ≤ edist (v n ω) (f n ω)} +
          μ {ω | ε / 2 ≤ edist (f n ω) (g ω)} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hinner_bound (hNfg n hnfg)
    _ = δ := ENNReal.add_halves δ

theorem sequentiallyClosedInMeasure_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)} :
    SequentiallyClosedInMeasure μ (InMeasureSequentialClosure μ K) := by
  intro f g hf hfg
  choose u hu h_u using hf
  obtain ⟨v, hv, hvg⟩ := tendstoInMeasure_diagonal hfg (fun n => ⟨u n, hu n, h_u n⟩)
  exact ⟨v, hv, hvg⟩

theorem claimSetAEStronglyMeasurable_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)}
    (hK : ClaimSetAEStronglyMeasurable μ K) :
    ClaimSetAEStronglyMeasurable μ (InMeasureSequentialClosure μ K) := by
  intro g hg
  rcases hg with ⟨f, hf, hfg⟩
  exact MeasureTheory.TendstoInMeasure.aestronglyMeasurable
    (fun n => hK (f n) (hf n)) hfg

theorem tendstoInMeasure_add
    {μ : Measure Ω} {f f' : ℕ → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : MeasureTheory.TendstoInMeasure μ f atTop g)
    (hf' : MeasureTheory.TendstoInMeasure μ f' atTop g') :
    MeasureTheory.TendstoInMeasure μ
      (fun n ω => f n ω + f' n ω) atTop (fun ω => g ω + g' ω) := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hf_zero := ENNReal.tendsto_atTop_zero.mp (hf (ε / 2) hεhalf)
  have hf'_zero := ENNReal.tendsto_atTop_zero.mp (hf' (ε / 2) hεhalf)
  obtain ⟨N, hN⟩ := hf_zero (δ / 2) hδhalf
  obtain ⟨N', hN'⟩ := hf'_zero (δ / 2) hδhalf
  refine ⟨max N N', ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
  have hset_union :
      {ω | ε ≤ edist (f n ω + f' n ω) (g ω + g' ω)} ⊆
        {ω | ε / 2 ≤ edist (f n ω) (g ω)} ∪
          {ω | ε / 2 ≤ edist (f' n ω) (g' ω)} := by
    intro ω hω
    by_cases hleft : ε / 2 ≤ edist (f n ω) (g ω)
    · exact Or.inl hleft
    · right
      by_contra hright
      have hleft' : edist (f n ω) (g ω) < ε / 2 := lt_of_not_ge hleft
      have hright' : edist (f' n ω) (g' ω) < ε / 2 := lt_of_not_ge hright
      have hsum :
          edist (f n ω) (g ω) + edist (f' n ω) (g' ω) < ε := by
        calc
          edist (f n ω) (g ω) + edist (f' n ω) (g' ω) <
              ε / 2 + ε / 2 := ENNReal.add_lt_add hleft' hright'
          _ = ε := ENNReal.add_halves ε
      exact False.elim ((not_lt_of_ge
        (le_trans hω (edist_add_add_le (f n ω) (f' n ω) (g ω) (g' ω)))) hsum)
  calc
    μ {ω | ε ≤ edist (f n ω + f' n ω) (g ω + g' ω)} ≤
        μ ({ω | ε / 2 ≤ edist (f n ω) (g ω)} ∪
          {ω | ε / 2 ≤ edist (f' n ω) (g' ω)}) := measure_mono hset_union
    _ ≤ μ {ω | ε / 2 ≤ edist (f n ω) (g ω)} +
          μ {ω | ε / 2 ≤ edist (f' n ω) (g' ω)} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hN n hnN) (hN' n hnN')
    _ = δ := ENNReal.add_halves δ

theorem tendstoInMeasure_smul_const
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (c : ℝ)
    (hf : MeasureTheory.TendstoInMeasure μ f atTop g) :
    MeasureTheory.TendstoInMeasure μ
      (fun n ω => c * f n ω) atTop (fun ω => c * g ω) := by
  by_cases hc : c = 0
  · subst c
    simpa using (tendstoInMeasure_const μ (fun _ : Ω => 0))
  let q : ENNReal := (‖c‖₊ : ENNReal)
  have hq_pos : 0 < q := by
    dsimp [q]
    exact ENNReal.coe_pos.mpr (norm_pos_iff.mpr hc)
  have hq_top : q ≠ ⊤ := by
    dsimp [q]
    finiteness
  intro ε hε
  have hεq : 0 < ε / q := ENNReal.div_pos hε.ne' hq_top
  have hinner := ENNReal.tendsto_atTop_zero.mp (hf (ε / q) hεq)
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  obtain ⟨N, hN⟩ := hinner δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  calc
    μ {ω | ε ≤ edist (c * f n ω) (c * g ω)} ≤
        μ {ω | ε / q ≤ edist (f n ω) (g ω)} := by
      apply measure_mono
      intro ω hω
      apply ENNReal.div_le_of_le_mul'
      calc
        ε ≤ edist (c * f n ω) (c * g ω) := hω
        _ ≤ q * edist (f n ω) (g ω) := by
          simpa only [q, ENNReal.smul_def, smul_eq_mul] using
            edist_smul_le c (f n ω) (g ω)
    _ ≤ δ := hN n hn

theorem tendstoInMeasure_affine
    {μ : Measure Ω} {f f' : ℕ → Ω → ℝ} {g g' : Ω → ℝ}
    {a b : ℝ}
    (hf : MeasureTheory.TendstoInMeasure μ f atTop g)
    (hf' : MeasureTheory.TendstoInMeasure μ f' atTop g') :
    MeasureTheory.TendstoInMeasure μ
      (fun n ω => a * f n ω + b * f' n ω) atTop
      (fun ω => a * g ω + b * g' ω) := by
  have hfa := tendstoInMeasure_smul_const a hf
  have hfb := tendstoInMeasure_smul_const b hf'
  simpa [smul_eq_mul] using tendstoInMeasure_add hfa hfb

theorem convexInvariant_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)}
    (hK : ConvexInvariant K) :
    ConvexInvariant (InMeasureSequentialClosure μ K) := by
  intro a b ha hb hab f g hf hg
  rcases hf with ⟨u, hu, huf⟩
  rcases hg with ⟨v, hv, hvg⟩
  refine ⟨fun n ω => a * u n ω + b * v n ω, ?_, ?_⟩
  · intro n
    exact hK ha hb hab (hu n) (hv n)
  · exact tendstoInMeasure_affine huf hvg

theorem claimSetBoundedInProbability_inMeasureSequentialClosure
    {μ : Measure Ω} {K : Set (Ω → ℝ)}
    (hK : ClaimSetBoundedInProbability μ K) :
    ClaimSetBoundedInProbability μ (InMeasureSequentialClosure μ K) := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  rcases hK (ε / 2) hεhalf with ⟨R, hR, hRtail⟩
  refine ⟨R + 1, by linarith, ?_⟩
  intro g hg
  rcases hg with ⟨f, hf, hfg⟩
  have hconv := hfg (1 : ENNReal) (by norm_num)
  rw [ENNReal.tendsto_atTop_zero] at hconv
  obtain ⟨N, hN⟩ := hconv (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr hεhalf)
  have hsubset :
      {ω | R + 1 < |g ω|} ⊆
        {ω | R < |f N ω|} ∪
          {ω | (1 : ENNReal) ≤ edist (f N ω) (g ω)} := by
    intro ω hω
    by_cases hlarge : R < |f N ω|
    · exact Or.inl hlarge
    · right
      by_contra hdist
      have hdistlt : edist (f N ω) (g ω) < 1 := lt_of_not_ge hdist
      have hdistreal : dist (f N ω) (g ω) < 1 := by
        rw [edist_dist] at hdistlt
        apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp
        simpa using hdistlt
      have hdiff : |g ω - f N ω| < 1 := by
        rw [abs_sub_comm]
        simpa [Real.dist_eq] using hdistreal
      have hfabs : |f N ω| ≤ R := le_of_not_gt hlarge
      have hupper : |g ω| < R + 1 := by
        calc
          |g ω| ≤ |g ω - f N ω| + |f N ω| := by
            simpa using abs_sub_le (g ω) (f N ω) 0
          _ < 1 + R := add_lt_add_of_lt_of_le hdiff hfabs
          _ = R + 1 := by ring
      exact False.elim ((not_lt_of_ge (le_of_lt hω)) hupper)
  calc
    μ {ω | R + 1 < |g ω|} ≤
        μ ({ω | R < |f N ω|} ∪
          {ω | (1 : ENNReal) ≤ edist (f N ω) (g ω)}) := measure_mono hsubset
    _ ≤ μ {ω | R < |f N ω|} +
          μ {ω | (1 : ENNReal) ≤ edist (f N ω) (g ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hRtail (f N) (hf N)) (hN N le_rfl)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A.e. convergence of an AEStronglyMeasurable sequence implies convergence in measure. -/
theorem tendstoInMeasure_of_tendstoAE
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : TendstoAE μ f g) :
    MeasureTheory.TendstoInMeasure μ f atTop g := by
  simpa [TendstoAE] using
    (MeasureTheory.tendstoInMeasure_of_tendsto_ae
      (μ := μ) (f := f) (g := g) hf hfg)

/-- Strong measurability is enough for the finite-measure a.e.-to-measure bridge. -/
theorem tendstoInMeasure_of_stronglyMeasurable_tendstoAE
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n))
    (hfg : TendstoAE μ f g) :
    MeasureTheory.TendstoInMeasure μ f atTop g :=
  tendstoInMeasure_of_tendstoAE (μ := μ)
    (fun n => (hf n).aestronglyMeasurable) hfg

/-- The a.e. upper section of a raw claim set at a lower function `u`. -/
def AEUpperSection
    (μ : Measure Ω) (D : Set (Ω → ℝ)) (u : Ω → ℝ) : Set (Ω → ℝ) :=
  {h | h ∈ D ∧ AEDominatedBy μ u h}

/-- Convexity is inherited by an a.e. upper section. -/
theorem ConvexInvariant.aeUpperSection
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {u : Ω → ℝ}
    (hD : ConvexInvariant D) :
    ConvexInvariant (AEUpperSection μ D u) := by
  intro a b ha hb hab f g hf hg
  refine ⟨hD ha hb hab hf.1 hg.1, ?_⟩
  filter_upwards [hf.2, hg.2] with ω hfu hgu
  calc
    u ω = 1 * u ω := by ring
    _ = (a + b) * u ω := by rw [hab]
    _ = a * u ω + b * u ω := by ring
    _ ≤ a * f ω + b * g ω := add_le_add
      (mul_le_mul_of_nonneg_left hfu ha)
      (mul_le_mul_of_nonneg_left hgu hb)

/--
Fatou upper bounds can be reduced from the terminal-gain cone `K0` to a
smaller source class `Ksrc`, typically the `1`-admissible terminal gains.
-/
def FatouUpperBoundsReducible
    (μ : Measure Ω) (K0 Ksrc : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f : ℕ → Ω → ℝ⦄ ⦃G : ℕ → Ω → ℝ⦄,
    (∀ n, G n ∈ K0) →
    (∀ n, AEDominatedBy μ (f n) (G n)) →
    (∀ n, AELowerBoundedBy μ (-1) (f n)) →
      ∃ Gsrc : ℕ → Ω → ℝ,
        (∀ n, Gsrc n ∈ Ksrc) ∧
        ∀ n, AEDominatedBy μ (f n) (Gsrc n)

/--
Every a.e. forward-convex limit from the source class is dominated a.e.
by a representative in the target class. This domination condition supplies
the upper bound needed for Fatou stability.
-/
def ForwardConvexLimitAEDominatedBetween
    (μ : Measure Ω) (Ksrc Kdst : Set (Ω → ℝ)) : Prop :=
  ∀ G : ℕ → Ω → ℝ,
    (∀ n, G n ∈ Ksrc) →
      ∀ W : ForwardConvexWeights, ∀ G_lim,
        TendstoAE μ (W.apply G) G_lim →
          ∃ G_rep ∈ Kdst, AEDominatedBy μ G_lim G_rep

/--
The maximal-limit realization boundary for a source set.  It only asks for
a.e. representatives of maximal points in the in-measure sequential closure;
it does not assert realization of arbitrary forward-convex limits.
-/
def MaximalInMeasureClosureAERealizableBetween
    (μ : Measure Ω) (Ksrc Kdst : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃h : Ω → ℝ⦄,
    h ∈ InMeasureSequentialClosure μ Ksrc →
      AEMaximalIn μ (InMeasureSequentialClosure μ Ksrc) h →
        ∃ G_rep ∈ Kdst, h =ᵐ[μ] G_rep

/--
Fatou stability follows by reducing terminal upper bounds to the source
class, extracting an a.e. forward-convex limit, and dominating that limit
by a representative in the terminal-gain cone.
-/
theorem TerminalGainFatouStable.of_reducible_candidate_dominatedBetween
    {μ : Measure Ω} {K0 Ksrc : Set (Ω → ℝ)}
    (hReduce : FatouUpperBoundsReducible μ K0 Ksrc)
    (hCandidate : TerminalGainHasAEForwardConvexCandidate μ Ksrc)
    (hDominated : ForwardConvexLimitAEDominatedBetween μ Ksrc K0) :
    TerminalGainFatouStable μ K0 := by
  intro f g G hG hdom hlower hlim
  rcases hReduce hG hdom hlower with ⟨Gsrc, hGsrc, hdomsrc⟩
  rcases hCandidate Gsrc hGsrc with ⟨W, G_lim, hGlim⟩
  rcases hDominated Gsrc hGsrc W G_lim hGlim with
    ⟨G_rep, hGrep_mem, hGlim_dom⟩
  refine ⟨G_rep, hGrep_mem, ?_⟩
  have hg_le_Glim : AEDominatedBy μ g G_lim := by
    apply AEDominatedBy.limit
    · exact W.preservesTendstoAE μ hlim
    · exact hGlim
    · intro n
      exact W.apply_dominated hdomsrc n
  exact AEDominatedBy.trans hg_le_Glim hGlim_dom

theorem fatouClosed_C0FromTerminalGains_of_terminalGainFatouStable
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hStable : TerminalGainFatouStable μ K0) :
    FatouClosed μ (C0FromTerminalGains μ K0) := by
  intro f g hf hbound hlim
  choose G hGmem hdom using hf
  exact hStable hGmem hdom hbound hlim

theorem fatouClosed_C0AsDifference_of_terminalGainFatouStable
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hStable : TerminalGainFatouStable μ K0) :
    FatouClosed μ (C0AsDifference μ K0) := by
  simpa [C0AsDifference_eq_C0FromTerminalGains μ K0] using
    fatouClosed_C0FromTerminalGains_of_terminalGainFatouStable
      (μ := μ) (K0 := K0) hStable

/--
The bounded part of a set of raw claims, transported to mathlib's `L∞`.
This is the concrete Lean counterpart of the README notation `D ∩ L∞`.
-/
def LinftyClaims (μ : Measure Ω) (D : Set (Ω → ℝ)) :
    Set (Linfty (Ω := Ω) μ) :=
  { F | ∃ f ∈ D, ∃ hf : MemLp f ⊤ μ, hf.toLp f = F }

theorem LinftyClaims_convex
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD : Convex ℝ D) :
    Convex ℝ (LinftyClaims μ D) := by
  intro F hF G hG a b ha hb hab
  rcases hF with ⟨f, hfD, hfLp, rfl⟩
  rcases hG with ⟨g, hgD, hgLp, rfl⟩
  let hAf : MemLp (a • f) ⊤ μ := hfLp.const_smul a
  let hBg : MemLp (b • g) ⊤ μ := hgLp.const_smul b
  let hAB : MemLp (a • f + b • g) ⊤ μ := hAf.add hBg
  refine ⟨a • f + b • g, hD hfD hgD ha hb hab, hAB, ?_⟩
  calc
    hAB.toLp (a • f + b • g)
        = hAf.toLp (a • f) + hBg.toLp (b • g) := MemLp.toLp_add hAf hBg
    _ = a • hfLp.toLp f + b • hgLp.toLp g := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]

/-- The nonnegative cone in the concrete `L∞(μ)` model. -/
def LinftyNonnegative (μ : Measure Ω) : Set (Linfty (Ω := Ω) μ) :=
  { F | ∀ᵐ ω ∂μ, 0 ≤ F ω }

/--
The concrete `L∞` form of NFLVR:
the norm closure of bounded attainable claims has no nonzero nonnegative claim.
-/
def LinftyNFLVR
    (μ : Measure Ω) (C : Set (Linfty (Ω := Ω) μ)) : Prop :=
  closure C ∩ LinftyNonnegative μ ⊆ ({0} : Set (Linfty (Ω := Ω) μ))

theorem linftyNFLVR_iff
    {μ : Measure Ω} {C : Set (Linfty (Ω := Ω) μ)} :
    LinftyNFLVR μ C ↔
      ∀ F, F ∈ closure C → F ∈ LinftyNonnegative μ → F = 0 := by
  constructor
  · intro hNFLVR F hFC hFpos
    have hF : F ∈ ({0} : Set (Linfty (Ω := Ω) μ)) := hNFLVR ⟨hFC, hFpos⟩
    simpa using hF
  · intro h F hF
    simpa using h F hF.1 hF.2

/--
Subset form of the unbounded-in-probability free-lunch step.  This is the
form used for uniformly `1`-admissible terminal gains: the unbounded class `D`
is a subset of the trading cone `K₀`, while the free lunch is produced in the
`L∞` closure of `C₀(K₀)`.
-/
def ClaimSubsetUnboundedInProbabilityProducesLinftyFreeLunch
    (μ : Measure Ω) (D K0 : Set (Ω → ℝ)) : Prop :=
  ¬ ClaimSetBoundedInProbability μ D →
    ∃ F : Linfty (Ω := Ω) μ,
      F ∈ closure (LinftyClaims μ (C0AsDifference μ K0)) ∧
      F ∈ LinftyNonnegative μ ∧
      F ≠ 0

end FTAPTheorem42
