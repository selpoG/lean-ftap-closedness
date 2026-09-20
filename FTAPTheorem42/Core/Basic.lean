import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Sequences

/-!
# Core abstractions for Delbaen--Schachermayer Theorem 4.2

This module contains the order, Fatou-closedness, `L∞`, NFLVR, forward-convex,
and bounded-in-probability interfaces used by the rest of the development.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/--
In a locally convex real topological vector space, a strongly closed convex set
is closed for the weak topology.  This is the abstract functional-analytic
mechanism behind the weak-star half of Theorem 4.2.
-/
theorem isClosed_toWeakSpace_image_of_isClosed_convex
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hsConvex : Convex ℝ s) (hsClosed : IsClosed s) :
    IsClosed ((toWeakSpace ℝ E) '' s : Set (WeakSpace ℝ E)) := by
  apply isClosed_of_closure_subset
  intro x hx
  have hclosure :=
    (hsConvex.toWeakSpace_closure (𝕜 := ℝ) :
      (toWeakSpace ℝ E) '' closure s =
        closure ((toWeakSpace ℝ E) '' s : Set (WeakSpace ℝ E)))
  rw [← hclosure] at hx
  rw [hsClosed.closure_eq] at hx
  exact hx

omit [MeasurableSpace Ω] in
/-- A sequential limit of points of a set lies in its topological closure. -/
theorem mem_closure_of_tendsto_atTop
    {E : Type*} [TopologicalSpace E] {s : Set E}
    {u : ℕ → E} {x : E}
    (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (nhds x)) :
    x ∈ closure s :=
  isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun n => subset_closure (hu n))

/-- The mathlib model of `L∞(μ)` as `Lp` with exponent `∞`. -/
abbrev Linfty (μ : Measure Ω) : Type _ :=
  MeasureTheory.Lp ℝ ⊤ μ

/-- A function is almost everywhere bounded below by a real constant. -/
def AELowerBoundedBy (μ : Measure Ω) (c : ℝ) (f : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, c ≤ f ω

theorem AELowerBoundedBy.mono_const
    {μ : Measure Ω} {c d : ℝ} {f : Ω → ℝ}
    (hcd : c ≤ d) (hf : AELowerBoundedBy μ d f) :
    AELowerBoundedBy μ c f := by
  filter_upwards [hf] with ω hω
  exact le_trans hcd hω

theorem Linfty.dist_toLp_le_of_ae_abs_sub_le
    {μ : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ C) :
    dist (hf.toLp f) (hg.toLp g) ≤ C := by
  have hnorm : ∀ᵐ ω ∂μ, ‖(f - g) ω‖ ≤ C := by
    filter_upwards [hbound] with ω hω
    simpa [Pi.sub_apply, Real.norm_eq_abs] using hω
  have hEss :
      eLpNorm (f - g) ⊤ μ ≤ ENNReal.ofReal C := by
    simpa [eLpNorm_exponent_top (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)] using
      eLpNormEssSup_le_of_ae_bound (μ := μ) (f := f - g) hnorm
  calc
    dist (hf.toLp f) (hg.toLp g)
        = (eLpNorm (f - g) ⊤ μ).toReal := by
          rw [MeasureTheory.Lp.dist_edist, MeasureTheory.Lp.edist_toLp_toLp]
    _ ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hEss
    _ = C := by rw [ENNReal.toReal_ofReal hC]

/-- Pointwise almost everywhere convergence of a sequence of real-valued functions. -/
def TendstoAE (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (nhds (g ω))

theorem TendstoAE.comp_strictMono
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hlim : TendstoAE μ f g) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoAE μ (fun n ω => f (φ n) ω) g := by
  filter_upwards [hlim] with ω hω
  simpa [Function.comp_def] using hω.comp hφ.tendsto_atTop

theorem TendstoAE.nonnegative_of_vanishing_lower
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {δ : ℕ → ℝ}
    (hlim : TendstoAE μ f g)
    (hδ : Tendsto δ atTop (nhds 0))
    (hlower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) :
    ∀ᵐ ω ∂μ, 0 ≤ g ω := by
  have hlower_all : ∀ᵐ ω ∂μ, ∀ n, -(δ n) ≤ f n ω := by
    exact ae_all_iff.mpr hlower
  filter_upwards [hlim, hlower_all] with ω hlimω hlowerω
  have hnegδ : Tendsto (fun n => -(δ n)) atTop (nhds 0) := by
    simpa using hδ.neg
  exact le_of_tendsto_of_tendsto hnegδ hlimω
    (Filter.Eventually.of_forall hlowerω)

/-- Almost everywhere pointwise domination. -/
def AEDominatedBy (μ : Measure Ω) (f g : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, f ω ≤ g ω

/--
An a.e.-maximal member of a claim set: any member of the set which dominates
it a.e. must agree with it a.e.  This is the raw-function maximality notion
used by the later upper-section/existence layer.
-/
def AEMaximalIn (μ : Measure Ω) (D : Set (Ω → ℝ)) (f : Ω → ℝ) : Prop :=
  f ∈ D ∧ ∀ g, g ∈ D → AEDominatedBy μ f g → g =ᵐ[μ] f

theorem AEDominatedBy.refl (μ : Measure Ω) (f : Ω → ℝ) :
    AEDominatedBy μ f f :=
  Filter.Eventually.of_forall (fun _ => le_rfl)

theorem AEDominatedBy.trans
    {μ : Measure Ω} {f g h : Ω → ℝ}
    (hfg : AEDominatedBy μ f g) (hgh : AEDominatedBy μ g h) :
    AEDominatedBy μ f h := by
  filter_upwards [hfg, hgh] with ω hfgω hghω
  exact le_trans hfgω hghω

theorem AEDominatedBy.limit_const
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g h : Ω → ℝ}
    (hlim : TendstoAE μ f g)
    (hdom : ∀ n, AEDominatedBy μ (f n) h) :
    AEDominatedBy μ g h := by
  have hdom_all : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ h ω := by
    exact ae_all_iff.mpr hdom
  filter_upwards [hlim, hdom_all] with ω hωlim hωdom
  exact le_of_tendsto_of_tendsto hωlim tendsto_const_nhds
    (Filter.Eventually.of_forall hωdom)

theorem AEDominatedBy.limit
    {μ : Measure Ω} {f g : ℕ → Ω → ℝ} {f_lim g_lim : Ω → ℝ}
    (hf : TendstoAE μ f f_lim)
    (hg : TendstoAE μ g g_lim)
    (hdom : ∀ n, AEDominatedBy μ (f n) (g n)) :
    AEDominatedBy μ f_lim g_lim := by
  have hdom_all : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ g n ω := by
    exact ae_all_iff.mpr hdom
  filter_upwards [hf, hg, hdom_all] with ω hfω hgω hdomω
  exact le_of_tendsto_of_tendsto hfω hgω
    (Filter.Eventually.of_forall hdomω)

/-- Almost everywhere nonnegativity. -/
def AENonnegative (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, 0 ≤ f ω

/-- Almost everywhere equality to a pointwise difference. -/
def AESub (μ : Measure Ω) (f g h : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, f ω = g ω - h ω

/--
The README's equivalent presentation of `C₀`: claims dominated almost
everywhere by some terminal gain in `K₀`.
-/
def C0FromTerminalGains (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  { f | ∃ g ∈ K0, AEDominatedBy μ f g }

/-- The downward hull of `K₀` on raw functions, expressed by a nonnegative
residual. No measurability is imposed here. On a.e.-strongly-measurable
claims and gains, `C0AsDifference_iff_measurable_residual` recovers `K₀ - L⁰₊`. -/
def C0AsDifference (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  { f | ∃ g ∈ K0, ∃ h, AENonnegative μ h ∧ AESub μ f g h }

theorem C0AsDifference_subset_C0FromTerminalGains
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} :
    C0AsDifference μ K0 ⊆ C0FromTerminalGains μ K0 := by
  intro f hf
  rcases hf with ⟨g, hg, h, hnonneg, hsub⟩
  refine ⟨g, hg, ?_⟩
  filter_upwards [hnonneg, hsub] with ω hnonnegω hsubω
  rw [hsubω]
  linarith

theorem C0FromTerminalGains_subset_C0AsDifference
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} :
    C0FromTerminalGains μ K0 ⊆ C0AsDifference μ K0 := by
  intro f hf
  rcases hf with ⟨g, hg, hfg⟩
  refine ⟨g, hg, fun ω => g ω - f ω, ?_, ?_⟩
  · filter_upwards [hfg] with ω hfgω
    linarith
  · exact Filter.Eventually.of_forall (fun ω => by ring)

/-- Restricting the raw downward hull to measurable claims recovers the usual
`K₀ - L⁰₊`: the residual can be chosen a.e. strongly measurable. -/
theorem C0AsDifference_iff_measurable_residual
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} {f : Ω → ℝ}
    (hK : ∀ g ∈ K0, AEStronglyMeasurable g μ)
    (hf : AEStronglyMeasurable f μ) :
    f ∈ C0AsDifference μ K0 ↔
      ∃ g ∈ K0, ∃ h, AEStronglyMeasurable h μ ∧
        AENonnegative μ h ∧ AESub μ f g h := by
  constructor
  · intro hmem
    obtain ⟨g, hg, hfg⟩ := C0AsDifference_subset_C0FromTerminalGains hmem
    refine ⟨g, hg, fun ω => g ω - f ω, (hK g hg).sub hf, ?_, ?_⟩
    · exact hfg.mono fun _ h => sub_nonneg.mpr h
    · exact Filter.Eventually.of_forall (fun ω => by ring)
  · rintro ⟨g, hg, h, _, hnonneg, hsub⟩
    exact ⟨g, hg, h, hnonneg, hsub⟩

theorem C0AsDifference_eq_C0FromTerminalGains
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) :
    C0AsDifference μ K0 = C0FromTerminalGains μ K0 := by
  ext f
  exact ⟨
    fun hf => C0AsDifference_subset_C0FromTerminalGains hf,
    fun hf => C0FromTerminalGains_subset_C0AsDifference hf⟩

theorem terminalGain_mem_C0FromTerminalGains
    (μ : Measure Ω) {K0 : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hg : g ∈ K0) :
    g ∈ C0FromTerminalGains μ K0 := by
  exact ⟨g, hg, Filter.Eventually.of_forall (fun _ => le_rfl)⟩

theorem C0FromTerminalGains_downward_closed
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)} {f h : Ω → ℝ}
    (hf : f ∈ C0FromTerminalGains μ K0)
    (hhf : AEDominatedBy μ h f) :
    h ∈ C0FromTerminalGains μ K0 := by
  rcases hf with ⟨g, hg, hfg⟩
  refine ⟨g, hg, ?_⟩
  filter_upwards [hhf, hfg] with ω hle hfg'
  exact le_trans hle hfg'

/-- A set of claims is solid: it contains every a.e. smaller claim. -/
def Solid (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f h : Ω → ℝ⦄, f ∈ D → AEDominatedBy μ h f → h ∈ D

theorem C0FromTerminalGains_solid
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) :
    Solid μ (C0FromTerminalGains μ K0) := by
  intro f h hf hhf
  exact C0FromTerminalGains_downward_closed hf hhf

theorem C0AsDifference_solid
    (μ : Measure Ω) (K0 : Set (Ω → ℝ)) :
    Solid μ (C0AsDifference μ K0) := by
  rw [C0AsDifference_eq_C0FromTerminalGains]
  exact C0FromTerminalGains_solid μ K0

/-- A set of claims contains the zero claim. -/
def HasZeroClaim (D : Set (Ω → ℝ)) : Prop :=
  (fun _ => 0) ∈ D

/-- A set of claims is closed under pointwise addition. -/
def AddInvariant (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f g : Ω → ℝ⦄, f ∈ D → g ∈ D → (fun ω => f ω + g ω) ∈ D

/-- Closure of a set of claims under multiplication by a strictly positive scalar. -/
def PosSMulInvariant (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃f : Ω → ℝ⦄, f ∈ D → (fun ω => c * f ω) ∈ D

/-- Closure of a set of claims under multiplication by a nonnegative scalar. -/
def NonnegSMulInvariant (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ ⦃f : Ω → ℝ⦄, f ∈ D → (fun ω => c * f ω) ∈ D

/-- Closure of a set of claims under pointwise convex combinations. -/
def ConvexInvariant (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃a b : ℝ⦄,
    0 ≤ a →
    0 ≤ b →
    a + b = 1 →
    ∀ ⦃f g : Ω → ℝ⦄,
      f ∈ D →
      g ∈ D →
      (fun ω => a * f ω + b * g ω) ∈ D

/-- A positive cone of claims, stated only with the operations needed here. -/
def ClaimCone (D : Set (Ω → ℝ)) : Prop :=
  HasZeroClaim D ∧ AddInvariant D ∧ PosSMulInvariant D

omit [MeasurableSpace Ω] in
theorem ClaimCone.nonnegSMulInvariant
    {D : Set (Ω → ℝ)}
    (hD : ClaimCone D) :
    NonnegSMulInvariant D := by
  intro c hc f hf
  rcases lt_or_eq_of_le hc with hcpos | rfl
  · exact hD.2.2 hcpos hf
  · have hzero : (fun ω => 0 * f ω) = (fun _ : Ω => 0) := by
      ext ω
      ring
    rw [hzero]
    exact hD.1

omit [MeasurableSpace Ω] in
theorem ClaimCone.convexInvariant
    {D : Set (Ω → ℝ)}
    (hD : ClaimCone D) :
    ConvexInvariant D := by
  intro a b ha hb _hsum f g hf hg
  exact hD.2.1
    (hD.nonnegSMulInvariant ha hf)
    (hD.nonnegSMulInvariant hb hg)

omit [MeasurableSpace Ω] in
theorem ConvexInvariant.convex
    {D : Set (Ω → ℝ)}
    (hD : ConvexInvariant D) :
    Convex ℝ D := by
  intro f hf g hg a b ha hb hab
  change (fun ω => a * f ω + b * g ω) ∈ D
  exact hD ha hb hab hf hg

omit [MeasurableSpace Ω] in
theorem ConvexInvariant.finset_nonneg_sum_mem
    {ι : Type*} {D : Set (Ω → ℝ)}
    (hD : ConvexInvariant D) (s : Finset ι)
    (w : ι → ℝ) (F : ι → Ω → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1)
    (hF : ∀ i ∈ s, F i ∈ D) :
    (fun ω => ∑ i ∈ s, w i * F i ω) ∈ D := by
  convert (hD.convex.sum_mem (t := s) (w := w) (z := F) hw hsum hF) using 1
  ext ω
  simp [Pi.smul_apply]

omit [MeasurableSpace Ω] in
theorem ClaimCone.convex
    {D : Set (Ω → ℝ)}
    (hD : ClaimCone D) :
    Convex ℝ D :=
  hD.convexInvariant.convex

omit [MeasurableSpace Ω] in
theorem ClaimCone.finset_nonneg_sum_mem
    {ι : Type*} {D : Set (Ω → ℝ)}
    (hD : ClaimCone D) (s : Finset ι)
    (w : ι → ℝ) (F : ι → Ω → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hF : ∀ i ∈ s, F i ∈ D) :
    (fun ω => ∑ i ∈ s, w i * F i ω) ∈ D := by
  classical
  revert hw hF
  refine Finset.induction_on s ?base ?step
  · intro _hw _hF
    have hzero := hD.1
    change (fun _ : Ω => 0) ∈ D at hzero
    simpa only [Finset.sum_empty] using hzero
  · intro a s ha ih hw hF
    have hterm : (fun ω => w a * F a ω) ∈ D :=
      hD.nonnegSMulInvariant
        (hw a (Finset.mem_insert_self a s))
        (hF a (Finset.mem_insert_self a s))
    have hsum : (fun ω => ∑ i ∈ s, w i * F i ω) ∈ D :=
      ih
        (fun i hi => hw i (Finset.mem_insert_of_mem hi))
        (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have hadd := hD.2.1 hterm hsum
    convert hadd using 1
    ext ω
    rw [Finset.sum_insert ha]

theorem C0AsDifference_hasZeroClaim
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hK0 : HasZeroClaim K0) :
    HasZeroClaim (C0AsDifference μ K0) := by
  refine ⟨fun _ => 0, hK0, fun _ => 0, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ => le_rfl)
  · exact Filter.Eventually.of_forall (fun _ => by ring)

theorem C0AsDifference_addInvariant
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hKadd : AddInvariant K0) :
    AddInvariant (C0AsDifference μ K0) := by
  intro f h hf hh
  rcases hf with ⟨g, hg, u, hunonneg, hfsub⟩
  rcases hh with ⟨k, hk, v, hvnonneg, hhsub⟩
  refine ⟨fun ω => g ω + k ω, hKadd hg hk, fun ω => u ω + v ω, ?_, ?_⟩
  · filter_upwards [hunonneg, hvnonneg] with ω huω hvω
    linarith
  · filter_upwards [hfsub, hhsub] with ω hfω hhω
    rw [hfω, hhω]
    ring

/--
The normalized Fatou closedness condition used in the README for cones:
if `f n ∈ D`, all `f n` are bounded below by `-1` a.e., and `f n → g` a.e.,
then `g ∈ D`.
-/
def FatouClosed (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f : ℕ → Ω → ℝ⦄ ⦃g : Ω → ℝ⦄,
    (∀ n, f n ∈ D) →
    (∀ n, AELowerBoundedBy μ (-1) (f n)) →
    TendstoAE μ f g →
    g ∈ D

/-- Positive scalar invariance passes from `K₀` to its raw downward hull. -/
theorem C0AsDifference_posSMulInvariant
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hK : PosSMulInvariant K0) :
    PosSMulInvariant (C0AsDifference μ K0) := by
  intro c hc f hf
  rcases hf with ⟨g, hg, h, hnonneg, hsub⟩
  refine ⟨fun ω => c * g ω, hK hc hg, fun ω => c * h ω, ?_, ?_⟩
  · filter_upwards [hnonneg] with ω hnonnegω
    exact mul_nonneg (le_of_lt hc) hnonnegω
  · filter_upwards [hsub] with ω hsubω
    rw [hsubω]
    ring

theorem C0AsDifference_claimCone
    {μ : Measure Ω} {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0) :
    ClaimCone (C0AsDifference μ K0) :=
  ⟨C0AsDifference_hasZeroClaim hK.1,
    C0AsDifference_addInvariant hK.2.1,
    C0AsDifference_posSMulInvariant hK.2.2⟩

end FTAPTheorem42
