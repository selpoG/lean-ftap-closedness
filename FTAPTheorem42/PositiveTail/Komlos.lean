import FTAPTheorem42.PositiveTail.Base
import FTAPTheorem42.Core.Closedness
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded/truncated Komlós-lite extraction

This module contains the bounded nonnegative extraction, the shift-back from
`[-δₙ, 1]`, and the strong/a.e. bridges used by Proposition 3.1.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The bounded/truncated Komlós-lite input needed after the positive-tail
truncation.  It returns forward convex combinations with the vanishing lower
risk and upper bound still available, plus a nonzero nonnegative a.e. limit.
-/
def KomlosLiteVanishingRiskPositiveMass (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ f : ℕ → Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) →
          (∀ n, AEStronglyMeasurable (f n) μ) →
            (∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) →
              Antitone δ →
                Tendsto δ atTop (nhds 0) →
                  (∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) →
                    ∃ W : ForwardConvexWeights,
                      ∃ g : Ω → ℝ,
                        TendstoAE μ (W.apply f) g ∧
                        AEStronglyMeasurable g μ ∧
                        (∀ n, AELowerBoundedBy μ (-(δ n)) (W.apply f n)) ∧
                        (∀ n, ∀ᵐ ω ∂μ, W.apply f n ω ≤ 1) ∧
                        (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
                        (∀ᵐ ω ∂μ, g ω ≤ 1) ∧
                        0 < μ {ω | 0 < g ω}

/--
Strong-measurability version of the bounded/truncated Komlós-lite input.  It is
suited to the proved Egorov core, which works with concrete strongly measurable
representatives rather than only a.e. strongly measurable ones.
-/
def KomlosLiteVanishingRiskPositiveMassStrong (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ f : ℕ → Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, 0 ≤ δ n) →
          (∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) →
            (∀ n, StronglyMeasurable (f n)) →
              (∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) →
                Antitone δ →
                  Tendsto δ atTop (nhds 0) →
                    (∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) →
                      ∃ W : ForwardConvexWeights,
                        ∃ g : Ω → ℝ,
                          TendstoAE μ (W.apply f) g ∧
                          StronglyMeasurable g ∧
                          (∀ n, AELowerBoundedBy μ (-(δ n)) (W.apply f n)) ∧
                          (∀ n, ∀ᵐ ω ∂μ, W.apply f n ω ≤ 1) ∧
                          (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
                          (∀ᵐ ω ∂μ, g ω ≤ 1) ∧
                          0 < μ {ω | 0 < g ω}

/--
The genuinely compactness-like part of the bounded/truncated Komlós-lite input:
produce forward convex combinations with a nonzero nonnegative a.e. limit.  The
routine preservation of lower risk, upper bound, and measurability is proved
below, so this is the smaller target for the remaining Komlós argument.
-/
def KomlosLiteExtractionStrong (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ f : ℕ → Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, 0 ≤ δ n) →
          (∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) →
            (∀ n, StronglyMeasurable (f n)) →
              (∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) →
                Antitone δ →
                  Tendsto δ atTop (nhds 0) →
                    (∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) →
                      ∃ W : ForwardConvexWeights,
                        ∃ g : Ω → ℝ,
                          TendstoAE μ (W.apply f) g ∧
                          StronglyMeasurable g ∧
                          (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
                          (∀ᵐ ω ∂μ, g ω ≤ 1) ∧
                          0 < μ {ω | 0 < g ω}

/--
Quadratic concave utility used for the bounded nonnegative Komlós-lite route.
The midpoint identity below converts near-maximality into an `L²` Cauchy
estimate.
-/
def quadraticUtility (M x : ℝ) : ℝ :=
  2 * M * x - x ^ 2

theorem quadraticUtility_midpoint (M x y : ℝ) :
    quadraticUtility M ((x + y) / 2) =
      (quadraticUtility M x + quadraticUtility M y) / 2 +
        (x - y) ^ 2 / 4 := by
  unfold quadraticUtility
  ring

theorem quadraticUtility_nonneg_of_nonneg_of_le
    {M x : ℝ} (h0 : 0 ≤ x) (hxM : x ≤ 2 * M) :
    0 ≤ quadraticUtility M x := by
  unfold quadraticUtility
  nlinarith [sq_nonneg x]

theorem quadraticUtility_nonneg_of_mem_Icc
    {M x : ℝ} (hM : 0 ≤ M) (hx : x ∈ Set.Icc (0 : ℝ) M) :
    0 ≤ quadraticUtility M x :=
  quadraticUtility_nonneg_of_nonneg_of_le hx.1 (by nlinarith [hx.2])

theorem quadraticUtility_pos_of_pos_of_le
    {M x : ℝ} (hx0 : 0 < x) (hxM : x < 2 * M) :
    0 < quadraticUtility M x := by
  unfold quadraticUtility
  have hxpos : 0 < x := hx0
  have hfactor : 0 < 2 * M - x := by linarith
  nlinarith [mul_pos hxpos hfactor]

theorem quadraticUtility_pos_of_mem_Ioc
    {M x : ℝ} (hM : 0 < M) (hx : x ∈ Set.Ioc (0 : ℝ) M) :
    0 < quadraticUtility M x :=
  quadraticUtility_pos_of_pos_of_le hx.1 (by nlinarith [hx.2, hM])

theorem quadraticUtility_le_of_le_of_mem_Icc
    {M c x : ℝ}
    (_hc0 : 0 ≤ c) (hcx : c ≤ x) (hxM : x ≤ M) (hcM : c ≤ M) :
    quadraticUtility M c ≤ quadraticUtility M x := by
  unfold quadraticUtility
  have hxmc : 0 ≤ x - c := sub_nonneg.mpr hcx
  have hfactor : 0 ≤ 2 * M - x - c := by
    have hxM' : x ≤ M := hxM
    have hcM' : c ≤ M := hcM
    linarith
  nlinarith [mul_nonneg hxmc hfactor]

theorem quadraticUtility_le_M_sq (M x : ℝ) :
    quadraticUtility M x ≤ M ^ 2 := by
  unfold quadraticUtility
  nlinarith [sq_nonneg (x - M)]

theorem quadraticUtility_le_M_sq_of_mem_Icc
    {M x : ℝ} (_hx : x ∈ Set.Icc (0 : ℝ) M) :
    quadraticUtility M x ≤ M ^ 2 :=
  quadraticUtility_le_M_sq M x

/-- The expected quadratic utility of a real-valued claim representative. -/
noncomputable def utilityIntegral
    (μ : Measure Ω) (M : ℝ) (h : Ω → ℝ) : ℝ :=
  ∫ ω, quadraticUtility M (h ω) ∂μ

/-- Utility values attained by fixed-tail convex weights. -/
def convTailUtilityValues
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (M : ℝ) (n : ℕ) : Set ℝ :=
  Set.range fun w : TailConvexWeights n =>
    utilityIntegral μ M (w.apply x)

/-- Supremum of utility values over all fixed-tail convex weights. -/
noncomputable def convTailUtilitySup
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (M : ℝ) (n : ℕ) : ℝ :=
  sSup (convTailUtilityValues μ x M n)

theorem convTailUtilityValues_nonempty
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (M : ℝ) (n : ℕ) :
    (convTailUtilityValues μ x M n).Nonempty :=
  ⟨utilityIntegral μ M ((TailConvexWeights.singleton n).apply x),
    TailConvexWeights.singleton n, rfl⟩

theorem convTailUtilitySup_le
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {M : ℝ} {n : ℕ}
    (hbdd : BddAbove (convTailUtilityValues μ x M n))
    (w : TailConvexWeights n) :
    utilityIntegral μ M (w.apply x) ≤
      convTailUtilitySup μ x M n := by
  exact le_csSup hbdd ⟨w, rfl⟩

theorem convTailUtilitySup_antitone
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {M : ℝ}
    (hbdd : ∀ n, BddAbove (convTailUtilityValues μ x M n)) :
    Antitone (fun n => convTailUtilitySup μ x M n) := by
  intro n m hnm
  unfold convTailUtilitySup
  exact csSup_le_csSup (hbdd n)
    (convTailUtilityValues_nonempty μ x M m)
    (by
      intro a ha
      rcases ha with ⟨w, rfl⟩
      exact ⟨w.mono hnm, rfl⟩)

theorem exists_near_convTailUtilitySup
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {M : ℝ} {n : ℕ}
    {η : ℝ} (hη : 0 < η) :
    ∃ w : TailConvexWeights n,
      convTailUtilitySup μ x M n - η <
        utilityIntegral μ M (w.apply x) := by
  obtain ⟨a, ha, hlt⟩ :=
    exists_lt_of_lt_csSup
      (convTailUtilityValues_nonempty μ x M n)
      (sub_lt_self _ hη)
  rcases ha with ⟨w, rfl⟩
  exact ⟨w, hlt⟩

theorem utilityIntegral_nonneg_of_ae_Icc
    {μ : Measure Ω} {M : ℝ} {h : Ω → ℝ}
    (hM : 0 ≤ M)
    (hh : ∀ᵐ ω ∂μ, h ω ∈ Set.Icc (0 : ℝ) M) :
    0 ≤ utilityIntegral μ M h := by
  unfold utilityIntegral
  exact integral_nonneg_of_ae <| hh.mono fun _ω hω =>
    quadraticUtility_nonneg_of_mem_Icc hM hω

theorem lt_measureReal_of_ofReal_lt
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {ε : ℝ} {A : Set Ω}
    (hε : 0 < ε)
    (hA : ENNReal.ofReal ε < μ A) :
    ε < μ.real A := by
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hε) (by finiteness)).mp hA

theorem utilityIntegrable_of_ae_Icc
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : ℝ} {h : Ω → ℝ}
    (hh_meas : StronglyMeasurable h)
    (hh : ∀ᵐ ω ∂μ, h ω ∈ Set.Icc (0 : ℝ) M) :
    Integrable (fun ω => quadraticUtility M (h ω)) μ := by
  refine MeasureTheory.Integrable.of_bound ?_ (M ^ 2) ?_
  · unfold quadraticUtility
    fun_prop
  · filter_upwards [hh] with _ω hω
    have hM : 0 ≤ M := le_trans hω.1 hω.2
    have hnonneg := quadraticUtility_nonneg_of_mem_Icc hM hω
    have hle := quadraticUtility_le_M_sq_of_mem_Icc hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

theorem utilityIntegral_le_const_of_ae_Icc
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : ℝ} {h : Ω → ℝ}
    (hh_meas : StronglyMeasurable h)
    (hh : ∀ᵐ ω ∂μ, h ω ∈ Set.Icc (0 : ℝ) M) :
    utilityIntegral μ M h ≤ M ^ 2 * (μ Set.univ).toReal := by
  unfold utilityIntegral
  have hInt := utilityIntegrable_of_ae_Icc (μ := μ) (M := M) hh_meas hh
  have hconst : Integrable (fun _ : Ω => M ^ 2) μ := integrable_const _
  calc
    ∫ ω, quadraticUtility M (h ω) ∂μ
        ≤ ∫ _ : Ω, M ^ 2 ∂μ := by
          refine integral_mono_ae hInt hconst ?_
          exact hh.mono fun _ω hω => quadraticUtility_le_M_sq_of_mem_Icc hω
    _ = M ^ 2 * (μ Set.univ).toReal := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, smul_eq_mul, mul_comm]

theorem utilityIntegral_original_pos_lower
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : Ω → ℝ} {M ε c : ℝ}
    (hM : 0 < M)
    (hc : 0 < c)
    (hcM : c ≤ M)
    (hε : 0 < ε)
    (hx_meas : StronglyMeasurable x)
    (hx_nonneg : ∀ᵐ ω ∂μ, 0 ≤ x ω)
    (hx_le : ∀ᵐ ω ∂μ, x ω ≤ M)
    (hmass : ENNReal.ofReal ε < μ {ω | c < x ω}) :
    quadraticUtility M c * ε < utilityIntegral μ M x := by
  let A : Set Ω := {ω | c < x ω}
  let u : ℝ := quadraticUtility M c
  have hA : MeasurableSet A := by
    dsimp [A]
    exact stronglyMeasurable_const.measurableSet_lt hx_meas
  have hu_pos : 0 < u := by
    dsimp [u]
    exact quadraticUtility_pos_of_mem_Ioc hM ⟨hc, hcM⟩
  have hleft_int : Integrable (A.indicator (fun _ : Ω => u)) μ :=
    (integrable_const u).indicator hA
  have hx_Icc : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [hx_nonneg, hx_le] with ω h0 hle
    exact ⟨h0, hle⟩
  have hright_int := utilityIntegrable_of_ae_Icc (μ := μ) (M := M) hx_meas hx_Icc
  have hpoint :
      (A.indicator (fun _ : Ω => u)) ≤ᶠ[ae μ]
        fun ω => quadraticUtility M (x ω) := by
    filter_upwards [hx_Icc] with ω hxω
    by_cases hω : ω ∈ A
    · have hcx : c ≤ x ω := le_of_lt hω
      have hle :=
        quadraticUtility_le_of_le_of_mem_Icc
          (le_of_lt hc) hcx hxω.2 hcM
      simpa [A, u, hω] using hle
    · have hnonneg := quadraticUtility_nonneg_of_mem_Icc (le_of_lt hM) hxω
      simpa [A, u, hω] using hnonneg
  have hint :
      ∫ ω, A.indicator (fun _ : Ω => u) ω ∂μ ≤ utilityIntegral μ M x := by
    unfold utilityIntegral
    exact MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hleft_eq :
      ∫ ω, A.indicator (fun _ : Ω => u) ω ∂μ = μ.real A * u := by
    rw [MeasureTheory.integral_indicator_const u hA]
    simp [smul_eq_mul]
  have hε_real : ε < μ.real A :=
    lt_measureReal_of_ofReal_lt (μ := μ) hε hmass
  have hmul : ε * u < μ.real A * u :=
    mul_lt_mul_of_pos_right hε_real hu_pos
  have hlt_left :
      quadraticUtility M c * ε <
        ∫ ω, A.indicator (fun _ : Ω => u) ω ∂μ := by
    rw [hleft_eq]
    dsimp [u] at hmul ⊢
    nlinarith
  exact lt_of_lt_of_le hlt_left hint

noncomputable def nearError (a : ℝ) (n : ℕ) : ℝ :=
  min (a / 2) ((positiveTailScaleDenom n)⁻¹)

theorem nearError_pos {a : ℝ} (ha : 0 < a) :
    ∀ n, 0 < nearError a n := by
  intro n
  unfold nearError
  exact lt_min (by positivity) (inv_pos.mpr (positiveTailScaleDenom_pos n))

theorem nearError_nonneg {a : ℝ} (ha : 0 < a) :
    ∀ n, 0 ≤ nearError a n := fun n => le_of_lt (nearError_pos ha n)

theorem nearError_le_half {a : ℝ} :
    ∀ n, nearError a n ≤ a / 2 := by
  intro n
  unfold nearError
  exact min_le_left _ _

theorem tendsto_nearError_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (nearError a) atTop (nhds 0) := by
  refine squeeze_zero (fun n => nearError_nonneg ha n)
    (fun n => by
      unfold nearError
      exact min_le_right _ _)
    ?_
  exact positiveTailScaleInv_tendsto_zero

theorem nearSupWeights_utilityIntegral_pos_lower
    {S J η : ℕ → ℝ} {a : ℝ}
    (_ha : 0 < a)
    (hS_lower : ∀ n, a < S n)
    (hη_le : ∀ n, η n ≤ a / 2)
    (hnear : ∀ n, S n - η n < J n) :
    ∀ n, a / 2 < J n := by
  intro n
  have hη := hη_le n
  have hS := hS_lower n
  have hnear_n := hnear n
  nlinarith

theorem convTailUtilityValues_bddAbove
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M : ℝ} (n : ℕ)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M) :
    BddAbove (convTailUtilityValues μ x M n) := by
  refine ⟨M ^ 2 * (μ Set.univ).toReal, ?_⟩
  intro a ha
  rcases ha with ⟨w, rfl⟩
  have hIcc : ∀ᵐ ω ∂μ, w.apply x ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [w.apply_ae_nonneg hx_nonneg, w.apply_ae_le hx_le] with ω h0 hle
    exact ⟨h0, hle⟩
  exact utilityIntegral_le_const_of_ae_Icc (w.apply_stronglyMeasurable hx_meas) hIcc

theorem convTailUtilitySup_pos_lower
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M ε c : ℝ}
    (hM : 0 < M)
    (hc : 0 < c)
    (hcM : c ≤ M)
    (hε : 0 < ε)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M)
    (hmass : ∀ n, ENNReal.ofReal ε < μ {ω | c < x n ω}) :
    ∀ n,
      quadraticUtility M c * ε <
        convTailUtilitySup μ x M n := by
  intro n
  have hbdd := convTailUtilityValues_bddAbove μ n hx_meas hx_nonneg hx_le
  have hJx :
      quadraticUtility M c * ε < utilityIntegral μ M (x n) :=
    utilityIntegral_original_pos_lower (μ := μ)
      hM hc hcM hε (hx_meas n) (hx_nonneg n) (hx_le n) (hmass n)
  have hsingleton :
      utilityIntegral μ M ((TailConvexWeights.singleton n).apply x) =
        utilityIntegral μ M (x n) := by
    unfold utilityIntegral
    apply integral_congr_ae
    filter_upwards with ω
    simp [TailConvexWeights.singleton_apply]
  have hle :
      utilityIntegral μ M (x n) ≤ convTailUtilitySup μ x M n := by
    rw [← hsingleton]
    exact convTailUtilitySup_le hbdd (TailConvexWeights.singleton n)
  exact lt_of_lt_of_le hJx hle

theorem exists_nearSupWeights
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {M : ℝ}
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ∃ w : ∀ n, TailConvexWeights n,
      ∀ n,
        convTailUtilitySup μ x M n - η n <
          utilityIntegral μ M ((w n).apply x) := by
  choose w hw using fun n =>
    exists_near_convTailUtilitySup
      (μ := μ) (x := x) (M := M) (n := n) (hη n)
  exact ⟨w, hw⟩

/-- Squared `L²` distance of two real-valued representatives. -/
noncomputable def L2SqDist
    (μ : Measure Ω) (y z : Ω → ℝ) : ℝ :=
  ∫ ω, (y ω - z ω) ^ 2 ∂μ

theorem L2SqDist_comm (μ : Measure Ω) (y z : Ω → ℝ) :
    L2SqDist μ y z = L2SqDist μ z y := by
  unfold L2SqDist
  apply integral_congr_ae
  filter_upwards with ω
  ring

/-!
### Bounded exponential utility

For nonnegative claims, `1 - exp (-x)` is bounded and its midpoint defect is
the squared `L²` distance of the exponential transforms.
-/

noncomputable def exponentialUtility (x : ℝ) : ℝ :=
  1 - Real.exp (-x)

theorem exponentialUtility_strictMono : StrictMono exponentialUtility := by
  intro x y hxy
  unfold exponentialUtility
  have hneg : -y < -x := by linarith
  have hexp : Real.exp (-y) < Real.exp (-x) :=
    Real.exp_lt_exp.mpr hneg
  linarith

noncomputable def exponentialTransform (x : ℝ) : ℝ :=
  Real.exp (-x / 2)

theorem exponentialUtility_midpoint (x y : ℝ) :
    exponentialUtility ((x + y) / 2) -
        (exponentialUtility x + exponentialUtility y) / 2 =
      (exponentialTransform x - exponentialTransform y) ^ 2 / 2 := by
  unfold exponentialUtility exponentialTransform
  have hxy : Real.exp (-((x + y) / 2)) =
      Real.exp (-x / 2) * Real.exp (-y / 2) := by
    rw [show -((x + y) / 2) = -x / 2 + -y / 2 by ring, Real.exp_add]
  have hx : Real.exp (-x) = Real.exp (-x / 2) ^ 2 := by
    rw [show -x = -x / 2 + -x / 2 by ring, Real.exp_add]
    ring_nf
  have hy : Real.exp (-y) = Real.exp (-y / 2) ^ 2 := by
    rw [show -y = -y / 2 + -y / 2 by ring, Real.exp_add]
    ring_nf
  rw [hxy, hx, hy]
  ring

theorem exponentialUtility_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ exponentialUtility x := by
  unfold exponentialUtility
  have hle : Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

theorem exponentialUtility_le_one (x : ℝ) :
    exponentialUtility x ≤ 1 := by
  unfold exponentialUtility
  linarith [Real.exp_pos (-x)]

theorem exponentialTransform_nonneg (x : ℝ) :
    0 ≤ exponentialTransform x :=
  (Real.exp_pos _).le

theorem exponentialTransform_le_one {x : ℝ} (hx : 0 ≤ x) :
    exponentialTransform x ≤ 1 := by
  unfold exponentialTransform
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith)

noncomputable def exponentialUtilityIntegral
    (μ : Measure Ω) (h : Ω → ℝ) : ℝ :=
  ∫ ω, exponentialUtility (h ω) ∂μ

theorem exponentialUtility_integrable_of_ae_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ}
    (hh_meas : StronglyMeasurable h)
    (hh : ∀ᵐ ω ∂μ, 0 ≤ h ω) :
    Integrable (fun ω => exponentialUtility (h ω)) μ := by
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · unfold exponentialUtility
    fun_prop
  · filter_upwards [hh] with ω hω
    have hnonneg := exponentialUtility_nonneg hω
    have hle := exponentialUtility_le_one (h ω)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

theorem exponentialUtilityIntegral_nonneg_of_ae_nonneg
    {μ : Measure Ω} {h : Ω → ℝ}
    (hh : ∀ᵐ ω ∂μ, 0 ≤ h ω) :
    0 ≤ exponentialUtilityIntegral μ h := by
  unfold exponentialUtilityIntegral
  exact integral_nonneg_of_ae <| hh.mono fun _ω hω =>
    exponentialUtility_nonneg hω

theorem exponentialUtilityIntegral_lt_of_ae_le_of_measure_set_lt_pos
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ}
    (hf_meas : StronglyMeasurable f)
    (hg_meas : StronglyMeasurable g)
    (hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hfg : AEDominatedBy μ f g)
    (hstrict : 0 < μ {ω | f ω < g ω}) :
    exponentialUtilityIntegral μ f < exponentialUtilityIntegral μ g := by
  have hf_int :
      Integrable (fun ω => exponentialUtility (f ω)) μ :=
    exponentialUtility_integrable_of_ae_nonneg hf_meas hf_nonneg
  have hg_int :
      Integrable (fun ω => exponentialUtility (g ω)) μ :=
    exponentialUtility_integrable_of_ae_nonneg hg_meas hg_nonneg
  have hUle :
      ∀ᵐ ω ∂μ,
        exponentialUtility (f ω) ≤ exponentialUtility (g ω) := by
    filter_upwards [hfg] with ω hω
    exact exponentialUtility_strictMono.monotone hω
  let d : Ω → ℝ := fun ω =>
    exponentialUtility (g ω) - exponentialUtility (f ω)
  have hd_nonneg : ∀ᵐ ω ∂μ, 0 ≤ d ω := by
    filter_upwards [hUle] with ω hω
    dsimp [d]
    linarith
  have hd_int : Integrable d μ := by
    dsimp [d]
    exact hg_int.sub hf_int
  have hstrict_support :
      {ω | f ω < g ω} ⊆ Function.support d := by
    intro ω hω
    change d ω ≠ 0
    intro hzero
    have hUstrict :
        exponentialUtility (f ω) < exponentialUtility (g ω) :=
      exponentialUtility_strictMono hω
    dsimp [d] at hzero
    linarith
  have hsupport_pos : 0 < μ (Function.support d) :=
    lt_of_lt_of_le hstrict (measure_mono hstrict_support)
  have hd_integral_pos : 0 < ∫ ω, d ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hd_nonneg hd_int).2 hsupport_pos
  have hdiff_pos :
      0 < exponentialUtilityIntegral μ g - exponentialUtilityIntegral μ f := by
    rw [← show
      (∫ ω, d ω ∂μ) =
        exponentialUtilityIntegral μ g - exponentialUtilityIntegral μ f by
          dsimp [d, exponentialUtilityIntegral]
          rw [integral_sub hg_int hf_int]]
    exact hd_integral_pos
  exact sub_pos.mp hdiff_pos

theorem exponentialUtilityIntegral_le_measure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} (hh_meas : StronglyMeasurable h)
    (hh : ∀ᵐ ω ∂μ, 0 ≤ h ω) :
    exponentialUtilityIntegral μ h ≤ (μ Set.univ).toReal := by
  unfold exponentialUtilityIntegral
  have hInt := exponentialUtility_integrable_of_ae_nonneg hh_meas hh
  have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  calc
    ∫ ω, exponentialUtility (h ω) ∂μ
        ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
          refine integral_mono_ae hInt hconst ?_
          exact Eventually.of_forall (fun ω => exponentialUtility_le_one _)
    _ = (μ Set.univ).toReal := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, smul_eq_mul]

theorem exponentialUtilityIntegral_midpoint_of_integrable
    {μ : Measure Ω} {y z : Ω → ℝ}
    (hy_int : Integrable (fun ω => exponentialUtility (y ω)) μ)
    (hz_int : Integrable (fun ω => exponentialUtility (z ω)) μ)
    (hd_int : Integrable
      (fun ω => (exponentialTransform (y ω) - exponentialTransform (z ω)) ^ 2) μ) :
    exponentialUtilityIntegral μ (fun ω => (y ω + z ω) / 2) =
      (exponentialUtilityIntegral μ y + exponentialUtilityIntegral μ z) / 2 +
        (1 / 2) * L2SqDist μ
          (fun ω => exponentialTransform (y ω))
          (fun ω => exponentialTransform (z ω)) := by
  unfold exponentialUtilityIntegral L2SqDist
  have hpoint :
      (fun ω => exponentialUtility ((y ω + z ω) / 2)) =
        fun ω => (exponentialUtility (y ω) + exponentialUtility (z ω)) / 2 +
          (1 / 2) *
            (exponentialTransform (y ω) - exponentialTransform (z ω)) ^ 2 := by
    ext ω
    have h := exponentialUtility_midpoint (y ω) (z ω)
    linarith
  rw [hpoint]
  have hsum_int :
      Integrable
        (fun ω => (exponentialUtility (y ω) + exponentialUtility (z ω)) / 2) μ := by
    exact (hy_int.add hz_int).div_const 2
  have hdist_int :
      Integrable
        (fun ω => (1 / 2) *
          (exponentialTransform (y ω) - exponentialTransform (z ω)) ^ 2) μ :=
    hd_int.const_mul (1 / 2)
  rw [integral_add hsum_int hdist_int]
  rw [integral_div]
  rw [integral_add hy_int hz_int]
  rw [integral_const_mul]

theorem exponentialUtilityIntegral_midpoint_of_ae_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {y z : Ω → ℝ}
    (hy_meas : StronglyMeasurable y)
    (hz_meas : StronglyMeasurable z)
    (hy_nonneg : ∀ᵐ ω ∂μ, 0 ≤ y ω)
    (hz_nonneg : ∀ᵐ ω ∂μ, 0 ≤ z ω) :
    exponentialUtilityIntegral μ (fun ω => (y ω + z ω) / 2) =
      (exponentialUtilityIntegral μ y + exponentialUtilityIntegral μ z) / 2 +
        (1 / 2) * L2SqDist μ
          (fun ω => exponentialTransform (y ω))
          (fun ω => exponentialTransform (z ω)) := by
  have hy_int := exponentialUtility_integrable_of_ae_nonneg hy_meas hy_nonneg
  have hz_int := exponentialUtility_integrable_of_ae_nonneg hz_meas hz_nonneg
  have hqy_meas : StronglyMeasurable (fun ω => exponentialTransform (y ω)) := by
    unfold exponentialTransform
    fun_prop
  have hqz_meas : StronglyMeasurable (fun ω => exponentialTransform (z ω)) := by
    unfold exponentialTransform
    fun_prop
  have hqy_nonneg : ∀ᵐ ω ∂μ, 0 ≤ exponentialTransform (y ω) :=
    Eventually.of_forall fun ω => exponentialTransform_nonneg _
  have hqz_nonneg : ∀ᵐ ω ∂μ, 0 ≤ exponentialTransform (z ω) :=
    Eventually.of_forall fun ω => exponentialTransform_nonneg _
  have hqy_le : ∀ᵐ ω ∂μ, exponentialTransform (y ω) ≤ 1 := by
    filter_upwards [hy_nonneg] with ω hω
    exact exponentialTransform_le_one hω
  have hqz_le : ∀ᵐ ω ∂μ, exponentialTransform (z ω) ≤ 1 := by
    filter_upwards [hz_nonneg] with ω hω
    exact exponentialTransform_le_one hω
  have hd_int :
      Integrable
        (fun ω => (exponentialTransform (y ω) - exponentialTransform (z ω)) ^ 2) μ := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · fun_prop
    · filter_upwards [hqy_nonneg, hqy_le, hqz_nonneg, hqz_le] with ω hy0 hy1 hz0 hz1
      have habs :
          |exponentialTransform (y ω) - exponentialTransform (z ω)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hsq :
          (exponentialTransform (y ω) - exponentialTransform (z ω)) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg
          (exponentialTransform (y ω) - exponentialTransform (z ω))]
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg
          (exponentialTransform (y ω) - exponentialTransform (z ω)))] using hsq
  exact exponentialUtilityIntegral_midpoint_of_integrable hy_int hz_int hd_int

def expTailUtilityValues
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (n : ℕ) : Set ℝ :=
  Set.range fun w : TailConvexWeights n =>
    exponentialUtilityIntegral μ (w.apply x)

noncomputable def expTailUtilitySup
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  sSup (expTailUtilityValues μ x n)

theorem expTailUtilityValues_nonempty
    (μ : Measure Ω) (x : ℕ → Ω → ℝ) (n : ℕ) :
    (expTailUtilityValues μ x n).Nonempty :=
  ⟨exponentialUtilityIntegral μ ((TailConvexWeights.singleton n).apply x),
    TailConvexWeights.singleton n, rfl⟩

theorem expTailUtilitySup_le
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {n : ℕ}
    (hbdd : BddAbove (expTailUtilityValues μ x n))
    (w : TailConvexWeights n) :
    exponentialUtilityIntegral μ (w.apply x) ≤ expTailUtilitySup μ x n := by
  exact le_csSup hbdd ⟨w, rfl⟩

theorem expTailUtilitySup_antitone
    {μ : Measure Ω} {x : ℕ → Ω → ℝ}
    (hbdd : ∀ n, BddAbove (expTailUtilityValues μ x n)) :
    Antitone (fun n => expTailUtilitySup μ x n) := by
  intro n m hnm
  unfold expTailUtilitySup
  exact csSup_le_csSup (hbdd n)
    (expTailUtilityValues_nonempty μ x m)
    (by
      intro a ha
      rcases ha with ⟨w, rfl⟩
      exact ⟨w.mono hnm, rfl⟩)

theorem exists_near_expTailUtilitySup
    {μ : Measure Ω} {x : ℕ → Ω → ℝ} {n : ℕ}
    {η : ℝ} (hη : 0 < η) :
    ∃ w : TailConvexWeights n,
      expTailUtilitySup μ x n - η <
        exponentialUtilityIntegral μ (w.apply x) := by
  obtain ⟨a, ha, hlt⟩ :=
    exists_lt_of_lt_csSup
      (expTailUtilityValues_nonempty μ x n)
      (sub_lt_self _ hη)
  rcases ha with ⟨w, rfl⟩
  exact ⟨w, hlt⟩

theorem expTailUtilityValues_bddAbove
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} (n : ℕ)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω) :
    BddAbove (expTailUtilityValues μ x n) := by
  refine ⟨(μ Set.univ).toReal, ?_⟩
  intro a ha
  rcases ha with ⟨w, rfl⟩
  exact exponentialUtilityIntegral_le_measure
    (w.apply_stronglyMeasurable hx_meas)
    (w.apply_ae_nonneg hx_nonneg)

theorem exists_near_expTailUtilitySup_weights
    {μ : Measure Ω} {x : ℕ → Ω → ℝ}
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ∃ w : ∀ n, TailConvexWeights n,
      ∀ n,
        expTailUtilitySup μ x n - η n <
          exponentialUtilityIntegral μ ((w n).apply x) := by
  choose w hw using fun n =>
    exists_near_expTailUtilitySup (μ := μ) (x := x) (n := n) (hη n)
  exact ⟨w, hw⟩

theorem nearExpSup_L2SqDist_lt_of_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {η : ℕ → ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - η n <
        exponentialUtilityIntegral μ ((w n).apply x))
    {n m : ℕ} (hnm : n ≤ m) :
    L2SqDist μ
        (fun ω => exponentialTransform ((w n).apply x ω))
        (fun ω => exponentialTransform ((w m).apply x ω)) <
      expTailUtilitySup μ x n - expTailUtilitySup μ x m + η n + η m := by
  let wm : TailConvexWeights n := (w m).mono hnm
  have hbddn := expTailUtilityValues_bddAbove μ n hx_meas hx_nonneg
  have hmid_le :
      exponentialUtilityIntegral μ (((w n).average wm).apply x) ≤
        expTailUtilitySup μ x n :=
    expTailUtilitySup_le hbddn ((w n).average wm)
  have hmid_fun :
      ((w n).average wm).apply x =
        fun ω => ((w n).apply x ω + (w m).apply x ω) / 2 := by
    rw [TailConvexWeights.average_apply, TailConvexWeights.mono_apply]
  rw [hmid_fun] at hmid_le
  have hid := exponentialUtilityIntegral_midpoint_of_ae_nonneg
    ((w n).apply_stronglyMeasurable hx_meas)
    ((w m).apply_stronglyMeasurable hx_meas)
    ((w n).apply_ae_nonneg hx_nonneg)
    ((w m).apply_ae_nonneg hx_nonneg)
  have hmid_bound :
      (exponentialUtilityIntegral μ ((w n).apply x) +
          exponentialUtilityIntegral μ ((w m).apply x)) / 2 +
        (1 / 2) * L2SqDist μ
          (fun ω => exponentialTransform ((w n).apply x ω))
          (fun ω => exponentialTransform ((w m).apply x ω)) ≤
          expTailUtilitySup μ x n := by
    rw [← hid]
    exact hmid_le
  have hn_near := hw_near n
  have hm_near := hw_near m
  nlinarith

theorem expTailUtilitySup_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} (n : ℕ)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω) :
    0 ≤ expTailUtilitySup μ x n := by
  have hbdd := expTailUtilityValues_bddAbove μ n hx_meas hx_nonneg
  have hsingle_nonneg :
      ∀ᵐ ω ∂μ, 0 ≤ (TailConvexWeights.singleton n).apply x ω := by
    simpa [TailConvexWeights.singleton_apply] using hx_nonneg n
  have hnonneg :
      0 ≤ exponentialUtilityIntegral μ ((TailConvexWeights.singleton n).apply x) :=
    exponentialUtilityIntegral_nonneg_of_ae_nonneg hsingle_nonneg
  exact le_trans hnonneg
    (expTailUtilitySup_le hbdd (TailConvexWeights.singleton n))

/-!
### Exponential utility on an a.e. upper section

The next layer records the exponential utility values of the a.e. upper
section of a claim set.  The supremum is deliberately a real `sSup`: a
finite-measure upper bound is supplied by the measurability and nonnegativity
lemmas below whenever an order comparison with the supremum is needed.
-/

def aeUpperSectionExponentialUtilityValues
    (μ : Measure Ω) (D : Set (Ω → ℝ)) (g : Ω → ℝ) : Set ℝ :=
  (fun h => exponentialUtilityIntegral μ (fun ω => h ω - g ω)) ''
    (AEUpperSection μ D g)

noncomputable def aeUpperSectionExponentialUtilitySup
    (μ : Measure Ω) (D : Set (Ω → ℝ)) (g : Ω → ℝ) : ℝ :=
  sSup (aeUpperSectionExponentialUtilityValues μ D g)

theorem aeUpperSection_nonempty_of_mem
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hg_mem : g ∈ D) :
    (AEUpperSection μ D g).Nonempty := by
  exact ⟨g, ⟨hg_mem, AEDominatedBy.refl μ g⟩⟩

theorem aeUpperSectionExponentialUtilityValues_nonempty
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hUpper : (AEUpperSection μ D g).Nonempty) :
    (aeUpperSectionExponentialUtilityValues μ D g).Nonempty := by
  rcases hUpper with ⟨h, hh⟩
  exact ⟨exponentialUtilityIntegral μ (fun ω => h ω - g ω), h, hh, rfl⟩

theorem aeUpperSectionExponentialUtilityValues_bddAbove
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hD_meas : ClaimSetStronglyMeasurable D)
    (hg_meas : StronglyMeasurable g) :
    BddAbove (aeUpperSectionExponentialUtilityValues μ D g) := by
  refine ⟨(μ Set.univ).toReal, ?_⟩
  intro a ha
  rcases ha with ⟨h, hh, rfl⟩
  apply exponentialUtilityIntegral_le_measure
  · exact (hD_meas h hh.1).sub hg_meas
  · filter_upwards [hh.2] with ω hω
    exact sub_nonneg.mpr hω

theorem aeUpperSectionExponentialUtilitySup_le
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g h : Ω → ℝ}
    (hBdd : BddAbove (aeUpperSectionExponentialUtilityValues μ D g))
    (hh : h ∈ AEUpperSection μ D g) :
    exponentialUtilityIntegral μ (fun ω => h ω - g ω) ≤
      aeUpperSectionExponentialUtilitySup μ D g := by
  exact le_csSup hBdd ⟨h, hh, rfl⟩

theorem exists_near_aeUpperSectionExponentialUtilitySup
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    {η : ℝ} (hUpper : (AEUpperSection μ D g).Nonempty)
    (hη : 0 < η) :
    ∃ h, h ∈ AEUpperSection μ D g ∧
      aeUpperSectionExponentialUtilitySup μ D g - η <
        exponentialUtilityIntegral μ (fun ω => h ω - g ω) := by
  obtain ⟨a, ha, hlt⟩ :=
    exists_lt_of_lt_csSup
      (aeUpperSectionExponentialUtilityValues_nonempty hUpper)
      (sub_lt_self _ hη)
  rcases ha with ⟨h, hh, rfl⟩
  exact ⟨h, hh, hlt⟩

theorem exists_near_aeUpperSectionExponentialUtilitySup_sequence
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    {η : ℕ → ℝ} (hUpper : (AEUpperSection μ D g).Nonempty)
    (hη : ∀ n, 0 < η n) :
    ∃ H : ℕ → Ω → ℝ,
      (∀ n, H n ∈ AEUpperSection μ D g) ∧
      ∀ n, aeUpperSectionExponentialUtilitySup μ D g - η n <
        exponentialUtilityIntegral μ (fun ω => H n ω - g ω) := by
  choose H hH hnear using fun n =>
    exists_near_aeUpperSectionExponentialUtilitySup
      (hUpper := hUpper) (hη := hη n)
  exact ⟨H, hH, hnear⟩

theorem aeUpperSectionExponentialUtility_gap_le_expTailUtilitySup
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ} {H : ℕ → Ω → ℝ}
    (hD_meas : ClaimSetStronglyMeasurable D)
    (hg_meas : StronglyMeasurable g)
    (hH : ∀ n, H n ∈ AEUpperSection μ D g)
    (n : ℕ) :
    exponentialUtilityIntegral μ (fun ω => H n ω - g ω) ≤
      expTailUtilitySup μ (fun i ω => H i ω - g ω) n := by
  let x : ℕ → Ω → ℝ := fun i ω => H i ω - g ω
  have hx_meas : ∀ i, StronglyMeasurable (x i) := by
    intro i
    exact (hD_meas (H i) (hH i).1).sub hg_meas
  have hx_nonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ x i ω := by
    intro i
    filter_upwards [(hH i).2] with ω hω
    exact sub_nonneg.mpr hω
  have hx_bdd : BddAbove (expTailUtilityValues μ x n) :=
    expTailUtilityValues_bddAbove μ n hx_meas hx_nonneg
  have hsingle :=
    expTailUtilitySup_le hx_bdd (TailConvexWeights.singleton n)
  simpa [x] using hsingle

theorem expTailUtilitySup_gap_le_aeUpperSectionExponentialUtilitySup
    {μ : Measure Ω} {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    {H : ℕ → Ω → ℝ}
    (hD_convex : ConvexInvariant D)
    (hH : ∀ n, H n ∈ AEUpperSection μ D g)
    (hBdd : BddAbove (aeUpperSectionExponentialUtilityValues μ D g))
    (n : ℕ) :
    expTailUtilitySup μ (fun i ω => H i ω - g ω) n ≤
      aeUpperSectionExponentialUtilitySup μ D g := by
  unfold expTailUtilitySup
  apply csSup_le (expTailUtilityValues_nonempty μ (fun i ω => H i ω - g ω) n)
  intro a ha
  rcases ha with ⟨w, rfl⟩
  change exponentialUtilityIntegral μ
      (w.apply (fun i ω => H i ω - g ω)) ≤
        aeUpperSectionExponentialUtilitySup μ D g
  have hUpperConvex :
      ConvexInvariant (AEUpperSection μ D g) :=
    hD_convex.aeUpperSection
  have hw_mem : w.apply H ∈ AEUpperSection μ D g := by
    change (fun ω => ∑ i ∈ w.support, w.weight i * H i ω) ∈
      AEUpperSection μ D g
    exact hUpperConvex.finset_nonneg_sum_mem w.support w.weight H
      w.nonneg w.sum_eq_one (fun i _hi => hH i)
  rw [w.apply_sub_constFunction H g]
  exact aeUpperSectionExponentialUtilitySup_le hBdd hw_mem

theorem tendsto_expTailUtilitySup_gap_of_nearMaximizingSequence
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    {H : ℕ → Ω → ℝ} {η : ℕ → ℝ}
    (hD_convex : ConvexInvariant D)
    (hD_meas : ClaimSetStronglyMeasurable D)
    (hg_meas : StronglyMeasurable g)
    (hH : ∀ n, H n ∈ AEUpperSection μ D g)
    (hnear : ∀ n,
      aeUpperSectionExponentialUtilitySup μ D g - η n <
        exponentialUtilityIntegral μ (fun ω => H n ω - g ω))
    (hη_tendsto : Tendsto η atTop (nhds 0)) :
    Tendsto
      (fun n => expTailUtilitySup μ (fun i ω => H i ω - g ω) n)
      atTop
      (nhds (aeUpperSectionExponentialUtilitySup μ D g)) := by
  let x : ℕ → Ω → ℝ := fun n ω => H n ω - g ω
  let S : ℝ := aeUpperSectionExponentialUtilitySup μ D g
  have hSetBdd :
      BddAbove (aeUpperSectionExponentialUtilityValues μ D g) :=
    aeUpperSectionExponentialUtilityValues_bddAbove hD_meas hg_meas
  have hx_meas : ∀ n, StronglyMeasurable (x n) := by
    intro n
    exact (hD_meas (H n) (hH n).1).sub hg_meas
  have hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω := by
    intro n
    filter_upwards [(hH n).2] with ω hω
    exact sub_nonneg.mpr hω
  have hUpper : ∀ n, expTailUtilitySup μ x n ≤ S := by
    intro n
    simpa [x, S] using
      (expTailUtilitySup_gap_le_aeUpperSectionExponentialUtilitySup
        (μ := μ) (D := D) (g := g) (H := H)
        hD_convex hH hSetBdd n)
  have hnear' : ∀ n, S - η n < exponentialUtilityIntegral μ (x n) := by
    intro n
    simpa [x, S] using hnear n
  have hLower : ∀ n, S - η n ≤ expTailUtilitySup μ x n := by
    intro n
    have hsingle' :
        exponentialUtilityIntegral μ (x n) ≤ expTailUtilitySup μ x n := by
      simpa [x] using
        (aeUpperSectionExponentialUtility_gap_le_expTailUtilitySup
          (μ := μ) (D := D) (g := g) (H := H)
          hD_meas hg_meas hH n)
    exact le_trans (le_of_lt (hnear' n)) hsingle'
  have hleft : Tendsto (fun n => S - η n) atTop (nhds S) := by
    simpa using (tendsto_const_nhds.sub hη_tendsto)
  have hright : Tendsto (fun _ : ℕ => S) atTop (nhds S) :=
    tendsto_const_nhds
  have htail :
      Tendsto (fun n => expTailUtilitySup μ x n) atTop (nhds S) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hleft hright hLower hUpper
  simpa [x, S] using htail

theorem tendsto_exponentialUtilityIntegral_of_tendstoAE
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {y : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hy_meas : ∀ n, StronglyMeasurable (y n))
    (hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ y n ω)
    (hlim : TendstoAE μ y g) :
    Tendsto
      (fun n => exponentialUtilityIntegral μ (y n))
      atTop
      (nhds (exponentialUtilityIntegral μ g)) := by
  have hcont : Continuous exponentialUtility := by
    unfold exponentialUtility
    fun_prop
  have hF_meas : ∀ n, AEStronglyMeasurable
      (fun ω => exponentialUtility (y n ω)) μ := by
    intro n
    exact (hcont.comp_stronglyMeasurable (hy_meas n)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖exponentialUtility (y n ω)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [hy_nonneg n] with ω hω
    have hnonneg := exponentialUtility_nonneg hω
    have hle := exponentialUtility_le_one (y n ω)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hlim_exp : ∀ᵐ ω ∂μ,
      Tendsto (fun n => exponentialUtility (y n ω)) atTop
        (nhds (exponentialUtility (g ω))) := by
    filter_upwards [hlim] with ω hω
    exact hcont.continuousAt.tendsto.comp hω
  have _hlim_exp_meas : AEStronglyMeasurable
      (fun ω => exponentialUtility (g ω)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF_meas hlim_exp
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ)
    (F := fun n ω => exponentialUtility (y n ω))
    (f := fun ω => exponentialUtility (g ω))
    (fun _ : Ω => (1 : ℝ))
    hF_meas
    (integrable_const _)
    hbound
    hlim_exp
  simpa [exponentialUtilityIntegral] using hDCT

theorem tendsto_exponentialUtilityIntegral_of_near_expTailUtilitySup
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    {w : ∀ n, TailConvexWeights n} {S : ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (_hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hδ_tendsto : Tendsto δ atTop (nhds 0))
    (hSup_tendsto :
      Tendsto (fun n => expTailUtilitySup μ x n) atTop (nhds S))
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - δ n <
        exponentialUtilityIntegral μ ((w n).apply x)) :
    Tendsto
      (fun n => exponentialUtilityIntegral μ ((w n).apply x))
      atTop
      (nhds S) := by
  have hbdd : ∀ n, BddAbove (expTailUtilityValues μ x n) := by
    intro n
    exact expTailUtilityValues_bddAbove μ n hx_meas hx_nonneg
  have hLower : ∀ n,
      expTailUtilitySup μ x n - δ n ≤
        exponentialUtilityIntegral μ ((w n).apply x) := by
    intro n
    exact le_of_lt (hw_near n)
  have hUpper : ∀ n,
      exponentialUtilityIntegral μ ((w n).apply x) ≤
        expTailUtilitySup μ x n := by
    intro n
    exact expTailUtilitySup_le (hbdd n) (w n)
  have hleft :
      Tendsto (fun n => expTailUtilitySup μ x n - δ n) atTop (nhds S) := by
    simpa using hSup_tendsto.sub hδ_tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hleft hSup_tendsto hLower hUpper

theorem tendsto_aeUpperSection_nearMaximizingWeights_exponentialUtilityIntegral
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    {H : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    {w : ∀ n, TailConvexWeights n} {S : ℝ}
    (hD_meas : ClaimSetStronglyMeasurable D)
    (hg_meas : StronglyMeasurable g)
    (hH : ∀ n, H n ∈ AEUpperSection μ D g)
    (_hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hδ_tendsto : Tendsto δ atTop (nhds 0))
    (hSup_tendsto :
      Tendsto
        (fun n => expTailUtilitySup μ (fun i ω => H i ω - g ω) n)
        atTop (nhds S))
    (hw_near : ∀ n,
      expTailUtilitySup μ (fun i ω => H i ω - g ω) n - δ n <
        exponentialUtilityIntegral μ
          ((w n).apply (fun i ω => H i ω - g ω))) :
    Tendsto
      (fun n => exponentialUtilityIntegral μ
        ((w n).apply (fun i ω => H i ω - g ω)))
      atTop
      (nhds S) := by
  let x : ℕ → Ω → ℝ := fun n ω => H n ω - g ω
  have hx_meas : ∀ n, StronglyMeasurable (x n) := by
    intro n
    exact (hD_meas (H n) (hH n).1).sub hg_meas
  have hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω := by
    intro n
    filter_upwards [(hH n).2] with ω hω
    exact sub_nonneg.mpr hω
  apply tendsto_exponentialUtilityIntegral_of_near_expTailUtilitySup
    (x := x) (δ := δ) (w := w) (S := S)
    hx_meas hx_nonneg _hδ_nonneg hδ_tendsto
  · simpa [x] using hSup_tendsto
  · intro n
    simpa [x] using hw_near n

theorem nearExpSupWeights_L2Cauchy
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {η : ℕ → ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (nhds 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - η n <
        exponentialUtilityIntegral μ ((w n).apply x)) :
    ∀ r : ℝ, 0 < r →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        L2SqDist μ
          (fun ω => exponentialTransform ((w n).apply x ω))
          (fun ω => exponentialTransform ((w m).apply x ω)) < r ^ 2 := by
  let S : ℕ → ℝ := fun n => expTailUtilitySup μ x n
  have hbdd : ∀ n, BddAbove (expTailUtilityValues μ x n) :=
    fun n => expTailUtilityValues_bddAbove μ n hx_meas hx_nonneg
  have hS_ant : Antitone S := expTailUtilitySup_antitone (μ := μ) (x := x) hbdd
  have hS_bdd : BddBelow (Set.range S) := by
    refine ⟨0, ?_⟩
    intro a ha
    rcases ha with ⟨n, rfl⟩
    exact expTailUtilitySup_nonneg n hx_meas hx_nonneg
  have hS_tendsto : Tendsto S atTop (nhds (⨅ n, S n)) :=
    tendsto_atTop_ciInf hS_ant hS_bdd
  have hS_cauchy : CauchySeq S := hS_tendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hS_cauchy
  rw [Metric.tendsto_atTop] at hη_tendsto
  intro r hr
  have heps : 0 < r ^ 2 / 4 := by positivity
  rcases hS_cauchy (r ^ 2 / 4) heps with ⟨NS, hNS⟩
  rcases hη_tendsto (r ^ 2 / 4) heps with ⟨Nη, hNη⟩
  refine ⟨max NS Nη, ?_⟩
  have hordered : ∀ n m, max NS Nη ≤ n → max NS Nη ≤ m → n ≤ m →
      L2SqDist μ
          (fun ω => exponentialTransform ((w n).apply x ω))
          (fun ω => exponentialTransform ((w m).apply x ω)) < r ^ 2 := by
    intro n m hn hm hnm
    have hnS : NS ≤ n := le_trans (le_max_left _ _) hn
    have hmS : NS ≤ m := le_trans (le_max_left _ _) hm
    have hnη : Nη ≤ n := le_trans (le_max_right _ _) hn
    have hmη : Nη ≤ m := le_trans (le_max_right _ _) hm
    have hSdist := hNS n hnS m hmS
    have hηn_dist := hNη n hnη
    have hηm_dist := hNη m hmη
    have hSdiff_lt : S n - S m < r ^ 2 / 4 := by
      have hSm_le : S m ≤ S n := hS_ant hnm
      have habs : |S n - S m| < r ^ 2 / 4 := by
        simpa [Real.dist_eq] using hSdist
      rwa [abs_of_nonneg (sub_nonneg.mpr hSm_le)] at habs
    have hηn_lt : η n < r ^ 2 / 4 := by
      have habs : |η n| < r ^ 2 / 4 := by
        simpa [Real.dist_eq] using hηn_dist
      exact (abs_of_nonneg (hη_nonneg n)) ▸ habs
    have hηm_lt : η m < r ^ 2 / 4 := by
      have habs : |η m| < r ^ 2 / 4 := by
        simpa [Real.dist_eq] using hηm_dist
      exact (abs_of_nonneg (hη_nonneg m)) ▸ habs
    have hD := nearExpSup_L2SqDist_lt_of_le
      (μ := μ) (x := x) (η := η) hx_meas hx_nonneg w hw_near hnm
    dsimp [S] at hSdiff_lt
    nlinarith
  intro n m hn hm
  by_cases hnm : n ≤ m
  · exact hordered n m hn hm hnm
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hswap := hordered m n hm hn hmn
    rw [L2SqDist_comm]
    exact hswap

theorem utilityIntegral_midpoint_of_integrable
    {μ : Measure Ω} {M : ℝ} {y z : Ω → ℝ}
    (hy_int : Integrable (fun ω => quadraticUtility M (y ω)) μ)
    (hz_int : Integrable (fun ω => quadraticUtility M (z ω)) μ)
    (hd_int : Integrable (fun ω => (y ω - z ω) ^ 2) μ) :
    utilityIntegral μ M (fun ω => (y ω + z ω) / 2) =
      (utilityIntegral μ M y + utilityIntegral μ M z) / 2 +
        (1 / 4) * L2SqDist μ y z := by
  unfold utilityIntegral L2SqDist
  have hpoint :
      (fun ω => quadraticUtility M ((y ω + z ω) / 2)) =
        fun ω => (quadraticUtility M (y ω) + quadraticUtility M (z ω)) / 2 +
          (1 / 4) * (y ω - z ω) ^ 2 := by
    ext ω
    rw [quadraticUtility_midpoint]
    ring
  rw [hpoint]
  have hsum_int :
      Integrable
        (fun ω => (quadraticUtility M (y ω) + quadraticUtility M (z ω)) / 2) μ := by
    exact (hy_int.add hz_int).div_const 2
  have hdist_int : Integrable (fun ω => (1 / 4) * (y ω - z ω) ^ 2) μ :=
    hd_int.const_mul (1 / 4)
  rw [integral_add hsum_int hdist_int]
  rw [integral_div]
  rw [integral_add hy_int hz_int]
  rw [integral_const_mul]

/-- A uniformly a.e. bounded real function on a finite measure space belongs to `L²`. -/
theorem memLp_two_of_ae_Icc
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} {M : ℝ}
    (_hM : 0 ≤ M)
    (hf_meas : StronglyMeasurable f)
    (hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hf_le : ∀ᵐ ω ∂μ, f ω ≤ M) :
    MemLp f (2 : ℝ≥0∞) μ := by
  refine MemLp.of_bound hf_meas.aestronglyMeasurable M ?_
  filter_upwards [hf_nonneg, hf_le] with ω h0 hle
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

theorem utilityIntegral_midpoint_of_ae_Icc
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : ℝ} {y z : Ω → ℝ}
    (hM : 0 ≤ M)
    (hy_meas : StronglyMeasurable y)
    (hz_meas : StronglyMeasurable z)
    (hy_nonneg : ∀ᵐ ω ∂μ, 0 ≤ y ω)
    (hy_le : ∀ᵐ ω ∂μ, y ω ≤ M)
    (hz_nonneg : ∀ᵐ ω ∂μ, 0 ≤ z ω)
    (hz_le : ∀ᵐ ω ∂μ, z ω ≤ M) :
    utilityIntegral μ M (fun ω => (y ω + z ω) / 2) =
      (utilityIntegral μ M y + utilityIntegral μ M z) / 2 +
        (1 / 4) * L2SqDist μ y z := by
  have hy_Icc : ∀ᵐ ω ∂μ, y ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [hy_nonneg, hy_le] with _ω h0 hle
    exact ⟨h0, hle⟩
  have hz_Icc : ∀ᵐ ω ∂μ, z ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [hz_nonneg, hz_le] with _ω h0 hle
    exact ⟨h0, hle⟩
  have hy_int := utilityIntegrable_of_ae_Icc (μ := μ) (M := M) hy_meas hy_Icc
  have hz_int := utilityIntegrable_of_ae_Icc (μ := μ) (M := M) hz_meas hz_Icc
  have hyMem := memLp_two_of_ae_Icc (μ := μ) hM hy_meas hy_nonneg hy_le
  have hzMem := memLp_two_of_ae_Icc (μ := μ) hM hz_meas hz_nonneg hz_le
  have hd_int : Integrable (fun ω => (y ω - z ω) ^ 2) μ := by
    simpa [Pi.sub_apply] using (hyMem.sub hzMem).integrable_sq
  exact utilityIntegral_midpoint_of_integrable hy_int hz_int hd_int

theorem nearSup_L2SqDist_lt_of_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M : ℝ} {η : ℕ → ℝ}
    (hM : 0 ≤ M)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M)
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      convTailUtilitySup μ x M n - η n <
        utilityIntegral μ M ((w n).apply x))
    {n m : ℕ} (hnm : n ≤ m) :
    L2SqDist μ ((w n).apply x) ((w m).apply x) <
      2 * ((convTailUtilitySup μ x M n - convTailUtilitySup μ x M m) +
        η n + η m) := by
  let wm : TailConvexWeights n := (w m).mono hnm
  have hbddn := convTailUtilityValues_bddAbove μ n hx_meas hx_nonneg hx_le
  have hmid_le :
      utilityIntegral μ M (((w n).average wm).apply x) ≤
        convTailUtilitySup μ x M n :=
    convTailUtilitySup_le hbddn ((w n).average wm)
  have hmid_fun :
      ((w n).average wm).apply x =
        fun ω => ((w n).apply x ω + (w m).apply x ω) / 2 := by
    rw [TailConvexWeights.average_apply, TailConvexWeights.mono_apply]
  rw [hmid_fun] at hmid_le
  have hid := utilityIntegral_midpoint_of_ae_Icc (μ := μ) (M := M)
    hM
    ((w n).apply_stronglyMeasurable hx_meas)
    ((w m).apply_stronglyMeasurable hx_meas)
    ((w n).apply_ae_nonneg hx_nonneg)
    ((w n).apply_ae_le hx_le)
    ((w m).apply_ae_nonneg hx_nonneg)
    ((w m).apply_ae_le hx_le)
  have hmid_bound :
      (utilityIntegral μ M ((w n).apply x) +
          utilityIntegral μ M ((w m).apply x)) / 2 +
        (1 / 4) * L2SqDist μ ((w n).apply x) ((w m).apply x) ≤
          convTailUtilitySup μ x M n := by
    rw [← hid]
    exact hmid_le
  have hn_near := hw_near n
  have hm_near := hw_near m
  nlinarith

theorem convTailUtilitySup_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M : ℝ} (n : ℕ)
    (hM : 0 ≤ M)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M) :
    0 ≤ convTailUtilitySup μ x M n := by
  have hbdd := convTailUtilityValues_bddAbove μ n hx_meas hx_nonneg hx_le
  have hIcc :
      ∀ᵐ ω ∂μ, (TailConvexWeights.singleton n).apply x ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [hx_nonneg n, hx_le n] with ω h0 hle
    simpa [TailConvexWeights.singleton_apply] using
      (show x n ω ∈ Set.Icc (0 : ℝ) M from ⟨h0, hle⟩)
  exact le_trans (utilityIntegral_nonneg_of_ae_Icc hM hIcc)
    (convTailUtilitySup_le hbdd (TailConvexWeights.singleton n))

theorem nearSupWeights_L2Cauchy
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M : ℝ} {η : ℕ → ℝ}
    (hM : 0 ≤ M)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (nhds 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      convTailUtilitySup μ x M n - η n <
        utilityIntegral μ M ((w n).apply x)) :
    ∀ r : ℝ, 0 < r →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        L2SqDist μ ((w n).apply x) ((w m).apply x) < r ^ 2 := by
  let S : ℕ → ℝ := fun n => convTailUtilitySup μ x M n
  have hbdd : ∀ n, BddAbove (convTailUtilityValues μ x M n) :=
    fun n => convTailUtilityValues_bddAbove μ n hx_meas hx_nonneg hx_le
  have hS_ant : Antitone S := convTailUtilitySup_antitone (μ := μ) (x := x) (M := M) hbdd
  have hS_bdd : BddBelow (Set.range S) := by
    refine ⟨0, ?_⟩
    intro a ha
    rcases ha with ⟨n, rfl⟩
    exact convTailUtilitySup_nonneg n hM hx_meas hx_nonneg hx_le
  have hS_tendsto : Tendsto S atTop (nhds (⨅ n, S n)) :=
    tendsto_atTop_ciInf hS_ant hS_bdd
  have hS_cauchy : CauchySeq S := hS_tendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hS_cauchy
  rw [Metric.tendsto_atTop] at hη_tendsto
  intro r hr
  have heps : 0 < r ^ 2 / 8 := by positivity
  rcases hS_cauchy (r ^ 2 / 8) heps with ⟨NS, hNS⟩
  rcases hη_tendsto (r ^ 2 / 8) heps with ⟨Nη, hNη⟩
  refine ⟨max NS Nη, ?_⟩
  have hordered : ∀ n m, max NS Nη ≤ n → max NS Nη ≤ m → n ≤ m →
      L2SqDist μ ((w n).apply x) ((w m).apply x) < r ^ 2 := by
    intro n m hn hm hnm
    have hnS : NS ≤ n := le_trans (le_max_left _ _) hn
    have hmS : NS ≤ m := le_trans (le_max_left _ _) hm
    have hnη : Nη ≤ n := le_trans (le_max_right _ _) hn
    have hmη : Nη ≤ m := le_trans (le_max_right _ _) hm
    have hSdist := hNS n hnS m hmS
    have hηn_dist := hNη n hnη
    have hηm_dist := hNη m hmη
    have hSdiff_lt : S n - S m < r ^ 2 / 8 := by
      have hSm_le : S m ≤ S n := hS_ant hnm
      have habs : |S n - S m| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hSdist
      rwa [abs_of_nonneg (sub_nonneg.mpr hSm_le)] at habs
    have hηn_lt : η n < r ^ 2 / 8 := by
      have habs : |η n| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hηn_dist
      exact (abs_of_nonneg (hη_nonneg n)) ▸ habs
    have hηm_lt : η m < r ^ 2 / 8 := by
      have habs : |η m| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hηm_dist
      exact (abs_of_nonneg (hη_nonneg m)) ▸ habs
    have hD := nearSup_L2SqDist_lt_of_le
      (μ := μ) (x := x) (M := M) (η := η)
      hM hx_meas hx_nonneg hx_le w hw_near hnm
    dsimp [S] at hSdiff_lt
    nlinarith
  intro n m hn hm
  by_cases hnm : n ≤ m
  · exact hordered n m hn hm hnm
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hswap := hordered m n hm hn hmn
    rw [L2SqDist_comm]
    exact hswap

theorem eLpNorm_two_toReal_eq_sqrt_L2SqDist
    {μ : Measure Ω} {y z : Ω → ℝ}
    (hy : MemLp y (2 : ℝ≥0∞) μ)
    (hz : MemLp z (2 : ℝ≥0∞) μ) :
    (eLpNorm (y - z) (2 : ℝ≥0∞) μ).toReal =
      Real.sqrt (L2SqDist μ y z) := by
  have hsub : MemLp (y - z) (2 : ℝ≥0∞) μ := hy.sub hz
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have heq := MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpTop hsub
  rw [heq]
  have hInt :
      (∫ a, ‖(y - z) a‖ ^ (2 : ℝ≥0∞).toReal ∂μ) =
        L2SqDist μ y z := by
    unfold L2SqDist
    apply integral_congr_ae
    filter_upwards with a
    simp [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [hInt]
  have hL2_nonneg : 0 ≤ L2SqDist μ y z := by
    unfold L2SqDist
    exact integral_nonneg_of_ae
      (Eventually.of_forall fun ω => sq_nonneg (y ω - z ω))
  rw [ENNReal.toReal_ofReal]
  · rw [Real.sqrt_eq_rpow]
    norm_num
  · exact Real.rpow_nonneg hL2_nonneg _

/--
The bridge from the quadratic utility estimate to the `Lp ℝ 2 μ` metric.
Keeping the `eLpNorm` calculation inside this lemma lets the later Komlós
extraction use only ordinary metric completeness of `Lp`.
-/
theorem dist_toLp_two_lt_of_L2SqDist_lt
    {μ : Measure Ω}
    {y z : Ω → ℝ}
    (hy : MemLp y (2 : ℝ≥0∞) μ)
    (hz : MemLp z (2 : ℝ≥0∞) μ)
    {r : ℝ} (hr : 0 < r)
    (h : L2SqDist μ y z < r ^ 2) :
    dist (MemLp.toLp y hy) (MemLp.toLp z hz) < r := by
  have hdist_eq :
      dist (MemLp.toLp y hy) (MemLp.toLp z hz) =
        (eLpNorm (y - z) (2 : ℝ≥0∞) μ).toReal := by
    rw [MeasureTheory.Lp.dist_edist, MeasureTheory.Lp.edist_toLp_toLp]
  rw [hdist_eq, eLpNorm_two_toReal_eq_sqrt_L2SqDist hy hz]
  have hnonneg : 0 ≤ L2SqDist μ y z := by
    unfold L2SqDist
    exact integral_nonneg_of_ae
      (Eventually.of_forall fun ω => sq_nonneg (y ω - z ω))
  exact (Real.sqrt_lt hnonneg (le_of_lt hr)).2 h

theorem cauchySeq_toLp_of_L2SqDist_cauchy_bdd
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {y : ℕ → Ω → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hy_meas : ∀ n, StronglyMeasurable (y n))
    (hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ y n ω)
    (hy_le : ∀ n, ∀ᵐ ω ∂μ, y n ω ≤ M)
    (hCauchy :
      ∀ r : ℝ, 0 < r →
        ∃ N, ∀ n m, N ≤ n → N ≤ m →
          L2SqDist μ (y n) (y m) < r ^ 2) :
    CauchySeq
      (fun n =>
        MemLp.toLp (y n)
          (memLp_two_of_ae_Icc (μ := μ) hM (hy_meas n)
            (hy_nonneg n) (hy_le n) : MemLp (y n) (2 : ℝ≥0∞) μ)) := by
  rw [Metric.cauchySeq_iff]
  intro r hr
  rcases hCauchy r hr with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  exact dist_toLp_two_lt_of_L2SqDist_lt
    (memLp_two_of_ae_Icc (μ := μ) hM (hy_meas m) (hy_nonneg m) (hy_le m))
    (memLp_two_of_ae_Icc (μ := μ) hM (hy_meas n) (hy_nonneg n) (hy_le n))
    hr (hN m n hm hn)

/--
An `L²`-Cauchy bounded sequence has an a.e. convergent subsequence, with the
same interval bounds inherited by the limit.  This is the extraction bridge
needed after the quadratic-utility near-maximizer construction.
-/
theorem exists_subseq_tendstoAE_of_L2SqDist_cauchy_bdd
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {y : ℕ → Ω → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hy_meas : ∀ n, StronglyMeasurable (y n))
    (hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ y n ω)
    (hy_le : ∀ n, ∀ᵐ ω ∂μ, y n ω ≤ M)
    (hCauchy :
      ∀ r : ℝ, 0 < r →
        ∃ N, ∀ n m, N ≤ n → N ≤ m →
          L2SqDist μ (y n) (y m) < r ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ g : Ω → ℝ,
      TendstoAE μ (fun k ω => y (φ k) ω) g ∧
      StronglyMeasurable g ∧
      (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
      (∀ᵐ ω ∂μ, g ω ≤ M) := by
  let p : ℝ≥0∞ := 2
  have hp : Fact (1 ≤ p) := ⟨by dsimp [p]; norm_num⟩
  have hy_mem : ∀ n, MemLp (y n) p μ := by
    intro n
    dsimp [p]
    exact memLp_two_of_ae_Icc (μ := μ) hM (hy_meas n) (hy_nonneg n) (hy_le n)
  let Y : ℕ → Lp ℝ p μ := fun n => MemLp.toLp (y n) (hy_mem n)
  have hY_cauchy : CauchySeq Y := by
    dsimp [Y, p]
    exact cauchySeq_toLp_of_L2SqDist_cauchy_bdd μ hM hy_meas hy_nonneg hy_le hCauchy
  obtain ⟨Ylim, hYlim⟩ := cauchySeq_tendsto_of_complete hY_cauchy
  let g : Ω → ℝ := ((Ylim : Lp ℝ p μ) : Ω → ℝ)
  have hg_meas : StronglyMeasurable g := by
    dsimp [g]
    exact MeasureTheory.Lp.stronglyMeasurable Ylim
  have hInM0 :
      TendstoInMeasure μ
        (fun n => ((Y n : Lp ℝ p μ) : Ω → ℝ))
        atTop g := by
    dsimp [g]
    exact MeasureTheory.tendstoInMeasure_of_tendsto_Lp hYlim
  have hInM : TendstoInMeasure μ y atTop g := by
    refine MeasureTheory.TendstoInMeasure.congr_left ?_ hInM0
    intro n
    dsimp [Y]
    exact MeasureTheory.MemLp.coeFn_toLp (hy_mem n)
  obtain ⟨φ, hφ, hφ_ae⟩ := hInM.exists_seq_tendsto_ae
  have hIcc_seq : ∀ᵐ ω ∂μ, ∀ k, y (φ k) ω ∈ Set.Icc (0 : ℝ) M := by
    refine ae_all_iff.mpr ?_
    intro k
    filter_upwards [hy_nonneg (φ k), hy_le (φ k)] with ω h0 hle
    exact ⟨h0, hle⟩
  have hg_Icc : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc (0 : ℝ) M := by
    filter_upwards [hIcc_seq, hφ_ae] with ω hIcc hlim
    exact (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) M)).mem_of_tendsto
      hlim (Eventually.of_forall hIcc)
  refine ⟨φ, hφ, g, hφ_ae, hg_meas, ?_, ?_⟩
  · filter_upwards [hg_Icc] with ω hω
    exact hω.1
  · filter_upwards [hg_Icc] with ω hω
    exact hω.2

theorem exists_subseq_tendstoAE_of_nearExpSup
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {η : ℕ → ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (nhds 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - η n <
        exponentialUtilityIntegral μ ((w n).apply x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ z : Ω → ℝ,
        TendstoAE μ
          (fun k ω => exponentialTransform ((w (φ k)).apply x ω)) z ∧
        StronglyMeasurable z ∧
        (∀ᵐ ω ∂μ, 0 ≤ z ω) ∧
        (∀ᵐ ω ∂μ, z ω ≤ 1) := by
  let q : ℕ → Ω → ℝ := fun n ω =>
    exponentialTransform ((w n).apply x ω)
  have hq_meas : ∀ n, StronglyMeasurable (q n) := by
    intro n
    dsimp [q, exponentialTransform]
    exact Real.continuous_exp.comp_stronglyMeasurable
      (by
        simpa [div_eq_mul_inv] using
          (((w n).apply_stronglyMeasurable hx_meas).neg.mul_const (1 / 2 : ℝ)))
  have hq_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ q n ω := by
    intro n
    exact Eventually.of_forall fun ω => exponentialTransform_nonneg _
  have hq_le : ∀ n, ∀ᵐ ω ∂μ, q n ω ≤ 1 := by
    intro n
    filter_upwards [(w n).apply_ae_nonneg hx_nonneg] with ω hω
    exact exponentialTransform_le_one hω
  have hCauchy := nearExpSupWeights_L2Cauchy
    (μ := μ) (x := x) (η := η)
    hx_meas hx_nonneg hη_nonneg hη_tendsto w hw_near
  have hCauchy_q :
      ∀ r : ℝ, 0 < r →
        ∃ N, ∀ n m, N ≤ n → N ≤ m →
          L2SqDist μ (q n) (q m) < r ^ 2 := by
    simpa [q] using hCauchy
  obtain ⟨φ, hφ, z, hlim, hz_meas, hz_nonneg, hz_le⟩ :=
    exists_subseq_tendstoAE_of_L2SqDist_cauchy_bdd
      (μ := μ) (y := q) (M := (1 : ℝ))
      (by norm_num) hq_meas hq_nonneg hq_le hCauchy_q
  refine ⟨φ, hφ, z, ?_, hz_meas, hz_nonneg, hz_le⟩
  simpa [q] using hlim

theorem ae_ne_zero_of_exponentialTransform_tendstoAE_of_boundedInProbability
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {y : ℕ → Ω → ℝ} {z : Ω → ℝ}
    (hy_bounded : BoundedInProbability μ y)
    (hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ y n ω)
    (hlim : TendstoAE μ
      (fun n ω => exponentialTransform (y n ω)) z) :
    ∀ᵐ ω ∂μ, z ω ≠ 0 := by
  have hzero : μ {ω | z ω = 0} = 0 := by
    apply le_antisymm
    · refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hε _hεtop
      have hε_real : 0 < (ε : ℝ) := by exact_mod_cast hε
      rcases hy_bounded (ε : ℝ) hε_real with ⟨R, hR, htail⟩
      let E : ℕ → Set Ω := fun n => {ω | R < y n ω}
      let A : ℕ → Set Ω := fun N => ⋂ n, ⋂ (_h : N ≤ n), E n
      have hE : ∀ n, μ (E n) ≤ ENNReal.ofReal (ε : ℝ) := by
        intro n
        have hsub : E n ≤ᵐ[μ] {ω | R < |y n ω|} := by
          filter_upwards [hy_nonneg n] with ω hω htailω
          rw [abs_of_nonneg hω]
          exact htailω
        exact (measure_mono_ae hsub).trans (htail n)
      have hAsub : ∀ N, A N ⊆ E N := by
        intro N ω hω
        dsimp [A] at hω
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hω N) le_rfl
      have hAmono : Monotone A := by
        intro N M hNM
        dsimp [A]
        intro ω hω
        refine Set.mem_iInter.2 ?_
        intro n
        refine Set.mem_iInter.2 ?_
        intro hn
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hω n) (le_trans hNM hn)
      have hAlimit : μ (⋃ N, A N) = ⨆ N, μ (A N) :=
        hAmono.measure_iUnion
      have hA_le : μ (⋃ N, A N) ≤ ENNReal.ofReal (ε : ℝ) := by
        rw [hAlimit]
        exact iSup_le (fun N => (measure_mono (hAsub N)).trans (hE N))
      have hzero_sub : {ω | z ω = 0} ≤ᵐ[μ] ⋃ N, A N := by
        filter_upwards [hlim] with ω hω
        intro hz
        change z ω = 0 at hz
        have hω0 :
            Tendsto (fun n => exponentialTransform (y n ω))
              atTop (nhds 0) := by
          rw [hz] at hω
          exact hω
        have hR_event : ∀ᶠ n in atTop, R < y n ω := by
          have hδ : 0 < exponentialTransform R := by
            unfold exponentialTransform
            positivity
          have hlt := hω0.eventually (Iio_mem_nhds hδ)
          filter_upwards [hlt] with n hn
          have hexp :
              Real.exp (-(y n ω) / 2) < Real.exp (-R / 2) := by
            simpa [exponentialTransform] using hn
          have harg := Real.exp_lt_exp.mp hexp
          linarith
        rcases (eventually_atTop.1 hR_event) with ⟨N, hN⟩
        refine Set.mem_iUnion.2 ⟨N, ?_⟩
        dsimp [A]
        refine Set.mem_iInter.2 ?_
        intro n
        refine Set.mem_iInter.2 ?_
        intro hn
        exact hN n hn
      exact (measure_mono_ae hzero_sub).trans (by simpa using hA_le)
    · exact bot_le
  rw [ae_iff]
  simpa using hzero

theorem tendsto_exponentialTransform_inverse
    {y : ℕ → ℝ} {z : ℝ} (hz : 0 < z)
    (hlim : Tendsto (fun n => exponentialTransform (y n)) atTop (nhds z)) :
    Tendsto y atTop (nhds (-2 * Real.log z)) := by
  have hcomp :
      Tendsto (fun n => -2 * Real.log (exponentialTransform (y n))) atTop
        (nhds (-2 * Real.log z)) :=
    ((Real.continuousAt_log hz.ne').const_mul (-2 : ℝ)).tendsto.comp hlim
  have hsource :
      (fun n => -2 * Real.log (exponentialTransform (y n))) = y := by
    funext n
    simp [exponentialTransform]
    ring
  rw [← hsource]
  exact hcomp

theorem tendstoAE_exponentialTransform_inverse
    {μ : Measure Ω} {y : ℕ → Ω → ℝ} {z : Ω → ℝ}
    (hlim : TendstoAE μ (fun n ω => exponentialTransform (y n ω)) z)
    (hz_pos : ∀ᵐ ω ∂μ, 0 < z ω) :
    TendstoAE μ y (fun ω => -2 * Real.log (z ω)) := by
  filter_upwards [hlim, hz_pos] with ω hω hpos
  exact tendsto_exponentialTransform_inverse hpos hω

theorem hasForwardConvexAELimit_of_nearExpSup_of_boundedInProbability
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {η : ℕ → ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (nhds 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - η n <
        exponentialUtilityIntegral μ ((w n).apply x))
    (hy_bounded :
      BoundedInProbability μ (fun n => (w n).apply x)) :
    HasForwardConvexAELimit μ x := by
  have hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ (w n).apply x ω := by
    intro n
    exact (w n).apply_ae_nonneg hx_nonneg
  obtain ⟨φ, hφ, z, hlim, hz_meas, hz_nonneg, hz_le⟩ :=
    exists_subseq_tendstoAE_of_nearExpSup
      (μ := μ) (x := x) (η := η)
      hx_meas hx_nonneg hη_nonneg hη_tendsto w hw_near
  have hsub_bounded :
      BoundedInProbability μ (fun k => (w (φ k)).apply x) := by
    intro ε hε
    rcases hy_bounded ε hε with ⟨R, hR, htail⟩
    exact ⟨R, hR, fun k => htail (φ k)⟩
  have hsub_nonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ (w (φ k)).apply x ω :=
    fun k => hy_nonneg (φ k)
  have hz_ne : ∀ᵐ ω ∂μ, z ω ≠ 0 :=
    ae_ne_zero_of_exponentialTransform_tendstoAE_of_boundedInProbability
      hsub_bounded hsub_nonneg hlim
  have hz_pos : ∀ᵐ ω ∂μ, 0 < z ω := by
    filter_upwards [hz_ne, hz_nonneg] with ω hne hnonneg
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hyl :
      TendstoAE μ
        (fun k ω => (w (φ k)).apply x ω)
        (fun ω => -2 * Real.log (z ω)) :=
    tendstoAE_exponentialTransform_inverse hlim hz_pos
  let W : ForwardConvexWeights :=
    TailConvexWeights.toForwardReindex φ hφ w
  refine ⟨W, (fun ω => -2 * Real.log (z ω)), ?_⟩
  simpa [W] using hyl

theorem exists_forwardConvexAELimit_with_expUtility_tendsto_of_nearExpSup_of_boundedInProbability
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {η : ℕ → ℝ} {S : ℝ}
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (nhds 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      expTailUtilitySup μ x n - η n <
        exponentialUtilityIntegral μ ((w n).apply x))
    (hy_bounded :
      BoundedInProbability μ (fun n => (w n).apply x))
    (hutility_tendsto :
      Tendsto
        (fun n => exponentialUtilityIntegral μ ((w n).apply x))
        atTop
        (nhds S)) :
    ∃ W : ForwardConvexWeights, ∃ d : Ω → ℝ,
      TendstoAE μ (W.apply x) d ∧
      StronglyMeasurable d ∧
      Tendsto
        (fun n => exponentialUtilityIntegral μ (W.apply x n))
        atTop
        (nhds S) := by
  have hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ (w n).apply x ω := by
    intro n
    exact (w n).apply_ae_nonneg hx_nonneg
  obtain ⟨φ, hφ, z, hlim, hz_meas, hz_nonneg, hz_le⟩ :=
    exists_subseq_tendstoAE_of_nearExpSup
      (μ := μ) (x := x) (η := η)
      hx_meas hx_nonneg hη_nonneg hη_tendsto w hw_near
  have hsub_bounded :
      BoundedInProbability μ (fun k => (w (φ k)).apply x) := by
    intro ε hε
    rcases hy_bounded ε hε with ⟨R, hR, htail⟩
    exact ⟨R, hR, fun k => htail (φ k)⟩
  have hsub_nonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ (w (φ k)).apply x ω :=
    fun k => hy_nonneg (φ k)
  have hz_ne : ∀ᵐ ω ∂μ, z ω ≠ 0 :=
    ae_ne_zero_of_exponentialTransform_tendstoAE_of_boundedInProbability
      hsub_bounded hsub_nonneg hlim
  have hz_pos : ∀ᵐ ω ∂μ, 0 < z ω := by
    filter_upwards [hz_ne, hz_nonneg] with ω hne hnonneg
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hyl :
      TendstoAE μ
        (fun k ω => (w (φ k)).apply x ω)
        (fun ω => -2 * Real.log (z ω)) :=
    tendstoAE_exponentialTransform_inverse hlim hz_pos
  have hutility_sub :
      Tendsto
        (fun k => exponentialUtilityIntegral μ ((w (φ k)).apply x))
        atTop
        (nhds S) :=
    hutility_tendsto.comp hφ.tendsto_atTop
  let W : ForwardConvexWeights :=
    TailConvexWeights.toForwardReindex φ hφ w
  have hlog_meas : StronglyMeasurable (fun ω => Real.log (z ω)) := by
    simpa [Function.comp_def] using
      (Real.measurable_log.stronglyMeasurable.comp_measurable hz_meas.measurable)
  have hd_meas : StronglyMeasurable (fun ω => -2 * Real.log (z ω)) := by
    simpa using hlog_meas.const_mul (-2 : ℝ)
  refine ⟨W, (fun ω => -2 * Real.log (z ω)), ?_, ?_, ?_⟩
  · simpa [W] using hyl
  · exact hd_meas
  · simpa [W] using hutility_sub

theorem exists_aeMaximal_ge_of_strongLimitClosed
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hD_convex : ConvexInvariant D)
    (hD_closed : SequentiallyClosedInMeasureOnStrongLimits μ D)
    (hD_meas : ClaimSetStronglyMeasurable D)
    (hD_bounded : ClaimSetBoundedInProbability μ D)
    (hg_mem : g ∈ D) :
    ∃ h : Ω → ℝ,
      h ∈ D ∧ AEDominatedBy μ g h ∧ AEMaximalIn μ D h := by
  have hg_meas : StronglyMeasurable g := hD_meas g hg_mem
  have hUpper_nonempty : (AEUpperSection μ D g).Nonempty :=
    aeUpperSection_nonempty_of_mem hg_mem
  have hSetBdd :
      BddAbove (aeUpperSectionExponentialUtilityValues μ D g) :=
    aeUpperSectionExponentialUtilityValues_bddAbove hD_meas hg_meas
  let η : ℕ → ℝ := nearError 1
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    simpa [η] using nearError_pos (a := (1 : ℝ)) (by norm_num) n
  have hη_nonneg : ∀ n, 0 ≤ η n := fun n => le_of_lt (hη_pos n)
  have hη_tendsto : Tendsto η atTop (nhds 0) := by
    simpa [η] using tendsto_nearError_zero (a := (1 : ℝ)) (by norm_num)
  obtain ⟨H, hH, hH_near⟩ :=
    exists_near_aeUpperSectionExponentialUtilitySup_sequence
      (μ := μ) (D := D) (g := g) (η := η)
      hUpper_nonempty hη_pos
  let x : ℕ → Ω → ℝ := fun n ω => H n ω - g ω
  have hx_meas : ∀ n, StronglyMeasurable (x n) := by
    intro n
    exact (hD_meas (H n) (hH n).1).sub hg_meas
  have hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω := by
    intro n
    filter_upwards [(hH n).2] with ω hω
    exact sub_nonneg.mpr hω
  obtain ⟨w, hw_near⟩ :=
    exists_near_expTailUtilitySup_weights
      (μ := μ) (x := x) (η := η) hη_pos
  have hTailSup :
      Tendsto (fun n => expTailUtilitySup μ x n) atTop
        (nhds (aeUpperSectionExponentialUtilitySup μ D g)) := by
    simpa [x] using
      (tendsto_expTailUtilitySup_gap_of_nearMaximizingSequence
        (μ := μ) (D := D) (g := g) (H := H) (η := η)
        hD_convex hD_meas hg_meas hH hH_near hη_tendsto)
  have hUtilityW :
      Tendsto
        (fun n => exponentialUtilityIntegral μ ((w n).apply x))
        atTop
        (nhds (aeUpperSectionExponentialUtilitySup μ D g)) :=
    tendsto_aeUpperSection_nearMaximizingWeights_exponentialUtilityIntegral
      (μ := μ) (D := D) (g := g) (H := H) (δ := η) (w := w)
      (S := aeUpperSectionExponentialUtilitySup μ D g)
      hD_meas hg_meas hH hη_nonneg hη_tendsto hTailSup hw_near
  have hWeightedH_mem : ∀ n, (w n).apply H ∈ D := by
    intro n
    have hmem :
        (TailConvexWeights.toForward w).apply H n ∈ D :=
      (TailConvexWeights.toForward w).apply_mem_of_convexInvariant
        hD_convex (fun n => (hH n).1) n
    simpa using hmem
  have hWeightedH_bounded :
      BoundedInProbability μ (fun n => (w n).apply H) :=
    (TerminalGainSequencesBoundedInProbability.of_setBounded
      (μ := μ) (K0 := D) hD_bounded) hWeightedH_mem
  have hg_bounded : BoundedInProbability μ (fun _ : ℕ => g) :=
    BoundedInProbability.const_of_stronglyMeasurable hg_meas
  have hX_bounded' :
      BoundedInProbability μ (fun n ω => (w n).apply H ω - g ω) :=
    BoundedInProbability.sub hWeightedH_bounded hg_bounded
  have hX_bounded :
      BoundedInProbability μ (fun n => (w n).apply x) := by
    have hEq :
        (fun n ω => (w n).apply x ω) =
          (fun n ω => (w n).apply H ω - g ω) := by
      funext n ω
      simpa [x] using congrFun ((w n).apply_sub_constFunction H g) ω
    rw [hEq]
    exact hX_bounded'
  obtain ⟨W, d, hlimX, hd_meas, hUtilityWFinal⟩ :=
    exists_forwardConvexAELimit_with_expUtility_tendsto_of_nearExpSup_of_boundedInProbability
      (μ := μ) (x := x) (η := η)
      hx_meas hx_nonneg hη_nonneg hη_tendsto w hw_near hX_bounded hUtilityW
  have hW_H_mem : ∀ n, W.apply H n ∈ AEUpperSection μ D g := by
    intro n
    exact W.apply_mem_of_convexInvariant
      (hD_convex.aeUpperSection (μ := μ) (D := D) (u := g))
      (fun n => hH n) n
  have hH_meas : ∀ n, StronglyMeasurable (H n) := by
    intro n
    exact hD_meas (H n) (hH n).1
  have hW_H_meas : ∀ n, StronglyMeasurable (W.apply H n) := by
    intro n
    exact W.apply_stronglyMeasurable hH_meas n
  have hlimH :
      TendstoAE μ (W.apply H) (fun ω => d ω + g ω) := by
    have hlim_shift :
        TendstoAE μ (fun n ω => W.apply H n ω - g ω) d := by
      have hlimX' :
          TendstoAE μ
            (W.apply (fun n ω => H n ω - g ω)) d := by
        simpa [x] using hlimX
      rw [W.apply_sub_constFunction H g] at hlimX'
      exact hlimX'
    filter_upwards [hlim_shift] with ω hω
    simpa [sub_add_cancel] using hω.add_const (g ω)
  have hL_meas : StronglyMeasurable (fun ω => d ω + g ω) :=
    hd_meas.add hg_meas
  have hL_mem_D : (fun ω => d ω + g ω) ∈ D :=
    hD_closed (W.apply H) (fun ω => d ω + g ω)
      (fun n => (hW_H_mem n).1)
      hL_meas
      (tendstoInMeasure_of_stronglyMeasurable_tendstoAE hW_H_meas hlimH)
  have hW_x_meas : ∀ n, StronglyMeasurable (W.apply x n) := by
    intro n
    exact W.apply_stronglyMeasurable hx_meas n
  have hW_x_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ W.apply x n ω := by
    intro n
    exact W.apply_ae_nonneg hx_nonneg n
  have hzero : TendstoAE μ (fun _ : ℕ => (fun _ : Ω => 0)) (fun _ : Ω => 0) :=
    Filter.Eventually.of_forall (fun ω => tendsto_const_nhds)
  have hd_nonneg : AEDominatedBy μ (fun _ : Ω => 0) d :=
    AEDominatedBy.limit hzero hlimX (fun n => hW_x_nonneg n)
  have hL_dom : AEDominatedBy μ g (fun ω => d ω + g ω) := by
    filter_upwards [hd_nonneg] with ω hω
    linarith
  have hL_mem :
      (fun ω => d ω + g ω) ∈ AEUpperSection μ D g :=
    ⟨hL_mem_D, hL_dom⟩
  have hUtilityD :
      Tendsto (fun n => exponentialUtilityIntegral μ (W.apply x n)) atTop
        (nhds (exponentialUtilityIntegral μ d)) :=
    tendsto_exponentialUtilityIntegral_of_tendstoAE
      hW_x_meas hW_x_nonneg hlimX
  have hUtilityD_eq_sup :
      exponentialUtilityIntegral μ d =
        aeUpperSectionExponentialUtilitySup μ D g :=
    (tendsto_nhds_unique hUtilityWFinal hUtilityD).symm
  let L : Ω → ℝ := fun ω => d ω + g ω
  have hL_mem' : L ∈ AEUpperSection μ D g := by
    simpa [L] using hL_mem
  have hUtilityL_eq_sup :
      exponentialUtilityIntegral μ (fun ω => L ω - g ω) =
        aeUpperSectionExponentialUtilitySup μ D g := by
    have hEq : (fun ω => L ω - g ω) = d := by
      funext ω
      simp [L]
    rw [hEq]
    exact hUtilityD_eq_sup
  refine ⟨L, hL_mem'.1, hL_mem'.2, ?_⟩
  refine ⟨hL_mem'.1, ?_⟩
  intro k hk hLk
  have hgk : AEDominatedBy μ g k := AEDominatedBy.trans hL_mem'.2 hLk
  have hkUpper : k ∈ AEUpperSection μ D g := ⟨hk, hgk⟩
  have hL_meas' : StronglyMeasurable L := by
    simpa [L] using hL_meas
  have hk_meas : StronglyMeasurable k := hD_meas k hk
  have hL_nonneg : ∀ᵐ ω ∂μ, 0 ≤ L ω - g ω := by
    filter_upwards [hL_mem'.2] with ω hω
    exact sub_nonneg.mpr hω
  have hk_nonneg : ∀ᵐ ω ∂μ, 0 ≤ k ω - g ω := by
    filter_upwards [hgk] with ω hω
    exact sub_nonneg.mpr hω
  have hgap_dom :
      AEDominatedBy μ (fun ω => L ω - g ω) (fun ω => k ω - g ω) := by
    filter_upwards [hLk] with ω hω
    exact sub_le_sub_right hω _
  by_cases hstrict : 0 < μ {ω | L ω < k ω}
  · have hUstrict :
        exponentialUtilityIntegral μ (fun ω => L ω - g ω) <
          exponentialUtilityIntegral μ (fun ω => k ω - g ω) :=
      by
        have hstrict_gap :
            0 < μ {ω | L ω - g ω < k ω - g ω} := by
          simpa only [sub_lt_sub_iff_right] using hstrict
        exact exponentialUtilityIntegral_lt_of_ae_le_of_measure_set_lt_pos
          (hL_meas'.sub (hD_meas g hg_mem))
          (hk_meas.sub (hD_meas g hg_mem))
          hL_nonneg hk_nonneg hgap_dom hstrict_gap
    have hk_le_sup :
        exponentialUtilityIntegral μ (fun ω => k ω - g ω) ≤
          aeUpperSectionExponentialUtilitySup μ D g :=
      aeUpperSectionExponentialUtilitySup_le hSetBdd hkUpper
    exfalso
    linarith [hUstrict, hUtilityL_eq_sup, hk_le_sup]
  · have hzero : μ {ω | L ω < k ω} = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hstrict)
    have hnot : ∀ᵐ ω ∂μ, ¬ L ω < k ω := by
      rw [ae_iff]
      simpa using hzero
    filter_upwards [hLk, hnot] with ω hω hωnot
    exact (le_antisymm hω (le_of_not_gt hωnot)).symm

theorem exists_aeMaximal_ge_of_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hD_convex : ConvexInvariant D)
    (hD_closed : SequentiallyClosedInMeasureOnStrongLimits μ D)
    (hD_meas : ClaimSetAEStronglyMeasurable μ D)
    (hD_bounded : ClaimSetBoundedInProbability μ D)
    (hD_saturated : AESaturated μ D)
    (hg_mem : g ∈ D) :
    ∃ h : Ω → ℝ,
      h ∈ D ∧ AEDominatedBy μ g h ∧ AEMaximalIn μ D h := by
  let Dsm : Set (Ω → ℝ) := StronglyMeasurablePart D
  have hDsm_convex : ConvexInvariant Dsm := by
    simpa [Dsm] using hD_convex.stronglyMeasurablePart
  have hDsm_closed : SequentiallyClosedInMeasureOnStrongLimits μ Dsm := by
    simpa [Dsm] using hD_closed.stronglyMeasurablePart
  have hDsm_meas : ClaimSetStronglyMeasurable Dsm := by
    simpa [Dsm] using
      (claimSetStronglyMeasurable_stronglyMeasurablePart (D := D))
  have hDsm_bounded : ClaimSetBoundedInProbability μ Dsm := by
    simpa [Dsm] using hD_bounded.stronglyMeasurablePart
  let gmk : Ω → ℝ := (hD_meas g hg_mem).mk g
  have hgmk_meas : StronglyMeasurable gmk := by
    dsimp [gmk]
    exact (hD_meas g hg_mem).stronglyMeasurable_mk
  have hggmk : g =ᵐ[μ] gmk := by
    dsimp [gmk]
    exact (hD_meas g hg_mem).ae_eq_mk
  have hgmk_D : gmk ∈ D := hD_saturated hg_mem hggmk
  have hgmk_Dsm : gmk ∈ Dsm := by
    exact ⟨hgmk_D, hgmk_meas⟩
  obtain ⟨h, hh_Dsm, hgm_h, hmax_Dsm⟩ :=
    exists_aeMaximal_ge_of_strongLimitClosed
      (μ := μ) (D := Dsm) (g := gmk)
      hDsm_convex hDsm_closed hDsm_meas hDsm_bounded hgmk_Dsm
  have hh_D : h ∈ D := by
    simpa [Dsm] using hh_Dsm.1
  have hg_h : AEDominatedBy μ g h := by
    filter_upwards [hggmk, hgm_h] with ω hgg hgh
    rw [hgg]
    exact hgh
  have hmax_D : AEMaximalIn μ D h := by
    refine ⟨hh_D, ?_⟩
    intro k hk hhk
    let kmk : Ω → ℝ := (hD_meas k hk).mk k
    have hkkmk : k =ᵐ[μ] kmk := by
      dsimp [kmk]
      exact (hD_meas k hk).ae_eq_mk
    have hkmk_meas : StronglyMeasurable kmk := by
      dsimp [kmk]
      exact (hD_meas k hk).stronglyMeasurable_mk
    have hkmk_D : kmk ∈ D := hD_saturated hk hkkmk
    have hkmk_Dsm : kmk ∈ Dsm := ⟨hkmk_D, hkmk_meas⟩
    have hhk_mk : AEDominatedBy μ h kmk := by
      filter_upwards [hhk, hkkmk] with ω hω heq
      calc
        h ω ≤ k ω := hω
        _ = kmk ω := heq
    have hkmk_h : kmk =ᵐ[μ] h :=
      hmax_Dsm.2 kmk hkmk_Dsm hhk_mk
    filter_upwards [hkkmk, hkmk_h] with ω hkk hkh
    exact hkk.trans hkh
  exact ⟨h, hh_D, hg_h, hmax_D⟩

theorem exists_aeMaximal_ge_inMeasureSequentialClosure_of_mem
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {K : Set (Ω → ℝ)} {g : Ω → ℝ}
    (hK_convex : ConvexInvariant K)
    (hK_meas : ClaimSetAEStronglyMeasurable μ K)
    (hK_bounded : ClaimSetBoundedInProbability μ K)
    (hg_mem : g ∈ InMeasureSequentialClosure μ K) :
    ∃ h : Ω → ℝ,
      h ∈ InMeasureSequentialClosure μ K ∧
        AEDominatedBy μ g h ∧
          AEMaximalIn μ (InMeasureSequentialClosure μ K) h :=
  exists_aeMaximal_ge_of_aestronglyMeasurable
    (μ := μ) (D := InMeasureSequentialClosure μ K) (g := g)
    (convexInvariant_inMeasureSequentialClosure (μ := μ) (K := K) hK_convex)
    (sequentiallyClosedInMeasure_inMeasureSequentialClosure (μ := μ) (K := K)).onStrongLimits
    (claimSetAEStronglyMeasurable_inMeasureSequentialClosure
      (μ := μ) (K := K) hK_meas)
    (claimSetBoundedInProbability_inMeasureSequentialClosure
      (μ := μ) (K := K) hK_bounded)
    (aesaturated_inMeasureSequentialClosure (μ := μ) (K := K))
    hg_mem

theorem forwardConvexLimitAEDominatedBetween_of_maximalInMeasureClosureAERealizable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Ksrc Kdst : Set (Ω → ℝ)}
    (hKsrc_convex : ConvexInvariant Ksrc)
    (hKsrc_meas : ClaimSetAEStronglyMeasurable μ Ksrc)
    (hKsrc_bounded : ClaimSetBoundedInProbability μ Ksrc)
    (hRealize : MaximalInMeasureClosureAERealizableBetween μ Ksrc Kdst) :
    ForwardConvexLimitAEDominatedBetween μ Ksrc Kdst := by
  intro G hG W G_lim hlim
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) μ := by
    intro n
    exact hKsrc_meas (G n) (hG n)
  have hW_meas : ∀ n, AEStronglyMeasurable (W.apply G n) μ := by
    intro n
    exact W.apply_aestronglyMeasurable hG_meas n
  have hG_closure : ∀ n, G n ∈ InMeasureSequentialClosure μ Ksrc := by
    intro n
    exact subset_inMeasureSequentialClosure (μ := μ) (K := Ksrc) (hG n)
  have hW_closure : ∀ n, W.apply G n ∈ InMeasureSequentialClosure μ Ksrc := by
    intro n
    exact W.apply_mem_of_convexInvariant
      (convexInvariant_inMeasureSequentialClosure
        (μ := μ) (K := Ksrc) hKsrc_convex)
      hG_closure n
  have hlim_measure : MeasureTheory.TendstoInMeasure μ (W.apply G) atTop G_lim :=
    tendstoInMeasure_of_tendstoAE
      (μ := μ) hW_meas hlim
  have hG_lim_closure : G_lim ∈ InMeasureSequentialClosure μ Ksrc :=
    sequentiallyClosedInMeasure_inMeasureSequentialClosure
      (μ := μ) (K := Ksrc) (W.apply G) G_lim hW_closure hlim_measure
  obtain ⟨h, hh_closure, hdom, hmax⟩ :=
    exists_aeMaximal_ge_inMeasureSequentialClosure_of_mem
      (μ := μ) (K := Ksrc) (g := G_lim)
      hKsrc_convex hKsrc_meas hKsrc_bounded hG_lim_closure
  obtain ⟨G_rep, hG_rep, hEq⟩ := hRealize hh_closure hmax
  refine ⟨G_rep, hG_rep, ?_⟩
  filter_upwards [hdom, hEq] with ω hdomω hEqω
  calc
    G_lim ω ≤ h ω := hdomω
    _ = G_rep ω := hEqω

/-!
The positive-tail extraction applies directly to nonnegative sequences.  The
following bridge handles the common situation where the sequence is only
uniformly lower bounded: shift it into the nonnegative cone, use a uniformly
bounded claim set to retain boundedness after the selected convexification,
then shift the extracted limit back.
-/
theorem hasForwardConvexAELimit_of_lowerBounded_convexSet
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : ℕ → Ω → ℝ} {D : Set (Ω → ℝ)} {a : ℝ}
    (hG_meas : ∀ n, StronglyMeasurable (G n))
    (hG_lower : ∀ n, AELowerBoundedBy μ (-a) (G n))
    (hD_convex : ConvexInvariant D)
    (hD_bounded : ClaimSetBoundedInProbability μ D)
    (hG_mem : ∀ n, G n ∈ D) :
    HasForwardConvexAELimit μ G := by
  let x : ℕ → Ω → ℝ := fun n ω => G n ω + a
  have hx_meas : ∀ n, StronglyMeasurable (x n) := by
    intro n
    change StronglyMeasurable (G n + fun _ => a)
    exact (hG_meas n).add stronglyMeasurable_const
  have hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω := by
    intro n
    filter_upwards [hG_lower n] with ω hω
    dsimp [x]
    linarith
  let η : ℕ → ℝ := nearError 1
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    simpa [η] using nearError_pos (a := (1 : ℝ)) (by norm_num) n
  have hη_nonneg : ∀ n, 0 ≤ η n := fun n => le_of_lt (hη_pos n)
  have hη_tendsto : Tendsto η atTop (nhds 0) := by
    simpa [η] using tendsto_nearError_zero (a := (1 : ℝ)) (by norm_num)
  obtain ⟨w, hw_near⟩ :=
    exists_near_expTailUtilitySup_weights
      (μ := μ) (x := x) (η := η) hη_pos
  have hsel_mem : ∀ n, (w n).apply G ∈ D := by
    intro n
    have hmem :
        (TailConvexWeights.toForward w).apply G n ∈ D :=
      (TailConvexWeights.toForward w).apply_mem_of_convexInvariant
        hD_convex hG_mem n
    simpa using hmem
  have hsel_bounded :
      BoundedInProbability μ (fun n => (w n).apply G) := by
    exact
      (TerminalGainSequencesBoundedInProbability.of_setBounded
        (μ := μ) (K0 := D) hD_bounded) hsel_mem
  have hshift_bounded :
      BoundedInProbability μ (fun n => (w n).apply x) := by
    have hadd := BoundedInProbability.add_const
      (μ := μ) (G := fun n => (w n).apply G) (c := a) hsel_bounded
    have hEq :
        (fun n ω => (w n).apply x ω) =
          (fun n ω => (w n).apply G ω + a) := by
      funext n ω
      simpa [x] using congrFun ((w n).apply_add_const G a) ω
    rw [hEq]
    exact hadd
  have hlim_shift : HasForwardConvexAELimit μ x :=
    hasForwardConvexAELimit_of_nearExpSup_of_boundedInProbability
      (μ := μ) (x := x) (η := η)
      hx_meas hx_nonneg hη_nonneg hη_tendsto w hw_near hshift_bounded
  apply HasForwardConvexAELimit.shiftBack_const (G := G) (c := a)
  simpa [x] using hlim_shift

/-- The lower-bounded convex-set extraction only needs a.e. strongly
measurable claims when the ambient claim set is saturated under a.e.
equality.  Strongly measurable representatives are selected termwise, the
existing extraction is applied to those representatives, and the resulting
finite convex combinations are transferred back to the original sequence. -/
theorem hasForwardConvexAELimit_of_lowerBounded_convexSet_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : ℕ → Ω → ℝ} {D : Set (Ω → ℝ)} {a : ℝ}
    (hG_meas : ∀ n, AEStronglyMeasurable (G n) μ)
    (hG_lower : ∀ n, AELowerBoundedBy μ (-a) (G n))
    (hD_convex : ConvexInvariant D)
    (hD_bounded : ClaimSetBoundedInProbability μ D)
    (hD_saturated : AESaturated μ D)
    (hG_mem : ∀ n, G n ∈ D) :
    HasForwardConvexAELimit μ G := by
  let G' : ℕ → Ω → ℝ := fun n => (hG_meas n).mk (G n)
  have hGG' : ∀ n, G n =ᵐ[μ] G' n := fun n => (hG_meas n).ae_eq_mk
  have hG'_meas : ∀ n, StronglyMeasurable (G' n) := fun n =>
    (hG_meas n).stronglyMeasurable_mk
  have hG'_lower : ∀ n, AELowerBoundedBy μ (-a) (G' n) := by
    intro n
    filter_upwards [hG_lower n, hGG' n] with ω hLower hEq
    rwa [← hEq]
  have hG'_mem : ∀ n, G' n ∈ D := fun n =>
    hD_saturated (hG_mem n) (hGG' n)
  obtain ⟨W, g, hlim⟩ :=
    hasForwardConvexAELimit_of_lowerBounded_convexSet
      (μ := μ) (G := G') (D := D) (a := a)
      hG'_meas hG'_lower hD_convex hD_bounded hG'_mem
  refine ⟨W, g, ?_⟩
  have hAll : ∀ᵐ ω ∂μ, ∀ n, G n ω = G' n ω :=
    ae_all_iff.mpr hGG'
  filter_upwards [hlim, hAll] with ω hlimω hEqω
  have hApply :
      (fun n => W.apply G n ω) = (fun n => W.apply G' n ω) := by
    funext n
    simp only [ForwardConvexWeights.apply]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hEqω i]
  rw [hApply]
  exact hlimω

theorem tendsto_utilityIntegral_of_tendstoAE_bdd
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {y : ℕ → Ω → ℝ} {g : Ω → ℝ} {M : ℝ}
    (_hM : 0 ≤ M)
    (hy_meas : ∀ n, StronglyMeasurable (y n))
    (hy_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ y n ω)
    (hy_le : ∀ n, ∀ᵐ ω ∂μ, y n ω ≤ M)
    (hlim : TendstoAE μ y g) :
    Tendsto
      (fun n => utilityIntegral μ M (y n))
      atTop
      (nhds (utilityIntegral μ M g)) := by
  unfold utilityIntegral
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun ω => quadraticUtility M (y n ω)) μ := by
    intro n
    unfold quadraticUtility
    fun_prop
  have hbound_int : Integrable (fun _ : Ω => M ^ 2) μ :=
    integrable_const _
  have hbound :
      ∀ n, ∀ᵐ ω ∂μ,
        ‖quadraticUtility M (y n ω)‖ ≤ (fun _ : Ω => M ^ 2) ω := by
    intro n
    filter_upwards [hy_nonneg n, hy_le n] with ω h0 hle
    have hM_nonneg : 0 ≤ M := le_trans h0 hle
    have hu_nonneg :=
      quadraticUtility_nonneg_of_mem_Icc hM_nonneg
        (show y n ω ∈ Set.Icc (0 : ℝ) M from ⟨h0, hle⟩)
    have hu_le :=
      quadraticUtility_le_M_sq_of_mem_Icc
        (show y n ω ∈ Set.Icc (0 : ℝ) M from ⟨h0, hle⟩)
    simpa [Real.norm_eq_abs, abs_of_nonneg hu_nonneg] using hu_le
  have hcont : Continuous (quadraticUtility M) := by
    unfold quadraticUtility
    fun_prop
  have hlim_u :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => quadraticUtility M (y n ω))
          atTop
          (nhds (quadraticUtility M (g ω))) := by
    filter_upwards [hlim] with ω hω
    exact (hcont.tendsto (g ω)).comp hω
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => M ^ 2) hF_meas hbound_int hbound hlim_u

theorem pos_measure_pos_of_utilityIntegral_pos
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : Ω → ℝ} {M : ℝ}
    (_hM : 0 < M)
    (_hg_meas : StronglyMeasurable g)
    (hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (_hg_le : ∀ᵐ ω ∂μ, g ω ≤ M)
    (hJ_pos : 0 < utilityIntegral μ M g) :
    0 < μ {ω | 0 < g ω} := by
  by_contra hnot
  have hμ_zero : μ {ω | 0 < g ω} = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  have hnot_pos : ∀ᵐ ω ∂μ, ¬ 0 < g ω := by
    rw [ae_iff]
    simpa using hμ_zero
  have hg_zero : ∀ᵐ ω ∂μ, g ω = 0 := by
    filter_upwards [hg_nonneg, hnot_pos] with ω h0 hnp
    exact le_antisymm (le_of_not_gt hnp) h0
  have hJ_zero : utilityIntegral μ M g = 0 := by
    unfold utilityIntegral
    rw [integral_eq_zero_of_ae]
    filter_upwards [hg_zero] with ω hω
    simp [quadraticUtility, hω]
  nlinarith

/-!
### Finite truncation-level diagonalization

The next lemma is the finite-level consistency step for the general `L¹`
Komlós argument.  At each induction step we extract the next bounded
truncation from the already extracted sequence and compose the two forward
weight systems.  Thus one weight system handles every truncation level up to
the prescribed finite level; no boundedness of the original (untruncated)
sequence is assumed.
-/

theorem forwardConvex_tendstoAE_pos_of_bdd_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {x : ℕ → Ω → ℝ} {M ε c : ℝ}
    (hM : 0 < M)
    (hc : 0 < c)
    (hcM : c ≤ M)
    (hε : 0 < ε)
    (hx_meas : ∀ n, StronglyMeasurable (x n))
    (hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω)
    (hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M)
    (hmass : ∀ n, ENNReal.ofReal ε < μ {ω | c < x n ω}) :
    ∃ W : ForwardConvexWeights, ∃ g : Ω → ℝ,
      TendstoAE μ (W.apply x) g ∧
      StronglyMeasurable g ∧
      (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
      (∀ᵐ ω ∂μ, g ω ≤ M) ∧
      0 < μ {ω | 0 < g ω} := by
  let a : ℝ := quadraticUtility M c * ε
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (quadraticUtility_pos_of_mem_Ioc hM ⟨hc, hcM⟩) hε
  let η : ℕ → ℝ := nearError a
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    exact nearError_pos ha n
  obtain ⟨w, hw_near⟩ :=
    exists_nearSupWeights (μ := μ) (x := x) (M := M) hη_pos
  have hη_nonneg : ∀ n, 0 ≤ η n := fun n => le_of_lt (hη_pos n)
  have hη_tendsto : Tendsto η atTop (nhds 0) := by
    simpa [η] using tendsto_nearError_zero (a := a) ha
  have hCauchy := nearSupWeights_L2Cauchy
    (μ := μ) (x := x) (M := M) (η := η)
    (le_of_lt hM) hx_meas hx_nonneg hx_le hη_nonneg hη_tendsto w hw_near
  obtain ⟨φ, hφ, g, hlim, hg_meas, hg_nonneg, hg_le⟩ :=
    exists_subseq_tendstoAE_of_L2SqDist_cauchy_bdd
      (μ := μ) (M := M) (le_of_lt hM)
      (fun n => (w n).apply_stronglyMeasurable hx_meas)
      (fun n => (w n).apply_ae_nonneg hx_nonneg)
      (fun n => (w n).apply_ae_le hx_le)
      hCauchy
  have hS_lower : ∀ n, a < convTailUtilitySup μ x M n := by
    simpa [a] using
      convTailUtilitySup_pos_lower
        (μ := μ) (x := x) (M := M) (ε := ε) (c := c)
        hM hc hcM hε hx_meas hx_nonneg hx_le hmass
  have hJ_lower :
      ∀ n, a / 2 < utilityIntegral μ M ((w n).apply x) :=
    nearSupWeights_utilityIntegral_pos_lower
      (S := fun n => convTailUtilitySup μ x M n)
      (J := fun n => utilityIntegral μ M ((w n).apply x))
      (η := η) ha hS_lower
      (by
        intro n
        simpa [η] using nearError_le_half (a := a) n)
      hw_near
  have hJ_tendsto :
      Tendsto
        (fun k => utilityIntegral μ M ((w (φ k)).apply x))
        atTop
        (nhds (utilityIntegral μ M g)) :=
    tendsto_utilityIntegral_of_tendstoAE_bdd
      (μ := μ) (M := M) (le_of_lt hM)
      (fun k => (w (φ k)).apply_stronglyMeasurable hx_meas)
      (fun k => (w (φ k)).apply_ae_nonneg hx_nonneg)
      (fun k => (w (φ k)).apply_ae_le hx_le)
      hlim
  have hJ_ge : a / 2 ≤ utilityIntegral μ M g :=
    ge_of_tendsto hJ_tendsto
      (Eventually.of_forall fun k => le_of_lt (hJ_lower (φ k)))
  have hJ_pos : 0 < utilityIntegral μ M g := by
    have : 0 < a / 2 := by positivity
    exact lt_of_lt_of_le this hJ_ge
  have hg_pos : 0 < μ {ω | 0 < g ω} :=
    pos_measure_pos_of_utilityIntegral_pos
      (μ := μ) (M := M) hM hg_meas hg_nonneg hg_le hJ_pos
  let W : ForwardConvexWeights := TailConvexWeights.toForwardReindex φ hφ w
  refine ⟨W, g, ?_, hg_meas, hg_nonneg, hg_le, hg_pos⟩
  simpa [W] using hlim

def shiftedNonneg
    (f : ℕ → Ω → ℝ) (δ : ℕ → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => max 0 (f n ω + δ n)

theorem shiftedNonneg_stronglyMeasurable
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hf_meas : ∀ n, StronglyMeasurable (f n)) :
    ∀ n, StronglyMeasurable (shiftedNonneg f δ n) := by
  intro n
  unfold shiftedNonneg
  fun_prop

theorem shiftedNonneg_nonneg
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ} :
    ∀ n, ∀ᵐ ω ∂(μ : Measure Ω), 0 ≤ shiftedNonneg f δ n ω := by
  intro n
  exact Eventually.of_forall fun ω => le_max_left _ _

theorem shiftedNonneg_le
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hδ_anti : Antitone δ)
    (hf_le : ∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) :
    ∀ n, ∀ᵐ ω ∂μ, shiftedNonneg f δ n ω ≤ 1 + δ 0 := by
  intro n
  filter_upwards [hf_le n] with ω hle
  have hδn : δ n ≤ δ 0 := hδ_anti (Nat.zero_le n)
  have hsum : f n ω + δ n ≤ 1 + δ 0 := by linarith
  have hzero : (0 : ℝ) ≤ 1 + δ 0 := by
    have hδ0 := hδ_nonneg 0
    linarith
  unfold shiftedNonneg
  exact max_le hzero hsum

theorem shiftedNonneg_gt_half_mass
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ} {ε : ℝ}
    (hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hmass : ∀ n,
      ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) :
    ∀ n,
      ENNReal.ofReal ε <
        μ {ω | (1 / 2 : ℝ) < shiftedNonneg f δ n ω} := by
  intro n
  refine lt_of_lt_of_le (hmass n) (measure_mono ?_)
  intro ω hω
  unfold shiftedNonneg
  have hδn := hδ_nonneg n
  have hfhalf : (1 / 2 : ℝ) < f n ω := hω
  have hlt : (1 / 2 : ℝ) < f n ω + δ n := by linarith
  exact lt_of_lt_of_le hlt (le_max_right _ _)

theorem shiftedNonneg_eq_add_ae
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hf_lower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) :
    ∀ n,
      shiftedNonneg f δ n =ᵐ[μ] fun ω => f n ω + δ n := by
  intro n
  filter_upwards [hf_lower n] with ω hlow
  have hnonneg : 0 ≤ f n ω + δ n := by linarith
  unfold shiftedNonneg
  exact max_eq_right hnonneg

namespace ForwardConvexWeights

def applyScalar (W : ForwardConvexWeights) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => ∑ i ∈ W.support n, W.weight n i * a i

theorem tendsto_applyScalar
    (W : ForwardConvexWeights) {a : ℕ → ℝ} {b : ℝ}
    (ha : Tendsto a atTop (nhds b)) :
    Tendsto (W.applyScalar a) atTop (nhds b) := by
  change Tendsto
    (fun n => ∑ i ∈ W.support n, W.weight n i * a i) atTop (nhds b)
  exact W.tendsto_apply_real ha

theorem apply_shiftedNonneg_eq_add_scalar_ae
    (W : ForwardConvexWeights)
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hf_lower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) :
    ∀ᵐ ω ∂μ, ∀ n,
      W.apply (shiftedNonneg f δ) n ω =
        W.apply f n ω + W.applyScalar δ n := by
  have hshift_all :
      ∀ᵐ ω ∂μ, ∀ i, shiftedNonneg f δ i ω = f i ω + δ i :=
    ae_all_iff.mpr (shiftedNonneg_eq_add_ae (μ := μ) (f := f) (δ := δ) hf_lower)
  filter_upwards [hshift_all] with ω hω n
  unfold ForwardConvexWeights.apply applyScalar
  calc
    ∑ i ∈ W.support n, W.weight n i * shiftedNonneg f δ i ω
        = ∑ i ∈ W.support n, W.weight n i * (f i ω + δ i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hω i]
    _ = (∑ i ∈ W.support n, W.weight n i * f i ω) +
          ∑ i ∈ W.support n, W.weight n i * δ i := by
            simp [mul_add, Finset.sum_add_distrib]

theorem tendstoAE_apply_of_tendstoAE_shiftedNonneg
    (W : ForwardConvexWeights)
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ} {g : Ω → ℝ}
    (hf_lower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n))
    (hδ : Tendsto δ atTop (nhds 0))
    (hx_lim : TendstoAE μ (W.apply (shiftedNonneg f δ)) g) :
    TendstoAE μ (W.apply f) g := by
  have hshift := W.apply_shiftedNonneg_eq_add_scalar_ae
    (μ := μ) (f := f) (δ := δ) hf_lower
  have hscalar : Tendsto (W.applyScalar δ) atTop (nhds 0) :=
    W.tendsto_applyScalar hδ
  filter_upwards [hx_lim, hshift] with ω hxω hω
  have hsub :
      Tendsto
        (fun n => W.apply (shiftedNonneg f δ) n ω - W.applyScalar δ n)
        atTop (nhds (g ω - 0)) :=
    hxω.sub hscalar
  have hfun :
      (fun n => W.apply f n ω) =
        fun n => W.apply (shiftedNonneg f δ) n ω - W.applyScalar δ n := by
    funext n
    have hn := hω n
    linarith
  simpa [hfun] using hsub

end ForwardConvexWeights

/--
The minimal a.e.-limit extraction target used by the bounded/truncated
Komlós-lite route.  Bounds on the limit are consequences of the vanishing lower
risk and the uniform upper bound, so this target only asks for convergence,
measurability, and survival of positive mass.
-/
def KomlosLiteAELimitExtractionStrong (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ f : ℕ → Ω → ℝ,
      ∀ δ : ℕ → ℝ,
        (∀ n, 0 ≤ δ n) →
          (∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) →
            (∀ n, StronglyMeasurable (f n)) →
              (∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) →
                Antitone δ →
                  Tendsto δ atTop (nhds 0) →
                    (∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) →
                      ∃ W : ForwardConvexWeights,
                        ∃ g : Ω → ℝ,
                          TendstoAE μ (W.apply f) g ∧
                          StronglyMeasurable g ∧
                          0 < μ {ω | 0 < g ω}

theorem KomlosLiteAELimitExtractionStrong.of_bdd_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ] :
    KomlosLiteAELimitExtractionStrong μ := by
  intro ε hε f δ hδnonneg hlower hfmeas hfupper hδmono hδtendsto hmass
  let x : ℕ → Ω → ℝ := shiftedNonneg f δ
  let M : ℝ := 1 + δ 0
  have hM : 0 < M := by
    have hδ0 := hδnonneg 0
    dsimp [M]
    linarith
  have hc : 0 < (1 / 2 : ℝ) := by norm_num
  have hcM : (1 / 2 : ℝ) ≤ M := by
    have hδ0 := hδnonneg 0
    dsimp [M]
    linarith
  have hx_meas : ∀ n, StronglyMeasurable (x n) :=
    shiftedNonneg_stronglyMeasurable (f := f) (δ := δ) hfmeas
  have hx_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ x n ω :=
    shiftedNonneg_nonneg (μ := μ) (f := f) (δ := δ)
  have hx_le : ∀ n, ∀ᵐ ω ∂μ, x n ω ≤ M := by
    simpa [x, M] using
      shiftedNonneg_le (μ := μ) (f := f) (δ := δ)
        hδnonneg hδmono hfupper
  have hx_mass :
      ∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < x n ω} := by
    simpa [x] using
      shiftedNonneg_gt_half_mass (μ := μ) (f := f) (δ := δ)
        hδnonneg hmass
  rcases forwardConvex_tendstoAE_pos_of_bdd_nonneg
      (μ := μ) (x := x) (M := M) (ε := ε) (c := (1 / 2 : ℝ))
      hM hc hcM hε hx_meas hx_nonneg hx_le hx_mass with
    ⟨W, g, hxlim, hgmeas, _hgnonneg, _hgle, hgpos⟩
  have hlim : TendstoAE μ (W.apply f) g :=
    W.tendstoAE_apply_of_tendstoAE_shiftedNonneg
      (μ := μ) (f := f) (δ := δ) hlower hδtendsto hxlim
  exact ⟨W, g, hlim, hgmeas, hgpos⟩

theorem KomlosLiteAELimitExtractionStrong.of_finiteMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ] :
    KomlosLiteAELimitExtractionStrong μ :=
  KomlosLiteAELimitExtractionStrong.of_bdd_nonneg

theorem KomlosLiteExtractionStrong.of_aeLimitExtraction
    {μ : Measure Ω}
    (hExtract : KomlosLiteAELimitExtractionStrong μ) :
    KomlosLiteExtractionStrong μ := by
  intro ε hε f δ hδnonneg hlower hfmeas hfupper hδmono hδtendsto hmass
  rcases hExtract ε hε f δ hδnonneg hlower hfmeas hfupper hδmono
      hδtendsto hmass with
    ⟨W, g, hlim, hgmeas, hgpos⟩
  have hWlower : ∀ n, AELowerBoundedBy μ (-(δ n)) (W.apply f n) := fun n =>
    W.apply_aeLowerBounded_of_antitone hδmono hlower n
  have hWupper : ∀ n, ∀ᵐ ω ∂μ, W.apply f n ω ≤ 1 := fun n =>
    W.apply_aeUpperBounded_one hfupper n
  have hgnonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω :=
    hlim.nonnegative_of_vanishing_lower hδtendsto hWlower
  have hgle_one : ∀ᵐ ω ∂μ, g ω ≤ 1 :=
    AEDominatedBy.limit_const hlim hWupper
  exact ⟨W, g, hlim, hgmeas, hgnonneg, hgle_one, hgpos⟩

theorem KomlosLiteVanishingRiskPositiveMassStrong.of_extraction
    {μ : Measure Ω}
    (hExtract : KomlosLiteExtractionStrong μ) :
    KomlosLiteVanishingRiskPositiveMassStrong μ := by
  intro ε hε f δ hδnonneg hlower hfmeas hfupper hδmono hδtendsto hmass
  rcases hExtract ε hε f δ hδnonneg hlower hfmeas hfupper hδmono
      hδtendsto hmass with
    ⟨W, g, hlim, hgmeas, hgnonneg, hgle_one, hgpos⟩
  exact ⟨W, g, hlim, hgmeas,
    fun n => W.apply_aeLowerBounded_of_antitone hδmono hlower n,
    fun n => W.apply_aeUpperBounded_one hfupper n,
    hgnonneg, hgle_one, hgpos⟩

theorem KomlosLiteVanishingRiskPositiveMassStrong.of_aeLimitExtraction
    {μ : Measure Ω}
    (hExtract : KomlosLiteAELimitExtractionStrong μ) :
    KomlosLiteVanishingRiskPositiveMassStrong μ :=
  KomlosLiteVanishingRiskPositiveMassStrong.of_extraction
    (KomlosLiteExtractionStrong.of_aeLimitExtraction hExtract)

theorem KomlosLiteVanishingRiskPositiveMassStrong.of_finiteMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ] :
    KomlosLiteVanishingRiskPositiveMassStrong μ :=
  KomlosLiteVanishingRiskPositiveMassStrong.of_aeLimitExtraction
    (KomlosLiteAELimitExtractionStrong.of_finiteMeasure (μ := μ))

theorem KomlosLiteVanishingRiskPositiveMass.of_strong
    {μ : Measure Ω}
    (hStrong : KomlosLiteVanishingRiskPositiveMassStrong μ) :
    KomlosLiteVanishingRiskPositiveMass μ := by
  intro ε hε f δ hlower hfmeas hfupper hδmono hδtendsto hmass
  let f' : ℕ → Ω → ℝ := fun n => (hfmeas n).mk (f n)
  let δ' : ℕ → ℝ := fun n => max (δ n) 0
  have hfEq : ∀ n, f n =ᵐ[μ] f' n := fun n =>
    (hfmeas n).ae_eq_mk
  have hδnonneg : ∀ n, 0 ≤ δ' n := by
    intro n
    exact le_max_right (δ n) 0
  have hlower' : ∀ n, AELowerBoundedBy μ (-(δ' n)) (f' n) := by
    intro n
    filter_upwards [hlower n, hfEq n] with ω hlow hω
    have hδle : δ n ≤ δ' n := le_max_left (δ n) 0
    have hneg : -(δ' n) ≤ -(δ n) := neg_le_neg hδle
    rw [← hω]
    exact le_trans hneg hlow
  have hfstrong : ∀ n, StronglyMeasurable (f' n) := fun n =>
    (hfmeas n).stronglyMeasurable_mk
  have hfupper' : ∀ n, ∀ᵐ ω ∂μ, f' n ω ≤ 1 := by
    intro n
    filter_upwards [hfupper n, hfEq n] with ω hupper hω
    rw [← hω]
    exact hupper
  have hδmono' : Antitone δ' := by
    intro m n hmn
    exact max_le_max (hδmono hmn) le_rfl
  have hδtendsto' : Tendsto δ' atTop (nhds 0) := by
    have h := hδtendsto.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa [δ'] using h
  have hmass' : ∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f' n ω} := by
    intro n
    have hmono :
        μ {ω | (1 / 2 : ℝ) < f n ω} ≤
          μ {ω | (1 / 2 : ℝ) < f' n ω} := by
      exact measure_mono_ae <| (hfEq n).mono fun ω hω hlt => by
        change (1 / 2 : ℝ) < f' n ω
        rw [← hω]
        exact hlt
    exact lt_of_lt_of_le (hmass n) hmono
  rcases hStrong ε hε f' δ' hδnonneg hlower' hfstrong hfupper'
      hδmono' hδtendsto' hmass' with
    ⟨W, g, hlim', hgmeas, _hWlower', _hWupper',
      hgnonneg, hgle_one, hgpos⟩
  have hW_eq : ∀ n, W.apply f n =ᵐ[μ] W.apply f' n := by
    intro n
    have hfEq_all : ∀ᵐ ω ∂μ, ∀ i, f i ω = f' i ω :=
      ae_all_iff.mpr hfEq
    filter_upwards [hfEq_all] with ω hω
    simp [ForwardConvexWeights.apply, hω]
  have hlim : TendstoAE μ (W.apply f) g := by
    have hW_eq_all : ∀ᵐ ω ∂μ, ∀ n, W.apply f n ω = W.apply f' n ω :=
      ae_all_iff.mpr hW_eq
    filter_upwards [hlim', hW_eq_all] with ω hlimω hω
    have hfun : (fun n => W.apply f n ω) = fun n => W.apply f' n ω := by
      funext n
      exact hω n
    rw [hfun]
    exact hlimω
  refine ⟨W, g, hlim, hgmeas.aestronglyMeasurable, ?_, ?_,
    hgnonneg, hgle_one, hgpos⟩
  · intro n
    exact W.apply_aeLowerBounded_of_antitone hδmono hlower n
  · intro n
    exact W.apply_aeUpperBounded_one hfupper n

end FTAPTheorem42
