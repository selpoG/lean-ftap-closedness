import FTAPTheorem42.PositiveTail

/-!
# The vanishing-risk contradiction supplied by NFLVR

This module packages the analytic Komlós--Egorov construction as the terminal
contradiction used in the stochastic proof of Lemma 4.7.  It first proves the
normalized contradiction, then removes the upper bound, distinguished positive
level, monotonicity of the downside bounds, and an initial finite exceptional
set of indices.
-/

open Filter MeasureTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/--
A real sequence converging to zero admits a strictly increasing subsequence
lying below any prescribed positive error schedule.
-/
theorem exists_strictMono_subsequence_lt_of_tendsto_zero
    {δ r : ℕ → ℝ}
    (hδZero : Tendsto δ atTop (nhds 0))
    (hrPositive : ∀ n, 0 < r n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, δ (φ n) < r n := by
  have hEventually : ∀ n, ∀ᶠ m in atTop, δ m < r n := by
    intro n
    exact hδZero (Iio_mem_nhds (hrPositive n))
  choose witness hwitness using fun n => eventually_atTop.1 (hEventually n)
  let φ : ℕ → ℕ := fun n =>
    Nat.rec (witness 0)
      (fun k previous => max (previous + 1) (witness (k + 1))) n
  have hwitness_le : ∀ n, witness n ≤ φ n := by
    intro n
    induction n with
    | zero =>
        simp [φ]
    | succ n _ =>
        dsimp [φ]
        exact le_max_right _ _
  have hφStep : ∀ n, φ n < φ (n + 1) := by
    intro n
    dsimp [φ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφStrict : StrictMono φ :=
    strictMono_nat_of_lt_succ hφStep
  refine ⟨φ, hφStrict, ?_⟩
  intro n
  exact hwitness n (φ n) (hwitness_le n)

/--
NFLVR rules out a normalized vanishing-risk sequence in a solid claim cone.

The proof applies the finite-measure Komlós extraction and the Egorov
construction to obtain a nonzero nonnegative element in the `L∞` norm closure,
contradicting `LinftyNFLVR`.
-/
theorem not_vanishingRiskPositiveMass_of_linfyNFLVR
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hC0Cone : ClaimCone C0)
    (hC0Solid : Solid μ C0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ C0))
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hfC0 : ∀ n, f n ∈ C0)
    (hfMeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfLower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n))
    (hfUpper : ∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1)
    (hδAnti : Antitone δ)
    (hδZero : Tendsto δ atTop (nhds 0))
    (hfMass :
      ∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < f n ω}) :
    False := by
  have hAnalytic :
      VanishingRiskPositiveMassSequenceProducesLinftyLimit μ C0 :=
    vanishingRiskPositiveMassSequenceProducesLinftyLimit_of_komlosLite_and_egorov
      hC0Cone
      (KomlosLiteVanishingRiskPositiveMass.of_strong
        (KomlosLiteVanishingRiskPositiveMassStrong.of_finiteMeasure (μ := μ)))
      (egorovVanishingRiskToLinftyNormLimit_of_core hC0Solid)
  rcases hAnalytic ε hε f δ hfC0 hfMeas hfLower hfUpper hδAnti hδZero
      hfMass with
    ⟨U, F, hU, hUF, hFNonnegative, hFNe⟩
  have hFClosure : F ∈ closure (LinftyClaims μ C0) :=
    mem_closure_of_tendsto_atTop hU hUF
  have hFZero : F = 0 :=
    (linftyNFLVR_iff.mp hNFLVR) F hFClosure hFNonnegative
  exact hFNe hFZero

/--
Scale- and truncation-invariant form of the vanishing-risk contradiction.

No upper bound or distinguished positive level is required.  If a fixed
positive mass remains above any fixed level `η > 0`, scaling by `(2 * η)⁻¹`
and truncating from above at one reduces the sequence to the normalized
contradiction above.
-/
theorem not_vanishingRiskPositiveLevel_of_linfyNFLVR
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hC0Cone : ClaimCone C0)
    (hC0Solid : Solid μ C0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ C0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hfC0 : ∀ n, f n ∈ C0)
    (hfMeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfLower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n))
    (hδAnti : Antitone δ)
    (hδZero : Tendsto δ atTop (nhds 0))
    (hfMass : ∀ n, ENNReal.ofReal ε < μ {ω | η < f n ω}) :
    False := by
  let c : ℝ := (2 * η)⁻¹
  let g : ℕ → Ω → ℝ := fun n ω => min (c * f n ω) 1
  let δ' : ℕ → ℝ := fun n => c * δ n
  have hcPositive : 0 < c := by
    dsimp [c]
    positivity
  have hcNonnegative : 0 ≤ c := hcPositive.le
  have hcMul : c * (2 * η) = 1 := by
    dsimp [c]
    exact inv_mul_cancel₀ (by positivity)
  have hδNonnegative : ∀ n, 0 ≤ δ n := by
    intro n
    exact le_of_tendsto_of_tendsto hδZero tendsto_const_nhds
      (eventually_atTop.2 ⟨n, fun m hnm => hδAnti hnm⟩)
  have hgC0 : ∀ n, g n ∈ C0 := by
    intro n
    apply hC0Solid (hC0Cone.2.2 hcPositive (hfC0 n))
    exact Filter.Eventually.of_forall fun _ => min_le_left _ _
  have hgMeas : ∀ n, AEStronglyMeasurable (g n) μ := by
    intro n
    exact ((hfMeas n).const_mul c).inf aestronglyMeasurable_const
  have hgLower : ∀ n, AELowerBoundedBy μ (-(δ' n)) (g n) := by
    intro n
    filter_upwards [hfLower n] with ω hLower
    apply le_min
    · have hScaled := mul_le_mul_of_nonneg_left hLower hcNonnegative
      dsimp [δ']
      linarith
    · dsimp [δ']
      have hδScaled : 0 ≤ c * δ n :=
        mul_nonneg hcNonnegative (hδNonnegative n)
      linarith
  have hgUpper : ∀ n, ∀ᵐ ω ∂μ, g n ω ≤ 1 := by
    intro n
    exact Filter.Eventually.of_forall fun _ => min_le_right _ _
  have hδ'Anti : Antitone δ' := by
    intro m n hmn
    exact mul_le_mul_of_nonneg_left (hδAnti hmn) hcNonnegative
  have hδ'Zero : Tendsto δ' atTop (nhds 0) := by
    have hScaled :=
      (tendsto_const_nhds (x := c)).mul hδZero
    simpa [δ'] using hScaled
  have hgMass :
      ∀ n, ENNReal.ofReal ε < μ {ω | (1 / 2 : ℝ) < g n ω} := by
    intro n
    apply lt_of_lt_of_le (hfMass n)
    apply measure_mono
    intro ω hω
    change (1 / 2 : ℝ) < min (c * f n ω) 1
    rw [lt_min_iff]
    constructor
    · have hScaled := mul_lt_mul_of_pos_left hω hcPositive
      nlinarith
    · norm_num
  exact not_vanishingRiskPositiveMass_of_linfyNFLVR
    hC0Cone hC0Solid hNFLVR hε hgC0 hgMeas hgLower hgUpper hδ'Anti
    hδ'Zero hgMass

/--
Natural sequential form of the vanishing-risk contradiction.

The downside bounds only need to converge to zero; neither nonnegativity nor
monotonicity is required.  A strict subsequence is selected below the standard
decreasing risk schedule before applying the scale- and truncation-invariant
endpoint.
-/
theorem not_vanishingRiskPositiveLevel_of_tendsto_linfyNFLVR
    {μ : Measure Ω} [IsFiniteMeasure μ] {C0 : Set (Ω → ℝ)}
    (hC0Cone : ClaimCone C0)
    (hC0Solid : Solid μ C0)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ C0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hfC0 : ∀ n, f n ∈ C0)
    (hfMeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfLower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n))
    (hδZero : Tendsto δ atTop (nhds 0))
    (hfMass : ∀ n, ENNReal.ofReal ε < μ {ω | η < f n ω}) :
    False := by
  let r : ℕ → ℝ := fun n => (positiveTailScaleDenom n)⁻¹
  have hrPositive : ∀ n, 0 < r n := by
    intro n
    exact inv_pos.mpr (positiveTailScaleDenom_pos n)
  rcases exists_strictMono_subsequence_lt_of_tendsto_zero hδZero hrPositive with
    ⟨φ, hφStrict, hφRisk⟩
  let f' : ℕ → Ω → ℝ := fun n => f (φ n)
  have hf'Lower : ∀ n, AELowerBoundedBy μ (-(r n)) (f' n) := by
    intro n
    apply (hfLower (φ n)).mono_const
    exact neg_le_neg (le_of_lt (hφRisk n))
  exact not_vanishingRiskPositiveLevel_of_linfyNFLVR
    hC0Cone hC0Solid hNFLVR hε hη
    (fun n => hfC0 (φ n))
    (fun n => hfMeas (φ n))
    hf'Lower
    (by simpa [r] using positiveTailScaleInv_antitone)
    (by simpa [r] using positiveTailScaleInv_tendsto_zero)
    (fun n => hfMass (φ n))

end FTAPTheorem42
