/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.HahnData
import FTAPTheorem42.Closedness.HahnMaximality

/-! # Finite-horizon FV Cauchy bounds from original-market maximality -/

namespace FTAPTheorem42

/-! ## Varying indices and terminal horizons under an all-time uniform limit -/

open Filter MeasureTheory Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An all-time uniform path limit retains its own terminal along moving
indices and moving horizons. No terminal for each approximating path is needed. -/
theorem tendstoAE_varyingTime_of_uniformAE_terminal
    {Y : Nat → Process Ω} {X : Process Ω} {h : Ω → Real}
    (hUniform : ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => Y n t ω) (X · ω) atTop)
    (hTerminal : ∀ᵐ ω ∂μ, Tendsto (X · ω) atTop (𝓝 (h ω)))
    {ℓ : Nat → Nat} {U : Nat → NNReal}
    (hℓ : Tendsto ℓ atTop atTop) (hU : Tendsto U atTop atTop) :
    TendstoAE μ (fun r ω => Y (ℓ r) (U r) ω) h := by
  filter_upwards [hUniform, hTerminal] with ω hω hT
  have hError : Tendsto (fun r => Y (ℓ r) (U r) ω - X (U r) ω) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hℓ.eventually ((Metric.tendstoUniformly_iff.mp hω) ε hε)] with r hr
    simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hr (U r)
  have ht := hError.add (hT.comp hU)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using ht

end FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
namespace FTAPTheorem42.BoundedSourceIntegralMarket
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F]

/-- The actual oriented improvements force the FV differences to be Cauchy
on each fixed positive horizon. The later terminal horizons grow independently. -/
theorem original_finiteVariation_cauchyInProbability
    (source : BoundedSemimartingaleSource S F μ) (hμQ : μ ≪ Q) (hQμ : Q ≪ μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    {h : Ω → Real}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      (generalAdmissibleClaims source 1)) h)
    (Y : Nat → Process Ω)
    (hYA : ∀ n, StronglyAdapted F (Y n))
    (E : ∀ n, J1Decomposition (Y n) F Q)
    {X : Process Ω}
    (hUniform : ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => Y n t ω) (X · ω) atTop)
    (hTerminal : ∀ᵐ ω ∂μ, Tendsto (X · ω) atTop (𝓝 (h ω)))
    (T : NNReal)
    (hHahn : ∀ ε : Real, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
      ∀ δ : Real, 0 ≤ δ → OriginalPairHahnOrientedImprovement source (Y n) (Y k)
        (E n) (E k) T ε δ) :
    ∀ α : Real, 0 < α → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
      Q.real {ω | α < finiteHorizonPathVariation ((E n).A - (E k).A)
        (fun ω a c ha hc => by
          simpa only [Pi.sub_apply, sub_eq_add_neg] using
            boundedVariationOn_add ((E n).variationA ω a c ha hc)
              (boundedVariationOn_neg ((E k).variationA ω a c ha hc))) T ω} ≤ α := by
  classical
  intro α hα
  by_contra hNot
  push Not at hNot
  let c : Real := min (α / 8) 1
  let δ : Nat → Real := fun r => c * (2 : Real)⁻¹ ^ (r + 1)
  let b : Nat → Real := fun r => δ r ^ 2 / 8
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  have hδ : ∀ r, 0 < δ r := fun r => mul_pos hc (by positivity)
  have hδc : ∀ r, δ r ≤ c := fun r =>
    mul_le_of_le_one_right hc.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hδ1 : ∀ r, δ r ≤ 1 := fun r => (hδc r).trans (min_le_right _ _)
  have hδα : ∀ r, δ r ≤ α / 8 := fun r => (hδc r).trans (min_le_left _ _)
  have hbPos : ∀ r, 0 < b r := fun r => div_pos (sq_pos_of_pos (hδ r)) (by norm_num)
  have hb : ∀ r, (b r + b r) / (δ r / 4) ≤ δ r := by
    intro r
    dsimp only [b]
    apply le_of_eq
    field_simp
    ring
  have hGeometric : Tendsto (fun r : Nat => (2 : Real)⁻¹ ^ (r + 1)) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using tendsto_const_nhds.mul hGeometric
  have hδsum : (∑' r, ENNReal.ofReal (δ r)) ≠ ⊤ := by
    have hGeo : (∑' r : Nat, (2 : ENNReal)⁻¹ ^ (r + 1)) ≠ ⊤ := by
      rw [ENNReal.tsum_geometric_add_one]
      norm_num
    apply ne_top_of_le_ne_top hGeo
    apply ENNReal.tsum_le_tsum
    intro r
    calc
      ENNReal.ofReal (δ r) ≤ ENNReal.ofReal ((2 : Real)⁻¹ ^ (r + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_of_le_one_left (by positivity) (min_le_right _ _)
      _ = (2 : ENNReal)⁻¹ ^ (r + 1) := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
  have hWitness : ∀ r : Nat, ∃ j ℓ : Nat, r ≤ j ∧ r ≤ ℓ ∧
      ∃ P : OriginalHahnImprovement source Q (Y ℓ)
        ((E j).N - (E ℓ).N) ((E j).A - (E ℓ).A) T (b r) (δ r),
        α / 2 < Q.real {ω | α / 2 < P.finiteVariation T ω} := by
    intro r
    obtain ⟨N, hN⟩ := hHahn (b r) (hbPos r)
    obtain ⟨n, hn, k, hk, hMass⟩ := hNot (max N r)
    obtain ⟨P, P', hOrient⟩ := hN n ((le_max_left _ _).trans hn)
      k ((le_max_left _ _).trans hk) (δ r) (hδ r).le
    rcases hOrient α hMass with hp | hp
    · exact ⟨n, k, (le_max_right _ _).trans hn, (le_max_right _ _).trans hk, P, hp⟩
    · exact ⟨k, n, (le_max_right _ _).trans hk, (le_max_right _ _).trans hn, P', hp⟩
  choose j ℓ _hj hℓ P hP using hWitness
  let U : Nat → NNReal := fun r => max T ((r + 1 : Nat) : NNReal)
  have hU : ∀ r, T ≤ U r := fun r => le_max_left _ _
  have hUlim : Tendsto U atTop atTop := by
    apply tendsto_atTop_mono (fun r => le_max_right T ((r + 1 : Nat) : NNReal))
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hℓlim : Tendsto ℓ atTop atTop := tendsto_atTop_mono hℓ tendsto_id
  have hYlim := tendstoAE_varyingTime_of_uniformAE_terminal hUniform hTerminal hℓlim hUlim
  exact not_originalHahn_improvements source hμQ hQμ hNFLVR hmax hα P
    (fun r => ((E (j r)).adaptedN).sub (E (ℓ r)).adaptedN)
    (fun r ω t => ((E (j r)).rightN ω t).sub ((E (ℓ r)).rightN ω t))
    hU hδ hδ1 hδα hδlim hδsum hb hP
    (fun r => ((hYA (ℓ r) (U r)).mono (F.le (U r))).aestronglyMeasurable)
    (hQμ.ae_le hYlim)
end FTAPTheorem42.BoundedSourceIntegralMarket
