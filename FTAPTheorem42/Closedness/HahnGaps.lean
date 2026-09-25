/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.HahnData

/-! # Normalization and terminal gap estimates -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open MeasureTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Positive normalization preserves the actual original-market terminal claim. -/
theorem truncatedTerminalClaimsBy_normalize
    (source : BoundedSemimartingaleSource S F μ) {a : Real} {g : Ω → Real}
    (hg : g ∈ generalAdmissibleClaims source a) :
    (fun ω => g ω / a) ∈ generalAdmissibleClaims source 1 := by
  rw [generalAdmissibleClaims_eq_generalMarket] at hg ⊢
  obtain ⟨H, ⟨ha, hLower⟩, rfl⟩ := hg
  let B := generalMarket source
  refine ⟨B.posSMulStrategy a⁻¹ (inv_pos.mpr ha) H, ⟨zero_lt_one, ?_⟩, ?_⟩
  · intro t
    rw [B.gain_posSMul]
    filter_upwards [hLower t] with ω hω
    rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ ha]
    simpa only [neg_one_mul] using hω
  · rw [B.terminalGain_posSMul]
    funext ω
    exact (div_eq_inv_mul _ _).symm

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket.OriginalHahnImprovement

/-! ## Survival controls the normalized Hahn improvement without another M event -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {source : BoundedSemimartingaleSource S F μ}
  {Y M A : Process Ω} {T U : NNReal} {b δ : Real}

/-- Use exactly the same normalization for the improved terminal and the baseline. -/
theorem normalized_terminal_gap_of_survival
    (P : OriginalHahnImprovement source Q Y M A T b δ)
    (hTU : T ≤ U) (hδ : 0 ≤ δ) :
    ∀ᵐ ω ∂Q,
      (T : WithTop NNReal) < lowerStrictHittingAfter
        (hahnMartingaleAdvantage P.martingale M) δ ω →
      (P.finiteVariation T ω - δ) / (1 + δ) ≤
        finiteHahnPastedGain Y P.gain P.martingale M δ T U U ω / (1 + δ) -
          Y U ω / (1 + δ) := by
  filter_upwards [P.decomposition] with ω hDec hSurvive
  rw [finiteHahnPastedGain_terminal_of_survival _ _ _ _ hTU δ ω hSurvive,
    ← sub_div]
  apply (div_le_div_iff_of_pos_right (by linarith : 0 < 1 + δ)).mpr
  have hN := neg_le_of_lt_lowerStrictHittingAfter
    (hahnMartingaleAdvantage P.martingale M) δ ω T hSurvive
  change -δ ≤ P.martingale T ω - max (M T ω) 0 at hN
  have hD := hDec T
  change P.gain T ω = P.martingale T ω + P.finiteVariation T ω at hD
  linarith [le_max_right (M T ω) 0]

/-- Survival bounds the negative gap; a large FV increment forces a fixed positive gap. -/
theorem normalized_terminal_gap_bounds
    (P : OriginalHahnImprovement source Q Y M A T b δ)
    (hTU : T ≤ U) (hδ : 0 ≤ δ) {α : Real} (hδ1 : δ ≤ 1) (hδα : δ ≤ α / 8) :
    ∀ᵐ ω ∂Q,
      (T : WithTop NNReal) < lowerStrictHittingAfter
        (hahnMartingaleAdvantage P.martingale M) δ ω →
      let g := finiteHahnPastedGain Y P.gain P.martingale M δ T U U ω / (1 + δ)
      let f := Y U ω / (1 + δ)
      max (f - g) 0 ≤ δ ∧
        (α / 2 < P.finiteVariation T ω → α / 8 ≤ g - f) := by
  have hden : 0 < 1 + δ := by linarith
  filter_upwards [P.normalized_terminal_gap_of_survival hTU hδ,
    P.increment, P.finiteVariation_zero] with ω hGap hInc hZero hSurvive
  have hC : 0 ≤ P.finiteVariation T ω := by
    have h := (hInc 0 T zero_le).1
    change P.finiteVariation 0 ω = 0 at hZero
    linarith
  have h := (div_le_iff₀ hden).mp (hGap hSurvive)
  dsimp only
  constructor
  · apply max_le _ hδ
    nlinarith [sq_nonneg δ]
  · intro hBig
    have hα : 0 ≤ α := by linarith
    nlinarith

end FTAPTheorem42.BoundedSourceIntegralMarket.OriginalHahnImprovement
