/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.CumulativeVariationJumpEnumeration

/-!
# Predictable backward ratios for finite-variation paths

For a predictable finite-variation process `A` and its cumulative total
variation `V`, the quotient

`(A t - A (t⁻ₙ)) / (V t - V (t⁻ₙ))`

uses only the present and the deterministic factorial-grid point immediately
to the left.  It is therefore predictable.  Each quotient lies in `[-1, 1]`,
and its pointwise limsup is a bounded predictable process.  The latter is the
concrete candidate for the predictable polar density of `dA` with respect to
`dV`.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

namespace SIntegrableFiniteVariationBridge

/-- The finite backward ratio of the finite-variation component with respect
to its cumulative total variation.  Division by a zero variation increment
is zero in `ℝ`. -/
noncomputable def variationBackwardRatio
    (H : SIntegrableStrategy D) (n : ℕ) : Process Ω :=
  fun t ω =>
    (H.finiteVariationPart t ω -
        H.finiteVariationPart (LeftContinuousPredictable.approx n t) ω) /
      (cumulativeVariation H t ω -
        cumulativeVariation H (LeftContinuousPredictable.approx n t) ω)

/-- The predictable polar-density candidate obtained as the pointwise limsup
of the finite backward ratios. -/
noncomputable def variationBackwardDensity
    (H : SIntegrableStrategy D) : Process Ω :=
  fun t ω => limsup (fun n => variationBackwardRatio H n t ω) atTop

/-- Each finite backward ratio is predictable. -/
theorem variationBackwardRatio_isStronglyPredictable
    (E : SIntegrableFiniteVariationBridge H) (n : ℕ) :
    IsStronglyPredictable ℱ (variationBackwardRatio H n) := by
  have hAstep : IsStronglyPredictable ℱ
      (LeftContinuousPredictable.step n H.finiteVariationPart) :=
    LeftContinuousPredictable.stronglyPredictable_step
      H.finiteVariationPart_isPredictable.stronglyAdapted n
  have hV := CumulativeVariationJumpEnumeration.cumulativeVariation_isStronglyPredictable
    H E.rightContinuous
  have hVstep : IsStronglyPredictable ℱ
      (LeftContinuousPredictable.step n (cumulativeVariation H)) :=
    LeftContinuousPredictable.stronglyPredictable_step
      (cumulativeVariation_stronglyAdapted H E.rightContinuous) n
  exact (H.finiteVariationPart_isPredictable.sub hAstep).div
    (hV.sub hVstep)

/-- A finite backward ratio has absolute value at most one, path by path. -/
theorem abs_variationBackwardRatio_le_one
    (_E : SIntegrableFiniteVariationBridge H) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |variationBackwardRatio H n t ω| ≤ 1 := by
  let s := LeftContinuousPredictable.approx n t
  have hst : s ≤ t := LeftContinuousPredictable.approx_le n t
  have hvar :
      |H.finiteVariationPart t ω - H.finiteVariationPart s ω| ≤
        cumulativeVariation H t ω - cumulativeVariation H s ω := by
    rw [← totalVariation_real_Ioc_eq_cumulativeVariation_sub H ω hst]
    rw [← FiniteVariationPath.signedMeasure_Ioc
      (H.finiteVariationPart_isBoundedVariation ω) (_E.rightContinuous ω) hst]
    let ν := FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)
    apply abs_le.2
    constructor
    · have hneg := signedMeasure_apply_le_totalVariation_real
        (-ν) (B := Ioc s t) measurableSet_Ioc
      rw [neg_apply, SignedMeasure.totalVariation_neg] at hneg
      linarith
    · exact signedMeasure_apply_le_totalVariation_real
        ν (B := Ioc s t) measurableSet_Ioc
  have hdenom : 0 ≤ cumulativeVariation H t ω - cumulativeVariation H s ω :=
    le_trans (abs_nonneg _) hvar
  rw [variationBackwardRatio, abs_div]
  rw [abs_of_nonneg hdenom]
  exact div_le_one_of_le₀ hvar hdenom

/-- The limsup polar-density candidate is predictable. -/
theorem variationBackwardDensity_isStronglyPredictable
    (E : SIntegrableFiniteVariationBridge H) :
    IsStronglyPredictable ℱ (variationBackwardDensity H) := by
  apply Measurable.stronglyMeasurable
  exact Measurable.limsup fun n =>
    (variationBackwardRatio_isStronglyPredictable E n).measurable

/-- The predictable limsup density remains in the closed unit interval. -/
theorem abs_variationBackwardDensity_le_one
    (E : SIntegrableFiniteVariationBridge H) (t : ℝ≥0) (ω : Ω) :
    |variationBackwardDensity H t ω| ≤ 1 := by
  have hUpper :
      limsup (fun n => variationBackwardRatio H n t ω) atTop ≤ 1 := by
    refine limsup_le_of_le ?_ (Filter.Eventually.of_forall fun n =>
      (le_abs_self (variationBackwardRatio H n t ω)).trans
        (abs_variationBackwardRatio_le_one E n t ω))
    exact isCoboundedUnder_le_of_le atTop fun n =>
      neg_le_of_abs_le (abs_variationBackwardRatio_le_one E n t ω)
  have hLower :
      -1 ≤ limsup (fun n => variationBackwardRatio H n t ω) atTop := by
    refine le_limsup_of_frequently_le
      (Frequently.of_forall fun n =>
        neg_le_of_abs_le (abs_variationBackwardRatio_le_one E n t ω)) ?_
    exact isBoundedUnder_of ⟨1, fun n =>
      (le_abs_self (variationBackwardRatio H n t ω)).trans
        (abs_variationBackwardRatio_le_one E n t ω)⟩
  exact abs_le.2 ⟨hLower, hUpper⟩

/-- At every nonzero left jump, the backward density is exactly the normalized
jump.  Thus the same predictable process already recovers the atomic polar
sign; no exceptional set is needed for this part. -/
theorem variationBackwardDensity_eq_leftJump_div_abs
    (E : SIntegrableFiniteVariationBridge H) {t : ℝ≥0} {ω : Ω}
    (hJump : processLeftJump H.finiteVariationPart t ω ≠ 0) :
    variationBackwardDensity H t ω =
      processLeftJump H.finiteVariationPart t ω /
        |processLeftJump H.finiteVariationPart t ω| := by
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hJump
    have hleft : Function.leftLim
        (fun s => H.finiteVariationPart s ω) (0 : ℝ≥0) =
          H.finiteVariationPart 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    unfold processLeftJump
    rw [hleft, sub_self]
  have hApprox : Tendsto (fun n => LeftContinuousPredictable.approx n t)
      atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨LeftContinuousPredictable.tendsto_approx t,
      Filter.Eventually.of_forall fun n =>
        LeftContinuousPredictable.approx_lt ht n⟩
  have hA : Tendsto
      (fun n => H.finiteVariationPart
        (LeftContinuousPredictable.approx n t) ω)
      atTop
      (𝓝 (Function.leftLim (H.finiteVariationPart · ω) t)) :=
    (H.finiteVariationPart_hasLeftLimits ω t).comp hApprox
  have hV : Tendsto
      (fun n => cumulativeVariation H
        (LeftContinuousPredictable.approx n t) ω)
      atTop
      (𝓝 (Function.leftLim (cumulativeVariation H · ω) t)) :=
    (CumulativeVariationJumpEnumeration.cumulativeVariation_hasLeftLimits
      H E.rightContinuous ω t).comp hApprox
  have hDenom :
      cumulativeVariation H t ω -
          Function.leftLim (cumulativeVariation H · ω) t =
        |processLeftJump H.finiteVariationPart t ω| := by
    rw [← CumulativeVariationJumpEnumeration.processLeftJump_cumulativeVariation_eq_abs
      H E.rightContinuous t ω]
    rfl
  have hTendsto : Tendsto
      (fun n => variationBackwardRatio H n t ω) atTop
      (𝓝 (processLeftJump H.finiteVariationPart t ω /
        |processLeftJump H.finiteVariationPart t ω|)) := by
    have hNum : Tendsto
        (fun n => H.finiteVariationPart t ω -
          H.finiteVariationPart (LeftContinuousPredictable.approx n t) ω)
        atTop
        (nhds (H.finiteVariationPart t ω -
          Function.leftLim (H.finiteVariationPart · ω) t)) :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => H.finiteVariationPart t ω) atTop
        (nhds (H.finiteVariationPart t ω))).sub hA
    have hDen : Tendsto
        (fun n => cumulativeVariation H t ω -
          cumulativeVariation H (LeftContinuousPredictable.approx n t) ω)
        atTop
        (nhds (cumulativeVariation H t ω -
          Function.leftLim (cumulativeVariation H · ω) t)) :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => cumulativeVariation H t ω) atTop
        (nhds (cumulativeVariation H t ω))).sub hV
    have hDenomNe : cumulativeVariation H t ω -
        Function.leftLim (cumulativeVariation H · ω) t ≠ 0 := by
      rw [hDenom]
      exact abs_ne_zero.mpr hJump
    have hDiv := hNum.div hDen hDenomNe
    convert hDiv using 1
    · funext n
      rfl
    · unfold processLeftJump
      rw [hDenom]
      rfl
  exact hTendsto.limsup_eq

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
