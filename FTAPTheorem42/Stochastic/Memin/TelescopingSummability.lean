import FTAPTheorem42.Stochastic.Memin.TelescopingComponentLimit
import FTAPTheorem42.Stochastic.Memin.LocalS1Normalization

/-! # Canonical variation summability for the actual telescoping row -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.ActualSIntegrableStrategy

open SIntegrablePredictableMultiplierLinearL2Calculus

private theorem totalVariation_eq_of_constant_after
    (f : NNReal → Real) (hBV : BoundedVariationOn f univ)
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (T : NNReal) (hConst : ∀ t, T ≤ t → f t = f T) :
    (FiniteVariationPath.signedMeasure hBV).totalVariation univ =
      eVariationOn f (Icc 0 T) := by
  have hEq : FiniteVariationStoppedPath.stopAt f T = f := by
    funext t
    dsimp only [FiniteVariationStoppedPath.stopAt]
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht), hConst t (le_of_not_ge ht)]
  have hVar := FiniteVariationStoppedPath.totalVariation_univ_stopAt f hBV hRight T
  rw [variationOnFromTo.eq_of_le f univ (show (0 : NNReal) ≤ T from bot_le), univ_inter,
    ENNReal.ofReal_toReal (hBV.mono (subset_univ _))] at hVar
  simpa only [hEq] using hVar

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {R : SIntegrableRealizationModel D}

/-- The record's canonical signed-measure variation is supplied from the
original stopped FV costs, not from convergence of the component series. -/
theorem variation_summable_of_telescoping_stopped_cost
    (A P : Nat → ActualSIntegrableStrategy R) (T : NNReal)
    (hConst : ∀ k ω t, T ≤ t →
      (A k).val.finiteVariationPart t ω = (A k).val.finiteVariationPart T ω)
    (hSum : (∑' k, ∫⁻ ω,
      eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) ∂μ) ≠ ∞)
    (hRec : ∀ n, (P (n + 1)).val = (P n).val.add_of_rightContinuous (A n).val) :
    ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (P (k + 1)).val (P k).val ω) := by
  let g := fun k => lemma411DifferenceTotalVariation (P (k + 1)).val (P k).val
  have hEq : ∀ k ω, ENNReal.ofReal (g k ω) =
      eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) := by
    intro k ω
    have hPath : ((lemma411Difference (P (k + 1)).val (P k).val).finiteVariationPart · ω) =
        ((A k).val.finiteVariationPart · ω) := by
      funext t
      change (P (k + 1)).val.finiteVariationPart t ω - (P k).val.finiteVariationPart t ω = _
      rw [hRec]
      change (_ + _) - _ = _
      ring
    change ENNReal.ofReal ((FiniteVariationPath.signedMeasure
      ((lemma411Difference (P (k + 1)).val (P k).val).finiteVariationPart_isBoundedVariation ω)
      ).totalVariation.real univ) = _
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp only [hPath]
    exact totalVariation_eq_of_constant_after _ _
      ((A k).val.finiteVariationPart_isRightContinuous ω) T (hConst k ω)
  apply ae_summable_of_summable_envelope_integrals g
    (fun k => lemma411_differenceTotalVariation_measurable _ _) (fun _ _ => ENNReal.toReal_nonneg)
  convert hSum using 1
  congr 1
  funext k
  exact lintegral_congr_ae (Eventually.of_forall (hEq k))

/-- Every horizon envelope of a successive martingale difference is bounded
by the original common stopped cost. Tonelli supplies the required a.e. sum. -/
theorem martingaleEnvelope_summable_of_telescoping_stopped_cost
    (A P : Nat → ActualSIntegrableStrategy R) (T : NNReal)
    (hLeft : ∀ k, ProcessHasLeftLimits (A k).val.martingalePart)
    (hZero : ∀ k, (A k).val.martingalePart 0 = 0)
    (hConst : ∀ k ω t, T ≤ t →
      (A k).val.martingalePart t ω = (A k).val.martingalePart T ω)
    (hSum : (∑' k, ∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂μ) ≠ ∞)
    (hRec : ∀ n, (P (n + 1)).val = (P n).val.add_of_rightContinuous (A n).val) :
    ∀ U, ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope (rawSequence P) U k ω) := by
  intro U
  let g := fun k => meminMartingaleDifferenceEnvelope (rawSequence P) U k
  have hBound : ∀ k ω, ENNReal.ofReal (g k ω) ≤
      ⨆ t : Icc (0 : NNReal) T, ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| := by
    intro k ω
    have hPath : (lemma411Difference (P (k + 1)).val (P k).val).martingalePart =
        (A k).val.martingalePart := by
      funext t w
      change (P (k + 1)).val.martingalePart t w - (P k).val.martingalePart t w = _
      rw [hRec]
      change (_ + _) - _ = _
      ring
    change ENNReal.ofReal (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (lemma411Difference (P (k + 1)).val (P k).val).martingalePart U ω) ≤ _
    rw [hPath, FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
      (A k).val.martingalePart_isRightContinuous (hLeft k)]
    apply iSup_le
    intro t
    apply le_iSup_of_le ⟨min t.1 T, bot_le, min_le_right _ _⟩
    simp only [SIntegrableStrategy.centeredMartingalePart, hZero k, Pi.zero_apply, sub_zero]
    have hEq : (A k).val.martingalePart t.1 ω = (A k).val.martingalePart (min t.1 T) ω := by
      by_cases ht : t.1 ≤ T
      · rw [min_eq_left ht]
      · rw [min_eq_right (le_of_not_ge ht), hConst k ω _ (le_of_not_ge ht)]
    exact le_of_eq (congrArg (fun x : Real => ENNReal.ofReal |x|) hEq)
  apply ae_summable_of_summable_envelope_integrals g
    (fun k => meminMartingaleDifferenceEnvelope_measurable _ _ _)
    (fun k ω => meminMartingaleDifferenceEnvelope_nonnegative _ _ _ _)
  exact ne_top_of_le_ne_top hSum
    (ENNReal.tsum_le_tsum fun k => lintegral_mono (hBound k))

end FTAPTheorem42.ActualSIntegrableStrategy
