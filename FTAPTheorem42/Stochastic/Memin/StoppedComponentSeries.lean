import FTAPTheorem42.Stochastic.Martingale.Basic.SummableMartingaleEnvelope
import FTAPTheorem42.Stochastic.Martingale.Basic.DominatedLocalMartingale
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Topology.J1.ActualVariation

/-! # All-time component series from summable bounded-stop actual rows -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.ActualSIntegrableStrategy

open FactorialChronologicalGrid SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {R : SIntegrableRealizationModel D}

/-- The centered component sums converge uniformly on the whole time axis;
the FV sum also converges in variation and the martingale sum is a true
martingale. Integral realization is established separately by the
Mémín construction. -/
theorem component_series_of_summable_stopped_cost
    (A : Nat → ActualSIntegrableStrategy R) (T : NNReal)
    (hLeft : ∀ k, ProcessHasLeftLimits (A k).val.martingalePart)
    (hConst : ∀ k ω t, T ≤ t →
      (A k).val.martingalePart t ω = (A k).val.martingalePart T ω ∧
      (A k).val.finiteVariationPart t ω = (A k).val.finiteVariationPart T ω)
    (hSum : (∑' k, ((∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂μ) +
      ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) ∂μ)) ≠ ∞) :
    let M := fun k => (A k).val.centeredMartingalePart
    let B := fun k t ω => (A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω
    Martingale (fun t ω => ∑' k, M k t ω) F μ ∧
      IsStronglyPredictable F (fun t ω => ∑' k, B k t ω) ∧
      ∀ᵐ ω ∂μ,
        TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, M k t ω)
          (fun t => ∑' k, M k t ω) atTop ∧
        BoundedVariationOn (fun t => ∑' k, B k t ω) univ ∧
        TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, B k t ω)
          (fun t => ∑' k, B k t ω) atTop ∧
        Tendsto (fun n => eVariationOn
          (fun t => (∑' k, B k t ω) - ∑ k ∈ Finset.range n, B k t ω) univ) atTop (𝓝 0) := by
  dsimp only
  let M := fun k => (A k).val.centeredMartingalePart
  let B := fun k t ω => (A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω
  have hMR : ∀ k ω t, ContinuousWithinAt (M k · ω) (Ici t) t :=
    fun k ω t => ((A k).val.martingalePart_isRightContinuous ω t).sub continuousWithinAt_const
  have hML : ∀ k, ProcessHasLeftLimits (M k) :=
    fun k => (hLeft k).sub (.timeConstant _)
  have hMA : ∀ k, StronglyAdapted F (M k) := fun k t =>
    ((A k).val.martingalePart_isStronglyAdapted t).sub
      (((A k).val.martingalePart_isStronglyAdapted 0).mono (F.mono bot_le))
  let g := fun k => finiteHorizonAbsoluteEnvelope (M k) T
  have hg : ∀ k, Measurable (g k) := fun k =>
    ((stronglyMeasurable_finiteHorizonAbsoluteEnvelope (hMA k) T).mono (F.le T)).measurable
  have hgPos : ∀ k ω, 0 ≤ g k ω := fun _ _ => Real.sqrt_nonneg _
  have hgEq : ∀ k ω, ENNReal.ofReal (g k ω) =
      ⨆ t : Icc (0 : NNReal) T, ENNReal.ofReal |M k t.1 ω| := by
    intro k ω
    rw [ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup (hMR k) (hML k)]
    apply le_antisymm
    · exact iSup_le fun t => le_iSup_of_le ⟨t.1, bot_le, t.2⟩ le_rfl
    · exact iSup_le fun t => le_iSup_of_le ⟨t.1, t.2.2⟩ le_rfl
  have hgBound : ∀ k ω t, |M k t ω| ≤ g k ω := by
    intro k ω t
    have hEq : M k t ω = M k (min t T) ω := by
      by_cases ht : t ≤ T
      · rw [min_eq_left ht]
      · change _ - _ = _ - _
        rw [min_eq_right (le_of_not_ge ht), (hConst k ω t (le_of_not_ge ht)).1]
    rw [hEq]
    exact abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag (hMR k) (hML k) T
      (min t T) (min_le_right _ _)
  have hgSum : (∑' k, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top hSum
    apply ENNReal.tsum_le_tsum
    intro k
    rw [lintegral_congr_ae (Eventually.of_forall (hgEq k))]
    exact le_add_right le_rfl
  have hMart : ∀ k, Martingale (M k) F μ := by
    intro k
    have hInt := integrable_toReal_of_lintegral_ne_top (hg k).ennreal_ofReal.aemeasurable
      (ne_top_of_le_ne_top hgSum
        (ENNReal.le_tsum (f := fun k => ∫⁻ ω, ENNReal.ofReal (g k ω) ∂μ) k))
    have hgInt : Integrable (g k) μ := by
      simpa only [ENNReal.toReal_ofReal (hgPos _ _)] using hInt
    exact (A k).val.martingalePart_isLocalMartingale.centered.martingale_of_integrable_bound
      (hMA k) (g k) hgInt (Eventually.of_forall (hgBound k))
  have hBP : ∀ k, IsStronglyPredictable F (B k) := fun k =>
    (A k).val.finiteVariationPart_isPredictable.sub
      (IsStronglyPredictable.timeConstant_initial (A k).val.finiteVariationPart_isPredictable)
  have hBPsum : IsStronglyPredictable F (fun t ω => ∑' k, B k t ω) := by
    let : MeasurableSpace (NNReal × Ω) := F.predictable
    exact (Measurable.tsum (fun k => (hBP k).measurable)).stronglyMeasurable
  refine ⟨martingale_tsum_of_summable_envelopes M g hMart hg hgPos hgBound hgSum, hBPsum, ?_⟩
  let v := fun k ω => eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T)
  have hv : ∀ k, Measurable (v k) := fun k =>
    measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
      (A k).val.finiteVariationPart_isPredictable.stronglyAdapted
      (A k).val.finiteVariationPart_isRightContinuous
  have hvSum : (∑' k, ∫⁻ ω, v k ω ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hSum (ENNReal.tsum_le_tsum fun _ => le_add_left le_rfl)
  have hvInt : (∫⁻ ω, ∑' k, v k ω ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (hv k).aemeasurable)]
    exact hvSum
  filter_upwards [ae_uniform_series_of_summable_envelopes M g hg hgPos hgBound hgSum,
    ae_lt_top (Measurable.tsum hv) hvInt] with ω hM hV
  refine ⟨hM, ?_⟩
  apply variation_series_convergence (fun k t => B k t ω) 0 (fun _ => sub_self _)
  apply ne_top_of_le_ne_top hV.ne
  apply ENNReal.tsum_le_tsum
  intro k
  rw [pathVariation_sub_const]
  have hEq : ((A k).val.finiteVariationPart · ω) =
      (fun t => (A k).val.finiteVariationPart (min t T) ω) := by
    funext t
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht)]
      exact (hConst k ω t (le_of_not_ge ht)).2
  calc
    _ = eVariationOn (fun t => (A k).val.finiteVariationPart (min t T) ω) univ :=
      congrArg (fun f => eVariationOn f univ) hEq
    _ ≤ v k ω := eVariationOn.comp_le_of_monotoneOn
      (fun t => (A k).val.finiteVariationPart t ω) (s := Icc 0 T) (fun t => min t T)
      ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ)
      (fun _ _ => ⟨bot_le, min_le_right _ _⟩)

end FTAPTheorem42.ActualSIntegrableStrategy
