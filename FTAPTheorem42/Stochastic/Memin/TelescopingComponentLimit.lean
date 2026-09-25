/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Memin.StoppedComponentSeries
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Regular limits of telescoping components

Regularize the summable stopped increment series, then add the initial actual
strategy. The resulting components retain uniform and variation convergence
of the original telescoping approximants. -/

namespace FTAPTheorem42.ActualSIntegrableStrategy

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {R : SIntegrableRealizationModel D}

/-- Null-set regularization retains the original centered series and all its
convergence assertions. Regularity holds on every path, while both versions
agree with the series simultaneously at every time almost surely. -/
theorem exists_regular_component_series
    (hUsual : Filtration.UsualConditions μ F)
    (A : Nat → ActualSIntegrableStrategy R) (T : NNReal)
    (hLeft : ∀ k, ProcessHasLeftLimits (A k).val.martingalePart)
    (hConst : ∀ k ω t, T ≤ t →
      (A k).val.martingalePart t ω = (A k).val.martingalePart T ω ∧
      (A k).val.finiteVariationPart t ω = (A k).val.finiteVariationPart T ω)
    (hSum : (∑' k, ((∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂μ) +
      ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) ∂μ)) ≠ ∞) :
    let m := fun k => (A k).val.centeredMartingalePart
    let v := fun k t ω => (A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω
    ∃ M V : Process Ω,
      Martingale M F μ ∧ IsStronglyPredictable F V ∧
      (∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t) ∧ ProcessHasLeftLimits M ∧
      (∀ ω t, ContinuousWithinAt (V · ω) (Ici t) t) ∧
      (∀ ω, BoundedVariationOn (V · ω) univ) ∧
      M 0 =ᵐ[μ] 0 ∧ V 0 =ᵐ[μ] 0 ∧
      ProcessIndistinguishable μ M (fun t ω => ∑' k, m k t ω) ∧
      ProcessIndistinguishable μ V (fun t ω => ∑' k, v k t ω) ∧
      ∀ᵐ ω ∂μ,
        TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, m k t ω) (M · ω) atTop ∧
        TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, v k t ω) (V · ω) atTop ∧
        Tendsto (fun n => eVariationOn
          (fun t => V t ω - ∑ k ∈ Finset.range n, v k t ω) univ) atTop (𝓝 0) := by
  let m := fun k => (A k).val.centeredMartingalePart
  let v := fun k t ω => (A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω
  obtain ⟨hMart, hPred, hPaths⟩ :=
    component_series_of_summable_stopped_cost A T hLeft hConst hSum
  have hmR : ∀ n ω t, ContinuousWithinAt
      (fun s => ∑ k ∈ Finset.range n, m k s ω) (Ici t) t := by
    intro n ω t
    induction n with
    | zero => simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Ici t) t)
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      convert ih.add (((A n).val.martingalePart_isRightContinuous ω t).sub
        (continuousWithinAt_const (b := (A n).val.martingalePart 0 ω))) using 1
      rfl
  have hmL : ∀ n, ProcessHasLeftLimits (fun t ω => ∑ k ∈ Finset.range n, m k t ω) := by
    intro n
    induction n with
    | zero => simpa using (ProcessHasLeftLimits.timeConstant (fun _ : Ω => (0 : Real)))
    | succ n ih =>
      simpa only [Finset.sum_range_succ, m, SIntegrableStrategy.centeredMartingalePart] using
        ih.add ((hLeft n).sub (.timeConstant _))
  have hvR : ∀ n ω t, ContinuousWithinAt
      (fun s => ∑ k ∈ Finset.range n, v k s ω) (Ici t) t := by
    intro n ω t
    induction n with
    | zero => simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Ici t) t)
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      convert ih.add (((A n).val.finiteVariationPart_isRightContinuous ω t).sub
        (continuousWithinAt_const (b := (A n).val.finiteVariationPart 0 ω))) using 1
  obtain ⟨M, hMA, hMR, hML, hMEq⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hMart.stronglyAdapted (hPaths.mono fun ω hω =>
        ⟨rightContinuous_of_tendstoUniformly _ _ hω.1 (fun n => hmR n ω),
          leftLimits_of_tendstoUniformly _ _ hω.1 (fun n => hmL n ω)⟩)
  obtain ⟨V, hVP, hVR, hVBV, hVEq⟩ :=
    ProcessNullSetRegularization.exists_predictable_rightContinuous_boundedVariation_version
      hUsual hPred (hPaths.mono fun ω hω =>
        ⟨rightContinuous_of_tendstoUniformly _ _ hω.2.2.1 (fun n => hvR n ω), hω.2.1⟩)
  refine ⟨M, V, hMart.congr hMA (fun t => hMEq.symm.mono fun ω hω => hω t),
    hVP, hMR, hML, hVR, hVBV, ?_, ?_, hMEq, hVEq, ?_⟩
  · filter_upwards [hMEq] with ω hω
    rw [hω 0]
    simp [SIntegrableStrategy.centeredMartingalePart]
  · filter_upwards [hVEq] with ω hω
    rw [hω 0]
    simp
  · filter_upwards [hPaths, hMEq, hVEq] with ω hω hm hv
    have hm' : (M · ω) = (fun t => ∑' k, m k t ω) := funext hm
    have hv' : (V · ω) = (fun t => ∑' k, v k t ω) := funext hv
    change TendstoUniformly _ (M · ω) atTop ∧ TendstoUniformly _ (V · ω) atTop ∧ _
    rw [hm', hv']
    simp_rw [hv]
    exact ⟨hω.1, hω.2.2.1, hω.2.2.2⟩

end FTAPTheorem42.ActualSIntegrableStrategy

namespace FTAPTheorem42.ActualSIntegrableStrategy

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ} {R : SIntegrableRealizationModel D}

/-- Add the actual initial term to the regularized increment series, retaining
the components of the supplied raw telescoping approximants. -/
theorem exists_regular_telescoping_component_limit
    (hUsual : Filtration.UsualConditions μ F)
    (A P : Nat → ActualSIntegrableStrategy R) (T : NNReal)
    (hLeft : ∀ k, ProcessHasLeftLimits (A k).val.martingalePart)
    (hConst : ∀ k ω t, T ≤ t →
      (A k).val.martingalePart t ω = (A k).val.martingalePart T ω ∧
      (A k).val.finiteVariationPart t ω = (A k).val.finiteVariationPart T ω)
    (hSum : (∑' k, ((∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |(A k).val.centeredMartingalePart t.1 ω| ∂μ) +
      ∫⁻ ω, eVariationOn ((A k).val.finiteVariationPart · ω) (Icc 0 T) ∂μ)) ≠ ∞)
    (hZero : ∀ k, (A k).val.martingalePart 0 = 0 ∧ (A k).val.finiteVariationPart 0 = 0)
    (hRec : ∀ n, (P (n + 1)).val = (P n).val.add_of_rightContinuous (A n).val)
    (hPLeft : ProcessHasLeftLimits (P 0).val.martingalePart)
    (hPZero : (P 0).val.martingalePart 0 = 0 ∧ (P 0).val.finiteVariationPart 0 = 0) :
    ∃ M V : Process Ω,
      StronglyAdapted F M ∧ LocalMartingale M F μ ∧ IsStronglyPredictable F V ∧
      (∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t) ∧ ProcessHasLeftLimits M ∧
      (∀ ω t, ContinuousWithinAt (V · ω) (Ici t) t) ∧
      (∀ ω, BoundedVariationOn (V · ω) univ) ∧ M 0 =ᵐ[μ] 0 ∧ V 0 =ᵐ[μ] 0 ∧
      ∀ᵐ ω ∂μ,
        TendstoUniformly (fun n t => (P n).val.martingalePart t ω) (M · ω) atTop ∧
        TendstoUniformly (fun n t => (P n).val.finiteVariationPart t ω) (V · ω) atTop ∧
        Tendsto (fun n => eVariationOn
          (fun t => V t ω - (P n).val.finiteVariationPart t ω) univ) atTop (𝓝 0) ∧
        ∀ t, Tendsto (fun n => (P n).val.stochasticIntegral t ω) atTop (𝓝 (M t ω + V t ω)) := by
  obtain ⟨M, V, hMM, hVP, hMR, hML, hVR, hVBV, hM0, hV0, _, _, hU⟩ :=
    exists_regular_component_series hUsual A T hLeft hConst hSum
  have hMEq : ∀ n t ω, (P n).val.martingalePart t ω =
      (P 0).val.martingalePart t ω +
        ∑ k ∈ Finset.range n, (A k).val.centeredMartingalePart t ω := by
    intro n t ω
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hRec]
      change (P n).val.martingalePart t ω + (A n).val.martingalePart t ω = _
      rw [ih, Finset.sum_range_succ]
      simp only [SIntegrableStrategy.centeredMartingalePart, (hZero n).1, Pi.zero_apply, sub_zero]
      ring
  have hVEq : ∀ n t ω, (P n).val.finiteVariationPart t ω =
      (P 0).val.finiteVariationPart t ω + ∑ k ∈ Finset.range n,
        ((A k).val.finiteVariationPart t ω - (A k).val.finiteVariationPart 0 ω) := by
    intro n t ω
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hRec]
      change (P n).val.finiteVariationPart t ω + (A n).val.finiteVariationPart t ω = _
      rw [ih, Finset.sum_range_succ]
      simp only [(hZero n).2, Pi.zero_apply, sub_zero]
      ring
  refine ⟨(fun t ω => (P 0).val.martingalePart t ω + M t ω),
    (fun t ω => (P 0).val.finiteVariationPart t ω + V t ω),
    (P 0).val.martingalePart_isStronglyAdapted.add hMM.stronglyAdapted,
    (P 0).val.martingalePart_isLocalMartingale.add_of_rightContinuous
      (Locally.of_prop hMM) (P 0).val.martingalePart_isRightContinuous hMR,
    (P 0).val.finiteVariationPart_isPredictable.add hVP,
    fun ω t => ((P 0).val.martingalePart_isRightContinuous ω t).add (hMR ω t),
    hPLeft.add hML,
    fun ω t => ((P 0).val.finiteVariationPart_isRightContinuous ω t).add (hVR ω t),
    fun ω => ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨(P 0).val.finiteVariationPart_isBoundedVariation ω, hVBV ω⟩)
      (eVariationOn_add_le_real _ _ univ), ?_, ?_, ?_⟩
  · simpa only [hPZero.1, Pi.zero_apply, zero_add] using hM0
  · simpa only [hPZero.2, Pi.zero_apply, zero_add] using hV0
  have hDecomp : ∀ᵐ ω ∂μ, ∀ n t, (P n).val.stochasticIntegral t ω =
      (P n).val.martingalePart t ω + (P n).val.finiteVariationPart t ω := by
    exact ae_all_iff.mpr (fun n => (P n).val.integral_decomposition)
  filter_upwards [hU, hDecomp] with ω hω hDω
  have hc (f : NNReal → Real) : TendstoUniformly (fun _ : Nat => f) f atTop :=
    fun _ hu => Eventually.of_forall fun _ _ => refl_mem_uniformity hu
  have hm := (hc ((P 0).val.martingalePart · ω)).add hω.1
  have hv := (hc ((P 0).val.finiteVariationPart · ω)).add hω.2.1
  have hm' : TendstoUniformly (fun n t => (P n).val.martingalePart t ω)
      (fun t => (P 0).val.martingalePart t ω + M t ω) atTop := by
    convert hm using 1
    funext n t
    exact hMEq n t ω
  have hv' : TendstoUniformly (fun n t => (P n).val.finiteVariationPart t ω)
      (fun t => (P 0).val.finiteVariationPart t ω + V t ω) atTop := by
    convert hv using 1
    funext n t
    exact hVEq n t ω
  refine ⟨hm', hv', ?_, fun t => ?_⟩
  · convert hω.2.2 using 1
    funext n
    congr 1
    funext t
    rw [hVEq n t ω]
    ring
  · exact ((hm'.tendsto_at t).add (hv'.tendsto_at t)).congr'
      (Eventually.of_forall fun n => (hDω n t).symm)

end FTAPTheorem42.ActualSIntegrableStrategy
