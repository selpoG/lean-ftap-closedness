/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.Basic

/-! # The finite-variation sum of the retained global decompositions -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

theorem J1Decomposition.ae_variation_series_of_summable_r1Cost
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hSum : (∑' k, (D k).r1Cost (Q k)) ≠ ∞) :
    ∀ᵐ w ∂mu,
      LocallyBoundedVariationOn (fun t => ∑' k, (D k).A t w) univ ∧
      ∀ T : NNReal,
        TendstoUniformlyOn (fun n t => ∑ k ∈ Finset.range n, (D k).A t w)
          (fun t => ∑' k, (D k).A t w) atTop (Icc 0 T) ∧
        Tendsto (fun n => eVariationOn (fun t => (∑' k, (D k).A t w) -
          ∑ k ∈ Finset.range n, (D k).A t w) (Icc 0 T)) atTop (𝓝 0) := by
  obtain ⟨hCap, _⟩ := J1Decomposition.capped_and_jump_summable_of_r1Cost D Q hSum
  filter_upwards [J1Decomposition.ae_allTime_tsum_clock_ne_top_of_capped D Q hCap] with w hw
  have hStage (T : NNReal) := by
    let f : Nat → NNReal → Real := fun k t => (D k).A (min t T) w
    have hVar : ∀ k, eVariationOn (f k) univ ≤ eVariationOn ((D k).A · w) (Icc 0 T) := by
      intro k
      exact eVariationOn.comp_le_of_monotoneOn ((D k).A · w) (fun t => min t T)
        ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ)
        (fun _ _ => ⟨bot_le, min_le_right _ _⟩)
    have hFinite : (∑' k, eVariationOn (f k) univ) ≠ ∞ := by
      apply ne_top_of_le_ne_top (hw T)
      exact ENNReal.tsum_le_tsum (fun k => (hVar k).trans
        (show eVariationOn ((D k).A · w) (Icc 0 T) ≤ (D k).clock (Q k) T w from
          le_add_left le_rfl))
    exact variation_series_convergence f 0
      (fun k => by simp only [f, min_eq_left (show (0 : NNReal) ≤ T from bot_le),
        (D k).zeroA, Pi.zero_apply]) hFinite
  have hBV (T : NNReal) : BoundedVariationOn (fun t => ∑' k, (D k).A t w) (Icc 0 T) := by
    have h := (hStage T).1.mono (subset_univ (Icc 0 T))
    change eVariationOn _ _ ≠ ∞ at h ⊢
    have hEq := eVariationOn.congr (f := fun t => ∑' k, (D k).A (min t T) w)
      (g := fun t => ∑' k, (D k).A t w) (s := Icc 0 T)
      (fun t ht => by simp only [min_eq_left ht.2])
    dsimp only at h
    rwa [hEq] at h
  refine ⟨fun a b _ _ => (hBV b).mono (fun t ht => ⟨bot_le, ht.2.2⟩), ?_⟩
  intro T
  constructor
  · exact ((hStage T).2.1.tendstoUniformlyOn.congr
      (Eventually.of_forall (fun _ t ht => by simp only [min_eq_left ht.2]))).congr_right
      (fun t ht => by simp only [min_eq_left ht.2])
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hStage T).2.2
      (fun _ => bot_le)
    intro n
    have hEq := eVariationOn.congr
      (f := fun t => (∑' k, (D k).A (min t T) w) -
        ∑ k ∈ Finset.range n, (D k).A (min t T) w)
      (g := fun t => (∑' k, (D k).A t w) - ∑ k ∈ Finset.range n, (D k).A t w)
      (s := Icc 0 T) (fun t ht => by simp only [min_eq_left ht.2])
    dsimp only
    rw [← hEq]
    exact eVariationOn.mono _ (subset_univ _)

/-! ## A regular version of the retained finite-variation component series -/

theorem J1Decomposition.exists_regular_variation_series
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hSum : (∑' k, (D k).r1Cost (Q k)) ≠ ∞) :
    ∃ A : Process Ω, StronglyAdapted F A ∧
      (∀ w t, ContinuousWithinAt (A · w) (Ici t) t) ∧
      ProcessHasLeftLimits A ∧
      (∀ w, LocallyBoundedVariationOn (A · w) univ) ∧ A 0 = 0 ∧
      ProcessIndistinguishable mu A (fun t w => ∑' k, (D k).A t w) := by
  let X : Process Ω := fun t w => ∑' k, (D k).A t w
  have hAdapted : StronglyAdapted F X := by
    intro t
    have hMeas : ∀ k, @Measurable Ω Real (F t) _ ((D k).A t) :=
      fun k => ((D k).adaptedA t).measurable
    let : MeasurableSpace Ω := F t
    exact (Measurable.tsum hMeas).stronglyMeasurable
  have hRegular : ∀ᵐ w ∂mu,
      LocallyBoundedVariationOn (X · w) univ ∧
      ∀ t, ContinuousWithinAt (X · w) (Ici t) t := by
    filter_upwards [J1Decomposition.ae_variation_series_of_summable_r1Cost D Q hSum] with w hw
    refine ⟨hw.1, ?_⟩
    intro t
    have hU := (hw.2 (t + 1)).1
    have hFilter : 𝓝[Ici t] t ≤ 𝓟 (Icc 0 (t + 1)) := by
      apply le_principal_iff.mpr
      exact mem_of_superset (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one t)))
        (fun s hs => ⟨bot_le, hs.le⟩)
    have hUF := (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hU).mono_right hFilter
    apply hUF.tendsto_of_eventually_tendsto _
      (hU.tendsto_at (show t ∈ Icc 0 (t + 1) from ⟨bot_le, (lt_add_one t).le⟩))
    apply Eventually.of_forall
    intro n
    induction n with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : NNReal => (0 : Real)) (𝓝[Ici t] t) (𝓝 0))
    | succ n ih =>
      simpa only [Finset.sum_range_succ] using ih.add ((D n).rightA w t)
  let bad : Set Ω := {w | ¬(LocallyBoundedVariationOn (X · w) univ ∧
    ∀ t, ContinuousWithinAt (X · w) (Ici t) t)}
  have hNull : mu bad = 0 := ae_iff.mp hRegular
  have hOff : ∀ w, w ∉ bad → LocallyBoundedVariationOn (X · w) univ ∧
      ∀ t, ContinuousWithinAt (X · w) (Ici t) t := by
    intro w hw
    simpa only [bad, mem_ofPred_eq, not_not] using hw
  let A := ProcessNullSetRegularization.zeroOn bad X
  have hBV : ∀ w, LocallyBoundedVariationOn (A · w) univ :=
    ProcessNullSetRegularization.zeroOn_isLocallyBoundedVariation (fun w hw => (hOff w hw).1)
  refine ⟨A, ProcessNullSetRegularization.stronglyAdapted_zeroOn
    (hUsual.containsNullSetsAtZero bad hNull) hAdapted,
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun w hw => (hOff w hw).2),
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      hBV,
    hBV, ?_, ProcessNullSetRegularization.zeroOn_indistinguishable hNull X⟩
  funext w
  simp only [A, ProcessNullSetRegularization.zeroOn, X, (D _).zeroA, Pi.zero_apply, tsum_zero,
    ite_self]

/-! ## Capped expected variation of the tails of the retained component series -/

theorem J1Decomposition.tendsto_capped_variation_series_tail
    [IsFiniteMeasure mu]
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hSum : (∑' k, (D k).r1Cost (Q k)) ≠ ∞)
    {A : Process Ω} (hAdapted : StronglyAdapted F A)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (hEq : ProcessIndistinguishable mu A (fun t w => ∑' k, (D k).A t w)) (T : NNReal) :
    Tendsto (fun n => ∫⁻ w, min (eVariationOn
      (fun t => A t w - ∑ k ∈ Finset.range n, (D k).A t w) (Icc 0 T)) 1 ∂mu)
      atTop (𝓝 0) := by
  let P : Nat → Process Ω := fun n t w => ∑ k ∈ Finset.range n, (D k).A t w
  have hStep (n : Nat) : P (n + 1) = P n + (D n).A := by
    funext t w
    exact Finset.sum_range_succ _ _
  have hPA : ∀ n, StronglyAdapted F (P n) := by
    intro n
    induction n with
    | zero => exact fun _ => by simpa [P] using stronglyMeasurable_const (b := (0 : Real))
    | succ n ih => rw [hStep]; exact ih.add (D n).adaptedA
  have hPR : ∀ n w t, ContinuousWithinAt (P n · w) (Ici t) t := by
    intro n w t
    induction n with
    | zero => exact continuousWithinAt_const
    | succ n ih => rw [hStep]; exact ih.add ((D n).rightA w t)
  have hMeas (n : Nat) : Measurable (fun w => min
      (eVariationOn (fun t => A t w - P n t w) (Icc 0 T)) 1) :=
    (SIntegrableFiniteVariationBridge.measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
      (hAdapted.sub (hPA n)) (fun w t => (hRight w t).sub (hPR n w t))).min measurable_const
  have hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => min
      (eVariationOn (fun t => A t w - P n t w) (Icc 0 T)) 1) atTop (𝓝 0) := by
    filter_upwards [J1Decomposition.ae_variation_series_of_summable_r1Cost D Q hSum, hEq]
      with w hw heq
    have hV := (hw.2 T).2
    have hV' : Tendsto (fun n => eVariationOn
        (fun t => A t w - P n t w) (Icc 0 T)) atTop (𝓝 0) := by
      convert hV using 1
      exact funext (fun n => congrArg (fun f => eVariationOn f (Icc 0 T))
        (funext (fun t => by rw [heq t])))
    simpa only [zero_min] using hV'.min (tendsto_const_nhds (x := (1 : ENNReal)))
  have hInt := tendsto_lintegral_of_dominated_convergence' (fun _ : Ω => (1 : ENNReal))
    (fun n => (hMeas n).aemeasurable)
    (fun _ => Eventually.of_forall (fun _ => min_le_right _ _)) (by simp) hLimit
  simpa only [lintegral_zero] using hInt

end FTAPTheorem42
