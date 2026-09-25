/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.CappedClock

/-! # A common passage for a summable family of decomposition clocks -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem J1Decomposition.clock_toReal_stronglyAdapted (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) :
    StronglyAdapted F (fun t w => (D.clock Q t w).toReal) := by
  intro t
  change StronglyMeasurable[F t] (fun w => (D.clock Q t w).toReal)
  have hV : Measurable[F t] (fun w => variationOnFromTo (D.A · w) univ 0 t) :=
    @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
      Ω Real (F t) _ _ _ _ D.A t
      (fun s hs => ((D.adaptedA s).mono (F.mono hs)).measurable) D.rightA
  have hEq : (fun w => (D.clock Q t w).toReal) =
      (fun w => Real.sqrt (Q.variation t w) + variationOnFromTo (D.A · w) univ 0 t) := by
    funext w
    rw [J1Decomposition.clock, ENNReal.toReal_add ENNReal.ofReal_ne_top
      ((ENNReal.add_ne_top.mp (D.clock_ne_top Q t w)).2),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le), univ_inter]
  rw [hEq]
  exact ((Q.stronglyAdapted t).measurable.sqrt.add hV).stronglyMeasurable

theorem J1Decomposition.exists_common_clock_passage_of_capped
    [F.IsRightContinuous] (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) :
    ∃ U : Process Ω,
      StronglyAdapted F U ∧
      (∀ w t, ContinuousWithinAt (U · w) (Ici t) t) ∧ ProcessHasLeftLimits U ∧
      IsLocalizingSequence F (cadlagAbsolutePassageLocalizer U) mu ∧
      (∀ r w, cadlagAbsolutePassageLocalizerFinite U r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ᵐ w ∂mu,
        (∀ t : NNReal, (∑' k, (D k).clock (Q k) t w) ≠ ∞) ∧
        (∀ t, U t w = ∑' k, ((D k).clock (Q k) t w).toReal) ∧
        ∀ r t, t < cadlagAbsolutePassageLocalizerFinite U r w →
          (∑' k, ((D k).clock (Q k) t w).toReal) ≤ (r + 1 : Nat) := by
  let V : Process Ω := fun t w => ∑' k, ((D k).clock (Q k) t w).toReal
  have hV : StronglyAdapted F V := by
    intro t
    let f : Nat → Ω → Real := fun k w => ((D k).clock (Q k) t w).toReal
    have hf : ∀ k, Measurable[F t] (f k) :=
      fun k => ((D k).clock_toReal_stronglyAdapted (Q k) t).measurable
    let : MeasurableSpace Ω := F t
    change StronglyMeasurable (fun w => ∑' k, f k w)
    apply Measurable.stronglyMeasurable
    apply Measurable.tsum
    intro k
    exact hf k
  have hGood := J1Decomposition.ae_rightContinuous_tsum_clock_of_capped D Q hCap
  have hRegular : ∀ᵐ w ∂mu, (∀ t, ContinuousWithinAt (V · w) (Ici t) t) ∧
      ∀ t, Tendsto (V · w) (𝓝[<] t) (𝓝 (Function.leftLim (V · w) t)) := by
    filter_upwards [hGood] with w hw
    exact ⟨hw.2.2, fun t => hw.2.1.tendsto_leftLim t⟩
  obtain ⟨U, hU, hRight, hLeft, hEq⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hV hRegular
  refine ⟨U, hU, hRight, hLeft,
    cadlagAbsolutePassageLocalizer_isLocalizingSequence hU hRight hLeft,
    cadlagAbsolutePassageLocalizerFinite_le_horizon U, ?_⟩
  filter_upwards [hGood, hEq] with w hw hSame
  refine ⟨hw.1, hSame, ?_⟩
  intro r t ht
  have ht' : (t : WithTop NNReal) < cadlagAbsolutePassageLocalizer U r w := by
    rw [← coe_cadlagAbsolutePassageLocalizerFinite]
    exact WithTop.coe_lt_coe.mpr ht
  have hHit : (t : WithTop NNReal) < absoluteStrictHittingAfter U (cadlagPassageLevel r) w :=
    ht'.trans_le (min_le_left _ _)
  have hBound := abs_le_of_lt_absoluteStrictHittingAfter U (cadlagPassageLevel r) w t hHit
  change V t w ≤ _
  rw [← hSame t]
  exact (le_abs_self _).trans hBound

/-! ## The left-limit clock sum at the common passage -/

noncomputable def J1Decomposition.leftClock (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (t : NNReal) (w : Ω) : Real :=
  Real.sqrt (Function.leftLim (Q.variation · w) t) +
    Function.leftLim (variationOnFromTo (D.A · w) univ 0) t

theorem J1Decomposition.tendsto_clock_leftClock (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (t : NNReal) (w : Ω) :
    Tendsto (fun s => (D.clock Q s w).toReal) (𝓝[<] t) (𝓝 (D.leftClock Q t w)) := by
  have hMono : Monotone (variationOnFromTo (D.A · w) univ 0) := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn (D.variationA w) (mem_univ 0)
  have hEq : (fun s => (D.clock Q s w).toReal) =
      (fun s => Real.sqrt (Q.variation s w) + variationOnFromTo (D.A · w) univ 0 s) := by
    funext s
    rw [J1Decomposition.clock, ENNReal.toReal_add ENNReal.ofReal_ne_top
      ((ENNReal.add_ne_top.mp (D.clock_ne_top Q s w)).2),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ s from bot_le), univ_inter]
  rw [hEq]
  exact ((Q.leftLimits w t).sqrt).add (hMono.tendsto_leftLim t)

theorem J1Decomposition.leftClock_zero (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (w : Ω) : D.leftClock Q 0 w = 0 := by
  unfold leftClock
  rw [leftLim_eq_of_isBot (a := (0 : NNReal)) isBot_bot,
    leftLim_eq_of_isBot (a := (0 : NNReal)) isBot_bot, Q.zero]
  simp only [Pi.zero_apply, Real.sqrt_zero, variationOnFromTo.self, add_zero]

theorem J1Decomposition.tsum_leftClock_le_of_before
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (w : Ω) (tau : NNReal) {b : Real}
    (hFinite : ∀ t, (∑' k, (D k).clock (Q k) t w) ≠ ∞)
    (hBefore : ∀ t, t < tau → (∑' k, ((D k).clock (Q k) t w).toReal) ≤ b) :
    (∑' k, ENNReal.ofReal ((D k).leftClock (Q k) tau w)) ≤ ENNReal.ofReal b := by
  by_cases ht : tau = 0
  · subst tau
    simp only [leftClock_zero, ENNReal.ofReal_zero, tsum_zero]
    exact bot_le
  let : NeBot (𝓝[<] tau) := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  have hLimit : Tendsto (fun t => ∑ k ∈ s, ENNReal.ofReal ((D k).clock (Q k) t w).toReal)
      (𝓝[<] tau) (𝓝 (∑ k ∈ s, ENNReal.ofReal ((D k).leftClock (Q k) tau w))) :=
    tendsto_finsetSum s (fun k _ =>
      ENNReal.tendsto_ofReal ((D k).tendsto_clock_leftClock (Q k) tau w))
  apply le_of_tendsto hLimit
  filter_upwards [self_mem_nhdsWithin] with t htau
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => ENNReal.toReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  exact ((ENNReal.summable_toReal (hFinite t)).sum_le_tsum s
    (fun k _ => ENNReal.toReal_nonneg)).trans (hBefore t htau)

theorem J1Decomposition.exists_common_passage_leftClock_bound
    [F.IsRightContinuous] (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) :
    ∃ U : Process Ω,
      StronglyAdapted F U ∧
      (∀ w t, ContinuousWithinAt (U · w) (Ici t) t) ∧ ProcessHasLeftLimits U ∧
      IsLocalizingSequence F (cadlagAbsolutePassageLocalizer U) mu ∧
      (∀ r w, cadlagAbsolutePassageLocalizerFinite U r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ᵐ w ∂mu,
        (∀ t, U t w = ∑' k, ((D k).clock (Q k) t w).toReal) ∧
        ∀ r, (∑' k, ENNReal.ofReal ((D k).leftClock (Q k)
          (cadlagAbsolutePassageLocalizerFinite U r w) w)) ≤ (r + 1 : Nat) := by
  obtain ⟨U, hU, hR, hL, hLoc, hT, hGood⟩ :=
    J1Decomposition.exists_common_clock_passage_of_capped hUsual D Q hCap
  refine ⟨U, hU, hR, hL, hLoc, hT, ?_⟩
  filter_upwards [hGood] with w hw
  refine ⟨hw.2.1, ?_⟩
  intro r
  simpa only [ENNReal.ofReal_natCast] using
    J1Decomposition.tsum_leftClock_le_of_before D Q w
      (cadlagAbsolutePassageLocalizerFinite U r w) hw.1 (hw.2.2 r)

end FTAPTheorem42
