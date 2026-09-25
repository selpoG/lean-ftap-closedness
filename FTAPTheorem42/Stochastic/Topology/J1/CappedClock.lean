/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.Triangle
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Pathwise summability of the clocks used for common localization -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

private theorem tsum_ne_top_of_capped_tsum_ne_top {a : Nat → ENNReal}
    (ha : ∀ k, a k ≠ ∞) (hCap : (∑' k, min (a k) 1) ≠ ∞) : (∑' k, a k) ≠ ∞ := by
  have hZero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hCap
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hZero).2 1 (by norm_num))
  have hTail : ∀ k, a (k + N) = min (a (k + N)) 1 := by
    intro k
    have hk := hN (k + N) (Nat.le_add_left N k)
    exact (min_eq_left ((min_lt_iff.mp hk).resolve_right (lt_irrefl _)).le).symm
  have hTailFinite : (∑' k, a (k + N)) ≠ ∞ := by
    have hEq : (∑' k, a (k + N)) = ∑' k, min (a (k + N)) 1 := tsum_congr hTail
    have hLe : (∑' k, min (a (k + N)) 1) ≤ ∑' k, min (a k) 1 :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (show Function.Injective (fun k : Nat => k + N) from
          fun i j hij => Nat.add_right_cancel hij)
        (fun k => min (a k) 1)
    exact ne_top_of_le_ne_top hCap (hEq.le.trans hLe)
  have hSplit := (ENNReal.summable : Summable (fun k => a (k + N))).sum_add_tsum_nat_add'
  rw [← hSplit]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr (fun k _ => ha k), hTailFinite⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

noncomputable def J1Decomposition.clock (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (t : NNReal) (w : Ω) : ENNReal :=
  ENNReal.ofReal (Real.sqrt (Q.variation t w)) + eVariationOn (D.A · w) (Icc 0 t)

theorem J1Decomposition.clock_ne_top (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (t : NNReal) (w : Ω) :
    D.clock Q t w ≠ ∞ := by
  apply ENNReal.add_ne_top.mpr
  exact ⟨ENNReal.ofReal_ne_top, by
    simpa only [BoundedVariationOn, univ_inter] using
      D.variationA w 0 t (mem_univ _) (mem_univ _)⟩

theorem J1Decomposition.clock_monotone (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (w : Ω) :
    Monotone (fun t => D.clock Q t w) := by
  intro s t hst
  exact add_le_add (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (Q.monotone w hst)))
    (eVariationOn.mono _ (Icc_subset_Icc_right hst))

theorem J1Decomposition.clock_measurable (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (t : NNReal) :
    Measurable (D.clock Q t) :=
  (((Q.stronglyAdapted t).mono (F.le t)).measurable.sqrt.ennreal_ofReal).add
    (SIntegrableFiniteVariationBridge.measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
      D.adaptedA D.rightA)

theorem J1Decomposition.ae_allTime_tsum_clock_ne_top_of_capped
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) :
    ∀ᵐ w ∂mu, ∀ t : NNReal, (∑' k, (D k).clock (Q k) t w) ≠ ∞ := by
  have hInteger : ∀ n : Nat, ∀ᵐ w ∂mu,
      (∑' k, (D k).clock (Q k) (n : NNReal) w) ≠ ∞ := by
    intro n
    have hMeas : ∀ k, Measurable (fun w => min ((D k).clock (Q k) (n : NNReal) w) 1) :=
      fun k => ((D k).clock_measurable (Q k) _).min measurable_const
    have hInt : (∫⁻ w, ∑' k, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞ := by
      rw [lintegral_tsum (fun k => (hMeas k).aemeasurable)]
      exact hCap n
    filter_upwards [ae_lt_top (Measurable.tsum hMeas) hInt] with w hw
    exact tsum_ne_top_of_capped_tsum_ne_top (fun k => (D k).clock_ne_top (Q k) _ w) hw.ne
  filter_upwards [ae_all_iff.mpr hInteger] with w hw
  intro t
  exact ne_top_of_le_ne_top (hw (Nat.ceil t)) (ENNReal.tsum_le_tsum (fun k =>
    (D k).clock_monotone (Q k) w (Nat.le_ceil t)))

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Right continuity of the common decomposition clock -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem J1Decomposition.clock_toReal_rightContinuous (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (w : Ω) (t : NNReal) :
    ContinuousWithinAt (fun s => (D.clock Q s w).toReal) (Ici t) t := by
  have hV : ContinuousWithinAt (variationOnFromTo (D.A · w) univ 0) (Ici t) t := by
    have hRight := (D.rightA w t).mono Ioi_subset_Ici_self
    change Tendsto (D.A · w) (𝓝[>] t) (𝓝 (D.A t w)) at hRight
    have h := variationOnFromTo.tendsto_right (mem_univ 0) (mem_univ t)
      (D.variationA w) (by simpa only [univ_inter] using hRight)
    have hOpen : ContinuousWithinAt (variationOnFromTo (D.A · w) univ 0) (Ioi t) t := by
      change Tendsto _ (𝓝[>] t) (𝓝 _)
      simpa only [univ_inter, dist_self, add_zero] using h
    have hSet : insert t (Ioi t) = Ici t := by ext s; simp [le_iff_eq_or_lt]
    rw [← hSet]
    exact hOpen.insert
  have hEq : (fun s => (D.clock Q s w).toReal) =
      (fun s => Real.sqrt (Q.variation s w) + variationOnFromTo (D.A · w) univ 0 s) := by
    funext s
    rw [J1Decomposition.clock, ENNReal.toReal_add ENNReal.ofReal_ne_top
      ((ENNReal.add_ne_top.mp (D.clock_ne_top Q s w)).2),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ s from bot_le),
      univ_inter]
  rw [hEq]
  exact (Q.rightContinuous w t).sqrt.add hV

theorem J1Decomposition.ae_rightContinuous_tsum_clock_of_capped
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) :
    ∀ᵐ w ∂mu,
      (∀ t : NNReal, (∑' k, (D k).clock (Q k) t w) ≠ ∞) ∧
      Monotone (fun s => ∑' k, ((D k).clock (Q k) s w).toReal) ∧
      ∀ t : NNReal, ContinuousWithinAt
        (fun s => ∑' k, ((D k).clock (Q k) s w).toReal) (Ici t) t := by
  filter_upwards [J1Decomposition.ae_allTime_tsum_clock_ne_top_of_capped D Q hCap] with w hw
  have hSummable : ∀ t, Summable (fun k => ((D k).clock (Q k) t w).toReal) :=
    fun t => ENNReal.summable_toReal (hw t)
  refine ⟨hw, ?_, ?_⟩
  · intro s t hst
    exact (hSummable s).tsum_le_tsum (fun k =>
      ENNReal.toReal_mono ((D k).clock_ne_top (Q k) t w)
        ((D k).clock_monotone (Q k) w hst)) (hSummable t)
  intro t
  apply tendsto_tsum_of_dominated_convergence (hSummable (t + 1))
  · intro k
    exact (D k).clock_toReal_rightContinuous (Q k) w t
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (show t < t + 1 by exact lt_add_one t))] with s hs
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono ((D k).clock_ne_top (Q k) (t + 1) w)
      ((D k).clock_monotone (Q k) w hs.le)

end FTAPTheorem42
