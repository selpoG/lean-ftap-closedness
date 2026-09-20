/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessApproximationRealization

/-! # Initial values and composition of realized integral gains -/

namespace FTAPTheorem42.PredictableElementaryEmery

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The stored gain starts at zero because its elementary representatives
converge in the compact-uniform gauge, which includes time zero. -/
theorem RealizedStrategy.gain_initial_eq_zero
    (S : Process Ω) (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (H : RealizedStrategy (ℱ := F) μ S) : H.gain 0 =ᵐ[μ] 0 := by
  obtain ⟨f, _hf, hAE⟩ := (H.gain_convergence 0).exists_seq_tendsto_ae
  filter_upwards [hAE] with ω hω
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  let δ : Real := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨n, hn⟩ := (hω.eventually (gt_mem_nhds hδ)).exists
  have hEnv := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_lt_of_capped_lt
    (fun t ω => elementaryGain S (H.representative (f n)) t ω - H.gain t ω)
    1 ω hδ.le (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    (by simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using hn)
  have hVal := FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
    (fun t ω => |elementaryGain S (H.representative (f n)) t ω - H.gain t ω|)
    1 (fun ω t => (((H.representative (f n)).rightContinuous_gain S hSR ω t).sub
      (H.gain_rightContinuous ω t)).abs) ω (show (0 : NNReal) ≤ 1 by norm_num)
  have hlt := (ENNReal.ofReal_lt_ofReal_iff hδ).mp (hVal.trans_lt hEnv)
  have hz : elementaryGain S (H.representative (f n)) 0 ω = 0 := by
    simp [elementaryGain, ElementaryStrategy.gain, ElementaryInterval.gain]
  simpa only [hz, zero_sub, abs_neg, zero_add] using
    hlt.trans_le (min_le_left ε (1 / 2))

end FTAPTheorem42.PredictableElementaryEmery

namespace FTAPTheorem42.PredictableElementaryEmery

/-! ## Composition of realized elementary integral gains

An integral against a realized gain is returned to the original price by
composing elementary rows and then taking their uniform-test limit.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Process Ω}

/-- Each stored realized gain retains elementary approximants with the
same deterministic row bounds. -/
theorem RealizedStrategy.elementaryApproximable
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (R : RealizedStrategy (ℱ := F) μ S) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S R.gain := by
  intro T ε hε
  obtain ⟨n, hn⟩ := (R.elementaryEmeryConverges hS hSR T ε hε).exists
  exact ⟨R.representative n, R.representativeBound n,
    R.representative_coefficientAbsSum_le n, hn⟩

/-- A deterministic coefficient bound suffices for an arbitrary elementary
transform: normalize the test, apply the existing transform, and rescale. -/
theorem RealizedStrategy.exists_elementaryTransform
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (R : RealizedStrategy (ℱ := F) μ S)
    (J : PredictableElementaryStrategy F) (C : NNReal)
    (hC : ∀ ω, J.coefficientAbsSum ω ≤ C) :
    ∃ V : RealizedStrategy (ℱ := F) μ S, V.gain = elementaryGain R.gain J := by
  let c : Real := max (C : Real) 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let L := J.posSMul c⁻¹ (inv_pos.mpr hc)
  have hL ω : L.coefficientAbsSum ω ≤ (1 : NNReal) := by
    change L.coefficientAbsSum ω ≤ (1 : Real)
    rw [PredictableElementaryStrategy.coefficientAbsSum_posSMul]
    calc
      c⁻¹ * J.coefficientAbsSum ω ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left ((hC ω).trans (le_max_left _ _)) (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  let U : CoefficientBoundedPredictableElementaryMultiplier (Ω := Ω) F := {
    strategy := L
    abs_integrand_le_one := by
      intro t ω
      exact (L.abs_integrand_le_coefficientAbsSum t ω).trans (hL ω)
    coefficientAbsSumBound := 1
    coefficientAbsSum_le := hL }
  let V := (R.transform S hS hSR U).posSMul S hS c hc
  refine ⟨V, ?_⟩
  funext t ω
  change c * elementaryGain R.gain (J.posSMul c⁻¹ (inv_pos.mpr hc)) t ω = _
  rw [elementaryGain_posSMul]
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- Approximation against a realized gain composes to approximation against
the same original price. No new-price market is substituted. -/
theorem RealizedStrategy.elementaryApproximable_comp
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (R : RealizedStrategy (ℱ := F) μ S)
    {X : Process Ω} (hXP : IsStronglyProgressive F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hApprox : ElementaryEmeryApproximable (F := F) (μ := μ) R.gain X) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S X := by
  have hRP := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    R.gain_stronglyAdapted R.gain_rightContinuous
  obtain ⟨J, C, hC, hConv⟩ := hApprox.exists_convergent_sequence
    hRP R.gain_rightContinuous hXP hXR
  choose V hV using fun n => R.exists_elementaryTransform hS hSR (J n) (C n) (hC n)
  have hApproxV n := (V n).elementaryApproximable hS hSR
  apply ElementaryEmeryApproximable.of_converges hS hSR
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (V n).gain_stronglyAdapted (V n).gain_rightContinuous) hXP hApproxV
  simpa only [hV] using hConv

end FTAPTheorem42.PredictableElementaryEmery
