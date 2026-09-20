/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.ElementaryScalarTopology
import FTAPTheorem42.Stochastic.Topology.Emery.GainSemimartingale
import FTAPTheorem42.Stochastic.Topology.Emery.InnerJumpMeasure

/-! # From original-source realized representatives to R1 localization -/

namespace FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- The representatives of an original-source realization approach its
stored gain in R1. Decompositions and a regular limit are generated internally. -/
theorem tendsto_r1_error (hUsual : Filtration.UsualConditions μ F)
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits S) (hGI : IsSemimartingale S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    Tendsto (fun n => semimartingaleR1
      (elementaryGain S (H.representative n) - H.gain) F μ) atTop (𝓝 0) := by
  let : Fact (Filtration.UsualConditions μ F) := ⟨hUsual⟩
  let X := fun n => elementaryGain S (H.representative n)
  have hXA : ∀ n, StronglyAdapted F (X n) := fun n =>
    PredictableElementaryStrategy.stronglyAdapted_gain S hS (H.representative n)
  have hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t := fun n =>
    PredictableElementaryStrategy.rightContinuous_gain S hRight (H.representative n)
  have hXL : ∀ n, ProcessHasLeftLimits (X n) := fun n =>
    ElementaryStrategy.gain_hasLeftLimits S hLeft (H.representative n).toElementary
  have hXP : ∀ n, IsStronglyProgressive F (X n) := fun n =>
    StronglyAdapted.isStronglyProgressive_of_rightContinuous (hXA n) (hXR n)
  have hX0 : ∀ n, X n 0 = 0 := by
    intro n
    funext w
    simp [X, elementaryGain, ElementaryStrategy.gain, ElementaryInterval.gain]
  have hXGI : ∀ n, IsSemimartingale (X n) F μ := fun n =>
    (RealizedStrategy.constant S hS hRight hLeft (H.representative n)
      (H.representativeBound n) (H.representative_coefficientAbsSum_le n)).gain_isSemimartingale
      S hS hRight hLeft hGI
  let R : Nat → R1Process F μ := fun n => ⟨X n,
    exists_j1Decomposition_of_goodIntegrator_cadlag_zero hUsual (hXGI n)
      (hXA n) (hXR n) (hXL n) (hX0 n)⟩
  have hHG := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    H.gain_stronglyAdapted H.gain_rightContinuous
  have hConv := H.elementaryEmeryConverges hS hRight
  obtain ⟨Y, hYP, hYR, _, hY0, hY⟩ :=
    R1Process.exists_elementaryEmery_limit hUsual R (hConv.cauchy hXP hHG)
  have hEq : ProcessIndistinguishable μ Y.val H.gain :=
    FactorialChronologicalGrid.processIndistinguishable_of_common_cappedFiniteHorizon_limit
      X Y.val H.gain hYR H.gain_rightContinuous
      (fun r => hY.ucp hXP hYP
        (fun n => Eventually.of_forall fun w => by
          change X n 0 w = Y.val 0 w
          rw [hX0, hY0]) _) H.gain_convergence
  have hCost := ElementaryMetricProcess.tendsto_r1_of_elementary R Y hY
  apply hCost.congr'
  apply Eventually.of_forall
  intro n
  apply semimartingaleR1_congr
  filter_upwards [hEq] with w hw
  intro t
  change X n t w - Y.val t w = X n t w - H.gain t w
  rw [hw t]

end FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

namespace FTAPTheorem42

/-! ## One measure and one selection for R1 cost and growing-horizon error -/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

private theorem exists_strictMono_summable_pair {a b : Nat → ENNReal}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    ∃ f : Nat → Nat, StrictMono f ∧ (∑' k, a (f k)) ≤ 1 ∧ (∑' k, b (f k)) ≤ 1 := by
  let e : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have h : Tendsto (fun n => a n + b n) atTop (𝓝 0) := by simpa using ha.add hb
  obtain ⟨f, hf, hSmall⟩ := extraction_forall_of_eventually (fun k =>
    h (Iio_mem_nhds (show 0 < e k from
      ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _)))
  have hSum : (∑' k, (a (f k) + b (f k))) ≤ 1 := by
    calc
      _ ≤ ∑' k, e k := ENNReal.tsum_le_tsum fun k => (hSmall k).le
      _ = 1 := by
        simp only [e]
        rw [ENNReal.tsum_geometric_add_one]
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  exact ⟨f, hf, (ENNReal.tsum_le_tsum fun _ => le_add_right le_rfl).trans hSum,
    (ENNReal.tsum_le_tsum fun _ => le_add_left le_rfl).trans hSum⟩

namespace PredictableElementaryEmery.RealizedStrategy

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Fix the tilt before constructing R1 decompositions, and retain its L2
envelope while selecting both error costs at once. -/
theorem exists_summable_r1_and_error_envelope
    (hUsual : Filtration.UsualConditions μ F)
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits S) (hGI : IsSemimartingale S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (f : Nat → Nat) (Q : Measure Ω) (HQ : RealizedStrategy (ℱ := F) Q S),
      StrictMono f ∧ IsProbabilityMeasure Q ∧ Q ≪ μ ∧ μ ≪ Q ∧
      Filtration.UsualConditions Q F ∧ IsSemimartingale S F Q ∧
      HQ.representative = H.representative ∧ HQ.gain = H.gain ∧
      ∃ η : Ω → Real, Measurable η ∧ (∀ w, 0 ≤ η w) ∧
      Q = CommonEnvelopeMeasure.tilted μ η ∧ MemLp η 2 Q ∧
      (∀ᵐ w ∂Q, ∀ k,
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (elementaryGain S (HQ.representative (f k)) - HQ.gain)
          ((k + 1 : Nat) : NNReal) w ≤ η w) ∧
      (∑' k, semimartingaleR1
        (elementaryGain S (HQ.representative (f k)) - HQ.gain) F Q) ≤ 1 ∧
      (∑' k, ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (elementaryGain S (HQ.representative (f k)) - HQ.gain)
          ((k + 1 : Nat) : NNReal) w) ∂Q) ≤ 1 := by
  obtain ⟨c, Q, HQ, hc, hQ, hQμ, hμQ, hSQ, hRep, hGain,
    η, hηMeas, hηPos, hTilt, hηL2, hDom, hErr⟩ :=
    H.exists_growingHorizon_L2_error_envelope S hS hGI
  let : IsProbabilityMeasure Q := hQ
  have hUsualQ := hUsual.mono_ac hμQ
  have hR1 := (HQ.tendsto_r1_error hUsualQ hS hRight hLeft hSQ).comp hc.tendsto_atTop
  obtain ⟨g, hg, hSumR1, hSumErr⟩ := exists_strictMono_summable_pair hR1 hErr
  have hMono : ∀ k w,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (HQ.representative (c (g k))) - HQ.gain)
        ((k + 1 : Nat) : NNReal) w ≤
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (HQ.representative (c (g k))) - HQ.gain)
        ((g k + 1 : Nat) : NNReal) w := by
    intro k w
    apply FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_mono
      (fun w t => (PredictableElementaryStrategy.rightContinuous_gain S hRight
        (HQ.representative (c (g k))) w t).sub (HQ.gain_rightContinuous w t))
      ((ElementaryStrategy.gain_hasLeftLimits S hLeft
        (HQ.representative (c (g k))).toElementary).sub HQ.gain_hasLeftLimits)
    exact_mod_cast Nat.succ_le_succ (hg.id_le k)
  refine ⟨c ∘ g, Q, HQ, hc.comp hg, hQ, hQμ, hμQ, hUsualQ, hSQ, hRep, hGain,
    η, hηMeas, hηPos, hTilt, hηL2, ?_, hSumR1, ?_⟩
  · filter_upwards [hDom] with w hw
    exact fun k => (hMono k w).trans (hw (g k))
  · exact (ENNReal.tsum_le_tsum fun k => lintegral_mono fun w =>
      ENNReal.ofReal_le_ofReal (hMono k w)).trans hSumErr

end PredictableElementaryEmery.RealizedStrategy

end FTAPTheorem42
