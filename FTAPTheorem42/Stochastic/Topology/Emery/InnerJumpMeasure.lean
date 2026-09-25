/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Semimartingale
import FTAPTheorem42.Stochastic.Topology.Emery.MeasureTransfer
import FTAPTheorem42.Stochastic.Decomposition.Source.ConvexDecomposition
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralCadlag
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # One equivalent measure controlling the inner elementary representatives -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem exists_strictMono_diagonal_tendstoAE_zero
    {mu : Measure Ω} {f : Nat → Nat → Ω → Real}
    (h : ∀ r, TendstoInMeasure mu (fun n => f n r) atTop (fun _ => 0)) :
    ∃ cutoff : Nat → Nat, StrictMono cutoff ∧
      TendstoAE mu (fun k => f (cutoff k) k) (fun _ => 0) := by
  classical
  let q : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have hqPos : ∀ k, 0 < q k := fun _ =>
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  have hSmall : ∀ k, ∃ N, ∀ n, N ≤ n →
      mu {w | q k ≤ edist (f n k w) 0} ≤ q k := by
    intro k
    have he := (tendsto_order.1 (h k (q k) (hqPos k))).2 _ (hqPos k)
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    exact ⟨N, fun n hn => (hN n hn).le⟩
  choose threshold hThreshold using hSmall
  let cutoff : Nat → Nat := fun k => Nat.rec (threshold 0)
    (fun i previous => max (previous + 1) (threshold (i + 1))) k
  have hCut : ∀ k, threshold k ≤ cutoff k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  have hStrict : StrictMono cutoff := strictMono_nat_of_lt_succ (fun k =>
    (Nat.lt_succ_self (cutoff k)).trans_le (le_max_left _ _))
  have hSum : (∑' k, q k) ≠ ∞ := by
    simp only [q]
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
  have hGood := MeasureTheory.ae_eventually_notMem (μ := mu)
    (s := fun k => {w | q k ≤ edist (f (cutoff k) k w) 0})
    (ne_top_of_le_ne_top hSum (ENNReal.tsum_le_tsum (fun k =>
      hThreshold k (cutoff k) (hCut k))))
  have hq : Tendsto q atTop (𝓝 0) := by
    exact (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (2 : ENNReal)⁻¹ < 1)).comp (tendsto_add_atTop_nat 1)
  refine ⟨cutoff, hStrict, ?_⟩
  filter_upwards [hGood] with w hw
  apply EMetric.tendsto_atTop.2
  intro e he
  apply eventually_atTop.1
  filter_upwards [hw, (tendsto_order.1 hq).2 e he] with k hk hke
  exact (lt_of_not_ge hk).trans hke

namespace PredictableElementaryEmery

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]

/-- Retain the error envelope and the exact tilt used for the inner sequence. -/
theorem RealizedStrategy.exists_growingHorizon_L2_error_envelope
    (S : Process Ω) (hS : IsStronglyProgressive F S)
    (hSemimartingale : IsSemimartingale S F mu)
    (H : RealizedStrategy (ℱ := F) mu S) :
    ∃ (cutoff : Nat → Nat) (Q : Measure Ω) (HQ : RealizedStrategy (ℱ := F) Q S),
      StrictMono cutoff ∧ IsProbabilityMeasure Q ∧ Q ≪ mu ∧ mu ≪ Q ∧
      IsSemimartingale S F Q ∧ HQ.representative = H.representative ∧ HQ.gain = H.gain ∧
      ∃ xi : Ω → Real, Measurable xi ∧ (∀ w, 0 ≤ xi w) ∧
      Q = CommonEnvelopeMeasure.tilted mu xi ∧ MemLp xi 2 Q ∧
      (∀ᵐ w ∂Q, ∀ k,
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (fun t w => elementaryGain S (HQ.representative (cutoff k)) t w - HQ.gain t w)
          ((k + 1 : Nat) : NNReal) w ≤ xi w) ∧
      Tendsto (fun k => ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (fun t w => elementaryGain S (HQ.representative (cutoff k)) t w - HQ.gain t w)
          ((k + 1 : Nat) : NNReal) w) ∂Q) atTop (𝓝 0) := by
  let error : Nat → Nat → Ω → Real := fun n r =>
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (fun t w => elementaryGain S (H.representative n) t w - H.gain t w)
      ((r + 1 : Nat) : NNReal)
  have hConv : ∀ r, TendstoInMeasure mu (fun n => error n r) atTop (fun _ => 0) := by
    intro r
    exact FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_capped
      _ (H.gain_convergence r)
  obtain ⟨cutoff, hCutoff, hAE⟩ := exists_strictMono_diagonal_tendstoAE_zero hConv
  have hMeas : ∀ k, Measurable (error (cutoff k) k) := by
    intro k
    have hGain : StronglyAdapted F (elementaryGain S (H.representative (cutoff k))) :=
      PredictableElementaryStrategy.stronglyAdapted_gain S hS (H.representative (cutoff k))
    exact ((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (hGain.sub H.gain_stronglyAdapted) _).mono (F.le _)).measurable
  obtain ⟨xi, Q, hXiMeas, hXiPos, hDom, hTilt, hProb, hQmu, hMuQ, hXiL2⟩ :=
    exists_tilted_sequenceNormEnvelope_of_tendstoAE (fun k => error (cutoff k) k)
      (fun _ => 0) hMeas hAE
  let : IsProbabilityMeasure Q := hProb
  let HQ := H.transferMeasure hMuQ hQmu S hS
  have hL1 : Integrable xi Q := memLp_one_iff_integrable.mp
    (hXiL2.mono_exponent (by norm_num))
  have hFinite : (∫⁻ w, ENNReal.ofReal (xi w) ∂Q) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hXiMeas.aestronglyMeasurable
      (Eventually.of_forall hXiPos)).mpr hL1
  have hBound : ∀ k, ∀ᵐ w ∂Q,
      ENNReal.ofReal (error (cutoff k) k w) ≤ ENNReal.ofReal (xi w) := by
    intro k
    filter_upwards [hQmu.ae_le hDom] with w hw
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hw k))
  have hENN : ∀ᵐ w ∂Q, Tendsto
      (fun k => ENNReal.ofReal (error (cutoff k) k w)) atTop (𝓝 0) := by
    filter_upwards [hQmu.ae_le hAE] with w hw
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hw
  have hInt := tendsto_lintegral_of_dominated_convergence' (fun w => ENNReal.ofReal (xi w))
    (fun k => (hMeas k).ennreal_ofReal.aemeasurable) hBound hFinite hENN
  refine ⟨cutoff, Q, HQ, hCutoff, hProb, hQmu, hMuQ, ?_, rfl, rfl,
    xi, hXiMeas, hXiPos, hTilt, hXiL2, ?_, ?_⟩
  · exact (IsSemimartingale.iff_of_mutuallyAbsolutelyContinuous hMuQ hQmu).mp hSemimartingale
  · filter_upwards [hQmu.ae_le hDom] with w hw
    intro k
    exact (le_abs_self _).trans (hw k)
  · simpa only [error, HQ, RealizedStrategy.transferMeasure, lintegral_zero] using hInt

end PredictableElementaryEmery

end FTAPTheorem42
