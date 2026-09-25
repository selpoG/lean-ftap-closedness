/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Variation
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteVariationGoodIntegrator
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessUniqueness

/-! # Uniform elementary-test control by pathwise total variation -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

namespace SIntegrableFiniteVariationBridge

omit [MeasurableSpace Omega] in
theorem cappedFiniteHorizonAbsoluteEnvelope_le_min_of_bound
    (X : Process Omega) (T : NNReal) (G : Real) (omega : Omega)
    (hG : 0 ≤ G)
    (hBound : ∀ t, t ≤ T → |X t omega| ≤ G) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T omega ≤
      min G 1 := by
  let E := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    (fun t omega => |X t omega|) T omega
  have hE : E ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro r
    have hMax : FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |X t omega|) T r omega ≤ G := by
      obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
        (s := Finset.range (r * r.factorial + 1))
        Finset.nonempty_range_add_one
        (fun j => (FactorialChronologicalGrid.stoppedGrid T r).natSample
          (fun t omega => |X t omega|) j omega)
      rw [show FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |X t omega|) T r omega =
          (FactorialChronologicalGrid.stoppedGrid T r).natSample
            (fun t omega => |X t omega|) k omega by exact hkEq]
      apply hBound
      simp only [ChronologicalGrid.sampledTime,
        FactorialChronologicalGrid.stoppedGrid_time]
      exact min_le_right _ _
    exact ENNReal.ofReal_le_ofReal hMax
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  change (min E 1).toReal ≤ min G 1
  have hMin : min E 1 ≤ ENNReal.ofReal (min G 1) := by
    rw [ENNReal.ofReal_min]
    exact min_le_min hE (by norm_num)
  have hMinFinite : min E 1 ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hReal : (min E 1).toReal ≤ (ENNReal.ofReal (min G 1)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hMin
  rw [ENNReal.toReal_ofReal (le_min hG (by norm_num))] at hReal
  exact hReal

end SIntegrableFiniteVariationBridge

/-- Unit-bounded predictable elementary tests contract whole-path total variation. -/
theorem BoundedPredictableElementaryMultiplier.abs_gain_le_totalVariation
    (J : BoundedPredictableElementaryMultiplier (Ω := Omega) F)
    (A : Process Omega) (hA : ∀ w, BoundedVariationOn (A · w) univ)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (T : NNReal) (w : Omega) :
    |ElementaryStrategy.gain A J.strategy.toElementary T w| ≤
      (FiniteVariationPath.signedMeasure (hA w)).totalVariation.real univ := by
  let ν := FiniteVariationPath.signedMeasure (hA w)
  let : IsFiniteMeasure (ν : VectorMeasure NNReal Real).variation := by
    rw [← signedMeasure_totalVariation_eq_variation]
    infer_instance
  have hGain := (J.strategy.finiteVariationIntegral_eq_gain A hA hRight T w).symm.trans
    (J.strategy.finiteVariationIntegral_eq_integral_indicator_integrand A hA T w)
  rw [hGain, ← Real.norm_eq_abs]
  have hBound : ∀ᵐ t ∂(ν : VectorMeasure NNReal Real).variation,
      ‖(Ioc 0 T).indicator (fun t => J.strategy.integrand t w) t‖ ≤ (1 : Real) := by
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Ioc 0 T
    · simpa only [indicator_of_mem ht, Real.norm_eq_abs] using J.abs_integrand_le_one t w
    · simp only [indicator_of_notMem ht, norm_zero, zero_le_one]
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.lsmul Real Real) hBound
  simpa only [FiniteVariationPath.integral, one_mul,
    ContinuousLinearMap.opNorm_lsmul, mul_one,
    ← signedMeasure_totalVariation_eq_variation] using h

/-- The same total-variation bound controls the capped maximal test process. -/
theorem BoundedPredictableElementaryMultiplier.capped_gain_le_totalVariation
    (J : BoundedPredictableElementaryMultiplier (Ω := Omega) F)
    (A : Process Omega) (hA : ∀ w, BoundedVariationOn (A · w) univ)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (T : NNReal) (w : Omega) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (ElementaryStrategy.gain A J.strategy.toElementary) T w ≤
      min ((FiniteVariationPath.signedMeasure (hA w)).totalVariation.real univ) 1 := by
  apply SIntegrableFiniteVariationBridge.cappedFiniteHorizonAbsoluteEnvelope_le_min_of_bound
    _ _ _ _ ENNReal.toReal_nonneg
  intro t _
  exact J.abs_gain_le_totalVariation A hA hRight t w

/-- A finite-horizon test only sees the stopped finite-variation path. -/
theorem BoundedPredictableElementaryMultiplier.capped_gain_le_finiteHorizonPathVariation
    (J : BoundedPredictableElementaryMultiplier (Ω := Omega) F)
    (A : Process Omega) (hA : ∀ w, LocallyBoundedVariationOn (A · w) univ)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (T : NNReal) (w : Omega) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (ElementaryStrategy.gain A J.strategy.toElementary) T w ≤
      min (finiteHorizonPathVariation A hA T w) 1 := by
  let B : Process Omega := fun t w => A (min t T) w
  have hB w : BoundedVariationOn (B · w) univ :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn (hA w) T
  have hBR w t : ContinuousWithinAt (B · w) (Ici t) t :=
    FiniteVariationStoppedPath.rightContinuous_stopAt _ (hRight w) T t
  apply SIntegrableFiniteVariationBridge.cappedFiniteHorizonAbsoluteEnvelope_le_min_of_bound
    _ _ _ _ ENNReal.toReal_nonneg
  intro t ht
  rw [J.strategy.toElementary.gain_congr_price_upto t w (T := B)
    (fun s hs => by simp only [B, min_eq_left (hs.trans ht)])]
  exact J.abs_gain_le_totalVariation B hB hBR t w

/-- Vanishing integrals of a common capped variation control give convergence
uniformly over all elementary tests. -/
theorem elementaryEmeryConverges_zero_of_boundedVariation
    {μ : Measure Omega} [IsProbabilityMeasure μ]
    {A : Nat → Process Omega}
    (hA : ∀ n, IsStronglyProgressive F (A n))
    (hBV : ∀ n w, BoundedVariationOn (A n · w) univ)
    (hRight : ∀ n w t, ContinuousWithinAt (A n · w) (Ici t) t)
    {V : Nat → Omega → Real} (hV : ∀ n, StronglyMeasurable (V n))
    (hBound : ∀ n w, 0 ≤ V n w ∧ V n w ≤ 1)
    (hVar : ∀ n, ∀ᵐ w ∂μ,
      min ((FiniteVariationPath.signedMeasure (hBV n w)).totalVariation.real univ) 1 ≤ V n w)
    (hLim : Tendsto (fun n => ∫ w, V n w ∂μ) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F A 0 := by
  intro T ε hε
  filter_upwards [hLim.eventually (gt_mem_nhds hε)] with n hn
  intro J
  have hCapInt : Integrable (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (ElementaryStrategy.gain (A n) J.strategy.toElementary) T) μ := by
    apply Integrable.of_bound
      ((FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
        (J.strategy.stronglyAdapted_gain _ (hA n)) T).mono (F.le T)).aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _)]
      exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _
  have hVInt : Integrable (V n) μ := Integrable.of_bound (hV n).aestronglyMeasurable 1
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBound n w).1]
      exact (hBound n w).2)
  have hLe := integral_mono_ae hCapInt hVInt (show ∀ᵐ w ∂μ,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (ElementaryStrategy.gain (A n) J.strategy.toElementary) T w ≤ V n w by
    filter_upwards [hVar n] with w hw
    exact (J.capped_gain_le_totalVariation _ (hBV n) (hRight n) T w).trans hw)
  have hZeroGain : ElementaryStrategy.gain (0 : Process Omega) J.strategy.toElementary = 0 := by
    funext t w
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  simpa only [hZeroGain, Pi.zero_apply, sub_zero] using hLe.trans hn.le

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Two monotone increment controls bound the finite-horizon variation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators

/-- Opposite increment bounds telescope along each finite chronological partition. -/
theorem eVariationOn_le_of_two_monotone_controls
    (A P Q : NNReal → Real) (T : NNReal)
    (hP : Monotone P) (hQ : Monotone Q)
    (hUpper : ∀ a b, a ≤ b → b ≤ T → A b - A a ≤ P b - P a)
    (hLower : ∀ a b, a ≤ b → b ≤ T → -(A b - A a) ≤ Q b - Q a) :
    eVariationOn A (Icc 0 T) ≤ ENNReal.ofReal ((P T - P 0) + (Q T - Q 0)) := by
  let G := fun t => P t + Q t
  have hG : Monotone G := hP.add hQ
  have hVar : eVariationOn A (Icc 0 T) ≤ eVariationOn G (Icc 0 T) := by
    unfold eVariationOn
    apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    apply le_trans _ (le_iSup _ ⟨n, ⟨u, hu, hus⟩⟩)
    apply Finset.sum_le_sum
    intro i _
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hG (hu (Nat.le_succ i))))]
    apply ENNReal.ofReal_le_ofReal
    apply abs_le.mpr
    dsimp only [G]
    constructor
    · linarith [hLower (u i) (u (i + 1)) (hu (Nat.le_succ i)) (hus (i + 1)).2,
        hP (hu (Nat.le_succ i))]
    · linarith [hUpper (u i) (u (i + 1)) (hu (Nat.le_succ i)) (hus (i + 1)).2,
        hQ (hu (Nat.le_succ i))]
  have hEq := hG.monotoneOn (s := univ) |>.eVariationOn_eq
    (a := 0) (b := T) (mem_univ _) (mem_univ _)
  simp only [univ_inter] at hEq
  rw [hEq] at hVar
  convert hVar using 1
  dsimp only [G]
  congr 1
  ring

variable {Ω : Type*}
/-- Two monotone improvement processes bound the variation used by the
elementary-test Cauchy consumer. -/
theorem finiteHorizonPathVariation_le_of_two_monotone_controls
    (A : Process Ω) (hA : ∀ ω, LocallyBoundedVariationOn (A · ω) univ)
    (hAR : ∀ ω t, ContinuousWithinAt (A · ω) (Ici t) t)
    (P Q : NNReal → Real) (T : NNReal) (ω : Ω)
    (hP : Monotone P) (hQ : Monotone Q)
    (hUpper : ∀ a b, a ≤ b → b ≤ T → A b ω - A a ω ≤ P b - P a)
    (hLower : ∀ a b, a ≤ b → b ≤ T → -(A b ω - A a ω) ≤ Q b - Q a) :
    finiteHorizonPathVariation A hA T ω ≤ (P T - P 0) + (Q T - Q 0) := by
  rw [finiteHorizonPathVariation_eq_eVariationOn A hA hAR T ω]
  exact ENNReal.toReal_le_of_le_ofReal
    (by linarith [hP (show (0 : NNReal) ≤ T from zero_le), hQ (show (0 : NNReal) ≤ T from zero_le)])
    (eVariationOn_le_of_two_monotone_controls (A · ω) P Q T hP hQ hUpper hLower)

end FTAPTheorem42
