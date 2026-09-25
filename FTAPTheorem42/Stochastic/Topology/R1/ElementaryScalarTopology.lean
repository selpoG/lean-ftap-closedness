/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryGoodIntegratorSmallScalar
import FTAPTheorem42.Stochastic.Topology.R1.ElementaryConvergence

/-! # Continuity of fixed scalar multiplication for the elementary metric -/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

omit [MeasurableSpace Ω] in
theorem ElementaryStrategy.gain_smul_price (a : Real) (X : Process Ω)
    (J : ElementaryStrategy Ω NNReal) :
    ElementaryStrategy.gain (a • X) J = a • ElementaryStrategy.gain X J := by
  induction J with
  | nil => funext t w; simp [ElementaryStrategy.gain]
  | cons B J ih =>
    funext t w
    change B.gain (a • X) t w + ElementaryStrategy.gain (a • X) J t w =
      a * (B.gain X t w + ElementaryStrategy.gain X J t w)
    rw [ih]
    simp only [Pi.smul_apply, smul_eq_mul, ElementaryInterval.gain]
    ring

namespace R1Process

theorem elementaryGauge_posSMul_le (a : Real) (ha : 0 < a) (T : NNReal)
    (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryGauge T (a • X) (a • Y) ≤ ENNReal.ofReal (max a 1) * elementaryGauge T X Y := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  rw [← SeparationQuotient.mk_smul, ← SeparationQuotient.mk_smul]
  simp only [elementaryGauge_mk]
  apply iSup_le
  intro J
  have hPoint w : elementaryEmeryTestError (a • X).val (a • Y).val J T w ≤
      max a 1 * elementaryEmeryTestError X.val Y.val J T w := by
    simp only [elementaryEmeryTestError, smul_val, ElementaryStrategy.gain_smul_price]
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
    exact PredictableElementaryEmery.cappedFiniteHorizonAbsoluteEnvelope_posSMul_le
      (ElementaryStrategy.gain X.val J.strategy.toElementary -
        ElementaryStrategy.gain Y.val J.strategy.toElementary) a ha T w
  have hInt := integral_mono_ae (testError_integrable (a • X) (a • Y) J T)
    ((testError_integrable X Y J T).const_mul (max a 1)) (Eventually.of_forall hPoint)
  rw [integral_const_mul] at hInt
  have h := ENNReal.ofReal_le_ofReal hInt
  rw [ENNReal.ofReal_mul (le_max_of_le_right zero_le_one)] at h
  exact h.trans (mul_le_mul' le_rfl (le_iSup
    (fun K : BoundedPredictableElementaryMultiplier (Ω := Ω) F =>
      ENNReal.ofReal (∫ w, elementaryEmeryTestError X.val Y.val K T w ∂μ)) J))

theorem elementaryEDist_posSMul_le (a : Real) (ha : 0 < a)
    (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryEDist (a • X) (a • Y) ≤ ENNReal.ofReal (max a 1) * elementaryEDist X Y := by
  unfold elementaryEDist
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have h := mul_le_mul' (le_rfl : ((2 : ENNReal)⁻¹) ^ (n + 1) ≤ _)
    (elementaryGauge_posSMul_le a ha (n + 1) X Y)
  simpa only [mul_left_comm] using h

end R1Process

namespace ElementaryMetricProcess

theorem lipschitzWith_posSMul (a : Real) (ha : 0 < a) :
    LipschitzWith (Real.toNNReal (max a 1)) (fun X : ElementaryMetricProcess F μ => a • X) := by
  intro X Y
  exact R1Process.elementaryEDist_posSMul_le a ha X Y

theorem lipschitzWith_smul (a : Real) :
    LipschitzWith (Real.toNNReal (max |a| 1))
      (fun X : ElementaryMetricProcess F μ => a • X) := by
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · simpa only [abs_of_pos ha] using lipschitzWith_posSMul (F := F) (μ := μ) a ha
  · intro X Y
    simp only [zero_smul, edist_self]
    exact bot_le
  · intro X Y
    have h := lipschitzWith_posSMul (F := F) (μ := μ) (-a) (neg_pos.mpr ha) X Y
    simpa only [neg_smul, edist_neg, abs_of_neg ha] using h

end ElementaryMetricProcess

end FTAPTheorem42

namespace FTAPTheorem42.ElementaryMetricProcess

/-! ## Joint scalar continuity of the complete elementary process space -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [hUsual : Fact (Filtration.UsualConditions μ F)]

theorem tendsto_smul_zero (X : ElementaryMetricProcess F μ)
    (a : Nat → Real) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => a n • X) atTop (𝓝 (0 : ElementaryMetricProcess F μ)) := by
  obtain ⟨R, hR⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, hRY, hYP, hYR, _⟩ := R.exists_regular_representative
  have hY : SeparationQuotient.mk Y = X :=
    ((R1Process.quotient_eq_iff R Y).mpr hRY).symm.trans hR
  have hGI := (Classical.choice Y.property).isSemimartingale hUsual.out
  let : F.IsRightContinuous := hUsual.out.1
  apply tendsto_of_gauge
  intro T ε hε
  obtain ⟨δ, hδ, hSmall⟩ := hGI.uniform_smallScalar_integral hYP hYR T ε hε
  have hAbs : ∀ᶠ n in atTop, |a n| ≤ δ :=
    ((ha.abs).eventually (Iio_mem_nhds (by simpa using hδ))).mono fun _ hn => hn.le
  filter_upwards [hAbs] with n hn
  have hBound : R1Process.elementaryGauge T (SeparationQuotient.mk (a n • Y))
      (SeparationQuotient.mk (0 : R1Process F μ)) ≤ ENNReal.ofReal ε := by
    apply (R1Process.elementaryGauge_mk_le_iff T (a n • Y) 0 hε.le).mpr
    intro J
    have hZero : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
      funext t w
      simp [ElementaryStrategy.gain, ElementaryInterval.gain]
    simpa only [elementaryEmeryTestError, R1Process.smul_val, R1Process.zero_val,
      ElementaryStrategy.gain_smul_price, hZero, Pi.zero_apply, sub_zero,
      Pi.smul_apply, smul_eq_mul] using hSmall (a n) hn J.strategy J.abs_integrand_le_one
  rw [SeparationQuotient.mk_smul, hY, SeparationQuotient.mk_zero] at hBound
  exact hBound

instance : ContinuousSMul Real (ElementaryMetricProcess F μ) where
  continuous_smul := by
    apply continuous_iff_seqContinuous.mpr
    intro u p hu
    have ha := (continuous_fst.tendsto p).comp hu
    have hX : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp hu
    have hOrbit := tendsto_smul_zero p.2 (fun n => (u n).1 - p.1)
      (by simpa using ha.sub_const p.1)
    have hFirst : Tendsto (fun n => dist ((u n).1 • (u n).2) ((u n).1 • p.2))
        atTop (𝓝 0) := by
      have hFactor : Tendsto (fun n => max |(u n).1| 1) atTop (𝓝 (max |p.1| 1)) :=
        ha.abs.max tendsto_const_nhds
      have hProduct := hFactor.mul (tendsto_iff_dist_tendsto_zero.mp hX)
      simp only [mul_zero] at hProduct
      apply squeeze_zero (fun _ => dist_nonneg) _ hProduct
      intro n
      simpa only [Real.coe_toNNReal _ (le_max_of_le_right zero_le_one)] using
        (lipschitzWith_smul ((u n).1)).dist_le_mul (u n).2 p.2
    have hSecond : Tendsto (fun n => dist ((u n).1 • p.2) (p.1 • p.2)) atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hOrbit
      have hEq n : dist (((u n).1 - p.1) • p.2) 0 =
          dist ((u n).1 • p.2) (p.1 • p.2) := by
        rw [sub_smul, dist_edist, dist_edist]
        have he := edist_add_right ((u n).1 • p.2 - p.1 • p.2) 0 (p.1 • p.2)
        rw [sub_add_cancel, zero_add] at he
        exact congrArg ENNReal.toReal he.symm
      simpa only [hEq] using h
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hSum := hFirst.add hSecond
    simp only [add_zero] at hSum
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle _ ((u n).1 • p.2) _) hSum

end FTAPTheorem42.ElementaryMetricProcess

namespace FTAPTheorem42

/-! ## Comparing the elementary and R1 topologies by the F-space closed graph theorem -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

namespace ElementaryMetricProcess

instance : IsIsometricVAdd (ElementaryMetricProcess F μ) (ElementaryMetricProcess F μ) :=
  ⟨fun X Y Z => by
    change edist (X + Y) (X + Z) = edist Y Z
    simpa only [add_comm X] using edist_add_right Y Z X⟩

private theorem r1_isIsometricVAdd :
    IsIsometricVAdd (SeparationQuotient (R1Process F μ))
      (SeparationQuotient (R1Process F μ)) := by
  refine ⟨fun X Y Z => ?_⟩
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨Z, rfl⟩ := SeparationQuotient.surjective_mk Z
  change edist (SeparationQuotient.mk X + SeparationQuotient.mk Y)
    (SeparationQuotient.mk X + SeparationQuotient.mk Z) = _
  rw [← SeparationQuotient.mk_add, ← SeparationQuotient.mk_add]
  simp only [R1Process.quotient_edist_eq, R1Process.add_val, add_sub_add_left_eq_sub]

/-- The identity map is continuous in the direction needed for prelocal cost control. -/
theorem continuous_toR1 : Continuous (toR1 (F := F) (μ := μ)) := by
  let : IsIsometricVAdd (SeparationQuotient (R1Process F μ))
      (SeparationQuotient (R1Process F μ)) := r1_isIsometricVAdd
  let f : ElementaryMetricProcess F μ →ₗ[Real] SeparationQuotient (R1Process F μ) :=
    { toFun := toR1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply FSpace.continuous_of_isClosed_graph f
  have heq : (f.graph : Set (ElementaryMetricProcess F μ ×
      SeparationQuotient (R1Process F μ))) = {p | toR1 p.1 = p.2} := by
    ext p
    exact eq_comm
  rw [heq]
  exact isClosed_graph_toR1

/-- Uniform elementary test convergence supplies vanishing R1 cost on the
full decomposable carrier, without fixed-source closure assumptions. -/
theorem tendsto_r1_of_elementary (X : Nat → R1Process F μ) (Y : R1Process F μ)
    (h : ElementaryEmeryConverges μ F (fun n => (X n).val) Y.val) :
    Tendsto (fun n => semimartingaleR1 ((X n).val - Y.val) F μ) atTop (𝓝 0) := by
  apply R1Process.quotient_tendsto_iff.mp
  exact (continuous_toR1.tendsto (ofR1 Y)).comp ((tendsto_mk_iff X Y).mpr h)

end ElementaryMetricProcess

end FTAPTheorem42
