/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Realization
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer

/-!
# Measure transfer for the elementary Emery completion

The finite-horizon Emery gauge is an upper envelope over all bounded
predictable elementary tests.  This file records the finite-measure transfer
needed for that envelope.  The proof is deliberately uniform in the test:
bounded envelopes are transferred in measure and then back to their integrals
by a direct bounded-integral estimate.  Thus the `sSup` defining the gauge is
not transferred one test at a time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

private theorem eLpNorm_one_eq_integral_of_nonnegative
    {ν : Measure Ω} [IsFiniteMeasure ν]
    {f : Ω → ℝ} (hf : StronglyMeasurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    eLpNorm f (1 : ℝ≥0∞) ν = ENNReal.ofReal (∫ x, f x ∂ν) := by
  have hInt : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
    exact hbound x |>.2
  have hMem : MemLp f (1 : ℝ≥0∞) ν :=
    memLp_one_iff_integrable.mpr hInt
  rw [← MeasureTheory.ofReal_lpNorm hMem]
  rw [lpNorm_one_eq_integral_norm hf.aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]

theorem integral_tendsto_zero_of_tendstoInMeasure_of_bounded
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    {f : ι → Ω → ℝ}
    (hf : ∀ i, StronglyMeasurable (f i))
    (hbound : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1)
    (hmeasure : TendstoInMeasure ν f atTop (fun _ => (0 : ℝ))) :
    Tendsto (fun i => ∫ x, f i x ∂ν) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hEvent :=
    (tendstoInMeasure_iff_measureReal_norm.mp hmeasure) (ε / 2) hε2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hEvent (ε / 2) hε2
  refine ⟨N, fun i hi => ?_⟩
  let s : Set Ω := {x | ε / 2 ≤ f i x}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const (hf i).measurable
  have hInt : Integrable (f i) ν := by
    apply Integrable.of_bound (hf i).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound i x).1]
    exact hbound i x |>.2
  have hUpper : ∀ x, f i x ≤ ε / 2 + s.indicator (fun _ : Ω => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      linarith [hbound i x |>.2]
    · rw [Set.indicator_of_notMem hx]
      have hx' : ¬ ε / 2 ≤ f i x := hx
      simpa using (lt_of_not_ge hx').le
  have hIntegralLe :
      ∫ x, f i x ∂ν ≤ ε / 2 + ν.real s := by
    have hConst : Integrable (fun _ : Ω => ε / 2) ν :=
      integrable_const (μ := ν) _
    have hInd' : Integrable (s.indicator (fun _ : Ω => (1 : ℝ))) ν :=
      (integrable_const (μ := ν) 1).indicator hs
    have hUpperInt :
        Integrable (fun x => ε / 2 + s.indicator (fun _ : Ω => (1 : ℝ)) x) ν :=
      by
        have hEq :
            (fun x => ε / 2 + s.indicator (fun _ : Ω => (1 : ℝ)) x) =
              (fun _ : Ω => ε / 2) + s.indicator (fun _ : Ω => (1 : ℝ)) := by
          funext x
          rfl
        rw [hEq]
        exact hConst.add hInd'
    calc
      ∫ x, f i x ∂ν ≤
          ∫ x, (fun x => ε / 2 + s.indicator (fun _ : Ω => (1 : ℝ)) x) x ∂ν :=
        integral_mono_ae hInt hUpperInt (ae_of_all _ hUpper)
      _ = ε / 2 + ν.real s := by
        have hEq :
            (fun x => ε / 2 + s.indicator (fun _ : Ω => (1 : ℝ)) x) =
              (fun _ : Ω => ε / 2) + s.indicator (fun _ : Ω => (1 : ℝ)) := by
          funext x
          rfl
        have hIndIntegral :
            ∫ x, s.indicator (fun _ : Ω => (1 : ℝ)) x ∂ν = ν.real s := by
          have hfun : (fun _ : Ω => (1 : ℝ)) = (1 : Ω → ℝ) := by
            funext x
            simp
          rw [hfun]
          exact integral_indicator_one (μ := ν) hs
        rw [hEq]
        calc
          ∫ x, ((fun _ : Ω => ε / 2) +
              s.indicator (fun _ : Ω => (1 : ℝ))) x ∂ν =
              (∫ x, (fun _ : Ω => ε / 2) x ∂ν) +
                ∫ x, s.indicator (fun _ : Ω => (1 : ℝ)) x ∂ν :=
            integral_add hConst hInd'
          _ = ε / 2 + ν.real s := by
            rw [integral_const, hIndIntegral]
            simp
  have hEventRewrite :
      ν.real {x | ε / 2 ≤ ‖f i x - (0 : ℝ)‖} = ν.real s := by
    have hset : {x | ε / 2 ≤ ‖f i x - (0 : ℝ)‖} = s := by
      ext x
      change ε / 2 ≤ ‖f i x - (0 : ℝ)‖ ↔ ε / 2 ≤ f i x
      simp [Real.norm_eq_abs, abs_of_nonneg (hbound i x).1]
    exact congrArg ν.real hset
  have hMeasure : ν.real s < ε / 2 := by
    have hNi := hN i hi
    have hNi' : ‖ν.real {x | ε / 2 ≤ ‖f i x - (0 : ℝ)‖}‖ < ε / 2 := by
      simpa only [dist_zero_right] using hNi
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] at hNi'
    exact hEventRewrite ▸ hNi'
  have hNonneg : 0 ≤ ∫ x, f i x ∂ν :=
    integral_nonneg (fun x => (hbound i x).1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg]
  exact lt_of_le_of_lt hIntegralLe (by linarith)

theorem tendstoInMeasure_of_integral_tendsto_zero_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    {f : ι → Ω → ℝ}
    (hf : ∀ i, StronglyMeasurable (f i))
    (hbound : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1)
    (hIntegral : Tendsto (fun i => ∫ x, f i x ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)) := by
  have hNorm : Tendsto
      (fun i => eLpNorm (f i - (fun _ : Ω => (0 : ℝ)))
        (1 : ℝ≥0∞) μ) atTop (𝓝 0) := by
    have hEq : ∀ i,
        eLpNorm (f i - (fun _ : Ω => (0 : ℝ))) (1 : ℝ≥0∞) μ =
          ENNReal.ofReal (∫ x, f i x ∂μ) := by
      intro i
      have hSub : f i - (fun _ : Ω => (0 : ℝ)) = f i := by
        funext x
        simp
      rw [hSub]
      exact eLpNorm_one_eq_integral_of_nonnegative (ν := μ) (hf i) (hbound i)
    have hOfReal := ENNReal.tendsto_ofReal hIntegral
    rw [show (fun i => eLpNorm (f i - (fun _ : Ω => (0 : ℝ)))
        (1 : ℝ≥0∞) μ) =
          (fun i => ENNReal.ofReal (∫ x, f i x ∂μ)) by
      funext i
      exact hEq i]
    simpa only [ENNReal.ofReal_zero] using hOfReal
  exact tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞))
    (by norm_num) hNorm

theorem integral_tendsto_zero_of_integral_tendsto_zero_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n))
    (hbound : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (hIntegral : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 0) := by
  have hMeasureμ := tendstoInMeasure_of_integral_tendsto_zero_of_bounded
    (μ := μ) hf hbound hIntegral
  have hfμ : ∀ i, AEStronglyMeasurable (f i) μ :=
    fun i => (hf i).aestronglyMeasurable
  have hMeasureν : TendstoInMeasure ν f atTop (fun _ => (0 : ℝ)) :=
    (EquivalentMeasureTransfer.tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
      hμν hνμ hfμ).1 hMeasureμ
  exact integral_tendsto_zero_of_tendstoInMeasure_of_bounded
    (ν := ν) hf hbound hMeasureν

theorem testValue_le_gauge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S J H K T ≤ gauge μ S H K T := by
  exact le_csSup (gauge_bddAbove S hS H K T)
    (Set.mem_insert_of_mem 0 (Set.mem_range_self J))

theorem testValue_tendsto_zero_of_gauge_tendsto_zero_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : ℕ → BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : ℕ → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hμ : Tendsto (fun n => gauge μ S (H n) (K n) T)
      atTop (𝓝 0)) :
    Tendsto (fun n => testValue ν S (J n) (H n) (K n) T)
      atTop (𝓝 0) := by
  let E : ℕ → Ω → ℝ := fun n =>
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S (J n) (H n) (K n)) T
  have hEStrong : ∀ n, StronglyMeasurable (E n) := by
    intro n
    simpa only [E] using
      testEnvelope_stronglyMeasurable S hS (J n) (H n) (K n) T
  have hEBound : ∀ n x, 0 ≤ E n x ∧ E n x ≤ 1 := by
    intro n x
    exact ⟨
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
        (testedDifference S (J n) (H n) (K n)) T x,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
        (testedDifference S (J n) (H n) (K n)) T x⟩
  have hTestμ : Tendsto
      (fun n => testValue μ S (J n) (H n) (K n) T)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hμ
    · filter_upwards [] with n
      exact testValue_nonnegative μ S (J n) (H n) (K n) T
    · filter_upwards [] with n
      exact testValue_le_gauge S hS (J n) (H n) (K n) T
  have hEμ : Tendsto (fun n => ∫ x, E n x ∂μ)
      atTop (𝓝 0) := by
    have hEq : (fun n => ∫ x, E n x ∂μ) =
        (fun n => testValue μ S (J n) (H n) (K n) T) := by
      funext n
      simpa only [E] using
        (testValue_eq_integral μ S (J n) (H n) (K n) T).symm
    rw [hEq]
    exact hTestμ
  have hEν : Tendsto (fun n => ∫ x, E n x ∂ν)
      atTop (𝓝 0) :=
    integral_tendsto_zero_of_integral_tendsto_zero_of_mutuallyAbsolutelyContinuous
      hμν hνμ hEStrong hEBound hEμ
  have hEqν : (fun n => testValue ν S (J n) (H n) (K n) T) =
      (fun n => ∫ x, E n x ∂ν) := by
    funext n
    simpa only [E] using
      (testValue_eq_integral ν S (J n) (H n) (K n) T)
  rw [hEqν]
  exact hEν

theorem gauge_tendsto_zero_of_gauge_tendsto_zero_of_cofinal
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    (b : ℕ → ι) (hb : Tendsto b atTop atTop)
    (H K : ι → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hμ : Tendsto (fun i => gauge μ S (H i) (K i) T)
      atTop (𝓝 0)) :
    Tendsto (fun i => gauge ν S (H i) (K i) T)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hNo
  push Not at hNo
  have hqexist : ∀ n : ℕ, ∃ i : ι,
      b n ≤ i ∧ ε ≤ dist (gauge ν S (H i) (K i) T) 0 := by
    intro n
    rcases hNo (b n) with ⟨i, hi, hbad⟩
    exact ⟨i, hi, hbad⟩
  choose q hq hbad using hqexist
  have hqT : Tendsto q atTop atTop := by
    rw [tendsto_atTop]
    intro i
    filter_upwards [(tendsto_atTop.1 hb) i] with n hn
    exact hn.trans (hq n)
  have hGaugeμ : Tendsto
      (fun n => gauge μ S (H (q n)) (K (q n)) T)
      atTop (𝓝 0) := by
    have hcomp := hμ.comp hqT
    simpa only [Function.comp_def] using hcomp
  have hChoose : ∀ n : ℕ, ∃ J,
      ε / 2 < testValue ν S J (H (q n)) (K (q n)) T := by
    intro n
    have hNonneg : 0 ≤ gauge ν S (H (q n)) (K (q n)) T :=
      gauge_nonnegative S hS (H (q n)) (K (q n)) T
    have hGauge : ε ≤ gauge ν S (H (q n)) (K (q n)) T := by
      have h := hbad n
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hNonneg] at h
      exact h
    have hGaugeLt : ε / 2 < gauge ν S (H (q n)) (K (q n)) T := by
      linarith
    have hltSup : ε / 2 < sSup
        (insert 0 (Set.range (fun J =>
          testValue ν S J (H (q n)) (K (q n)) T))) := by
      simpa only [gauge] using hGaugeLt
    have hBdd := gauge_bddAbove (μ := ν) (ℱ := ℱ) S hS
      (H (q n)) (K (q n)) T
    have hNonempty : (insert 0 (Set.range (fun J =>
        testValue ν S J (H (q n)) (K (q n)) T))).Nonempty :=
      ⟨0, Set.mem_insert 0 _⟩
    rcases (lt_csSup_iff hBdd hNonempty).1 hltSup with
      ⟨x, hx, hxlt⟩
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨J, rfl⟩
    · exfalso
      linarith
    · exact ⟨J, hxlt⟩
  choose J hJ using hChoose
  let E : ℕ → Ω → ℝ := fun n =>
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (testedDifference S (J n) (H (q n)) (K (q n))) T
  have hEBound : ∀ n x, 0 ≤ E n x ∧ E n x ≤ 1 := by
    intro n x
    exact ⟨
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
        (testedDifference S (J n) (H (q n)) (K (q n))) T x,
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
        (testedDifference S (J n) (H (q n)) (K (q n))) T x⟩
  have hTestν : Tendsto
      (fun n => testValue ν S (J n) (H (q n)) (K (q n)) T)
      atTop (𝓝 0) :=
    testValue_tendsto_zero_of_gauge_tendsto_zero_of_mutuallyAbsolutelyContinuous
      hμν hνμ S hS J (fun n => H (q n)) (fun n => K (q n)) T hGaugeμ
  have hEν : Tendsto (fun n => ∫ x, E n x ∂ν)
      atTop (𝓝 0) := by
    have hEq : (fun n => testValue ν S (J n) (H (q n)) (K (q n)) T) =
        (fun n => ∫ x, E n x ∂ν) := by
      funext n
      simpa only [E] using
        (testValue_eq_integral ν S (J n) (H (q n)) (K (q n)) T)
    rw [← hEq]
    exact hTestν
  have hJIntegral : ∀ n, ε / 2 < ∫ x, E n x ∂ν := by
    intro n
    have hEq : testValue ν S (J n) (H (q n)) (K (q n)) T =
        ∫ x, E n x ∂ν := by
      simpa only [E] using
        testValue_eq_integral ν S (J n) (H (q n)) (K (q n)) T
    rw [← hEq]
    exact hJ n
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hEν (ε / 2) (half_pos hε)
  have hNonneg : 0 ≤ ∫ x, E N x ∂ν :=
    integral_nonneg (fun x => (hEBound N x).1)
  have hlt : ∫ x, E N x ∂ν < ε / 2 := by
    have h := hN N le_rfl
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hNonneg]
      using h
  exact (not_lt_of_ge (le_of_lt (hJIntegral N))) hlt

theorem gauge_product_tendsto_zero_of_gauge_product_tendsto_zero_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : ℕ → PredictableElementaryStrategy ℱ) (T : ℝ≥0)
    (hμ : Tendsto (fun p : ℕ × ℕ =>
        gauge μ S (H p.1) (H p.2) T) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ =>
        gauge ν S (H p.1) (H p.2) T) atTop (𝓝 0) := by
  have hdiag : Tendsto (fun n : ℕ => (n, n)) atTop atTop := by
    rw [tendsto_atTop]
    intro p
    filter_upwards [eventually_ge_atTop (max p.1 p.2)] with n hn
    exact Prod.mk_le_mk.mpr ⟨
      (le_max_left p.1 p.2).trans hn,
      (le_max_right p.1 p.2).trans hn⟩
  exact gauge_tendsto_zero_of_gauge_tendsto_zero_of_cofinal
    hμν hνμ S hS (fun n : ℕ => (n, n)) hdiag
    (fun p : ℕ × ℕ => H p.1) (fun p : ℕ × ℕ => H p.2) T hμ

theorem isCauchy_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : ℕ → PredictableElementaryStrategy ℱ) :
    IsCauchy μ S H ↔ IsCauchy ν S H := by
  constructor
  · intro h T
    exact gauge_product_tendsto_zero_of_gauge_product_tendsto_zero_of_mutuallyAbsolutelyContinuous
      hμν hνμ S hS H T (h T)
  · intro h T
    exact gauge_product_tendsto_zero_of_gauge_product_tendsto_zero_of_mutuallyAbsolutelyContinuous
      hνμ hμν S hS H T (h T)

theorem RealizedStrategy.gain_convergence_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (r : ℕ) :
    TendstoInMeasure ν
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        ((r + 1 : ℕ) : ℝ≥0))
      atTop (fun _ => 0) := by
  have hMeas : ∀ n, AEStronglyMeasurable
      (FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        ((r + 1 : ℕ) : ℝ≥0)) μ := by
    intro n
    have hElementary : StronglyAdapted ℱ
        (fun t ω => elementaryGain S (H.representative n) t ω) := by
      simpa only [elementaryGain] using
        PredictableElementaryStrategy.stronglyAdapted_gain S hS
          (H.representative n)
    have hDifference : StronglyAdapted ℱ
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω) :=
      hElementary.sub H.gain_stronglyAdapted
    exact ((FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      hDifference ((r + 1 : ℕ) : ℝ≥0)).mono
        (ℱ.le ((r + 1 : ℕ) : ℝ≥0))).aestronglyMeasurable
  exact (EquivalentMeasureTransfer.tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
    hμν hνμ hMeas).1 (H.gain_convergence r)

theorem RealizedStrategy.isCauchy_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : RealizedStrategy (ℱ := ℱ) μ S) :
    IsCauchy ν S H.representative := by
  exact (isCauchy_iff_of_mutuallyAbsolutelyContinuous
    hμν hνμ S hS H.representative).1 H.isCauchy

noncomputable def RealizedStrategy.transferMeasure
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (H : RealizedStrategy (ℱ := ℱ) μ S) :
    RealizedStrategy (ℱ := ℱ) ν S where
  representative := H.representative
  representativeBound := H.representativeBound
  representative_coefficientAbsSum_le := H.representative_coefficientAbsSum_le
  gain := H.gain
  gain_stronglyAdapted := H.gain_stronglyAdapted
  gain_rightContinuous := H.gain_rightContinuous
  gain_hasLeftLimits := H.gain_hasLeftLimits
  gain_convergence := by
    intro r
    exact H.gain_convergence_of_mutuallyAbsolutelyContinuous
      hμν hνμ S hS r
  isCauchy := H.isCauchy_of_mutuallyAbsolutelyContinuous
    hμν hνμ S hS

end PredictableElementaryEmery

end FTAPTheorem42
