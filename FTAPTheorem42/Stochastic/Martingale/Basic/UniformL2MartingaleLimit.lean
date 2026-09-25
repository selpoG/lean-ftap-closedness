/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Uniform L² bounds and martingale limits

A family uniformly bounded in `L²` is uniformly integrable in `L¹`.  As a
consequence, an almost-everywhere pointwise limit of uniformly `L²`-bounded
martingales is again a martingale once strong adaptedness of the limit is
known.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- A uniform `L²` bound under a probability measure supplies uniform
integrability in `L¹`. -/
theorem uniformIntegrable_one_of_eLpNorm_two_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : ι → Ω → ℝ) (B : ℝ≥0)
    (hf : ∀ i, MemLp (f i) (2 : ℝ≥0∞) μ)
    (hB : ∀ i, eLpNorm (f i) (2 : ℝ≥0∞) μ ≤ B) :
    UniformIntegrable f 1 μ := by
  refine ⟨unifIntegrable_iff.2 ?_, ⟨B, fun i => ?_⟩⟩
  · intro η hη
    obtain ⟨ε, _, hε, hεη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    have hε : 0 < ε := ENNReal.ofReal_pos.1 hε
    let δ : ℝ := (ε / ((B : ℝ) + 1)) ^ 2
    have hBpos : 0 < (B : ℝ) + 1 := by positivity
    have hδpos : 0 < δ := sq_pos_of_pos (div_pos hε hBpos)
    refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδpos, fun i s hμs => ?_⟩
    apply le_trans ?_ hεη.le
    calc
      eLpNorm (f i) 1 (μ.restrict s) ≤
          eLpNorm (f i) 2 (μ.restrict s) *
            (μ.restrict s Set.univ) ^
              (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
          ((hf i).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      _ ≤ (B : ℝ≥0∞) * (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) := by
        rw [Measure.restrict_apply_univ s, show
          1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal =
            (1 / 2 : ℝ) by norm_num]
        exact mul_le_mul
          (eLpNorm_mono_measure (f i) Measure.restrict_le_self |>.trans (hB i))
          (ENNReal.rpow_le_rpow hμs (by norm_num)) bot_le bot_le
      _ ≤ ENNReal.ofReal ε := by
        rw [show ENNReal.ofReal δ =
            ENNReal.ofReal (ε / ((B : ℝ) + 1)) ^ 2 by
          dsimp only [δ]
          rw [ENNReal.ofReal_pow (div_nonneg hε.le hBpos.le) 2]]
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        norm_num
        rw [ENNReal.ofReal_div_of_pos hBpos,
          ENNReal.ofReal_add (by positivity : 0 ≤ (B : ℝ)) zero_le_one,
          ENNReal.ofReal_one]
        simp only [ENNReal.ofReal_coe_nnreal]
        calc
          (B : ℝ≥0∞) * (ENNReal.ofReal ε / ((B : ℝ≥0∞) + 1)) ≤
              ((B : ℝ≥0∞) + 1) *
                (ENNReal.ofReal ε / ((B : ℝ≥0∞) + 1)) := by
            gcongr
            norm_num
          _ = ENNReal.ofReal ε := by
            rw [ENNReal.mul_div_cancel]
            · exact ne_of_gt (by positivity)
            · finiteness
  · exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans (hB i)

/-- An almost-everywhere pointwise limit of martingales with one uniform
`L²` bound is a martingale. -/
theorem Martingale.of_ae_tendsto_of_eLpNorm_two_le
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
    (M : ℕ → Process Ω) (X : Process Ω)
    (hM : ∀ n, Martingale (M n) ℱ μ)
    (hX : StronglyAdapted ℱ X)
    (hlim : ∀ t, ∀ᵐ ω ∂μ,
      Tendsto (fun n => M n t ω) atTop (𝓝 (X t ω)))
    (B : ℝ≥0)
    (hB : ∀ n t, eLpNorm (M n t) (2 : ℝ≥0∞) μ ≤ B) :
    Martingale X ℱ μ := by
  have hUI : ∀ t, UniformIntegrable (fun n => M n t) 1 μ := by
    intro t
    exact uniformIntegrable_one_of_eLpNorm_two_le
      (fun n => M n t) B (fun n =>
        (hB n t).trans_lt ENNReal.coe_lt_top)
        (fun n => hB n t)
  have hXIntegrable : ∀ t, Integrable (X t) μ := by
    intro t
    exact (hUI t).integrable_of_ae_tendsto (hlim t)
  refine ⟨hX, ?_⟩
  intro i j hij
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i)
    (hXIntegrable j)
  · intro s _ _
    exact (hXIntegrable i).integrableOn
  · intro s hs _
    have hs0 : MeasurableSet s := ℱ.le i s hs
    let F : ℕ → Ω → ℝ := fun n => s.indicator (M n i)
    let G : ℕ → Ω → ℝ := fun n => s.indicator (M n j)
    let f : Ω → ℝ := s.indicator (X i)
    let g : Ω → ℝ := s.indicator (X j)
    have hFUI : UniformIntegrable F 1 μ := by
      obtain ⟨C, hC⟩ := (hUI i).2
      refine ⟨(hUI i).unifIntegrable.indicator s hs0, ⟨C, fun n => ?_⟩⟩
      simpa only [F] using (eLpNorm_indicator_le (M n i) hs0).trans (hC n)
    have hGUI : UniformIntegrable G 1 μ := by
      obtain ⟨C, hC⟩ := (hUI j).2
      refine ⟨(hUI j).unifIntegrable.indicator s hs0, ⟨C, fun n => ?_⟩⟩
      simpa only [G] using (eLpNorm_indicator_le (M n j) hs0).trans (hC n)
    have hFLim : ∀ᵐ ω ∂μ,
        Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) := by
      filter_upwards [hlim i] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [F, f, Set.indicator_of_mem hωs] using hω
      · simp [F, f, Set.indicator_of_notMem hωs]
    have hGLim : ∀ᵐ ω ∂μ,
        Tendsto (fun n => G n ω) atTop (𝓝 (g ω)) := by
      filter_upwards [hlim j] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [G, g, Set.indicator_of_mem hωs] using hω
      · simp [G, g, Set.indicator_of_notMem hωs]
    have hfInt : Integrable f μ := (hXIntegrable i).indicator hs0
    have hgInt : Integrable g μ := (hXIntegrable j).indicator hs0
    have hFLp : Tendsto (fun n => eLpNorm (F n - f) 1 μ)
        atTop (𝓝 0) :=
      tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
        hFUI.aestronglyMeasurable (memLp_one_iff_integrable.2 hfInt) hFUI.unifIntegrable hFLim
    have hGLp : Tendsto (fun n => eLpNorm (G n - g) 1 μ)
        atTop (𝓝 0) :=
      tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
        hGUI.aestronglyMeasurable (memLp_one_iff_integrable.2 hgInt) hGUI.unifIntegrable hGLim
    have hFInt : Tendsto (fun n => ∫ ω, F n ω ∂μ)
        atTop (𝓝 (∫ ω, f ω ∂μ)) :=
      tendsto_integral_of_L1' f
        (Filter.Eventually.of_forall fun n =>
          (hM n).integrable i |>.indicator hs0)
        hFLp
    have hGInt : Tendsto (fun n => ∫ ω, G n ω ∂μ)
        atTop (𝓝 (∫ ω, g ω ∂μ)) :=
      tendsto_integral_of_L1' g
        (Filter.Eventually.of_forall fun n =>
          (hM n).integrable j |>.indicator hs0)
        hGLp
    have hEq : ∀ n, (∫ ω, F n ω ∂μ) = ∫ ω, G n ω ∂μ := by
      intro n
      simpa only [F, G, integral_indicator hs0] using
        (hM n).setIntegral_eq hij hs
    have hLimits := tendsto_nhds_unique hFInt
      (hGInt.congr' (Eventually.of_forall fun n => (hEq n).symm))
    simpa only [f, g, integral_indicator hs0] using hLimits
  · exact (hX i).aestronglyMeasurable

end FTAPTheorem42
