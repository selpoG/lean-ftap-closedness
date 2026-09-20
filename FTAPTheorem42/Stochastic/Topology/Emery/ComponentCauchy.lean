import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Stochastic.Topology.Emery.FiniteVariationTestEstimate

/-! # Component probability estimates imply uniform elementary Emery Cauchy control

The two indices refer to the same sequence throughout. The martingale test
threshold is chosen before the elementary multiplier; the finite-variation
estimate uses only a deterministic finite horizon. No component limit is needed.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_le_threshold_add_tail
    {f : Ω → Real} (hf : Measurable f) (hBound : ∀ w, 0 ≤ f w ∧ f w ≤ 1)
    {δ : Real} (hδ : 0 ≤ δ) :
    ∫ w, f w ∂μ ≤ δ + μ.real {w | δ < f w} := by
  let s := {w | δ < f w}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hf
  have hInt : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBound w).1]
      exact (hBound w).2)
  have hInd : Integrable (s.indicator (fun _ : Ω => (1 : Real))) μ :=
    (integrable_const 1).indicator hs
  have hLe : ∀ w, f w ≤ δ + s.indicator (fun _ : Ω => (1 : Real)) w := by
    intro w
    by_cases hw : w ∈ s
    · rw [indicator_of_mem hw]
      exact (hBound w).2.trans (le_add_of_nonneg_left hδ)
    · rw [indicator_of_notMem hw, add_zero]
      exact le_of_not_gt hw
  have h := integral_mono_ae hInt ((integrable_const δ).add hInd)
    (Eventually.of_forall hLe)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const δ) hInd, integral_const] at h
  have hIndEq : (∫ w, s.indicator (fun _ : Ω => (1 : Real)) w ∂μ) = μ.real s :=
    integral_indicator_one hs
  rw [hIndEq] at h
  simpa using h

/-- Uniform probability control of the capped errors gives the expected-error
Cauchy estimate. The single index threshold works for every elementary test. -/
theorem elementaryEmeryCauchy_of_uniform_probability
    {Y : Nat → Process Ω} (hY : ∀ n, IsStronglyProgressive F (Y n))
    (hProb : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∀ J : BoundedPredictableElementaryMultiplier F,
        μ.real {w | ε < elementaryEmeryTestError (Y m) (Y n) J T w} ≤ ε) :
    ElementaryEmeryCauchy μ F Y := by
  intro T ε hε
  obtain ⟨N, hN⟩ := hProb T (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn J => ?_⟩
  exact (integral_le_threshold_add_tail
    (elementaryEmeryTestError_measurable (hY m) (hY n) J T).measurable
    (elementaryEmeryTestError_bounds _ _ J T) (half_pos hε).le).trans
      ((add_le_add le_rfl (hN m hm n hn J)).trans_eq (add_halves ε))

/-- A common residual control and a test-uniform component estimate give
Cauchy control of the sum, also for indistinguishable decompositions. -/
theorem elementaryEmeryCauchy_of_component_estimates
    {Y M A : Nat → Process Ω} (hY : ∀ n, IsStronglyProgressive F (Y n))
    (hDecomp : ∀ n, ProcessIndistinguishable μ (Y n) (M n + A n))
    {V : Nat → Nat → NNReal → Ω → Real}
    (hBound : ∀ m n T, ∀ J : BoundedPredictableElementaryMultiplier F,
      ∀ᵐ w ∂μ, elementaryEmeryTestError (A m) (A n) J T w ≤ V m n T w)
    (hM : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∀ J : BoundedPredictableElementaryMultiplier F,
        μ.real {w | ε < elementaryEmeryTestError (M m) (M n) J T w} ≤ ε)
    (hV : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      μ.real {w | ε < V m n T w} ≤ ε) :
    ElementaryEmeryCauchy μ F Y := by
  apply elementaryEmeryCauchy_of_uniform_probability hY
  intro T ε hε
  have hδ : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨NM, hNM⟩ := hM T (ε / 3) hδ
  obtain ⟨NV, hNV⟩ := hV T (ε / 3) hδ
  refine ⟨max NM NV, fun m hm n hn J => ?_⟩
  have hSub : ∀ᵐ w ∂μ,
      w ∈ {w | ε < elementaryEmeryTestError (Y m) (Y n) J T w} →
      w ∈ ({w | ε / 3 < elementaryEmeryTestError (M m) (M n) J T w} ∪
        {w | ε / 3 < V m n T w} : Set Ω) := by
    filter_upwards [elementaryEmeryTestError_congr (hDecomp m) (hDecomp n) J T,
      hBound m n T J] with w hEq hA
    intro hw
    change ε < elementaryEmeryTestError (Y m) (Y n) J T w at hw
    change ε / 3 < elementaryEmeryTestError (M m) (M n) J T w ∨ ε / 3 < V m n T w
    by_contra h
    push Not at h
    have hAdd := elementaryEmeryTestError_add_le (M m) (A m) (M n) (A n) J T w
    rw [hEq] at hw
    linarith
  have hMeasure := ENNReal.toReal_mono (measure_ne_top μ _ ) (measure_mono_ae hSub)
  have hUnion := measureReal_union_le (μ := μ)
    {w | ε / 3 < elementaryEmeryTestError (M m) (M n) J T w}
    {w | ε / 3 < V m n T w}
  have hMm := hNM m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn) J
  have hVn := hNV m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
  exact hMeasure.trans (hUnion.trans ((add_le_add hMm hVn).trans (by linarith)))

/-- Locally finite variation supplies the residual control on each finite
horizon. Only the martingale transforms need a test-uniform probability bound. -/
theorem elementaryEmeryCauchy_of_local_component_estimates
    {Y M A : Nat → Process Ω} (hY : ∀ n, IsStronglyProgressive F (Y n))
    (hDecomp : ∀ n, ProcessIndistinguishable μ (Y n) (M n + A n))
    (hBV : ∀ m n w, LocallyBoundedVariationOn ((A m - A n) · w) univ)
    (hRight : ∀ n w t, ContinuousWithinAt (A n · w) (Ici t) t)
    (hM : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∀ J : BoundedPredictableElementaryMultiplier F,
        μ.real {w | ε < elementaryEmeryTestError (M m) (M n) J T w} ≤ ε)
    (hV : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      μ.real {w | ε < finiteHorizonPathVariation (A m - A n) (hBV m n) T w} ≤ ε) :
    ElementaryEmeryCauchy μ F Y := by
  apply elementaryEmeryCauchy_of_component_estimates hY hDecomp (V := fun m n T =>
    finiteHorizonPathVariation (A m - A n) (hBV m n) T) ?_ hM hV
  intro m n T J
  apply Eventually.of_forall
  intro w
  have h := J.capped_gain_le_finiteHorizonPathVariation (A m - A n) (hBV m n)
    (fun w t => (hRight m w t).sub (hRight n w t)) T w
  have hGain := PredictableElementaryEmery.elementaryGain_source_sub (A m) (A n) J.strategy
  change ElementaryStrategy.gain (A m - A n) J.strategy.toElementary =
    (fun t w => ElementaryStrategy.gain (A m) J.strategy.toElementary t w -
      ElementaryStrategy.gain (A n) J.strategy.toElementary t w) at hGain
  rw [hGain] at h
  exact h.trans (min_le_left _ _)

end FTAPTheorem42
