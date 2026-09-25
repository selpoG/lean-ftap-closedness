/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer

/-!
# Agreement of the finite-variation process completion

The canonical predictable simple approximations converge pathwise under
every finite source-variation measure when the target coefficient is
bounded.  The variation contraction therefore upgrades their coefficient
convergence to uniform convergence of the cumulative Stieltjes processes.
Consequently the selected completed process agrees, up to
indistinguishability, with the original cumulative integral on every bounded
predictable coefficient.
-/

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The common simple approximation is pointwise no farther from its target
than zero is. -/
theorem abs_predictableCommonSimpleApproximation_sub_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (n : Nat) (t : NNReal) (omega : Omega) :
    |predictableCommonSimpleApproximation f hf n t omega - f t omega| <=
      |f t omega| := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set Real) :=
    hf.separableSpace_range_union_singleton
  have h := SimpleFunc.nnnorm_approxOn_le
    hf.measurable
    (by simp : (0 : Real) ∈ Set.range (Function.uncurry f) ∪ {0})
    (t, omega) n
  have hReal :
      ‖(SimpleFunc.approxOn (Function.uncurry f) hf.measurable
          (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n) (t, omega) -
        Function.uncurry f (t, omega)‖ <=
      ‖Function.uncurry f (t, omega) - 0‖ := by
    exact_mod_cast h
  simpa only [predictableCommonSimpleApproximation,
    predictableCommonSimpleApproximationRaw, Real.norm_eq_abs,
    Function.uncurry_apply_pair, sub_zero] using hReal

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

omit [SigmaFiniteFiltration mu F] in
/-- For a bounded predictable target, the common simple cumulative
integrals converge uniformly on the whole time axis, path by path, to the
original cumulative Stieltjes integral. -/
theorem commonFiniteVariationProcessApproximation_tendstoUniformly_bounded
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    {C : Real} (hBound : forall t omega, |f t omega| <= C)
    (omega : Omega) :
    TendstoUniformly
      (fun n t => commonFiniteVariationProcessApproximation E f hf n t omega)
      (fun t => finiteVariationIntegralProcess E f t omega) atTop := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  let : IsFiniteMeasure nu := by
    dsimp only [nu]
    unfold SignedMeasure.totalVariation
    infer_instance
  let d : Nat -> NNReal -> Real := fun n t =>
    predictableCommonSimpleApproximation f hf n t omega - f t omega
  have hdMeasurable : forall n, AEStronglyMeasurable (d n) nu := by
    intro n
    exact (((predictableCommonSimpleApproximation_isStronglyPredictable
      f hf n).sub hf).mono
        (PredictableKernelMeasure.predictable_le_prod F)
      |>.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  have hdBound : forall n, ∀ᵐ t ∂nu, ‖d n t‖ <= max 0 C := by
    intro n
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact (abs_predictableCommonSimpleApproximation_sub_le
        f hf n t omega).trans ((hBound t omega).trans (le_max_right 0 C))
  have hdTendsto : ∀ᵐ t ∂nu,
      Tendsto (fun n => d n t) atTop (nhds 0) := by
    exact Filter.Eventually.of_forall fun t => by
      simpa only [d, sub_self] using
        (predictableCommonSimpleApproximation_tendsto f hf t omega).sub_const
          (f t omega)
  have hIntegralNorm : Tendsto (fun n => ∫ t, ‖d n t‖ ∂nu)
      atTop (nhds 0) := by
    have hDCT := tendsto_integral_of_dominated_convergence
      (μ := nu) (F := fun n t => ‖d n t‖) (f := fun _ => (0 : Real))
      (fun _ => max 0 C)
      (fun n => (hdMeasurable n).norm)
      (integrable_const (max 0 C))
      (fun n => by
        filter_upwards [hdBound n] with t ht
        simpa only [norm_norm] using ht)
      (by
        filter_upwards [hdTendsto] with t ht
        simpa using ht.norm)
    simpa using hDCT
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hIntegralNorm) epsilon hepsilon
  filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
  intro t
  have hApproxPredictable :=
    predictableCommonSimpleApproximation_isStronglyPredictable f hf n
  obtain ⟨A, hA⟩ :=
    exists_predictableCommonSimpleApproximation_bound f hf n
  have hDistance :=
    dist_finiteVariationIntegralProcess_le_lintegral_toReal E
      hApproxPredictable hf hA hBound omega t
  have hIntegralEq :
      (∫⁻ u, ‖predictableCommonSimpleApproximation f hf n u omega -
          f u omega‖ₑ ∂nu).toReal = ∫ u, ‖d n u‖ ∂nu := by
    rw [integral_norm_eq_lintegral_enorm (hdMeasurable n)]
  rw [show commonFiniteVariationProcessApproximation E f hf n t omega =
      finiteVariationIntegralProcess E
        (predictableCommonSimpleApproximation f hf n) t omega by rfl]
  rw [show (FiniteVariationPath.signedMeasure
      (G.finiteVariationPart_isBoundedVariation omega)).totalVariation =
      nu by rfl, hIntegralEq] at hDistance
  have hIntegralNonnegative : 0 <= ∫ u, ‖d n u‖ ∂nu :=
    integral_nonneg fun _ => norm_nonneg _
  have hn' : (∫ u, ‖d n u‖ ∂nu) < epsilon := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hIntegralNonnegative] using hn
  simpa only [dist_comm] using hDistance.trans_lt hn'

omit [SigmaFiniteFiltration mu F] in
/-- Restricting a coefficient to `(0,T]` and then integrating cumulatively
is exactly the same as stopping its cumulative integral at `T`. -/
theorem finiteVariationIntegralProcess_finiteHorizonCoefficient
    (E : SIntegrableFiniteVariationBridge G)
    (T t : NNReal) (f : NNReal × Omega -> Real) (omega : Omega) :
    finiteVariationIntegralProcess E (finiteHorizonCoefficient T f) t omega =
      finiteVariationIntegralProcess E (Function.curry f) (min t T) omega := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  change (∫ u in Ioc 0 t,
      finiteVariationIntegralDensity E (finiteHorizonCoefficient T f)
        (u, omega) ∂nu) =
    ∫ u in Ioc 0 (min t T),
      finiteVariationIntegralDensity E (Function.curry f) (u, omega) ∂nu
  rw [← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hut : u ∈ Ioc (0 : NNReal) t
  · by_cases huT : u ∈ Ioc (0 : NNReal) T
    · have huMin : u ∈ Ioc (0 : NNReal) (min t T) := by
        exact ⟨hut.1, le_min hut.2 huT.2⟩
      simp only [Set.indicator_of_mem hut, Set.indicator_of_mem huMin]
      rw [finiteVariationIntegralDensity, finiteVariationIntegralDensity,
        finiteHorizonCoefficient, PredictableProcess.restrict_apply_of_mem]
      exact (mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => T) u omega).2 huT
    · have huMin : u ∉ Ioc (0 : NNReal) (min t T) := by
        intro h
        exact huT ⟨h.1, h.2.trans (min_le_right t T)⟩
      simp only [Set.indicator_of_mem hut, Set.indicator_of_notMem huMin]
      rw [finiteVariationIntegralDensity, finiteHorizonCoefficient,
        PredictableProcess.restrict_apply_of_notMem, mul_zero]
      exact fun h => huT ((mem_stochasticIntervalIocZero_iff
        (fun _ : Omega => T) u omega).1 h)
  · have huMin : u ∉ Ioc (0 : NNReal) (min t T) := by
      intro h
      exact hut ⟨h.1, h.2.trans (min_le_left t T)⟩
    simp only [Set.indicator_of_notMem hut, Set.indicator_of_notMem huMin]

omit [SigmaFiniteFiltration mu F] in
/-- On every bounded predictable coefficient, the selected process
completion is the original cumulative Stieltjes integral up to
indistinguishability. -/
theorem completedFiniteVariationProcess_indistinguishable_bounded
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E))
    {C : Real} (hBound : forall t omega, |f t omega| <= C) :
    ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E f hf hVariation)
      (finiteVariationIntegralProcess E f) := by
  let data := completedFiniteVariationProcessData
    hUsual E f hf hVariation
  filter_upwards [data.approximation_tendsto] with omega hCompleted
  intro t
  have hDirect : TendstoUniformly
      (fun n u => commonFiniteVariationProcessApproximation
        E f hf (data.cutoff n) u omega)
      (fun u => finiteVariationIntegralProcess E f u omega) atTop :=
    (tendstoUniformly_iff_seq_tendstoUniformly.mp
      (commonFiniteVariationProcessApproximation_tendstoUniformly_bounded
        E f hf hBound omega)) data.cutoff data.cutoff_strictMono.tendsto_atTop
  exact tendsto_nhds_unique (hCompleted.1.tendsto_at t)
    (hDirect.tendsto_at t)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
