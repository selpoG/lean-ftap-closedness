/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedMartingaleTerminalIntegral
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridAdaptedElementaryStrategy

/-! # Energy convergence of the original quadratic grid coefficients -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedMartingaleQuadraticApproximation

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {M : Process Ω} {T : NNReal}

private theorem stoppedSource_stronglyAdapted (hM : StronglyAdapted F M) (T : NNReal) :
    StronglyAdapted F (deterministicallyStoppedProcess M T) := by
  intro t
  have hEq : deterministicallyStoppedProcess M T t = M (min t T) :=
    funext (fun _ => deterministicallyStoppedProcess_apply _ _ _ _)
  rw [hEq]
  exact (hM (min t T)).mono (F.mono (min_le_left _ _))

noncomputable def gridStrategy (hM : StronglyAdapted F M) (T : NNReal) (n : Nat) :
    PredictableElementaryStrategy F :=
  (grid T n).adaptedElementaryStrategy F
    ((grid T n).natSample (deterministicallyStoppedProcess M T))
    ((grid T n).stronglyAdapted_natSample
      (stoppedSource_stronglyAdapted hM T))

theorem gridStrategy_integrand (hM : StronglyAdapted F M) (T : NNReal) (n : Nat) :
    (gridStrategy hM T n).integrand =
      (grid T n).predictableStepProcess (deterministicallyStoppedProcess M T) := by
  unfold gridStrategy ChronologicalGrid.adaptedElementaryStrategy
    PredictableElementaryStrategy.integrand ChronologicalGrid.predictableStepProcess
  simp only [List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem gridStrategy_bound (hM : StronglyAdapted F M) (T : NNReal) (n : Nat)
    {C : NNReal} (hBound : ∀ t, t ≤ T → ∀ w, |M t w| ≤ C) :
    ∀ w, (gridStrategy hM T n).coefficientAbsSum w ≤
      (((level T n) * (level T n).factorial : Nat) : Real) * C := by
  intro w
  unfold gridStrategy ChronologicalGrid.adaptedElementaryStrategy
    PredictableElementaryStrategy.coefficientAbsSum
  simp only [List.map_map]
  calc
    _ ≤ ((List.range ((level T n) * (level T n).factorial)).map
        (fun _ => (C : Real))).sum := by
      apply List.sum_le_sum
      intro k _
      exact hBound _ (min_le_right _ _) w
    _ = _ := by simp

theorem gridStrategy_gain (hM : StronglyAdapted F M) (T : NNReal) (n : Nat) :
    martingalePart M T n T =
      (2 : Real) • ElementaryStrategy.gain M (gridStrategy hM T n).toElementary T := by
  funext w
  unfold martingalePart ChronologicalGrid.martingaleIntegralProcess
    gridStrategy ChronologicalGrid.adaptedElementaryStrategy
    PredictableElementaryStrategy.toElementary ElementaryStrategy.gain
  simp only [List.map_map, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [deterministicIntervalMartingaleTransform,
    ChronologicalGrid.adaptedElementaryBlock, ElementaryInterval.gain,
    stoppedProcess_const_apply, deterministicallyStoppedProcess_apply, ChronologicalGrid.natSample,
    Function.comp_apply, min_assoc]
  have hMin (s : NNReal) : min T (min s T) = min T s := by
    rw [min_eq_right (min_le_right s T), min_comm T s]
  rw [hMin, hMin]

variable [IsProbabilityMeasure mu]

theorem tendsto_gridStrategy_energy
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : StronglyAdapted F M) (hLeft : ProcessHasLeftLimits M)
    {C : NNReal} (hBound : ∀ t, t ≤ T → ∀ w, |M t w| ≤ C) :
    Tendsto (fun n => eLpNorm
      (Function.uncurry (gridStrategy hM T n).integrand -
        fun p => Function.leftLim (deterministicallyStoppedProcess M T · p.2) p.1)
      (2 : ENNReal) D.predictableEnergyMeasure) atTop (𝓝 0) := by
  let : MeasurableSpace (NNReal × Ω) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure := D.predictableEnergyMeasure_isFinite
  let K : Nat → NNReal × Ω → Real := fun n => Function.uncurry (gridStrategy hM T n).integrand
  let L : NNReal × Ω → Real :=
    fun p => Function.leftLim (deterministicallyStoppedProcess M T · p.2) p.1
  have hLeftX : ProcessHasLeftLimits (deterministicallyStoppedProcess M T) := hLeft.stoppedProcess _
  have hAX : StronglyAdapted F (deterministicallyStoppedProcess M T) :=
    stoppedSource_stronglyAdapted hM T
  have hKBound : ∀ n p, |K n p| ≤ C := by
    intro n p
    exact (grid T n).abs_adaptedElementaryStrategy_integrand_le F _ _ C.coe_nonneg
      (fun _ w => hBound _ (min_le_right _ _) w) p.1 p.2
  have hLBound : ∀ᵐ p ∂D.predictableEnergyMeasure, |L p| ≤ C := by
    filter_upwards [D.ae_time_pos, D.ae_time_le_horizon] with p hp0 hpT
    have h := tendsto_grid_predictableStepProcess_stoppedSource M hLeft T hp0.ne' hpT p.2
    apply le_of_tendsto h.abs
    exact Eventually.of_forall (fun n => by
      simpa only [K, gridStrategy_integrand, Function.uncurry] using hKBound n p)
  have hLimit : ∀ᵐ p ∂D.predictableEnergyMeasure,
      Tendsto (fun n => K n p) atTop (𝓝 (L p)) := by
    filter_upwards [D.ae_time_pos, D.ae_time_le_horizon] with p hp0 hpT
    simpa only [K, L, gridStrategy_integrand, Function.uncurry] using
      tendsto_grid_predictableStepProcess_stoppedSource M hLeft T hp0.ne' hpT p.2
  apply tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    (fun n => (gridStrategy hM T n).integrand_isStronglyPredictable.aestronglyMeasurable)
    (hLeftX.stronglyPredictable_leftLim hAX).aestronglyMeasurable
    (memLp_const (μ := D.predictableEnergyMeasure) (p := (2 : ENNReal)) (2 * (C : Real)))
    _ hLimit
  intro n
  filter_upwards [hLBound] with p hp
  change ‖K n p - L p‖ ≤ ‖2 * (C : Real)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (C : Real))]
  exact (abs_sub _ _).trans (by linarith [hKBound n p])

theorem gridStrategy_terminal_cauchy [SigmaFiniteFiltration mu F]
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {C : NNReal} (hBound : ∀ t, t ≤ T → ∀ w, |M t w| ≤ C) :
    CauchySeq (fun n =>
      ((gridStrategy hM.stronglyAdapted T n).gain_memLp_two M hM hRight T hMT
        (((level T n) * (level T n).factorial : Nat) * C)
        (gridStrategy_bound hM.stronglyAdapted T n hBound)).toLp
          (ElementaryStrategy.gain M (gridStrategy hM.stronglyAdapted T n).toElementary T)) := by
  let : MeasurableSpace (NNReal × Ω) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure := D.predictableEnergyMeasure_isFinite
  let H := fun n => gridStrategy hM.stronglyAdapted T n
  let B : Nat → NNReal := fun n => ((level T n) * (level T n).factorial : Nat) * C
  have hB : ∀ n w, (H n).coefficientAbsSum w ≤ B n :=
    fun n => gridStrategy_bound hM.stronglyAdapted T n hBound
  have hKH := fun n => BoundedMartingaleQuadraticEnergy.Data.elementaryIntegrand_memLp_two
    D (H n) (B n) (hB n)
  let K := fun n => (hKH n).toLp (Function.uncurry (H n).integrand)
  have hK : CauchySeq K := by
    have h := tendsto_gridStrategy_energy D hM.stronglyAdapted hLeft hBound
    let L : NNReal × Ω → Real :=
      fun p => Function.leftLim (deterministicallyStoppedProcess M T · p.2) p.1
    have hLMeas : StronglyMeasurable[F.predictable] L :=
      (hLeft.stoppedProcess _).stronglyPredictable_leftLim
        (stoppedSource_stronglyAdapted hM.stronglyAdapted T)
    have hLMem : MemLp L (2 : ENNReal) D.predictableEnergyMeasure := by
      apply MemLp.of_bound hLMeas.aestronglyMeasurable (C : Real)
      filter_upwards [D.ae_time_pos, D.ae_time_le_horizon] with p hp0 hpT
      rw [Real.norm_eq_abs]
      have hLimit :=
        tendsto_grid_predictableStepProcess_stoppedSource M hLeft T hp0.ne' hpT p.2
      apply le_of_tendsto hLimit.abs
      apply Eventually.of_forall
      intro n
      rw [← gridStrategy_integrand hM.stronglyAdapted T n]
      exact (grid T n).abs_adaptedElementaryStrategy_integrand_le F _ _ C.coe_nonneg
        (fun _ w => hBound _ (min_le_right _ _) w) p.1 p.2
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hKH L hLMem).mpr h |>.cauchySeq
  rw [Metric.cauchySeq_iff] at hK ⊢
  intro e he
  obtain ⟨N, hN⟩ := hK e he
  refine ⟨N, fun n hn m hm => ?_⟩
  have hIso :=
    BoundedMartingaleQuadraticEnergy.Data.eLpNorm_predictableEnergyMeasure_sub_eq_gain_sub
    D hM hRight hMT (H n) (H m) (B n) (B m) (hB n) (hB m)
  have hDist : dist
      (((H n).gain_memLp_two M hM hRight T hMT (B n) (hB n)).toLp
        (ElementaryStrategy.gain M (H n).toElementary T))
      (((H m).gain_memLp_two M hM hRight T hMT (B m) (hB m)).toLp
        (ElementaryStrategy.gain M (H m).toElementary T)) = dist (K n) (K m) := by
    rw [Lp.dist_edist, Lp.edist_toLp_toLp, Lp.dist_edist, Lp.edist_toLp_toLp]
    exact congrArg ENNReal.toReal hIso.symm
  rw [hDist]
  exact hN n hn m hm

end FTAPTheorem42.BoundedMartingaleQuadraticApproximation
