/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryMartingaleIntegral
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleEnergyContent
import FTAPTheorem42.Stochastic.Martingale.Quadratic.DiscreteMartingaleSquaredIncrement

/-! # Elementary good-integrator estimates for square-integrable martingales -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {M : Process Ω}

open FiniteHorizonMartingaleEnergyContent

/-- A chronological approximation has the same uniform energy bound as its
represented integrand, independently of the grid size. -/
theorem PredictableElementaryStrategy.horizonGrid_memLp_and_eLpNorm_le
    (H : PredictableElementaryStrategy F) (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) 2 mu) {B : Real} (hB : 0 ≤ B)
    (hBound : ∀ t w, |H.integrand t w| ≤ B) (r : Nat) :
    let g := (LeftContinuousPredictable.finiteGrid r
      (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess H.integrand M T
    MemLp g 2 mu ∧ eLpNorm g 2 mu ≤
      ENNReal.ofReal (B * Real.sqrt (∫ w, (M T w - M 0 w) ^ 2 ∂mu)) := by
  let G r := LeftContinuousPredictable.finiteGrid r
    (LeftContinuousPredictable.horizonCellCount r T)
  let X := deterministicallyStoppedProcess M T
  let f r := (G r).martingaleIntegralProcess H.integrand M T
  have hX := martingale_deterministicallyStopped hM hRight T
  have hXLp t := stoppedProcess_const_memLp_two hM T hMT t
  have hRep r : f r = discretePredictableIntegral
      ((G r).natSample H.integrand) ((G r).natSample X)
        (LeftContinuousPredictable.horizonCellCount r T) := by
    rw [← (G r).martingaleIntegralProcess_last,
      martingaleIntegralProcess_stoppedSource_last]
  have hKB r := (G r).stronglyAdapted_natSample H.integrand_isStronglyPredictable.stronglyAdapted
  have hBound' r : ∀ n, ∀ᵐ w ∂mu, |(G r).natSample H.integrand n w| ≤ B :=
    fun n => Eventually.of_forall (hBound ((G r).sampledTime n))
  have hf r : MemLp (f r) 2 mu := by
    rw [hRep]
    exact DiscretePredictableIntegral.memLp_two
      (ChronologicalGrid.Martingale.natSample (G := G r) hX)
      (fun n => hXLp ((G r).sampledTime n))
      (hKB r) (hBound' r) _
  have hEnergy : 0 ≤ ∫ w, (M T w - M 0 w) ^ 2 ∂mu := integral_nonneg (fun _ => sq_nonneg _)
  have hEstimate r : eLpNorm (f r) 2 mu ≤
      ENNReal.ofReal (B * Real.sqrt (∫ w, (M T w - M 0 w) ^ 2 ∂mu)) := by
    apply DiscreteMartingaleSquaredIncrement.eLpNorm_two_le_of_integral_sq_le (hf r)
      (mul_nonneg hB (Real.sqrt_nonneg _))
    rw [mul_pow, Real.sq_sqrt hEnergy, hRep]
    have hLast : (G r).sampledTime (LeftContinuousPredictable.horizonCellCount r T) =
        LeftContinuousPredictable.gridPoint r (LeftContinuousPredictable.horizonCellCount r T) :=
      LeftContinuousPredictable.finiteGrid_sampledTime_eq _ _ _ le_rfl
    have hFirst : (G r).sampledTime 0 = 0 := by
      rw [LeftContinuousPredictable.finiteGrid_sampledTime_eq _ _ _ (Nat.zero_le _)]
      simp [LeftContinuousPredictable.gridPoint]
    have hContract := DiscretePredictableIntegral.integral_sq_le_mul_terminalIncrement_sq
      (ChronologicalGrid.Martingale.natSample (G := G r) hX)
      (fun n => hXLp ((G r).sampledTime n)) (hKB r) hB (hBound' r)
      (LeftContinuousPredictable.horizonCellCount r T)
    simpa only [ChronologicalGrid.natSample, X, deterministicallyStoppedProcess_apply,
      hLast, hFirst,
      min_eq_right (LeftContinuousPredictable.le_gridPoint_horizonCellCount r T),
      min_eq_left (show (0 : NNReal) ≤ T from bot_le)] using hContract
  exact ⟨hf r, hEstimate r⟩

/-- The bound uses the represented integrand, independently of its number
of elementary blocks or the sum of their coefficient bounds. -/
theorem PredictableElementaryStrategy.eLpNorm_gain_le_integrand_bound
    (H : PredictableElementaryStrategy F) (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) 2 mu) {B : Real} (hB : 0 ≤ B)
    (hBound : ∀ t w, |H.integrand t w| ≤ B) :
    eLpNorm (ElementaryStrategy.gain M H.toElementary T) 2 mu ≤
      ENNReal.ofReal (B * Real.sqrt (∫ w, (M T w - M 0 w) ^ 2 ∂mu)) := by
  have hGrid r := H.horizonGrid_memLp_and_eLpNorm_le hM hRight T hMT hB hBound r
  exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun r => (hGrid r).2)
    (fun r => (hGrid r).1.aestronglyMeasurable)
    ((H.stronglyAdapted_gain M
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous hM.stronglyAdapted hRight) T).mono
      (F.le T)).aestronglyMeasurable
    (Eventually.of_forall (H.tendsto_horizonGrid_martingaleIntegralProcess_of_le M hRight le_rfl))

/-- A bounded represented integrand gives a true stopped martingale even
when its elementary presentation has no bounded absolute coefficient sum. -/
theorem PredictableElementaryStrategy.stoppedGain_isMartingale_of_integrand_bound
    (H : PredictableElementaryStrategy F) (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) 2 mu) {B : Real} (hB : 0 ≤ B)
    (hBound : ∀ t w, |H.integrand t w| ≤ B) :
    Martingale (stoppedProcess (ElementaryStrategy.gain M H.toElementary)
      (fun _ : Ω => (T : WithTop NNReal))) F mu := by
  let grid r := LeftContinuousPredictable.finiteGrid r
    (LeftContinuousPredictable.horizonCellCount r T)
  let X r := (grid r).martingaleIntegralProcess H.integrand M
  let A r := stoppedProcess (X r) (fun _ : Ω => (T : WithTop NNReal))
  let Y := stoppedProcess (ElementaryStrategy.gain M H.toElementary)
    (fun _ : Ω => (T : WithTop NNReal))
  have hXM r : Martingale (X r) F mu :=
    (grid r).martingaleIntegralProcess_isMartingale hM hRight
      H.integrand_isStronglyPredictable (fun t => Eventually.of_forall (hBound t))
  have hAM r : Martingale (A r) F mu :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (hXM r) (isStoppingTime_const F T)
      ((grid r).martingaleIntegralProcess_rightContinuous H.integrand M hRight)
  have hYA : StronglyAdapted F Y :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      (H.stronglyAdapted_gain M
        (StronglyAdapted.isStronglyProgressive_of_rightContinuous hM.stronglyAdapted hRight))
      (isStoppingTime_const F T) (H.rightContinuous_gain M hRight)
  have hLim t : ∀ᵐ w ∂mu, Tendsto (fun r => A r t w) atTop (𝓝 (Y t w)) := by
    apply Eventually.of_forall
    intro w
    simp only [A, Y, stoppedProcess_const_apply]
    exact H.tendsto_horizonGrid_martingaleIntegralProcess_of_le
      M hRight (min_le_right t T) w
  let C : NNReal := ⟨B * Real.sqrt (∫ w, (M T w - M 0 w) ^ 2 ∂mu),
    mul_nonneg hB (Real.sqrt_nonneg _)⟩
  apply Martingale.of_ae_tendsto_of_eLpNorm_two_le A Y hAM hYA hLim C
  intro r t
  have hGrid := H.horizonGrid_memLp_and_eLpNorm_le hM hRight T hMT hB hBound r
  have hEarlier := MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
    (hXM r) (min_le_right t T) hGrid.1
  have hEq : A r t = X r (min t T) := by
    funext w
    exact stoppedProcess_const_apply (X r) T t w
  rw [hEq]
  have hGridBound : eLpNorm (X r T) 2 mu ≤ ENNReal.ofReal (C : Real) := hGrid.2
  exact hEarlier.2.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hGridBound)

theorem ElementaryIntegrandsTendstoUniformlyZero.gain_tendsto_eLpNorm_of_martingale
    {H : Nat → PredictableElementaryStrategy F} (hH : ElementaryIntegrandsTendstoUniformlyZero H)
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) 2 mu) :
    Tendsto (fun n => eLpNorm (ElementaryStrategy.gain M (H n).toElementary T) 2 mu)
      atTop (𝓝 0) := by
  let C := Real.sqrt (∫ w, (M T w - M 0 w) ^ 2 ∂mu)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  by_cases heTop : e = ∞
  · subst e
    exact Eventually.of_forall (fun _ => le_top)
  have heReal : 0 < e.toReal := ENNReal.toReal_pos he.ne' heTop
  let B := e.toReal / (C + 1)
  have hB : 0 < B := div_pos heReal (by positivity)
  filter_upwards [hH B hB] with n hn
  apply ((H n).eLpNorm_gain_le_integrand_bound hM hRight T hMT hB.le hn).trans
  have hBC : B * C ≤ e.toReal := by
    calc
      B * C ≤ B * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ = e.toReal := div_mul_cancel₀ _ (by positivity)
  exact (ENNReal.ofReal_le_ofReal hBC).trans_eq (ENNReal.ofReal_toReal heTop)

theorem isSemimartingale_of_squareIntegrable_martingale
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hMLp : ∀ T, MemLp (M T) 2 mu) : IsSemimartingale M F mu := by
  have hMeas (H : PredictableElementaryStrategy F) (T : NNReal) :
      AEStronglyMeasurable (ElementaryStrategy.gain M H.toElementary T) mu :=
    ((H.stronglyAdapted_gain M
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous hM.stronglyAdapted hRight) T).mono
      (F.le T)).aestronglyMeasurable
  refine ⟨hMeas, ?_⟩
  intro H hH T
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ENNReal) ≠ 0)
  simpa only [sub_zero] using hH.gain_tendsto_eLpNorm_of_martingale hM hRight T (hMLp T)

end FTAPTheorem42
