/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticUnconvex
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticConvexification

/-! # Original quadratic sums under an almost sure uniform bound -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42

open BoundedMartingaleQuadraticApproximation SquareIntegrableMartingaleQuadraticConvexification

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {M N : Process Ω} {T : NNReal}

omit [MeasurableSpace Ω] in
theorem squaredIncrementPart_congr_path {w : Ω} (h : ∀ t, M t w = N t w)
    (T : NNReal) (n : Nat) (t : NNReal) :
    squaredIncrementPart M T n t w = squaredIncrementPart N T n t w := by
  simp only [squaredIncrementPart, ChronologicalGrid.squaredIncrementProcess,
    deterministicallyStoppedProcess_apply, h]

noncomputable def BoundedMartingaleQuadraticKernel.Data.congr_source
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (h : ProcessIndistinguishable mu M N) :
    BoundedMartingaleQuadraticKernel.Data F mu N T :=
  { D with
    martingalePart_uniform := by
      filter_upwards [D.martingalePart_uniform, h] with w hw hPath
      have hRows : ∀ k t,
          BoundedMartingaleQuadraticConvexification.martingalePart M T
            (D.weights (D.cutoff k)) t w =
          BoundedMartingaleQuadraticConvexification.martingalePart N T
            (D.weights (D.cutoff k)) t w := by
        intro k t
        simp only [BoundedMartingaleQuadraticConvexification.martingalePart,
          BoundedMartingaleQuadraticApproximation.martingalePart,
          ChronologicalGrid.martingaleIntegralProcess, Finset.sum_apply,
          Pi.smul_apply, deterministicIntervalMartingaleTransform,
          stoppedProcess_const_apply, deterministicallyStoppedProcess_apply, hPath]
      simpa only [hRows] using hw
    variation_uniform := by
      filter_upwards [D.variation_uniform, h] with w hw hPath
      have hRows : ∀ k t,
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T
            (D.weights (D.cutoff k)) t w =
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart N T
            (D.weights (D.cutoff k)) t w := by
        intro k t
        simp only [BoundedMartingaleQuadraticConvexification.squaredIncrementPart,
          Finset.sum_apply, Pi.smul_apply, squaredIncrementPart_congr_path hPath]
      simpa only [hRows] using hw
    variation_indistinguishable_raw := by
      filter_upwards [D.variation_indistinguishable_raw, h] with w hw hPath
      intro t
      simpa only [BoundedMartingaleQuadraticKernel.rawVariation,
        deterministicallyStoppedProcess_apply, hPath] using hw t }

theorem BoundedMartingaleQuadraticKernel.Data.squaredIncrementPart_terminal_tendstoInMeasure
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hUsual : Filtration.UsualConditions mu F) (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {C : NNReal} (hBound : ∀ᵐ w ∂mu, ∀ t, t ≤ T → |M t w| ≤ C) :
    TendstoInMeasure mu (fun n => squaredIncrementPart M T n T) atTop (D.variation T) := by
  let bad : Set Ω := {w | ¬ ∀ t, t ≤ T → |M t w| ≤ C}
  have hNull : mu bad = 0 := ae_iff.mp hBound
  let N := ProcessNullSetRegularization.zeroOn bad M
  have hInd : ProcessIndistinguishable mu N M :=
    ProcessNullSetRegularization.zeroOn_indistinguishable hNull M
  have hNA : StronglyAdapted F N := ProcessNullSetRegularization.stronglyAdapted_zeroOn
    (hUsual.containsNullSetsAtZero bad hNull) hM.stronglyAdapted
  have hNM : Martingale N F mu := hM.congr hNA
    (fun t => hInd.mono (fun _ hw => (hw t).symm))
  have hNR : ∀ w t, ContinuousWithinAt (N · w) (Ici t) t :=
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun w _ => hRight w)
  have hNL : ProcessHasLeftLimits N :=
    ProcessNullSetRegularization.zeroOn_hasLeftLimits (fun w _ => hLeft w)
  have hNT : MemLp (N T) (2 : ENNReal) mu :=
    hMT.ae_eq (hInd.mono (fun _ hw => (hw T).symm))
  have hNB : ∀ t, t ≤ T → ∀ w, |N t w| ≤ C := by
    intro t ht w
    by_cases hw : w ∈ bad
    · simp only [N, ProcessNullSetRegularization.zeroOn_apply_of_mem bad M hw, abs_zero]
      exact C.coe_nonneg
    · rw [show N t w = M t w from
        ProcessNullSetRegularization.zeroOn_apply_of_notMem bad M hw]
      exact (not_not.mp hw) t ht
  let DN := D.congr_source (hInd.mono (fun _ hw t => (hw t).symm))
  have hLimit := squaredIncrementPart_terminal_tendsto_eLpNorm_two DN hNM hNR hNL hNT hNB
  have hInMeasure : TendstoInMeasure mu (fun n => squaredIncrementPart N T n T)
      atTop (D.variation T) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
      hLimit
  apply hInMeasure.congr_left
  intro n
  filter_upwards [hInd] with w hw
  exact squaredIncrementPart_congr_path hw T n T

end FTAPTheorem42
