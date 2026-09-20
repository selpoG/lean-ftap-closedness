/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Davis.MartingaleConvexGridDavis
import FTAPTheorem42.Stochastic.Martingale.Davis.FiniteDiscreteReverseDavis

/-! # Reverse Davis inequality from the original quadratic sums -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open BoundedMartingaleQuadraticApproximation BoundedMartingaleQuadraticKernel
open SIntegrableFiniteVariationBridge SquareIntegrableMartingaleQuadraticConvexification

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] {M : Process Ω} {T : NNReal}

theorem lintegral_root_le_seven_maximal_of_quadraticGrid_tendstoInMeasure
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hZero : M 0 = 0)
    {V : Ω → Real}
    (hLimit : TendstoInMeasure mu (fun n => squaredIncrementPart M T n T) atTop V) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (V w)) ∂mu) ≤
      7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T w) ∂mu := by
  let E := FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T
  have hBound (n : Nat) :
      (∫⁻ w, ENNReal.ofReal (Real.sqrt (squaredIncrementPart M T n T w)) ∂mu) ≤
        7 * ∫⁻ w, ENNReal.ofReal (E w) ∂mu := by
    let G := grid T n
    let N := (level T n) * (level T n).factorial
    have hSample := ChronologicalGrid.Martingale.natSample (G := G) hM
    have hRoot := finiteDiscreteDavisRoot_integrable_of_martingale hSample N
    have hStar := finiteDiscreteDavisStar_integrable_of_martingale hSample N
    have hRootEq : (fun w => Real.sqrt (squaredIncrementPart M T n T w)) =
        finiteDiscreteDavisRoot (G.natSample M) N := by
      funext w
      exact (finiteDiscreteDavisRoot_grid_eq_squaredIncrementPart_root M T n hZero w).symm
    simp_rw [congrFun hRootEq]
    calc
      (∫⁻ w, ENNReal.ofReal (finiteDiscreteDavisRoot (G.natSample M) N w) ∂mu) =
          ENNReal.ofReal (∫ w, finiteDiscreteDavisRoot (G.natSample M) N w ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal hRoot
          (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))).symm
      _ ≤ ENNReal.ofReal (7 * ∫ w, finiteDiscreteDavisStar (G.natSample M) N w ∂mu) :=
        ENNReal.ofReal_le_ofReal (integral_finiteDiscrete_root_le_seven_star_of_martingale
          hSample N)
      _ = 7 * ∫⁻ w, ENNReal.ofReal (finiteDiscreteDavisStar (G.natSample M) N w) ∂mu := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 7),
          ofReal_integral_eq_lintegral_ofReal hStar
            (Eventually.of_forall (finiteDiscreteDavisStar_nonneg _ _))]
        norm_num
      _ ≤ _ := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono
        intro w
        apply ENNReal.ofReal_le_ofReal
        apply Finset.sup'_le Finset.nonempty_range_add_one
        intro k _
        exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
          hRight hLeft T _ (show G.sampledTime k ≤ T from min_le_right _ _)
  obtain ⟨ns, _, hns⟩ := hLimit.exists_seq_tendsto_ae
  have hRootLimit : ∀ᵐ w ∂mu, Tendsto
      (fun n => ENNReal.ofReal (Real.sqrt (squaredIncrementPart M T (ns n) T w)))
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt (V w)))) := by
    filter_upwards [hns] with w hw
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp hw)
  have hMeas (n : Nat) : AEMeasurable
      (fun w => ENNReal.ofReal (Real.sqrt (squaredIncrementPart M T (ns n) T w))) mu := by
    have h := Real.continuous_sqrt.comp_stronglyMeasurable
      (squaredIncrementPart_terminal_stronglyMeasurable hM hRight T (ns n))
    exact h.measurable.ennreal_ofReal.aemeasurable
  calc
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (V w)) ∂mu) =
        ∫⁻ w, liminf
          (fun n => ENNReal.ofReal (Real.sqrt (squaredIncrementPart M T (ns n) T w)))
          atTop ∂mu := lintegral_congr_ae (hRootLimit.mono (fun _ h => h.liminf_eq.symm))
    _ ≤ liminf (fun n => ∫⁻ w,
        ENNReal.ofReal (Real.sqrt (squaredIncrementPart M T (ns n) T w)) ∂mu) atTop :=
      lintegral_liminf_le' hMeas
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall (fun n => hBound (ns n))).frequently

end FTAPTheorem42
