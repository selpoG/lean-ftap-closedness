/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernelTerminalRootLimit
import FTAPTheorem42.Stochastic.Martingale.Davis.FiniteDiscreteReverseDavis
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Foundations.CadlagEnvelope

/-!
# Davis estimates on convexified grids

Identify the discrete maximal and square functions on factorial grids and pass
the Davis estimate to forward convex combinations.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel

variable {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open SIntegrableFiniteVariationBridge
open SquareIntegrableMartingaleQuadraticApproximation

omit [MeasurableSpace Omega] in
theorem finiteDiscreteDavisStar_grid_eq_factorialRunningMax
    (M : Process Omega) (T : NNReal) (i : Nat) (omega : Omega) :
    finiteDiscreteDavisStar ((grid T i).natSample M)
        ((level T i) * (level T i).factorial) omega =
      FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T i) omega := by
  rfl

omit [MeasurableSpace Omega] in
theorem finiteDiscreteDavisSquare_grid_eq_squaredIncrementPart
    (M : Process Omega) (T : NNReal) (i : Nat)
    (hM0 : M 0 = 0) (omega : Omega) :
    finiteDiscreteDavisSquare ((grid T i).natSample M)
        ((level T i) * (level T i).factorial) omega =
      BoundedMartingaleQuadraticApproximation.squaredIncrementPart
        M T i T omega := by
  unfold finiteDiscreteDavisSquare
  rw [show ((grid T i).natSample M) 0 omega = 0 by
    change M ((grid T i).sampledTime 0) omega = 0
    rw [grid_sampledTime_zero]
    simpa using congrFun hM0 omega]
  rw [squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum]
  norm_num
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hTime (j : Nat) : (grid T i).sampledTime j ≤ T := by
    change min _ T ≤ T
    exact min_le_right _ _
  change M ((grid T i).sampledTime (k + 1)) omega -
      M ((grid T i).sampledTime k) omega =
    (deterministicallyStoppedProcess M T ((grid T i).sampledTime (k + 1)) omega -
      deterministicallyStoppedProcess M T ((grid T i).sampledTime k) omega)
  rw [deterministicallyStoppedProcess_apply, deterministicallyStoppedProcess_apply]
  simp only [min_eq_left (hTime (k + 1)), min_eq_left (hTime k)]

omit [MeasurableSpace Omega] in
theorem finiteDiscreteDavisRoot_grid_eq_squaredIncrementPart_root
    (M : Process Omega) (T : NNReal) (i : Nat)
    (hM0 : M 0 = 0) (omega : Omega) :
    finiteDiscreteDavisRoot ((grid T i).natSample M)
        ((level T i) * (level T i).factorial) omega =
      Real.sqrt
        (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
          M T i T omega) := by
  unfold finiteDiscreteDavisRoot
  rw [finiteDiscreteDavisSquare_grid_eq_squaredIncrementPart
    M T i hM0 omega]

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridDavis_integral_runningMax_le_six_root
    (M : Process Omega) (T : NNReal)
    (hM : Martingale M F mu)
    (hM0 : M 0 = 0) (i : Nat) :
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T i) omega ∂mu) ≤
      6 * ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
          M T i T omega) ∂mu := by
  let G := grid T i
  let N := (level T i) * (level T i).factorial
  have hSample : Martingale (G.natSample M) (G.sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hM
  have hDavis :=
    integral_finiteDiscreteDavis_le_six_root_of_martingale hSample N
  calc
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T i) omega ∂mu) =
        ∫ omega, finiteDiscreteDavisStar (G.natSample M) N omega ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by
        simpa only [G, N] using
          (finiteDiscreteDavisStar_grid_eq_factorialRunningMax M T i omega).symm
    _ ≤ 6 * ∫ omega, finiteDiscreteDavisRoot (G.natSample M) N omega ∂mu :=
      hDavis
    _ = 6 * ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
          M T i T omega) ∂mu := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by
        simpa only [G, N] using
          (finiteDiscreteDavisRoot_grid_eq_squaredIncrementPart_root
            M T i hM0 omega)

omit [SigmaFiniteFiltration mu F] [IsProbabilityMeasure mu] in
theorem factorialGridDavisStar_integrable
    (M : Process Omega) (T : NNReal)
    (hM : Martingale M F mu)
    (i : Nat) :
    Integrable (FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T i)) mu := by
  let G := grid T i
  let N := (level T i) * (level T i).factorial
  have hSample : Martingale (G.natSample M) (G.sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hM
  have hStarInt := finiteDiscreteDavisStar_integrable_of_martingale hSample N
  apply hStarInt.congr
  exact Filter.Eventually.of_forall fun omega => by
    simpa only [G, N] using
      (finiteDiscreteDavisStar_grid_eq_factorialRunningMax M T i omega)

omit [SigmaFiniteFiltration mu F] [IsProbabilityMeasure mu] in
theorem factorialGridDavisRoot_integrable
    (M : Process Omega) (T : NNReal)
    (hM : Martingale M F mu)
    (hM0 : M 0 = 0) (i : Nat) :
    Integrable (fun omega => Real.sqrt
      (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
        M T i T omega)) mu := by
  let G := grid T i
  let N := (level T i) * (level T i).factorial
  have hSample : Martingale (G.natSample M) (G.sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hM
  have hRoot := finiteDiscreteDavisRoot_integrable_of_martingale hSample N
  apply hRoot.congr
  exact Filter.Eventually.of_forall fun omega => by
    simpa only [G, N] using
      (finiteDiscreteDavisRoot_grid_eq_squaredIncrementPart_root
        M T i hM0 omega)

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridDavis_integral_runningMax_le_six_convexRoot
    (M : Process Omega) (T : NNReal) (hM : Martingale M F mu) (hM0 : M 0 = 0)
    {m : Nat} (w : TailConvexWeights m)
    (hRowInt : Integrable (fun omega => Real.sqrt
      (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega)) mu)
    (r : Nat) (hkr : r ≤ m) :
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
      6 * ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) ∂mu := by
  have hCoarseStarInt : Integrable
      (FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T r)) mu :=
    factorialGridDavisStar_integrable M T hM r
  have hWeightedStarInt : Integrable (fun omega =>
      ∑ i ∈ w.support, w.weight i *
        FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T i) omega) mu := by
    apply integrable_finsetSum w.support
    intro i hi
    exact (factorialGridDavisStar_integrable M T hM i).const_mul _
  have hPointwiseStar : ∀ᵐ omega ∂mu,
      FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega ≤
        ∑ i ∈ w.support, w.weight i *
          FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T i) omega := by
    filter_upwards [] with omega
    calc
      FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega =
          ∑ i ∈ w.support, w.weight i *
            FactorialChronologicalGrid.factorialRunningMax
              (fun t omega => |M t omega|) T (level T r) omega := by
        rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
      _ ≤ ∑ i ∈ w.support, w.weight i *
          FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T i) omega := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        · exact (FactorialChronologicalGrid.factorialRunningMax_mono
            (fun t omega => |M t omega|) T)
            (BoundedMartingaleQuadraticApproximation.level_mono T
              (hkr.trans (w.tail i hi))) omega
        · exact w.nonneg i hi
  have hStarIntegralBound :
      (∫ omega, FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
        ∑ i ∈ w.support, w.weight i *
          (∫ omega, FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T i) omega ∂mu) := by
    calc
      (∫ omega, FactorialChronologicalGrid.factorialRunningMax
          (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
          ∫ omega, ∑ i ∈ w.support, w.weight i *
            FactorialChronologicalGrid.factorialRunningMax
              (fun t omega => |M t omega|) T (level T i) omega ∂mu :=
        integral_mono_ae hCoarseStarInt hWeightedStarInt hPointwiseStar
      _ = ∑ i ∈ w.support, w.weight i *
          (∫ omega, FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T i) omega ∂mu) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [integral_const_mul]
        · intro i hi
          exact (factorialGridDavisStar_integrable M T hM i).const_mul _
  have hWeightedRootInt : Integrable (fun omega =>
      ∑ i ∈ w.support, w.weight i * Real.sqrt
        (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
          M T i T omega)) mu := by
    apply integrable_finsetSum w.support
    intro i hi
    exact (factorialGridDavisRoot_integrable M T hM hM0 i).const_mul _
  have hRootIntegralBound :
      ∑ i ∈ w.support, w.weight i *
          (∫ omega, Real.sqrt
            (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i T omega) ∂mu) ≤
        ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) ∂mu := by
    have hPointwiseRoot : ∀ᵐ omega ∂mu, (fun omega =>
        ∑ i ∈ w.support, w.weight i * Real.sqrt
          (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
            M T i T omega)) omega ≤ Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) := by
      filter_upwards [] with omega
      have hCS := Real.sum_sqrt_mul_sqrt_le w.support
        (fun i => w.coeff_nonneg i)
        (fun i => mul_nonneg (w.coeff_nonneg i)
          (BoundedMartingaleQuadraticApproximation.squaredIncrementPart_nonneg
            M T T i omega))
      have hLeft : (∑ i ∈ w.support, Real.sqrt (w.coeff i) *
          Real.sqrt (w.coeff i *
            BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i T omega)) =
          ∑ i ∈ w.support, w.weight i * Real.sqrt
            (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i T omega) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [w.coeff_of_mem hi,
          Real.sqrt_mul (w.nonneg i hi)]
        calc
          Real.sqrt (w.weight i) *
              (Real.sqrt (w.weight i) * Real.sqrt
                (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
                  M T i T omega)) =
              (Real.sqrt (w.weight i)) ^ 2 * Real.sqrt
                (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
                  M T i T omega) := by ring
          _ = w.weight i * Real.sqrt
                (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
                  M T i T omega) := by
            rw [Real.sq_sqrt (w.nonneg i hi)]
      have hRow : (∑ i ∈ w.support, w.coeff i *
          BoundedMartingaleQuadraticApproximation.squaredIncrementPart
            M T i T omega) =
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega := by
        rw [BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply]
        apply Finset.sum_congr rfl
        intro i hi
        rw [w.coeff_of_mem hi]
      rw [← hLeft]
      calc
        (∑ i ∈ w.support, Real.sqrt (w.coeff i) *
            Real.sqrt (w.coeff i *
              BoundedMartingaleQuadraticApproximation.squaredIncrementPart
                M T i T omega)) ≤
            Real.sqrt (∑ i ∈ w.support, w.coeff i) *
              Real.sqrt (∑ i ∈ w.support, w.coeff i *
                BoundedMartingaleQuadraticApproximation.squaredIncrementPart
                  M T i T omega) := hCS
        _ = Real.sqrt
            (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) := by
          rw [w.sum_coeff_eq_one, Real.sqrt_one, one_mul, hRow]
    calc
      ∑ i ∈ w.support, w.weight i *
          (∫ omega, Real.sqrt
            (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i T omega) ∂mu) =
          ∫ omega, ∑ i ∈ w.support, w.weight i * Real.sqrt
            (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i T omega) ∂mu := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [integral_const_mul]
        · intro i hi
          exact (factorialGridDavisRoot_integrable M T hM hM0 i).const_mul _
      _ ≤ ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) ∂mu :=
        integral_mono_ae hWeightedRootInt
          hRowInt
          hPointwiseRoot
  calc
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
        ∑ i ∈ w.support, w.weight i *
          (∫ omega, FactorialChronologicalGrid.factorialRunningMax
            (fun t omega => |M t omega|) T (level T i) omega ∂mu) :=
      hStarIntegralBound
    _ ≤ ∑ i ∈ w.support, w.weight i *
        (6 * ∫ omega, Real.sqrt
          (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
            M T i T omega) ∂mu) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (factorialGridDavis_integral_runningMax_le_six_root
          M T hM hM0 i) (w.nonneg i hi)
    _ = 6 * ∑ i ∈ w.support, w.weight i *
        (∫ omega, Real.sqrt
          (BoundedMartingaleQuadraticApproximation.squaredIncrementPart
            M T i T omega) ∂mu) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 6 * ∫ omega, Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T w T omega) ∂mu :=
      mul_le_mul_of_nonneg_left hRootIntegralBound (by norm_num)

end BoundedMartingaleQuadraticKernel

end FTAPTheorem42
