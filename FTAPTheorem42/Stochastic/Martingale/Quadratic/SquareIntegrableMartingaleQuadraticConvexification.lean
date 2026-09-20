/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Compactness.ForwardConvexUniformIntegrability
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticUniformIntegrability

/-!
# Mass-preserving quadratic convexification for finite-horizon M² martingales

Uniform integrability upgrades the nonnegative Komlós extraction for the
terminal factorial-grid quadratic sums to `L¹` convergence.  Since every
grid has the same centered energy, the limit retains the full mass.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SquareIntegrableMartingaleQuadraticConvexification

open BoundedMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticUniformIntegrability

/-- Each terminal factorial-grid quadratic sum is strongly measurable. -/
theorem squaredIncrementPart_terminal_stronglyMeasurable
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (n : Nat) :
    StronglyMeasurable (squaredIncrementPart M T n T) := by
  let G := grid T n
  let X := deterministicallyStoppedProcess M T
  have hX : Martingale X F mu :=
    martingale_deterministicallyStopped hM hMRight T
  rw [squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum]
  apply discreteSquaredIncrementSum_stronglyMeasurable
  intro k
  exact (hX.stronglyAdapted (G.sampledTime k)).mono
    (F.le (G.sampledTime k))

omit [MeasurableSpace Omega] in
/-- The same forward weights preserve the exact terminal square
decomposition. -/
theorem apply_martingalePart_terminal_eq_square_sub_apply_squaredIncrementPart
    (M : Process Omega) (T : NNReal) (W : ForwardConvexWeights)
    (n : Nat) (omega : Omega) :
    W.apply (fun k => martingalePart M T k T) n omega =
      M T omega ^ 2 - M 0 omega ^ 2 -
        W.apply (fun k => squaredIncrementPart M T k T) n omega := by
  unfold ForwardConvexWeights.apply
  calc
    (∑ i ∈ W.support n,
        W.weight n i * martingalePart M T i T omega) =
        ∑ i ∈ W.support n, W.weight n i *
          (M T omega ^ 2 - M 0 omega ^ 2 -
            squaredIncrementPart M T i T omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hDecomposition :=
        martingalePart_add_squaredIncrementPart M T T i omega
      rw [deterministicallyStoppedProcess_apply, deterministicallyStoppedProcess_apply, min_self,
        show min (0 : NNReal) T = 0 from min_eq_left bot_le] at hDecomposition
      congr 1
      linarith
    _ = ∑ i ∈ W.support n,
        (W.weight n i * (M T omega ^ 2 - M 0 omega ^ 2) -
          W.weight n i * squaredIncrementPart M T i T omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i ∈ W.support n,
          W.weight n i * (M T omega ^ 2 - M 0 omega ^ 2)) -
        ∑ i ∈ W.support n,
          W.weight n i * squaredIncrementPart M T i T omega := by
      rw [Finset.sum_sub_distrib]
    _ = M T omega ^ 2 - M 0 omega ^ 2 -
        ∑ i ∈ W.support n,
          W.weight n i * squaredIncrementPart M T i T omega := by
      rw [← Finset.sum_mul, W.sum_eq_one, one_mul]

/-- Forward convex terminal quadratic sums converge almost everywhere and
in `L¹`, and their limit retains the common centered energy. -/
theorem exists_forwardConvex_terminal_tendstoAE_L1_integral_eq
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    exists W : ForwardConvexWeights, exists A : Omega -> Real,
      TendstoAE mu
        (W.apply (fun n => squaredIncrementPart M T n T)) A /\
      MemLp A 1 mu /\
      (∀ᵐ omega ∂mu, 0 <= A omega) /\
      Tendsto (fun n => eLpNorm
        (W.apply (fun k => squaredIncrementPart M T k T) n - A) 1 mu)
        atTop (nhds 0) /\
      (∫ omega, A omega ∂mu) =
        ∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu /\
      Tendsto (fun n => eLpNorm
        (W.apply (fun k => martingalePart M T k T) n -
          fun omega => M T omega ^ 2 - M 0 omega ^ 2 - A omega)
        1 mu) atTop (nhds 0) := by
  let Q : Nat -> Omega -> Real :=
    fun n => squaredIncrementPart M T n T
  have hQMeas : forall n, StronglyMeasurable (Q n) := by
    intro n
    exact squaredIncrementPart_terminal_stronglyMeasurable
      hM hMRight T n
  have hQNonneg : forall n, ∀ᵐ omega ∂mu, 0 <= Q n omega := by
    intro n
    exact Filter.Eventually.of_forall fun omega =>
      squaredIncrementPart_nonneg M T T n omega
  have hQUI : UniformIntegrable Q 1 mu := by
    exact squaredIncrementPart_terminal_uniformIntegrable
      hM hMRight T hMT
  obtain ⟨W, A, hAE, hAMemLp, hANonneg, hL1⟩ :=
    exists_forwardConvexWeights_tendstoAE_L1_of_uniformIntegrable_nonneg
      hQMeas hQNonneg hQUI
  have hQIntegrable : forall n, Integrable (Q n) mu :=
    fun n => squaredIncrementPart_terminal_integrable
      hM hMRight T hMT n
  let c : Real := ∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu
  have hQIntegral : forall n, (∫ omega, Q n omega ∂mu) = c := by
    intro n
    exact integral_squaredIncrementPart_terminal_eq_centeredVariance
      hM hMRight T hMT n
  have hWIntegral : forall n,
      (∫ omega, W.apply Q n omega ∂mu) = c :=
    fun n => W.integral_apply_eq_of_integral_eq hQIntegrable hQIntegral n
  have hWUI : UniformIntegrable (W.apply Q) 1 mu :=
    W.uniformIntegrable_apply (by norm_num) hQUI
  have hIntegralTendsto : Tendsto
      (fun n => ∫ omega, W.apply Q n omega ∂mu)
      atTop (nhds (∫ omega, A omega ∂mu)) :=
    tendsto_integral_of_L1' A
      (Filter.Eventually.of_forall fun n =>
        memLp_one_iff_integrable.mp (hWUI.memLp n)) hL1
  have hIntegralConst :
      (fun n => ∫ omega, W.apply Q n omega ∂mu) =
        fun _ : Nat => c := by
    funext n
    exact hWIntegral n
  rw [hIntegralConst] at hIntegralTendsto
  have hMass : (∫ omega, A omega ∂mu) = c :=
    tendsto_nhds_unique hIntegralTendsto tendsto_const_nhds
  have hMartingaleDifference (n : Nat) :
      W.apply (fun k => martingalePart M T k T) n -
          (fun omega => M T omega ^ 2 - M 0 omega ^ 2 - A omega) =
        -(W.apply Q n - A) := by
    funext omega
    rw [Pi.sub_apply, Pi.neg_apply, Pi.sub_apply]
    rw [apply_martingalePart_terminal_eq_square_sub_apply_squaredIncrementPart]
    dsimp only [Q]
    ring
  have hMartingaleL1 : Tendsto (fun n => eLpNorm
      (W.apply (fun k => martingalePart M T k T) n -
        fun omega => M T omega ^ 2 - M 0 omega ^ 2 - A omega)
      1 mu) atTop (nhds 0) := by
    have hNormEq : (fun n => eLpNorm
        (W.apply (fun k => martingalePart M T k T) n -
          fun omega => M T omega ^ 2 - M 0 omega ^ 2 - A omega)
        1 mu) = fun n => eLpNorm (W.apply Q n - A) 1 mu := by
      funext n
      rw [hMartingaleDifference n, eLpNorm_neg]
    rw [hNormEq]
    exact hL1
  exact ⟨W, A, hAE, hAMemLp, hANonneg, hL1, hMass, hMartingaleL1⟩

end SquareIntegrableMartingaleQuadraticConvexification

end FTAPTheorem42
