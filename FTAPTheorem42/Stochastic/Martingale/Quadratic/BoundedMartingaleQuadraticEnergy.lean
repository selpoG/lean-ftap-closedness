/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernel
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleControl
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridPredictableElementaryStrategy
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleEnergyContent
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepApproximation
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepMartingaleApproximation

/-!
# Energy identities for bounded-martingale quadratic variation

The increasing process constructed from forward-convex squared increments
has the correct martingale energy on each deterministic predictable
interval.  This module proves the weighted interval identity that connects
its Stieltjes measure to finite-grid stochastic-integral isometries.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy

/-- An integrable coefficient known at the left endpoint is orthogonal in
expectation to the following martingale increment. -/
theorem integral_mul_increment_eq_zero
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Z : Process Omega} (hZ : Martingale Z F mu)
    {a b : NNReal} (hab : a <= b) {K : Omega -> Real}
    (hK : StronglyMeasurable[F a] K)
    (hProduct : Integrable (fun omega =>
      K omega * (Z b omega - Z a omega)) mu) :
    (∫ omega, K omega * (Z b omega - Z a omega) ∂mu) = 0 := by
  let increment : Omega -> Real := fun omega => Z b omega - Z a omega
  have hIncrement : Integrable increment mu :=
    (hZ.integrable b).sub (hZ.integrable a)
  have hCondIncrement : mu[increment | F a] =ᵐ[mu] 0 := by
    filter_upwards [
      condExp_sub (hZ.integrable b) (hZ.integrable a) (F a),
      hZ.condExp_ae_eq hab,
      hZ.condExp_ae_eq (le_refl a)] with omega hsub hb ha
    change mu[Z b - Z a | F a] omega = 0
    rw [hsub]
    change mu[Z b | F a] omega - mu[Z a | F a] omega = 0
    rw [hb, ha, sub_self]
  have hPull : mu[K * increment | F a] =ᵐ[mu]
      K * mu[increment | F a] :=
    condExp_mul_of_stronglyMeasurable_left
      hK hProduct hIncrement
  calc
    (∫ omega, K omega * (Z b omega - Z a omega) ∂mu) =
        ∫ omega, mu[K * increment | F a] omega ∂mu :=
      (integral_condExp (F.le a)).symm
    _ = ∫ _omega, (0 : Real) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hPull, hCondIncrement] with omega hpull hzero
      rw [hpull]
      change K omega * mu[increment | F a] omega = 0
      rw [hzero]
      simp
    _ = 0 := by simp

omit [MeasurableSpace Omega] in
/-- Squaring a finite chronological left-step process gives the sum of the
squares of its disjoint interval blocks. -/
theorem enorm_sq_predictableStepProcess_eq_sum
    {N : Nat} (G : ChronologicalGrid NNReal N) (K : Process Omega)
    (t : NNReal) (omega : Omega) :
    ‖G.predictableStepProcess K t omega‖ₑ ^ 2 =
      ∑ k ∈ Finset.range N,
        ‖ChronologicalGrid.deterministicIntervalCoefficient K
          (G.sampledTime k) (G.sampledTime (k + 1)) t omega‖ₑ ^ 2 := by
  by_cases hActive : ∃ k ∈ Finset.range N,
      t ∈ Ioc (G.sampledTime k) (G.sampledTime (k + 1))
  · obtain ⟨k, hk, ht⟩ := hActive
    rw [congrFun
      (FTAPTheorem42.ChronologicalGrid.predictableStepProcess_eq_of_mem_Ioc
        G K
      (Finset.mem_range.mp hk) ht) omega]
    rw [Finset.sum_eq_single k]
    · simp [ChronologicalGrid.deterministicIntervalCoefficient, ht]
    · intro j hj hjne
      have hnot : t ∉
          Ioc (G.sampledTime j) (G.sampledTime (j + 1)) := by
        intro hmem
        rcases lt_or_gt_of_ne hjne with hjk | hkj
        · have hEndLe : G.sampledTime (j + 1) ≤ G.sampledTime k :=
            G.sampledTime_mono (Nat.succ_le_of_lt hjk)
          exact (not_le_of_gt (hEndLe.trans_lt ht.1)) hmem.2
        · have hStartGe : G.sampledTime (k + 1) ≤ G.sampledTime j :=
            G.sampledTime_mono (Nat.succ_le_of_lt hkj)
          exact (not_lt_of_ge (ht.2.trans hStartGe)) hmem.1
      simp [ChronologicalGrid.deterministicIntervalCoefficient, hnot]
    · simp [hk]
  · have hnot (k : Nat) (hk : k ∈ Finset.range N) :
        t ∉ Ioc (G.sampledTime k) (G.sampledTime (k + 1)) := by
      exact fun ht => hActive ⟨k, hk, ht⟩
    have hStep : G.predictableStepProcess K t omega = 0 := by
      unfold ChronologicalGrid.predictableStepProcess
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      simp [ChronologicalGrid.deterministicIntervalCoefficient, hnot k hk]
    rw [hStep]
    have hZero : ‖(0 : Real)‖ₑ ^ 2 = 0 := by norm_num
    rw [hZero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    simp [ChronologicalGrid.deterministicIntervalCoefficient, hnot k hk]

namespace Data

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticKernel

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Process Omega} {T : NNReal}

omit [IsProbabilityMeasure mu] in
/-- Every value of the increasing quadratic variation is integrable. -/
theorem variation_integrable
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (t : NNReal) : Integrable (D.variation t) mu := by
  apply D.variation_terminal_integrable.mono'
    (D.variation_measurable t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun omega => by
    have hZero : 0 <= D.variation t omega := by
      calc
        0 = D.variation 0 omega :=
          (congrFun D.variation_zero omega).symm
        _ <= D.variation t omega :=
          D.variation_monotone omega bot_le
    simp only [Real.norm_eq_abs, abs_of_nonneg hZero]
    by_cases ht : t <= T
    · exact D.variation_monotone omega ht
    · rw [D.variation_constantAfter omega t (le_of_not_ge ht)]

/-- The Stieltjes increment of the quadratic-variation candidate has the
same weighted expectation as the squared martingale increment. -/
theorem integral_sq_mul_variation_increment_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    {a b : NNReal} (hab : a <= b)
    {K : Omega -> Real} (hK : StronglyMeasurable[F a] K)
    {C : Real} (hC : 0 <= C)
    (hKBound : ∀ᵐ omega ∂mu, |K omega| <= C) :
    (∫ omega, K omega ^ 2 *
        (D.variation b omega - D.variation a omega) ∂mu) =
      ∫ omega, (K omega *
        (deterministicallyStoppedProcess M T b omega
          - deterministicallyStoppedProcess M T a omega)) ^ 2
          ∂mu := by
  let X := deterministicallyStoppedProcess M T
  have hX : Martingale X F mu := martingale_deterministicallyStopped hM hMRight T
  have hXa : MemLp (X a) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT a
  have hXb : MemLp (X b) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT b
  have hXIncrement : MemLp (X b - X a) (2 : ENNReal) mu := hXb.sub hXa
  have hKMeas : StronglyMeasurable K := hK.mono (F.le a)
  have hKSqMeasF : StronglyMeasurable[F a]
      (fun omega => K omega ^ 2) :=
    hK.pow 2
  have hKSqMeas : StronglyMeasurable (fun omega => K omega ^ 2) :=
    hKSqMeasF.mono (F.le a)
  have hKSqBound : ∀ᵐ omega ∂mu, ‖K omega ^ 2‖ <= C ^ 2 := by
    filter_upwards [hKBound] with omega hBound
    rw [Real.norm_eq_abs, abs_sq]
    exact sq_le_sq.mpr (by
      simpa only [abs_of_nonneg hC] using hBound)
  have hWeightedIncrement : MemLp
      (fun omega => K omega * (X b omega - X a omega))
      (2 : ENNReal) mu := by
    apply MemLp.of_le_mul (c := C) hXIncrement
      (hKMeas.mul
        (((hX.stronglyMeasurable b).mono (F.le b)).sub
          ((hX.stronglyMeasurable a).mono (F.le a)))).aestronglyMeasurable
    filter_upwards [hKBound] with omega hBound
    change |K omega * (X b omega - X a omega)| <=
      C * ‖X b omega - X a omega‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hBound (abs_nonneg _)
  have hWeightedSqInt : Integrable (fun omega =>
      (K omega * (X b omega - X a omega)) ^ 2) mu :=
    hWeightedIncrement.integrable_sq
  have hVariationDiffInt : Integrable
      (D.variation b - D.variation a) mu :=
    (variation_integrable D b).sub (variation_integrable D a)
  have hWeightedVariationInt : Integrable (fun omega =>
      K omega ^ 2 * (D.variation b omega - D.variation a omega)) mu :=
    hVariationDiffInt.bdd_mul hKSqMeas.aestronglyMeasurable hKSqBound
  have hYIncrementInt : Integrable
      (D.martingalePart b - D.martingalePart a) mu :=
    (D.martingalePart_isMartingale.integrable b).sub
      (D.martingalePart_isMartingale.integrable a)
  have hWeightedYInt : Integrable (fun omega =>
      K omega ^ 2 *
        (D.martingalePart b omega - D.martingalePart a omega)) mu :=
    hYIncrementInt.bdd_mul hKSqMeas.aestronglyMeasurable hKSqBound
  have hBaseCrossInt : Integrable
      ((X a) * (X b - X a)) mu :=
    hXa.integrable_mul hXIncrement
  have hWeightedCrossInt : Integrable (fun omega =>
      (K omega ^ 2 * X a omega) *
        (X b omega - X a omega)) mu := by
    have h := hBaseCrossInt.bdd_mul
      hKSqMeas.aestronglyMeasurable hKSqBound
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc] using h
  have hCrossZero : (∫ omega,
      (K omega ^ 2 * X a omega) *
        (X b omega - X a omega) ∂mu) = 0 := by
    apply integral_mul_increment_eq_zero hX hab
      (hKSqMeasF.mul (hX.stronglyMeasurable a))
    exact hWeightedCrossInt
  have hYZero : (∫ omega, K omega ^ 2 *
      (D.martingalePart b omega - D.martingalePart a omega) ∂mu) = 0 := by
    apply integral_mul_increment_eq_zero
      D.martingalePart_isMartingale hab hKSqMeasF
    exact hWeightedYInt
  have hRawEq := ae_iff.mp D.variation_indistinguishable_raw
  have hPointwise : ∀ᵐ omega ∂mu,
      K omega ^ 2 * (D.variation b omega - D.variation a omega) =
        (K omega * (X b omega - X a omega)) ^ 2 +
          2 * ((K omega ^ 2 * X a omega) *
            (X b omega - X a omega)) -
          K omega ^ 2 *
            (D.martingalePart b omega - D.martingalePart a omega) := by
    filter_upwards [hRawEq] with omega hEq
    rw [hEq b, hEq a]
    simp only [BoundedMartingaleQuadraticKernel.rawVariation_apply, X]
    ring
  calc
    (∫ omega, K omega ^ 2 *
        (D.variation b omega - D.variation a omega) ∂mu) =
        ∫ omega,
          (K omega * (X b omega - X a omega)) ^ 2 +
            2 * ((K omega ^ 2 * X a omega) *
              (X b omega - X a omega)) -
            K omega ^ 2 *
              (D.martingalePart b omega - D.martingalePart a omega) ∂mu :=
      integral_congr_ae hPointwise
    _ = (∫ omega, (K omega * (X b omega - X a omega)) ^ 2 ∂mu) +
          2 * (∫ omega, (K omega ^ 2 * X a omega) *
            (X b omega - X a omega) ∂mu) -
          ∫ omega, K omega ^ 2 *
            (D.martingalePart b omega - D.martingalePart a omega) ∂mu := by
      have hSub := integral_sub
        (hWeightedSqInt.add (hWeightedCrossInt.const_mul 2))
        hWeightedYInt
      have hAdd := integral_add hWeightedSqInt
        (hWeightedCrossInt.const_mul 2)
      have hMul := integral_const_mul (μ := mu) 2
        (fun omega => (K omega ^ 2 * X a omega) *
          (X b omega - X a omega))
      rw [show (∫ omega,
          (K omega * (X b omega - X a omega)) ^ 2 +
            2 * ((K omega ^ 2 * X a omega) *
              (X b omega - X a omega)) -
            K omega ^ 2 *
              (D.martingalePart b omega - D.martingalePart a omega) ∂mu) =
          (∫ omega,
            (K omega * (X b omega - X a omega)) ^ 2 +
              2 * ((K omega ^ 2 * X a omega) *
                (X b omega - X a omega)) ∂mu) -
            ∫ omega, K omega ^ 2 *
              (D.martingalePart b omega - D.martingalePart a omega) ∂mu by
        simpa only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using hSub]
      rw [show (∫ omega,
          (K omega * (X b omega - X a omega)) ^ 2 +
            2 * ((K omega ^ 2 * X a omega) *
              (X b omega - X a omega)) ∂mu) =
          (∫ omega, (K omega * (X b omega - X a omega)) ^ 2 ∂mu) +
            ∫ omega, 2 * ((K omega ^ 2 * X a omega) *
              (X b omega - X a omega)) ∂mu by
        simpa only [Pi.add_apply, Pi.mul_apply] using hAdd]
      rw [show (∫ omega, 2 * ((K omega ^ 2 * X a omega) *
          (X b omega - X a omega)) ∂mu) =
          2 * (∫ omega, (K omega ^ 2 * X a omega) *
            (X b omega - X a omega) ∂mu) by
        simpa only [Pi.mul_apply] using hMul]
    _ = ∫ omega, (K omega * (X b omega - X a omega)) ^ 2 ∂mu := by
      rw [hCrossZero, hYZero]
      ring

/-- On one deterministic predictable interval, the Stieltjes quadratic
measure gives exactly the squared terminal energy of the corresponding
bounded martingale increment. -/
theorem lintegral_deterministicIntervalCoefficient_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    {a b : NNReal} (hab : a <= b)
    (K : Process Omega) (hK : IsStronglyPredictable F K)
    {C : Real} (hC : 0 <= C)
    (hKBound : ∀ᵐ omega ∂mu, |K a omega| <= C) :
    (∫⁻ p, ‖Function.uncurry
        (ChronologicalGrid.deterministicIntervalCoefficient K a b) p‖ₑ ^ 2
      ∂D.predictableEnergyMeasure) =
      ∫⁻ omega, ‖K a omega *
        (deterministicallyStoppedProcess M T b omega
          - deterministicallyStoppedProcess M T a omega)‖ₑ ^ 2
          ∂mu := by
  let coefficient : Process Omega :=
    ChronologicalGrid.deterministicIntervalCoefficient K a b
  have hCoefficient : IsStronglyPredictable F coefficient :=
    ChronologicalGrid.deterministicIntervalCoefficient_isStronglyPredictable
      hK a b
  have hIntegrand : Measurable[F.predictable]
      (fun p => ‖Function.uncurry coefficient p‖ₑ ^ 2) :=
    hCoefficient.enorm.pow_const 2
  let : IsSFiniteKernel D.stieltjesKernel :=
    IncreasingProcessStieltjesKernel.kernel_isSFinite D.variation
      D.variation_monotone D.variation_rightContinuous T
      D.variation_constantAfter D.variation_measurable
  have hIterated :
      (∫⁻ p, ‖Function.uncurry coefficient p‖ₑ ^ 2
          ∂D.predictableEnergyMeasure) =
        ∫⁻ omega, ∫⁻ t, ‖coefficient t omega‖ₑ ^ 2
          ∂D.stieltjesKernel omega ∂mu := by
    change (∫⁻ p, ‖Function.uncurry coefficient p‖ₑ ^ 2
        ∂PredictableKernelMeasure.predictableMeasure F mu
          D.stieltjesKernel) = _
    exact PredictableKernelMeasure.lintegral_predictableMeasure_eq_lintegral_kernel
      (κ := D.stieltjesKernel) hIntegrand
  have hInner (omega : Omega) :
      (∫⁻ t, ‖coefficient t omega‖ₑ ^ 2
          ∂D.stieltjesKernel omega) =
        ENNReal.ofReal (K a omega ^ 2 *
          (D.variation b omega - D.variation a omega)) := by
    have hFunction : (fun t => ‖coefficient t omega‖ₑ ^ 2) =
        (Ioc a b).indicator (fun _ => ‖K a omega‖ₑ ^ 2) := by
      funext t
      by_cases ht : t ∈ Ioc a b <;>
        simp [coefficient,
          ChronologicalGrid.deterministicIntervalCoefficient, ht]
    rw [D.stieltjesKernel_apply, hFunction,
      lintegral_indicator measurableSet_Ioc, setLIntegral_const,
      IncreasingProcessStieltjesKernel.pathMeasure_Ioc]
    have hVariationNonnegative :
        0 <= D.variation b omega - D.variation a omega :=
      sub_nonneg.mpr (D.variation_monotone omega hab)
    have hNormSq : ‖K a omega‖ ^ 2 = K a omega ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg (K a omega)),
      hNormSq,
      ← ENNReal.ofReal_mul (sq_nonneg (K a omega))]
  have hVariationDiffInt : Integrable
      (D.variation b - D.variation a) mu :=
    (variation_integrable D b).sub (variation_integrable D a)
  have hKSqMeas : StronglyMeasurable (fun omega => K a omega ^ 2) :=
    (hK.stronglyAdapted a).pow 2 |>.mono (F.le a)
  have hKSqBound : ∀ᵐ omega ∂mu, ‖K a omega ^ 2‖ <= C ^ 2 := by
    filter_upwards [hKBound] with omega hBound
    rw [Real.norm_eq_abs, abs_sq]
    exact sq_le_sq.mpr (by
      simpa only [abs_of_nonneg hC] using hBound)
  have hLeftInt : Integrable (fun omega => K a omega ^ 2 *
      (D.variation b omega - D.variation a omega)) mu :=
    hVariationDiffInt.bdd_mul
      hKSqMeas.aestronglyMeasurable hKSqBound
  have hXb : MemLp (deterministicallyStoppedProcess M T b) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT b
  have hXa : MemLp (deterministicallyStoppedProcess M T a) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT a
  have hIncrement : MemLp
      (deterministicallyStoppedProcess M T b - deterministicallyStoppedProcess M T a)
      (2 : ENNReal) mu := hXb.sub hXa
  have hWeightedIncrement : MemLp (fun omega =>
      K a omega * (deterministicallyStoppedProcess M T b omega -
        deterministicallyStoppedProcess M T a omega)) (2 : ENNReal) mu := by
    apply MemLp.of_le_mul (c := C) hIncrement
      (((hK.stronglyAdapted a).mono (F.le a)).mul
        (((martingale_deterministicallyStopped hM hMRight T).stronglyMeasurable b).mono
          (F.le b) |>.sub
          (((martingale_deterministicallyStopped hM hMRight T).stronglyMeasurable a).mono
            (F.le a)))).aestronglyMeasurable
    filter_upwards [hKBound] with omega hBound
    change |K a omega * (deterministicallyStoppedProcess M T b omega -
      deterministicallyStoppedProcess M T a omega)| <=
      C * ‖deterministicallyStoppedProcess M T b omega
        - deterministicallyStoppedProcess M T a omega‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hBound (abs_nonneg _)
  have hRightInt : Integrable (fun omega =>
      (K a omega * (deterministicallyStoppedProcess M T b omega -
        deterministicallyStoppedProcess M T a omega)) ^ 2) mu :=
    hWeightedIncrement.integrable_sq
  have hLeftNonnegative : ∀ᵐ omega ∂mu,
      0 <= K a omega ^ 2 *
        (D.variation b omega - D.variation a omega) :=
    Filter.Eventually.of_forall fun omega => mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (D.variation_monotone omega hab))
  have hRightNonnegative : ∀ᵐ omega ∂mu,
      0 <= (K a omega * (deterministicallyStoppedProcess M T b omega -
        deterministicallyStoppedProcess M T a omega)) ^ 2 :=
    Filter.Eventually.of_forall fun omega => sq_nonneg _
  have hReal := integral_sq_mul_variation_increment_eq D
    hM hMRight hMT hab (hK.stronglyAdapted a) hC hKBound
  rw [hIterated]
  simp_rw [hInner]
  calc
    (∫⁻ omega, ENNReal.ofReal (K a omega ^ 2 *
        (D.variation b omega - D.variation a omega)) ∂mu) =
        ENNReal.ofReal (∫ omega, K a omega ^ 2 *
          (D.variation b omega - D.variation a omega) ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal hLeftInt hLeftNonnegative).symm
    _ = ENNReal.ofReal (∫ omega,
        (K a omega * (deterministicallyStoppedProcess M T b omega -
          deterministicallyStoppedProcess M T a omega)) ^ 2 ∂mu) := by
      rw [hReal]
    _ = ∫⁻ omega, ENNReal.ofReal
        ((K a omega * (deterministicallyStoppedProcess M T b omega -
          deterministicallyStoppedProcess M T a omega)) ^ 2) ∂mu :=
      ofReal_integral_eq_lintegral_ofReal hRightInt hRightNonnegative
    _ = ∫⁻ omega, ‖K a omega * (deterministicallyStoppedProcess M T b omega -
        deterministicallyStoppedProcess M T a omega)‖ₑ ^ 2 ∂mu := by
      apply lintegral_congr
      intro omega
      rw [← sq_abs, ← Real.norm_eq_abs, ← ofReal_norm,
        ENNReal.ofReal_pow (norm_nonneg _)]

/-- The quadratic Stieltjes measure gives the exact terminal energy of any
bounded predictable left-step integral on a finite chronological grid. -/
theorem lintegral_predictableStepProcess_eq_terminal
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K : Process Omega) (hK : IsStronglyPredictable F K)
    {C : NNReal → Real}
    (hKBound : forall t, ∀ᵐ omega ∂mu, |K t omega| <= C t) :
    (∫⁻ p, ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^ 2
        ∂D.predictableEnergyMeasure) =
      ∫⁻ omega, ‖discretePredictableIntegral
        (G.natSample K) (G.natSample (deterministicallyStoppedProcess M T)) N omega‖ₑ ^ 2
          ∂mu := by
  let X := deterministicallyStoppedProcess M T
  have hX : Martingale X F mu := martingale_deterministicallyStopped hM hMRight T
  have hXLp : forall n, MemLp (G.natSample X n) (2 : ENNReal) mu := by
    intro n
    exact stoppedProcess_const_memLp_two hM T hMT (G.sampledTime n)
  have hKSampleBound : forall n, ∀ᵐ omega ∂mu,
      |G.natSample K n omega| <= C (G.sampledTime n) := by
    intro n
    exact hKBound (G.sampledTime n)
  have hSum :
      (∫⁻ p, ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^ 2
          ∂D.predictableEnergyMeasure) =
        ∑ k ∈ Finset.range N,
          ∫⁻ omega, ‖K (G.sampledTime k) omega *
            (X (G.sampledTime (k + 1)) omega -
              X (G.sampledTime k) omega)‖ₑ ^ 2 ∂mu := by
    rw [show (fun p : NNReal × Omega =>
        ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^ 2) =
        fun p => ∑ k ∈ Finset.range N,
          ‖ChronologicalGrid.deterministicIntervalCoefficient K
            (G.sampledTime k) (G.sampledTime (k + 1)) p.1 p.2‖ₑ ^ 2 by
      funext p
      exact enorm_sq_predictableStepProcess_eq_sum G K p.1 p.2]
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      apply lintegral_deterministicIntervalCoefficient_eq D
        hM hMRight hMT (G.sampledTime_mono (Nat.le_succ k)) K hK
        (abs_nonneg (C (G.sampledTime k)))
      filter_upwards [hKBound (G.sampledTime k)] with omega hBound
      exact hBound.trans (le_abs_self (C (G.sampledTime k)))
    · intro k _hk
      exact
        (ChronologicalGrid.deterministicIntervalCoefficient_isStronglyPredictable
          hK (G.sampledTime k) (G.sampledTime (k + 1))).enorm.pow_const 2
  calc
    (∫⁻ p, ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^ 2
        ∂D.predictableEnergyMeasure) =
        ∑ k ∈ Finset.range N,
          ∫⁻ omega, ‖K (G.sampledTime k) omega *
            (X (G.sampledTime (k + 1)) omega -
              X (G.sampledTime k) omega)‖ₑ ^ 2 ∂mu := hSum
    _ = ∫⁻ omega, ‖discretePredictableIntegral
        (G.natSample K) (G.natSample X) N omega‖ₑ ^ 2 ∂mu := by
      symm
      simpa only [ChronologicalGrid.natSample] using
        DiscretePredictableIntegral.lintegral_enorm_sq_eq_sum
          (ChronologicalGrid.Martingale.natSample (G := G) hX)
          hXLp (G.stronglyAdapted_natSample hK.stronglyAdapted)
          hKSampleBound N

/-- `L²`-seminorm form of the finite chronological left-step isometry. -/
theorem eLpNorm_predictableStepProcess_eq_terminal
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K : Process Omega) (hK : IsStronglyPredictable F K)
    {C : NNReal → Real}
    (hKBound : forall t, ∀ᵐ omega ∂mu, |K t omega| <= C t) :
    eLpNorm (Function.uncurry (G.predictableStepProcess K))
        (2 : ENNReal) D.predictableEnergyMeasure =
      eLpNorm (discretePredictableIntegral
        (G.natSample K) (G.natSample (deterministicallyStoppedProcess M T)) N)
          (2 : ENNReal) mu := by
  have hStep : IsStronglyPredictable F (G.predictableStepProcess K) := by
    rw [← G.predictableElementaryStrategy_integrand K hK]
    exact (G.predictableElementaryStrategy K hK).integrand_isStronglyPredictable
  have hIntegral := DiscretePredictableIntegral.memLp_two
    (ChronologicalGrid.Martingale.natSample (G := G)
      (martingale_deterministicallyStopped hM hMRight T))
    (fun n => stoppedProcess_const_memLp_two hM T hMT (G.sampledTime n))
    (G.stronglyAdapted_natSample hK.stronglyAdapted)
    (fun n => hKBound (G.sampledTime n)) N
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hStep.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hIntegral.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  have hEnergy := lintegral_predictableStepProcess_eq_terminal
    D hM hMRight hMT G K hK hKBound
  have hLeftPow :
      (fun p : NNReal × Omega =>
        ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^ (2 : Real)) =
        fun p => ‖Function.uncurry (G.predictableStepProcess K) p‖ₑ ^
          (2 : Nat) := by
    funext p
    exact ENNReal.rpow_natCast _ 2
  have hRightPow :
      (fun omega => ‖discretePredictableIntegral
        (G.natSample K) (G.natSample (deterministicallyStoppedProcess M T)) N omega‖ₑ ^
          (2 : Real)) =
        fun omega => ‖discretePredictableIntegral
          (G.natSample K) (G.natSample (deterministicallyStoppedProcess M T)) N omega‖ₑ ^
            (2 : Nat) := by
    funext omega
    exact ENNReal.rpow_natCast _ 2
  rw [hLeftPow, hRightPow, hEnergy]

/-- Under the quadratic Stieltjes measure, horizon-covering chronological
left steps converge in `L²` to the original bounded elementary integrand. -/
theorem tendsto_eLpNorm_two_horizonLeftStepStrategy_integrand_sub
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hCoefficient : forall omega, H.coefficientAbsSum omega <= C) :
    Tendsto (fun r => eLpNorm
      (Function.uncurry (H.horizonLeftStepStrategy r T).integrand -
        Function.uncurry H.integrand) (2 : ENNReal)
          D.predictableEnergyMeasure) atTop (nhds 0) := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure :=
    D.predictableEnergyMeasure_isFinite
  let approximant : Nat → NNReal × Omega → Real := fun r =>
    Function.uncurry (H.horizonLeftStepStrategy r T).integrand
  let target : NNReal × Omega → Real := Function.uncurry H.integrand
  let bound : NNReal × Omega → Real := fun _ => 2 * (C : Real)
  have hSupport : ∀ᵐ p ∂D.predictableEnergyMeasure, p.1 <= T :=
    D.ae_time_le_horizon
  have hApproximantMeas : forall r,
      AEStronglyMeasurable[F.predictable] (approximant r)
        D.predictableEnergyMeasure := by
    intro r
    exact (H.horizonLeftStepStrategy r T).integrand_isStronglyPredictable
      |>.aestronglyMeasurable
  have hTargetMeas : AEStronglyMeasurable[F.predictable] target
      D.predictableEnergyMeasure :=
    H.integrand_isStronglyPredictable.aestronglyMeasurable
  have hBoundMem : MemLp bound (2 : ENNReal)
      D.predictableEnergyMeasure :=
    memLp_const (μ := D.predictableEnergyMeasure)
      (p := (2 : ENNReal)) (2 * (C : Real))
  have hBound : forall r, ∀ᵐ p ∂D.predictableEnergyMeasure,
      ‖approximant r p - target p‖ <= ‖bound p‖ := by
    intro r
    filter_upwards [hSupport] with p hp
    have hApprox : |approximant r p| <= (C : Real) := by
      rw [show approximant r p =
          LeftContinuousPredictable.step r H.integrand p.1 p.2 by
        exact congrFun (H.horizonLeftStepStrategy_integrand_eq r T hp) p.2]
      exact (H.abs_integrand_le_coefficientAbsSum
        (LeftContinuousPredictable.approx r p.1) p.2).trans
          (by exact_mod_cast hCoefficient p.2)
    have hTarget : |target p| <= (C : Real) :=
      (H.abs_integrand_le_coefficientAbsSum p.1 p.2).trans
        (by exact_mod_cast hCoefficient p.2)
    simp only [Real.norm_eq_abs]
    calc
      |approximant r p - target p| <=
          |approximant r p| + |target p| := abs_sub _ _
      _ <= (C : Real) + C := add_le_add hApprox hTarget
      _ = |bound p| := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg C))]
        ring
  have hTendsto : ∀ᵐ p ∂D.predictableEnergyMeasure,
      Tendsto (fun r => approximant r p) atTop (nhds (target p)) := by
    filter_upwards [hSupport] with p hp
    apply (H.tendsto_leftStep_integrand p.1 p.2).congr'
    exact Filter.Eventually.of_forall fun r => by
      exact (congrFun
        (H.horizonLeftStepStrategy_integrand_eq r T hp) p.2).symm
  exact tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    hApproximantMeas hTargetMeas hBoundMem hBound hTendsto

/-- The grid-independent quadratic Stieltjes measure has exactly the
terminal `L²` seminorm of every bounded predictable elementary martingale
integral. -/
theorem eLpNorm_predictableEnergyMeasure_eq_gain
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hCoefficient : forall omega, H.coefficientAbsSum omega <= C) :
    eLpNorm (Function.uncurry H.integrand) (2 : ENNReal)
        D.predictableEnergyMeasure =
      eLpNorm (ElementaryStrategy.gain M H.toElementary T)
        (2 : ENNReal) mu := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure :=
    D.predictableEnergyMeasure_isFinite
  let approximantIntegrand : Nat → NNReal × Omega → Real := fun r =>
    Function.uncurry (H.horizonLeftStepStrategy r T).integrand
  let targetIntegrand : NNReal × Omega → Real :=
    Function.uncurry H.integrand
  let approximantGain : Nat → Omega → Real := fun r =>
    ElementaryStrategy.gain M
      (H.horizonLeftStepStrategy r T).toElementary T
  let targetGain : Omega → Real :=
    ElementaryStrategy.gain M H.toElementary T
  have hSupport : ∀ᵐ p ∂D.predictableEnergyMeasure, p.1 <= T :=
    D.ae_time_le_horizon
  have hApproximantIntegrandMeas : forall r,
      AEStronglyMeasurable[F.predictable] (approximantIntegrand r)
        D.predictableEnergyMeasure := by
    intro r
    exact (H.horizonLeftStepStrategy r T).integrand_isStronglyPredictable
      |>.aestronglyMeasurable
  have hTargetIntegrandMeas :
      AEStronglyMeasurable[F.predictable] targetIntegrand
        D.predictableEnergyMeasure :=
    H.integrand_isStronglyPredictable.aestronglyMeasurable
  have hApproximantIntegrandBound : forall r,
      ∀ᵐ p ∂D.predictableEnergyMeasure,
        ‖approximantIntegrand r p‖ <= (C : Real) := by
    intro r
    filter_upwards [hSupport] with p hp
    rw [Real.norm_eq_abs, show approximantIntegrand r p =
        LeftContinuousPredictable.step r H.integrand p.1 p.2 by
      exact congrFun (H.horizonLeftStepStrategy_integrand_eq r T hp) p.2]
    exact (H.abs_integrand_le_coefficientAbsSum
      (LeftContinuousPredictable.approx r p.1) p.2).trans
        (by exact_mod_cast hCoefficient p.2)
  have hTargetIntegrandBound : ∀ᵐ p ∂D.predictableEnergyMeasure,
      ‖targetIntegrand p‖ <= (C : Real) :=
    Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact (H.abs_integrand_le_coefficientAbsSum p.1 p.2).trans
        (by exact_mod_cast hCoefficient p.2)
  have hApproximantIntegrandMem : forall r,
      MemLp (approximantIntegrand r) (2 : ENNReal)
        D.predictableEnergyMeasure := fun r =>
    MemLp.of_bound (hApproximantIntegrandMeas r) (C : Real)
      (hApproximantIntegrandBound r)
  have hTargetIntegrandMem : MemLp targetIntegrand (2 : ENNReal)
      D.predictableEnergyMeasure :=
    MemLp.of_bound hTargetIntegrandMeas (C : Real) hTargetIntegrandBound
  have hIntegrandRaw : Tendsto (fun r => eLpNorm
      (approximantIntegrand r - targetIntegrand) (2 : ENNReal)
        D.predictableEnergyMeasure) atTop (nhds 0) := by
    simpa only [approximantIntegrand, targetIntegrand] using
      tendsto_eLpNorm_two_horizonLeftStepStrategy_integrand_sub
        D H C hCoefficient
  have hIntegrandLp : Tendsto
      (fun r => (hApproximantIntegrandMem r).toLp
        (approximantIntegrand r)) atTop
      (nhds (hTargetIntegrandMem.toLp targetIntegrand)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' approximantIntegrand
      hApproximantIntegrandMem targetIntegrand hTargetIntegrandMem).mpr
        hIntegrandRaw
  have hIntegrandNorm : Tendsto
      (fun r => (eLpNorm (approximantIntegrand r) (2 : ENNReal)
        D.predictableEnergyMeasure).toReal) atTop
      (nhds ((eLpNorm targetIntegrand (2 : ENNReal)
        D.predictableEnergyMeasure).toReal)) := by
    simpa only [Lp.norm_toLp] using hIntegrandLp.norm
  have hApproximantGainMem : forall r,
      MemLp (approximantGain r) (2 : ENNReal) mu := by
    intro r
    let Cr : NNReal :=
      (LeftContinuousPredictable.horizonCellCount r T : NNReal) * C
    apply (H.horizonLeftStepStrategy r T).gain_memLp_two
      M hM hMRight T hMT Cr
    intro omega
    have hBound := H.horizonLeftStepStrategy_coefficientAbsSum_le
      r T C hCoefficient omega
    simpa only [Cr, NNReal.coe_mul, NNReal.coe_natCast] using hBound
  have hTargetGainMem : MemLp targetGain (2 : ENNReal) mu := by
    exact H.gain_memLp_two M hM hMRight T hMT C hCoefficient
  have hGainRaw : Tendsto (fun r => eLpNorm
      (approximantGain r - targetGain) (2 : ENNReal) mu)
      atTop (nhds 0) := by
    simpa only [approximantGain, targetGain] using
      H.horizonLeftStepStrategy_gain_tendsto_eLpNorm_two
        M hM hMRight T hMT C hCoefficient
  have hGainLp : Tendsto
      (fun r => (hApproximantGainMem r).toLp (approximantGain r)) atTop
      (nhds (hTargetGainMem.toLp targetGain)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' approximantGain
      hApproximantGainMem targetGain hTargetGainMem).mpr hGainRaw
  have hGainNorm : Tendsto
      (fun r => (eLpNorm (approximantGain r) (2 : ENNReal) mu).toReal)
      atTop (nhds ((eLpNorm targetGain (2 : ENNReal) mu).toReal)) := by
    simpa only [Lp.norm_toLp] using hGainLp.norm
  have hApproximationIsometry (r : Nat) :
      eLpNorm (approximantIntegrand r) (2 : ENNReal)
          D.predictableEnergyMeasure =
        eLpNorm (approximantGain r) (2 : ENNReal) mu := by
    let N := LeftContinuousPredictable.horizonCellCount r T
    let G : ChronologicalGrid NNReal N :=
      LeftContinuousPredictable.finiteGrid r N
    have hBound : forall t, ∀ᵐ omega ∂mu,
        |H.integrand t omega| <= (C : Real) := by
      intro t
      exact Filter.Eventually.of_forall fun omega =>
        (H.abs_integrand_le_coefficientAbsSum t omega).trans
          (by exact_mod_cast hCoefficient omega)
    have hGrid := eLpNorm_predictableStepProcess_eq_terminal
      D hM hMRight hMT G H.integrand
        H.integrand_isStronglyPredictable (C := fun _ => (C : Real)) hBound
    have hLeft : Function.uncurry (G.predictableStepProcess H.integrand) =
        approximantIntegrand r := by
      funext p
      change G.predictableStepProcess H.integrand p.1 p.2 =
        (H.horizonLeftStepStrategy r T).integrand p.1 p.2
      rw [PredictableElementaryStrategy.horizonLeftStepStrategy,
        PredictableElementaryStrategy.finiteLeftStepStrategy,
        ChronologicalGrid.predictableElementaryStrategy_integrand]
    have hRight : discretePredictableIntegral
        (G.natSample H.integrand)
        (G.natSample (deterministicallyStoppedProcess M T)) N = approximantGain r := by
      calc
        discretePredictableIntegral
            (G.natSample H.integrand)
            (G.natSample (deterministicallyStoppedProcess M T)) N =
            G.martingaleIntegralProcess H.integrand
              (deterministicallyStoppedProcess M T) (G.sampledTime N) :=
          (G.martingaleIntegralProcess_last H.integrand
            (deterministicallyStoppedProcess M T)).symm
        _ = G.martingaleIntegralProcess H.integrand M T := by
          simpa only [deterministicallyStoppedProcess,
            deterministicallyStoppedProcess] using
            FiniteHorizonMartingaleEnergyContent.martingaleIntegralProcess_stoppedSource_last
              G H.integrand M T
        _ = approximantGain r := by
          funext omega
          change G.martingaleIntegralProcess H.integrand M T omega =
            ElementaryStrategy.gain M
              (H.horizonLeftStepStrategy r T).toElementary T omega
          symm
          simpa only [PredictableElementaryStrategy.horizonLeftStepStrategy,
            PredictableElementaryStrategy.finiteLeftStepStrategy, G, N] using
            G.predictableElementaryStrategy_gain H.integrand
              H.integrand_isStronglyPredictable M T omega
    simpa only [hLeft, hRight] using hGrid
  have hGainNorm' : Tendsto
      (fun r => (eLpNorm (approximantIntegrand r) (2 : ENNReal)
        D.predictableEnergyMeasure).toReal) atTop
      (nhds ((eLpNorm targetGain (2 : ENNReal) mu).toReal)) :=
    hGainNorm.congr'
      (Filter.Eventually.of_forall fun r =>
        congrArg ENNReal.toReal (hApproximationIsometry r) |>.symm)
  have hToReal : (eLpNorm targetIntegrand (2 : ENNReal)
      D.predictableEnergyMeasure).toReal =
      (eLpNorm targetGain (2 : ENNReal) mu).toReal :=
    tendsto_nhds_unique hIntegrandNorm hGainNorm'
  exact (ENNReal.toReal_eq_toReal_iff'
    hTargetIntegrandMem.eLpNorm_ne_top hTargetGainMem.eLpNorm_ne_top).mp
      hToReal

/-- On the elementary predictable indicator ring, the quadratic Stieltjes
measure is exactly the previously constructed martingale energy content. -/
theorem predictableEnergyMeasure_apply_eq_addContent
    [SigmaFiniteFiltration mu F]
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    {s : Set (NNReal × Omega)}
    (hs : s ∈ FiniteHorizonPredictableIndicatorRing.sets (F := F) T) :
    D.predictableEnergyMeasure s =
      FiniteHorizonMartingaleEnergyContent.addContent
        M hM hMRight T hMT s := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure :=
    D.predictableEnergyMeasure_isFinite
  let R := Classical.choice hs.2
  let carrier :=
    FiniteHorizonPredictableIndicatorRing.horizonCarrier
      (Omega := Omega) T
  have hCarrierAE : ∀ᵐ p ∂D.predictableEnergyMeasure,
      p ∈ carrier := by
    filter_upwards [D.ae_time_pos, D.ae_time_le_horizon]
      with p hp hle
    exact ⟨⟨hp, hle⟩, Set.mem_univ p.2⟩
  have hMeasureInter : D.predictableEnergyMeasure s =
      D.predictableEnergyMeasure (s ∩ carrier) := by
    have h := Measure.measure_inter_eq_of_ae
      (μ := D.predictableEnergyMeasure) (s := s) hCarrierAE
    simpa only [inter_comm] using h.symm
  have hInterMeas : MeasurableSet[F.predictable] (s ∩ carrier) :=
    hs.1.inter
      (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T)
  have hIndicator :
      (fun p : NNReal × Omega =>
        ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2) =
        (s ∩ carrier).indicator (fun _ => (1 : ENNReal)) := by
    funext p
    change ‖R.strategy.integrand p.1 p.2‖ₑ ^ 2 = _
    rw [congrFun (congrFun R.integrand_eq p.1) p.2]
    by_cases hp : p ∈ s ∩ carrier <;>
      simp [FiniteHorizonPredictableIndicatorRing.indicatorProcess,
        carrier, hp]
  have hIntegrandMem : MemLp (Function.uncurry R.strategy.integrand)
      (2 : ENNReal) D.predictableEnergyMeasure := by
    apply MemLp.of_bound
      R.strategy.integrand_isStronglyPredictable.aestronglyMeasurable
      (R.bound : Real)
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact (R.strategy.abs_integrand_le_coefficientAbsSum p.1 p.2).trans
        (R.coefficientAbsSum_le p.2)
  have hGainMem : MemLp
      (FiniteHorizonMartingaleEnergyContent.representationGain R M)
      (2 : ENNReal) mu :=
    R.strategy.gain_memLp_two M hM hMRight T hMT R.bound
      R.coefficientAbsSum_le
  have hNormEq :
      ‖hIntegrandMem.toLp (Function.uncurry R.strategy.integrand)‖ =
        ‖hGainMem.toLp
          (FiniteHorizonMartingaleEnergyContent.representationGain R M)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact congrArg ENNReal.toReal
      (eLpNorm_predictableEnergyMeasure_eq_gain D hM hMRight hMT
        R.strategy R.bound R.coefficientAbsSum_le)
  have hLIntegral :
      (∫⁻ p, ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2
          ∂D.predictableEnergyMeasure) =
        ∫⁻ omega,
          ‖FiniteHorizonMartingaleEnergyContent.representationGain R M omega‖ₑ ^
            2 ∂mu := by
    rw [FiniteHorizonMartingaleEnergyContent.lintegral_enorm_sq_eq_ofReal_norm_toLp_sq
        hIntegrandMem,
      FiniteHorizonMartingaleEnergyContent.lintegral_enorm_sq_eq_ofReal_norm_toLp_sq
        hGainMem,
      hNormEq]
  have hGainEnergy :
      (∫⁻ omega,
          ‖FiniteHorizonMartingaleEnergyContent.representationGain R M omega‖ₑ ^
            2 ∂mu) =
        FiniteHorizonMartingaleEnergyContent.representationEnergy
          hM hMRight hMT R := by
    rw [FiniteHorizonMartingaleEnergyContent.lintegral_enorm_sq_eq_ofReal_norm_toLp_sq
      hGainMem]
    rfl
  calc
    D.predictableEnergyMeasure s =
        D.predictableEnergyMeasure (s ∩ carrier) := hMeasureInter
    _ = ∫⁻ p, ‖Function.uncurry R.strategy.integrand p‖ₑ ^ 2
        ∂D.predictableEnergyMeasure := by
      rw [hIndicator]
      exact (lintegral_indicator_one hInterMeas).symm
    _ = ∫⁻ omega,
        ‖FiniteHorizonMartingaleEnergyContent.representationGain R M omega‖ₑ ^
          2 ∂mu := hLIntegral
    _ = FiniteHorizonMartingaleEnergyContent.representationEnergy
        hM hMRight hMT R := hGainEnergy
    _ = FiniteHorizonMartingaleEnergyContent.addContent
        M hM hMRight T hMT s :=
      (FiniteHorizonMartingaleEnergyContent.addContent_apply_eq_representationEnergy
        hM hMRight hMT hs.1 R).symm

end Data

end BoundedMartingaleQuadraticEnergy

end FTAPTheorem42
