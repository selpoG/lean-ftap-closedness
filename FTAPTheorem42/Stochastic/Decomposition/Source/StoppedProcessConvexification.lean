/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationCadlagRegularization
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedPredictableProcess
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import Mathlib.Analysis.BoundedVariation

/-!
# Process-level convex rows for the stopped factorial decomposition

The common tail-convex weights selected on the canonical skeleton are applied
to the three full-time stopped rows simultaneously.  The predictable row uses
`stoppedPredictableProcess` itself; no new predictable version is selected at
this stage.  The rows are only asserted to have the regularity proved below:
the predictable row is strongly predictable and of bounded variation, while
the martingale row is deliberately not given an unsupported grid-between-time
identity or right-continuity statement.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Full-time rows -/

/-- The `n`-th common-weight row of the stopped source approximations. -/
noncomputable def stoppedSourceConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    (w n).apply (fun r =>
      stoppedSourceApproximation a T (min t T) (min_le_right t T) r S F mu) omega

/-- The `n`-th common-weight row of the stopped martingale step processes. -/
noncomputable def stoppedMartingaleConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    (w n).apply (fun r =>
      stoppedMartingaleApproximation a T (min t T) (min_le_right t T) r S F mu) omega

/-- The `n`-th common-weight row of the stopped predictable processes. -/
noncomputable def stoppedPredictableConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Process Omega :=
  fun t omega =>
    (w n).apply (fun r => stoppedPredictableProcess a T r S F mu t) omega

/-! ## Row identities and stopping -/

private theorem dependent_time_eq
    {β : Type*} {p : NNReal → Prop}
    (f : (u : NNReal) → p u → β)
    {u v : NNReal} (h : u = v) (hu : p u) (hv : p v) :
    f u hu = f v hv := by
  subst v
  rfl

/-- The three rows retain the stopped Doob decomposition at every time. -/
theorem stoppedSourceConvexRow_eq_add
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    stoppedSourceConvexRow w n a T S F mu =
      stoppedMartingaleConvexRow w n a T S F mu +
        stoppedPredictableConvexRow w n a T S F mu := by
  funext t omega
  unfold stoppedSourceConvexRow stoppedMartingaleConvexRow
    stoppedPredictableConvexRow stoppedPredictableProcess stoppedPredictablePath
    TailConvexWeights.apply
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hDecomposition := congrFun
    (stoppedSourceApproximation_eq_martingale_add_predictable
      a T (min t T) (min_le_right t T) r S F mu) omega
  simp only [Pi.add_apply] at hDecomposition
  rw [hDecomposition]
  ring

@[simp]
theorem stoppedPredictableConvexRow_stopAt
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) :
    MeasureTheory.stoppedProcess
        (stoppedPredictableConvexRow w n a T S F mu)
        (fun _ : Omega => (T : WithTop NNReal)) =
      stoppedPredictableConvexRow w n a T S F mu := by
  funext t omega
  change stoppedPredictableConvexRow w n a T S F mu (min t T) omega =
    stoppedPredictableConvexRow w n a T S F mu t omega
  unfold stoppedPredictableConvexRow
  unfold TailConvexWeights.apply
  apply Finset.sum_congr rfl
  intro r hr
  have hP := congrFun
    (congrFun (stoppedPredictableProcess_stopAt a T r S F mu) t) omega
  change stoppedPredictableProcess a T r S F mu (min t T) omega =
    stoppedPredictableProcess a T r S F mu t omega at hP
  change (w n).weight r * stoppedPredictableProcess a T r S F mu
      (min t T) omega =
    (w n).weight r * stoppedPredictableProcess a T r S F mu t omega
  rw [hP]

/-! ## Predictability and variation of the predictable row -/

private theorem eVariationOn_const_mul_le
    {Time : Type*} [LinearOrder Time]
    (c : Real) (f : Time → Real) (D : ENNReal)
    (hf : ∀ t, ‖f t‖ₑ ≤ D) :
    eVariationOn (fun t => c * f t) Set.univ ≤
      ENNReal.ofReal |c| * eVariationOn f Set.univ := by
  have hconst : eVariationOn (fun _ : Time => c) Set.univ = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
    rfl
  have h := eVariationOn_smul_le
    (f := fun _ : Time => c) (g := f)
    (C := ENNReal.ofReal |c|) (D := D) (s := Set.univ)
    (fun _ _ => by
      rw [enorm_eq_nnnorm]
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg c)]
      rw [ENNReal.coe_le_coe]
      apply le_of_eq
      apply NNReal.eq
      change ‖c‖ = |c|
      exact Real.norm_eq_abs c)
    (fun t _ => hf t)
  change eVariationOn (fun t => c * f t) Set.univ ≤ _ at h
  rw [hconst, mul_zero, add_zero] at h
  exact h

private theorem eVariationOn_finset_sum_le
    {Time : Type*} [LinearOrder Time]
    (s : Finset Nat) (f : Nat → Time → Real) :
    eVariationOn (fun t => ∑ i ∈ s, f i t) Set.univ ≤
      ∑ i ∈ s, eVariationOn (f i) Set.univ := by
  induction s using Finset.induction_on with
  | empty =>
      have hzero : eVariationOn (fun _ : Time => (0 : Real)) Set.univ = 0 := by
        apply eVariationOn.constant_on
        rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
        rfl
      simpa only [Finset.sum_empty] using hzero.le
  | @insert i s hi ih =>
      calc
        eVariationOn (fun t => ∑ j ∈ insert i s, f j t) Set.univ =
            eVariationOn (fun t => f i t + ∑ j ∈ s, f j t) Set.univ := by
              congr 1
              funext t
              rw [Finset.sum_insert hi]
        _ ≤ eVariationOn (f i) Set.univ +
            eVariationOn (fun t => ∑ j ∈ s, f j t) Set.univ :=
          eVariationOn_add_le_real _ _ _
        _ ≤ eVariationOn (f i) Set.univ + ∑ j ∈ s, eVariationOn (f j) Set.univ :=
          add_le_add le_rfl ih
        _ = ∑ j ∈ insert i s, eVariationOn (f j) Set.univ := by
          rw [Finset.sum_insert hi]

theorem isStronglyPredictable_stoppedPredictableConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n) (n : Nat) :
    IsStronglyPredictable F
      (stoppedPredictableConvexRow w n a T S F mu) := by
  change StronglyMeasurable[F.predictable]
    (fun p : NNReal × Omega =>
      ∑ r ∈ (w n).support,
        (w n).weight r * stoppedPredictableProcess a T r S F mu p.1 p.2)
  refine (w n).support.stronglyMeasurable_fun_sum ?_
  intro r hr
  have hR := isStronglyPredictable_stoppedPredictableProcess
    source ha T r
  change StronglyMeasurable[F.predictable]
    (fun p : NNReal × Omega =>
      (w n).weight r * stoppedPredictableProcess a T r S F mu p.1 p.2)
  have h :=
    ((show StronglyMeasurable[F.predictable]
        (Function.uncurry (stoppedPredictableProcess a T r S F mu)) from hR).const_smul
      ((w n).weight r))
  change StronglyMeasurable[F.predictable]
    (fun p : NNReal × Omega =>
      (w n).weight r * stoppedPredictableProcess a T r S F mu p.1 p.2) at h
  exact h

theorem boundedVariationOn_stoppedPredictableConvexRow
    (w : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) :
    BoundedVariationOn
      (stoppedPredictableConvexRow w n a T S F mu · omega) Set.univ := by
  let P : Nat → NNReal → Real := fun r t =>
    stoppedPredictableProcess a T r S F mu t omega
  have hP : ∀ r, BoundedVariationOn (P r) Set.univ := by
    intro r
    exact boundedVariationOn_stoppedPredictableProcess a T r S F mu omega
  have hScaled : ∀ i ∈ (w n).support,
      BoundedVariationOn (fun t => (w n).weight i * P i t) Set.univ := by
    intro i hi
    have hConst : BoundedVariationOn
        (fun _ : NNReal => (w n).weight i) Set.univ := by
      change eVariationOn (fun _ : NNReal => (w n).weight i) Set.univ ≠ ∞
      have hzero : eVariationOn
          (fun _ : NNReal => (w n).weight i) Set.univ = 0 := by
        apply eVariationOn.constant_on
        rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
        rfl
      rw [hzero]
      exact ENNReal.zero_ne_top
    convert hConst.smul (hP i) using 1
  change BoundedVariationOn
    (fun t => ∑ i ∈ (w n).support, (w n).weight i * P i t) Set.univ
  change eVariationOn
      (fun t => ∑ i ∈ (w n).support, (w n).weight i * P i t) Set.univ ≠ ∞
  have hSum := eVariationOn_finset_sum_le
    (s := (w n).support)
    (f := fun i t => (w n).weight i * P i t)
  have hFinite : ∀ i ∈ (w n).support,
      eVariationOn (fun t => (w n).weight i * P i t) Set.univ ≠ ∞ := by
    intro i hi
    exact hScaled i hi
  exact ne_top_of_le_ne_top
    (b := ∑ i ∈ (w n).support,
      eVariationOn (fun t => (w n).weight i * P i t) Set.univ)
    (ENNReal.sum_ne_top.mpr (fun i hi => hFinite i hi)) hSum

theorem ae_eVariationOn_stoppedPredictableConvexRow_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n) (n : Nat) :
    ∀ᵐ omega ∂mu,
      eVariationOn
          (stoppedPredictableConvexRow w n a T S F mu · omega) Set.univ ≤
        ENNReal.ofReal (a + 2 * max source.bound 0) := by
  have hAll : ∀ᵐ omega ∂mu, ∀ r,
      eVariationOn
          (stoppedPredictableProcess a T r S F mu · omega) Set.univ ≤
        ENNReal.ofReal (a + 2 * max source.bound 0) := by
    exact ae_all_iff.mpr (fun r =>
      ae_eVariationOn_stoppedPredictableProcess_le source ha T r)
  filter_upwards [hAll] with omega hOmega
  let C : Real := a + 2 * max source.bound 0
  let P : Nat → NNReal → Real := fun r t =>
    stoppedPredictableProcess a T r S F mu t omega
  have hSum := eVariationOn_finset_sum_le
    (s := (w n).support)
    (f := fun i t => (w n).weight i * P i t)
  calc
    eVariationOn
        (stoppedPredictableConvexRow w n a T S F mu · omega) Set.univ =
        eVariationOn
          (fun t => ∑ i ∈ (w n).support, (w n).weight i * P i t) Set.univ := by
      rfl
    _ ≤ ∑ i ∈ (w n).support,
        eVariationOn (fun t => (w n).weight i * P i t) Set.univ := hSum
    _ ≤ ∑ i ∈ (w n).support,
        ENNReal.ofReal |(w n).weight i| *
          eVariationOn (P i) Set.univ := by
      apply Finset.sum_le_sum
      intro i hi
      exact eVariationOn_const_mul_le ((w n).weight i) (P i) ∞
        (fun _ => le_top)
    _ ≤ ∑ i ∈ (w n).support,
        ENNReal.ofReal |(w n).weight i| * ENNReal.ofReal C := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact hOmega i
    _ = ENNReal.ofReal C := by
      rw [← Finset.sum_mul]
      have hWeights : ∑ i ∈ (w n).support,
          ENNReal.ofReal |(w n).weight i| = 1 := by
        calc
          ∑ i ∈ (w n).support, ENNReal.ofReal |(w n).weight i| =
              ENNReal.ofReal (∑ i ∈ (w n).support, |(w n).weight i|) := by
                symm
                rw [ENNReal.ofReal_sum_of_nonneg]
                intro i hi
                exact abs_nonneg _
          _ = ENNReal.ofReal (∑ i ∈ (w n).support, (w n).weight i) := by
                apply congrArg ENNReal.ofReal
                apply Finset.sum_congr rfl
                intro i hi
                rw [abs_of_nonneg ((w n).nonneg i hi)]
          _ = ENNReal.ofReal 1 := by rw [(w n).sum_eq_one]
          _ = 1 := by norm_num
      rw [hWeights, one_mul]

/-! ## Bridges to the existing skeleton `applyVector` coordinates -/

private theorem stoppedPredictableConvexRow_skeleton_apply
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n) (n i : Nat) :
    stoppedPredictableConvexRow w n a T S F mu
        (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((w n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
  have hiT : (stoppedLimitSkeleton T i).1 ≤ T := by
    exact (stoppedLimitSkeleton T i).2
  have hRaw :
      (((w n).applyVector (fun r =>
        stoppedPredictableApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 hiT r) : Lp Real 2 mu) : Omega → Real) =ᵐ[mu]
        (w n).apply (fun r => stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    exact (w n).applyVector_coeFn_ae
      (fun r => stoppedPredictableApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 hiT r)
      (fun r => stoppedPredictableApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_stoppedPredictableApproximation source ha T
          (stoppedLimitSkeleton T i).1 hiT r))
  have hRow :
      stoppedPredictableConvexRow w n a T S F mu
          (stoppedLimitSkeleton T i).1 =
        (w n).apply (fun r => stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    funext omega
    unfold stoppedPredictableConvexRow
    change (∑ r ∈ (w n).support,
      (w n).weight r * stoppedPredictableProcess a T r S F mu
        (stoppedLimitSkeleton T i).1 omega) =
      ∑ r ∈ (w n).support,
        (w n).weight r * stoppedPredictableApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    apply Finset.sum_congr rfl
    intro r hr
    have hprocess :
        stoppedPredictableProcess a T r S F mu
            (stoppedLimitSkeleton T i).1 omega =
          stoppedPredictableApproximation a T
            (stoppedLimitSkeleton T i).1 hiT r S F mu omega := by
      unfold stoppedPredictableProcess stoppedPredictablePath
      exact dependent_time_eq
        (f := fun u hu => stoppedPredictableApproximation a T u hu r S F mu omega)
        (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT
    change (w n).weight r * stoppedPredictableProcess a T r S F mu
        (stoppedLimitSkeleton T i).1 omega =
      (w n).weight r * stoppedPredictableApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    rw [hprocess]
  rw [hRow]
  exact hRaw.symm

private theorem stoppedMartingaleConvexRow_skeleton_apply
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n) (n i : Nat) :
    stoppedMartingaleConvexRow w n a T S F mu
        (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      (((w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
        Lp Real 2 mu) : Omega → Real) := by
  have hiT : (stoppedLimitSkeleton T i).1 ≤ T := by
    exact (stoppedLimitSkeleton T i).2
  have hRaw :
      (((w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 hiT r) : Lp Real 2 mu) : Omega → Real) =ᵐ[mu]
        (w n).apply (fun r => stoppedMartingaleApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    exact (w n).applyVector_coeFn_ae
      (fun r => stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 hiT r)
      (fun r => stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_stoppedMartingaleApproximation source ha T
          (stoppedLimitSkeleton T i).1 hiT r))
  have hRow :
      stoppedMartingaleConvexRow w n a T S F mu
          (stoppedLimitSkeleton T i).1 =
        (w n).apply (fun r => stoppedMartingaleApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu) := by
    funext omega
    unfold stoppedMartingaleConvexRow
    change (∑ r ∈ (w n).support,
      (w n).weight r * stoppedMartingaleApproximation a T
        (min (stoppedLimitSkeleton T i).1 T)
          (min_le_right (stoppedLimitSkeleton T i).1 T) r S F mu omega) =
      ∑ r ∈ (w n).support,
        (w n).weight r * stoppedMartingaleApproximation a T
          (stoppedLimitSkeleton T i).1 hiT r S F mu omega
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    exact dependent_time_eq
      (f := fun u hu => stoppedMartingaleApproximation a T u hu r S F mu omega)
      (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT
  rw [hRow]
  exact hRaw.symm

theorem exists_stoppedProcessConvexification_rows
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (predictableLimit martingaleLimit : Nat → Lp Real 2 mu)
      (M : Process Omega)
      (Xbar Mbar A : Nat → Process Omega),
      (∀ j, Tendsto
        (fun n => (w n).applyVector (fun r =>
          stoppedPredictableApproximationToLp source ha T
            (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
        atTop (𝓝 (predictableLimit j))) ∧
      (∀ j, Tendsto
        (fun n => (w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
        atTop (𝓝 (martingaleLimit j))) ∧
      Martingale M F mu ∧
      (∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t) ∧
      ProcessHasLeftLimits M ∧
      (∀ i, M (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (martingaleLimit i : Omega → Real)) ∧
      (∀ n, Xbar n = Mbar n + A n) ∧
      (∀ n, IsStronglyPredictable F (A n)) ∧
      (∀ n, MeasureTheory.stoppedProcess (A n)
        (fun _ : Omega => (T : WithTop NNReal)) = A n) ∧
      (∀ n omega, BoundedVariationOn (A n · omega) Set.univ) ∧
      (∀ n, ∀ᵐ omega ∂mu,
        eVariationOn (A n · omega) Set.univ ≤
          ENNReal.ofReal (a + 2 * max source.bound 0)) ∧
      (∀ n i, Xbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (w n).apply (fun r => stoppedSourceApproximation a T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r S F mu)) ∧
      (∀ n i, Mbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (((w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
          Lp Real 2 mu) : Omega → Real)) ∧
      (∀ n i, A n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (((w n).applyVector (fun r =>
          stoppedPredictableApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
          Lp Real 2 mu) : Omega → Real)) := by
  obtain ⟨w, predictableLimit, martingaleLimit, M,
      hPredictable, hMartingale, hM, hMRight, hMLeft, hMSkeleton⟩ :=
    exists_common_stoppedComponentConvexification_cadlagMartingaleProcess
      hUsual source ha T
  let Xbar : Nat → Process Omega := fun n =>
    stoppedSourceConvexRow w n a T S F mu
  let Mbar : Nat → Process Omega := fun n =>
    stoppedMartingaleConvexRow w n a T S F mu
  let A : Nat → Process Omega := fun n =>
    stoppedPredictableConvexRow w n a T S F mu
  refine ⟨w, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
    hPredictable, hMartingale, hM, hMRight, hMLeft, hMSkeleton,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact stoppedSourceConvexRow_eq_add w n a T S F mu
  · intro n
    exact isStronglyPredictable_stoppedPredictableConvexRow source ha T w n
  · intro n
    exact stoppedPredictableConvexRow_stopAt w n a T S F mu
  · intro n omega
    exact boundedVariationOn_stoppedPredictableConvexRow w n a T S F mu omega
  · intro n
    exact ae_eVariationOn_stoppedPredictableConvexRow_le source ha T w n
  · intro n i
    have hiT : (stoppedLimitSkeleton T i).1 ≤ T := by
      exact (stoppedLimitSkeleton T i).2
    change stoppedSourceConvexRow w n a T S F mu
      (stoppedLimitSkeleton T i).1 =ᵐ[mu] _
    rw [show stoppedSourceConvexRow w n a T S F mu
        (stoppedLimitSkeleton T i).1 =
        (w n).apply (fun r => stoppedSourceApproximation a T
        (stoppedLimitSkeleton T i).1 hiT r S F mu) by
          unfold stoppedSourceConvexRow
          change (fun omega => ∑ r ∈ (w n).support,
            (w n).weight r * stoppedSourceApproximation a T
              (min (stoppedLimitSkeleton T i).1 T)
                (min_le_right (stoppedLimitSkeleton T i).1 T) r S F mu omega) =
            (fun omega => ∑ r ∈ (w n).support,
              (w n).weight r * stoppedSourceApproximation a T
                (stoppedLimitSkeleton T i).1 hiT r S F mu omega)
          funext omega
          apply Finset.sum_congr rfl
          intro r hr
          congr 1
          exact dependent_time_eq
            (f := fun u hu => stoppedSourceApproximation a T u hu r S F mu omega)
            (min_eq_left hiT) (min_le_right (stoppedLimitSkeleton T i).1 T) hiT]
  · intro n i
    exact stoppedMartingaleConvexRow_skeleton_apply source ha T w n i
  · intro n i
    exact stoppedPredictableConvexRow_skeleton_apply source ha T w n i

end HorizonFactorialGrid

end FTAPTheorem42
