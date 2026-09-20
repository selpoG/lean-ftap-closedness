/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRegularizedRawFiniteVariation
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridPredictableElementaryStrategy
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral
import FTAPTheorem42.Stochastic.Decomposition.Source.CompensatorKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Finite-grid predictable compensator rows

For an adapted increasing process which is bounded at a deterministic horizon,
this file constructs the predictable finite-grid compensator directly.  The
increment on the `k`-th grid block is a pointwise clipped version of
`E[V(t_(k+1))-V(t_k) | F(t_k)]`.  Clipping only changes a null set, while it
gives an everywhere nonnegative and bounded version which can be put into a
predictable step process.

The second-moment estimate is proved at the finite-grid level.  In particular,
it uses the discrete integration-by-parts estimate for the increasing source;
an `L¹` estimate is not used as an `L²` substitute.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

/-! ## The bounded increasing input -/

structure BoundedIncreasingProcessData
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (V : Process Ω) (T C : NNReal) : Prop where
  stronglyAdapted : StronglyAdapted F V
  adapted : Adapted F V
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (V · omega) (Ici t) t
  monotone : ∀ omega, Monotone (V · omega)
  zero : V 0 = 0
  constant_after : ∀ omega t, T ≤ t → V t omega = V T omega
  terminal_bound : ∀ omega, 0 ≤ V T omega ∧ V T omega ≤ C

namespace BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

theorem value_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    {t : NNReal} (_ht : t ≤ T) (omega : Ω) :
    0 ≤ V t omega := by
  have hmono := hV.monotone omega (show (0 : NNReal) ≤ t from bot_le)
  have hzero : V 0 omega = 0 := congrFun hV.zero omega
  linarith

theorem value_le_bound
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    {t : NNReal} (ht : t ≤ T) (omega : Ω) :
    V t omega ≤ C := by
  exact (hV.monotone omega ht).trans (hV.terminal_bound omega).2

theorem value_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    {t : NNReal} (ht : t ≤ T) :
    MemLp (V t) (2 : ENNReal) mu := by
  have hC : 0 ≤ (C : Real) := by positivity
  apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    ((hV.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    (C : Real)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (hV.value_nonneg ht omega)]
  exact hV.value_le_bound ht omega

theorem increment_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (_hk : k < size T r) (omega : Ω) :
    0 ≤ V ((grid T r).sampledTime (k + 1)) omega -
      V ((grid T r).sampledTime k) omega := by
  exact sub_nonneg.mpr (hV.monotone omega
    ((grid T r).sampledTime_mono (Nat.le_succ k)))

theorem increment_le_bound
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) (omega : Ω) :
    V ((grid T r).sampledTime (k + 1)) omega -
      V ((grid T r).sampledTime k) omega ≤ C := by
  have hk1 : (grid T r).sampledTime (k + 1) ≤ T := by
    exact ((grid T r).sampledTime_mono (Nat.succ_le_iff.mpr hk)).trans_eq
      (sampledTime_size T r)
  have hleft : 0 ≤ V ((grid T r).sampledTime k) omega :=
    hV.value_nonneg (((grid T r).sampledTime_mono (Nat.le_succ k)).trans hk1) omega
  have hright : V ((grid T r).sampledTime (k + 1)) omega ≤ C :=
    hV.value_le_bound hk1 omega
  linarith

end BoundedIncreasingProcessData

/-! ## Clipped conditional increments -/

noncomputable def compensatorIncrement
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r k : Nat) : Ω → Real :=
  if (grid T r).sampledTime k < (grid T r).sampledTime (k + 1) then
    fun omega => max 0 (min (C : Real)
      (rawCompensatorIncrement V F mu T r k omega))
  else 0

noncomputable def compensatorCumulative
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r n : Nat) : Ω → Real :=
  finiteGridCompensatorCumulative T
    (fun k => compensatorIncrement V F mu T C r k) r n

noncomputable def predictableCompensatorProcess
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r : Nat) : Process Ω :=
  finiteGridPredictableCompensatorProcess T
    (fun k => compensatorIncrement V F mu T C r k) r

@[simp] theorem compensatorCumulative_succ
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) (r n : Nat) :
    compensatorCumulative V F mu T C r (n + 1) =
      compensatorCumulative V F mu T C r n +
        compensatorIncrement V F mu T C r n := by
  simpa [compensatorCumulative] using
    (finiteGridCompensatorCumulative_succ T
      (fun k => compensatorIncrement V F mu T C r k) r n)

namespace BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T C : NNReal}

theorem increment_eq_zero_of_grid_time_eq
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (_hk : k < size T r)
    (h : (grid T r).sampledTime k =
      (grid T r).sampledTime (k + 1)) :
    gridIncrement V T r k = 0 := by
  funext omega
  simp [gridIncrement, h]

theorem increment_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    MemLp (gridIncrement V T r k) (2 : ENNReal) mu := by
  have hk0 : (grid T r).sampledTime k ≤ T :=
    finiteGrid_sampledTime_le_horizon T r k
      (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hk))
  have hk1 : (grid T r).sampledTime (k + 1) ≤ T :=
    finiteGrid_sampledTime_le_horizon T r (k + 1)
      (Nat.succ_le_iff.mpr hk)
  have hleft := hV.value_memLp_two (mu := mu) hk0
  have hright := hV.value_memLp_two (mu := mu) hk1
  change MemLp (fun omega =>
    V ((grid T r).sampledTime (k + 1)) omega -
      V ((grid T r).sampledTime k) omega) (2 : ENNReal) mu
  exact hright.sub hleft

theorem integrable_gridIncrement
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    Integrable (gridIncrement V T r k) mu :=
  (hV.increment_memLp_two r k hk).integrable (by norm_num)

omit [IsProbabilityMeasure mu] in
theorem ae_rawCompensatorIncrement_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    0 ≤ᵐ[mu] rawCompensatorIncrement V F mu T r k := by
  unfold rawCompensatorIncrement
  apply condExp_nonneg
  exact ae_of_all mu (fun omega => hV.increment_nonneg r k hk omega)

omit [IsProbabilityMeasure mu] in
theorem ae_rawCompensatorIncrement_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    rawCompensatorIncrement V F mu T r k ≤ᵐ[mu]
      (fun _ => (C : Real)) := by
  unfold rawCompensatorIncrement
  apply condExp_le_nonneg_const (by positivity)
  exact ae_of_all mu (fun omega => hV.increment_le_bound r k hk omega)

omit [IsProbabilityMeasure mu] in
theorem compensatorIncrement_nonneg
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    0 ≤ compensatorIncrement V F mu T C r k := by
  classical
  intro omega
  unfold compensatorIncrement
  split_ifs
  · exact le_max_left _ _
  · simp

omit [IsProbabilityMeasure mu] in
theorem compensatorIncrement_le
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    compensatorIncrement V F mu T C r k ≤ fun _ => (C : Real) := by
  classical
  intro omega
  unfold compensatorIncrement
  split_ifs
  · exact max_le (by positivity) (min_le_left _ _)
  · simp only [Pi.zero_apply]
    positivity

omit [IsProbabilityMeasure mu] in
theorem compensatorIncrement_eq_raw_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    compensatorIncrement V F mu T C r k =ᵐ[mu]
      rawCompensatorIncrement V F mu T r k := by
  classical
  have hnonneg := hV.ae_rawCompensatorIncrement_nonneg
    (F := F) (mu := mu) r k hk
  have hle := hV.ae_rawCompensatorIncrement_le
    (F := F) (mu := mu) r k hk
  have htime :
      (grid T r).sampledTime k < (grid T r).sampledTime (k + 1) ∨
        (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) := by
    exact le_iff_lt_or_eq.mp ((grid T r).sampledTime_mono (Nat.le_succ k))
  cases htime with
  | inl hlt =>
      filter_upwards [hnonneg, hle] with omega h0 hC
      simp only [compensatorIncrement, hlt, ↓reduceIte]
      rw [min_eq_right hC]
      exact max_eq_right h0
  | inr heq =>
      have hz := hV.increment_eq_zero_of_grid_time_eq
        (F := F) r k hk heq
      have hcond : rawCompensatorIncrement V F mu T r k =ᵐ[mu] 0 := by
        rw [show rawCompensatorIncrement V F mu T r k =
            mu[gridIncrement V T r k | F ((grid T r).sampledTime k)] by rfl]
        rw [show gridIncrement V T r k = 0 by exact hz]
        simp
      filter_upwards [hcond] with omega hzero
      simp [compensatorIncrement, heq, hzero]

omit [IsProbabilityMeasure mu] in
theorem compensatorIncrement_measurable
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    StronglyMeasurable[F ((grid T r).sampledTime k)]
      (compensatorIncrement V F mu T C r k) := by
  classical
  unfold compensatorIncrement
  split_ifs with htime
  · have hcond : StronglyMeasurable[F ((grid T r).sampledTime k)]
        (rawCompensatorIncrement V F mu T r k) :=
      stronglyMeasurable_condExp
    have hmin : StronglyMeasurable[F ((grid T r).sampledTime k)]
        (fun omega => min (C : Real)
          (rawCompensatorIncrement V F mu T r k omega)) :=
      ((stronglyMeasurable_const :
        StronglyMeasurable[F ((grid T r).sampledTime k)]
          (fun _ : Ω => (C : Real))).measurable.min hcond.measurable).stronglyMeasurable
    exact ((stronglyMeasurable_const :
      StronglyMeasurable[F ((grid T r).sampledTime k)]
        (fun _ : Ω => (0 : Real))).measurable.max hmin.measurable).stronglyMeasurable
  · exact stronglyMeasurable_const

theorem compensatorIncrement_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    Integrable (compensatorIncrement V F mu T C r k) mu := by
  have hC : 0 ≤ (C : Real) := by positivity
  apply Integrable.of_bound
    ((hV.compensatorIncrement_measurable r k).mono (F.le _)).aestronglyMeasurable
    (C : Real)
  filter_upwards with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (hV.compensatorIncrement_nonneg
      (mu := mu) r k omega)]
  exact hV.compensatorIncrement_le (mu := mu) r k omega

/-! ## Predictable step producers -/

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_isStronglyPredictable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    IsStronglyPredictable F
      (predictableCompensatorProcess V F mu T C r) := by
  change IsStronglyPredictable F
    (finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r)
  apply finiteGridCompensatorProcess_isStronglyPredictable
  intro k
  exact hV.compensatorIncrement_measurable (F := F) (mu := mu) r k

omit [IsProbabilityMeasure mu] in
@[simp] theorem compensatorIncrement_eq_zero_of_grid_time_eq
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat)
    (h : (grid T r).sampledTime k =
      (grid T r).sampledTime (k + 1)) :
    compensatorIncrement V F mu T C r k = 0 := by
  simp [compensatorIncrement, h]

omit [IsProbabilityMeasure mu] in
@[simp] theorem predictableCompensatorProcess_zero
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    predictableCompensatorProcess V F mu T C r 0 = 0 := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r 0 = 0
  exact finiteGridPredictableCompensatorProcess_zero T
    (fun k => compensatorIncrement V F mu T C r k) r

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) (t : NNReal) (omega : Ω) :
    0 ≤ predictableCompensatorProcess V F mu T C r t omega := by
  change 0 ≤ finiteGridPredictableCompensatorProcess T
    (fun k => compensatorIncrement V F mu T C r k) r t omega
  apply finiteGridPredictableCompensatorProcess_nonneg
  · intro k omega
    exact hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_mono
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) (omega : Ω) :
    Monotone (predictableCompensatorProcess V F mu T C r · omega) := by
  change Monotone (finiteGridPredictableCompensatorProcess T
    (fun k => compensatorIncrement V F mu T C r k) r · omega)
  apply finiteGridPredictableCompensatorProcess_mono
  intro k omega
  exact hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_constant_after
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) (omega : Ω) (t : NNReal) (ht : T ≤ t) :
    predictableCompensatorProcess V F mu T C r t omega =
      predictableCompensatorProcess V F mu T C r T omega := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r t omega =
    finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r T omega
  refine finiteGridPredictableCompensatorProcess_constant_after T
    (fun k => compensatorIncrement V F mu T C r k) r ?_ omega t ht
  intro k hklt heq
  exact hV.compensatorIncrement_eq_zero_of_grid_time_eq
    (F := F) (mu := mu) r k heq

theorem compensator_grid_condExp_law
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r i : Nat) (hi : i < size T r) :
    mu[gridIncrement V T r i -
      compensatorIncrement V F mu T C r i |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0 := by
  have hGridInt := hV.integrable_gridIncrement (mu := mu) r i hi
  have hCompInt := hV.compensatorIncrement_integrable
    (F := F) (mu := mu) r i
  have hSub := condExp_sub hGridInt hCompInt
    (F ((grid T r).sampledTime i))
  have hRaw := hV.compensatorIncrement_eq_raw_ae
    (F := F) (mu := mu) r i hi
  have hCompMeas := hV.compensatorIncrement_measurable
    (F := F) (mu := mu) r i
  have hCompCE :
      mu[compensatorIncrement V F mu T C r i |
          F ((grid T r).sampledTime i)] =
        compensatorIncrement V F mu T C r i :=
    condExp_of_stronglyMeasurable (F.le _) hCompMeas hCompInt
  filter_upwards [hSub, hRaw] with omega hSub hRaw
  rw [hCompCE] at hSub
  rw [hSub]
  change mu[gridIncrement V T r i |
      F ((grid T r).sampledTime i)] omega -
        compensatorIncrement V F mu T C r i omega = 0
  rw [hRaw]
  rw [show mu[gridIncrement V T r i |
      F ((grid T r).sampledTime i)] =
        rawCompensatorIncrement V F mu T r i by rfl]
  ring

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_terminal_eq_cumulative
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    predictableCompensatorProcess V F mu T C r T =
      compensatorCumulative V F mu T C r (size T r) := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r T =
    finiteGridCompensatorCumulative T
      (fun k => compensatorIncrement V F mu T C r k) r (size T r)
  apply finiteGridPredictableCompensatorProcess_terminal_eq_cumulative
  intro k hklt heq
  exact hV.compensatorIncrement_eq_zero_of_grid_time_eq
    (F := F) (mu := mu) r k heq

omit [IsProbabilityMeasure mu] in
theorem compensatorCumulative_nonneg
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r n : Nat) (omega : Ω) :
    0 ≤ compensatorCumulative V F mu T C r n omega := by
  change 0 ≤ finiteGridCompensatorCumulative T
    (fun k => compensatorIncrement V F mu T C r k) r n omega
  apply finiteGridCompensatorCumulative_nonneg
  intro k omega
  exact hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega

omit [IsProbabilityMeasure mu] in
theorem compensatorCumulative_mono
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r m n : Nat) (hmn : m ≤ n) (omega : Ω) :
    compensatorCumulative V F mu T C r m omega ≤
      compensatorCumulative V F mu T C r n omega := by
  change finiteGridCompensatorCumulative T
      (fun k => compensatorIncrement V F mu T C r k) r m omega ≤
    finiteGridCompensatorCumulative T
      (fun k => compensatorIncrement V F mu T C r k) r n omega
  apply finiteGridCompensatorCumulative_mono
  · exact hmn
  · intro k omega
    exact hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega

omit [IsProbabilityMeasure mu] in
theorem compensatorCumulative_le_index_bound
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r n : Nat) (hn : n ≤ size T r) (omega : Ω) :
    compensatorCumulative V F mu T C r n omega ≤
      (n : Real) * (C : Real) := by
  induction n with
  | zero => simp [compensatorCumulative, finiteGridCompensatorCumulative]
  | succ n ih =>
      have hnlt : n < size T r := lt_of_lt_of_le (Nat.lt_succ_self n) hn
      rw [compensatorCumulative_succ]
      change compensatorCumulative V F mu T C r n omega +
          compensatorIncrement V F mu T C r n omega ≤
        ((n + 1 : Nat) : Real) * (C : Real)
      have hinc := hV.compensatorIncrement_le (F := F) (mu := mu) r n omega
      have hinc' : compensatorIncrement V F mu T C r n omega ≤
          (C : Real) := by simpa using hinc
      have hnonneg : 0 ≤ (C : Real) := by positivity
      have hcast : ((n + 1 : Nat) : Real) = (n : Real) + 1 := by
        norm_num
      rw [hcast]
      nlinarith [ih (Nat.le_trans (Nat.le_succ n) hn), hinc']

omit [IsProbabilityMeasure mu] in
theorem compensatorCumulative_stronglyMeasurable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r n : Nat) :
    StronglyMeasurable[F ((grid T r).sampledTime n)]
      (compensatorCumulative V F mu T C r n) := by
  change StronglyMeasurable[F ((grid T r).sampledTime n)]
    (finiteGridCompensatorCumulative T
      (fun k => compensatorIncrement V F mu T C r k) r n)
  apply finiteGridCompensatorCumulative_stronglyMeasurable
  intro k
  exact hV.compensatorIncrement_measurable (F := F) (mu := mu) r k

theorem compensatorCumulative_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r n : Nat) :
    Integrable (compensatorCumulative V F mu T C r n) mu := by
  unfold compensatorCumulative
  apply integrable_finsetSum
  intro k hk
  exact hV.compensatorIncrement_integrable (F := F) (mu := mu) r k

theorem compensatorCumulative_memLp_two
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r n : Nat) (hn : n ≤ size T r) :
    MemLp (compensatorCumulative V F mu T C r n) (2 : ENNReal) mu := by
  have hC : 0 ≤ (C : Real) := by positivity
  have hBound : ∀ᵐ omega ∂mu,
      ‖compensatorCumulative V F mu T C r n omega‖ ≤
        (n : Real) * (C : Real) := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hV.compensatorCumulative_nonneg (F := F) (mu := mu) r n omega)]
    exact hV.compensatorCumulative_le_index_bound
      (F := F) (mu := mu) r n hn omega
  apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    ((hV.compensatorCumulative_stronglyMeasurable
      (F := F) (mu := mu) r n).mono (F.le _)).aestronglyMeasurable
      ((n : Real) * (C : Real))
  exact hBound

omit [IsProbabilityMeasure mu] in
theorem compensatorCumulative_terminal_sq_identity
    (_hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    (fun omega =>
      (compensatorCumulative V F mu T C r (size T r) omega) ^ 2) =
    (fun omega => ∑ k ∈ Finset.range (size T r),
        (2 * compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega +
          compensatorIncrement V F mu T C r k omega ^ 2)) := by
  change (fun omega =>
      finiteGridCompensatorCumulative T
        (fun k => compensatorIncrement V F mu T C r k) r (size T r) omega ^ 2) =
    (fun omega => ∑ k ∈ Finset.range (size T r),
      (2 * finiteGridCompensatorCumulative T
          (fun k => compensatorIncrement V F mu T C r k) r k omega *
        compensatorIncrement V F mu T C r k omega +
        compensatorIncrement V F mu T C r k omega ^ 2))
  exact finiteGridCompensatorCumulative_terminal_sq_identity T
    (fun k => compensatorIncrement V F mu T C r k) r

theorem compensatorIncrement_sq_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    Integrable (fun omega =>
      compensatorIncrement V F mu T C r k omega ^ 2) mu := by
  have hDInt := hV.compensatorIncrement_integrable
    (F := F) (mu := mu) r k
  have hDMeas := (hV.compensatorIncrement_measurable
    (F := F) (mu := mu) r k).mono (F.le _)
  have hDBound : ∀ᵐ omega ∂mu,
      ‖compensatorIncrement V F mu T C r k omega‖ ≤ (C : Real) := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega)]
    exact hV.compensatorIncrement_le (F := F) (mu := mu) r k omega
  simpa only [pow_two] using hDInt.mul_bdd hDMeas.aestronglyMeasurable hDBound

theorem cumulative_mul_compensator_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    Integrable (fun omega =>
      compensatorCumulative V F mu T C r k omega *
        compensatorIncrement V F mu T C r k omega) mu := by
  have hPInt := hV.compensatorCumulative_integrable
    (F := F) (mu := mu) r k
  have hDMeas := (hV.compensatorIncrement_measurable
    (F := F) (mu := mu) r k).mono (F.le _)
  have hDBound : ∀ᵐ omega ∂mu,
      ‖compensatorIncrement V F mu T C r k omega‖ ≤ (C : Real) := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega)]
    exact hV.compensatorIncrement_le (F := F) (mu := mu) r k omega
  exact hPInt.mul_bdd hDMeas.aestronglyMeasurable hDBound

theorem cumulative_mul_gridIncrement_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    Integrable (fun omega =>
      compensatorCumulative V F mu T C r k omega *
        gridIncrement V T r k omega) mu := by
  have hPInt := hV.compensatorCumulative_integrable
    (F := F) (mu := mu) r k
  have hDeltaLp := hV.increment_memLp_two (mu := mu) r k hk
  have hDeltaBound : ∀ᵐ omega ∂mu,
      ‖gridIncrement V T r k omega‖ ≤ (C : Real) := by
    filter_upwards with omega
    change |V ((grid T r).sampledTime (k + 1)) omega -
      V ((grid T r).sampledTime k) omega| ≤ (C : Real)
    rw [abs_of_nonneg
      (hV.increment_nonneg r k hk omega)]
    exact hV.increment_le_bound r k hk omega
  exact hPInt.mul_bdd hDeltaLp.aestronglyMeasurable hDeltaBound

theorem cumulative_mul_compensator_eq_gridIncrement
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    (∫ omega, compensatorCumulative V F mu T C r k omega *
      compensatorIncrement V F mu T C r k omega ∂mu) =
      ∫ omega, compensatorCumulative V F mu T C r k omega *
        gridIncrement V T r k omega ∂mu := by
  have hPMeas := hV.compensatorCumulative_stronglyMeasurable
    (F := F) (mu := mu) r k
  have hDeltaInt := hV.integrable_gridIncrement (mu := mu) r k hk
  have hPDeltaInt := hV.cumulative_mul_gridIncrement_integrable
    (F := F) (mu := mu) r k hk
  have hRawEq : compensatorIncrement V F mu T C r k =ᵐ[mu]
      mu[((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) |
          F ((grid T r).sampledTime k)] := by
    change compensatorIncrement V F mu T C r k =ᵐ[mu]
      mu[gridIncrement V T r k |
        F ((grid T r).sampledTime k)]
    exact hV.compensatorIncrement_eq_raw_ae
      (F := F) (mu := mu) r k hk
  change (∫ omega, compensatorCumulative V F mu T C r k omega *
      compensatorIncrement V F mu T C r k omega ∂mu) =
    ∫ omega, compensatorCumulative V F mu T C r k omega *
      ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) omega ∂mu
  exact finiteGrid_predictable_cross_term_identity T
    (fun k => compensatorIncrement V F mu T C r k)
    ((grid T r).natSample V)
    (compensatorCumulative V F mu T C r k) r k hRawEq hPMeas hDeltaInt hPDeltaInt

theorem compensatorCumulative_terminal_sq_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    Integrable (fun omega =>
      compensatorCumulative V F mu T C r (size T r) omega ^ 2) mu :=
  (hV.compensatorCumulative_memLp_two (F := F) (mu := mu) r
    (size T r) le_rfl).integrable_sq

theorem integral_compensatorIncrement_sq_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) :
    (∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu) ≤
      (C : Real) * ∫ omega,
        compensatorIncrement V F mu T C r k omega ∂mu := by
  have hDInt := hV.compensatorIncrement_integrable
    (F := F) (mu := mu) r k
  have hDSqInt := hV.compensatorIncrement_sq_integrable
    (F := F) (mu := mu) r k
  have hPoint : ∀ omega,
      compensatorIncrement V F mu T C r k omega ^ 2 ≤
        (C : Real) * compensatorIncrement V F mu T C r k omega := by
    intro omega
    have hnonneg := hV.compensatorIncrement_nonneg
      (F := F) (mu := mu) r k omega
    have hle := hV.compensatorIncrement_le
      (F := F) (mu := mu) r k omega
    have hle' : compensatorIncrement V F mu T C r k omega ≤
        (C : Real) := by simpa using hle
    have hnonneg' : 0 ≤ compensatorIncrement V F mu T C r k omega := by
      simpa using hnonneg
    simpa only [pow_two] using
      (mul_le_mul_of_nonneg_right hle' hnonneg')
  calc
    (∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu) ≤
        ∫ omega, (C : Real) *
          compensatorIncrement V F mu T C r k omega ∂mu :=
      integral_mono_ae hDSqInt (hDInt.const_mul (C : Real))
        (ae_of_all mu hPoint)
    _ = (C : Real) * ∫ omega,
        compensatorIncrement V F mu T C r k omega ∂mu := by
      rw [integral_const_mul]

theorem gridIncrement_sum_eq_terminal
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) (omega : Ω) :
    (∑ k ∈ Finset.range (size T r), gridIncrement V T r k omega) =
      V T omega := by
  have hTel := Finset.sum_range_sub
    (fun k => V ((grid T r).sampledTime k) omega) (size T r)
  calc
    (∑ k ∈ Finset.range (size T r), gridIncrement V T r k omega) =
        ∑ k ∈ Finset.range (size T r),
          (V ((grid T r).sampledTime (k + 1)) omega -
            V ((grid T r).sampledTime k) omega) := by
      rfl
    _ = V ((grid T r).sampledTime (size T r)) omega -
        V ((grid T r).sampledTime 0) omega := hTel
    _ = V T omega - V 0 omega := by
      rw [sampledTime_size]
      have hz : (grid T r).sampledTime 0 = 0 := by
        simp [ChronologicalGrid.sampledTime,
          ChronologicalGrid.natIndex, grid_time]
      rw [hz]
    _ = V T omega := by simp [hV.zero]

omit [IsProbabilityMeasure mu] in
theorem cumulative_gridIncrement_sum_le_terminal_product
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) (omega : Ω) :
    (∑ k ∈ Finset.range (size T r),
      compensatorCumulative V F mu T C r k omega *
        gridIncrement V T r k omega) ≤
      compensatorCumulative V F mu T C r (size T r) omega * V T omega := by
  have hTerm : ∀ k ∈ Finset.range (size T r),
      compensatorCumulative V F mu T C r k omega *
          gridIncrement V T r k omega ≤
        compensatorCumulative V F mu T C r (size T r) omega *
          gridIncrement V T r k omega := by
    intro k hk
    have hklt : k < size T r := Finset.mem_range.mp hk
    have hP : compensatorCumulative V F mu T C r k omega ≤
        compensatorCumulative V F mu T C r (size T r) omega :=
      hV.compensatorCumulative_mono (F := F) (mu := mu) r k
        (size T r) hklt.le omega
    have hDelta : 0 ≤ gridIncrement V T r k omega := by
      exact hV.increment_nonneg r k hklt omega
    exact mul_le_mul_of_nonneg_right hP hDelta
  calc
    (∑ k ∈ Finset.range (size T r),
      compensatorCumulative V F mu T C r k omega *
        gridIncrement V T r k omega) ≤
      ∑ k ∈ Finset.range (size T r),
        compensatorCumulative V F mu T C r (size T r) omega *
          gridIncrement V T r k omega := by
      exact Finset.sum_le_sum hTerm
    _ = compensatorCumulative V F mu T C r (size T r) omega *
        (∑ k ∈ Finset.range (size T r), gridIncrement V T r k omega) := by
      rw [Finset.mul_sum]
    _ = compensatorCumulative V F mu T C r (size T r) omega * V T omega := by
      rw [hV.gridIncrement_sum_eq_terminal r omega]

theorem cumulative_terminal_mul_value_integrable
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    Integrable (fun omega =>
      compensatorCumulative V F mu T C r (size T r) omega * V T omega) mu := by
  have hPInt := hV.compensatorCumulative_integrable
    (F := F) (mu := mu) r (size T r)
  have hVTMeas := (hV.stronglyAdapted T).mono (F.le T)
  have hVTBound : ∀ᵐ omega ∂mu, ‖V T omega‖ ≤ (C : Real) := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.value_nonneg le_rfl omega)]
    exact hV.value_le_bound le_rfl omega
  exact hPInt.mul_bdd hVTMeas.aestronglyMeasurable hVTBound

theorem integral_cumulative_gridIncrement_sum_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    (∫ omega, ∑ k ∈ Finset.range (size T r),
      compensatorCumulative V F mu T C r k omega *
        gridIncrement V T r k omega ∂mu) ≤
      ∫ omega, compensatorCumulative V F mu T C r (size T r) omega *
        V T omega ∂mu := by
  apply integral_mono_ae
  · apply integrable_finsetSum
    intro k hk
    exact hV.cumulative_mul_gridIncrement_integrable
      (F := F) (mu := mu) r k (Finset.mem_range.mp hk)
  · exact hV.cumulative_terminal_mul_value_integrable
      (F := F) (mu := mu) r
  · exact ae_of_all mu (hV.cumulative_gridIncrement_sum_le_terminal_product
      (F := F) (mu := mu) r)

theorem cumulative_terminal_sq_integral_eq_sum
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    (∫ omega, compensatorCumulative V F mu T C r (size T r) omega ^ 2 ∂mu) =
      ∑ k ∈ Finset.range (size T r),
        ∫ omega, (2 * compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega +
          compensatorIncrement V F mu T C r k omega ^ 2) ∂mu := by
  have hTermInt : ∀ k ∈ Finset.range (size T r), Integrable (fun omega =>
      2 * compensatorCumulative V F mu T C r k omega *
          compensatorIncrement V F mu T C r k omega +
        compensatorIncrement V F mu T C r k omega ^ 2) mu := by
    intro k hk
    have hPDInt := hV.cumulative_mul_compensator_integrable
      (F := F) (mu := mu) r k
    have hDSqInt := hV.compensatorIncrement_sq_integrable
      (F := F) (mu := mu) r k
    have hEq :
        (fun omega =>
          2 * compensatorCumulative V F mu T C r k omega *
              compensatorIncrement V F mu T C r k omega +
            compensatorIncrement V F mu T C r k omega ^ 2) =
          (fun omega =>
            2 * (compensatorCumulative V F mu T C r k omega *
                compensatorIncrement V F mu T C r k omega) +
              compensatorIncrement V F mu T C r k omega ^ 2) := by
      funext omega
      ring
    rw [hEq]
    exact (hPDInt.const_mul 2).add hDSqInt
  rw [hV.compensatorCumulative_terminal_sq_identity (F := F) (mu := mu) r]
  exact integral_finsetSum (Finset.range (size T r)) hTermInt

omit [IsProbabilityMeasure mu] in
theorem predictableCompensatorProcess_sampled_increment
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r i : Nat) (hi : i < size T r) :
    (fun omega =>
      predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega) =
      compensatorIncrement V F mu T C r i := by
  change (fun omega =>
      finiteGridPredictableCompensatorProcess T
          (fun k => compensatorIncrement V F mu T C r k) r
          ((grid T r).sampledTime (i + 1)) omega -
        finiteGridPredictableCompensatorProcess T
          (fun k => compensatorIncrement V F mu T C r k) r
          ((grid T r).sampledTime i) omega) =
    compensatorIncrement V F mu T C r i
  refine finiteGridPredictableCompensatorProcess_sampled_increment T
    (fun k => compensatorIncrement V F mu T C r k) r i hi ?_
  intro k hk heq
  exact hV.compensatorIncrement_eq_zero_of_grid_time_eq
    (F := F) (mu := mu) r k heq

theorem residual_grid_condExp_law
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r i : Nat) (hi : i < size T r) :
    mu[(fun omega =>
      (V ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega)) |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0 := by
  have hEq :
      (fun omega =>
        (V ((grid T r).sampledTime (i + 1)) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime (i + 1)) omega) -
        (V ((grid T r).sampledTime i) omega -
          predictableCompensatorProcess V F mu T C r
            ((grid T r).sampledTime i) omega)) =
      gridIncrement V T r i -
        compensatorIncrement V F mu T C r i := by
    funext omega
    have hP := congrFun
      (hV.predictableCompensatorProcess_sampled_increment
        (F := F) (mu := mu) r i hi) omega
    change (V ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega) =
      (V ((grid T r).sampledTime (i + 1)) omega -
        V ((grid T r).sampledTime i) omega) -
        compensatorIncrement V F mu T C r i omega
    rw [sub_eq_iff_eq_add] at hP
    linarith
  rw [hEq]
  exact hV.compensator_grid_condExp_law (F := F) (mu := mu) r i hi

theorem integral_compensatorIncrement_eq_integral_gridIncrement
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r k : Nat) (hk : k < size T r) :
    (∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) =
      ∫ omega, gridIncrement V T r k omega ∂mu := by
  calc
    (∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) =
        ∫ omega, rawCompensatorIncrement V F mu T r k omega ∂mu :=
      integral_congr_ae (hV.compensatorIncrement_eq_raw_ae
        (F := F) (mu := mu) r k hk)
    _ = ∫ omega, gridIncrement V T r k omega ∂mu :=
      integral_condExp (F.le ((grid T r).sampledTime k))

theorem predictableCompensatorProcess_terminal_expectation
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    (∫ omega, predictableCompensatorProcess V F mu T C r T omega ∂mu) =
      ∫ omega, V T omega ∂mu := by
  rw [hV.predictableCompensatorProcess_terminal_eq_cumulative
    (F := F) (mu := mu) r]
  unfold compensatorCumulative finiteGridCompensatorCumulative
  rw [integral_finsetSum]
  · have hSum :
        (∑ k ∈ Finset.range (size T r),
          ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) =
        ∑ k ∈ Finset.range (size T r),
          ∫ omega, gridIncrement V T r k omega ∂mu := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hV.integral_compensatorIncrement_eq_integral_gridIncrement
        (F := F) (mu := mu) r k (Finset.mem_range.mp hk)
    rw [hSum]
    rw [← integral_finsetSum]
    · have hTel :
      (fun omega => ∑ k ∈ Finset.range (size T r),
            gridIncrement V T r k omega) =
            (fun omega => V T omega - V 0 omega) := by
        funext omega
        have hTel := Finset.sum_range_sub
          (fun k => V ((grid T r).sampledTime k) omega) (size T r)
        calc
          (∑ k ∈ Finset.range (size T r), gridIncrement V T r k omega) =
              ∑ k ∈ Finset.range (size T r),
                (V ((grid T r).sampledTime (k + 1)) omega -
                  V ((grid T r).sampledTime k) omega) := by
            rfl
          _ = V ((grid T r).sampledTime (size T r)) omega -
              V ((grid T r).sampledTime 0) omega := hTel
          _ = V T omega - V 0 omega := by
            rw [sampledTime_size]
            have hz : (grid T r).sampledTime 0 = 0 := by
              simp [ChronologicalGrid.sampledTime,
                ChronologicalGrid.natIndex, grid_time]
            rw [hz]
      rw [hTel]
      have hV0 : V 0 = 0 := hV.zero
      simp only [hV0, Pi.zero_apply, sub_zero]
    · intro k hk
      exact hV.integrable_gridIncrement r k (Finset.mem_range.mp hk)
  · intro k hk
    exact hV.compensatorIncrement_integrable
      (F := F) (mu := mu) r k

theorem grid_predictable_testing_identity
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r N : Nat) (hN : N ≤ size T r) (K : Nat → Ω → Real)
    (hK : StronglyAdapted ((grid T r).sampledFiltration F) K)
    (hSourceInt : ∀ k, Integrable
      (K k * ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k)) mu)
    (hCompInt : ∀ k, Integrable
      (K k * compensatorIncrement V F mu T C r k) mu) :
    (∫ omega, discretePredictableIntegral K
        ((grid T r).natSample V) N omega ∂mu) =
      ∫ omega, (∑ k ∈ Finset.range N,
        K k omega * compensatorIncrement V F mu T C r k omega) ∂mu := by
  have hD_raw : ∀ k, k < N →
      compensatorIncrement V F mu T C r k =ᵐ[mu]
        mu[(grid T r).natSample V (k + 1) -
          (grid T r).natSample V k |
            F ((grid T r).sampledTime k)] := by
    intro k hk
    have hklt : k < size T r := hk.trans_le hN
    change compensatorIncrement V F mu T C r k =ᵐ[mu]
      mu[gridIncrement V T r k |
        F ((grid T r).sampledTime k)]
    exact hV.compensatorIncrement_eq_raw_ae (F := F) (mu := mu) r k hklt
  have hMInt : ∀ k, k < N →
      Integrable ((grid T r).natSample V (k + 1) -
        (grid T r).natSample V k) mu := by
    intro k hk
    have hklt : k < size T r := hk.trans_le hN
    change Integrable (gridIncrement V T r k) mu
    exact hV.integrable_gridIncrement (mu := mu) r k hklt
  exact finiteGrid_predictable_testing_identity T
    (fun k => compensatorIncrement V F mu T C r k)
    ((grid T r).natSample V) r N hD_raw K hK hMInt hSourceInt hCompInt

/-! ## The uniform terminal second-moment estimate -/

theorem integral_terminal_value_le
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    (∫ omega, V T omega ∂mu) ≤ (C : Real) := by
  have hVT := hV.value_memLp_two (mu := mu) (t := T) le_rfl
  have hVTInt := hVT.integrable (by norm_num)
  have hCInt : Integrable (fun _ : Ω => (C : Real)) mu :=
    integrable_const _
  calc
    (∫ omega, V T omega ∂mu) ≤
        ∫ omega, (C : Real) ∂mu :=
      integral_mono_ae hVTInt hCInt
        (ae_of_all mu (fun omega => hV.value_le_bound le_rfl omega))
    _ = (C : Real) := by simp

theorem integral_terminal_value_sq_le
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    (∫ omega, (V T omega) ^ 2 ∂mu) ≤ (C : Real) ^ 2 := by
  have hVT := hV.value_memLp_two (mu := mu) (t := T) le_rfl
  have hVTSqInt := hVT.integrable_sq
  have hCSqInt : Integrable (fun _ : Ω => (C : Real) ^ 2) mu :=
    integrable_const _
  have hPoint : ∀ omega, (V T omega) ^ 2 ≤ (C : Real) ^ 2 := by
    intro omega
    have hnonneg := hV.value_nonneg le_rfl omega
    have hle := hV.value_le_bound le_rfl omega
    nlinarith [sq_nonneg (V T omega), sq_nonneg (C : Real)]
  calc
    (∫ omega, (V T omega) ^ 2 ∂mu) ≤
        ∫ omega, (C : Real) ^ 2 ∂mu :=
      integral_mono_ae hVTSqInt hCSqInt (ae_of_all mu hPoint)
    _ = (C : Real) ^ 2 := by simp

omit [IsProbabilityMeasure mu] in
theorem boundedIncreasingProcessData_of_real_bound
    {V : Process Ω} {T : NNReal} {B : Real}
    (hB : 0 ≤ B)
    (hStronglyAdapted : StronglyAdapted F V)
    (hAdapted : Adapted F V)
    (hRightContinuous : ∀ omega t,
      ContinuousWithinAt (V · omega) (Ici t) t)
    (hMonotone : ∀ omega, Monotone (V · omega))
    (hZero : V 0 = 0)
    (hConstantAfter : ∀ omega t, T ≤ t → V t omega = V T omega)
    (hTerminalBound : ∀ omega, 0 ≤ V T omega ∧ V T omega ≤ B) :
    BoundedIncreasingProcessData (F := F) V T B.toNNReal := by
  have hBCoe : (B.toNNReal : Real) = B := Real.coe_toNNReal B hB
  refine {
    stronglyAdapted := hStronglyAdapted
    adapted := hAdapted
    rightContinuous := hRightContinuous
    monotone := hMonotone
    zero := hZero
    constant_after := hConstantAfter
    terminal_bound := ?_ }
  intro omega
  constructor
  · exact (hTerminalBound omega).1
  · rw [hBCoe]
    exact (hTerminalBound omega).2

theorem predictableCompensatorProcess_terminal_sq_integral_le
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (r : Nat) :
    (∫ omega,
      (predictableCompensatorProcess V F mu T C r T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2 := by
  let N := size T r
  have hSqEq := hV.cumulative_terminal_sq_integral_eq_sum
    (F := F) (mu := mu) r
  have hTermSplit : ∀ k ∈ Finset.range N,
      (∫ omega,
        (2 * compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega +
          compensatorIncrement V F mu T C r k omega ^ 2) ∂mu) =
        2 * (∫ omega,
          compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega ∂mu) +
          ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := by
    intro k hk
    have hPDInt := hV.cumulative_mul_compensator_integrable
      (F := F) (mu := mu) r k
    have hDSqInt := hV.compensatorIncrement_sq_integrable
      (F := F) (mu := mu) r k
    calc
      (∫ omega,
          (2 * compensatorCumulative V F mu T C r k omega *
              compensatorIncrement V F mu T C r k omega +
            compensatorIncrement V F mu T C r k omega ^ 2) ∂mu) =
          ∫ omega, 2 *
              (compensatorCumulative V F mu T C r k omega *
                compensatorIncrement V F mu T C r k omega) +
            compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu (fun omega => by ring)
      _ = (∫ omega, 2 *
              (compensatorCumulative V F mu T C r k omega *
                compensatorIncrement V F mu T C r k omega) ∂mu) +
            ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu :=
        integral_add (hPDInt.const_mul 2) hDSqInt
      _ = 2 * (∫ omega,
          compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega ∂mu) +
          ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := by
        rw [integral_const_mul]
  have hSplit :
      (∑ k ∈ Finset.range N,
        ∫ omega,
          (2 * compensatorCumulative V F mu T C r k omega *
              compensatorIncrement V F mu T C r k omega +
            compensatorIncrement V F mu T C r k omega ^ 2) ∂mu) =
        2 * (∑ k ∈ Finset.range N,
          ∫ omega, compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega ∂mu) +
        ∑ k ∈ Finset.range N,
          ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := by
    calc
      (∑ k ∈ Finset.range N,
          ∫ omega,
            (2 * compensatorCumulative V F mu T C r k omega *
                compensatorIncrement V F mu T C r k omega +
              compensatorIncrement V F mu T C r k omega ^ 2) ∂mu) =
          ∑ k ∈ Finset.range N,
            (2 * (∫ omega,
              compensatorCumulative V F mu T C r k omega *
                compensatorIncrement V F mu T C r k omega ∂mu) +
              ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hTermSplit k hk
      _ = 2 * (∑ k ∈ Finset.range N,
          ∫ omega, compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega ∂mu) +
          ∑ k ∈ Finset.range N,
            ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hPDReplace :
      (∑ k ∈ Finset.range N,
        ∫ omega, compensatorCumulative V F mu T C r k omega *
          compensatorIncrement V F mu T C r k omega ∂mu) =
      ∑ k ∈ Finset.range N,
        ∫ omega, compensatorCumulative V F mu T C r k omega *
          gridIncrement V T r k omega ∂mu := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hV.cumulative_mul_compensator_eq_gridIncrement
      (F := F) (mu := mu) r k (by
        simpa [N] using (Finset.mem_range.mp hk))
  have hSqBound :
      (∑ k ∈ Finset.range N,
        ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu) ≤
      (C : Real) *
        (∑ k ∈ Finset.range N,
          ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) := by
    calc
      (∑ k ∈ Finset.range N,
          ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu) ≤
          ∑ k ∈ Finset.range N,
            (C : Real) *
              ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu := by
        apply Finset.sum_le_sum
        intro k hk
        exact hV.integral_compensatorIncrement_sq_le
          (F := F) (mu := mu) r k
      _ = (C : Real) *
          (∑ k ∈ Finset.range N,
            ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) := by
        rw [Finset.mul_sum]
  have hSourceIntegral :
      (∑ k ∈ Finset.range N,
        ∫ omega, compensatorCumulative V F mu T C r k omega *
          gridIncrement V T r k omega ∂mu) =
      ∫ omega, ∑ k ∈ Finset.range N,
        compensatorCumulative V F mu T C r k omega *
          gridIncrement V T r k omega ∂mu := by
    symm
    apply integral_finsetSum
    intro k hk
    exact hV.cumulative_mul_gridIncrement_integrable
      (F := F) (mu := mu) r k (by
        simpa [N] using (Finset.mem_range.mp hk))
  have hSourceBound :
      (∑ k ∈ Finset.range N,
        ∫ omega, compensatorCumulative V F mu T C r k omega *
          gridIncrement V T r k omega ∂mu) ≤
      ∫ omega, compensatorCumulative V F mu T C r N omega *
        V T omega ∂mu := by
    rw [hSourceIntegral]
    exact hV.integral_cumulative_gridIncrement_sum_le (F := F) (mu := mu) r
  have hDIntegral :
      (∑ k ∈ Finset.range N,
        ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) =
      ∫ omega, compensatorCumulative V F mu T C r N omega ∂mu := by
    unfold compensatorCumulative
    symm
    apply integral_finsetSum
    intro k hk
    exact hV.compensatorIncrement_integrable (F := F) (mu := mu) r k
  have hPExpectation :
      (∫ omega, compensatorCumulative V F mu T C r N omega ∂mu) =
      ∫ omega, V T omega ∂mu := by
    calc
      (∫ omega, compensatorCumulative V F mu T C r N omega ∂mu) =
          ∫ omega, predictableCompensatorProcess V F mu T C r T omega ∂mu := by
        rw [hV.predictableCompensatorProcess_terminal_eq_cumulative
          (F := F) (mu := mu) r]
      _ = ∫ omega, V T omega ∂mu :=
        hV.predictableCompensatorProcess_terminal_expectation
          (F := F) (mu := mu) r
  have hMain :
      (∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) ≤
      2 * (∫ omega, compensatorCumulative V F mu T C r N omega *
        V T omega ∂mu) +
        (C : Real) * (∫ omega,
          compensatorCumulative V F mu T C r N omega ∂mu) := by
    calc
      (∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) =
          ∑ k ∈ Finset.range N,
            ∫ omega,
              (2 * compensatorCumulative V F mu T C r k omega *
                  compensatorIncrement V F mu T C r k omega +
                compensatorIncrement V F mu T C r k omega ^ 2) ∂mu := by
        simpa [N] using hSqEq
      _ = 2 * (∑ k ∈ Finset.range N,
          ∫ omega, compensatorCumulative V F mu T C r k omega *
            compensatorIncrement V F mu T C r k omega ∂mu) +
          ∑ k ∈ Finset.range N,
            ∫ omega, compensatorIncrement V F mu T C r k omega ^ 2 ∂mu := hSplit
      _ ≤ 2 * (∑ k ∈ Finset.range N,
          ∫ omega, compensatorCumulative V F mu T C r k omega *
            gridIncrement V T r k omega ∂mu) +
          (C : Real) *
            (∑ k ∈ Finset.range N,
              ∫ omega, compensatorIncrement V F mu T C r k omega ∂mu) := by
        rw [hPDReplace]
        exact add_le_add (le_refl _) hSqBound
      _ ≤ 2 * (∫ omega, compensatorCumulative V F mu T C r N omega *
          V T omega ∂mu) +
          (C : Real) *
            (∫ omega, compensatorCumulative V F mu T C r N omega ∂mu) := by
        rw [hDIntegral]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hSourceBound (by norm_num))
          (le_refl _)
  have hPVInt := hV.cumulative_terminal_mul_value_integrable
    (F := F) (mu := mu) r
  have hP2Int := hV.compensatorCumulative_terminal_sq_integrable
    (F := F) (mu := mu) r
  have hVT := hV.value_memLp_two (mu := mu) (t := T) le_rfl
  have hVTSqInt := hVT.integrable_sq
  have hYoung :
      2 * (∫ omega, compensatorCumulative V F mu T C r N omega *
        V T omega ∂mu) ≤
      (1 / 2 : Real) * (∫ omega,
        compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
      2 * (∫ omega, (V T omega) ^ 2 ∂mu) := by
    have hPoint : ∀ omega,
        2 * (compensatorCumulative V F mu T C r N omega * V T omega) ≤
          (1 / 2 : Real) *
              compensatorCumulative V F mu T C r N omega ^ 2 +
            2 * (V T omega) ^ 2 := by
      intro omega
      nlinarith [sq_nonneg
        (compensatorCumulative V F mu T C r N omega - 2 * V T omega)]
    have hInt := integral_mono_ae (hPVInt.const_mul 2)
      ((hP2Int.const_mul (1 / 2 : Real)).add (hVTSqInt.const_mul 2))
      (ae_of_all mu hPoint)
    calc
      2 * (∫ omega, compensatorCumulative V F mu T C r N omega *
          V T omega ∂mu) =
          ∫ omega, 2 *
            (compensatorCumulative V F mu T C r N omega * V T omega) ∂mu := by
        rw [integral_const_mul]
      _ ≤ ∫ omega, (1 / 2 : Real) *
            compensatorCumulative V F mu T C r N omega ^ 2 +
          2 * (V T omega) ^ 2 ∂mu := hInt
      _ = (1 / 2 : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
          2 * (∫ omega, (V T omega) ^ 2 ∂mu) := by
        rw [integral_add (hP2Int.const_mul (1 / 2 : Real))
          (hVTSqInt.const_mul 2), integral_const_mul, integral_const_mul]
  have hVTermBound :
      (∫ omega, (V T omega) ^ 2 ∂mu) ≤ (C : Real) ^ 2 :=
    hV.integral_terminal_value_sq_le (F := F) (mu := mu)
  have hPTermBound :
      (∫ omega, compensatorCumulative V F mu T C r N omega ∂mu) ≤
      (C : Real) := by
    rw [hPExpectation]
    exact hV.integral_terminal_value_le (F := F) (mu := mu)
  have hC : 0 ≤ (C : Real) := by positivity
  have hCProduct :
      (C : Real) * (∫ omega,
        compensatorCumulative V F mu T C r N omega ∂mu) ≤
      (C : Real) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hPTermBound hC
    nlinarith
  have hHalf :
      (1 / 2 : Real) * (∫ omega,
        compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
        2 * (∫ omega, (V T omega) ^ 2 ∂mu) ≤
      (1 / 2 : Real) * (∫ omega,
        compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
        2 * (C : Real) ^ 2 := by
    gcongr
  have hMain' :
      (∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) ≤
      (1 / 2 : Real) * (∫ omega,
        compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
        2 * (C : Real) ^ 2 + (C : Real) ^ 2 := by
    calc
      (∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) ≤
          2 * (∫ omega, compensatorCumulative V F mu T C r N omega *
            V T omega ∂mu) +
          (C : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ∂mu) := hMain
      _ ≤ ((1 / 2 : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
          2 * (∫ omega, (V T omega) ^ 2 ∂mu)) +
          (C : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ∂mu) :=
        add_le_add hYoung (le_refl _)
      _ ≤ ((1 / 2 : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
          2 * (C : Real) ^ 2) + (C : Real) ^ 2 := by
        exact add_le_add hHalf hCProduct
      _ = (1 / 2 : Real) * (∫ omega,
            compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) +
          2 * (C : Real) ^ 2 + (C : Real) ^ 2 := by ring
  have hCumBound :
      (∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu) ≤
      6 * (C : Real) ^ 2 := by
    nlinarith [hMain', sq_nonneg (C : Real)]
  calc
    (∫ omega,
        (predictableCompensatorProcess V F mu T C r T omega) ^ 2 ∂mu) =
        ∫ omega, compensatorCumulative V F mu T C r N omega ^ 2 ∂mu := by
      rw [hV.predictableCompensatorProcess_terminal_eq_cumulative
        (F := F) (mu := mu) r]
    _ ≤ 8 * (C : Real) ^ 2 := by
      nlinarith [hCumBound, sq_nonneg (C : Real)]

/-! ## Public row certificate and producers -/

structure FactorialGridPredictableCompensatorRowsData
    (hV : BoundedIncreasingProcessData (F := F) V T C) where
  increment_nonneg : ∀ r k omega,
    0 ≤ compensatorIncrement V F mu T C r k omega
  increment_measurable : ∀ r k,
    StronglyMeasurable[F ((grid T r).sampledTime k)]
      (compensatorIncrement V F mu T C r k)
  increment_eq_raw_ae : ∀ r k, k < size T r →
    compensatorIncrement V F mu T C r k =ᵐ[mu]
      rawCompensatorIncrement V F mu T r k
  process_predictable : ∀ r,
    IsStronglyPredictable F (predictableCompensatorProcess V F mu T C r)
  process_zero : ∀ r,
    predictableCompensatorProcess V F mu T C r 0 = 0
  process_nonneg : ∀ r t omega,
    0 ≤ predictableCompensatorProcess V F mu T C r t omega
  process_mono : ∀ r omega,
    Monotone (predictableCompensatorProcess V F mu T C r · omega)
  process_constant_after : ∀ r omega t, T ≤ t →
    predictableCompensatorProcess V F mu T C r t omega =
      predictableCompensatorProcess V F mu T C r T omega
  process_terminal_eq_cumulative : ∀ r,
    predictableCompensatorProcess V F mu T C r T =
      compensatorCumulative V F mu T C r (size T r)
  process_sampled_increment : ∀ r i, i < size T r →
    (fun omega =>
      predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega) =
      compensatorIncrement V F mu T C r i
  residual_grid_condExp_law : ∀ r i, i < size T r →
    mu[(fun omega =>
      (V ((grid T r).sampledTime (i + 1)) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime (i + 1)) omega) -
      (V ((grid T r).sampledTime i) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime i) omega)) |
        F ((grid T r).sampledTime i)] =ᵐ[mu] 0
  terminal_expectation : ∀ r,
    (∫ omega, predictableCompensatorProcess V F mu T C r T omega ∂mu) =
      ∫ omega, V T omega ∂mu
  testing_identity : ∀ (r N : Nat), N ≤ size T r →
    ∀ (K : Nat → Ω → Real),
      StronglyAdapted ((grid T r).sampledFiltration F) K →
      (∀ k, Integrable
        (K k * ((grid T r).natSample V (k + 1) -
          (grid T r).natSample V k)) mu) →
      (∀ k, Integrable
        (K k * compensatorIncrement V F mu T C r k) mu) →
      (∫ omega, discretePredictableIntegral K
        ((grid T r).natSample V) N omega ∂mu) =
        ∫ omega, (∑ k ∈ Finset.range N,
          K k omega * compensatorIncrement V F mu T C r k omega) ∂mu
  terminal_memLp_two : ∀ r,
    MemLp (predictableCompensatorProcess V F mu T C r T)
      (2 : ENNReal) mu
  terminal_L2_bound : ∀ r,
    (∫ omega,
      (predictableCompensatorProcess V F mu T C r T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2

theorem factorialGridPredictableCompensatorRows_producer
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    Nonempty (FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV) := by
  refine ⟨{
    increment_nonneg := ?_,
    increment_measurable := ?_,
    increment_eq_raw_ae := ?_,
    process_predictable := ?_,
    process_zero := ?_,
    process_nonneg := ?_,
    process_mono := ?_,
    process_constant_after := ?_,
    process_terminal_eq_cumulative := ?_,
    process_sampled_increment := ?_,
    residual_grid_condExp_law := ?_,
    terminal_expectation := ?_,
    testing_identity := ?_,
    terminal_memLp_two := ?_,
    terminal_L2_bound := ?_ }⟩
  · intro r k omega
    exact hV.compensatorIncrement_nonneg (F := F) (mu := mu) r k omega
  · intro r k
    exact hV.compensatorIncrement_measurable (F := F) (mu := mu) r k
  · intro r k hk
    exact hV.compensatorIncrement_eq_raw_ae (F := F) (mu := mu) r k hk
  · intro r
    exact hV.predictableCompensatorProcess_isStronglyPredictable
      (F := F) (mu := mu) r
  · intro r
    exact hV.predictableCompensatorProcess_zero (F := F) (mu := mu) r
  · intro r t omega
    exact hV.predictableCompensatorProcess_nonneg
      (F := F) (mu := mu) r t omega
  · intro r omega
    exact hV.predictableCompensatorProcess_mono
      (F := F) (mu := mu) r omega
  · intro r omega t ht
    exact hV.predictableCompensatorProcess_constant_after
      (F := F) (mu := mu) r omega t ht
  · intro r
    exact hV.predictableCompensatorProcess_terminal_eq_cumulative
      (F := F) (mu := mu) r
  · intro r i hi
    exact hV.predictableCompensatorProcess_sampled_increment
      (F := F) (mu := mu) r i hi
  · intro r i hi
    exact hV.residual_grid_condExp_law (F := F) (mu := mu) r i hi
  · intro r
    exact hV.predictableCompensatorProcess_terminal_expectation
      (F := F) (mu := mu) r
  · intro r N hN K hK hSourceInt hCompInt
    exact hV.grid_predictable_testing_identity
      (F := F) (mu := mu) r N hN K hK hSourceInt hCompInt
  · intro r
    rw [hV.predictableCompensatorProcess_terminal_eq_cumulative
      (F := F) (mu := mu) r]
    exact hV.compensatorCumulative_memLp_two
      (F := F) (mu := mu) r (size T r) le_rfl
  · intro r
    exact hV.predictableCompensatorProcess_terminal_sq_integral_le
      (F := F) (mu := mu) r

/-! The regularized common-stop package supplies two such inputs.  Its
terminal estimate is real-valued, so the consumer first records its
nonnegativity and changes it to the corresponding `NNReal` bound explicitly. -/

theorem exists_factorialGridPredictableCompensatorRows_of_commonStopJordanComponents
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Ω → WithTop NNReal}
    {alpha : Ω → WithTop NNReal} {R : Ω → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ hPlus : BoundedIncreasingProcessData (F := F) Aplus T
        (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
      ∃ hMinus : BoundedIncreasingProcessData (F := F) Aminus T
          (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
        Nonempty (FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hPlus) ∧
        Nonempty (FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hMinus) := by
  have hBound : 0 ≤ commonStoppedRowsResidualVariationBound a source.bound := by
    dsimp [commonStoppedRowsResidualVariationBound]
    have ha : 0 < a := endpoint.a_pos
    positivity
  have hPlus : BoundedIncreasingProcessData (F := F) Aplus T
      (commonStoppedRowsResidualVariationBound a source.bound).toNNReal :=
    boundedIncreasingProcessData_of_real_bound
      (F := F) hBound hReg.jordanPositive_stronglyAdapted
      hReg.jordanPositive_adapted hReg.jordanPositive_rightContinuous
      hReg.jordanPositive_monotone hReg.jordanPositive_zero
      hReg.jordanPositive_constant_after hReg.jordanPositive_terminal_bound
  have hMinus : BoundedIncreasingProcessData (F := F) Aminus T
      (commonStoppedRowsResidualVariationBound a source.bound).toNNReal :=
    boundedIncreasingProcessData_of_real_bound
      (F := F) hBound hReg.jordanNegative_stronglyAdapted
      hReg.jordanNegative_adapted hReg.jordanNegative_rightContinuous
      hReg.jordanNegative_monotone hReg.jordanNegative_zero
      hReg.jordanNegative_constant_after hReg.jordanNegative_terminal_bound
  exact ⟨hPlus, hMinus,
    factorialGridPredictableCompensatorRows_producer
      (F := F) (mu := mu) hPlus,
    factorialGridPredictableCompensatorRows_producer
      (F := F) (mu := mu) hMinus⟩

end BoundedIncreasingProcessData

end HorizonFactorialGrid

end FTAPTheorem42
