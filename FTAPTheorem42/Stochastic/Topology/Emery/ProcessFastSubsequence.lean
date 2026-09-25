/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessCauchy

/-! # Recovering ucp control from elementary tests

The horizon unit test detects increments. Common initial values are therefore
explicit hypotheses when recovering control of the processes themselves.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}

/-- On the stopped grids the unit test is exactly the centered source.
No path regularity is needed for this identity. -/
theorem elementaryEmeryTestError_horizonUnit {X Y : Process Ω}
    (hInitial : X 0 =ᵐ[μ] Y 0) (T : NNReal) :
    elementaryEmeryTestError X Y
      (BoundedPredictableElementaryMultiplier.horizonUnit (ℱ := F) T) T =ᵐ[μ]
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => X t w - Y t w) T := by
  filter_upwards [hInitial] with w hw
  unfold elementaryEmeryTestError
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  congr 2
  apply iSup_congr
  intro r
  congr 1
  unfold FactorialChronologicalGrid.factorialRunningMax
  apply Finset.sup'_congr
  · rfl
  · intro k hk
    have ht : (FactorialChronologicalGrid.stoppedGrid T r).sampledTime k ≤ T := by
      simp only [ChronologicalGrid.sampledTime, FactorialChronologicalGrid.stoppedGrid_time]
      exact min_le_right _ _
    simp only [ChronologicalGrid.natSample,
      BoundedPredictableElementaryMultiplier.horizonUnit,
      PredictableElementaryStrategy.toElementary, List.map_cons, List.map_nil,
      ElementaryStrategy.gain, List.sum_cons, List.sum_nil, add_zero,
      ElementaryInterval.gain,
      FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.horizonBlock,
      min_eq_left ht, min_zero, one_mul, hw, sub_sub_sub_cancel_right]

/-- Uniform test Cauchy control also controls the untested process on every
finite horizon, provided the initial values agree. -/
theorem ElementaryEmeryCauchy.ucp_integral_cauchy
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0) :
    ∀ T : NNReal, ∀ ε > (0 : Real), ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X m t w - X n t w) T w ∂μ ≤ ε := by
  intro T ε hε
  obtain ⟨N, hN⟩ := h T ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [← integral_congr_ae
    (elementaryEmeryTestError_horizonUnit (F := F)
      ((hInitial m).trans (hInitial n).symm) T)]
  exact hN m hm n hn _

variable [IsProbabilityMeasure μ]

/-- Test convergence implies the capped-grid ucp criterion with a common
initial value. The grid statement needs no regularity; for right-continuous
paths these grids detect the whole finite-horizon supremum. -/
theorem ElementaryEmeryConverges.ucp
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hInitial : ∀ n, X n 0 =ᵐ[μ] Y 0) (T : NNReal) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X n t w - Y t w) T) atTop (fun _ => (0 : Real)) := by
  exact (h.test_convergence hX hY
    (BoundedPredictableElementaryMultiplier.horizonUnit (ℱ := F) T) T).congr
    (fun n => elementaryEmeryTestError_horizonUnit (F := F) (hInitial n) T) (EventuallyEq.refl _ _)

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## A pathwise fast subsequence from uniform elementary-test Cauchy control

Markov's inequality and Borel--Cantelli give summable adjacent differences
on growing horizons. This construction uses no fixed-source graph closure.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One subsequence controls all finite horizons on a common exceptional
set: eventually its consecutive differences on `[0,k+1]` are at most
`2^(-k-1)`. -/
theorem ElementaryEmeryCauchy.exists_fast_subsequence
    {X : Nat → Process Ω} (h : ElementaryEmeryCauchy μ F X)
    (hX : ∀ n, IsStronglyProgressive F (X n))
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hInitial : ∀ n, X n 0 =ᵐ[μ] X 0 0) :
    ∃ f : Nat → Nat, StrictMono f ∧
      ∀ᵐ w ∂μ, ∀ᶠ k in atTop, ∀ t : NNReal, t ≤ ((k + 1 : Nat) : NNReal) →
        |X (f (k + 1)) t w - X (f k) t w| ≤ ((1 : Real) / 2) ^ (k + 1) := by
  classical
  let q : Nat → Real := fun k => ((1 : Real) / 2) ^ (k + 1)
  have hq k : 0 < q k := by positivity
  have hq1 k : q k < 1 := pow_lt_one₀ (by positivity) (by norm_num) (Nat.succ_ne_zero k)
  obtain ⟨N, hN⟩ : ∃ N : Nat → Nat, ∀ k m, N k ≤ m → ∀ n, N k ≤ n →
      ∫ w, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X m t w - X n t w) ((k + 1 : Nat) : NNReal) w ∂μ ≤ q k * q k := by
    choose N hN using fun k => h.ucp_integral_cauchy hInitial
      ((k + 1 : Nat) : NNReal) (q k * q k) (mul_pos (hq k) (hq k))
    exact ⟨N, hN⟩
  let f : Nat → Nat := fun k => Nat.rec (N 0)
    (fun i previous => max (previous + 1) (N (i + 1))) k
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun k =>
    (Nat.lt_succ_self (f k)).trans_le (le_max_left _ _)
  have hNf k : N k ≤ f k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  let E : Nat → Ω → Real := fun k =>
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => X (f (k + 1)) t w - X (f k) t w) ((k + 1 : Nat) : NNReal)
  have hE k : StronglyMeasurable (E k) :=
    (FactorialChronologicalGrid.stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope
      ((hX (f (k + 1))).stronglyAdapted.sub (hX (f k)).stronglyAdapted) _).mono (F.le _)
  have hE0 k w : 0 ≤ E k w :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg _ _ _
  have hEi k : Integrable (E k) μ :=
    (integrable_const (1 : Real)).mono' (hE k).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hE0 k w)]
        exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one _ _ _)
  let bad : Nat → Set Ω := fun k => {w | q k ≤ E k w}
  have hBad k : μ (bad k) ≤ ENNReal.ofReal (q k) := by
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall (hE0 k)) (hEi k) (q k)
    have hInt := hN k (f (k + 1)) ((hNf k).trans (hf.monotone (Nat.le_succ k)))
      (f k) (hNf k)
    have hReal : μ.real (bad k) ≤ q k := by
      apply (mul_le_mul_iff_right₀ (hq k)).mp
      exact hMarkov.trans hInt
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using
      ENNReal.ofReal_le_ofReal hReal
  have hSummable : Summable q := by
    simpa [q, pow_succ, mul_comm] using
      (summable_geometric_two.mul_left ((1 : Real) / 2))
  have hBadSum : (∑' k, μ (bad k)) ≠ ∞ :=
    ne_top_of_le_ne_top hSummable.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hBad)
  refine ⟨f, hf, ?_⟩
  filter_upwards [MeasureTheory.ae_eventually_notMem (μ := μ) (s := bad) hBadSum] with w hw
  filter_upwards [hw] with k hk
  intro t ht
  have hCap : E k w < q k := lt_of_not_ge hk
  have hEnvelope := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_lt_of_capped_lt
    (fun t w => X (f (k + 1)) t w - X (f k) t w)
    ((k + 1 : Nat) : NNReal) w (hq k).le (hq1 k) hCap
  have hValue := FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
    (fun t w => |X (f (k + 1)) t w - X (f k) t w|) ((k + 1 : Nat) : NNReal)
    (fun w t => ((hXR _ w t).sub (hXR _ w t)).abs) w ht
  exact ((ENNReal.ofReal_lt_ofReal_iff (hq k)).mp (hValue.trans_lt hEnvelope)).le

end FTAPTheorem42
