/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingOptionalSamplingCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.RowControl

/-!
# Source-independent right rounding of stopping times on factorial grids

For a finite stopping time `τ ≤ T`, this file records the finite-grid
stopping index obtained by rounding `τ` upward and clamping at `T`.  The
index is a stopping time for the pulled-back grid filtration.  The associated
time is squeezed between `τ` and `T`, converges to `τ`, and satisfies the
mesh estimate needed for a common tail convexification.

No source or compensator row is imported here.  The activation identity for
finite-grid compensator rows is kept in the bounded adapter module.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {τ : Ω → NNReal} {T : NNReal}

/-! ## The rounded time and its finite grid index -/

/-- The level-`r` right-rounded time, clamped at the fixed horizon. -/
noncomputable def rightRoundedTime (T : NNReal) (τ : Ω → NNReal) (r : Nat) :
    Ω → NNReal :=
  fun omega => min (StoppingTimeRightApproximation.approx r τ omega) T

/-- The natural index of the first factorial-grid point at or after `τ`.

The `min` makes this definition total even before a bound on `τ` is supplied;
under `τ ≤ T` it is the value of the finite-horizon `approxIndex`. -/
noncomputable def rightRoundedIndex (T : NNReal) (τ : Ω → NNReal) (r : Nat) :
    Ω → Nat :=
  fun omega => min
    (Nat.ceil (τ omega * (r.factorial : NNReal)))
    (size T r)

/-- The same rounded index as a finite grid index. -/
noncomputable def rightRoundedFinIndex (T : NNReal) (τ : Ω → NNReal) (r : Nat) :
    Ω → Fin (size T r + 1) :=
  fun omega =>
    ⟨rightRoundedIndex T τ r omega,
      Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [MeasurableSpace Ω] in
theorem rightRoundedIndex_le_size (r : Nat) (omega : Ω) :
    rightRoundedIndex T τ r omega ≤ size T r := by
  exact min_le_right _ _

omit [MeasurableSpace Ω] in
theorem rightRoundedFinIndex_eq_approxIndex
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    rightRoundedFinIndex T τ r omega =
      approxIndex T (τ omega) (hτT omega) r := by
  apply Fin.ext
  have hceil : Nat.ceil (τ omega * (r.factorial : NNReal)) ≤ size T r := by
    exact Nat.le_of_lt_succ (approxIndex T (τ omega) (hτT omega) r).isLt
  simp only [rightRoundedFinIndex, rightRoundedIndex, approxIndex,
    min_eq_left hceil]

omit [MeasurableSpace Ω] in
theorem rightRoundedTime_eq_grid_time
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    rightRoundedTime T τ r omega =
      (grid T r).time (rightRoundedFinIndex T τ r omega) := by
  rw [rightRoundedFinIndex_eq_approxIndex hτT r omega]
  simpa only [rightRoundedTime, StoppingTimeRightApproximation.approx] using
    (grid_time_approxIndex T (τ omega) (hτT omega) r).symm

omit [MeasurableSpace Ω] in
theorem rightRoundedTime_eq_sampledTime_index
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    rightRoundedTime T τ r omega =
      (grid T r).sampledTime (rightRoundedIndex T τ r omega) := by
  have hIndex := rightRoundedIndex_le_size (T := T) (τ := τ) r omega
  have hFin : (grid T r).natIndex (rightRoundedIndex T τ r omega) =
      rightRoundedFinIndex T τ r omega := by
    apply Fin.ext
    simp only [ChronologicalGrid.natIndex, rightRoundedFinIndex,
      rightRoundedIndex]
    rw [min_eq_left (min_le_right _ _)]
  calc
    rightRoundedTime T τ r omega =
        (grid T r).time (rightRoundedFinIndex T τ r omega) :=
      rightRoundedTime_eq_grid_time hτT r omega
    _ = (grid T r).time
        ((grid T r).natIndex (rightRoundedIndex T τ r omega)) := by
      rw [hFin]
    _ = (grid T r).sampledTime (rightRoundedIndex T τ r omega) := rfl

/-! ## Stopping-time and mesh properties -/

theorem rightRoundedTime_isStoppingTime
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (r : Nat) :
    IsStoppingTime F
      (fun omega => (rightRoundedTime T τ r omega : WithTop NNReal)) := by
  have hApprox := StoppingTimeRightApproximation.isStoppingTime hτ r
  have hMin := hApprox.min (isStoppingTime_const F T)
  simpa only [rightRoundedTime, StoppingTimeRightApproximation.approx,
    WithTop.coe_min] using hMin

omit [MeasurableSpace Ω] in
theorem rightRoundedTime_bounds
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    τ omega ≤ rightRoundedTime T τ r omega ∧
      rightRoundedTime T τ r omega ≤ T := by
  constructor
  · exact le_min (StoppingTimeRightApproximation.le_approx r τ omega)
      (hτT omega)
  · exact min_le_right _ _

omit [MeasurableSpace Ω] in
theorem rightRoundedTime_mesh_bound
    (r : Nat) (omega : Ω) :
    rightRoundedTime T τ r omega ≤
      τ omega + (r.factorial : NNReal)⁻¹ := by
  unfold rightRoundedTime StoppingTimeRightApproximation.approx
  exact (min_le_left _ _).trans
    (FactorialChronologicalGrid.approx_le_add_inv_factorial r (τ omega))

omit [MeasurableSpace Ω] in
theorem rightRoundedTime_mesh_bound_of_le
    (n r : Nat) (hnr : n ≤ r) (omega : Ω) :
    rightRoundedTime T τ r omega ≤
      τ omega + (n.factorial : NNReal)⁻¹ := by
  have hfactorial : (n.factorial : NNReal) ≤ (r.factorial : NNReal) := by
    exact_mod_cast Nat.factorial_le hnr
  have hinv : (r.factorial : NNReal)⁻¹ ≤
      (n.factorial : NNReal)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hfactorial
  have hsum : τ omega + (r.factorial : NNReal)⁻¹ ≤
      τ omega + (n.factorial : NNReal)⁻¹ := by
    simpa only [add_comm] using add_le_add_left hinv (τ omega)
  exact (rightRoundedTime_mesh_bound (T := T) (τ := τ) r omega).trans hsum

/-! ## The discrete stopping index -/

omit [MeasurableSpace Ω] in
theorem rightRoundedIndex_le_iff_sampledTime
    (hτT : ∀ omega, τ omega ≤ T) (r k : Nat) :
    {omega | rightRoundedIndex T τ r omega ≤ k} =
      {omega | τ omega ≤ (grid T r).sampledTime k} := by
  ext omega
  by_cases hsize : size T r ≤ k
  · have hIndex : rightRoundedIndex T τ r omega ≤ k :=
      (rightRoundedIndex_le_size (T := T) (τ := τ) r omega).trans hsize
    have hTime : (grid T r).sampledTime k = T := by
      have hmono := (grid T r).sampledTime_mono hsize
      rw [sampledTime_size] at hmono
      have hle : (grid T r).sampledTime k ≤ T := by
        unfold ChronologicalGrid.sampledTime
        rw [grid_time]
        exact min_le_right _ _
      exact le_antisymm hle hmono
    simp only [Set.mem_ofPred_eq, hIndex, true_iff, hTime]
    exact hτT omega
  · have hkSize : k < size T r := Nat.lt_of_not_ge hsize
    have hkLe : k ≤ size T r := hkSize.le
    constructor
    · intro hIndex
      have hTimeQ : (grid T r).sampledTime
          (rightRoundedIndex T τ r omega) =
          rightRoundedTime T τ r omega := by
        exact (rightRoundedTime_eq_sampledTime_index
          (T := T) (τ := τ) hτT r omega).symm
      have hτQ : τ omega ≤ (grid T r).sampledTime
          (rightRoundedIndex T τ r omega) := by
        rw [hTimeQ]
        exact (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).1
      have hqk : rightRoundedIndex T τ r omega ≤ k := hIndex
      have hgrid := (grid T r).sampledTime_mono hqk
      exact hτQ.trans hgrid
    · intro hτk
      have hTimeT : (grid T r).sampledTime k ≤ T := by
        unfold ChronologicalGrid.sampledTime
        rw [grid_time]
        exact min_le_right _ _
      have hIndexMono :
          approxIndex T (τ omega) (hτT omega) r ≤
            approxIndex T ((grid T r).sampledTime k) hTimeT r := by
        change Nat.ceil (τ omega * (r.factorial : NNReal)) ≤
          Nat.ceil ((grid T r).sampledTime k * (r.factorial : NNReal))
        exact Nat.ceil_mono
          (mul_le_mul_of_nonneg_right hτk (by positivity))
      have hApproxIndexLe :
          (approxIndex T ((grid T r).sampledTime k) hTimeT r).1 ≤ k := by
        change Nat.ceil ((grid T r).sampledTime k *
          (r.factorial : NNReal)) ≤ k
        unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
        simp only [grid_time, min_eq_left hkLe]
        by_cases hkt : (k : NNReal) / (r.factorial : NNReal) ≤ T
        · rw [min_eq_left hkt]
          have hfac : (r.factorial : NNReal) ≠ 0 := by positivity
          rw [div_mul_cancel₀ _ hfac, Nat.ceil_natCast]
        · have hT : T ≤ (k : NNReal) / (r.factorial : NNReal) :=
            le_of_not_ge hkt
          rw [min_eq_right hT]
          apply Nat.ceil_le.mpr
          exact_mod_cast
            ((le_div_iff₀ (show (0 : NNReal) < (r.factorial : NNReal) by
              positivity)).mp hT)
      have hIndexLeApprox :
          rightRoundedIndex T τ r omega ≤
            (approxIndex T ((grid T r).sampledTime k) hTimeT r).1 := by
        have hEq := rightRoundedFinIndex_eq_approxIndex
          (T := T) (τ := τ) hτT r omega
        have hOrder : rightRoundedFinIndex T τ r omega ≤
            approxIndex T ((grid T r).sampledTime k) hTimeT r := by
          rw [hEq]
          exact hIndexMono
        change rightRoundedIndex T τ r omega ≤
          (approxIndex T ((grid T r).sampledTime k) hTimeT r).1
        exact hOrder
      exact hIndexLeApprox.trans hApproxIndexLe

theorem rightRoundedIndex_isStoppingTime
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    IsStoppingTime ((grid T r).sampledFiltration F)
      (fun omega => (rightRoundedIndex T τ r omega : WithTop Nat)) := by
  intro k
  have hMeas :
      MeasurableSet[((grid T r).sampledFiltration F) k]
        {omega | rightRoundedIndex T τ r omega ≤ k} := by
    rw [rightRoundedIndex_le_iff_sampledTime
      (T := T) (τ := τ) hτT r k]
    have hEq :
        {omega | τ omega ≤ (grid T r).sampledTime k} =
          {omega | (τ omega : WithTop NNReal) ≤
            ((grid T r).sampledTime k : WithTop NNReal)} := by
      ext omega
      change τ omega ≤ (grid T r).sampledTime k ↔
        (τ omega : WithTop NNReal) ≤
          ((grid T r).sampledTime k : WithTop NNReal)
      exact (WithTop.coe_le_coe).symm
    rw [hEq]
    change MeasurableSet[F ((grid T r).sampledTime k)]
      {omega | (τ omega : WithTop NNReal) ≤
        ((grid T r).sampledTime k : WithTop NNReal)}
    exact hτ ((grid T r).sampledTime k)
  have hEq :
      {omega | rightRoundedIndex T τ r omega ≤ k} =
        {omega | (rightRoundedIndex T τ r omega : WithTop Nat) ≤
          (k : WithTop Nat)} := by
    ext omega
    change rightRoundedIndex T τ r omega ≤ k ↔
      (rightRoundedIndex T τ r omega : WithTop Nat) ≤ (k : WithTop Nat)
    exact (WithTop.coe_le_coe).symm
  change MeasurableSet[((grid T r).sampledFiltration F) k]
    {omega | (rightRoundedIndex T τ r omega : WithTop Nat) ≤ (k : WithTop Nat)}
  rw [← hEq]
  exact hMeas

end HorizonFactorialGrid

/-!
## Bounded finite-grid compensator activation at right-rounded times

The source-independent right-rounding API is provided by the core module.
This adapter records the left-endpoint activation identity for bounded
finite-grid compensator rows:
`P t = ∑ k, d k * 1_{t_k < t}`.  Hence the row has the same value at `τ`
and at its first grid point to the right.  No optional-sampling theorem is
proved here; the finite discrete stopping index is provided for the next
boundary.
-/

namespace HorizonFactorialGrid

/-! ## Left-endpoint activation -/

theorem predictableCompensatorProcess_at_tau_eq_at_rightRoundedTime
    (V : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) (omega : Ω) :
    predictableCompensatorProcess V F mu T C r (τ omega) omega =
      predictableCompensatorProcess V F mu T C r
        (rightRoundedTime T τ r omega) omega := by
  change finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r
      (τ omega) omega =
    finiteGridPredictableCompensatorProcess T
      (fun k => compensatorIncrement V F mu T C r k) r
      (rightRoundedTime T τ r omega) omega
  exact finiteGridPredictableCompensatorProcess_at_tau_eq_at_gridTime
    T τ (rightRoundedTime T τ r) (rightRoundedIndex T τ r)
    (fun k => compensatorIncrement V F mu T C r k) r omega
    (fun omega => rightRoundedTime_eq_sampledTime_index
      (T := T) (τ := τ) hτT r omega)
    (fun omega => by
      rw [← rightRoundedTime_eq_sampledTime_index
        (T := T) (τ := τ) hτT r omega]
      exact (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).1)
    (fun omega => rightRoundedIndex_le_size (T := T) (τ := τ) r omega)
    (fun omega => by
      have hceil : Nat.ceil (τ omega * (r.factorial : NNReal)) ≤ size T r := by
        exact Nat.le_of_lt_succ
          (approxIndex T (τ omega) (hτT omega) r).isLt
      dsimp [rightRoundedIndex]
      rw [min_eq_left hceil])
    (fun k _hk hGridEq => by
      simp [compensatorIncrement, hGridEq])

end HorizonFactorialGrid

end FTAPTheorem42
