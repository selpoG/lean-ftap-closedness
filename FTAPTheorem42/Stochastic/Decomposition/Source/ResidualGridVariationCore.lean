/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopCadlagMartingaleLimit

/-!
# Source-independent residual grid variation

This module contains the finite-grid notation and coarser-grid transport
shared by the bounded-source and random-envelope common-stop routes.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! ## Finite-grid variation notation and telescoping -/

noncomputable def commonStoppedRowsResidualGridVariation
    (B : Process Omega) (T : NNReal) (r : Nat) : Omega → Real :=
  fun omega =>
    ∑ k ∈ Finset.range (size T r),
      |B ((grid T r).sampledTime (k + 1)) omega -
        B ((grid T r).sampledTime k) omega|

omit [MeasurableSpace Omega] in
theorem commonStoppedRowsResidualGridVariation_transport
    {B : Process Omega} (T : NNReal) (r q : Nat) (hrq : r ≤ q)
    (omega : Omega)
    {V : Real}
    (hVar : commonStoppedRowsResidualGridVariation B T q omega ≤ V) :
    commonStoppedRowsResidualGridVariation B T r omega ≤ V := by
  let m := factorialRatio r q
  let N := size T r
  let A : Nat → Real := fun i => B ((grid T q).sampledTime i) omega
  have htime : ∀ k, k ≤ N →
      (grid T q).sampledTime (m * k) =
        (grid T r).sampledTime k := by
    intro k hk
    simpa [m, factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T r q hrq k hk)
  have hbound :
      ∑ k ∈ Finset.range N,
        |A (m * (k + 1)) - A (m * k)| ≤
        ∑ i ∈ Finset.range (m * N), |A (i + 1) - A i| :=
    native_sum_abs_sub_mul_le m N A
  have hsize : m * N = size T q := by
    dsimp [m, N]
    exact factorialRatio_mul_size T r q hrq
  calc
    commonStoppedRowsResidualGridVariation B T r omega =
        ∑ k ∈ Finset.range N,
          |A (m * (k + 1)) - A (m * k)| := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      have hk0 : k ≤ N := hkN.le
      have hk1 : k + 1 ≤ N := Nat.succ_le_iff.mpr hkN
      simp only [A]
      rw [htime (k + 1) hk1, htime k hk0]
    _ ≤ ∑ i ∈ Finset.range (m * N), |A (i + 1) - A i| := hbound
    _ = commonStoppedRowsResidualGridVariation B T q omega := by
      rw [hsize]
      rfl
    _ ≤ V := hVar

end HorizonFactorialGrid

end FTAPTheorem42
