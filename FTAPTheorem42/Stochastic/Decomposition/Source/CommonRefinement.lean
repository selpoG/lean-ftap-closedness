/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGate

/-!
# Finite common refinements of fixed-horizon factorial grids

This file contains the explicit factorial-grid embedding used by the native
row construction.  If r ≤ q, the coarse index k is sent to
(q.factorial / r.factorial) * k, and the sampled time is preserved.  It does
not transport filtrations or Doob components between grids; any finite-sum
telescoping needed by a later consumer is added with that consumer.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

namespace HorizonFactorialGrid

/-! ## The explicit factorial-grid embedding -/

noncomputable def factorialRatio (r q : Nat) : Nat :=
  q.factorial / r.factorial

theorem factorialRatio_mul (r q : Nat) (hrq : r ≤ q) :
    r.factorial * factorialRatio r q = q.factorial := by
  unfold factorialRatio
  exact Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hrq)

theorem factorialRatio_pos (r q : Nat) (hrq : r ≤ q) :
    0 < factorialRatio r q := by
  have hfac : 0 < q.factorial := Nat.factorial_pos q
  have hmul := factorialRatio_mul r q hrq
  have hleft : 0 < r.factorial := Nat.factorial_pos r
  nlinarith

theorem factorialRatio_mul_size (T : NNReal) (r q : Nat) (hrq : r ≤ q) :
    factorialRatio r q * size T r = size T q := by
  calc
    factorialRatio r q * (Nat.ceil T * r.factorial) =
        Nat.ceil T * (factorialRatio r q * r.factorial) := by
          ac_rfl
    _ = Nat.ceil T * q.factorial := by
      rw [Nat.mul_comm (factorialRatio r q) r.factorial,
        factorialRatio_mul r q hrq]
    _ = size T q := rfl

noncomputable def factorialGridEmbedding
    (T : NNReal) (r q : Nat) (hrq : r ≤ q) :
    Fin (size T r + 1) → Fin (size T q + 1) := fun k =>
  ⟨factorialRatio r q * k.1,
    Nat.lt_succ_of_le (by
      rw [← factorialRatio_mul_size T r q hrq]
      exact Nat.mul_le_mul_left _ (Nat.le_of_lt_succ k.2))⟩

theorem factorialGridEmbedding_time
    (T : NNReal) (r q : Nat) (hrq : r ≤ q)
    (k : Fin (size T r + 1)) :
    (grid T q).time (factorialGridEmbedding T r q hrq k) =
      (grid T r).time k := by
  change min
      ((((factorialRatio r q * k.1 : Nat) : NNReal) /
        (q.factorial : NNReal))) T =
    min ((k.1 : NNReal) / (r.factorial : NNReal)) T
  congr 1
  rw [Nat.cast_mul]
  rw [show (q.factorial : NNReal) =
      (r.factorial : NNReal) * (factorialRatio r q : NNReal) by
        exact_mod_cast (factorialRatio_mul r q hrq).symm]
  have hratio : (factorialRatio r q : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (factorialRatio_pos r q hrq))
  field_simp [show (r.factorial : NNReal) ≠ 0 by positivity,
    hratio]

theorem factorialGridEmbedding_sampledTime
    (T : NNReal) (r q : Nat) (hrq : r ≤ q)
    (k : Nat) (hk : k ≤ size T r) :
    (grid T q).sampledTime
        ((factorialGridEmbedding T r q hrq
          ⟨k, Nat.lt_succ_of_le hk⟩)) =
      (grid T r).sampledTime k := by
  have hsample :
      (grid T r).sampledTime k =
        (grid T r).time ⟨k, Nat.lt_succ_of_le hk⟩ := by
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    simp [hk]
  rw [hsample]
  simpa only [ChronologicalGrid.sampledTime_fin_eq] using
    (show (grid T q).time
        (factorialGridEmbedding T r q hrq
          ⟨k, Nat.lt_succ_of_le hk⟩) =
      (grid T r).time ⟨k, Nat.lt_succ_of_le hk⟩ from
      factorialGridEmbedding_time T r q hrq
        ⟨k, Nat.lt_succ_of_le hk⟩)

end HorizonFactorialGrid

end FTAPTheorem42
