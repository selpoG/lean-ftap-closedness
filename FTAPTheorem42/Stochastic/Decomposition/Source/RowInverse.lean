/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.NativeExtension
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryStoppingIntegrand
import FTAPTheorem42.Stochastic.Stopping.FiniteTruncation
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval

/-!
# Inverting the native common gate

This module is the market-facing finite-grid bridge for the native stopped
Doob rows.  The only refinement performed here is the finite refinement of
the native *gate coefficients*.  The Doob martingale representatives remain
processes in the original filtration.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Finite support levels -/

noncomputable def rowCommonLevel
    (u : ∀ n, TailConvexWeights n) (n : Nat) : Nat :=
  (u n).support.sup id

theorem rowCommonLevel_ge
    (u : ∀ n, TailConvexWeights n) (n r : Nat)
    (hr : r ∈ (u n).support) : r ≤ rowCommonLevel u n := by
  exact Finset.le_sup (f := (id : Nat → Nat)) hr

noncomputable def rowNativeIndex
    (u : ∀ n, TailConvexWeights n) (n r k : Nat) : Nat :=
  k / factorialRatio r (rowCommonLevel u n)

theorem rowNativeIndex_le
    (u : ∀ n, TailConvexWeights n) (n r k : Nat)
    (hr : r ∈ (u n).support) (hk : k ≤ size T (rowCommonLevel u n)) :
    rowNativeIndex u n r k ≤ size T r := by
  let q := rowCommonLevel u n
  let m := factorialRatio r q
  have hrq : r ≤ q := rowCommonLevel_ge u n r hr
  have hm : 0 < m := factorialRatio_pos r q hrq
  have hsize : m * size T r = size T q :=
    factorialRatio_mul_size T r q hrq
  have hdiv : k / m ≤ size T r := by
    rw [Nat.div_le_iff_le_mul hm]
    have hkprod : k ≤ size T r * m := by
      calc
        k ≤ size T q := by simpa [q] using hk
        _ = m * size T r := hsize.symm
        _ = size T r * m := Nat.mul_comm _ _
    have hkm : k ≤ size T r * m + m - 1 := by
      calc
        k ≤ size T r * m := hkprod
        _ ≤ size T r * m + m - 1 := by omega
    exact hkm
  exact hdiv

theorem rowCommonGrid_sampledTime_nativeIndex_le
    (u : ∀ n, TailConvexWeights n) (n r k : Nat)
    (hr : r ∈ (u n).support) (hk : k ≤ size T (rowCommonLevel u n)) :
    (grid T r).sampledTime (rowNativeIndex u n r k) ≤
      (grid T (rowCommonLevel u n)).sampledTime k := by
  have hrq : r ≤ rowCommonLevel u n := rowCommonLevel_ge u n r hr
  have hm : 0 < factorialRatio r (rowCommonLevel u n) :=
    factorialRatio_pos r _ hrq
  have hdiv : rowNativeIndex u n r k * factorialRatio r
      (rowCommonLevel u n) ≤ k := Nat.div_mul_le_self k _
  have hidx : factorialRatio r (rowCommonLevel u n) *
      rowNativeIndex u n r k ≤ k := by
    simpa [Nat.mul_comm] using hdiv
  unfold ChronologicalGrid.sampledTime
  simp only [ChronologicalGrid.natIndex,
    Nat.min_eq_left (rowNativeIndex_le u n r k hr hk), grid_time]
  rw [Nat.min_eq_left hk]
  change min ((rowNativeIndex u n r k : NNReal) /
      (r.factorial : NNReal)) T ≤
    min ((k : NNReal) /
      ((rowCommonLevel u n).factorial : NNReal)) T
  apply min_le_min
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [show (rowCommonLevel u n).factorial =
      r.factorial * factorialRatio r (rowCommonLevel u n) by
        exact_mod_cast (factorialRatio_mul r (rowCommonLevel u n) hrq).symm]
    simp only [Nat.cast_mul]
    have hdiv' : (rowNativeIndex u n r k : NNReal) *
        (factorialRatio r (rowCommonLevel u n) : NNReal) ≤ k := by
      exact_mod_cast hdiv
    calc
      (rowNativeIndex u n r k : NNReal) *
          ((r.factorial : NNReal) *
            (factorialRatio r (rowCommonLevel u n) : NNReal)) =
          ((rowNativeIndex u n r k : NNReal) *
            (factorialRatio r (rowCommonLevel u n) : NNReal)) *
            (r.factorial : NNReal) := by ring
      _ ≤ (k : NNReal) * (r.factorial : NNReal) := by
        exact mul_le_mul_of_nonneg_right hdiv' (by positivity)
  · exact le_rfl

private theorem rowCommonGrid_sampledTime_mul_eq
    (u : ∀ n, TailConvexWeights n) (n r j : Nat)
    (hr : r ∈ (u n).support) (hj : j ≤ size T r) :
    (grid T (rowCommonLevel u n)).sampledTime
        (factorialRatio r (rowCommonLevel u n) * j) =
      (grid T r).sampledTime j := by
  have hrq : r ≤ rowCommonLevel u n := rowCommonLevel_ge u n r hr
  have hemb := factorialGridEmbedding_sampledTime T r
    (rowCommonLevel u n) hrq j hj
  simpa [factorialGridEmbedding] using hemb

private theorem rowNativeIndex_eq_approxIndex_sub_one
    (u : ∀ n, TailConvexWeights n) (n r k : Nat)
    (hr : r ∈ (u n).support) (hk : k < size T (rowCommonLevel u n))
    (t : NNReal) (htT : t ≤ T)
    (hlo : (grid T (rowCommonLevel u n)).sampledTime k < t)
    (hhi : t ≤ (grid T (rowCommonLevel u n)).sampledTime (k + 1)) :
    (approxIndex T t htT r).1 - 1 = rowNativeIndex u n r k := by
  let q := rowCommonLevel u n
  let m := factorialRatio r q
  have hrq : r ≤ q := rowCommonLevel_ge u n r hr
  have hm : 0 < m := factorialRatio_pos r q hrq
  have hsize : m * size T r = size T q :=
    factorialRatio_mul_size T r q hrq
  have hkq : k ≤ size T q := hk.le
  have hk1q : k + 1 ≤ size T q := Nat.succ_le_of_lt hk
  have htime_k_lt : (grid T q).sampledTime k < T :=
    hlo.trans_le htT
  have htime_k : (grid T q).sampledTime k =
      (k : NNReal) / (q.factorial : NNReal) := by
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    simp only [Nat.min_eq_left hkq, grid_time]
    apply min_eq_left
    have htime_k_lt' := htime_k_lt
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex at htime_k_lt'
    simp only [Nat.min_eq_left hkq, grid_time, min_lt_iff] at htime_k_lt'
    exact htime_k_lt'.resolve_right (lt_irrefl T) |>.le
  have htime_k1 : (grid T q).sampledTime (k + 1) =
      min (((k + 1 : Nat) : NNReal) / (q.factorial : NNReal)) T := by
    unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
    simp only [Nat.min_eq_left hk1q, grid_time]
  have hk_lt_t : (k : NNReal) / (q.factorial : NNReal) < t := by
    have hlo' := hlo
    change (grid T q).sampledTime k < t at hlo'
    rw [htime_k] at hlo'
    exact hlo'
  have ht_le_k1 : t ≤ ((k + 1 : Nat) : NNReal) / (q.factorial : NNReal) := by
    calc
      t ≤ (grid T q).sampledTime (k + 1) := hhi
      _ ≤ ((k + 1 : Nat) : NNReal) / (q.factorial : NNReal) := by
        rw [htime_k1]
        exact min_le_left _ _
  have hqfac : (q.factorial : NNReal) =
      (r.factorial : NNReal) * (m : NNReal) := by
    exact_mod_cast (factorialRatio_mul r q hrq).symm
  have hfacr : 0 < (r.factorial : NNReal) := by positivity
  have hfacq : 0 < (q.factorial : NNReal) := by positivity
  have hmul_lower : (k : NNReal) <
      (t * (r.factorial : NNReal)) * (m : NNReal) := by
    have hmul := (div_lt_iff₀ hfacq).1 hk_lt_t
    rw [hqfac] at hmul
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hlower : ((k / m : Nat) : NNReal) <
      t * (r.factorial : NNReal) := by
    have hquot : (k : NNReal) / (m : NNReal) <
        t * (r.factorial : NNReal) :=
      (div_lt_iff₀ (by exact_mod_cast hm)).2 hmul_lower
    calc
      ((k / m : Nat) : NNReal) ≤ (k : NNReal) / (m : NNReal) := by
        apply (le_div_iff₀ (by exact_mod_cast hm)).2
        exact_mod_cast Nat.div_mul_le_self k m
      _ < t * (r.factorial : NNReal) := hquot
  have hdiv_bound : k + 1 ≤ (k / m + 1) * m := by
    have hrem := Nat.mod_lt k hm
    have hdecomp := Nat.div_add_mod k m
    have hdecomp' : k / m * m + k % m = k := by
      simpa [Nat.mul_comm] using hdecomp
    calc
      k + 1 = k / m * m + k % m + 1 := by rw [hdecomp']
      _ ≤ k / m * m + m := by omega
      _ = (k / m + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
  have hupper : t * (r.factorial : NNReal) ≤
      ((k / m + 1 : Nat) : NNReal) := by
    apply le_of_mul_le_mul_right (a := (m : NNReal))
    · have hmul := (le_div_iff₀ hfacq).1 ht_le_k1
      rw [hqfac] at hmul
      calc
        t * (r.factorial : NNReal) * (m : NNReal) ≤
            ((k + 1 : Nat) : NNReal) := by
          simpa [mul_assoc] using hmul
        _ ≤ ((k / m + 1 : Nat) : NNReal) * (m : NNReal) := by
          exact_mod_cast hdiv_bound
    · exact_mod_cast hm
  have hceil : Nat.ceil (t * (r.factorial : NNReal)) = k / m + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero (k / m))).2
    constructor
    · simpa only [Nat.succ_sub_one, Nat.cast_id] using hlower
    · exact_mod_cast hupper
  change Nat.ceil (t * (r.factorial : NNReal)) - 1 = k / m
  rw [hceil, Nat.add_sub_cancel]

private theorem variationGateProcess_eq_rowNativeGate_of_commonCell
    (u : ∀ n, TailConvexWeights n) (n r k : Nat)
    (hr : r ∈ (u n).support) (hk : k < size T (rowCommonLevel u n))
    (a : Real) (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (t : NNReal) (htT : t ≤ T)
    (hlo : (grid T (rowCommonLevel u n)).sampledTime k < t)
    (hhi : t ≤ (grid T (rowCommonLevel u n)).sampledTime (k + 1))
    (omega : Omega) :
    variationGateProcess a T r S F mu t omega =
      (grid T r).doobVariationGate S F mu a
        (rowNativeIndex u n r k) omega := by
  have hidx := rowNativeIndex_eq_approxIndex_sub_one u n r k hr hk t htT hlo hhi
  unfold variationGateProcess variationGatePath
  simp only [min_eq_left htT]
  rw [hidx]

/-! ## The common refined gate coefficient -/

noncomputable def rowGateCoefficient
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Nat → Omega → Real :=
  fun k omega =>
    ∑ r ∈ (u n).support,
      (u n).weight r *
        (ChronologicalGrid.doobVariationGate (grid T r) S F mu a
          (rowNativeIndex u n r k) omega)

private theorem variationGateConvexRow_eq_rowGateCoefficient_of_commonCell
    (u : ∀ n, TailConvexWeights n) (n k : Nat)
    (a : Real) (T t : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (hk : k < size T (rowCommonLevel u n)) (htT : t ≤ T)
    (hlo : (grid T (rowCommonLevel u n)).sampledTime k < t)
    (hhi : t ≤ (grid T (rowCommonLevel u n)).sampledTime (k + 1))
    (omega : Omega) :
    variationGateConvexRow u n a T S F mu t omega =
      rowGateCoefficient u n a T S F mu k omega := by
  unfold variationGateConvexRow TailConvexWeights.apply rowGateCoefficient
  apply Finset.sum_congr rfl
  intro r hr
  change (u n).weight r * variationGateProcess a T r S F mu t omega = _
  rw [variationGateProcess_eq_rowNativeGate_of_commonCell
    u n r k hr hk a S F mu t htT hlo hhi omega]

private theorem rowGateTerm_measurable_of_time_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n r : Nat)
    (_hr : r ∈ (u n).support)
    (a : Real) (T : NNReal) (k : Nat)
    (htime : (grid T r).sampledTime (rowNativeIndex u n r k) ≤
      (grid T (rowCommonLevel u n)).sampledTime k) :
    StronglyMeasurable[(grid T (rowCommonLevel u n)).sampledFiltration F k]
      (ChronologicalGrid.doobVariationGate (grid T r) S F mu a
        (rowNativeIndex u n r k)) := by
  have hmeas : StronglyMeasurable[(grid T r).sampledFiltration F
      (rowNativeIndex u n r k)]
      (ChronologicalGrid.doobVariationGate (grid T r) S F mu a
        (rowNativeIndex u n r k)) :=
    (grid T r).stronglyAdapted_doobVariationGate S F mu a
      (rowNativeIndex u n r k)
  exact hmeas.mono (F.mono htime)

theorem rowGateTerm_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n r : Nat)
    (hr : r ∈ (u n).support)
    (a : Real) (T : NNReal) (k : Nat) :
    StronglyMeasurable[(grid T (rowCommonLevel u n)).sampledFiltration F k]
      (fun omega => (u n).weight r *
        (ChronologicalGrid.doobVariationGate (grid T r) S F mu a
          (rowNativeIndex u n r k) omega)) := by
  have htime : (grid T r).sampledTime (rowNativeIndex u n r k) ≤
      (grid T (rowCommonLevel u n)).sampledTime k := by
    rcases le_total k (size T (rowCommonLevel u n)) with hq | hq
    · exact rowCommonGrid_sampledTime_nativeIndex_le u n r k hr hq
    · have hqt : (grid T (rowCommonLevel u n)).sampledTime k = T := by
        have hi : (grid T (rowCommonLevel u n)).natIndex k =
            ⟨size T (rowCommonLevel u n),
              Nat.lt_succ_self (size T (rowCommonLevel u n))⟩ := by
          ext
          simp [ChronologicalGrid.natIndex, hq]
        calc
          (grid T (rowCommonLevel u n)).sampledTime k =
              (grid T (rowCommonLevel u n)).sampledTime
                (size T (rowCommonLevel u n)) := by
              change (grid T (rowCommonLevel u n)).time
                ((grid T (rowCommonLevel u n)).natIndex k) =
                (grid T (rowCommonLevel u n)).time
                  ((grid T (rowCommonLevel u n)).natIndex
                    (size T (rowCommonLevel u n)))
              rw [hi]
              rw [ChronologicalGrid.natIndex_last]
          _ = T := sampledTime_size T (rowCommonLevel u n)
      calc
        (grid T r).sampledTime (rowNativeIndex u n r k) ≤ T := by
          unfold ChronologicalGrid.sampledTime
          rw [grid_time]
          exact min_le_right _ _
        _ = (grid T (rowCommonLevel u n)).sampledTime k := hqt.symm
  exact (rowGateTerm_measurable_of_time_le
    (S := S) (F := F) (mu := mu) u n r hr a T k htime).const_mul
      ((u n).weight r)

theorem rowGateCoefficient_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) :
    StronglyAdapted
      ((grid T (rowCommonLevel u n)).sampledFiltration F)
      (rowGateCoefficient u n a T S F mu) := by
  intro k
  apply (u n).support.stronglyMeasurable_fun_sum
  intro r hr
  exact rowGateTerm_stronglyAdapted (S := S) (F := F) (mu := mu)
    u n r hr a T k

noncomputable def rowGateStrategy
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) : PredictableElementaryStrategy F :=
  (grid T (rowCommonLevel u n)).adaptedElementaryStrategy F
    (rowGateCoefficient u n a T S F mu)
    (rowGateCoefficient_stronglyAdapted (S := S) (F := F) (mu := mu) u n a T)

private theorem sum_div_block_mul_sub
    (m N : Nat) (hm : 0 < m) (c x : Nat → Real) :
    (∑ k ∈ Finset.range (m * N),
      c (k / m) * (x (k + 1) - x k)) =
      ∑ j ∈ Finset.range N,
        c j * (x (m * (j + 1)) - x (m * j)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hblock :
          (∑ j ∈ Finset.range m,
            c ((m * N + j) / m) *
              (x (m * N + j + 1) - x (m * N + j))) =
            c N * (x (m * (N + 1)) - x (m * N)) := by
        calc
          (∑ j ∈ Finset.range m,
              c ((m * N + j) / m) *
                (x (m * N + j + 1) - x (m * N + j))) =
              ∑ j ∈ Finset.range m,
                c N * (x (m * N + j + 1) - x (m * N + j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hjm : j < m := Finset.mem_range.mp hj
                  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hjm]
                  simp
          _ = c N * ∑ j ∈ Finset.range m,
                (x (m * N + j + 1) - x (m * N + j)) := by
                  rw [Finset.mul_sum]
          _ = c N * (x (m * (N + 1)) - x (m * N)) := by
                  simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    (congrArg (fun z => c N * z)
                      (Finset.sum_range_sub (fun j => x (m * N + j)) m))
      calc
        (∑ k ∈ Finset.range (m * (N + 1)),
            c (k / m) * (x (k + 1) - x k)) =
            (∑ k ∈ Finset.range (m * N),
              c (k / m) * (x (k + 1) - x k)) +
            ∑ j ∈ Finset.range m,
              c ((m * N + j) / m) *
                (x (m * N + j + 1) - x (m * N + j)) := by
                  rw [Nat.mul_succ, Finset.sum_range_add]
        _ = (∑ j ∈ Finset.range N,
              c j * (x (m * (j + 1)) - x (m * j))) +
            c N * (x (m * (N + 1)) - x (m * N)) := by
                  rw [ih, hblock]
        _ = ∑ j ∈ Finset.range (N + 1),
              c j * (x (m * (j + 1)) - x (m * j)) := by
                  rw [Finset.sum_range_succ]

theorem adaptedElementaryStrategy_gain_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K : Nat → Omega → Real)
    (hK : StronglyAdapted (G.sampledFiltration F) K)
    (t : NNReal) (omega : Omega) :
    ElementaryStrategy.gain S
        (G.adaptedElementaryStrategy F K hK).toElementary t omega =
      ∑ k ∈ Finset.range N,
        K k omega *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) := by
  classical
  unfold ChronologicalGrid.adaptedElementaryStrategy
    ChronologicalGrid.adaptedElementaryBlock
    PredictableElementaryStrategy.toElementary ElementaryStrategy.gain
    ElementaryInterval.gain
  simp only [List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  change K k omega *
      (S (min t (G.sampledTime (k + 1))) omega -
        S (min t (G.sampledTime k)) omega) = _
  by_cases hstart : G.sampledTime k ≤ t
  · simp only [min_eq_right hstart]
  · have hstart' : t ≤ G.sampledTime k := le_of_not_ge hstart
    have hstop' : t ≤ G.sampledTime (k + 1) :=
      hstart'.trans (G.sampledTime_mono (Nat.le_succ k))
    rw [min_eq_left hstart', min_eq_left hstop']

private theorem adaptedElementaryStrategy_gain_cell_sub
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {N : Nat} (G : ChronologicalGrid NNReal N)
    (K : Nat → Omega → Real)
    (hK : StronglyAdapted (G.sampledFiltration F) K)
    (t : NNReal) (omega : Omega) {k : Nat} (hk : k < N) :
    ElementaryStrategy.gain S
        (G.adaptedElementaryStrategy F K hK).toElementary
        (min t (G.sampledTime (k + 1))) omega -
      ElementaryStrategy.gain S
        (G.adaptedElementaryStrategy F K hK).toElementary
        (min t (G.sampledTime k)) omega =
      K k omega *
        (S (min t (G.sampledTime (k + 1))) omega -
          S (min t (G.sampledTime k)) omega) := by
  rw [adaptedElementaryStrategy_gain_at,
    adaptedElementaryStrategy_gain_at]
  rw [← Finset.sum_sub_distrib]
  let f : Nat → Real := fun x =>
    K x omega *
      (S (min (min t (G.sampledTime (k + 1)))
          (G.sampledTime (x + 1))) omega -
        S (min (min t (G.sampledTime (k + 1)))
          (G.sampledTime x)) omega)
  let g : Nat → Real := fun x =>
    K x omega *
      (S (min (min t (G.sampledTime k))
          (G.sampledTime (x + 1))) omega -
        S (min (min t (G.sampledTime k))
          (G.sampledTime x)) omega)
  calc
    (∑ x ∈ Finset.range N, (f x - g x)) = f k - g k := by
      apply Finset.sum_eq_single k
      · intro j hj hkj
        have hjlt : j < N := Finset.mem_range.mp hj
        rcases lt_or_gt_of_ne hkj with hjk | hkj
        · have hj1k : j + 1 ≤ k := Nat.succ_le_of_lt hjk
          have htimej1 : G.sampledTime (j + 1) ≤ G.sampledTime k :=
            G.sampledTime_mono hj1k
          have htimejk1 : G.sampledTime (j + 1) ≤ G.sampledTime (k + 1) :=
            htimej1.trans (G.sampledTime_mono (Nat.le_succ k))
          have htimej : G.sampledTime j ≤ G.sampledTime k :=
            (G.sampledTime_mono (Nat.le_succ j)).trans htimej1
          have htimejk1' : G.sampledTime j ≤ G.sampledTime (k + 1) :=
            htimej.trans (G.sampledTime_mono (Nat.le_succ k))
          simp only [sub_eq_zero]
          dsimp [f, g]
          rw [min_assoc, min_eq_right htimejk1,
            min_assoc, min_eq_right htimejk1',
            min_assoc, min_eq_right htimej1,
            min_assoc, min_eq_right htimej]
        · have hksucc : k + 1 ≤ j := Nat.succ_le_of_lt hkj
          have htimek1j : G.sampledTime (k + 1) ≤ G.sampledTime j :=
            G.sampledTime_mono hksucc
          have htimek1j1 : G.sampledTime (k + 1) ≤ G.sampledTime (j + 1) :=
            htimek1j.trans (G.sampledTime_mono (Nat.le_succ j))
          have htimekj1 : G.sampledTime k ≤ G.sampledTime (j + 1) :=
            (G.sampledTime_mono (Nat.le_succ k)).trans htimek1j1
          have htimekj : G.sampledTime k ≤ G.sampledTime j :=
            G.sampledTime_mono hkj.le
          have htimej1 : G.sampledTime k ≤ G.sampledTime (j + 1) :=
            htimekj.trans (G.sampledTime_mono (Nat.le_succ j))
          have hleft : min t (G.sampledTime (k + 1)) ≤
              G.sampledTime (j + 1) :=
            (min_le_right _ _).trans htimek1j1
          have hleft' : min t (G.sampledTime (k + 1)) ≤
              G.sampledTime j :=
            (min_le_right _ _).trans htimek1j
          have hright : min t (G.sampledTime k) ≤
              G.sampledTime (j + 1) :=
            (min_le_right _ _).trans htimekj1
          have hright' : min t (G.sampledTime k) ≤ G.sampledTime j :=
            (min_le_right _ _).trans htimekj
          dsimp [f, g]
          rw [min_eq_left hleft, min_eq_left hleft',
            min_eq_left hright, min_eq_left hright']
          simp only [sub_self, mul_zero]
      · intro hkn
        exact False.elim (hkn (Finset.mem_range.mpr hk))
    _ = _ := by
      have htimek : G.sampledTime k ≤ G.sampledTime (k + 1) :=
        G.sampledTime_mono (Nat.le_succ k)
      dsimp [f, g]
      simp [min_assoc, htimek]

theorem rowGateStrategy_gain
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T t : NNReal) (omega : Omega) :
    ElementaryStrategy.gain S
        (rowGateStrategy (S := S) (F := F) (mu := mu) u n a T).toElementary t omega =
      nativeGateGainConvexRow u n a T S F mu t omega := by
  let q := rowCommonLevel u n
  rw [show rowGateStrategy (S := S) (F := F) (mu := mu) u n a T =
      (grid T q).adaptedElementaryStrategy F
        (rowGateCoefficient u n a T S F mu)
        (rowGateCoefficient_stronglyAdapted (S := S) (F := F) (mu := mu) u n a T) by
    rfl]
  rw [adaptedElementaryStrategy_gain_at]
  unfold nativeGateGainConvexRow TailConvexWeights.apply
  calc
    (∑ k ∈ Finset.range (size T q),
        rowGateCoefficient u n a T S F mu k omega *
          (S (min t ((grid T q).sampledTime (k + 1))) omega -
            S (min t ((grid T q).sampledTime k)) omega)) =
      ∑ k ∈ Finset.range (size T q),
        ∑ r ∈ (u n).support,
          ((u n).weight r *
            (grid T r).doobVariationGate S F mu a
              (rowNativeIndex u n r k) omega) *
            (S (min t ((grid T q).sampledTime (k + 1))) omega -
              S (min t ((grid T q).sampledTime k)) omega) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rowGateCoefficient, Finset.sum_mul]
    _ = ∑ r ∈ (u n).support,
          ∑ k ∈ Finset.range (size T q),
            ((u n).weight r *
              (grid T r).doobVariationGate S F mu a
                (rowNativeIndex u n r k) omega) *
              (S (min t ((grid T q).sampledTime (k + 1))) omega -
                S (min t ((grid T q).sampledTime k)) omega) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ (u n).support,
          (u n).weight r * nativeGateGain a T r S F mu t omega := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrq : r ≤ q := rowCommonLevel_ge u n r hr
      have hm : 0 < factorialRatio r q := factorialRatio_pos r q hrq
      have hsize : factorialRatio r q * size T r = size T q :=
        factorialRatio_mul_size T r q hrq
      calc
        ∑ k ∈ Finset.range (size T q),
            ((u n).weight r *
              (grid T r).doobVariationGate S F mu a
                (rowNativeIndex u n r k) omega) *
              (S (min t ((grid T q).sampledTime (k + 1))) omega -
                S (min t ((grid T q).sampledTime k)) omega) =
            (u n).weight r *
              ∑ k ∈ Finset.range (size T q),
                (grid T r).doobVariationGate S F mu a
                  (rowNativeIndex u n r k) omega *
                  (S (min t ((grid T q).sampledTime (k + 1))) omega -
                    S (min t ((grid T q).sampledTime k)) omega) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (u n).weight r *
              ∑ j ∈ Finset.range (size T r),
                (grid T r).doobVariationGate S F mu a j omega *
                  (S (min t ((grid T q).sampledTime
                      (factorialRatio r q * (j + 1)))) omega -
                    S (min t ((grid T q).sampledTime
                      (factorialRatio r q * j))) omega) := by
          congr 1
          simpa only [rowNativeIndex, hsize] using
            (sum_div_block_mul_sub (factorialRatio r q)
              (size T r) hm
              (fun j => (grid T r).doobVariationGate S F mu a j omega)
              (fun k => S (min t ((grid T q).sampledTime k)) omega))
        _ = (u n).weight r * nativeGateGain a T r S F mu t omega := by
          rw [nativeGateGain_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < size T r := Finset.mem_range.mp hj
          have hjr : j ≤ size T r := hjlt.le
          have hj1r : j + 1 ≤ size T r := Nat.succ_le_of_lt hjlt
          change (grid T r).doobVariationGate S F mu a j omega *
            (S (min t ((grid T q).sampledTime
                (factorialRatio r q * (j + 1)))) omega -
              S (min t ((grid T q).sampledTime
                (factorialRatio r q * j))) omega) = _
          rw [rowCommonGrid_sampledTime_mul_eq u n r (j + 1) hr hj1r,
            rowCommonGrid_sampledTime_mul_eq u n r j hr hjr]

theorem rowGateCoefficient_nonneg_le_one
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (k : Nat) (omega : Omega) :
    0 ≤ rowGateCoefficient u n a T S F mu k omega ∧
      rowGateCoefficient u n a T S F mu k omega ≤ 1 := by
  unfold rowGateCoefficient
  have hnonneg : ∀ r ∈ (u n).support,
      0 ≤ (u n).weight r *
        (grid T r).doobVariationGate S F mu a
          (rowNativeIndex u n r k) omega := by
    intro r hr
    exact mul_nonneg ((u n).nonneg r hr) (by
      unfold ChronologicalGrid.doobVariationGate
      split_ifs <;> norm_num)
  constructor
  · exact Finset.sum_nonneg hnonneg
  · calc
      (∑ r ∈ (u n).support,
          (u n).weight r *
            (grid T r).doobVariationGate S F mu a
              (rowNativeIndex u n r k) omega) ≤
        ∑ r ∈ (u n).support, (u n).weight r * 1 := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_left (by
            unfold ChronologicalGrid.doobVariationGate
            split_ifs <;> norm_num) ((u n).nonneg r hr)
      _ = 1 := by
        rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]

/-! A finite-grid integrand and its actual predictable strategy. -/

noncomputable def rowInverseCoefficient
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
  (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal) : Nat → Omega → Real :=
  fun k omega =>
    if ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
        alpha omega ∧
      (grid T (rowCommonLevel u n)).sampledTime k <
        (grid T (rowCommonLevel u n)).sampledTime (k + 1) then
      (rowGateCoefficient u n a T S F mu k omega)⁻¹
    else 0

theorem rowInverseCoefficient_abs_le_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) (alpha : Omega → WithTop NNReal)
    (k : Nat) (omega : Omega)
    (hgate : (1 / 2 : Real) ≤ rowGateCoefficient u n a T S F mu k omega) :
    |rowInverseCoefficient u n a T S F mu alpha k omega| ≤ 2 := by
  unfold rowInverseCoefficient
  split_ifs with hactive
  · have hnonneg : 0 ≤ rowGateCoefficient u n a T S F mu k omega :=
      (rowGateCoefficient_nonneg_le_one u n a T S F mu k omega).1
    rw [abs_inv, abs_of_nonneg hnonneg, inv_eq_one_div]
    have hgpos : 0 < rowGateCoefficient u n a T S F mu k omega :=
      lt_of_lt_of_le (by norm_num) hgate
    rw [one_div_le hgpos (by norm_num)]
    exact hgate
  · simp

/-! The strict hitting convention is left-continuous: a cell whose left
endpoint is strictly before the (truncated) hitting time can be sampled at
an intermediate point of that same cell.  This is the point at which the
strict inequality in the definition of `rowInverseCoefficient` is used. -/

theorem rowGateCoefficient_ge_half_of_lt_alpha
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (k : Nat) (omega : Omega)
    (hk : k < size T (rowCommonLevel u n))
    (hactive : (grid T (rowCommonLevel u n)).sampledTime k < alpha omega)
    (hcell : (grid T (rowCommonLevel u n)).sampledTime k <
      (grid T (rowCommonLevel u n)).sampledTime (k + 1)) :
    (1 / 2 : Real) ≤ rowGateCoefficient u n a T S F mu k omega := by
  let q := rowCommonLevel u n
  let G := grid T q
  let l := G.sampledTime k
  let r := G.sampledTime (k + 1)
  have hcell' : l < r := hcell
  have hrT : r ≤ T := by
    dsimp [r, G, q]
    exact ((grid T q).sampledTime_mono (Nat.succ_le_of_lt hk)).trans_eq
      (sampledTime_size T q)
  have hαtop : alpha omega ≠ (⊤ : WithTop NNReal) := by
    apply ne_top_of_le_ne_top WithTop.coe_ne_top
    exact (hAlpha omega).trans (min_le_left _ _)
  let α := (alpha omega).untop hαtop
  have hαcoe : (α : WithTop NNReal) = alpha omega := by
    exact WithTop.coe_untop _ hαtop
  have hlα : l < α := by
    apply WithTop.coe_lt_coe.mp
    rw [hαcoe]
    exact hactive
  let v := min r α
  have hlv : l < v := lt_min hcell' hlα
  let s := (l + v) / 2
  have hls : l < s := by
    dsimp [s]
    nlinarith
  have hvs : s < v := by
    dsimp [s]
    nlinarith
  have hsα : s < α := (hvs.trans_le (min_le_right _ _))
  have hsr : s ≤ r := (hvs.le.trans (min_le_left _ _))
  have hsT : s ≤ T := hsr.trans hrT
  have hsτ : (s : WithTop NNReal) <
      LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega := by
    have hsα' : (s : WithTop NNReal) < alpha omega := by
      rw [← hαcoe]
      exact WithTop.coe_lt_coe.mpr hsα
    exact lt_of_lt_of_le hsα' ((hAlpha omega).trans (min_le_right _ _))
  have hbefore := LeftContinuousHittingTime.le_of_lt_strictHittingAfter
    (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
    (-1 / 2) omega s hsτ
  have hrow : variationGateConvexRow u n a T S F mu s omega =
      rowGateCoefficient u n a T S F mu k omega := by
    dsimp [G, l, r] at hls hsr
    exact variationGateConvexRow_eq_rowGateCoefficient_of_commonCell
      u n k a T s S F mu hk hsT hls hsr omega
  rw [hrow] at hbefore
  linarith

theorem rowInverseCoefficient_abs_le_two_of_lt_alpha
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (k : Nat) (omega : Omega)
    (hk : k < size T (rowCommonLevel u n)) :
    |rowInverseCoefficient u n a T S F mu alpha k omega| ≤ 2 := by
  by_cases hactive :
      ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
        alpha omega ∧
      (grid T (rowCommonLevel u n)).sampledTime k <
        (grid T (rowCommonLevel u n)).sampledTime (k + 1)
  · have hbound := rowInverseCoefficient_abs_le_two u n a T alpha k omega
      (rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha hAlpha
        k omega hk hactive.1 hactive.2)
    simpa [rowInverseCoefficient, hactive] using hbound
  · rw [rowInverseCoefficient]
    simp only [hactive, ite_false, abs_zero]
    norm_num

theorem rowInverseCoefficient_uniform_abs_le_two_of_le_hitting
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega)) :
    ∀ k omega, |rowInverseCoefficient u n a T S F mu alpha k omega| ≤ 2 := by
  intro k omega
  by_cases hk : k < size T (rowCommonLevel u n)
  · exact rowInverseCoefficient_abs_le_two_of_lt_alpha u n a T S F mu alpha
      hAlpha k omega hk
  · let q := rowCommonLevel u n
    let G := grid T q
    have hkge : size T q ≤ k := Nat.le_of_not_gt hk
    have hsize : G.sampledTime (size T q) = T := by
      change (grid T q).sampledTime (size T q) = T
      exact sampledTime_size T q
    have htime_ge : G.sampledTime (size T q) ≤ G.sampledTime k :=
      G.sampledTime_mono hkge
    have htime_le : G.sampledTime k ≤ T := by
      unfold G q ChronologicalGrid.sampledTime
      rw [grid_time]
      exact min_le_right _ _
    have htimek : G.sampledTime k = T := by
      exact le_antisymm htime_le
        (by rw [hsize] at htime_ge; exact htime_ge)
    have htimek1 : G.sampledTime (k + 1) = T := by
      have hge : G.sampledTime (size T q) ≤ G.sampledTime (k + 1) :=
        G.sampledTime_mono (hkge.trans (Nat.le_succ _))
      have hle : G.sampledTime (k + 1) ≤ T := by
        unfold G q ChronologicalGrid.sampledTime
        rw [grid_time]
        exact min_le_right _ _
      exact le_antisymm hle
        (by rw [hsize] at hge; exact hge)
    rw [rowInverseCoefficient]
    split_ifs with hactive
    · exfalso
      rw [htimek, htimek1] at hactive
      exact (not_lt_of_ge le_rfl) hactive.2
    · norm_num

theorem rowInverseCoefficient_mul_gate_eq_activeIndicator
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (k : Nat) (omega : Omega)
    (hk : k < size T (rowCommonLevel u n)) :
    rowInverseCoefficient u n a T S F mu alpha k omega *
        rowGateCoefficient u n a T S F mu k omega =
      if ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
          alpha omega ∧
        (grid T (rowCommonLevel u n)).sampledTime k <
          (grid T (rowCommonLevel u n)).sampledTime (k + 1) then
        1 else 0 := by
  by_cases hactive :
      ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
        alpha omega ∧
      (grid T (rowCommonLevel u n)).sampledTime k <
        (grid T (rowCommonLevel u n)).sampledTime (k + 1)
  · rw [rowInverseCoefficient, ite_eq_left hactive]
    have hgate := rowGateCoefficient_ge_half_of_lt_alpha u n a T S F mu alpha
      hAlpha k omega hk hactive.1 hactive.2
    have hgatepos : 0 < rowGateCoefficient u n a T S F mu k omega :=
      lt_of_lt_of_le (by norm_num) hgate
    rw [inv_mul_cancel₀ hgatepos.ne']
    rw [ite_eq_left hactive]
  · rw [rowInverseCoefficient, ite_eq_right hactive]
    rw [ite_eq_right hactive]
    simp

theorem rowInverseCoefficient_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) (alpha : Omega → WithTop NNReal)
    (hAlpha : IsStoppingTime F alpha) :
    StronglyAdapted
      ((grid T (rowCommonLevel u n)).sampledFiltration F)
      (rowInverseCoefficient u n a T S F mu alpha) := by
  intro k
  have hGate := rowGateCoefficient_stronglyAdapted (S := S) (F := F) (mu := mu) u n a T
  have hActive : MeasurableSet[
      (grid T (rowCommonLevel u n)).sampledFiltration F k]
      {omega | ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
        alpha omega ∧
      (grid T (rowCommonLevel u n)).sampledTime k <
        (grid T (rowCommonLevel u n)).sampledTime (k + 1)} := by
    rw [ChronologicalGrid.sampledFiltration_apply]
    apply (hAlpha.measurableSet_gt
      ((grid T (rowCommonLevel u n)).sampledTime k)).inter
    by_cases htime : (grid T (rowCommonLevel u n)).sampledTime k <
        (grid T (rowCommonLevel u n)).sampledTime (k + 1)
    · exact MeasurableSet.const _
    · exact MeasurableSet.const _
  change StronglyMeasurable[
      (grid T (rowCommonLevel u n)).sampledFiltration F k]
      (fun omega => if ((grid T (rowCommonLevel u n)).sampledTime k :
          WithTop NNReal) < alpha omega ∧
          (grid T (rowCommonLevel u n)).sampledTime k <
            (grid T (rowCommonLevel u n)).sampledTime (k + 1) then
        (rowGateCoefficient u n a T S F mu k omega)⁻¹ else 0)
  exact StronglyMeasurable.ite hActive (hGate k).inv₀
    stronglyMeasurable_const

noncomputable def rowInverseStrategy
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal) (alpha : Omega → WithTop NNReal)
    (hAlpha : IsStoppingTime F alpha) : PredictableElementaryStrategy F :=
  (grid T (rowCommonLevel u n)).adaptedElementaryStrategy F
    (rowInverseCoefficient u n a T S F mu alpha)
    (rowInverseCoefficient_stronglyAdapted (S := S) (F := F) (mu := mu) u n a T alpha hAlpha)

theorem rowInverseStrategy_gain_eq_activeCellSum
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (t : NNReal) (omega : Omega) :
    ElementaryStrategy.gain
        (nativeGateGainConvexRow u n a T S F mu)
        (rowInverseStrategy (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop).toElementary
        t omega =
      ∑ k ∈ Finset.range (size T (rowCommonLevel u n)),
        (if ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
              alpha omega ∧
            (grid T (rowCommonLevel u n)).sampledTime k <
              (grid T (rowCommonLevel u n)).sampledTime (k + 1) then
          (1 : Real) else 0) *
          (S (min t ((grid T (rowCommonLevel u n)).sampledTime (k + 1))) omega -
            S (min t ((grid T (rowCommonLevel u n)).sampledTime k)) omega) := by
  let q := rowCommonLevel u n
  let G := grid T q
  rw [show rowInverseStrategy (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop =
      G.adaptedElementaryStrategy F
        (rowInverseCoefficient u n a T S F mu alpha)
        (rowInverseCoefficient_stronglyAdapted
          (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop) by
    rfl]
  rw [adaptedElementaryStrategy_gain_at]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < size T q := Finset.mem_range.mp hk
  have hcell := adaptedElementaryStrategy_gain_cell_sub
    (S := S) G (rowGateCoefficient u n a T S F mu)
    (rowGateCoefficient_stronglyAdapted (S := S) (F := F) (mu := mu) u n a T) t omega hk'
  have hYdiff :
      nativeGateGainConvexRow u n a T S F mu
          (min t (G.sampledTime (k + 1))) omega -
        nativeGateGainConvexRow u n a T S F mu
          (min t (G.sampledTime k)) omega =
      rowGateCoefficient u n a T S F mu k omega *
        (S (min t (G.sampledTime (k + 1))) omega -
          S (min t (G.sampledTime k)) omega) := by
    rw [← rowGateStrategy_gain (S := S) (F := F) (mu := mu) u n a T
      (min t (G.sampledTime (k + 1))) omega,
      ← rowGateStrategy_gain (S := S) (F := F) (mu := mu) u n a T
        (min t (G.sampledTime k)) omega]
    exact hcell
  rw [hYdiff]
  have hprod := rowInverseCoefficient_mul_gate_eq_activeIndicator
    u n a T S F mu alpha hAlpha k omega hk'
  calc
    rowInverseCoefficient u n a T S F mu alpha k omega *
        (rowGateCoefficient u n a T S F mu k omega *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega)) =
        (rowInverseCoefficient u n a T S F mu alpha k omega *
          rowGateCoefficient u n a T S F mu k omega) *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) := by ring
    _ = (if (G.sampledTime k : WithTop NNReal) < alpha omega ∧
          G.sampledTime k < G.sampledTime (k + 1) then (1 : Real) else 0) *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) := by
      rw [hprod]

theorem rowAlpha_noCross_of_exact_hitting
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega)
    (alpha : Omega → WithTop NNReal)
    (hAlpha : ∀ omega, alpha omega = min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (k : Nat) (omega : Omega)
    (hk : k < size T (rowCommonLevel u n))
    (hleft : (grid T (rowCommonLevel u n)).sampledTime k < alpha omega) :
    ((grid T (rowCommonLevel u n)).sampledTime (k + 1) : WithTop NNReal) ≤
      alpha omega := by
  let q := rowCommonLevel u n
  let G := grid T q
  have hendT : G.sampledTime (k + 1) ≤ T := by
    exact (G.sampledTime_mono (Nat.succ_le_of_lt hk)).trans_eq
      (sampledTime_size T q)
  by_contra hend
  have hαT : alpha omega < (T : WithTop NNReal) := by
    have hendT' : (G.sampledTime (k + 1) : WithTop NNReal) ≤
        (T : WithTop NNReal) := WithTop.coe_le_coe.mpr hendT
    exact lt_of_not_ge (fun h => hend (hendT'.trans h))
  have hτeq :
      LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
          (-1 / 2) omega = alpha omega := by
    have hαleτ : alpha omega ≤
        LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
          (-1 / 2) omega := by
      rw [hAlpha omega]
      exact min_le_right _ _
    have hτleα :
        LeftContinuousHittingTime.strictHittingAfter
            (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
            (-1 / 2) omega ≤ alpha omega := by
      by_contra hnot
      have hατ : alpha omega <
          LeftContinuousHittingTime.strictHittingAfter
            (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
            (-1 / 2) omega := lt_of_not_ge hnot
      have hmin : alpha omega < min (T : WithTop NNReal)
          (LeftContinuousHittingTime.strictHittingAfter
            (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
            (-1 / 2) omega) := lt_min hαT hατ
      rw [← hAlpha omega] at hmin
      exact (lt_irrefl _ hmin)
    exact le_antisymm hτleα hαleτ
  have hHit :
      LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
          (-1 / 2) omega <
        (G.sampledTime (k + 1) : WithTop NNReal) := by
    rw [hτeq]
    exact lt_of_not_ge hend
  have hHit' : MeasureTheory.hittingAfter
      (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
      (Set.Ioi (-1 / 2)) 0 omega < G.sampledTime (k + 1) := hHit
  rw [MeasureTheory.hittingAfter_lt_iff] at hHit'
  obtain ⟨s, hs, hsGate⟩ := hHit'
  have hsEnd : s ≤ G.sampledTime (k + 1) := hs.2.le
  have hτs := MeasureTheory.hittingAfter_le_of_mem
    (u := fun t omega => -variationGateConvexRow u n a T S F mu t omega)
    (s := Set.Ioi (-1 / 2)) (n := (0 : NNReal)) (i := s) (ω := omega)
    hs.1 hsGate
  have hαs : alpha omega ≤ (s : WithTop NNReal) := by
    rw [← hτeq]
    exact hτs
  have hsαtop : alpha omega ≠ (⊤ : WithTop NNReal) :=
    ne_top_of_lt hαT
  let α := (alpha omega).untop hsαtop
  have hαcoe : (α : WithTop NNReal) = alpha omega :=
    WithTop.coe_untop _ hsαtop
  have hleftα : G.sampledTime k < α := by
    apply WithTop.coe_lt_coe.mp
    rw [hαcoe]
    exact hleft
  have hαs' : α ≤ s := by
    apply WithTop.coe_le_coe.mp
    rw [hαcoe]
    exact hαs
  let s₀ : NNReal := (G.sampledTime k + α) / 2
  have hs₀left : G.sampledTime k < s₀ := by
    dsimp [s₀]
    nlinarith
  have hs₀α : s₀ < α := by
    dsimp [s₀]
    nlinarith
  have hs₀s : s₀ ≤ s := hs₀α.le.trans hαs'
  have hsT : s ≤ T := hsEnd.trans hendT
  have hs₀T : s₀ ≤ T := hs₀s.trans hsT
  have hs₀end : s₀ ≤ G.sampledTime (k + 1) := hs₀s.trans hsEnd
  have hsτ : (s₀ : WithTop NNReal) <
      LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega := by
    rw [hτeq, ← hαcoe]
    exact WithTop.coe_lt_coe.mpr hs₀α
  have hbefore := LeftContinuousHittingTime.le_of_lt_strictHittingAfter
    (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
    (-1 / 2) omega s₀ hsτ
  have hrow₀ : variationGateConvexRow u n a T S F mu s₀ omega =
      rowGateCoefficient u n a T S F mu k omega := by
    exact variationGateConvexRow_eq_rowGateCoefficient_of_commonCell
      u n k a T s₀ S F mu hk hs₀T hs₀left hs₀end omega
  have hrowS : variationGateConvexRow u n a T S F mu s omega =
      rowGateCoefficient u n a T S F mu k omega := by
    have hlefts : G.sampledTime k < s := hleftα.trans_le hαs'
    exact variationGateConvexRow_eq_rowGateCoefficient_of_commonCell
      u n k a T s S F mu hk hsT hlefts hsEnd omega
  have hsGate' : -1 / 2 <
      -variationGateConvexRow u n a T S F mu s omega := by
    exact hsGate
  rw [hrow₀] at hbefore
  rw [hrowS] at hsGate'
  linarith

omit [MeasurableSpace Omega] in
/-- Active grid cells telescope to the gain stopped at a grid-aligned time. -/
theorem activeCellSum_eq_stoppedSource_sub_initial
    (S : Process Omega) (T : NNReal) (q : Nat)
    (alpha : Omega → WithTop NNReal)
    (hAlphaT : ∀ omega, alpha omega ≤ (T : WithTop NNReal))
    (hNoCross : ∀ k, k < size T q → ∀ omega,
      ((grid T q).sampledTime k : WithTop NNReal) < alpha omega →
        (grid T q).sampledTime k < (grid T q).sampledTime (k + 1) →
        ((grid T q).sampledTime (k + 1) : WithTop NNReal) ≤ alpha omega)
    (t : NNReal) (omega : Omega) :
    (∑ k ∈ Finset.range (size T q),
      (if ((grid T q).sampledTime k : WithTop NNReal) < alpha omega ∧
          (grid T q).sampledTime k < (grid T q).sampledTime (k + 1)
        then (1 : Real) else 0) *
        (S (min t ((grid T q).sampledTime (k + 1))) omega -
          S (min t ((grid T q).sampledTime k)) omega)) =
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega := by
  let G := grid T q
  let Z : Process Omega := MeasureTheory.stoppedProcess S alpha
  have hterm : ∀ k ∈ Finset.range (size T q),
      (if (G.sampledTime k : WithTop NNReal) < alpha omega ∧
          G.sampledTime k < G.sampledTime (k + 1) then (1 : Real) else 0) *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega) =
        Z (min t (G.sampledTime (k + 1))) omega -
          Z (min t (G.sampledTime k)) omega := by
    intro k hk
    have hk' : k < size T q := Finset.mem_range.mp hk
    have hmono : G.sampledTime k ≤ G.sampledTime (k + 1) :=
      G.sampledTime_mono (Nat.le_succ k)
    by_cases hleft : (G.sampledTime k : WithTop NNReal) < alpha omega
    · by_cases hcell : G.sampledTime k < G.sampledTime (k + 1)
      · have hend : (G.sampledTime (k + 1) : WithTop NNReal) ≤ alpha omega := by
          apply hNoCross k hk' omega hleft hcell
        have hstart : ((min t (G.sampledTime k) : NNReal) : WithTop NNReal) ≤
            alpha omega := by
          rw [WithTop.coe_min]
          exact (min_le_right _ _).trans
            hleft.le
        have hstop : ((min t (G.sampledTime (k + 1)) : NNReal) : WithTop NNReal) ≤
            alpha omega := by
          rw [WithTop.coe_min]
          exact (min_le_right _ _).trans hend
        rw [ite_eq_left ⟨hleft, hcell⟩]
        have hZstart : Z (min t (G.sampledTime k)) omega =
            S (min t (G.sampledTime k)) omega := by
          exact MeasureTheory.stoppedProcess_eq_of_le hstart
        have hZend : Z (min t (G.sampledTime (k + 1))) omega =
            S (min t (G.sampledTime (k + 1))) omega := by
          exact MeasureTheory.stoppedProcess_eq_of_le hstop
        rw [hZend, hZstart]
        simp
      · have heq : G.sampledTime k = G.sampledTime (k + 1) :=
          le_antisymm hmono (le_of_not_gt hcell)
        rw [ite_eq_right (by simp [hcell]), heq]
        simp
    · have hαleft : alpha omega ≤ (G.sampledTime k : WithTop NNReal) :=
        le_of_not_gt hleft
      have hαright : alpha omega ≤
          (G.sampledTime (k + 1) : WithTop NNReal) :=
        hαleft.trans (WithTop.coe_le_coe.mpr hmono)
      have hnot : ¬((G.sampledTime k : WithTop NNReal) < alpha omega ∧
          G.sampledTime k < G.sampledTime (k + 1)) := by
        intro h
        exact hleft h.1
      rw [ite_eq_right hnot]
      have hmin :
          min ((min t (G.sampledTime (k + 1)) : NNReal) : WithTop NNReal)
              (alpha omega) =
            min ((min t (G.sampledTime k) : NNReal) : WithTop NNReal)
              (alpha omega) := by
        rw [WithTop.coe_min, WithTop.coe_min, min_assoc, min_assoc,
          min_eq_right hαright, min_eq_right hαleft]
      simp only [zero_mul]
      have hZeq : Z (min t (G.sampledTime (k + 1))) omega =
          Z (min t (G.sampledTime k)) omega := by
        unfold Z MeasureTheory.stoppedProcess
        rw [hmin]
      exact (sub_eq_zero.mpr hZeq).symm
  calc
    (∑ k ∈ Finset.range (size T q),
        (if (G.sampledTime k : WithTop NNReal) < alpha omega ∧
            G.sampledTime k < G.sampledTime (k + 1) then (1 : Real) else 0) *
          (S (min t (G.sampledTime (k + 1))) omega -
            S (min t (G.sampledTime k)) omega)) =
      ∑ k ∈ Finset.range (size T q),
        (Z (min t (G.sampledTime (k + 1))) omega -
          Z (min t (G.sampledTime k)) omega) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k hk
    _ = Z (min t (G.sampledTime (size T q))) omega -
        Z (min t (G.sampledTime 0)) omega := by
      simpa using (Finset.sum_range_sub
        (fun k => Z (min t (G.sampledTime k)) omega) (size T q))
    _ = Z t omega - S 0 omega := by
      have hαT : alpha omega ≤ (T : WithTop NNReal) :=
        hAlphaT omega
      have hsize : G.sampledTime (size T q) = T := by
        change (grid T q).sampledTime (size T q) = T
        exact sampledTime_size T q
      have hZt : Z (min t (G.sampledTime (size T q))) omega = Z t omega := by
        rw [hsize]
        change S (min ((min t T : NNReal) : WithTop NNReal)
            (alpha omega)).untopA omega =
          S (min (t : WithTop NNReal) (alpha omega)).untopA omega
        rw [WithTop.coe_min, min_assoc, min_eq_right hαT]
      have hZ0 : Z (min t (G.sampledTime 0)) omega = S 0 omega := by
        have hzero : G.sampledTime 0 = 0 := by
          change (grid T q).sampledTime 0 = 0
          simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
            grid_time]
        rw [hzero]
        have ht0 : min t (0 : NNReal) = 0 := min_eq_right bot_le
        rw [ht0]
        change MeasureTheory.stoppedProcess S alpha 0 omega = S 0 omega
        exact MeasureTheory.stoppedProcess_eq_of_le (τ := alpha) bot_le
      rw [hZt, hZ0]

theorem rowInverseStrategy_gain_eq_stoppedSource_sub_initial
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (hNoCross : ∀ k, k < size T (rowCommonLevel u n) → ∀ omega,
      ((grid T (rowCommonLevel u n)).sampledTime k : WithTop NNReal) <
          alpha omega →
        (grid T (rowCommonLevel u n)).sampledTime k <
          (grid T (rowCommonLevel u n)).sampledTime (k + 1) →
        ((grid T (rowCommonLevel u n)).sampledTime (k + 1) : WithTop NNReal) ≤
          alpha omega)
    (t : NNReal) (omega : Omega) :
    ElementaryStrategy.gain
        (nativeGateGainConvexRow u n a T S F mu)
        (rowInverseStrategy (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop).toElementary
        t omega =
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega := by
  rw [rowInverseStrategy_gain_eq_activeCellSum (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
    hAlpha t omega]
  exact activeCellSum_eq_stoppedSource_sub_initial S T (rowCommonLevel u n) alpha
    (fun omega => (hAlpha omega).trans (min_le_left _ _)) hNoCross t omega

end HorizonFactorialGrid

end FTAPTheorem42
