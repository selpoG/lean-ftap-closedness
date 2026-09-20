/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.MartingaleFactorialSkeletonBounded
import FTAPTheorem42.Stochastic.Process.OneSidedLimitOfFiniteUpcrossings

/-!
# Right limits on the union of factorial grids

Every finite chronological chain of times from the union of the fixed-horizon
factorial grids occurs on one sufficiently fine grid.  Consequently the
finite total grid-upcrossing estimate and pathwise boundedness imply a right
limit along that union.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {Omega : Type*}

namespace HorizonFactorialGrid

/-- The union of all fixed-horizon factorial-grid times. -/
def factorialGridTimes (T : NNReal) : Set NNReal :=
  ⋃ r, Set.range (grid T r).time

theorem mem_factorialGridTimes_iff {T t : NNReal} :
    t ∈ factorialGridTimes T ↔
      ∃ r, t ∈ Set.range (grid T r).time := by
  simp only [factorialGridTimes, Set.mem_iUnion]

/-- The canonical skeleton enumerates every point of every fixed-horizon
factorial grid. -/
theorem factorialGridTimes_subset_range_stoppedLimitSkeleton (T : NNReal) :
    factorialGridTimes T ⊆
      Set.range (fun n => (stoppedLimitSkeleton T n).1) := by
  intro t ht
  obtain ⟨r, k, rfl⟩ := mem_factorialGridTimes_iff.1 ht
  refine ⟨Nat.pair r k.1, ?_⟩
  change (grid T (Nat.unpair (Nat.pair r k.1)).1).sampledTime
      (Nat.unpair (Nat.pair r k.1)).2 = (grid T r).time k
  rw [Nat.unpair_pair]
  exact ChronologicalGrid.sampledTime_fin_eq (grid T r) k

/-- A chronological chain on the union of factorial-grid times is realized
as an explicit natural-index chain on one finite grid. -/
theorem HasTimeUpcrossingChain.exists_factorialGrid_chain
    {M : Process Omega} {T U : NNReal} {a b : Real} {omega : Omega}
    {k : Nat} (hab : a < b) (hU : U ∈ factorialGridTimes T)
    (hChain : HasTimeUpcrossingChain (factorialGridTimes T) a b
      (fun t => M t omega) k U) :
    ∃ r N, N ≤ size T r ∧ (grid T r).sampledTime N = U ∧
      HasUpcrossingChain a b ((grid T r).natSample M) omega k N := by
  induction k generalizing U with
  | zero =>
      obtain ⟨r, j, hj⟩ := mem_factorialGridTimes_iff.1 hU
      refine ⟨r, j.1, Nat.le_of_lt_succ j.2, ?_, trivial⟩
      rw [ChronologicalGrid.sampledTime_fin_eq, hj]
  | succ k ih =>
      obtain ⟨l, hlD, v, hvD, hlv, hvU, hLow, hHigh, hPrevious⟩ :=
        hChain
      obtain ⟨r, N, hN, hTimeN, hGridPrevious⟩ := ih hlD hPrevious
      obtain ⟨rv, jv, hjv⟩ := mem_factorialGridTimes_iff.1 hvD
      obtain ⟨rU, jU, hjU⟩ := mem_factorialGridTimes_iff.1 hU
      let q := max (max r rv) rU
      obtain ⟨Nq, hNq, hTimeNq, hGridPreviousQ⟩ :=
        HasUpcrossingChain.exists_factorialGrid_mono_before T
          (le_trans (le_max_left r rv) (le_max_left (max r rv) rU))
          hN hGridPrevious
      have hvRange : v ∈ Set.range (grid T q).time :=
        range_grid_mono T
          (le_trans (le_max_right r rv) (le_max_left (max r rv) rU))
          ⟨jv, hjv⟩
      obtain ⟨jvq, hjvq⟩ := hvRange
      have hURange : U ∈ Set.range (grid T q).time :=
        range_grid_mono T (le_max_right (max r rv) rU) ⟨jU, hjU⟩
      obtain ⟨jUq, hjUq⟩ := hURange
      have hlvStrict : l < v := by
        refine lt_of_le_of_ne hlv ?_
        intro hlvEq
        rw [hlvEq] at hLow
        exact (not_lt_of_ge hab.le) (hHigh.trans hLow)
      let jq : Fin (size T q + 1) :=
        ⟨Nq, Nat.lt_succ_of_le hNq⟩
      have hIndex : Nq ≤ jvq.1 := by
        by_contra hNot
        have hReverse : jvq ≤ jq := by
          exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hNot))
        have hTimeReverse := (grid T q).monotone_time hReverse
        have hLowTime : (grid T q).time jq = l := by
          rw [← ChronologicalGrid.sampledTime_fin_eq]
          exact hTimeNq.trans hTimeN
        rw [hjvq, hLowTime] at hTimeReverse
        exact (not_le_of_gt hlvStrict) hTimeReverse
      have hIndexUpper : jvq.1 < jUq.1 := by
        by_contra hNot
        have hReverse : jUq ≤ jvq := by
          exact_mod_cast (Nat.le_of_not_gt hNot)
        have hTimeReverse := (grid T q).monotone_time hReverse
        rw [hjUq, hjvq] at hTimeReverse
        exact (not_le_of_gt hvU) hTimeReverse
      refine ⟨q, jUq.1, Nat.le_of_lt_succ jUq.2, ?_,
        Nq, jvq.1, hIndex, hIndexUpper, ?_, ?_, hGridPreviousQ⟩
      · rw [ChronologicalGrid.sampledTime_fin_eq, hjUq]
      · change M ((grid T q).sampledTime Nq) omega < a
        rw [hTimeNq, hTimeN]
        exact hLow
      · change b < M ((grid T q).sampledTime jvq.1) omega
        rw [ChronologicalGrid.sampledTime_fin_eq, hjvq]
        exact hHigh

/-- Finite total upcrossing count bounds every chronological chain on the
union of factorial-grid times before the horizon. -/
theorem HasTimeUpcrossingChain.le_of_factorialGridUpcrossings_lt_top
    {M : Process Omega} {T : NNReal} {a b : Real} (hab : a < b)
    {omega : Omega}
    (hFinite : martingaleFactorialGridUpcrossings M T a b omega < ∞) :
    ∃ K : Nat, ∀ k,
      HasTimeUpcrossingChain (factorialGridTimes T) a b
        (fun t => M t omega) k T → k ≤ K := by
  obtain ⟨K, hK⟩ :=
    (martingaleFactorialGridUpcrossings_lt_top_iff M T a b omega).1 hFinite
  refine ⟨K, fun k hChain => ?_⟩
  obtain ⟨r, N, hN, hTime, hGridChain⟩ :=
    HasTimeUpcrossingChain.exists_factorialGrid_chain hab (by
        refine mem_factorialGridTimes_iff.2 ⟨0, ?_⟩
        exact ⟨⟨size T 0, Nat.lt_succ_self _⟩, by
          exact (ChronologicalGrid.sampledTime_fin_eq
            (grid T 0) ⟨size T 0, Nat.lt_succ_self _⟩).symm.trans
              (sampledTime_size T 0)⟩) hChain
  have hExtended : HasUpcrossingChain a b ((grid T r).natSample M)
      omega k (size T r) := by
    exact hGridChain.mono_horizon hN
  exact (hExtended.le_upcrossingsBefore hab).trans (hK r)

/-- A martingale has a finite right limit along the union of the factorial
grids at every time strictly before the horizon, outside one null set. -/
theorem Martingale.exists_tendsto_factorialGridTimes_nhdsGT_ae
    [MeasurableSpace Omega]
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∀ t, t < T → ∃ c : Real,
      Tendsto (fun s => M s omega)
        (nhdsWithin t (factorialGridTimes T ∩ Ioi t)) (nhds c) := by
  filter_upwards
    [Martingale.factorialSkeleton_regularizationInputs_ae hM T hterminal]
      with omega hInputs
  intro t htT
  obtain ⟨C, hC⟩ := hInputs.1
  apply exists_tendsto_nhdsGT_of_bounded_upcrossingChains
      (factorialGridTimes T) (fun s => M s omega) t T htT
  · refine ⟨C, fun s hs => ?_⟩
    obtain ⟨n, hn⟩ := factorialGridTimes_subset_range_stoppedLimitSkeleton T hs
    rw [← hn]
    exact hC n
  · intro a b hab
    exact HasTimeUpcrossingChain.le_of_factorialGridUpcrossings_lt_top
      (Rat.cast_lt.2 hab) (hInputs.2 a b hab)

/-- A martingale has a finite left limit along the union of the factorial
grids at every positive time up to the horizon, outside one null set. -/
theorem Martingale.exists_tendsto_factorialGridTimes_nhdsLT_ae
    [MeasurableSpace Omega]
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∀ t, 0 < t -> t ≤ T -> ∃ c : Real,
      Tendsto (fun s => M s omega)
        (nhdsWithin t (factorialGridTimes T ∩ Iio t)) (nhds c) := by
  filter_upwards
    [Martingale.factorialSkeleton_regularizationInputs_ae hM T hterminal]
      with omega hInputs
  intro t ht htT
  obtain ⟨C, hC⟩ := hInputs.1
  apply exists_tendsto_nhdsLT_of_bounded_upcrossingChains
      (factorialGridTimes T) (fun s => M s omega) t T htT ht
  · refine ⟨C, fun s hs => ?_⟩
    obtain ⟨n, hn⟩ := factorialGridTimes_subset_range_stoppedLimitSkeleton T hs
    rw [← hn]
    exact hC n
  · intro a b hab
    exact HasTimeUpcrossingChain.le_of_factorialGridUpcrossings_lt_top
      (Rat.cast_lt.2 hab) (hInputs.2 a b hab)

end HorizonFactorialGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## The factorial-grid right-limit process

We choose the pathwise right limit along the union of the fixed-horizon
factorial grids.  At and beyond the horizon the original process is retained.
The preceding simultaneous upcrossing theorem then gives convergence to this
specific representative outside one null set.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- The selected right limit along all fixed-horizon factorial-grid times. -/
noncomputable def factorialGridRightLimit
    (M : Process Omega) (T : NNReal) : Process Omega :=
  fun t omega =>
    if t < T then
      limUnder (nhdsWithin t (factorialGridTimes T ∩ Ioi t))
        (fun s => M s omega)
    else M t omega

/-- Outside one null set, the martingale converges at every preterminal time
to the selected factorial-grid right-limit process. -/
theorem Martingale.tendsto_factorialGridRightLimit_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∀ t, t < T →
      Tendsto (fun s => M s omega)
        (nhdsWithin t (factorialGridTimes T ∩ Ioi t))
        (nhds (factorialGridRightLimit M T t omega)) := by
  filter_upwards
    [Martingale.exists_tendsto_factorialGridTimes_nhdsGT_ae
      hM T hterminal] with omega homega
  intro t ht
  have hExists := homega t ht
  simpa [factorialGridRightLimit, ht] using tendsto_nhds_limUnder hExists

/-- A deterministic right-approximating sequence identifies the selected
pathwise limit with any limit in measure of the same sampled martingale. -/
theorem Martingale.factorialGridRightLimit_ae_eq_of_sequence
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T t : NNReal) (ht : t < T)
    (hterminal : MemLp (M T) (2 : ENNReal) mu)
    (s : Nat -> NNReal)
    (hsMem : ∀ n, s n ∈ factorialGridTimes T)
    (hsRight : ∀ n, t < s n)
    (hsTendsto : Tendsto s atTop (nhds t))
    (hInMeasure : TendstoInMeasure mu (fun n omega => M (s n) omega)
      atTop (M t)) :
    factorialGridRightLimit M T t =ᵐ[mu] M t := by
  have hsWithin : Tendsto s atTop
      (nhdsWithin t (factorialGridTimes T ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.2 ⟨hsTendsto,
      Filter.Eventually.of_forall fun n => ⟨hsMem n, hsRight n⟩⟩
  obtain ⟨ns, hns, hSampleAE⟩ := hInMeasure.exists_seq_tendsto_ae
  filter_upwards
    [Martingale.tendsto_factorialGridRightLimit_ae hM T hterminal,
      hSampleAE]
      with omega hPath hSample
  exact tendsto_nhds_unique
    ((hPath t ht).comp hsWithin |>.comp hns.tendsto_atTop) hSample

end HorizonFactorialGrid

end FTAPTheorem42
