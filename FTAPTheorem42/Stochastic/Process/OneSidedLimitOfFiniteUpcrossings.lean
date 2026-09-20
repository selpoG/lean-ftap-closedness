/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Martingale.Upcrossing

/-!
# One-sided limits from finite upcrossing chains

A bounded real function has a right limit at a time `t` once the lengths of
all chronological upcrossing chains are bounded, for every rational interval.
The proof converts two frequently recurring separated values near `t` into
arbitrarily long chronological chains and then applies the standard dense-set
upcrossing criterion.
-/

open Filter Set Topology

namespace FTAPTheorem42

/-- `HasTimeUpcrossingChain a b u k U` records `k` chronologically ordered
upcrossings of `[a,b]`, all strictly before the time `U`. -/
def HasTimeUpcrossingChain
    (D : Set NNReal) (a b : Real) (u : NNReal -> Real) :
    Nat -> NNReal -> Prop
  | 0, _ => True
  | k + 1, U =>
      ∃ l ∈ D, ∃ v ∈ D, l ≤ v ∧ v < U ∧ u l < a ∧ b < u v ∧
        HasTimeUpcrossingChain D a b u k l

/-- Enlarging the terminal time preserves a chronological upcrossing chain. -/
theorem HasTimeUpcrossingChain.mono_horizon
    {D : Set NNReal} {a b : Real} {u : NNReal -> Real}
    {k : Nat} {U V : NNReal} (hUV : U ≤ V)
    (hChain : HasTimeUpcrossingChain D a b u k U) :
    HasTimeUpcrossingChain D a b u k V := by
  cases k with
  | zero => trivial
  | succ k =>
      obtain ⟨l, hlD, v, hvD, hlv, hvU, hLow, hHigh, hPrevious⟩ := hChain
      exact ⟨l, hlD, v, hvD, hlv, hvU.trans_le hUV,
        hLow, hHigh, hPrevious⟩

/-- If values below `a` and above `b` both occur frequently immediately to
the right of `t`, then there are chronological upcrossing chains of arbitrary
finite length before every later time. -/
theorem exists_hasTimeUpcrossingChain_of_frequently_nhdsGT
    {D : Set NNReal} {u : NNReal -> Real} {t : NNReal} {a b : Real}
    (hLow : ∃ᶠ s in nhdsWithin t (D ∩ Ioi t), u s < a)
    (hHigh : ∃ᶠ s in nhdsWithin t (D ∩ Ioi t), b < u s) :
    ∀ k U, t < U → HasTimeUpcrossingChain D a b u k U := by
  intro k
  induction k with
  | zero =>
      intro U _
      trivial
  | succ k ih =>
      intro U htU
      have hBeforeU : Iio U ∈ nhdsWithin t (D ∩ Ioi t) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htU)
      obtain ⟨v, hvHigh, hvU, hvD, hvRight⟩ :=
        (hHigh.and_eventually
          (inter_mem hBeforeU self_mem_nhdsWithin)).exists
      have hBeforeV : Iio v ∈ nhdsWithin t (D ∩ Ioi t) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hvRight)
      obtain ⟨l, hlLow, hlV, hlD, hlRight⟩ :=
        (hLow.and_eventually
          (inter_mem hBeforeV self_mem_nhdsWithin)).exists
      exact ⟨l, hlD, v, hvD, hlV.le, hvU, hlLow, hvHigh, ih l hlRight⟩

/-- A globally bounded function whose rational upcrossing-chain lengths are
uniformly bounded has a finite right limit at every time. -/
theorem exists_tendsto_nhdsGT_of_bounded_upcrossingChains
    (D : Set NNReal) (u : NNReal -> Real) (t T : NNReal) (htT : t < T)
    (hBound : ∃ C : Real, ∀ s ∈ D, abs (u s) ≤ C)
    (hChains : ∀ a b : Rat, a < b → ∃ K : Nat,
      ∀ k, HasTimeUpcrossingChain D a b u k T → k ≤ K) :
    ∃ c : Real, Tendsto u (nhdsWithin t (D ∩ Ioi t)) (nhds c) := by
  refine tendsto_of_no_upcrossings (s := Set.range ((↑) : Rat -> Real))
      Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    intro hFrequent
    obtain ⟨K, hK⟩ := hChains a b (Rat.cast_lt.1 hab)
    have hLong := exists_hasTimeUpcrossingChain_of_frequently_nhdsGT
      hFrequent.1 hFrequent.2 (K + 1) T htT
    exact (Nat.not_succ_le_self K) (hK (K + 1) hLong)
  · obtain ⟨C, hC⟩ := hBound
    have hAbs : (nhdsWithin t (D ∩ Ioi t)).IsBoundedUnder (· ≤ ·)
        (fun s => abs (u s)) :=
      isBoundedUnder_of_eventually_le <|
        eventually_mem_nhdsWithin.mono fun s hs => hC s hs.1
    exact (isBoundedUnder_le_abs.1 hAbs).1
  · obtain ⟨C, hC⟩ := hBound
    have hAbs : (nhdsWithin t (D ∩ Ioi t)).IsBoundedUnder (· ≤ ·)
        (fun s => abs (u s)) :=
      isBoundedUnder_of_eventually_le <|
        eventually_mem_nhdsWithin.mono fun s hs => hC s hs.1
    exact (isBoundedUnder_le_abs.1 hAbs).2

/-- If separated low and high values both occur frequently immediately to
the left of `t`, then arbitrarily long chronological upcrossing chains occur
before `t`. -/
theorem exists_hasTimeUpcrossingChain_of_frequently_nhdsLT
    {D : Set NNReal} {u : NNReal -> Real} {t : NNReal} {a b : Real}
    (hLow : ∃ᶠ s in nhdsWithin t (D ∩ Iio t), u s < a)
    (hHigh : ∃ᶠ s in nhdsWithin t (D ∩ Iio t), b < u s) :
    ∀ k L, L < t -> ∃ U, L < U ∧ U < t ∧
      HasTimeUpcrossingChain D a b u k U := by
  intro k
  induction k with
  | zero =>
      intro L hLt
      obtain ⟨U, hLU, hUt⟩ := exists_between hLt
      exact ⟨U, hLU, hUt, trivial⟩
  | succ k ih =>
      intro L hLt
      obtain ⟨U, hLU, hUt, hPrevious⟩ := ih L hLt
      have hAfterU : Ioi U ∈ nhdsWithin t (D ∩ Iio t) :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hUt)
      obtain ⟨l, hlLow, hlU, hlD, hlt⟩ :=
        (hLow.and_eventually
          (inter_mem hAfterU self_mem_nhdsWithin)).exists
      have hAfterL : Ioi l ∈ nhdsWithin t (D ∩ Iio t) :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)
      obtain ⟨v, hvHigh, hvl, hvD, hvt⟩ :=
        (hHigh.and_eventually
          (inter_mem hAfterL self_mem_nhdsWithin)).exists
      obtain ⟨W, hvW, hWt⟩ := exists_between (show v < t from hvt)
      refine ⟨W, hLU.trans (hlU.trans (hvl.trans hvW)), hWt,
        l, hlD, v, hvD, hvl.le, hvW, hlLow, hvHigh, ?_⟩
      exact hPrevious.mono_horizon hlU.le

/-- A globally bounded function whose rational upcrossing-chain lengths are
uniformly bounded has a finite left limit at each time before the supplied
terminal horizon. -/
theorem exists_tendsto_nhdsLT_of_bounded_upcrossingChains
    (D : Set NNReal) (u : NNReal -> Real) (t T : NNReal) (htT : t ≤ T)
    (ht : 0 < t)
    (hBound : ∃ C : Real, ∀ s ∈ D, abs (u s) ≤ C)
    (hChains : ∀ a b : Rat, a < b -> ∃ K : Nat,
      ∀ k, HasTimeUpcrossingChain D a b u k T -> k ≤ K) :
    ∃ c : Real, Tendsto u (nhdsWithin t (D ∩ Iio t)) (nhds c) := by
  refine tendsto_of_no_upcrossings (s := Set.range ((↑) : Rat -> Real))
      Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    intro hFrequent
    obtain ⟨K, hK⟩ := hChains a b (Rat.cast_lt.1 hab)
    obtain ⟨U, _, hUt, hLong⟩ :=
      exists_hasTimeUpcrossingChain_of_frequently_nhdsLT
        hFrequent.1 hFrequent.2 (K + 1) 0 ht
    have hLongT := hLong.mono_horizon (hUt.le.trans htT)
    exact (Nat.not_succ_le_self K) (hK (K + 1) hLongT)
  · obtain ⟨C, hC⟩ := hBound
    have hAbs : (nhdsWithin t (D ∩ Iio t)).IsBoundedUnder (· ≤ ·)
        (fun s => abs (u s)) :=
      isBoundedUnder_of_eventually_le <|
        eventually_mem_nhdsWithin.mono fun s hs => hC s hs.1
    exact (isBoundedUnder_le_abs.1 hAbs).1
  · obtain ⟨C, hC⟩ := hBound
    have hAbs : (nhdsWithin t (D ∩ Iio t)).IsBoundedUnder (· ≤ ·)
        (fun s => abs (u s)) :=
      isBoundedUnder_of_eventually_le <|
        eventually_mem_nhdsWithin.mono fun s hs => hC s hs.1
    exact (isBoundedUnder_le_abs.1 hAbs).2

end FTAPTheorem42
