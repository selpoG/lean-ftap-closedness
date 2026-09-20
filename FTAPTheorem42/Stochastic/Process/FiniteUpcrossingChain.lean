/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Martingale.Upcrossing

/-!
# Explicit finite upcrossing chains

An explicit chain records finitely many chronologically ordered visits below
`a` followed by visits above `b`.  Such a chain gives a lower bound for
mathlib's stopping-time definition `upcrossingsBefore`.  This combinatorial
bridge is independent of measurability and martingale assumptions.
-/

open MeasureTheory

namespace FTAPTheorem42

/-- `HasUpcrossingChain a b f omega k N` records `k` completed upcrossings
strictly before the natural-time horizon `N`.  The recursive chain is stored
from the latest pair backwards. -/
def HasUpcrossingChain {Omega : Type*}
    (a b : Real) (f : Nat -> Omega -> Real) (omega : Omega) :
    Nat -> Nat -> Prop
  | 0, _ => True
  | k + 1, N =>
      ∃ l u, l <= u ∧ u < N ∧ f l omega < a ∧ b < f u omega ∧
        HasUpcrossingChain a b f omega k l

/-- Enlarging the terminal index preserves an explicit crossing chain. -/
theorem HasUpcrossingChain.mono_horizon
    {Omega : Type*} {a b : Real} {f : Nat -> Omega -> Real}
    {omega : Omega} {k N P : Nat} (hNP : N <= P)
    (hChain : HasUpcrossingChain a b f omega k N) :
    HasUpcrossingChain a b f omega k P := by
  cases k with
  | zero => trivial
  | succ k =>
      obtain ⟨l, u, hlu, huN, hLow, hHigh, hPrevious⟩ := hChain
      exact ⟨l, u, hlu, huN.trans_le hNP, hLow, hHigh, hPrevious⟩

/-- A strictly increasing reindexing transports an explicit crossing chain. -/
theorem HasUpcrossingChain.map
    {Omega : Type*} {a b : Real} {f g : Nat -> Omega -> Real}
    {omega : Omega} {k N : Nat} (phi : Nat -> Nat)
    (hphi : StrictMono phi)
    (hfg : ∀ i, i < N -> g (phi i) omega = f i omega)
    (hChain : HasUpcrossingChain a b f omega k N) :
    HasUpcrossingChain a b g omega k (phi N) := by
  induction k generalizing N with
  | zero => trivial
  | succ k ih =>
      obtain ⟨l, u, hlu, huN, hLow, hHigh, hPrevious⟩ := hChain
      refine ⟨phi l, phi u, hphi.monotone hlu, hphi huN, ?_, ?_, ?_⟩
      · simpa only [hfg l (hlu.trans_lt huN)] using hLow
      · simpa only [hfg u huN] using hHigh
      · exact ih (fun i hi => hfg i
          (hi.trans (hlu.trans_lt huN))) hPrevious

/-- An explicit crossing chain is counted by `upcrossingsBefore`. -/
theorem HasUpcrossingChain.le_upcrossingsBefore
    {Omega : Type*} {a b : Real} {f : Nat -> Omega -> Real}
    {omega : Omega} (hab : a < b) :
    ∀ {k N}, HasUpcrossingChain a b f omega k N ->
      k <= upcrossingsBefore a b f N omega := by
  intro k
  induction k with
  | zero =>
      intro N _
      exact Nat.zero_le _
  | succ k ih =>
      intro N hChain
      obtain ⟨l, u, hlu, huN, hLow, hHigh, hPrevious⟩ := hChain
      have hPreviousCount :
          k <= upcrossingsBefore a b f l omega :=
        ih hPrevious
      have hStrict :
          upcrossingsBefore a b f l omega <
            upcrossingsBefore a b f (u + 1) omega :=
        upcrossingsBefore_lt_of_exists_upcrossing hab le_rfl hLow hlu hHigh
      have hTerminal : u + 1 <= N := huN
      exact Nat.succ_le_of_lt <| hPreviousCount.trans_lt <|
        hStrict.trans_le (upcrossingsBefore_mono hab hTerminal omega)

end FTAPTheorem42
