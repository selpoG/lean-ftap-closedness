/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Topology.Order.LeftRightLim

/-!
# Right continuity of limits selected on a dense time set

Suppose that, before a fixed horizon, `g t` is the right limit of values of
`u` restricted to a time set `D`. If the corresponding restricted right
neighbourhood filters are nontrivial, then `g` is right-continuous before the
horizon. Closed neighbourhoods allow the limit at a nearby time to inherit
the same bound as the original values on `D`.
-/

open Filter Set Topology

namespace FTAPTheorem42

/-- Right limits taken along a common time set form a right-continuous
function. The upper horizon only records the interval on which those limits
are known to exist. -/
theorem continuousWithinAt_Ici_of_tendsto_denseRight
    {D : Set NNReal} {u g : NNReal -> Real} {t T : NNReal} (ht : t < T)
    (hLim : ∀ s, s < T ->
      Tendsto u (nhdsWithin s (D ∩ Ioi s)) (nhds (g s)))
    (hNeBot : ∀ s, s < T -> (nhdsWithin s (D ∩ Ioi s)).NeBot) :
    ContinuousWithinAt g (Ici t) t := by
  have hIci : nhdsWithin t (Ici t) = nhdsWithin t (Ioi t) ⊔ pure t := by
    have hSet : Ici t = Ioi t ∪ {t} := by
      ext s
      simp only [mem_Ici, mem_union, mem_Ioi, mem_singleton_iff]
      constructor
      · intro hts
        rcases lt_or_eq_of_le hts with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      · intro h
        rcases h with h | h
        · exact h.le
        · subst s
          exact le_rfl
    rw [hSet, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, hIci, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (g t)).tendsto_right_iff.2
  intro C hC
  have hPreimage : {s | u s ∈ C} ∈ nhdsWithin t (D ∩ Ioi t) :=
    hLim t ht hC.1
  obtain ⟨V, hV, hVsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hPreimage
  have hVRight : V ∈ nhdsWithin t (Ioi t) :=
    mem_nhdsWithin_of_mem_nhds hV
  obtain ⟨b, htb, hbV⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' ht).1 hVRight
  let b' := min b T
  have htb' : t < b' := lt_min htb ht
  filter_upwards [Ioo_mem_nhdsGT htb'] with s hs
  have hsT : s < T := hs.2.trans_le (min_le_right b T)
  let _ := hNeBot s hsT
  apply hC.2.mem_of_tendsto (hLim s hsT)
  filter_upwards [eventually_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2)] with r hrWithin hrb
  apply hVsub
  refine ⟨hbV ⟨hs.1.trans hrWithin.2,
    hrb.trans_le (min_le_left b T)⟩, hrWithin.1, ?_⟩
  exact hs.1.trans hrWithin.2

/-- A left limit on the dense time set is also the left limit of the function
formed from its dense-set right limits. -/
theorem tendsto_nhdsLT_of_tendsto_denseLeftRight
    {D : Set NNReal} {u g : NNReal -> Real} {t : NNReal}
    {z : Real} (ht : 0 < t)
    (hLeft : Tendsto u (nhdsWithin t (D ∩ Iio t)) (nhds z))
    (hRight : ∀ s, s < t ->
      Tendsto u (nhdsWithin s (D ∩ Ioi s)) (nhds (g s)))
    (hNeBot : ∀ s, s < t -> (nhdsWithin s (D ∩ Ioi s)).NeBot) :
    Tendsto g (nhdsWithin t (Iio t)) (nhds z) := by
  apply (closed_nhds_basis z).tendsto_right_iff.2
  intro C hC
  have hPreimage : {s | u s ∈ C} ∈ nhdsWithin t (D ∩ Iio t) :=
    hLeft hC.1
  obtain ⟨V, hV, hVsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hPreimage
  have hVLeft : V ∈ nhdsWithin t (Iio t) :=
    mem_nhdsWithin_of_mem_nhds hV
  obtain ⟨a, hat, haV⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset' ht).1 hVLeft
  filter_upwards [Ioo_mem_nhdsLT hat] with s hs
  let _ := hNeBot s hs.2
  apply hC.2.mem_of_tendsto (hRight s hs.2)
  filter_upwards [eventually_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2)] with r hrWithin hrt
  apply hVsub
  refine ⟨haV ⟨hs.1.trans hrWithin.2, hrt⟩, hrWithin.1, hrt⟩

/-- Stopping before the upper endpoint turns right continuity known only
below that endpoint into global right continuity. -/
theorem continuousWithinAt_deterministicallyStopped_of_before
    {f : NNReal -> Real} {R T : NNReal} (hRT : R < T)
    (hRight : ∀ s, s < T -> ContinuousWithinAt f (Ici s) s) :
    ∀ t, ContinuousWithinAt (fun s => f (min s R)) (Ici t) t := by
  intro t
  have hminT : min t R < T := (min_le_right t R).trans_lt hRT
  let q : NNReal -> NNReal := fun s => min s R
  have hmin : ContinuousWithinAt q (Ici t) t := by
    fun_prop
  have hmaps : MapsTo q (Ici t) (Ici (min t R)) :=
    fun _ hs => min_le_min_right R hs
  simpa only [Function.comp_def] using
    (hRight (min t R) hminT).comp_of_eq hmin hmaps rfl

/-- If left limits are known up to a deterministic stopping time, the
stopped function has left limits at every time. -/
theorem deterministicallyStopped_hasLeftLimits_of_before
    {f : NNReal -> Real} {R : NNReal}
    (hLeft : ∀ t, 0 < t -> t ≤ R -> Tendsto f (nhdsWithin t (Iio t))
      (nhds (Function.leftLim f t))) :
    ∀ t, Tendsto (fun s => f (min s R)) (nhdsWithin t (Iio t))
      (nhds (Function.leftLim (fun s => f (min s R)) t)) := by
  intro t
  apply tendsto_leftLim_of_tendsto
  by_cases ht0 : t = 0
  · subst t
    refine ⟨f (min 0 R), ?_⟩
    simp
  by_cases htR : t ≤ R
  · have ht : 0 < t := bot_lt_iff_ne_bot.2 ht0
    have hEq : (fun s => f (min s R)) =ᶠ[nhdsWithin t (Iio t)] f := by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      rw [min_eq_left (hs.le.trans htR)]
    exact ⟨Function.leftLim f t, (hLeft t ht htR).congr' hEq.symm⟩
  · have hRt : R < t := lt_of_not_ge htR
    have hEq : (fun s => f (min s R)) =ᶠ[nhdsWithin t (Iio t)]
        (fun _ => f R) := by
      filter_upwards
        [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hRt)] with s hs
      rw [min_eq_right hs.le]
    exact ⟨f R, tendsto_const_nhds.congr' hEq.symm⟩

end FTAPTheorem42
