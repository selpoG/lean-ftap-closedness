/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Process.CadlagPathBoundedness
import FTAPTheorem42.Foundations.Variation

/-!
# Finite large-jump paths

This file is the deterministic path core for the large-jump part of the
Doléans--Dade--Yen construction.  A càdlàg real path has only finitely many
left jumps larger than a fixed positive threshold on a compact initial
interval.  The retained jumps are then summed in chronological order.

No enumeration of a dense time skeleton is used here.
-/

open Filter Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace FTAPTheorem42

/-! ## Local isolation of large jumps -/

noncomputable def cadlagLeftJump (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f t - Function.leftLim f t

private lemma leftLim_close_right
    {f : ℝ≥0 → ℝ}
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {t s d : ℝ≥0} (hts : t < s) (hsd : s < d) {ε : ℝ}
    (hbound : ∀ u ∈ Ico t d, dist (f u) (f t) < ε) :
    dist (Function.leftLim f s) (f t) ≤ ε := by
  let : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨t, hts⟩
  have hmem : Ico t d ∈ 𝓝[<] s := by
    apply Filter.mem_of_superset (Ico_mem_nhdsLT hts)
    intro u hu
    exact ⟨hu.1, hu.2.trans hsd⟩
  have hevent : ∀ᶠ u in 𝓝[<] s, dist (f u) (f t) ≤ ε :=
    Filter.Eventually.mono hmem (fun u hu => (hbound u hu).le)
  have hc : Function.leftLim f s ∈ Metric.closedBall (f t) ε := by
    apply Metric.isClosed_closedBall.mem_of_tendsto (hLeft s)
    exact hevent
  exact Metric.mem_closedBall.mp hc

private lemma leftLim_close_left
    {f : ℝ≥0 → ℝ}
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {d s t : ℝ≥0} (hds : d < s) (hst : s < t) {ε : ℝ}
    (hbound : ∀ u ∈ Ioo d t,
      dist (f u) (Function.leftLim f t) < ε) :
    dist (Function.leftLim f s) (Function.leftLim f t) ≤ ε := by
  let : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨d, hds⟩
  have hmem : Ioo d t ∈ 𝓝[<] s := by
    apply Filter.mem_of_superset (Ioo_mem_nhdsLT hds)
    intro u hu
    exact ⟨hu.1, hu.2.trans hst⟩
  have hevent : ∀ᶠ u in 𝓝[<] s,
      dist (f u) (Function.leftLim f t) ≤ ε :=
    Filter.Eventually.mono hmem (fun u hu => (hbound u hu).le)
  have hc : Function.leftLim f s ∈
      Metric.closedBall (Function.leftLim f t) ε := by
    apply Metric.isClosed_closedBall.mem_of_tendsto (hLeft s)
    exact hevent
  exact Metric.mem_closedBall.mp hc

private lemma exists_right_interval
    {f : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ContinuousWithinAt f (Ici t) t) {ε : ℝ} (hε : 0 < ε) :
    ∃ d, t < d ∧ ∀ u ∈ Ico t d, dist (f u) (f t) < ε := by
  have hball : {u | f u ∈ Metric.ball (f t) ε} ∈ 𝓝[Ici t] t := by
    exact h.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  obtain ⟨d, htd, hd⟩ := (nhdsGE_basis_Ico t).mem_iff.mp hball
  refine ⟨d, htd, ?_⟩
  intro u hu
  exact Metric.mem_ball.mp (hd hu)

private lemma exists_left_interval
    {f : ℝ≥0 → ℝ} {t : ℝ≥0} (ht : 0 < t) {ε : ℝ}
    (h : Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (hε : 0 < ε) :
    ∃ d, d < t ∧ ∀ u ∈ Ioo d t,
      dist (f u) (Function.leftLim f t) < ε := by
  have hball : ∀ᶠ u in 𝓝[<] t,
      f u ∈ Metric.ball (Function.leftLim f t) ε := by
    exact h.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  obtain ⟨d, hdt, hd⟩ :=
    (nhdsLT_basis_of_exists_lt ⟨0, ht⟩).mem_iff.mp hball
  refine ⟨d, hdt, ?_⟩
  intro u hu
  exact Metric.mem_ball.mp (hd hu)

private lemma large_jump_isolated
    {f : ℝ≥0 → ℝ}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    {c : ℝ} (hc : 0 < c) {t : ℝ≥0} (ht : 0 < t) :
    ∃ u, IsOpen u ∧ t ∈ u ∧
      ∀ s ∈ u, |cadlagLeftJump f s| > c → s = t := by
  let ε : ℝ := c / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨dL, hdLt, hL⟩ := exists_left_interval ht (hLeft t) hε
  obtain ⟨dR, htR, hR⟩ := exists_right_interval (hRight t) hε
  refine ⟨Ioo dL dR, isOpen_Ioo, ⟨hdLt, htR⟩, ?_⟩
  intro s hs hsjump
  by_cases hst : s = t
  · exact hst
  rcases lt_or_gt_of_ne hst with hst | hst
  · have hfirst : dist (f s) (Function.leftLim f t) < ε :=
      hL s ⟨hs.1, hst⟩
    have hsecond : dist (Function.leftLim f s) (Function.leftLim f t) ≤ ε :=
      leftLim_close_left hLeft hs.1 hst (fun u hu => hL u hu)
    have hbound : |cadlagLeftJump f s| < c := by
      dsimp [cadlagLeftJump]
      calc
        |f s - Function.leftLim f s| =
            dist (f s) (Function.leftLim f s) := by rw [Real.dist_eq]
        _ ≤ dist (f s) (Function.leftLim f t) +
              dist (Function.leftLim f t) (Function.leftLim f s) :=
          dist_triangle _ _ _
        _ < c := by
          rw [dist_comm (Function.leftLim f t) (Function.leftLim f s)]
          dsimp [ε] at *
          linarith
    exact False.elim ((not_lt_of_ge hsjump.le) hbound)
  · have hfirst : dist (f s) (f t) < ε :=
      hR s ⟨hst.le, hs.2⟩
    have hsecond : dist (Function.leftLim f s) (f t) ≤ ε :=
      leftLim_close_right hLeft hst hs.2 (fun u hu => hR u hu)
    have hbound : |cadlagLeftJump f s| < c := by
      dsimp [cadlagLeftJump]
      calc
        |f s - Function.leftLim f s| =
            dist (f s) (Function.leftLim f s) := by rw [Real.dist_eq]
        _ ≤ dist (f s) (f t) + dist (f t) (Function.leftLim f s) :=
          dist_triangle _ _ _
        _ < c := by
          rw [dist_comm (f t) (Function.leftLim f s)]
          dsimp [ε] at *
          linarith
    exact False.elim ((not_lt_of_ge hsjump.le) hbound)

/-! ## The finite set of retained jump times -/

noncomputable def largeJumpTimeSet
    (f : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) : Set ℝ≥0 :=
  Ioc 0 T ∩ {t | c < |cadlagLeftJump f t|}

private lemma large_jump_isolated_zero
    {f : ℝ≥0 → ℝ}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    {c : ℝ} (hc : 0 < c) :
    ∃ d, 0 < d ∧ ∀ s ∈ Ico 0 d, |cadlagLeftJump f s| < c := by
  obtain ⟨d, hd, hR⟩ := exists_right_interval (hRight 0) (by linarith : 0 < c / 3)
  refine ⟨d, hd, ?_⟩
  intro s hs
  by_cases hst : s = 0
  · subst s
    have hleft : Function.leftLim f 0 = f 0 :=
      leftLim_eq_of_isBot isBot_bot
    simpa [cadlagLeftJump, hleft] using hc
  · have hts : 0 < s := (pos_iff_ne_zero).2 hst
    have hsecond : dist (Function.leftLim f s) (f 0) ≤ c / 3 :=
      leftLim_close_right hLeft hts hs.2 (fun u hu => hR u hu)
    have hfirst : dist (f s) (f 0) < c / 3 := hR s hs
    dsimp [cadlagLeftJump]
    calc
      |f s - Function.leftLim f s| =
          dist (f s) (Function.leftLim f s) := by rw [Real.dist_eq]
      _ ≤ dist (f s) (f 0) + dist (f 0) (Function.leftLim f s) :=
        dist_triangle _ _ _
      _ < c := by
        rw [dist_comm (f 0) (Function.leftLim f s)]
        linarith

theorem finite_largeJumpTimeSet
    {f : ℝ≥0 → ℝ}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    {c : ℝ} (hc : 0 < c) (T : ℝ≥0) :
    (largeJumpTimeSet f c T).Finite := by
  let J := largeJumpTimeSet f c T
  have hclosed : IsClosed J := by
    apply isClosed_iff_nhds.2
    intro t ht
    by_cases htJ : t ∈ J
    · exact htJ
    by_cases ht0 : t = 0
    · obtain ⟨d, hd, hsmall⟩ := large_jump_isolated_zero hRight hLeft hc
      have hmem : Iio d ∈ 𝓝 t := by simpa [ht0] using Iio_mem_nhds hd
      have hnonempty := ht (Iio d) hmem
      rcases hnonempty with ⟨s, hsd, hsJ⟩
      exact (not_lt_of_ge (hsmall s ⟨bot_le, hsd⟩).le hsJ.2).elim
    by_cases htT : t ≤ T
    · have htpos : 0 < t := (pos_iff_ne_zero).2 ht0
      obtain ⟨u, hu, htu, huniq⟩ :=
        large_jump_isolated hRight hLeft hc htpos
      have hmem : u ∈ 𝓝 t := hu.mem_nhds htu
      have hnonempty := ht u hmem
      rcases hnonempty with ⟨s, hsu, hsJ⟩
      have hst : s = t := huniq s hsu hsJ.2
      exact (htJ (hst ▸ hsJ)).elim
    · have hTt : T < t := lt_of_not_ge htT
      have hmem : Ioi T ∈ 𝓝 t := Ioi_mem_nhds hTt
      have hnonempty := ht (Ioi T) hmem
      rcases hnonempty with ⟨s, hst, hsJ⟩
      exact (not_lt_of_ge hsJ.1.2 hst).elim
  have hcompact : IsCompact J := by
    have hsub : J ⊆ Icc 0 T := by
      intro t ht
      exact ⟨ht.1.1.le, ht.1.2⟩
    rw [show J = Icc 0 T ∩ J by
      ext t
      constructor
      · intro ht
        exact ⟨hsub ht, ht⟩
      · intro ht
        exact ht.2]
    exact isCompact_Icc.inter_right hclosed
  have hdisc : IsDiscrete J := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro t ht
    have htpos : 0 < t := ht.1.1
    obtain ⟨u, hu, htu, huniq⟩ :=
      large_jump_isolated hRight hLeft hc htpos
    refine ⟨u, hu, ?_⟩
    ext s
    constructor
    · rintro ⟨hsu, hsJ⟩
      have hst : s = t := huniq s hsu hsJ.2
      subst s
      simp
    · intro hs
      have hst : s = t := by simpa using hs
      subst s
      exact ⟨htu, ht⟩
  exact hcompact.finite hdisc

/-! ## Elementary finite-step variation bounds -/

private lemma eVariationOn_finset_sum_le
    {ι : Type*} (I : Finset ι) {f : ι → ℝ≥0 → ℝ} (s : Set ℝ≥0) :
    eVariationOn (fun t => (∑ i ∈ I, f i t)) s ≤
      ∑ i ∈ I, eVariationOn (f i) s := by
  classical
  apply iSup_le
  intro p
  rcases p with ⟨n, u⟩
  rcases u with ⟨u, hu, hus⟩
  dsimp only [Prod.fst, Prod.snd, Subtype.coe_mk]
  change (∑ i ∈ Finset.range n,
        edist (∑ j ∈ I, f j (u (i + 1))) (∑ j ∈ I, f j (u i))) ≤
      ∑ j ∈ I, eVariationOn (f j) s
  calc
    (∑ i ∈ Finset.range n,
        edist (∑ j ∈ I, f j (u (i + 1))) (∑ j ∈ I, f j (u i))) =
      ∑ i ∈ Finset.range n, edist (∑ j ∈ I, f j (u (i + 1)))
        (∑ j ∈ I, f j (u i)) := by rfl
    _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ I,
        edist (f j (u (i + 1))) (f j (u i)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [edist_dist]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_mono (dist_sum_sum_le I
          (fun j => f j (u (i + 1))) (fun j => f j (u i)))
      · intro j hj
        exact dist_nonneg
    _ = ∑ j ∈ I, ∑ i ∈ Finset.range n,
        edist (f j (u (i + 1))) (f j (u i)) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ I, eVariationOn (f j) s := by
      apply Finset.sum_le_sum
      intro j hj
      exact eVariationOn.sum_le hu hus

private noncomputable def finiteStep
    (s : ℝ≥0) (a : ℝ) (t : ℝ≥0) : ℝ := if s ≤ t then a else 0

private lemma finiteStep_mono {s : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) :
    Monotone (finiteStep s a) := by
  intro u v huv
  by_cases hus : s ≤ u
  · simp [finiteStep, hus, hus.trans huv]
  · by_cases hvs : s ≤ v
    · simp [finiteStep, hus, hvs, ha]
    · simp [finiteStep, hus, hvs]

private lemma eVariationOn_finiteStep_le_of_nonneg
    {s : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) :
    eVariationOn (finiteStep s a) Set.univ ≤ ENNReal.ofReal a := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [mem_ofPred_eq, iSup_le_iff, Prod.forall, Set.mem_univ, true_and]
  intro x y hxy
  rw [(monotoneOn_univ.mpr (finiteStep_mono ha)).eVariationOn_eq
    (Set.mem_univ _) (Set.mem_univ _)]
  apply ENNReal.ofReal_mono
  by_cases hxs : s ≤ x
  · simp [finiteStep, hxs, hxs.trans hxy, ha]
  · by_cases hys : s ≤ y
    · simp [finiteStep, hxs, hys]
    · simpa [finiteStep, hxs, hys] using ha

private lemma eVariationOn_finiteStep_le {s : ℝ≥0} {a : ℝ} :
    eVariationOn (finiteStep s a) Set.univ ≤ ENNReal.ofReal |a| := by
  by_cases ha : 0 ≤ a
  · simpa [abs_of_nonneg ha] using eVariationOn_finiteStep_le_of_nonneg ha
  · have hnega : 0 ≤ -a := le_of_lt (neg_pos.mpr (lt_of_not_ge ha))
    rw [show finiteStep s a = fun t => - finiteStep s (-a) t by
      funext t
      by_cases hst : s ≤ t <;> simp [finiteStep, hst]]
    rw [pathVariation_neg]
    simpa [abs_of_neg (lt_of_not_ge ha)] using
      eVariationOn_finiteStep_le_of_nonneg hnega

private lemma finiteStep_continuousWithinAt
    {s t : ℝ≥0} {a : ℝ} :
    ContinuousWithinAt (finiteStep s a) (Ici t) t := by
  by_cases hst : s ≤ t
  · apply (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : ℝ≥0 => a) (Ici t) t).congr
    · intro u hu
      have hsu : s ≤ u := hst.trans hu
      simp [finiteStep, hsu]
    · simp [finiteStep, hst]
  · have hts : t < s := lt_of_not_ge hst
    have hev : finiteStep s a =ᶠ[𝓝[Ici t] t] (fun _ => 0) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_of_mem (Iio_mem_nhds hts) (fun u hu => by
          change u < s at hu
          simp [finiteStep, not_le_of_gt hu]))
    exact ContinuousWithinAt.congr_of_eventuallyEq
      (f := fun _ : ℝ≥0 => (0 : ℝ)) (g := finiteStep s a)
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Ici t) t)
      hev (by simp [finiteStep, hst])

private lemma finiteStep_left_tendsto
    {s t : ℝ≥0} {a : ℝ} :
    Tendsto (finiteStep s a) (𝓝[<] t)
      (𝓝 (if s < t then a else 0)) := by
  by_cases ht : t = 0
  · subst t
    have hbot : 𝓝[<] (0 : ℝ≥0) = (⊥ : Filter ℝ≥0) := by simp
    rw [hbot]
    exact tendsto_bot
  by_cases hst : s < t
  · have hev : finiteStep s a =ᶠ[𝓝[<] t] (fun _ => a) := by
      have hmem : ∀ᶠ u in 𝓝[<] t, s ≤ u :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (eventually_of_mem (Ioi_mem_nhds hst) (fun u hu => le_of_lt hu))
      filter_upwards [hmem] with u hu
      simp [finiteStep, hu]
    rw [ite_eq_left hst]
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 => a) (𝓝[<] t) (𝓝 a)).congr' hev.symm
  · have hev_lt : ∀ᶠ u in 𝓝[<] t, u < s := by
      by_cases hts : t < s
      · exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (eventually_of_mem (Iio_mem_nhds hts) (fun u hu => by
            change u < s at hu
            exact hu))
      · have hst' : t ≤ s := le_of_not_gt hst
        filter_upwards [self_mem_nhdsWithin] with u hu
        change u < t at hu
        exact hu.trans_le hst'
    have hev : finiteStep s a =ᶠ[𝓝[<] t] (fun _ => 0) := by
      filter_upwards [hev_lt] with u hu
      change u < s at hu
      simp [finiteStep, not_le_of_gt hu]
    rw [ite_eq_right hst]
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[<] t) (𝓝 (0 : ℝ))).congr' hev.symm

/-! ## Finite chronological data and the path it generates -/

structure LargeJumpPathData (f : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) where
  times : Finset ℝ≥0
  times_mem : ∀ t, t ∈ times ↔ t ∈ largeJumpTimeSet f c T

noncomputable def largeJumpPathData
    {f : ℝ≥0 → ℝ} {c : ℝ} {T : ℝ≥0}
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (hc : 0 < c) : LargeJumpPathData f c T := by
  let hfinite := finite_largeJumpTimeSet hRight hLeft hc T
  exact ⟨hfinite.toFinset, fun t => by
    simp [hfinite.mem_toFinset]⟩

namespace LargeJumpPathData

variable {f : ℝ≥0 → ℝ} {c : ℝ} {T : ℝ≥0}

noncomputable def jump (_D : LargeJumpPathData f c T) (t : ℝ≥0) : ℝ :=
  cadlagLeftJump f t

noncomputable def path (D : LargeJumpPathData f c T) (t : ℝ≥0) : ℝ :=
  ∑ s ∈ D.times, if s ≤ t then D.jump s else 0

noncomputable def leftPath (D : LargeJumpPathData f c T) (t : ℝ≥0) : ℝ :=
  ∑ s ∈ D.times, if s < t then D.jump s else 0

theorem times_pos (D : LargeJumpPathData f c T) {t : ℝ≥0}
    (ht : t ∈ D.times) : 0 < t := by
  have hJ : t ∈ largeJumpTimeSet f c T := (D.times_mem t).1 ht
  exact hJ.1.1

theorem path_zero (D : LargeJumpPathData f c T) : D.path 0 = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  rw [ite_eq_right]
  exact not_le_of_gt (D.times_pos ht)

theorem leftPath_zero (D : LargeJumpPathData f c T) : D.leftPath 0 = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  rw [ite_eq_right]
  exact not_lt_of_ge bot_le

theorem path_continuousWithinAt
    (D : LargeJumpPathData f c T) (t : ℝ≥0) :
    ContinuousWithinAt D.path (Ici t) t := by
  change Tendsto (fun u => ∑ s ∈ D.times,
      finiteStep s (D.jump s) u) (𝓝[Ici t] t)
    (𝓝 (∑ s ∈ D.times, finiteStep s (D.jump s) t))
  apply tendsto_finsetSum D.times
  intro s hs
  exact finiteStep_continuousWithinAt

theorem path_left_tendsto
    (D : LargeJumpPathData f c T) (t : ℝ≥0) :
    Tendsto D.path (𝓝[<] t) (𝓝 (D.leftPath t)) := by
  change Tendsto (fun u => ∑ s ∈ D.times,
      finiteStep s (D.jump s) u) (𝓝[<] t)
    (𝓝 (∑ s ∈ D.times, if s < t then D.jump s else 0))
  apply tendsto_finsetSum D.times
  intro s hs
  simpa [finiteStep] using
    (finiteStep_left_tendsto (s := s) (t := t) (a := D.jump s))

theorem path_leftLim_eq
    (D : LargeJumpPathData f c T) (t : ℝ≥0) :
    Function.leftLim D.path t = D.leftPath t := by
  by_cases ht : t = 0
  · subst t
    have hleft : Function.leftLim D.path 0 = D.path 0 :=
      leftLim_eq_of_isBot isBot_bot
    rw [hleft, D.path_zero, D.leftPath_zero]
  · let : NeBot (𝓝[<] t) :=
      nhdsLT_neBot_of_exists_lt ⟨0, (pos_iff_ne_zero).2 ht⟩
    exact leftLim_eq_of_tendsto (D.path_left_tendsto t)

theorem path_hasLeftLimits
    (D : LargeJumpPathData f c T) :
    ∀ t, Tendsto D.path (𝓝[<] t) (𝓝 (Function.leftLim D.path t)) := by
  intro t
  rw [D.path_leftLim_eq]
  exact D.path_left_tendsto t

theorem path_sub_leftPath
    (D : LargeJumpPathData f c T) (t : ℝ≥0) :
    D.path t - D.leftPath t =
      ∑ s ∈ D.times, if s = t then D.jump s else 0 := by
  simp only [path, leftPath, jump]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hst : s = t
  · subst s
    simp
  · by_cases hle : s ≤ t
    · have hlt : s < t := lt_of_le_of_ne hle hst
      simp [hle, hlt, hst]
    · have hlt : ¬s < t := not_lt_of_ge (le_of_not_ge hle)
      simp [hle, hlt, hst]

theorem path_leftJump_eq
    (D : LargeJumpPathData f c T) (t : ℝ≥0) :
    D.path t - Function.leftLim D.path t =
      ∑ s ∈ D.times, if s = t then D.jump s else 0 := by
  rw [D.path_leftLim_eq]
  exact D.path_sub_leftPath t

theorem path_leftJump_eq_of_mem
    (D : LargeJumpPathData f c T) {t : ℝ≥0} (ht : t ∈ D.times) :
    D.path t - Function.leftLim D.path t = D.jump t := by
  rw [D.path_leftJump_eq]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s hs hst
    simp [hst]
  · exact fun h => (h ht).elim

theorem path_leftJump_eq_of_not_mem
    (D : LargeJumpPathData f c T) {t : ℝ≥0} (ht : t ∉ D.times) :
    D.path t - Function.leftLim D.path t = 0 := by
  rw [D.path_leftJump_eq]
  apply Finset.sum_eq_zero
  intro s hs
  have hst : s ≠ t := by
    intro hst
    exact ht (hst ▸ hs)
  simp [hst]

theorem path_leftJump_eq_of_large
    (D : LargeJumpPathData f c T) {t : ℝ≥0}
    (ht : t ∈ largeJumpTimeSet f c T) :
    D.path t - Function.leftLim D.path t = cadlagLeftJump f t := by
  exact D.path_leftJump_eq_of_mem ((D.times_mem t).2 ht)

theorem path_leftJump_eq_of_not_large
    (D : LargeJumpPathData f c T) {t : ℝ≥0}
    (ht : t ∉ largeJumpTimeSet f c T) :
    D.path t - Function.leftLim D.path t = 0 := by
  exact D.path_leftJump_eq_of_not_mem (by
    intro htimes
    exact ht ((D.times_mem t).1 htimes))

theorem path_eVariationOn_univ_le_totalJumpSize
    (D : LargeJumpPathData f c T) :
    eVariationOn D.path Set.univ ≤
      ∑ s ∈ D.times, ENNReal.ofReal |D.jump s| := by
  have hpath : D.path = fun t =>
      ∑ s ∈ D.times, finiteStep s (D.jump s) t := by
    funext t
    rfl
  rw [hpath]
  calc
    eVariationOn (fun t => ∑ s ∈ D.times,
        finiteStep s (D.jump s) t) Set.univ ≤
        ∑ s ∈ D.times, eVariationOn
          (finiteStep s (D.jump s)) Set.univ :=
      eVariationOn_finset_sum_le D.times Set.univ
    _ ≤ ∑ s ∈ D.times, ENNReal.ofReal |D.jump s| := by
      apply Finset.sum_le_sum
      intro s hs
      exact eVariationOn_finiteStep_le

theorem path_boundedVariationOn_univ
    (D : LargeJumpPathData f c T) :
    BoundedVariationOn D.path Set.univ := by
  exact ne_of_lt ((D.path_eVariationOn_univ_le_totalJumpSize).trans_lt
    ((ENNReal.sum_lt_top).2 (fun s hs => ENNReal.ofReal_lt_top)))

theorem path_locallyBoundedVariationOn
    (D : LargeJumpPathData f c T) :
    LocallyBoundedVariationOn D.path Set.univ := by
  exact D.path_boundedVariationOn_univ.locallyBoundedVariationOn

end LargeJumpPathData

end FTAPTheorem42
