/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Process.CadlagLargeJumpPath
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Compactness.Compact

/-!
# A stopping-time debut for large left jumps

This file gives a specialised debut construction for the first left jump
larger than a fixed threshold.  The measurable events are written as
countable unions and intersections of factorial-grid oscillation events; no
generic optional-debut theorem is used.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

namespace CadlagLargeJumpStopping

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The deterministic factorial-grid pairs -/

/-- The left endpoint of a factorial-grid pair. -/
noncomputable def gridLeft (r k : ℕ) : ℝ≥0 :=
  LeftContinuousPredictable.gridPoint r k

/-- The right endpoint of a factorial-grid pair. -/
noncomputable def gridRight (r k : ℕ) : ℝ≥0 :=
  LeftContinuousPredictable.gridPoint r (k + 1)

/-- The width of a factorial-grid pair. -/
noncomputable def gridWidth (r : ℕ) : ℝ≥0 :=
  (LeftContinuousPredictable.denominator r : ℝ≥0)⁻¹

theorem gridRight_eq (r k : ℕ) :
    gridRight r k = gridLeft r k + gridWidth r := by
  unfold gridRight gridLeft gridWidth LeftContinuousPredictable.gridPoint
  simp only [Nat.cast_add, Nat.cast_one, add_div]
  rw [one_div]

theorem gridLeft_le_right (r k : ℕ) : gridLeft r k ≤ gridRight r k := by
  rw [gridRight_eq]
  exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))

theorem gridWidth_tendsto :
    Tendsto gridWidth atTop (𝓝 0) := by
  have hdenom : Tendsto
      (fun r : ℕ => (LeftContinuousPredictable.denominator r : ℝ≥0))
      atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    have hadd : Tendsto (fun r : ℕ => r + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro n
      filter_upwards [eventually_ge_atTop n] with r hr
      exact hr.trans (Nat.le_succ r)
    change Tendsto (fun r : ℕ => (r + 1).factorial) atTop atTop
    exact factorial_tendsto_atTop.comp hadd
  change Tendsto
    (fun r : ℕ => (LeftContinuousPredictable.denominator r : ℝ≥0)⁻¹)
    atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp hdenom

theorem gridRight_tendsto (s : ℝ≥0) :
    Tendsto (fun r => gridRight r (LeftContinuousPredictable.leftIndex r s))
      atTop (𝓝 s) := by
  have hleft :
      (fun r => gridLeft r (LeftContinuousPredictable.leftIndex r s)) =
        fun r => LeftContinuousPredictable.approx r s := by
    funext r
    rfl
  have hright :
      (fun r => gridRight r (LeftContinuousPredictable.leftIndex r s)) =
        fun r => LeftContinuousPredictable.approx r s + gridWidth r := by
    funext r
    rw [gridRight_eq]
    exact congrArg (fun x => x + gridWidth r) (congrFun hleft r)
  rw [hright]
  simpa using (LeftContinuousPredictable.tendsto_approx s).add gridWidth_tendsto

theorem gridRight_ge (s : ℝ≥0) (r : ℕ) :
    s ≤ gridRight r (LeftContinuousPredictable.leftIndex r s) := by
  rw [gridRight_eq]
  change s ≤ LeftContinuousPredictable.approx r s + gridWidth r
  exact LeftContinuousPredictable.le_approx_add_inv r s

theorem gridLeft_lt {s : ℝ≥0} (hs : s ≠ 0) (r : ℕ) :
    gridLeft r (LeftContinuousPredictable.leftIndex r s) < s := by
  change LeftContinuousPredictable.approx r s < s
  exact LeftContinuousPredictable.approx_lt hs r

/-- Decreasing window widths for detecting large jumps, chosen independently of
interval-algebra approximation. -/
noncomputable def smallWidth (n : ℕ) : ℝ≥0 :=
  1 / ((n : ℝ≥0) + 1)

theorem smallWidth_pos (n : ℕ) : 0 < smallWidth n := by
  dsimp [smallWidth]
  positivity

theorem smallWidth_tendsto :
    Tendsto smallWidth atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Countable oscillation events -/

/-- Oscillation of the process across one deterministic factorial-grid pair. -/
def gridOscillationEvent
    (X : Process Ω) (d : ℝ) (t : ℝ≥0) (n r k : ℕ) : Set Ω :=
  if gridRight r k < t ∧ gridWidth r < smallWidth n then
    {ω | d < |X (gridRight r k) ω - X (gridLeft r k) ω|}
  else ∅

/-- The countable skeleton event for a left jump above `c` strictly before `t`.
The outer margin prevents a limiting oscillation from losing strictness at the
threshold. -/
def oscillationEvent
    (X : Process Ω) (c : ℝ) (t : ℝ≥0) : Set Ω :=
  ⋃ m : ℕ, ⋂ n : ℕ, ⋃ r : ℕ, ⋃ k : ℕ,
    gridOscillationEvent X (c + (smallWidth m : ℝ)) t n r k

theorem measurableSet_gridOscillationEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (d : ℝ) (t : ℝ≥0) (n r k : ℕ) :
    MeasurableSet[ℱ t] (gridOscillationEvent X d t n r k) := by
  unfold gridOscillationEvent
  split_ifs with hcond
  · have hp : gridRight r k ≤ t := hcond.1.le
    have hq : gridLeft r k ≤ t := (gridLeft_le_right r k).trans hp
    have hmeas : StronglyMeasurable[ℱ t]
        (fun ω => X (gridRight r k) ω - X (gridLeft r k) ω) :=
      (hX.stronglyMeasurable_le hp).sub
        (hX.stronglyMeasurable_le hq)
    have hpre : MeasurableSet[ℱ t]
        ((fun ω => |X (gridRight r k) ω - X (gridLeft r k) ω|) ⁻¹' Ioi d) :=
      measurableSet_Ioi.preimage hmeas.norm.measurable
    have hEq :
        ((fun ω => |X (gridRight r k) ω - X (gridLeft r k) ω|) ⁻¹' Ioi d) =
          {ω | d < |X (gridRight r k) ω - X (gridLeft r k) ω|} := by
      rfl
    rw [hEq] at hpre
    exact hpre
  · exact @MeasurableSet.empty Ω (ℱ t)

theorem measurableSet_oscillationEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (c : ℝ) (t : ℝ≥0) :
    MeasurableSet[ℱ t] (oscillationEvent X c t) := by
  unfold oscillationEvent
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_gridOscillationEvent hX _ _ _ _ _

/-! ## The local oscillation lemma -/

private theorem local_increment_bound
    {f : ℝ≥0 → ℝ} {c d : ℝ} {T : ℝ≥0}
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (hNo : ∀ s, s < T → |f s - Function.leftLim f s| ≤ c)
    (hc : 0 ≤ c) (hcd : c < d) :
    ∃ δ > 0, ∀ u v : ℝ≥0, u ≤ v → v < T →
      (v : ℝ) - u < δ → |f v - f u| < d := by
  let ε : ℝ := (d - c) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hRightInterval : ∀ {s : ℝ≥0}, ∃ d', s < d' ∧ ∀ u ∈ Ico s d',
      dist (f u) (f s) < ε := by
    intro s
    have hball : {u | f u ∈ Metric.ball (f s) ε} ∈ 𝓝[Ici s] s := by
      exact (hRight s).eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    obtain ⟨d', hsd', hd'⟩ := (nhdsGE_basis_Ico s).mem_iff.mp hball
    refine ⟨d', hsd', ?_⟩
    intro u hu
    exact Metric.mem_ball.mp (hd' hu)
  have hLeftInterval : ∀ {s : ℝ≥0}, 0 < s → ∃ d', d' < s ∧
      ∀ u ∈ Ioo d' s, dist (f u) (Function.leftLim f s) < ε := by
    intro s hs
    have hball : ∀ᶠ u in 𝓝[<] s,
        f u ∈ Metric.ball (Function.leftLim f s) ε := by
      exact (hLeft s).eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    obtain ⟨d', hsd', hd'⟩ :=
      (nhdsLT_basis_of_exists_lt ⟨0, hs⟩).mem_iff.mp hball
    refine ⟨d', hsd', ?_⟩
    intro u hu
    exact Metric.mem_ball.mp (hd' hu)
  have hlocal : ∀ s : Set.Icc (0 : ℝ≥0) T, ∃ U : Set ℝ≥0,
      IsOpen U ∧ s.1 ∈ U ∧
        ∀ u v : ℝ≥0, u ∈ U → v ∈ U → u ≤ v → (v : ℝ) < T →
          |f v - f u| < d := by
    intro s
    by_cases hsT : s.1 < T
    · by_cases hs0 : s.1 = 0
      · obtain ⟨dR, hsR, hR⟩ := hRightInterval (s := s.1)
        refine ⟨Iio dR, isOpen_Iio, ?_, ?_⟩
        · simpa [hs0] using hsR
        · intro u v hu hv huv hvT
          have huR : u ∈ Ico s.1 dR := ⟨by simp [hs0], hu⟩
          have hvR : v ∈ Ico s.1 dR := ⟨by simp [hs0], hv⟩
          have hRv : dist (f v) (f s.1) < ε := hR v hvR
          have hRu : dist (f s.1) (f u) < ε := by
            rw [dist_comm]
            exact hR u huR
          have h2ε : 2 * ε < d := by dsimp [ε]; linarith [hc, hcd]
          calc
            |f v - f u| = dist (f v) (f u) := by rw [Real.dist_eq]
            _ ≤ dist (f v) (f s.1) + dist (f s.1) (f u) :=
              dist_triangle _ _ _
            _ < d := by linarith
      · have hspos : 0 < s.1 := (pos_iff_ne_zero).2 hs0
        obtain ⟨dL, hdLs, hL⟩ := hLeftInterval hspos
        obtain ⟨dR, hsR, hR⟩ := hRightInterval (s := s.1)
        refine ⟨Ioo dL dR, isOpen_Ioo, ⟨hdLs, hsR⟩, ?_⟩
        intro u v hu hv huv hvT
        by_cases hvlt : v < s.1
        · have huL : u ∈ Ioo dL s.1 :=
            ⟨hu.1, lt_of_le_of_lt huv hvlt⟩
          have hvL : v ∈ Ioo dL s.1 := ⟨hv.1, hvlt⟩
          have hLv : dist (f v) (Function.leftLim f s.1) < ε := hL v hvL
          have hLu : dist (Function.leftLim f s.1) (f u) < ε := by
            rw [dist_comm]
            exact hL u huL
          have h2ε : 2 * ε < d := by dsimp [ε]; linarith [hc, hcd]
          calc
            |f v - f u| = dist (f v) (f u) := by rw [Real.dist_eq]
            _ ≤ dist (f v) (Function.leftLim f s.1) +
                dist (Function.leftLim f s.1) (f u) :=
              dist_triangle _ _ _
            _ < d := by linarith
        · have hsv : s.1 ≤ v := le_of_not_gt hvlt
          by_cases hus : u < s.1
          · have huL : u ∈ Ioo dL s.1 := ⟨hu.1, hus⟩
            have hvR : v ∈ Ico s.1 dR := ⟨hsv, hv.2⟩
            have hRv : dist (f v) (f s.1) < ε := hR v hvR
            have hLu : dist (Function.leftLim f s.1) (f u) < ε := by
              rw [dist_comm]
              exact hL u huL
            have hJs : dist (f s.1) (Function.leftLim f s.1) ≤ c := by
              rw [Real.dist_eq]
              exact hNo s.1 hsT
            have h3ε : 2 * ε + c < d := by dsimp [ε]; linarith [hcd]
            calc
              |f v - f u| = dist (f v) (f u) := by rw [Real.dist_eq]
              _ ≤ dist (f v) (f s.1) + dist (f s.1) (f u) :=
                dist_triangle _ _ _
              _ ≤ dist (f v) (f s.1) +
                    (dist (f s.1) (Function.leftLim f s.1) +
                      dist (Function.leftLim f s.1) (f u)) := by
                gcongr
                exact dist_triangle _ _ _
              _ < d := by
                linarith [hRv, hJs, hLu, h3ε]
          · have hsu : s.1 ≤ u := le_of_not_gt hus
            have huR : u ∈ Ico s.1 dR := ⟨hsu, hu.2⟩
            have hvR : v ∈ Ico s.1 dR := ⟨hsv, hv.2⟩
            have hRv : dist (f v) (f s.1) < ε := hR v hvR
            have hRu : dist (f s.1) (f u) < ε := by
              rw [dist_comm]
              exact hR u huR
            have h2ε : 2 * ε < d := by dsimp [ε]; linarith [hc, hcd]
            calc
              |f v - f u| = dist (f v) (f u) := by rw [Real.dist_eq]
              _ ≤ dist (f v) (f s.1) + dist (f s.1) (f u) :=
                dist_triangle _ _ _
              _ < d := by linarith
    · have hsEq : s.1 = T := le_antisymm s.property.2 (le_of_not_gt hsT)
      by_cases hT0 : T = 0
      · subst T
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
        intro u v hu hv huv hvT
        exact False.elim
          ((not_lt_of_ge (show (0 : ℝ) ≤ (v : ℝ) by positivity)) hvT)
      · have hTpos : 0 < T := (pos_iff_ne_zero).2 hT0
        obtain ⟨dL, hdLT, hL⟩ := hLeftInterval hTpos
        refine ⟨Ioi dL, isOpen_Ioi, ?_, ?_⟩
        · simpa [hsEq] using hdLT
        · intro u v hu hv huv hvT
          have huL : u ∈ Ioo dL T := ⟨hu, lt_of_le_of_lt huv hvT⟩
          have hvL : v ∈ Ioo dL T := ⟨hv, hvT⟩
          have hLv : dist (f v) (Function.leftLim f T) < ε := hL v hvL
          have hLu : dist (Function.leftLim f T) (f u) < ε := by
            rw [dist_comm]
            exact hL u huL
          have h2ε : 2 * ε < d := by dsimp [ε]; linarith [hc, hcd]
          calc
            |f v - f u| = dist (f v) (f u) := by rw [Real.dist_eq]
            _ ≤ dist (f v) (Function.leftLim f T) +
                dist (Function.leftLim f T) (f u) :=
              dist_triangle _ _ _
            _ < d := by linarith
  let K : Set ℝ≥0 := Icc 0 T
  choose U hUopen hUmem hUlocal using fun s : K => hlocal s
  have hUcover : K ⊆ ⋃ s : K, U s := by
    intro u hu
    exact Set.mem_iUnion.2 ⟨⟨u, hu⟩, hUmem ⟨u, hu⟩⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc : IsCompact K)
      hUopen hUcover
  refine ⟨δ, hδ, ?_⟩
  intro u v huv hvT hwidth
  have huK : u ∈ K := ⟨bot_le, huv.trans hvT.le⟩
  obtain ⟨s, hsball⟩ := hball u huK
  have huU : u ∈ U s := hsball (Metric.mem_ball_self hδ)
  have hvU : v ∈ U s := hsball (by
    rw [Metric.mem_ball]
    have hco : (0 : ℝ) ≤ (v : ℝ) - (u : ℝ) :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)
    rw [NNReal.dist_eq, abs_of_nonneg hco]
    exact hwidth)
  exact hUlocal s u v huU hvU huv hvT

/-! ## Identification of the skeleton event -/

private theorem largeJumpTimeSet_mem_implies_oscillation
    {f : ℝ≥0 → ℝ} (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {c : ℝ} {T t : ℝ≥0}
    {s : ℝ≥0} (hs : s ∈ largeJumpTimeSet f c T) (hst : s < t) :
    ∃ m, ∀ n, ∃ r k,
      gridRight r k < t ∧ gridWidth r < smallWidth n ∧
        c + (smallWidth m : ℝ) <
          |f (gridRight r k) - f (gridLeft r k)| := by
  have hspos : 0 < s := hs.1.1
  have hsjump : c <
      |f s - Function.leftLim f s| := hs.2
  have hqWithin : Tendsto
      (fun r => gridLeft r (LeftContinuousPredictable.leftIndex r s))
      atTop (𝓝[<] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · change Tendsto (fun r => LeftContinuousPredictable.approx r s)
        atTop (𝓝 s)
      exact LeftContinuousPredictable.tendsto_approx s
    · exact Filter.Eventually.of_forall fun r =>
        gridLeft_lt hspos.ne' r
  have hpGrid : Tendsto
      (fun r => gridRight r (LeftContinuousPredictable.leftIndex r s))
      atTop (𝓝 s) := gridRight_tendsto s
  have hpWithin : Tendsto
      (fun r => gridRight r (LeftContinuousPredictable.leftIndex r s))
      atTop (𝓝[Ici s] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hpGrid, Filter.Eventually.of_forall fun r =>
      gridRight_ge s r⟩
  have hfp : Tendsto
      (fun r => f (gridRight r (LeftContinuousPredictable.leftIndex r s)))
      atTop (𝓝 (f s)) :=
    (hRight s).tendsto.comp hpWithin
  have hfq : Tendsto
      (fun r => f (gridLeft r (LeftContinuousPredictable.leftIndex r s)))
      atTop (𝓝 (Function.leftLim f s)) :=
    (hLeft s).comp hqWithin
  have hdiff : Tendsto
      (fun r =>
        |f (gridRight r (LeftContinuousPredictable.leftIndex r s)) -
          f (gridLeft r (LeftContinuousPredictable.leftIndex r s))|)
      atTop (𝓝 |f s - Function.leftLim f s|) := by
    simpa only [Real.norm_eq_abs] using hfp.sub hfq |>.norm
  have hgap : 0 < |f s - Function.leftLim f s| - c :=
    sub_pos.mpr hsjump
  let g : ℝ≥0 := ⟨|f s - Function.leftLim f s| - c, hgap.le⟩
  have hgpos : 0 < g := hgap
  obtain ⟨m, hm⟩ :=
    (smallWidth_tendsto.eventually (Iio_mem_nhds hgpos)).exists
  have hmarg : c + (smallWidth m : ℝ) <
      |f s - Function.leftLim f s| := by
    have hm' : (smallWidth m : ℝ) < (g : ℝ) := by
      exact_mod_cast hm
    change (smallWidth m : ℝ) < |f s - Function.leftLim f s| - c at hm'
    linarith
  refine ⟨m, ?_⟩
  intro n
  have hpt : ∀ᶠ r in atTop,
      gridRight r (LeftContinuousPredictable.leftIndex r s) < t :=
    hpGrid.eventually_lt_const hst
  have hw : ∀ᶠ r in atTop, gridWidth r < smallWidth n :=
    gridWidth_tendsto.eventually (Iio_mem_nhds (smallWidth_pos n))
  have hd : ∀ᶠ r in atTop,
      c + (smallWidth m : ℝ) <
        |f (gridRight r (LeftContinuousPredictable.leftIndex r s)) -
          f (gridLeft r (LeftContinuousPredictable.leftIndex r s))| :=
    hdiff.eventually (Ioi_mem_nhds hmarg)
  obtain ⟨r, hr⟩ := (hpt.and hw).and hd |>.exists
  refine ⟨r, LeftContinuousPredictable.leftIndex r s, hr.1.1, hr.1.2, ?_⟩
  exact hr.2

private theorem oscillation_implies_largeJumpTimeSet_mem
    {f : ℝ≥0 → ℝ} (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {c : ℝ} (hc : 0 < c) {T t : ℝ≥0} (htt : t ≤ T)
    (hosc : ∃ m, ∀ n, ∃ r k,
      gridRight r k < t ∧ gridWidth r < smallWidth n ∧
        c + (smallWidth m : ℝ) <
          |f (gridRight r k) - f (gridLeft r k)|) :
    ∃ s, s ∈ largeJumpTimeSet f c T ∧ s < t := by
  rcases hosc with ⟨m, hosc⟩
  let d : ℝ := c + (smallWidth m : ℝ)
  have hcd : c < d := by
    dsimp [d]
    linarith [smallWidth_pos m]
  by_contra hno
  have hNo : ∀ s, s < t →
      |f s - Function.leftLim f s| ≤ c := by
    intro s hst
    by_cases hs0 : s = 0
    · subst s
      have hleft : Function.leftLim f 0 = f 0 :=
        leftLim_eq_of_isBot isBot_bot
      rw [hleft, sub_self, abs_zero]
      exact hc.le
    · by_contra hnot
      have hgt : c < |f s - Function.leftLim f s| := lt_of_not_ge hnot
      have hsJ : s ∈ largeJumpTimeSet f c T := by
        refine ⟨⟨(pos_iff_ne_zero).2 hs0, hst.le.trans htt⟩, hgt⟩
      exact hno ⟨s, hsJ, hst⟩
  obtain ⟨δ, hδ, hbound⟩ :=
    local_increment_bound hRight hLeft hNo hc.le hcd
  let δ₀ : ℝ≥0 := ⟨δ, hδ.le⟩
  have hδ₀ : 0 < δ₀ := hδ
  obtain ⟨n, hn⟩ :=
    (smallWidth_tendsto.eventually (Iio_mem_nhds hδ₀)).exists
  rcases hosc n with ⟨r, k, hrt, hrw, hval⟩
  have hrw' : (gridWidth r : ℝ) < (smallWidth n : ℝ) := by
    exact_mod_cast hrw
  have hmesh :
      (gridRight r k : ℝ) - (gridLeft r k : ℝ) = (gridWidth r : ℝ) := by
    rw [gridRight_eq]
    norm_num
  have hwidth : (gridRight r k : ℝ) - (gridLeft r k : ℝ) < δ := by
    rw [hmesh]
    exact hrw'.trans (by exact_mod_cast hn)
  have hbound' := hbound (gridLeft r k) (gridRight r k)
    (gridLeft_le_right r k) (by exact_mod_cast hrt) hwidth
  exact (not_lt_of_ge hbound'.le) (by simpa [d] using hval)

/-! ## Process-level event equality -/

/-- The event that the path has a retained left jump strictly before `t`. -/
def largeJumpBeforeEvent
    (X : Process Ω) (c : ℝ) (T t : ℝ≥0) : Set Ω :=
  {ω | ∃ s, s ∈ largeJumpTimeSet (fun u => X u ω) c T ∧ s < t}

omit [MeasurableSpace Ω] in
theorem largeJumpBeforeEvent_eq_oscillationEvent
    {X : Process Ω}
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (hLeft : ProcessHasLeftLimits X) {c : ℝ} (hc : 0 < c)
    {T t : ℝ≥0} (htt : t ≤ T) :
    largeJumpBeforeEvent X c T t = oscillationEvent X c t := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨s, hs, hst⟩
    obtain ⟨m, hm⟩ :=
      largeJumpTimeSet_mem_implies_oscillation
        (f := fun u => X u ω) (hRight := fun u => hRight ω u)
        (hLeft := fun u => hLeft ω u) hs hst
    change ω ∈ ⋃ m : ℕ, ⋂ n : ℕ, ⋃ r : ℕ, ⋃ k : ℕ,
      gridOscillationEvent X (c + (smallWidth m : ℝ)) t n r k
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    refine Set.mem_iInter.2 (fun n => ?_)
    obtain ⟨r, k, hrt, hrw, hval⟩ := hm n
    refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨k, ?_⟩⟩
    unfold gridOscillationEvent
    rw [ite_eq_left ⟨hrt, hrw⟩]
    exact hval
  · intro hω
    change ω ∈ ⋃ m : ℕ, ⋂ n : ℕ, ⋃ r : ℕ, ⋃ k : ℕ,
      gridOscillationEvent X (c + (smallWidth m : ℝ)) t n r k at hω
    obtain ⟨m, hω⟩ := Set.mem_iUnion.mp hω
    have hosc : ∃ m, ∀ n, ∃ r k,
        gridRight r k < t ∧ gridWidth r < smallWidth n ∧
          c + (smallWidth m : ℝ) <
            |(fun u => X u ω) (gridRight r k) -
              (fun u => X u ω) (gridLeft r k)| := by
      refine ⟨m, ?_⟩
      intro n
      obtain ⟨r, hω⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hω n)
      obtain ⟨k, hω⟩ := Set.mem_iUnion.mp hω
      unfold gridOscillationEvent at hω
      split_ifs at hω with hcond
      · exact ⟨r, k, hcond.1, hcond.2, hω⟩
      · exact False.elim hω
    obtain ⟨s, hs, hst⟩ :=
      oscillation_implies_largeJumpTimeSet_mem
        (f := fun u => X u ω) (hRight := fun u => hRight ω u)
        (hLeft := fun u => hLeft ω u) hc htt hosc
    exact ⟨s, hs, hst⟩

end CadlagLargeJumpStopping

end FTAPTheorem42
