/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.EMetricSpace.BoundedVariation
import FTAPTheorem42.Foundations.SignedMeasureVariation

/-!
# Canonical signed Stieltjes measures of finite-variation paths

This file constructs the canonical Jordan decomposition and the associated
signed Stieltjes measure for a real bounded-variation path.
-/

open Filter Set MeasureTheory MeasurableSpace
open scoped ENNReal Topology

namespace FTAPTheorem42

namespace FiniteVariationPath

variable {Time : Type*} [LinearOrder Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]
  {A : Time → ℝ} {a b : Time}

structure Decomposition (A : Time → ℝ) (hA : BoundedVariationOn A Set.univ) where
  p : Time → ℝ
  q : Time → ℝ
  monotone_p : Monotone p
  monotone_q : Monotone q
  sub_eq : A = p - q
  variation_eq : ∀ x ∈ Set.univ, ∀ y ∈ Set.univ,
    p y - p x + (q y - q x) = variationOnFromTo A Set.univ x y

noncomputable def canonicalP
    (_hA : BoundedVariationOn A Set.univ) : Time → ℝ := by
  classical
  exact if h : Nonempty Time then
    fun x =>
      (variationOnFromTo A Set.univ (Classical.choice h) x + A x) / 2
    else A

noncomputable def canonicalQ
    (_hA : BoundedVariationOn A Set.univ) : Time → ℝ := by
  classical
  exact if h : Nonempty Time then
    fun x =>
      (variationOnFromTo A Set.univ (Classical.choice h) x - A x) / 2
    else 0

noncomputable def canonicalDecomposition
    (hA : BoundedVariationOn A Set.univ) : Decomposition A hA := by
  classical
  by_cases h : Nonempty Time
  · let c : Time := Classical.choice h
    have hc : c ∈ Set.univ := mem_univ _
    have hloc := hA.locallyBoundedVariationOn
    have hpdef : canonicalP hA =
        fun x => (variationOnFromTo A Set.univ c x + A x) / 2 := by
      simp [canonicalP, h, c]
    have hqdef : canonicalQ hA =
        fun x => (variationOnFromTo A Set.univ c x - A x) / 2 := by
      simp [canonicalQ, h, c]
    refine ⟨canonicalP hA, canonicalQ hA, ?_, ?_, ?_, ?_⟩
    · rw [hpdef]
      intro x y hxy
      dsimp
      gcongr 1
      simpa using variationOnFromTo.add_self_monotoneOn hloc hc
        (mem_univ x) (mem_univ y) hxy
    · rw [hqdef]
      intro x y hxy
      dsimp
      gcongr 1
      simpa using variationOnFromTo.sub_self_monotoneOn hloc hc
        (mem_univ x) (mem_univ y) hxy
    · funext x
      rw [hpdef, hqdef]
      dsimp
      ring
    · intro x hx y hy
      rw [hpdef, hqdef]
      dsimp
      rw [← variationOnFromTo.add hloc hc hx hy]
      ring
  · letI : IsEmpty Time := ⟨fun x => h ⟨x⟩⟩
    refine ⟨canonicalP hA, canonicalQ hA, ?_, ?_, ?_, ?_⟩
    · intro x y hxy
      exact isEmptyElim x
    · intro x y hxy
      exact isEmptyElim x
    · exact Subsingleton.elim _ _
    · intro x
      exact isEmptyElim x

omit [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time] in
theorem abs_sub_le_variation (hA : BoundedVariationOn A Set.univ)
    (x y : Time) : |A x - A y| ≤ (eVariationOn A Set.univ).toReal := by
  have hdist : edist (A x) (A y) ≤ eVariationOn A Set.univ :=
    eVariationOn.edist_le _ (mem_univ _) (mem_univ _)
  have hdist' := ENNReal.toReal_mono hA hdist
  simpa [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal] using hdist'

omit [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time] in
theorem decomposition_bounded_of (hA : BoundedVariationOn A Set.univ)
    (D : Decomposition A hA) :
    ∃ C : ℝ, ∀ x, |D.p x| ≤ C ∧ |D.q x| ≤ C := by
  rcases isEmpty_or_nonempty Time with hempty | hnonempty
  · exact ⟨0, by simp⟩
  let c : Time := Classical.choice hnonempty
  let C : ℝ := (eVariationOn A Set.univ).toReal
  have hdiff : ∀ x, |A x - A c| ≤ C := by
    intro x
    simpa [C] using abs_sub_le_variation hA x c
  have hvarabs : ∀ x, |variationOnFromTo A Set.univ c x| ≤ C := by
    intro x
    simpa [C] using
      (variationOnFromTo.abs_le_eVariationOn hA (a := c) (b := x))
  have hincp : ∀ x, |D.p x - D.p c| ≤ C := by
    intro x
    have h := D.variation_eq c (mem_univ _) x (mem_univ _)
    have hAinc : A x - A c = (D.p x - D.q x) - (D.p c - D.q c) := by
      rw [congrFun D.sub_eq x, congrFun D.sub_eq c]
      rfl
    have hformula : 2 * (D.p x - D.p c) =
        variationOnFromTo A Set.univ c x + (A x - A c) := by
      nlinarith [hAinc]
    rw [show D.p x - D.p c =
        (variationOnFromTo A Set.univ c x + (A x - A c)) / 2 by
          nlinarith [hformula], abs_div]
    have habs : |variationOnFromTo A Set.univ c x + (A x - A c)| ≤
        |variationOnFromTo A Set.univ c x| + |A x - A c| :=
      abs_add_le _ _
    have hnonneg : 0 ≤ C := by dsimp [C]; positivity
    nlinarith [hvarabs x, hdiff x]
  have hincq : ∀ x, |D.q x - D.q c| ≤ C := by
    intro x
    have h := D.variation_eq c (mem_univ _) x (mem_univ _)
    have hAinc : A x - A c = (D.p x - D.q x) - (D.p c - D.q c) := by
      rw [congrFun D.sub_eq x, congrFun D.sub_eq c]
      rfl
    have hformula : 2 * (D.q x - D.q c) =
        variationOnFromTo A Set.univ c x - (A x - A c) := by
      nlinarith [hAinc]
    rw [show D.q x - D.q c =
        (variationOnFromTo A Set.univ c x - (A x - A c)) / 2 by
          nlinarith [hformula], abs_div]
    have habs : |variationOnFromTo A Set.univ c x - (A x - A c)| ≤
        |variationOnFromTo A Set.univ c x| + |A x - A c| :=
      abs_sub _ _
    have hnonneg : 0 ≤ C := by dsimp [C]; positivity
    nlinarith [hvarabs x, hdiff x]
  refine ⟨max |D.p c| |D.q c| + C, ?_⟩
  intro x
  constructor
  · calc
      |D.p x| = |(D.p x - D.p c) + D.p c| := by congr 1; ring
      _ ≤ |D.p x - D.p c| + |D.p c| := abs_add_le _ _
      _ ≤ max |D.p c| |D.q c| + C := by
        linarith [hincp x, le_max_left |D.p c| |D.q c|]
  · calc
      |D.q x| = |(D.q x - D.q c) + D.q c| := by congr 1; ring
      _ ≤ |D.q x - D.q c| + |D.q c| := abs_add_le _ _
      _ ≤ max |D.p c| |D.q c| + C := by
        linarith [hincq x, le_max_right |D.p c| |D.q c|]

omit [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time] in
theorem rightLim_decomposition_bounded_of (hA : BoundedVariationOn A Set.univ)
    (D : Decomposition A hA) :
    ∃ C : ℝ, ∀ x, |Function.rightLim D.p x| ≤ C ∧
      |Function.rightLim D.q x| ≤ C := by
  obtain ⟨C, hC⟩ := decomposition_bounded_of hA D
  refine ⟨C, ?_⟩
  intro x
  constructor
  · have hlow : -C ≤ Function.rightLim D.p x := by
      exact (neg_le_of_abs_le (hC x).1).trans
        (D.monotone_p.le_rightLim (x := x) (y := x) le_rfl)
    have hupp : Function.rightLim D.p x ≤ C := by
      by_cases hx : ∃ y, x < y
      · obtain ⟨y, hxy⟩ := hx
        exact D.monotone_p.rightLim_le hxy |>.trans
          (le_of_abs_le (hC y).1)
      · have htop : IsTop x := by
          intro y
          exact le_of_not_gt (fun hxy => hx ⟨y, hxy⟩)
        rw [rightLim_eq_of_isTop htop]
        exact le_of_abs_le (hC x).1
    exact abs_le.2 ⟨hlow, hupp⟩
  · have hlow : -C ≤ Function.rightLim D.q x := by
      exact (neg_le_of_abs_le (hC x).2).trans
        (D.monotone_q.le_rightLim (x := x) (y := x) le_rfl)
    have hupp : Function.rightLim D.q x ≤ C := by
      by_cases hx : ∃ y, x < y
      · obtain ⟨y, hxy⟩ := hx
        exact D.monotone_q.rightLim_le hxy |>.trans
          (le_of_abs_le (hC y).2)
      · have htop : IsTop x := by
          intro y
          exact le_of_not_gt (fun hxy => hx ⟨y, hxy⟩)
        rw [rightLim_eq_of_isTop htop]
        exact le_of_abs_le (hC x).2
    exact abs_le.2 ⟨hlow, hupp⟩

omit [DenselyOrdered Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [MeasurableSpace Time] [BorelSpace Time] in
theorem rightLim_sub_eq_rightLim
    (hA : BoundedVariationOn A Set.univ) (D : Decomposition A hA) (t : Time) :
    Function.rightLim D.p t - Function.rightLim D.q t =
      Function.rightLim A t := by
  rcases eq_or_neBot (𝓝[Set.Ioi t] t) with ht | ht
  · rw [rightLim_eq_of_eq_bot D.p ht, rightLim_eq_of_eq_bot D.q ht,
      rightLim_eq_of_eq_bot A ht]
    exact (congrFun D.sub_eq t).symm
  let : NeBot (𝓝[Set.Ioi t] t) := ht
  have hlim := (D.monotone_p.tendsto_rightLim t).sub
    (D.monotone_q.tendsto_rightLim t)
  have hlim' : Tendsto A (𝓝[Set.Ioi t] t)
      (𝓝 (Function.rightLim D.p t - Function.rightLim D.q t)) := by
    apply hlim.congr'
    filter_upwards [] with s
    exact (congrFun D.sub_eq s).symm
  exact tendsto_nhds_unique hlim' (hA.tendsto_rightLim t)

noncomputable instance pMeasureFinite
    (hA : BoundedVariationOn A Set.univ) :
    IsFiniteMeasure ((canonicalDecomposition hA).monotone_p.stieltjesFunction.measure) := by
  obtain ⟨C, hC⟩ := rightLim_decomposition_bounded_of hA (canonicalDecomposition hA)
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
  exact fun x => by simpa only [Monotone.stieltjesFunction_eq] using (hC x).1

noncomputable instance qMeasureFinite
    (hA : BoundedVariationOn A Set.univ) :
    IsFiniteMeasure ((canonicalDecomposition hA).monotone_q.stieltjesFunction.measure) := by
  obtain ⟨C, hC⟩ := rightLim_decomposition_bounded_of hA (canonicalDecomposition hA)
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
  exact fun x => by simpa only [Monotone.stieltjesFunction_eq] using (hC x).2

noncomputable def decompositionSignedMeasure
    (hA : BoundedVariationOn A Set.univ) : SignedMeasure Time :=
  (canonicalDecomposition hA).monotone_p.stieltjesFunction.measure.toSignedMeasure -
    (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure.toSignedMeasure

noncomputable instance decompositionSignedMeasureVariationFinite
    (hA : BoundedVariationOn A Set.univ) :
    IsFiniteMeasure (decompositionSignedMeasure hA).variation := by
  apply IsFiniteMeasure.mk
  have hle : (decompositionSignedMeasure hA).variation ≤
      (canonicalDecomposition hA).monotone_p.stieltjesFunction.measure +
        (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure := by
    rw [decompositionSignedMeasure]
    simpa only [Measure.variation_toSignedMeasure, add_comm] using
      (VectorMeasure.variation_sub_le
        (μ := (canonicalDecomposition hA).monotone_p.stieltjesFunction.measure.toSignedMeasure)
        (ν := (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure.toSignedMeasure))
  have huniv := (Measure.le_iff.1 hle) Set.univ MeasurableSet.univ
  exact huniv.trans_lt (by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩)

omit [DenselyOrdered Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [MeasurableSpace Time] [BorelSpace Time] in
theorem canonical_rightLim_eq
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t) (t : Time) :
    Function.rightLim (canonicalDecomposition hA).p t =
      (canonicalDecomposition hA).p t := by
  classical
  by_cases h : Nonempty Time
  · let c : Time := Classical.choice h
    have hc : c ∈ Set.univ := mem_univ _
    have hpdef : canonicalP hA =
        fun x => (variationOnFromTo A Set.univ c x + A x) / 2 := by
      simp [canonicalP, h, c]
    have hcont := hA.continuousWithinAt_variationOnFromTo_Ici
      (a := c) (hRight t)
    have hcont' : ContinuousWithinAt
        (fun x => (variationOnFromTo A Set.univ c x + A x) / 2)
        (Set.Ici t) t := by
      exact (hcont.add (hRight t)).div_const 2
    have hDp : (canonicalDecomposition hA).p = canonicalP hA := by
      simp [canonicalDecomposition, h]
    rw [hDp]
    rw [hpdef]
    exact hcont'.rightLim_eq
  · let : IsEmpty Time := ⟨fun x => h ⟨x⟩⟩
    exact rightLim_eq_of_eq_bot _ (filter_eq_bot_of_isEmpty _)

omit [DenselyOrdered Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [MeasurableSpace Time] [BorelSpace Time] in
theorem canonical_rightLim_eq_q
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t) (t : Time) :
    Function.rightLim (canonicalDecomposition hA).q t =
      (canonicalDecomposition hA).q t := by
  classical
  by_cases h : Nonempty Time
  · let c : Time := Classical.choice h
    have hpdef : canonicalQ hA =
        fun x => (variationOnFromTo A Set.univ c x - A x) / 2 := by
      simp [canonicalQ, h, c]
    have hcont := hA.continuousWithinAt_variationOnFromTo_Ici
      (a := c) (hRight t)
    have hcont' : ContinuousWithinAt
        (fun x => (variationOnFromTo A Set.univ c x - A x) / 2)
        (Set.Ici t) t := by
      exact (hcont.sub (hRight t)).div_const 2
    have hDq : (canonicalDecomposition hA).q = canonicalQ hA := by
      simp [canonicalDecomposition, h]
    rw [hDq, hpdef]
    exact hcont'.rightLim_eq
  · let : IsEmpty Time := ⟨fun x => h ⟨x⟩⟩
    exact rightLim_eq_of_eq_bot _ (filter_eq_bot_of_isEmpty _)

theorem decompositionSignedMeasure_Ioc
    (hA : BoundedVariationOn A Set.univ) (hab : a ≤ b) :
    decompositionSignedMeasure hA (Set.Ioc a b) =
      Function.rightLim A b - Function.rightLim A a := by
  rw [decompositionSignedMeasure, Measure.toSignedMeasure_sub_apply measurableSet_Ioc,
    measureReal_def, measureReal_def, StieltjesFunction.measure_Ioc,
    StieltjesFunction.measure_Ioc]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · have hp := (canonicalDecomposition hA).monotone_p.stieltjesFunction.mono hab
    have hq := (canonicalDecomposition hA).monotone_q.stieltjesFunction.mono hab
    change (Function.rightLim (canonicalDecomposition hA).p b -
          Function.rightLim (canonicalDecomposition hA).p a) -
        (Function.rightLim (canonicalDecomposition hA).q b -
          Function.rightLim (canonicalDecomposition hA).q a) =
      Function.rightLim A b - Function.rightLim A a
    linarith [rightLim_sub_eq_rightLim hA (canonicalDecomposition hA) b,
      rightLim_sub_eq_rightLim hA (canonicalDecomposition hA) a]
  · exact sub_nonneg.mpr ((canonicalDecomposition hA).monotone_q.stieltjesFunction.mono hab)
  · exact sub_nonneg.mpr ((canonicalDecomposition hA).monotone_p.stieltjesFunction.mono hab)

theorem decompositionMeasure_add_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    ((canonicalDecomposition hA).monotone_p.stieltjesFunction.measure +
        (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure) (Set.Ioc a b) =
      ENNReal.ofReal (variationOnFromTo A Set.univ a b) := by
  rw [Measure.add_apply, StieltjesFunction.measure_Ioc,
    StieltjesFunction.measure_Ioc]
  simp only [Monotone.stieltjesFunction_eq]
  rw [canonical_rightLim_eq hA hRight b, canonical_rightLim_eq hA hRight a,
    canonical_rightLim_eq_q hA hRight b, canonical_rightLim_eq_q hA hRight a]
  rw [← ENNReal.ofReal_add]
  · rw [(canonicalDecomposition hA).variation_eq a (mem_univ _) b (mem_univ _)]
  · exact sub_nonneg.mpr ((canonicalDecomposition hA).monotone_p hab)
  · exact sub_nonneg.mpr ((canonicalDecomposition hA).monotone_q hab)

theorem decompositionSignedMeasure_variation_le_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    (decompositionSignedMeasure hA).variation (Set.Ioc a b) ≤
      ENNReal.ofReal (variationOnFromTo A Set.univ a b) := by
  have hle : (decompositionSignedMeasure hA).variation ≤
      (canonicalDecomposition hA).monotone_p.stieltjesFunction.measure +
        (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure := by
    rw [decompositionSignedMeasure]
    simpa only [Measure.variation_toSignedMeasure, add_comm] using
      (VectorMeasure.variation_sub_le
        (μ := (canonicalDecomposition hA).monotone_p.stieltjesFunction.measure.toSignedMeasure)
        (ν := (canonicalDecomposition hA).monotone_q.stieltjesFunction.measure.toSignedMeasure))
  have hleIoc := (Measure.le_iff.1 hle) (Set.Ioc a b) measurableSet_Ioc
  rw [decompositionMeasure_add_Ioc hA hRight hab] at hleIoc
  exact hleIoc

theorem decompositionSignedMeasure_variation_le_eVariationOn_Icc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    (decompositionSignedMeasure hA).variation (Set.Ioc a b) ≤
      eVariationOn A (Set.Icc a b) := by
  have hfin : eVariationOn A (Set.Icc a b) ≠ ∞ := by
    exact ((eVariationOn.mono A (subset_univ _)).trans_lt hA.lt_top).ne
  have hrewrite :
      ENNReal.ofReal (variationOnFromTo A Set.univ a b) =
        eVariationOn A (Set.Icc a b) := by
    rw [variationOnFromTo.eq_of_le A Set.univ hab, Set.univ_inter,
      ENNReal.ofReal_toReal hfin]
  rw [← hrewrite]
  exact decompositionSignedMeasure_variation_le_Ioc hA hRight hab
theorem decompositionSignedMeasure_univ_base_nonempty
    (hA : BoundedVariationOn A Set.univ) (hTime : Nonempty Time) :
    decompositionSignedMeasure hA Set.univ =
      limUnder atTop (fun t => A t) -
        limUnder atBot (fun t => Function.rightLim A t) := by
  classical
  let : Nonempty Time := hTime
  let D : Decomposition A hA := canonicalDecomposition hA
  let P : StieltjesFunction Time := D.monotone_p.stieltjesFunction
  let Q : StieltjesFunction Time := D.monotone_q.stieltjesFunction
  let hpfin : IsFiniteMeasure P.measure := by
    dsimp [P, D]
    infer_instance
  let hqfin : IsFiniteMeasure Q.measure := by
    dsimp [Q, D]
    infer_instance
  obtain ⟨C, hC⟩ := rightLim_decomposition_bounded_of hA D
  have hDP : ∀ t, |P t| ≤ C := by
    intro t
    simpa [P, Monotone.stieltjesFunction_eq] using (hC t).1
  have hDQ : ∀ t, |Q t| ≤ C := by
    intro t
    simpa [Q, Monotone.stieltjesFunction_eq] using (hC t).2
  have hPBV : BoundedVariationOn (fun t => P t) Set.univ :=
    (monotoneOn_univ.2 P.mono).boundedVariationOn (C := C) (fun t _ => hDP t)
  have hQBV : BoundedVariationOn (fun t => Q t) Set.univ :=
    (monotoneOn_univ.2 Q.mono).boundedVariationOn (C := C) (fun t _ => hDQ t)
  have hPtop := hPBV.tendsto_atTop_limUnder
  have hQtop := hQBV.tendsto_atTop_limUnder
  have hPbot := hPBV.tendsto_atBot_limUnder
  have hQbot := hQBV.tendsto_atBot_limUnder
  have hrel : ∀ t, P t - Q t = Function.rightLim A t := by
    intro t
    change Function.rightLim D.p t - Function.rightLim D.q t =
      Function.rightLim A t
    exact rightLim_sub_eq_rightLim hA D t
  have htopRel :
      limUnder atTop (fun t => P t) - limUnder atTop (fun t => Q t) =
        limUnder atTop (fun t => A t) := by
    cases topOrderOrNoTopOrder Time
    · have hPtop' : limUnder atTop (fun t => P t) = P ⊤ := by
        rw [atTop_eq_pure_of_isTop isTop_top]
        exact (tendsto_pure_nhds P ⊤).limUnder_eq
      have hQtop' : limUnder atTop (fun t => Q t) = Q ⊤ := by
        rw [atTop_eq_pure_of_isTop isTop_top]
        exact (tendsto_pure_nhds Q ⊤).limUnder_eq
      have hAtop' : limUnder atTop (fun t => A t) = A ⊤ := by
        rw [atTop_eq_pure_of_isTop isTop_top]
        exact (tendsto_pure_nhds A ⊤).limUnder_eq
      rw [hPtop', hQtop', hAtop']
      simpa [rightLim_eq_of_isTop] using hrel ⊤
    · by_cases hne : Nonempty Time
      · let : Nonempty Time := hne
        have hright := tendsto_rightLim_atTop_of_tendsto hA.tendsto_atTop_limUnder
        have hright' : Tendsto (fun t => P t - Q t) atTop
            (𝓝 (limUnder atTop (fun t => A t))) := by
          apply hright.congr'
          filter_upwards [] with t
          exact (hrel t).symm
        exact tendsto_nhds_unique (hPtop.sub hQtop) hright'
      · let : IsEmpty Time := ⟨fun t => hne ⟨t⟩⟩
        exact (hne hTime).elim
  have hbotRel :
      limUnder atBot (fun t => P t) - limUnder atBot (fun t => Q t) =
        limUnder atBot (fun t => Function.rightLim A t) := by
    cases botOrderOrNoBotOrder Time
    · have hPbot' : limUnder atBot (fun t => P t) = P ⊥ := by
        rw [atBot_eq_pure_of_isBot isBot_bot]
        exact (tendsto_pure_nhds P ⊥).limUnder_eq
      have hQbot' : limUnder atBot (fun t => Q t) = Q ⊥ := by
        rw [atBot_eq_pure_of_isBot isBot_bot]
        exact (tendsto_pure_nhds Q ⊥).limUnder_eq
      have hRbot :
          limUnder atBot (fun t => Function.rightLim A t) =
            Function.rightLim A ⊥ := by
        rw [atBot_eq_pure_of_isBot isBot_bot]
        exact (tendsto_pure_nhds (fun t => Function.rightLim A t) ⊥).limUnder_eq
      rw [hPbot', hQbot', hRbot]
      exact hrel ⊥
    · by_cases hne : Nonempty Time
      · let : Nonempty Time := hne
        have hA' := tendsto_rightLim_atBot_of_tendsto hA.tendsto_atBot_limUnder
        have hright' : Tendsto (fun t => P t - Q t) atBot
            (𝓝 (limUnder atBot (fun t => A t))) := by
          apply hA'.congr'
          filter_upwards [] with t
          exact (hrel t).symm
        have hlim := tendsto_nhds_unique (hPbot.sub hQbot) hright'
        rw [hA'.limUnder_eq]
        exact hlim
      · let : IsEmpty Time := ⟨fun t => hne ⟨t⟩⟩
        exact (hne hTime).elim
  have hPmeasure : P.measure Set.univ =
      ENNReal.ofReal (limUnder atTop (fun t => P t) -
        limUnder atBot (fun t => P t)) :=
    P.measure_univ hPbot hPtop
  have hQmeasure : Q.measure Set.univ =
      ENNReal.ofReal (limUnder atTop (fun t => Q t) -
        limUnder atBot (fun t => Q t)) :=
    Q.measure_univ hQbot hQtop
  have hbase : decompositionSignedMeasure hA Set.univ =
      P.measure.real Set.univ - Q.measure.real Set.univ := by
    dsimp [decompositionSignedMeasure, P, Q, D]
    rw [Measure.toSignedMeasure_sub_apply MeasurableSet.univ]
  have hPnonneg :
      0 ≤ limUnder atTop (fun t => P t) - limUnder atBot (fun t => P t) := by
    obtain ⟨x⟩ := hTime
    have htop : P x ≤ limUnder atTop (fun t => P t) := by
      cases topOrderOrNoTopOrder Time
      · have hPtop' : limUnder atTop (fun t => P t) = P ⊤ := by
          rw [atTop_eq_pure_of_isTop isTop_top]
          exact (tendsto_pure_nhds P ⊤).limUnder_eq
        rw [hPtop']
        exact P.mono le_top
      · exact P.mono.ge_of_tendsto hPtop x
    have hbot : limUnder atBot (fun t => P t) ≤ P x := by
      cases botOrderOrNoBotOrder Time
      · have hPbot' : limUnder atBot (fun t => P t) = P ⊥ := by
          rw [atBot_eq_pure_of_isBot isBot_bot]
          exact (tendsto_pure_nhds P ⊥).limUnder_eq
        rw [hPbot']
        exact P.mono bot_le
      · exact P.mono.le_of_tendsto hPbot x
    linarith
  have hQnonneg :
      0 ≤ limUnder atTop (fun t => Q t) - limUnder atBot (fun t => Q t) := by
    obtain ⟨x⟩ := hTime
    have htop : Q x ≤ limUnder atTop (fun t => Q t) := by
      cases topOrderOrNoTopOrder Time
      · have hQtop' : limUnder atTop (fun t => Q t) = Q ⊤ := by
          rw [atTop_eq_pure_of_isTop isTop_top]
          exact (tendsto_pure_nhds Q ⊤).limUnder_eq
        rw [hQtop']
        exact Q.mono le_top
      · exact Q.mono.ge_of_tendsto hQtop x
    have hbot : limUnder atBot (fun t => Q t) ≤ Q x := by
      cases botOrderOrNoBotOrder Time
      · have hQbot' : limUnder atBot (fun t => Q t) = Q ⊥ := by
          rw [atBot_eq_pure_of_isBot isBot_bot]
          exact (tendsto_pure_nhds Q ⊥).limUnder_eq
        rw [hQbot']
        exact Q.mono bot_le
      · exact Q.mono.le_of_tendsto hQbot x
    linarith
  rw [hbase, measureReal_def, measureReal_def, hPmeasure, hQmeasure,
    ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · dsimp [P, Q] at htopRel hbotRel ⊢
    linarith
  · exact hQnonneg
  · exact hPnonneg

theorem decompositionSignedMeasure_univ_base
    (hA : BoundedVariationOn A Set.univ) :
    decompositionSignedMeasure hA Set.univ =
      limUnder atTop (fun t => A t) -
        limUnder atBot (fun t => Function.rightLim A t) := by
  classical
  rcases isEmpty_or_nonempty Time with hempty | hnonempty
  · let : IsEmpty Time := hempty
    simp [decompositionSignedMeasure, eq_empty_of_isEmpty,
      filter_eq_bot_of_isEmpty, Filter.limUnder, Filter.map_bot]
  · exact decompositionSignedMeasure_univ_base_nonempty hA hnonempty

noncomputable def botCorrection
    (_hA : BoundedVariationOn A Set.univ) : SignedMeasure Time := by
  classical
  exact if h : ∃ x, IsBot x then
    VectorMeasure.dirac h.choose
      (Function.rightLim A h.choose - A h.choose)
  else 0

omit [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [BorelSpace Time] in
theorem botCorrection_Ioc
    (_hA : BoundedVariationOn A Set.univ) (a b : Time) :
    botCorrection _hA (Set.Ioc a b) = 0 := by
  classical
  by_cases h : ∃ x : Time, IsBot x
  · rw [botCorrection, dite_eq_left h]
    rw [VectorMeasure.dirac_apply_of_notMem]
    simp only [mem_Ioc, not_and_or, not_lt, not_le]
    exact Or.inl (h.choose_spec _)
  · rw [botCorrection, dite_eq_right h]
    rfl

/-- The signed Stieltjes measure induced by a real bounded-variation path. -/
noncomputable def signedMeasure
    (hA : BoundedVariationOn A Set.univ) : SignedMeasure Time :=
  decompositionSignedMeasure hA + botCorrection hA

/-- The variation measure of the signed Stieltjes measure is finite. -/
noncomputable instance signedMeasureVariationFinite
    (hA : BoundedVariationOn A Set.univ) :
    IsFiniteMeasure (signedMeasure hA).variation := by
  classical
  have hcorrection : IsFiniteMeasure (botCorrection hA).variation := by
    by_cases h : ∃ x : Time, IsBot x
    · rw [botCorrection, dite_eq_left h]
      infer_instance
    · rw [botCorrection, dite_eq_right h]
      rw [VectorMeasure.variation_zero]
      infer_instance
  let := hcorrection
  exact isFiniteMeasure_of_le _ VectorMeasure.variation_add_le

/-- On an open-closed interval, the signed Stieltjes measure records the
increment between right limits. -/
theorem signedMeasure_Ioc_rightLim
    (hA : BoundedVariationOn A Set.univ) (hab : a ≤ b) :
    signedMeasure hA (Set.Ioc a b) = A.rightLim b - A.rightLim a := by
  rw [signedMeasure, add_apply,
    decompositionSignedMeasure_Ioc hA hab, botCorrection_Ioc hA a b, add_zero]

theorem signedMeasure_univ
    (hA : BoundedVariationOn A Set.univ) :
    signedMeasure hA Set.univ =
      limUnder atTop (fun t => A t) - limUnder atBot (fun t => A t) := by
  classical
  rcases isEmpty_or_nonempty Time with hempty | hnonempty
  · let : IsEmpty Time := hempty
    have hfun : (fun t => Function.rightLim A t) = (fun t => A t) :=
      Subsingleton.elim _ _
    have hno : ¬ ∃ x : Time, IsBot x := by
      intro h
      exact isEmptyElim h.choose
    rw [signedMeasure, add_apply, botCorrection, dite_eq_right hno,
      decompositionSignedMeasure_univ_base]
    rw [hfun]
    simp [Filter.limUnder]
  · let : Nonempty Time := hnonempty
    rw [signedMeasure, add_apply,
      decompositionSignedMeasure_univ_base hA]
    cases botOrderOrNoBotOrder Time
    · have hcorr : botCorrection hA Set.univ =
          Function.rightLim A ⊥ - A ⊥ := by
        have hbot : ∃ x : Time, IsBot x := ⟨⊥, isBot_bot⟩
        rw [botCorrection, dite_eq_left hbot,
          VectorMeasure.dirac_apply_of_mem MeasurableSet.univ (mem_univ _)]
        have heq : hbot.choose = (⊥ : Time) :=
          subsingleton_isBot _ hbot.choose_spec isBot_bot
        rw [heq]
      rw [hcorr]
      · have hR : limUnder atBot (fun t => Function.rightLim A t) =
            Function.rightLim A ⊥ := by
          rw [atBot_eq_pure_of_isBot isBot_bot]
          exact (tendsto_pure_nhds (fun t => Function.rightLim A t) ⊥).limUnder_eq
        have hA' : limUnder atBot (fun t => A t) = A ⊥ := by
          rw [atBot_eq_pure_of_isBot isBot_bot]
          exact (tendsto_pure_nhds A ⊥).limUnder_eq
        rw [hR, hA']
        ring
    · have hcorr : botCorrection hA Set.univ = 0 := by
        by_cases h : ∃ x : Time, IsBot x
        · exact (not_isBot h.choose) h.choose_spec |>.elim
        · rw [botCorrection, dite_eq_right h]
          rfl
      rw [hcorr]
      have hA' := tendsto_rightLim_atBot_of_tendsto hA.tendsto_atBot_limUnder
      rw [hA'.limUnder_eq]
      simp

omit [DenselyOrdered Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] in
theorem botCorrection_variation_Ioc
    (hA : BoundedVariationOn A Set.univ) (a b : Time) :
    (botCorrection hA).variation (Set.Ioc a b) = 0 := by
  classical
  apply (VectorMeasure.variation_apply_eq_zero measurableSet_Ioc).2
  intro t hts ht
  by_cases h : ∃ x : Time, IsBot x
  · rw [botCorrection, dite_eq_left h]
    apply VectorMeasure.dirac_apply_of_notMem
    intro hmem
    exact (not_lt_of_ge (h.choose_spec a)) (hts hmem).1
  · rw [botCorrection, dite_eq_right h]
    rfl

omit [DenselyOrdered Time] [CompactIccSpace Time] in
/-- Two finite signed measures on an ordered Borel time space are equal when
they agree on all `(a,b]` intervals and on the whole time space. -/
theorem signedMeasure_ext_of_Ioc_univ
    {ν₁ ν₂ : SignedMeasure Time}
    (hIoc : ∀ {a b : Time}, a ≤ b →
      ν₁ (Set.Ioc a b) = ν₂ (Set.Ioc a b))
    (hUniv : ν₁ Set.univ = ν₂ Set.univ) :
    ν₁ = ν₂ := by
  let s : SignedMeasure Time := ν₁ - ν₂
  have hsIoc : ∀ {a b : Time}, a ≤ b → s (Set.Ioc a b) = 0 := by
    intro a b hab
    dsimp [s]
    rw [sub_apply, hIoc hab, sub_self]
  have hsUniv : s Set.univ = 0 := by
    dsimp [s]
    rw [sub_apply, hUniv, sub_self]
  have hszero : s = 0 := by
    let j : JordanDecomposition Time := s.toJordanDecomposition
    let ρ : Measure Time := j.posPart + j.negPart
    let μplus : Measure Time := j.posPart + j.posPart
    let μminus : Measure Time := j.negPart + j.negPart
    have hsJordan : j.toSignedMeasure = s := by
      dsimp [j]
      simp
    have hplus : μplus.toSignedMeasure = ρ.toSignedMeasure + s := by
      change (j.posPart + j.posPart).toSignedMeasure =
        (j.posPart + j.negPart).toSignedMeasure + s
      rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add, ← hsJordan]
      change (j.posPart.toSignedMeasure + j.posPart.toSignedMeasure) =
        (j.posPart.toSignedMeasure + j.negPart.toSignedMeasure) +
          (j.posPart.toSignedMeasure - j.negPart.toSignedMeasure)
      abel
    have hminus : μminus.toSignedMeasure = ρ.toSignedMeasure - s := by
      change (j.negPart + j.negPart).toSignedMeasure =
        (j.posPart + j.negPart).toSignedMeasure - s
      rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add, ← hsJordan]
      change (j.negPart.toSignedMeasure + j.negPart.toSignedMeasure) =
        (j.posPart.toSignedMeasure + j.negPart.toSignedMeasure) -
          (j.posPart.toSignedMeasure - j.negPart.toSignedMeasure)
      abel
    have hplusIoc : ∀ {a b : Time}, a < b →
        μplus (Set.Ioc a b) = μminus (Set.Ioc a b) := by
      intro a b hab
      apply (measureReal_eq_measureReal_iff
        (measure_ne_top _ _) (measure_ne_top _ _)).1
      have hp := congrArg (fun z : SignedMeasure Time => z (Set.Ioc a b)) hplus
      have hm := congrArg (fun z : SignedMeasure Time => z (Set.Ioc a b)) hminus
      rw [Measure.toSignedMeasure_apply_measurable measurableSet_Ioc] at hp hm
      rw [add_apply] at hp
      rw [sub_apply] at hm
      rw [hsIoc hab.le] at hp hm
      linarith
    have hplusUniv : μplus Set.univ = μminus Set.univ := by
      apply (measureReal_eq_measureReal_iff
        (measure_ne_top _ _) (measure_ne_top _ _)).1
      have hp := congrArg (fun z : SignedMeasure Time => z Set.univ) hplus
      have hm := congrArg (fun z : SignedMeasure Time => z Set.univ) hminus
      rw [Measure.toSignedMeasure_apply_measurable MeasurableSet.univ] at hp hm
      rw [add_apply] at hp
      rw [sub_apply] at hm
      rw [hsUniv] at hp hm
      linarith
    have hmeasure : μplus = μminus := by
      apply Measure.ext_of_Ioc_finite
      · exact hplusUniv
      · intro a b hab
        exact hplusIoc hab
    have hmeasureSigned : μplus.toSignedMeasure = μminus.toSignedMeasure := by
      ext E hE
      rw [Measure.toSignedMeasure_apply_measurable hE,
        Measure.toSignedMeasure_apply_measurable hE, hmeasure]
    have hshift : ρ.toSignedMeasure + s = ρ.toSignedMeasure - s := by
      rw [← hplus, ← hminus, hmeasureSigned]
    have : s = 0 := by
      have h := congrArg (fun z : SignedMeasure Time => z - ρ.toSignedMeasure) hshift
      ext E hE
      have h' := congrArg (fun z : SignedMeasure Time => z E) h
      change ρ.toSignedMeasure E + s E - ρ.toSignedMeasure E =
        ρ.toSignedMeasure E - s E - ρ.toSignedMeasure E at h'
      change s E = 0
      linarith
    exact this
  exact sub_eq_zero.mp hszero

/-- The canonical construction agrees with mathlib's vector-measure
Stieltjes construction. -/
theorem signedMeasure_eq_vectorMeasure
    (hA : BoundedVariationOn A Set.univ) :
    signedMeasure hA = hA.vectorMeasure := by
  apply signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [signedMeasure_Ioc_rightLim hA hab, hA.vectorMeasure_Ioc hab]
  · rw [signedMeasure_univ hA, hA.vectorMeasure_univ]

end FiniteVariationPath

end FTAPTheorem42
