/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalAlgebra
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Inner approximation by countable intersections from an algebra

For a finite measure and an algebra generating the measurable space, every
measurable set can be approximated from inside by a countable intersection
of algebra sets.  The simultaneous outer approximation is retained in the
induction because complements exchange the two statements.
-/

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology

namespace FTAPTheorem42

namespace SetAlgebraInnerApproximation

variable {α : Type*} [m : MeasurableSpace α]

/-- Membership in the countable-intersection closure of `C`. -/
def IsCountableInter (C : Set (Set α)) (A : Set α) : Prop :=
  ∃ f : ℕ → Set α, (∀ n, f n ∈ C) ∧ A = ⋂ n, f n

/-- Membership in the countable-union closure of `C`. -/
def IsCountableUnion (C : Set (Set α)) (A : Set α) : Prop :=
  ∃ f : ℕ → Set α, (∀ n, f n ∈ C) ∧ A = ⋃ n, f n

omit m in
theorem isCountableInter_of_mem {C : Set (Set α)} {A : Set α}
    (hA : A ∈ C) : IsCountableInter C A := by
  refine ⟨fun _ => A, fun _ => hA, ?_⟩
  ext x
  simp

omit m in
theorem isCountableUnion_of_mem {C : Set (Set α)} {A : Set α}
    (hA : A ∈ C) : IsCountableUnion C A := by
  refine ⟨fun _ => A, fun _ => hA, ?_⟩
  ext x
  simp

omit m in
theorem IsCountableInter.compl
    {C : Set (Set α)} (hC : IsSetAlgebra C) {A : Set α}
    (hA : IsCountableInter C A) : IsCountableUnion C Aᶜ := by
  obtain ⟨f, hfC, rfl⟩ := hA
  refine ⟨fun n => (f n)ᶜ, fun n => hC.compl_mem (hfC n), ?_⟩
  simp

omit m in
theorem IsCountableUnion.compl
    {C : Set (Set α)} (hC : IsSetAlgebra C) {A : Set α}
    (hA : IsCountableUnion C A) : IsCountableInter C Aᶜ := by
  obtain ⟨f, hfC, rfl⟩ := hA
  refine ⟨fun n => (f n)ᶜ, fun n => hC.compl_mem (hfC n), ?_⟩
  simp

omit m in
/-- Flatten a doubly indexed countable union. -/
theorem isCountableUnion_iUnion
    {C : Set (Set α)} {A : ℕ → Set α}
    (hA : ∀ n, IsCountableUnion C (A n)) :
    IsCountableUnion C (⋃ n, A n) := by
  classical
  choose f hfC hf using hA
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun n => f (e n).1 (e n).2,
    fun n => hfC (e n).1 (e n).2, ?_⟩
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, hx⟩
    rw [hf n] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨k, hx⟩ := hx
    obtain ⟨r, hr⟩ := e.surjective (n, k)
    exact ⟨r, by simpa [hr] using hx⟩
  · rintro ⟨r, hx⟩
    refine ⟨(e r).1, ?_⟩
    rw [hf (e r).1]
    apply Set.mem_iUnion.2
    exact ⟨(e r).2, hx⟩

omit m in
theorem IsCountableInter.union
    {C : Set (Set α)} (hC : IsSetAlgebra C) {A B : Set α}
    (hA : IsCountableInter C A) (hB : IsCountableInter C B) :
    IsCountableInter C (A ∪ B) := by
  classical
  obtain ⟨f, hfC, rfl⟩ := hA
  obtain ⟨g, hgC, rfl⟩ := hB
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun n => f (e n).1 ∪ g (e n).2,
    fun n => hC.union_mem (hfC (e n).1) (hgC (e n).2), ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · rintro (hf | hg) n
    · exact Or.inl (hf (e n).1)
    · exact Or.inr (hg (e n).2)
  · intro h
    by_cases hleft : ∀ n, x ∈ f n
    · exact Or.inl hleft
    · push Not at hleft
      obtain ⟨n, hn⟩ := hleft
      right
      intro k
      obtain ⟨r, hr⟩ := e.surjective (n, k)
      have hrmem := h r
      simpa [hr, hn] using hrmem

omit m in
theorem isCountableInter_iUnion_finset
    {C : Set (Set α)} (hC : IsSetAlgebra C)
    {A : ℕ → Set α} (hA : ∀ n, IsCountableInter C (A n))
    (s : Finset ℕ) : IsCountableInter C (⋃ n ∈ s, A n) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.notMem_empty, iUnion_false, iUnion_empty]
      exact isCountableInter_of_mem hC.empty_mem
  | @insert n s hn ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA n).union hC ih

/-- Simultaneous inner and outer approximation property. -/
structure HasApproximation (μ : Measure α) (C : Set (Set α))
    (A : Set α) : Prop where
  inner : ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ B, IsCountableInter C B ∧ B ⊆ A ∧ μ (A \ B) < ε
  outer : ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ U, IsCountableUnion C U ∧ A ⊆ U ∧ μ (U \ A) < ε

theorem HasApproximation.compl
    {μ : Measure α} {C : Set (Set α)} (hC : IsSetAlgebra C)
    {A : Set α} (hA : HasApproximation μ C A) :
    HasApproximation μ C Aᶜ where
  inner := by
    intro ε hε
    obtain ⟨U, hU, hAU, hmeasure⟩ := hA.outer ε hε
    refine ⟨Uᶜ, hU.compl hC, compl_subset_compl.mpr hAU, ?_⟩
    have heq : Aᶜ \ Uᶜ = U \ A := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_compl_iff]
      tauto
    rwa [heq]
  outer := by
    intro ε hε
    obtain ⟨B, hB, hBA, hmeasure⟩ := hA.inner ε hε
    refine ⟨Bᶜ, hB.compl hC, compl_subset_compl.mpr hBA, ?_⟩
    have heq : Bᶜ \ Aᶜ = A \ B := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_compl_iff]
      tauto
    rwa [heq]

/-- Inner/outer approximation is stable under countable disjoint unions. -/
theorem hasApproximation_iUnion
    {μ : Measure α} [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetAlgebra C)
    (A : ℕ → Set α) (hdisj : Pairwise (Disjoint on A))
    (hAmeas : ∀ n, MeasurableSet (A n))
    (hA : ∀ n, HasApproximation μ C (A n)) :
    HasApproximation μ C (⋃ n, A n) where
  inner := by
    intro ε hε
    have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨δ, hδpos, hδsum⟩ :=
      ENNReal.exists_pos_sum_of_countable' hhalf.ne' ℕ
    choose B hBdelta hBA hBmeasure using fun n =>
      (hA n).inner (δ n) (hδpos n)
    have htail : Tendsto (fun n => μ (⋃ i ∈ Set.Ici n, A i))
        atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i => (hAmeas i).nullMeasurableSet) hdisj
    obtain ⟨n, hn⟩ : ∃ n, μ (⋃ i ∈ Set.Ici n, A i) < ε / 2 :=
      ((tendsto_order.1 htail).2 _ hhalf).exists
    let K : Set α := ⋃ i ∈ Finset.range n, B i
    refine ⟨K,
      isCountableInter_iUnion_finset hC hBdelta (Finset.range n), ?_, ?_⟩
    · intro x hx
      simp only [K, Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨i, hBA i hxi⟩
    · calc
        μ ((⋃ i, A i) \ K) ≤
            μ ((⋃ i ∈ Set.Ici n, A i) ∪
              ⋃ i ∈ Finset.range n, A i \ B i) := by
          apply measure_mono
          intro x hx
          simp only [Set.mem_sdiff, Set.mem_iUnion, K,
            Finset.mem_range, Set.mem_union] at hx ⊢
          obtain ⟨⟨i, hxi⟩, hxK⟩ := hx
          by_cases hi : i < n
          · exact Or.inr ⟨i, hi, hxi,
              fun hBi => hxK ⟨i, hi, hBi⟩⟩
          · exact Or.inl ⟨i, le_of_not_gt hi, hxi⟩
        _ ≤ μ (⋃ i ∈ Set.Ici n, A i) +
            μ (⋃ i ∈ Finset.range n, A i \ B i) :=
          measure_union_le _ _
        _ ≤ μ (⋃ i ∈ Set.Ici n, A i) +
            ∑ i ∈ Finset.range n, μ (A i \ B i) := by
          gcongr
          exact measure_biUnion_finset_le _ _
        _ ≤ μ (⋃ i ∈ Set.Ici n, A i) +
            ∑ i ∈ Finset.range n, δ i := by
          gcongr with i
          exact (hBmeasure i).le
        _ ≤ μ (⋃ i ∈ Set.Ici n, A i) + ∑' i, δ i := by
          gcongr
          exact ENNReal.sum_le_tsum (Finset.range n)
        _ < ε / 2 + ε / 2 := by gcongr
        _ = ε := ENNReal.add_halves ε
  outer := by
    intro ε hε
    obtain ⟨δ, hδpos, hδsum⟩ :=
      ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
    choose U hUsigma hAU hUmeasure using fun n =>
      (hA n).outer (δ n) (hδpos n)
    refine ⟨⋃ n, U n, isCountableUnion_iUnion hUsigma, ?_, ?_⟩
    · intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨n, hxn⟩ := hx
      exact ⟨n, hAU n hxn⟩
    · calc
        μ ((⋃ n, U n) \ ⋃ n, A n) ≤ μ (⋃ n, U n \ A n) := by
          apply measure_mono
          intro x hx
          simp only [Set.mem_sdiff, Set.mem_iUnion, not_exists] at hx ⊢
          obtain ⟨⟨n, hxn⟩, hxA⟩ := hx
          exact ⟨n, hxn, hxA n⟩
        _ ≤ ∑' n, μ (U n \ A n) := measure_iUnion_le _
        _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hUmeasure n).le
        _ < ε := hδsum

/-- A finite measure is inner-regular with respect to the countable-
intersection closure of any generating algebra. -/
theorem hasApproximation_of_generateFrom
    (μ : Measure α) [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetAlgebra C)
    (hgen : m = MeasurableSpace.generateFrom C)
    {A : Set α} (hA : MeasurableSet A) :
    HasApproximation μ C A := by
  apply MeasurableSpace.induction_on_inter
    (C := fun A _ => HasApproximation μ C A)
    hgen hC.isSetRing.isSetSemiring.isPiSystem
  · refine
      { inner := fun ε hε =>
          ⟨∅, isCountableInter_of_mem hC.empty_mem,
            empty_subset _, by simpa using hε⟩
        outer := fun ε hε =>
          ⟨∅, isCountableUnion_of_mem hC.empty_mem,
            empty_subset _, by simpa using hε⟩ }
  · intro B hBC
    refine
      { inner := fun ε hε =>
          ⟨B, isCountableInter_of_mem hBC, Subset.rfl,
            by simpa using hε⟩
        outer := fun ε hε =>
          ⟨B, isCountableUnion_of_mem hBC, Subset.rfl,
            by simpa using hε⟩ }
  · intro B _ hB
    exact hB.compl hC
  · intro B hdisj hBmeas hB
    exact hasApproximation_iUnion hC B hdisj hBmeas hB
  · exact hA

/-- The inner half of the approximation theorem. -/
theorem exists_countableInter_subset_measure_sdiff_lt
    (μ : Measure α) [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetAlgebra C)
    (hgen : m = MeasurableSpace.generateFrom C)
    {A : Set α} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, IsCountableInter C B ∧ B ⊆ A ∧ μ (A \ B) < ε :=
  (hasApproximation_of_generateFrom μ hC hgen hA).inner ε hε

end SetAlgebraInnerApproximation

end FTAPTheorem42
