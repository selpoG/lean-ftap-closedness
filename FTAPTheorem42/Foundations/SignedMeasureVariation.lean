/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Total variation of a signed measure

Mathlib provides both the Jordan total variation of a signed measure and the
variation of its underlying real vector measure.  This file identifies the
two constructions.
-/

open MeasureTheory Set

namespace FTAPTheorem42

/-- The Jordan total variation embedded as a nonnegative real signed
measure. -/
noncomputable def signedMeasureTotalVariation
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) : SignedMeasure X :=
  ν.toJordanDecomposition.posPart.toSignedMeasure +
    ν.toJordanDecomposition.negPart.toSignedMeasure

/-- The real signed embedding evaluates to the real mass of Jordan total
variation on every measurable set. -/
theorem signedMeasureTotalVariation_apply
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    {B : Set X} (hB : MeasurableSet B) :
    signedMeasureTotalVariation ν B = ν.totalVariation.real B := by
  rw [signedMeasureTotalVariation, add_apply]
  rw [Measure.toSignedMeasure_apply_measurable hB,
    Measure.toSignedMeasure_apply_measurable hB]
  rw [show ν.totalVariation = ν.toJordanDecomposition.posPart +
      ν.toJordanDecomposition.negPart by rfl,
    measureReal_add_apply]

/-- A measurable Hahn separator turns a signed measure into the real signed
embedding of its total variation. -/
theorem signedMeasure_hahnSplit_eq_totalVariation
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    {P : Set X} (hP : MeasurableSet P)
    (hpos : ν.toJordanDecomposition.posPart Pᶜ = 0)
    (hneg : ν.toJordanDecomposition.negPart P = 0) :
    ν.restrict P + -(ν.restrict Pᶜ) = signedMeasureTotalVariation ν := by
  let μp := ν.toJordanDecomposition.posPart
  let μn := ν.toJordanDecomposition.negPart
  have hposP : μp.restrict P = μp := by
    apply Measure.restrict_eq_self_of_ae_mem
    change P ∈ ae μp
    rw [mem_ae_iff]
    simpa [μp] using hpos
  have hnegP : μn.restrict P = 0 := by
    rw [Measure.restrict_eq_zero]
    simpa [μn] using hneg
  have hposN : μp.restrict Pᶜ = 0 := by
    rw [Measure.restrict_eq_zero]
    simpa [μp] using hpos
  have hnegN : μn.restrict Pᶜ = μn := by
    apply Measure.restrict_eq_self_of_ae_mem
    change Pᶜ ∈ ae μn
    rw [mem_ae_iff]
    simpa [μn] using hneg
  have hν : ν = μp.toSignedMeasure - μn.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm
  calc
    ν.restrict P + -(ν.restrict Pᶜ) =
        (μp.toSignedMeasure - μn.toSignedMeasure).restrict P +
          -((μp.toSignedMeasure - μn.toSignedMeasure).restrict Pᶜ) := by
      rw [← hν]
    _ = signedMeasureTotalVariation ν := by
      rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_sub]
      rw [Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hP,
        Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hP,
        Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hP.compl,
        Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hP.compl]
      simp only [hposP, hnegP, hposN, hnegN]
      simp [signedMeasureTotalVariation, μp, μn]

/-- Every signed mass is bounded above by its real total-variation mass. -/
theorem signedMeasure_apply_le_totalVariation_real
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    {B : Set X} (hB : MeasurableSet B) :
    ν B ≤ ν.totalVariation.real B := by
  have hν : ν B = ν.toJordanDecomposition.posPart.real B -
      ν.toJordanDecomposition.negPart.real B := by
    calc
      ν B = ν.toJordanDecomposition.toSignedMeasure B := by
        rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
      _ = _ := by
        rw [JordanDecomposition.toSignedMeasure,
          Measure.toSignedMeasure_sub_apply hB]
  have htv : ν.totalVariation.real B =
      ν.toJordanDecomposition.posPart.real B +
        ν.toJordanDecomposition.negPart.real B := by
    rw [SignedMeasure.totalVariation, measureReal_add_apply]
  rw [hν, htv]
  linarith [measureReal_nonneg
    (μ := ν.toJordanDecomposition.negPart) (s := B)]

/-- For a real signed measure, the Jordan total variation agrees with the
variation defined for vector measures. -/
theorem signedMeasure_totalVariation_eq_variation
    {X : Type*} [MeasurableSpace X] (s : SignedMeasure X) :
    s.totalVariation = s.variation := by
  apply le_antisymm
  · obtain ⟨i, hi, hpos, hneg, hposPart, hnegPart⟩ :=
      s.toJordanDecomposition_spec
    apply Measure.le_iff.2
    intro B hB
    by_cases hBempty : B = ∅
    · subst B
      simp
    have hBi : MeasurableSet (i ∩ B) := hi.inter hB
    have hBic : MeasurableSet (iᶜ ∩ B) := hi.compl.inter hB
    have hsBi : 0 ≤ s (i ∩ B) := by
      simpa using
        (VectorMeasure.restrict_le_restrict_iff 0 s hi).1 hpos hBi inter_subset_left
    have hsBic : s (iᶜ ∩ B) ≤ 0 := by
      simpa using
        (VectorMeasure.restrict_le_restrict_iff s 0 hi.compl).1 hneg hBic inter_subset_left
    have hdisj : Disjoint (i ∩ B) (iᶜ ∩ B) := by
      exact (disjoint_compl_right.inf_right B).inf_left B
    have hne : i ∩ B ≠ iᶜ ∩ B := by
      intro heq
      apply hBempty
      ext x
      constructor
      · intro hx
        by_cases hxi : x ∈ i
        · have hx' : x ∈ iᶜ ∩ B := heq ▸ ⟨hxi, hx⟩
          exact (hx'.1 hxi).elim
        · have hx' : x ∈ i ∩ B := heq.symm ▸ ⟨hxi, hx⟩
          exact (hxi hx'.1).elim
      · simp
    have hle := VectorMeasure.le_variation s hB
      (P := {i ∩ B, iᶜ ∩ B})
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; aesop)
      (by
        rw [Finset.coe_insert, Finset.coe_singleton]
        rw [Set.pairwiseDisjoint_insert]
        refine ⟨Set.pairwiseDisjoint_singleton _ _, ?_⟩
        intro b hb _
        simp only [Set.mem_singleton_iff] at hb
        subst b
        exact hdisj)
    rw [SignedMeasure.totalVariation, Measure.add_apply, hposPart,
      hnegPart, s.toMeasureOfZeroLE_apply hpos hi hB,
      s.toMeasureOfLEZero_apply hneg hi.compl hB]
    simpa [hne, hBi, hBic, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hsBi, abs_of_nonpos hsBic, ENNReal.ofReal_eq_coe_nnreal,
      s.toMeasureOfZeroLE_apply hpos hi hB,
      s.toMeasureOfLEZero_apply hneg hi.compl hB] using hle
  · calc
      s.variation =
          (s.toJordanDecomposition.posPart.toSignedMeasure -
            s.toJordanDecomposition.negPart.toSignedMeasure).variation := by
              rw [← JordanDecomposition.toSignedMeasure,
                SignedMeasure.toSignedMeasure_toJordanDecomposition]
      _ ≤ s.toJordanDecomposition.posPart.toSignedMeasure.variation +
          s.toJordanDecomposition.negPart.toSignedMeasure.variation :=
            VectorMeasure.variation_sub_le
      _ = s.totalVariation := by
        simp [SignedMeasure.totalVariation]

/-- The variation of a vector measure on a singleton is the extended norm
of its singleton mass. -/
theorem vectorMeasure_variation_singleton
    {X V : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]
    (ν : VectorMeasure X V) (x : X) :
    ν.variation {x} = ‖ν {x}‖ₑ := by
  exact VectorMeasure.variation_apply_singleton

/-- The Jordan total variation of a signed measure on a singleton is the
extended norm of its signed singleton mass. -/
theorem signedMeasure_totalVariation_singleton
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : SignedMeasure X) (x : X) :
    ν.totalVariation {x} = ‖ν {x}‖ₑ := by
  rw [signedMeasure_totalVariation_eq_variation]
  exact vectorMeasure_variation_singleton ν x

/-- Real-valued singleton total variation is the absolute signed mass. -/
theorem signedMeasure_totalVariation_real_singleton
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : SignedMeasure X) (x : X) :
    ν.totalVariation.real {x} = |ν {x}| := by
  rw [Measure.real, signedMeasure_totalVariation_singleton]
  rw [Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal (abs_nonneg (ν {x}))]

end FTAPTheorem42
