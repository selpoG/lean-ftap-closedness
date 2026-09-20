/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.EMetricSpace.BoundedVariation
import FTAPTheorem42.Foundations.FiniteVariationCanonicalMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Signed Stieltjes measures of finite-variation paths

The finite-variation part of the stochastic argument is integrated pathwise.
This file turns a real bounded-variation path into its signed Stieltjes measure
and records the interval and restriction identities needed by that integral.
-/

namespace FTAPTheorem42

open Filter Set MeasureTheory MeasurableSpace
open scoped ENNReal Topology

namespace FiniteVariationPath

variable {Time : Type*} [LinearOrder Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]
  {A : Time → ℝ} {a b : Time}

private theorem sum_le_eVariationOn_of_monotoneOn_Iic
    {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]
    {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (hus : ∀ i ≤ n, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
      eVariationOn f s := by
  let v : ℕ → α := fun i => u (min i n)
  have hv : Monotone v := by
    intro i j hij
    exact hu (min_le_right i n) (min_le_right j n)
      (min_le_min hij le_rfl)
  have hvs : ∀ i, v i ∈ s := fun i => hus _ (min_le_right i n)
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n := Finset.mem_range.1 hi
          simp [v, Nat.min_eq_left hi'.le, Nat.min_eq_left hi']
    _ ≤ eVariationOn f s := by
      rw [eVariationOn]
      exact le_iSup_of_le ⟨n, ⟨v, hv, hvs⟩⟩ le_rfl

/-- Strict-partition form of extended variation. -/
private theorem eVariationOn_eq_strictMonoOn'
    {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]
    (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : (n : ℕ) ×
          {u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s},
        ∑ i ∈ Finset.range p.1,
          edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have hcompress :
        ∃ p : (n : ℕ) ×
            {v : ℕ → α // StrictMonoOn v (Iic n) ∧ ∀ i ∈ Iic n, v i ∈ s},
          (p.2 : ℕ → α) p.1 = u n ∧
          ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) =
            ∑ i ∈ Finset.range p.1,
              edist (f ((p.2 : ℕ → α) (i + 1)))
                (f ((p.2 : ℕ → α) i)) := by
      induction n with
      | zero =>
          exact ⟨⟨0, ⟨u, by grind [StrictMonoOn], fun i _ => u_mem i⟩⟩, by simp⟩
      | succ n ih =>
          rcases ih with ⟨⟨m, v, v_mono, v_mem⟩, hv, h'v⟩
          simp only [Finset.sum_range_succ, Sigma.exists, Subtype.exists,
            mem_Iic, exists_and_left, exists_prop]
          rcases (u_mono (Nat.le_add_right n 1)).eq_or_lt with hn | hn
          · simp only [← hn, edist_self, add_zero]
            exact ⟨m, v, hv, ⟨v_mono, v_mem⟩, h'v⟩
          · refine ⟨m + 1, fun i => if i ≤ m then v i else u (n + 1), by simp,
              by grind [StrictMonoOn], ?_⟩
            simp only [h'v, ← hv, Order.add_one_le_iff,
              Finset.sum_range_succ, lt_self_iff_false, ↓reduceIte, le_refl]
            congr 1
            exact Finset.sum_congr rfl (by grind)
    rcases hcompress with ⟨p, -, hp⟩
    rw [hp]
    apply le_iSup _ p
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    exact sum_le_eVariationOn_of_monotoneOn_Iic
      (by grind [MonotoneOn, StrictMonoOn]) (by grind)

/-- For a right-continuous bounded-variation path, the signed Stieltjes mass
of `(a,b]` is the path increment `A b - A a`. -/
theorem signedMeasure_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    signedMeasure hA (Set.Ioc a b) = A b - A a := by
  rw [signedMeasure_eq_vectorMeasure hA, hA.vectorMeasure_Ioc hab,
    (hRight b).rightLim_eq, (hRight a).rightLim_eq]

/-- The signed Stieltjes atom of a right-continuous bounded-variation path
is its left jump. -/
theorem signedMeasure_singleton
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (t : Time) :
    signedMeasure hA {t} = A t - Function.leftLim A t := by
  rw [signedMeasure_eq_vectorMeasure hA, hA.vectorMeasure_singleton,
    (hRight t).rightLim_eq]

/-- The ordinary path variation on `[a,b]` is bounded by the variation mass
of the associated signed Stieltjes measure on `(a,b]`.  The proof realizes
every strictly increasing path partition as a measurable partition by
successive half-open intervals. -/
theorem eVariationOn_Icc_le_variation_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (_hab : a ≤ b) :
    eVariationOn A (Icc a b) ≤
      (signedMeasure hA).variation (Ioc a b) := by
  rw [eVariationOn_eq_strictMonoOn']
  apply iSup_le
  rintro ⟨n, u, hu, hmem⟩
  let I : ℕ → Set Time := fun i ↦ Ioc (u i) (u (i + 1))
  let P : Finset (Set Time) := (Finset.range n).image I
  have hstrict (i : ℕ) (hi : i < n) : u i < u (i + 1) := by
    exact hu (a := i) (b := i + 1) (mem_Iic.2 hi.le)
      (mem_Iic.2 (Nat.succ_le_iff.2 hi)) (by omega)
  have hIinj : Set.InjOn I (Finset.range n) := by
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.1 hi
    have hj' : j < n := Finset.mem_range.1 hj
    have he := (Ioc_eq_Ioc_iff (Or.inl (hstrict i hi'))).1 hij
    exact hu.injOn (mem_Iic.2 hi'.le) (mem_Iic.2 hj'.le) he.1
  have hsubset : ∀ s ∈ P, s ⊆ Ioc a b := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨i, hi, rfl⟩
    intro x hx
    have hi' : i < n := Finset.mem_range.1 hi
    have hui := (hmem i (mem_Iic.2 hi'.le)).1
    have hui1 := (hmem (i + 1)
      (mem_Iic.2 (Nat.succ_le_iff.2 hi'))).2
    exact ⟨hui.trans_lt hx.1, hx.2.trans hui1⟩
  have hdisj_of_lt {i j : ℕ} (hi : i < n) (hj : j < n)
      (hij : i < j) : Disjoint (I i) (I j) := by
    have hmono : u (i + 1) ≤ u j := by
      rcases (Nat.succ_le_iff.2 hij).eq_or_lt with heq | hlt
      · exact le_of_eq (congrArg u heq)
      · exact (hu (a := i + 1) (b := j)
          (mem_Iic.2 (Nat.succ_le_iff.2 hi)) (mem_Iic.2 hj.le) hlt).le
    apply Set.disjoint_left.2
    intro x hxi hxj
    exact (not_lt_of_ge (hxi.2.trans hmono)) hxj.1
  have hpair : (P : Set (Set Time)).PairwiseDisjoint id := by
    rw [Finset.coe_image]
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
    have hij : i ≠ j := by
      intro hij
      apply hne
      simp [hij]
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hdisj_of_lt (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
    · exact (hdisj_of_lt (Finset.mem_range.1 hj)
        (Finset.mem_range.1 hi) hji).symm
  have hle := VectorMeasure.le_variation (signedMeasure hA) measurableSet_Ioc
    hsubset hpair
  calc
    ∑ i ∈ Finset.range n, edist (A (u (i + 1))) (A (u i)) =
        ∑ i ∈ Finset.range n, ‖signedMeasure hA (I i)‖ₑ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [signedMeasure_Ioc hA hRight
            (hstrict i (Finset.mem_range.1 hi)).le]
          rw [edist_dist, Real.dist_eq, Real.enorm_eq_ofReal_abs]
    _ = ∑ s ∈ P, ‖signedMeasure hA s‖ₑ := by
      dsimp only [P]
      exact (Finset.sum_image
        (f := fun s : Set Time => ‖signedMeasure hA s‖ₑ) hIinj).symm
    _ ≤ (signedMeasure hA).variation (Ioc a b) := hle

/-- The extended variation of a right-continuous path on the whole time
axis is bounded by the variation of its signed Stieltjes measure. -/
theorem eVariationOn_univ_le_variation_univ
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t) :
    eVariationOn A Set.univ ≤ (signedMeasure hA).variation Set.univ := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, _huMem⟩
  have hMemIcc : ∀ i ≤ n, u i ∈ Set.Icc (u 0) (u n) := by
    intro i hi
    exact ⟨hu (Nat.zero_le i), hu hi⟩
  calc
    (∑ i ∈ Finset.range n, edist (A (u (i + 1))) (A (u i))) ≤
        eVariationOn A (Set.Icc (u 0) (u n)) :=
      sum_le_eVariationOn_of_monotoneOn_Iic (hu.monotoneOn (Set.Iic n)) hMemIcc
    _ ≤ (signedMeasure hA).variation (Set.Ioc (u 0) (u n)) :=
      eVariationOn_Icc_le_variation_Ioc hA hRight (hu (Nat.zero_le n))
    _ ≤ (signedMeasure hA).variation Set.univ :=
      measure_mono (Set.subset_univ _)

theorem signedMeasure_variation_le_eVariationOn_Icc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    (signedMeasure hA).variation (Set.Ioc a b) ≤
      eVariationOn A (Set.Icc a b) := by
  have hvar := VectorMeasure.variation_add_le
    (μ := decompositionSignedMeasure hA) (ν := botCorrection hA)
  have hpoint := (Measure.le_iff.1 hvar) (Set.Ioc a b) measurableSet_Ioc
  calc
    (signedMeasure hA).variation (Set.Ioc a b) =
        (decompositionSignedMeasure hA + botCorrection hA).variation
          (Set.Ioc a b) := rfl
    _ ≤ (decompositionSignedMeasure hA).variation (Set.Ioc a b) +
        (botCorrection hA).variation (Set.Ioc a b) := by
      rw [Measure.add_apply] at hpoint
      exact hpoint
    _ = (decompositionSignedMeasure hA).variation (Set.Ioc a b) := by
      rw [botCorrection_variation_Ioc hA a b, add_zero]
    _ ≤ eVariationOn A (Set.Icc a b) :=
      decompositionSignedMeasure_variation_le_eVariationOn_Icc hA hRight hab

theorem variationOnFromTo_eq_totalVariation_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) :
    variationOnFromTo A Set.univ a b =
      (signedMeasure hA).totalVariation.real (Ioc a b) := by
  rw [variationOnFromTo.eq_of_le A Set.univ hab, Set.univ_inter,
    signedMeasure_totalVariation_eq_variation, measureReal_def]
  have heq : eVariationOn A (Set.Icc a b) =
      (signedMeasure hA).variation (Ioc a b) :=
    le_antisymm (eVariationOn_Icc_le_variation_Ioc hA hRight hab)
      (signedMeasure_variation_le_eVariationOn_Icc hA hRight hab)
  rw [heq]

/-- The pathwise finite-variation integral against the signed Stieltjes
measure. -/
noncomputable def integral
    (hA : BoundedVariationOn A Set.univ) (H : Time → ℝ) : ℝ :=
  ∫ᵛ t, H t ∂•(signedMeasure hA)

/-- Restricting an integrand by a Borel set is the same as integrating over
that set. -/
theorem integral_indicator
    (hA : BoundedVariationOn A Set.univ)
    {H : Time → ℝ} {C : Set Time} (hC : MeasurableSet C) :
    integral hA (C.indicator H) =
      ∫ᵛ t in C, H t ∂•(signedMeasure hA) := by
  exact VectorMeasure.integral_indicator hC

/-- Integrating a constant over `(a,b]` recovers the scaled path increment. -/
theorem setIntegral_const_Ioc
    (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hab : a ≤ b) (c : ℝ) :
    (∫ᵛ _t in Set.Ioc a b, c ∂•(signedMeasure hA)) =
      c * (A b - A a) := by
  rw [VectorMeasure.integral_const]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [VectorMeasure.restrict_apply (signedMeasure hA) measurableSet_Ioc
    MeasurableSet.univ, Set.univ_inter, signedMeasure_Ioc hA hRight hab]

end FiniteVariationPath

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Measurable endpoint limits of finite-variation paths

For a bounded-variation path, a sequence tending to either end of the ordered
time space has the same limit as the corresponding `atTop` or `atBot` filter.
The sequence is useful because its `limUnder` is a countable operation, so
fixed-time measurability yields measurable endpoint data.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FiniteVariationEndpoint

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [LinearOrder Time]

variable {A : Time → Ω → ℝ}

/-! ### Countable endpoint limits -/

theorem measurable_limUnder_atTop_of_boundedVariation
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (hMeas : ∀ t, Measurable (A t))
    (u : ℕ → Time) (hu : Tendsto u atTop atTop) :
    Measurable (fun ω => limUnder atTop (fun t => A t ω)) := by
  have hseq : StronglyMeasurable
      (fun ω => limUnder atTop (fun n => A (u n) ω)) :=
    StronglyMeasurable.limUnder
      (fun n => (hMeas (u n)).stronglyMeasurable)
  have heq :
      (fun ω => limUnder atTop (fun t => A t ω)) =
        (fun ω => limUnder atTop (fun n => A (u n) ω)) := by
    funext ω
    have hlim : Tendsto (fun n => A (u n) ω) atTop
        (𝓝 (limUnder atTop (fun t => A t ω))) :=
      (hA ω).tendsto_atTop_limUnder.comp hu
    exact hlim.limUnder_eq.symm
  rw [heq]
  exact hseq.measurable

theorem measurable_limUnder_atBot_of_boundedVariation
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (hMeas : ∀ t, Measurable (A t))
    (u : ℕ → Time) (hu : Tendsto u atTop atBot) :
    Measurable (fun ω => limUnder atBot (fun t => A t ω)) := by
  have hseq : StronglyMeasurable
      (fun ω => limUnder atTop (fun n => A (u n) ω)) :=
    StronglyMeasurable.limUnder
      (fun n => (hMeas (u n)).stronglyMeasurable)
  have heq :
      (fun ω => limUnder atBot (fun t => A t ω)) =
        (fun ω => limUnder atTop (fun n => A (u n) ω)) := by
    funext ω
    have hlim : Tendsto (fun n => A (u n) ω) atTop
        (𝓝 (limUnder atBot (fun t => A t ω))) :=
      (hA ω).tendsto_atBot_limUnder.comp hu
    exact hlim.limUnder_eq.symm
  rw [heq]
  exact hseq.measurable

end FiniteVariationEndpoint

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Predictable-set restriction of pathwise finite-variation integrals

The predictable signed measure used in the finite-variation part lives on the
time--sample predictable sigma-algebra.  This section supplies the corresponding
pathwise bridge: restricting a predictable integrand to a predictable set is,
on every sample path, the same as integrating over the time section of that
set.  The result is a primitive for a general predictable integrand class; it
does not assert closedness of stochastic integrals or any semimartingale
decomposition theorem.
-/

open MeasureTheory Set
open scoped ENNReal Topology

namespace PredictableFiniteVariationRestriction

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Time] [LinearOrder Time] [OrderBot Time]
  [DenselyOrdered Time] [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [BorelSpace Time] [OpensMeasurableSpace Time] [OrderClosedTopology Time]

/-- The time section of a subset of the time--sample product. -/
def timeSection (B : Set (Time × Ω)) (ω : Ω) : Set Time :=
  {t | (t, ω) ∈ B}

end PredictableFiniteVariationRestriction

end FTAPTheorem42
