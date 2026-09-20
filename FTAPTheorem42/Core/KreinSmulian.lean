/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The bounded-slice criterion on a weak dual

This module develops the functional-analytic lemmas used in the proof of the
Krein--Šmulian theorem for a real Banach dual.  The final theorem is built from
bounded weak-star slices; no sequential compactness assumption on the predual
is used.
-/

open Filter Topology
open scoped Pointwise

namespace FTAPTheorem42

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The part of a weak-dual set lying in the closed operator-norm ball of
radius `r` centered at zero. -/
def weakDualNormSlice (C : Set (WeakDual ℝ E)) (r : ℝ) :
    Set (WeakDual ℝ E) :=
  C ∩ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r

/-- If every nonnegative norm slice of a weak-dual set is weak-star closed,
then the corresponding subset of the strong dual is norm closed. -/
theorem isClosed_strongDual_preimage_of_isClosed_weakDualNormSlice
    {C : Set (WeakDual ℝ E)}
    (hclosed : ∀ r : ℝ, 0 ≤ r → IsClosed (weakDualNormSlice C r)) :
    IsClosed (StrongDual.toWeakDual ⁻¹' C) := by
  rw [← isSeqClosed_iff_isClosed]
  intro φ φlim hφC hφlim
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : StrongDual ℝ E)).mp
      (Metric.isBounded_range_of_tendsto φ hφlim)
  let R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hφR : ∀ n, φ n ∈ Metric.closedBall (0 : StrongDual ℝ E) R' := by
    intro n
    exact Metric.closedBall_subset_closedBall (le_max_left _ _)
      (hR (Set.mem_range_self n))
  have hweak :
      Tendsto (fun n => StrongDual.toWeakDual (φ n)) atTop
        (𝓝 (StrongDual.toWeakDual φlim)) :=
    NormedSpace.Dual.toWeakDual_continuous.tendsto φlim |>.comp hφlim
  have hmem :
      ∀ n, StrongDual.toWeakDual (φ n) ∈ weakDualNormSlice C R' := by
    intro n
    exact ⟨hφC n, hφR n⟩
  exact ((hclosed R' hR').mem_of_tendsto hweak
    (Eventually.of_forall hmem)).1

/-- The polar of the closed ball of radius `r⁻¹` in the predual is the
closed operator-norm ball of radius `r` in the weak dual. -/
theorem weakDual_polar_closedBall_inv
    (r : ℝ) (hr : 0 < r) :
    WeakDual.polar ℝ (Metric.closedBall (0 : E) r⁻¹) =
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ E) r := by
  ext φ
  rw [WeakDual.polar_def]
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff]
  constructor
  · intro hφ
    apply (WeakDual.toStrongDual φ).opNorm_le_bound hr.le
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let c : ℝ := r⁻¹ * ‖x‖⁻¹
    have hc : 0 < c := mul_pos (inv_pos.mpr hr) (inv_pos.mpr hxnorm)
    have hy : ‖c • x‖ ≤ r⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      dsimp [c]
      field_simp
      exact le_rfl
    have heval : c * ‖φ x‖ ≤ 1 := by
      simpa [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] using
        hφ (c • x) hy
    calc
      ‖(WeakDual.toStrongDual φ) x‖ =
          (r * ‖x‖) * (c * ‖φ x‖) := by
        dsimp [c]
        field_simp
      _ ≤ (r * ‖x‖) * 1 :=
        mul_le_mul_of_nonneg_left heval
          (mul_nonneg hr.le (norm_nonneg x))
      _ = r * ‖x‖ := mul_one _
  · intro hnorm x hx
    calc
      ‖φ x‖ ≤ ‖WeakDual.toStrongDual φ‖ * ‖x‖ :=
        (WeakDual.toStrongDual φ).le_opNorm x
      _ ≤ r * r⁻¹ :=
        mul_le_mul hnorm hx (norm_nonneg x) hr.le
      _ = 1 := by field_simp

/-- The intersection of the polars of all finite subsets of the predual
`r⁻¹`-ball is the dual `r`-ball.  This is the finite-polar compactness input
in the Krein--Šmulian separation lemma. -/
theorem sInter_weakDual_polar_finite_subset_closedBall_inv
    (r : ℝ) (hr : 0 < r) :
    ⋂₀ (WeakDual.polar ℝ ''
        {F : Set E |
          F.Finite ∧ F ⊆ Metric.closedBall (0 : E) r⁻¹}) =
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ E) r := by
  rw [← weakDual_polar_closedBall_inv r hr]
  ext φ
  constructor
  · intro hφ
    rw [WeakDual.polar_def]
    intro x hx
    have hsingleton :=
      hφ (WeakDual.polar ℝ ({x} : Set E))
        ⟨{x}, ⟨Set.finite_singleton x,
          Set.singleton_subset_iff.mpr hx⟩, rfl⟩
    rw [WeakDual.polar_def] at hsingleton
    exact hsingleton x (Set.mem_singleton x)
  · intro hφ t ht
    obtain ⟨F, hF, rfl⟩ := ht
    rw [WeakDual.polar_def] at hφ ⊢
    intro x hx
    exact hφ x (hF.2 hx)

/-- A weak-star compact set disjoint from a dual norm ball is already
disjoint from the polar of one finite subset of the corresponding predual
ball. -/
theorem exists_finite_polar_disjoint_of_compact_disjoint_normBall
    (r : ℝ) (hr : 0 < r) {Q : Set (WeakDual ℝ E)}
    (hQcompact : IsCompact Q)
    (hdisj :
      Disjoint Q
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E) r)) :
    ∃ F : Set E,
      F.Finite ∧
      F ⊆ Metric.closedBall (0 : E) r⁻¹ ∧
      Disjoint Q (WeakDual.polar ℝ F) := by
  let I :=
    {F : Set E //
      F.Finite ∧ F ⊆ Metric.closedBall (0 : E) r⁻¹}
  let U : I → Set (WeakDual ℝ E) :=
    fun F => (WeakDual.polar ℝ (F : Set E))ᶜ
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact (WeakDual.isClosed_polar ℝ (i : Set E)).isOpen_compl
  have hcover : Q ⊆ ⋃ i, U i := by
    intro φ hφQ
    have hφ_not_ball :
        φ ∉ WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E) r :=
      Set.disjoint_left.mp hdisj hφQ
    have hφ_not_inter :
        φ ∉ ⋂₀ (WeakDual.polar ℝ ''
          {F : Set E |
            F.Finite ∧
              F ⊆ Metric.closedBall (0 : E) r⁻¹}) := by
      rwa [sInter_weakDual_polar_finite_subset_closedBall_inv r hr]
    by_contra hφ_not_cover
    apply hφ_not_inter
    intro t ht
    obtain ⟨F, hF, rfl⟩ := ht
    by_contra hφ_not_polar
    apply hφ_not_cover
    exact Set.mem_iUnion.mpr
      ⟨⟨F, hF⟩, hφ_not_polar⟩
  obtain ⟨t, ht⟩ :=
    hQcompact.elim_finite_subcover U hUopen hcover
  let F : Set E := ⋃ i ∈ (t : Set I), (i : Set E)
  have hFfinite : F.Finite := by
    dsimp [F]
    exact t.finite_toSet.biUnion fun i _ => i.property.1
  have hFsubset : F ⊆ Metric.closedBall (0 : E) r⁻¹ := by
    intro x hx
    simp only [F, Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact i.property.2 hxi
  refine ⟨F, hFfinite, hFsubset, Set.disjoint_left.mpr ?_⟩
  intro φ hφQ hφpolar
  have hφcover := ht hφQ
  simp only [Set.mem_iUnion] at hφcover
  obtain ⟨i, hi, hφUi⟩ := hφcover
  apply hφUi
  rw [WeakDual.polar_def] at hφpolar ⊢
  intro x hxi
  apply hφpolar x
  simp only [F, Set.mem_iUnion]
  exact ⟨i, hi, hxi⟩

/-- A finite initial segment in the polar construction used by the
Krein--Šmulian separation lemma.  The `i`-th set lies in the predual ball of
radius `(i + 1)⁻¹`, and the accumulated polars separate `C` from the dual ball
of radius `n + 1`. -/
structure KreinSmulianFinitePolarStage
    (C : Set (WeakDual ℝ E)) (n : ℕ) where
  family : Fin n → Set E
  finite : ∀ i, (family i).Finite
  subset_closedBall :
    ∀ i,
      family i ⊆
        Metric.closedBall (0 : E) (((i.1 + 1 : ℕ) : ℝ)⁻¹)
  separated :
    Disjoint
      (weakDualNormSlice C ((n + 1 : ℕ) : ℝ))
      (⋂ i, WeakDual.polar ℝ (family i))

namespace KreinSmulianFinitePolarStage

/-- The empty initial segment, using the hypothesis that `C` misses the unit
dual ball. -/
def empty
    (C : Set (WeakDual ℝ E))
    (hunit :
      Disjoint C
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E) 1)) :
    KreinSmulianFinitePolarStage C 0 where
  family := Fin.elim0
  finite := fun i => Fin.elim0 i
  subset_closedBall := fun i => Fin.elim0 i
  separated := Set.disjoint_left.mpr fun φ hφ _ =>
    Set.disjoint_left.mp hunit hφ.1 (by simpa using hφ.2)

/-- Extend a finite polar stage by one set.  Compactness of the next bounded
slice and the preceding separation invariant provide the new finite set. -/
noncomputable def succ
    {C : Set (WeakDual ℝ E)} {n : ℕ}
    (S : KreinSmulianFinitePolarStage C n)
    (hclosed :
      ∀ r : ℝ, 0 ≤ r → IsClosed (weakDualNormSlice C r)) :
    KreinSmulianFinitePolarStage C (n + 1) := by
  let Q : Set (WeakDual ℝ E) :=
    weakDualNormSlice C ((n + 2 : ℕ) : ℝ) ∩
      ⋂ i, WeakDual.polar ℝ (S.family i)
  have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn2 : 0 ≤ ((n + 2 : ℕ) : ℝ) := by positivity
  have hsliceCompact :
      IsCompact (weakDualNormSlice C ((n + 2 : ℕ) : ℝ)) := by
    exact
      (WeakDual.isCompact_closedBall
        (𝕜 := ℝ) (0 : StrongDual ℝ E) ((n + 2 : ℕ) : ℝ)).of_isClosed_subset
        (hclosed _ hn2) Set.inter_subset_right
  have hQcompact : IsCompact Q := by
    exact hsliceCompact.inter_right
      (isClosed_iInter fun i =>
        WeakDual.isClosed_polar ℝ (S.family i))
  have hQdisj :
      Disjoint Q
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E)
            ((n + 1 : ℕ) : ℝ)) := by
    rw [Set.disjoint_left]
    intro φ hφQ hφball
    exact Set.disjoint_left.mp S.separated
      ⟨hφQ.1.1, hφball⟩ hφQ.2
  let hex :=
    exists_finite_polar_disjoint_of_compact_disjoint_normBall
      ((n + 1 : ℕ) : ℝ) hn1 hQcompact hQdisj
  let F : Set E := Classical.choose hex
  have hFspec :
      F.Finite ∧
        F ⊆
          Metric.closedBall (0 : E) (((n + 1 : ℕ) : ℝ)⁻¹) ∧
        Disjoint Q (WeakDual.polar ℝ F) :=
    Classical.choose_spec hex
  have hFfinite := hFspec.1
  have hFsubset := hFspec.2.1
  have hFdisj := hFspec.2.2
  let family : Fin (n + 1) → Set E :=
    Fin.lastCases F S.family
  have hfamily_last : family (Fin.last n) = F := by
    simp [family]
  have hfamily_castSucc :
      ∀ j : Fin n, family j.castSucc = S.family j := by
    intro j
    simp [family]
  refine
    { family := family
      finite := ?_
      subset_closedBall := ?_
      separated := ?_ }
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hfamily_last]
      exact hFfinite
    · rw [hfamily_castSucc]
      exact S.finite j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hfamily_last]
      simpa using hFsubset
    · rw [hfamily_castSucc]
      exact S.subset_closedBall j
  · rw [Set.disjoint_left]
    intro φ hφslice hφpolar
    have hφpolar' :
        ∀ i : Fin (n + 1),
          φ ∈ WeakDual.polar ℝ (family i) :=
      Set.mem_iInter.mp hφpolar
    apply Set.disjoint_left.mp hFdisj
    · refine ⟨hφslice, ?_⟩
      apply Set.mem_iInter.mpr
      intro i
      rw [← hfamily_castSucc]
      exact hφpolar' i.castSucc
    · rw [← hfamily_last]
      exact hφpolar' (Fin.last n)

/-- Extending a stage leaves all preceding finite polar sets unchanged. -/
@[simp]
theorem succ_family_castSucc
    {C : Set (WeakDual ℝ E)} {n : ℕ}
    (S : KreinSmulianFinitePolarStage C n)
    (hclosed :
      ∀ r : ℝ, 0 ≤ r → IsClosed (weakDualNormSlice C r))
    (i : Fin n) :
    (S.succ hclosed).family i.castSucc = S.family i := by
  simp [succ]

end KreinSmulianFinitePolarStage

/-- A coherent tower of the finite polar stages. -/
structure KreinSmulianFinitePolarTower
    (C : Set (WeakDual ℝ E)) where
  stage : ∀ n, KreinSmulianFinitePolarStage C n
  compatible :
    ∀ n (i : Fin n),
      (stage (n + 1)).family i.castSucc = (stage n).family i

namespace KreinSmulianFinitePolarTower

/-- The infinite family read from the successive last entries of a coherent
finite-polar tower. -/
def family {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C) (n : ℕ) : Set E :=
  (T.stage (n + 1)).family (Fin.last n)

/-- Every finite stage is the corresponding initial segment of `family`. -/
@[simp]
theorem stage_family_eq_family
    {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C)
    (n : ℕ) (i : Fin n) :
    (T.stage n).family i = T.family i.1 := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [T.compatible n j]
        exact ih j

theorem family_finite
    {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C) (n : ℕ) :
    (T.family n).Finite :=
  (T.stage (n + 1)).finite (Fin.last n)

theorem family_subset_closedBall
    {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C) (n : ℕ) :
    T.family n ⊆
      Metric.closedBall (0 : E) (((n + 1 : ℕ) : ℝ)⁻¹) := by
  change
    (T.stage (n + 1)).family (Fin.last n) ⊆
      Metric.closedBall (0 : E) (((n + 1 : ℕ) : ℝ)⁻¹)
  exact (T.stage (n + 1)).subset_closedBall (Fin.last n)

/-- At every stage, the first `n` polars separate `C` from the dual ball of
radius `n + 1`. -/
theorem separated_initial
    {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C) (n : ℕ) :
    Disjoint
      (weakDualNormSlice C ((n + 1 : ℕ) : ℝ))
      (⋂ i : Fin n, WeakDual.polar ℝ (T.family i.1)) := by
  simpa only [stage_family_eq_family] using
    (T.stage n).separated

/-- The accumulated finite polars have empty intersection with `C`. -/
theorem disjoint_iInter_polar_family
    {C : Set (WeakDual ℝ E)}
    (T : KreinSmulianFinitePolarTower C) :
    Disjoint C (⋂ n, WeakDual.polar ℝ (T.family n)) := by
  rw [Set.disjoint_left]
  intro φ hφC hφpolar
  obtain ⟨n, hn⟩ :=
    exists_nat_ge ‖WeakDual.toStrongDual φ‖
  have hφball :
      φ ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ E)
          ((n + 1 : ℕ) : ℝ) := by
    have hnorm :
        ‖WeakDual.toStrongDual φ‖ ≤ ((n + 1 : ℕ) : ℝ) :=
      hn.trans (by exact_mod_cast Nat.le_succ n)
    simpa only [Set.mem_preimage, mem_closedBall_zero_iff] using hnorm
  apply Set.disjoint_left.mp (T.separated_initial n)
  · exact ⟨hφC, hφball⟩
  · apply Set.mem_iInter.mpr
    intro i
    exact Set.mem_iInter.mp hφpolar i.1

end KreinSmulianFinitePolarTower

/-- Construct the coherent finite-polar tower from closed bounded slices and
separation from the unit dual ball. -/
noncomputable def kreinSmulianFinitePolarTower
    (C : Set (WeakDual ℝ E))
    (hclosed :
      ∀ r : ℝ, 0 ≤ r → IsClosed (weakDualNormSlice C r))
    (hunit :
      Disjoint C
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E) 1)) :
    KreinSmulianFinitePolarTower C := by
  let stage : ∀ n, KreinSmulianFinitePolarStage C n :=
    fun n =>
      Nat.rec
        (KreinSmulianFinitePolarStage.empty C hunit)
        (fun _ S => S.succ hclosed)
        n
  refine ⟨stage, ?_⟩
  intro n i
  change ((stage n).succ hclosed).family i.castSucc =
    (stage n).family i
  exact
    KreinSmulianFinitePolarStage.succ_family_castSucc
      (stage n) hclosed i

end FTAPTheorem42
