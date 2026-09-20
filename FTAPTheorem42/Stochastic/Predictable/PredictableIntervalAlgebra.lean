/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetellingOperations
import Mathlib.MeasureTheory.SetAlgebra

/-!
# An interval algebra for the predictable sigma algebra

The predictable-section argument uses finite unions of stochastic intervals
`[[S,T[[`, where both endpoints are foretold stopping times.  This module
packages those unions, proves that they form an algebra, and identifies the
sigma algebra that they generate with the predictable sigma algebra.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableIntervalAlgebra

/-- The predictable open upper set of an extended stopping time. -/
def stoppingTimeOpenUpperSet
    (σ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {p | σ p.2 < (p.1 : WithTop ℝ≥0)}

/-- The open upper set of any stopping time is predictable. -/
theorem measurableSet_stoppingTimeOpenUpperSet
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    MeasurableSet[ℱ.predictable] (stoppingTimeOpenUpperSet σ) := by
  let U : Set (ℝ≥0 × Ω) :=
    ⋃ q : ℚ, Set.Ioi (Real.toNNReal q) ×ˢ
      {ω | σ ω ≤ (Real.toNNReal q : WithTop ℝ≥0)}
  have hU : MeasurableSet[ℱ.predictable] U := by
    apply MeasurableSet.iUnion
    intro q
    exact measurableSet_predictable_Ioi_prod (hσ (Real.toNNReal q))
  convert hU using 1
  ext p
  simp only [stoppingTimeOpenUpperSet, U, Set.mem_ofPred_eq,
    Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi]
  constructor
  · intro hp
    have hfinite : σ p.2 ≠ ⊤ := ne_top_of_lt hp
    let s : ℝ≥0 := (σ p.2).untop hfinite
    have hs : (s : WithTop ℝ≥0) = σ p.2 :=
      WithTop.coe_untop (σ p.2) hfinite
    have hst : s < p.1 := by
      exact WithTop.coe_lt_coe.mp (hs ▸ hp)
    obtain ⟨q, -, hsq, hqt⟩ :=
      (NNReal.lt_iff_exists_rat_btwn s p.1).1 hst
    refine ⟨q, hqt, ?_⟩
    rw [← hs]
    exact WithTop.coe_le_coe.mpr hsq.le
  · rintro ⟨q, hqt, hσq⟩
    exact hσq.trans_lt (WithTop.coe_lt_coe.mpr hqt)

/-- The closed upper stochastic interval of a foretold stopping time. -/
def foretoldUpperSet
    (σ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {p | σ p.2 ≤ (p.1 : WithTop ℝ≥0)}

/-- A foretold stopping time has a predictable closed upper stochastic
interval. -/
theorem measurableSet_foretoldUpperSet
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : Ω → WithTop ℝ≥0} (a : StoppingTimeForetelling ℱ σ) :
    MeasurableSet[ℱ.predictable] (foretoldUpperSet σ) := by
  let zeroGraph : Set (ℝ≥0 × Ω) :=
    {(0 : ℝ≥0)} ×ˢ {ω | σ ω = 0}
  let approximated : Set (ℝ≥0 × Ω) :=
    ⋂ n, stoppingTimeOpenUpperSet (a.time n)
  have hzero : MeasurableSet[ℱ.predictable] zeroGraph := by
    apply measurableSet_predictable_singleton_bot_prod
    exact a.target_isStoppingTime.measurableSet_eq 0
  have happ : MeasurableSet[ℱ.predictable] approximated :=
    MeasurableSet.iInter fun n =>
      measurableSet_stoppingTimeOpenUpperSet (a.isStoppingTime n)
  convert hzero.union happ using 1
  ext p
  simp only [foretoldUpperSet, zeroGraph, approximated,
    Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_iInter,
    stoppingTimeOpenUpperSet]
  constructor
  · intro hp
    by_cases hσ0 : σ p.2 = 0
    · by_cases hp0 : p.1 = 0
      · exact Or.inl ⟨hp0, hσ0⟩
      · exact Or.inr fun n => by
          have htime0 : a.time n p.2 = 0 :=
            bot_unique ((a.le n p.2).trans_eq hσ0)
          rw [htime0]
          exact WithTop.coe_pos.mpr (pos_iff_ne_zero.mpr hp0)
    · exact Or.inr fun n => (a.lt_of_ne_zero n p.2 hσ0).trans_le hp
  · rintro (hp | hp)
    · rw [hp.1, hp.2]
      exact bot_le
    · apply le_of_tendsto (a.tendsto p.2)
      exact Eventually.of_forall fun n => (hp n).le

/-- One stochastic interval `[[left,right[[`. -/
structure Interval
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) where
  left : Ω → WithTop ℝ≥0
  right : Ω → WithTop ℝ≥0
  left_foretelling : StoppingTimeForetelling ℱ left
  right_foretelling : StoppingTimeForetelling ℱ right

namespace Interval

/-- The carrier of a stochastic interval. -/
def carrier
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) : Set (ℝ≥0 × Ω) :=
  foretoldUpperSet I.left \ foretoldUpperSet I.right

theorem mem_carrier_iff
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ I.carrier ↔
      I.left ω ≤ (t : WithTop ℝ≥0) ∧
        (t : WithTop ℝ≥0) < I.right ω := by
  simp only [carrier, foretoldUpperSet, Set.mem_sdiff,
    Set.mem_ofPred_eq, not_le]

theorem measurableSet_carrier
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) : MeasurableSet[ℱ.predictable] I.carrier :=
  (measurableSet_foretoldUpperSet I.left_foretelling).diff
    (measurableSet_foretoldUpperSet I.right_foretelling)

/-- The universal stochastic interval. -/
noncomputable def univ
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) : Interval ℱ where
  left := fun _ => 0
  right := fun _ => ⊤
  left_foretelling := StoppingTimeForetelling.const ℱ 0
  right_foretelling := StoppingTimeForetelling.const ℱ ⊤

theorem carrier_univ
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    (univ ℱ).carrier = Set.univ := by
  ext p
  rcases p with ⟨t, ω⟩
  rw [Interval.mem_carrier_iff]
  simp only [Set.mem_univ, iff_true]
  change (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) ∧
    (t : WithTop ℝ≥0) < ⊤
  exact ⟨bot_le, WithTop.coe_lt_top t⟩

/-- Intersection of two stochastic intervals. -/
noncomputable def inter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I J : Interval ℱ) : Interval ℱ where
  left := fun ω => max (I.left ω) (J.left ω)
  right := fun ω => min (I.right ω) (J.right ω)
  left_foretelling := I.left_foretelling.max J.left_foretelling
  right_foretelling := I.right_foretelling.min J.right_foretelling

theorem carrier_inter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I J : Interval ℱ) :
    (inter I J).carrier = I.carrier ∩ J.carrier := by
  ext p
  rcases p with ⟨t, ω⟩
  simp only [Interval.mem_carrier_iff, Interval.inter, max_le_iff,
    lt_min_iff, Set.mem_inter_iff]
  tauto

/-- The two intervals forming the complement of one stochastic interval. -/
noncomputable def complement
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) : List (Interval ℱ) :=
  [
    { left := fun _ => 0
      right := I.left
      left_foretelling := StoppingTimeForetelling.const ℱ 0
      right_foretelling := I.left_foretelling },
    { left := I.right
      right := fun _ => ⊤
      left_foretelling := I.right_foretelling
      right_foretelling := StoppingTimeForetelling.const ℱ ⊤ }
  ]

end Interval

/-- Carrier of a finite list of stochastic intervals. -/
def carrier
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} :
    List (Interval ℱ) → Set (ℝ≥0 × Ω)
  | [] => ∅
  | I :: L => I.carrier ∪ carrier L

attribute [simp] carrier.eq_1

@[simp] theorem carrier_cons
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) (L : List (Interval ℱ)) :
    carrier (I :: L) = I.carrier ∪ carrier L := rfl

/-- Pairwise intersections of two finite interval unions. -/
noncomputable def inter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} :
    List (Interval ℱ) → List (Interval ℱ) → List (Interval ℱ)
  | [], _ => []
  | I :: L, K => K.map (Interval.inter I) ++ inter L K

theorem carrier_map_inter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) (L : List (Interval ℱ)) :
    carrier (L.map (Interval.inter I)) = I.carrier ∩ carrier L := by
  induction L with
  | nil => simp
  | cons J L ih =>
      simp only [List.map_cons, carrier_cons, Interval.carrier_inter, ih]
      ext p
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto

theorem carrier_append
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (L K : List (Interval ℱ)) :
    carrier (L ++ K) = carrier L ∪ carrier K := by
  induction L with
  | nil => simp
  | cons I L ih => simp only [List.cons_append, carrier_cons, ih, union_assoc]

theorem carrier_inter
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (L K : List (Interval ℱ)) :
    carrier (inter L K) = carrier L ∩ carrier K := by
  induction L with
  | nil => simp [inter]
  | cons I L ih =>
      simp only [inter, carrier_append, carrier_map_inter, carrier_cons, ih]
      ext p
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto

/-- Complement of a finite interval union, distributed back into finite
union normal form. -/
noncomputable def complement
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} :
    List (Interval ℱ) → List (Interval ℱ)
  | [] => [Interval.univ ℱ]
  | I :: L => inter I.complement (complement L)

theorem carrier_interval_complement
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) :
    carrier I.complement = I.carrierᶜ := by
  ext p
  rcases p with ⟨t, ω⟩
  simp only [Interval.complement, carrier_cons, carrier.eq_1,
    union_empty, Interval.mem_carrier_iff, Set.mem_compl_iff,
    Set.mem_union]
  rw [not_and_or, not_le, not_lt]
  constructor
  · rintro (h | h)
    · exact Or.inl h.2
    · exact Or.inr h.1
  · rintro (h | h)
    · exact Or.inl ⟨bot_le, h⟩
    · exact Or.inr ⟨h, WithTop.coe_lt_top t⟩

theorem carrier_complement
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (L : List (Interval ℱ)) :
    carrier (complement L) = (carrier L)ᶜ := by
  induction L with
  | nil => simp [complement, Interval.carrier_univ]
  | cons I L ih =>
      rw [complement, carrier_inter, carrier_interval_complement, ih,
        carrier_cons, compl_union]

/-- Finite unions of foretold stochastic intervals. -/
def sets
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    Set (Set (ℝ≥0 × Ω)) :=
  {A | ∃ L : List (Interval ℱ), carrier L = A}

theorem isSetAlgebra_sets
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    IsSetAlgebra (sets ℱ) where
  empty_mem := ⟨[], rfl⟩
  compl_mem := by
    rintro A ⟨L, rfl⟩
    exact ⟨complement L, carrier_complement L⟩
  union_mem := by
    rintro A B ⟨L, rfl⟩ ⟨K, rfl⟩
    exact ⟨L ++ K, carrier_append L K⟩

theorem measurableSet_of_mem_sets
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {A : Set (ℝ≥0 × Ω)} (hA : A ∈ sets ℱ) :
    MeasurableSet[ℱ.predictable] A := by
  obtain ⟨L, rfl⟩ := hA
  induction L with
  | nil => exact @MeasurableSet.empty (ℝ≥0 × Ω) ℱ.predictable
  | cons I L ih =>
      exact (@Interval.measurableSet_carrier Ω _ ℱ I).union ih

/-! ## Generation of the predictable sigma algebra -/

/-- A stopping-time gate which is infinite on `A` and equals `i` on its
complement. -/
noncomputable def eventGate (i : ℝ≥0) (A : Set Ω) : Ω → WithTop ℝ≥0 :=
  by
    classical
    exact fun ω => if ω ∈ A then ⊤ else (i : WithTop ℝ≥0)

/-- An event known at `i` can be encoded by a stopping-time gate. -/
theorem eventGate_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {i : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ i] A) :
    IsStoppingTime ℱ (eventGate i A) := by
  intro t
  by_cases hit : i ≤ t
  · have heq : {ω | eventGate i A ω ≤ (t : WithTop ℝ≥0)} = Aᶜ := by
      ext ω
      by_cases hω : ω ∈ A
      · constructor
        · intro h
          have htop : (⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
            simpa [eventGate, hω] using h
          exact (not_le_of_gt (WithTop.coe_lt_top t)) htop |>.elim
        · intro h
          exact (h hω).elim
      · constructor
        · intro _
          exact hω
        · intro _
          simpa [eventGate, hω] using WithTop.coe_le_coe.mpr hit
    rw [heq]
    exact (ℱ.mono hit _ hA).compl
  · have heq : {ω | eventGate i A ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      by_cases hω : ω ∈ A
      · change eventGate i A ω ≤ (t : WithTop ℝ≥0) ↔ False
        constructor
        · intro h
          have htop : (⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
            simpa [eventGate, hω] using h
          exact (not_le_of_gt (WithTop.coe_lt_top t)) htop
        · intro h
          exact h.elim
      · simp only [eventGate, hω, ite_false, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h => hit (WithTop.coe_le_coe.mp h)
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- The time `c` on `A` and infinity off `A`, obtained by restricting a
deterministic foretold time to a later stopping-time gate. -/
noncomputable def constOnEvent
    (i c : ℝ≥0) (A : Set Ω) : Ω → WithTop ℝ≥0 :=
  StoppingTimeForetelling.restrictLE (fun _ => (c : WithTop ℝ≥0))
    (eventGate i A)

omit [MeasurableSpace Ω] in
theorem constOnEvent_eq_of_mem
    {i c : ℝ≥0} {A : Set Ω} {ω : Ω} (hω : ω ∈ A) :
    constOnEvent i c A ω = (c : WithTop ℝ≥0) := by
  classical
  unfold constOnEvent StoppingTimeForetelling.restrictLE eventGate
  rw [ite_eq_left hω,
    ite_eq_left (show (c : WithTop ℝ≥0) ≤ ⊤ from le_top)]

omit [MeasurableSpace Ω] in
theorem constOnEvent_eq_top_of_not_mem
    {i c : ℝ≥0} (hic : i < c) {A : Set Ω} {ω : Ω} (hω : ω ∉ A) :
    constOnEvent i c A ω = ⊤ := by
  classical
  simp only [constOnEvent, StoppingTimeForetelling.restrictLE,
    eventGate, hω, ite_false]
  rw [ite_eq_right]
  exact not_le_of_gt (WithTop.coe_lt_coe.mpr hic)

/-- A deterministic time strictly after the revelation time of `A`, kept
on `A` and sent to infinity otherwise, is foretold. -/
noncomputable def constOnEvent_foretelling
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {i c : ℝ≥0} (_hic : i < c) {A : Set Ω}
    (hA : MeasurableSet[ℱ i] A) :
    StoppingTimeForetelling ℱ (constOnEvent i c A) :=
  (StoppingTimeForetelling.const ℱ (c : WithTop ℝ≥0)).on_le
    (eventGate_isStoppingTime hA)

/-- The upper interval starting at `c` on `A` is one member of the interval
algebra when `A` is known strictly before `c`. -/
noncomputable def upperOnEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {i c : ℝ≥0} (hic : i < c) {A : Set Ω}
    (hA : MeasurableSet[ℱ i] A) : Interval ℱ where
  left := constOnEvent i c A
  right := fun _ => ⊤
  left_foretelling := constOnEvent_foretelling hic hA
  right_foretelling := StoppingTimeForetelling.const ℱ ⊤

theorem carrier_upperOnEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {i c : ℝ≥0} (hic : i < c) {A : Set Ω}
    (hA : MeasurableSet[ℱ i] A) :
    (upperOnEvent hic hA).carrier = Set.Ici c ×ˢ A := by
  classical
  ext p
  rcases p with ⟨t, ω⟩
  rw [Interval.mem_carrier_iff]
  simp only [upperOnEvent, WithTop.coe_lt_top, and_true,
    Set.mem_prod, Set.mem_Ici]
  by_cases hω : ω ∈ A
  · rw [constOnEvent_eq_of_mem hω]
    simp only [WithTop.coe_le_coe, hω, and_true]
  · rw [constOnEvent_eq_top_of_not_mem hic hω]
    constructor
    · intro h
      exact (not_le_of_gt (WithTop.coe_lt_top t)) h |>.elim
    · intro h
      exact (hω h.2).elim

/-- A positive deterministic sequence decreasing to zero. -/
noncomputable def rightApproxZero (n : ℕ) : ℝ≥0 :=
  1 / ((n : ℝ≥0) + 1)

theorem rightApproxZero_pos (n : ℕ) : 0 < rightApproxZero n := by
  unfold rightApproxZero
  positivity

theorem tendsto_rightApproxZero :
    Tendsto rightApproxZero atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The time zero on `A` and infinity off `A`. -/
noncomputable def zeroOnEvent (A : Set Ω) : Ω → WithTop ℝ≥0 :=
  StoppingTimeForetelling.restrictEvent (fun _ => 0) A

/-- If `A` is known at time zero, the time zero on `A` and infinity off
`A` is foretold. -/
noncomputable def zeroOnEvent_foretelling
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    StoppingTimeForetelling ℱ (zeroOnEvent A) :=
  (StoppingTimeForetelling.const ℱ 0).on_event A hA

/-- A shrinking interval which isolates `{0} × A`. -/
noncomputable def zeroSliceApprox
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (n : ℕ) : Interval ℱ where
  left := zeroOnEvent A
  right := fun _ => (rightApproxZero n : WithTop ℝ≥0)
  left_foretelling := zeroOnEvent_foretelling hA
  right_foretelling :=
    StoppingTimeForetelling.const ℱ (rightApproxZero n : WithTop ℝ≥0)

theorem iInter_carrier_zeroSliceApprox
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    (⋂ n, (zeroSliceApprox hA n).carrier) = {(0 : ℝ≥0)} ×ˢ A := by
  classical
  ext p
  rcases p with ⟨t, ω⟩
  simp only [Set.mem_iInter, Interval.mem_carrier_iff, zeroSliceApprox,
    Set.mem_prod, Set.mem_singleton_iff]
  have hzeroApply : zeroOnEvent A ω =
      if ω ∈ A then 0 else ⊤ := by
    rfl
  rw [hzeroApply]
  by_cases hω : ω ∈ A
  · simp only [hω, ite_true]
    constructor
    · intro h
      refine ⟨?_, trivial⟩
      apply le_antisymm
      · by_contra ht
        have htpos : 0 < t := lt_of_not_ge ht
        have heventually : ∀ᶠ n in atTop, rightApproxZero n < t :=
          tendsto_rightApproxZero.eventually (Iio_mem_nhds htpos)
        obtain ⟨n, hn⟩ := heventually.exists
        exact (lt_asymm hn (WithTop.coe_lt_coe.mp (h n).2)).elim
      · exact bot_le
    · rintro ⟨rfl, -⟩ n
      exact ⟨bot_le, WithTop.coe_lt_coe.mpr (rightApproxZero_pos n)⟩
  · constructor
    · intro h
      have hfalse := (h 0).1
      simp only [hω, ite_false] at hfalse
      exact (not_le_of_gt (WithTop.coe_lt_top t)) hfalse |>.elim
    · rintro ⟨-, hmem⟩
      exact (hω hmem).elim

/-- The interval algebra generates the predictable sigma algebra. -/
theorem generateFrom_sets
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    MeasurableSpace.generateFrom (sets ℱ) = ℱ.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro A hA
    exact measurableSet_of_mem_sets hA
  · unfold Filtration.predictable
    apply MeasurableSpace.generateFrom_le
    rintro A (⟨B, hB, rfl⟩ | ⟨i, B, hB, rfl⟩)
    · change MeasurableSet[MeasurableSpace.generateFrom (sets ℱ)]
        ({(0 : ℝ≥0)} ×ˢ B)
      rw [← iInter_carrier_zeroSliceApprox hB]
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨[(zeroSliceApprox hB n)], by simp⟩
    · let c : ℕ → ℝ≥0 := fun n => i + rightApproxZero n
      have hic : ∀ n, i < c n := fun n =>
        lt_add_of_pos_right i (rightApproxZero_pos n)
      have heq : (⋃ n, (upperOnEvent (hic n) hB).carrier) =
          Set.Ioi i ×ˢ B := by
        ext p
        rcases p with ⟨t, ω⟩
        simp only [Set.mem_iUnion, carrier_upperOnEvent,
          Set.mem_prod, Set.mem_Ici, Set.mem_Ioi]
        constructor
        · rintro ⟨n, htn, hω⟩
          exact ⟨(hic n).trans_le htn, hω⟩
        · rintro ⟨hit, hω⟩
          have htend : Tendsto c atTop (𝓝 i) := by
            simpa [c] using
              (tendsto_const_nhds.add tendsto_rightApproxZero :
                Tendsto (fun n => i + rightApproxZero n) atTop (𝓝 (i + 0)))
          have heventually : ∀ᶠ n in atTop, c n < t :=
            htend.eventually (Iio_mem_nhds hit)
          obtain ⟨n, hn⟩ := heventually.exists
          exact ⟨n, hn.le, hω⟩
      rw [← heq]
      apply MeasurableSet.iUnion
      intro n
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨[(upperOnEvent (hic n) hB)], by simp⟩

/-! ## Debuts of interval-algebra sets -/

/-- The debut of a time-sample set, with the empty section assigned
infinity. -/
noncomputable def debut (A : Set (ℝ≥0 × Ω)) (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact ⨅ t : ℝ≥0, if (t, ω) ∈ A then (t : WithTop ℝ≥0) else ⊤

omit [MeasurableSpace Ω] in
theorem debut_empty (ω : Ω) : debut (∅ : Set (ℝ≥0 × Ω)) ω = ⊤ := by
  classical
  simp [debut]

omit [MeasurableSpace Ω] in
theorem debut_union (A B : Set (ℝ≥0 × Ω)) (ω : Ω) :
    debut (A ∪ B) ω = min (debut A ω) (debut B ω) := by
  classical
  unfold debut
  rw [← iInf_inf_eq]
  apply iInf_congr
  intro t
  by_cases hA : (t, ω) ∈ A
  · by_cases hB : (t, ω) ∈ B
    · have hAB : (t, ω) ∈ A ∪ B := Or.inl hA
      rw [ite_eq_left hAB, ite_eq_left hA, ite_eq_left hB]
      exact (min_eq_left le_rfl).symm
    · have hAB : (t, ω) ∈ A ∪ B := Or.inl hA
      rw [ite_eq_left hAB, ite_eq_left hA, ite_eq_right hB]
      exact (min_eq_left le_top).symm
  · by_cases hB : (t, ω) ∈ B
    · have hAB : (t, ω) ∈ A ∪ B := Or.inr hB
      rw [ite_eq_left hAB, ite_eq_right hA, ite_eq_left hB]
      exact (min_eq_right le_top).symm
    · have hAB : (t, ω) ∉ A ∪ B := by
        rintro (h | h)
        · exact hA h
        · exact hB h
      rw [ite_eq_right hAB, ite_eq_right hA, ite_eq_right hB]
      exact (min_eq_left le_rfl).symm

theorem debut_interval
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) (ω : Ω) :
    debut I.carrier ω =
      StoppingTimeForetelling.restrictLT I.left I.right ω := by
  classical
  unfold debut StoppingTimeForetelling.restrictLT
  by_cases hlt : I.left ω < I.right ω
  · rw [ite_eq_left hlt]
    have hleftFinite : I.left ω ≠ ⊤ := ne_top_of_lt hlt
    let s : ℝ≥0 := (I.left ω).untop hleftFinite
    have hs : (s : WithTop ℝ≥0) = I.left ω :=
      WithTop.coe_untop (I.left ω) hleftFinite
    apply le_antisymm
    · apply iInf_le_of_le s
      rw [ite_eq_left]
      · exact hs.le
      · rw [Interval.mem_carrier_iff, hs]
        exact ⟨le_rfl, hlt⟩
    · apply le_iInf
      intro t
      by_cases ht : (t, ω) ∈ I.carrier
      · rw [ite_eq_left ht]
        exact (Interval.mem_carrier_iff I t ω).1 ht |>.1
      · rw [ite_eq_right ht]
        exact le_top
  · rw [ite_eq_right hlt]
    have hempty : ∀ t : ℝ≥0, (t, ω) ∉ I.carrier := by
      intro t ht
      exact hlt (((Interval.mem_carrier_iff I t ω).1 ht).1.trans_lt
        ((Interval.mem_carrier_iff I t ω).1 ht).2)
    simp [hempty]

omit [MeasurableSpace Ω] in
theorem debut_le_of_mem {A : Set (ℝ≥0 × Ω)} {t : ℝ≥0} {ω : Ω}
    (ht : (t, ω) ∈ A) : debut A ω ≤ (t : WithTop ℝ≥0) := by
  classical
  unfold debut
  exact iInf_le_of_le t (by rw [ite_eq_left ht])

theorem debut_interval_mem_of_ne_top
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (I : Interval ℱ) (ω : Ω) (hfinite : debut I.carrier ω ≠ ⊤) :
    ((debut I.carrier ω).untop hfinite, ω) ∈ I.carrier := by
  have hd := debut_interval I ω
  by_cases hlt : I.left ω < I.right ω
  · rw [StoppingTimeForetelling.restrictLT, ite_eq_left hlt] at hd
    rw [Interval.mem_carrier_iff,
      show ((debut I.carrier ω).untop hfinite : WithTop ℝ≥0) =
          debut I.carrier ω from
        WithTop.coe_untop (debut I.carrier ω) hfinite,
      hd]
    exact ⟨le_rfl, hlt⟩
  · rw [StoppingTimeForetelling.restrictLT, ite_eq_right hlt] at hd
    exact (hfinite hd).elim

theorem debut_carrier_mem_of_ne_top
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (L : List (Interval ℱ)) (ω : Ω)
    (hfinite : debut (carrier L) ω ≠ ⊤) :
    ((debut (carrier L) ω).untop hfinite, ω) ∈ carrier L := by
  induction L with
  | nil =>
      exact (hfinite (debut_empty ω)).elim
  | cons I L ih =>
      have hd : debut (carrier (I :: L)) ω =
          min (debut I.carrier ω) (debut (carrier L) ω) :=
        debut_union I.carrier (carrier L) ω
      by_cases hle : debut I.carrier ω ≤ debut (carrier L) ω
      · have hmin : debut (carrier (I :: L)) ω = debut I.carrier ω := by
          rw [hd, min_eq_left hle]
        have hIfinite : debut I.carrier ω ≠ ⊤ := by
          intro htop
          apply hfinite
          rw [hmin, htop]
        have hmem := debut_interval_mem_of_ne_top I ω hIfinite
        change ((debut (carrier (I :: L)) ω).untop hfinite, ω) ∈
          I.carrier ∪ carrier L
        apply Set.mem_union_left
        have ht : (debut (carrier (I :: L)) ω).untop hfinite =
            (debut I.carrier ω).untop hIfinite := by
          apply WithTop.coe_injective
          rw [WithTop.coe_untop (debut (carrier (I :: L)) ω) hfinite,
            WithTop.coe_untop (debut I.carrier ω) hIfinite, hmin]
        rwa [ht]
      · have hlt : debut (carrier L) ω < debut I.carrier ω :=
          lt_of_not_ge hle
        have hmin : debut (carrier (I :: L)) ω = debut (carrier L) ω := by
          rw [hd, min_eq_right hlt.le]
        have hLfinite : debut (carrier L) ω ≠ ⊤ := by
          intro htop
          apply hfinite
          rw [hmin, htop]
        have hmem := ih hLfinite
        change ((debut (carrier (I :: L)) ω).untop hfinite, ω) ∈
          I.carrier ∪ carrier L
        apply Set.mem_union_right
        have ht : (debut (carrier (I :: L)) ω).untop hfinite =
            (debut (carrier L) ω).untop hLfinite := by
          apply WithTop.coe_injective
          rw [WithTop.coe_untop (debut (carrier (I :: L)) ω) hfinite,
            WithTop.coe_untop (debut (carrier L) ω) hLfinite, hmin]
        rwa [ht]

/-- The debut of a finite interval union is foretold. -/
noncomputable def debut_foretelling
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ) :
    (L : List (Interval ℱ)) → StoppingTimeForetelling ℱ (debut (carrier L))
  | [] => by
      have heq : debut (carrier ([] : List (Interval ℱ))) = fun _ => ⊤ := by
        funext ω
        exact debut_empty ω
      rw [heq]
      exact StoppingTimeForetelling.const ℱ (⊤ : WithTop ℝ≥0)
  | I :: L => by
      have hI : StoppingTimeForetelling ℱ (debut I.carrier) := by
        have heq : debut I.carrier =
            StoppingTimeForetelling.restrictLT I.left I.right := by
          funext ω
          exact debut_interval I ω
        rw [heq]
        exact I.left_foretelling.on_lt hUsual I.right_foretelling
      have hL := debut_foretelling hUsual L
      have heq : debut (carrier (I :: L)) =
          fun ω => min (debut I.carrier ω) (debut (carrier L) ω) := by
        funext ω
        exact debut_union I.carrier (carrier L) ω
      rw [heq]
      exact hI.min hL

end PredictableIntervalAlgebra

end FTAPTheorem42
