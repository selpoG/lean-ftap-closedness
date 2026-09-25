/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Stopping.MonotoneCadlagRationalPassage
import FTAPTheorem42.Stochastic.Predictable.PredictableGraphForetelling

/-!
# Enumerating finite-variation jumps by variation passages

A nonzero jump of a bounded-variation path produces a positive jump of its
cumulative total variation.  A rational level strictly between the left and
right variation values therefore has its first strict passage at precisely
that jump time.  This replaces a nonmeasurable pathwise choice of jump times
by a fixed countable family of stopping times.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CumulativeVariationJumpEnumeration

/-- A fixed surjective enumeration of the positive rational numbers,
embedded in the reals.  Positivity prevents the associated variation passage
from occurring at the initial time. -/
noncomputable def rationalLevel (n : ℕ) : ℝ :=
  MonotoneCadlagRationalPassage.positiveRationalLevel n

theorem rationalLevel_pos (n : ℕ) : 0 < rationalLevel n := by
  exact MonotoneCadlagRationalPassage.positiveRationalLevel_pos n

theorem exists_rationalLevel_eq (q : ℚ) (hq : 0 < q) :
    ∃ n, rationalLevel n = (q : ℝ) :=
  MonotoneCadlagRationalPassage.exists_positiveRationalLevel_eq q hq

omit [MeasurableSpace Ω] in
/-- If all values strictly before `t` lie below `l`, while the value at `t`
lies above `c > l`, then the first strict upper-level passage is `t`. -/
theorem strictHittingAfter_eq_of_forall_lt_le
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) {t : ℝ≥0} {l c : ℝ}
    (hbefore : ∀ s, s < t → X s ω ≤ l) (hlc : l < c)
    (hct : c < X t ω) :
    RightContinuousHittingTime.strictHittingAfter X c ω = t := by
  exact MonotoneCadlagRationalPassage.strictHittingAfter_eq_of_forall_lt_le
    X ω hbefore hlc hct

variable
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Rational cumulative-variation passages, clamped at a deterministic
horizon so that every graph is finite. -/
noncomputable def passageGraph
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) : Ω → ℝ≥0 :=
  fun ω => (min
    (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter H
      (rationalLevel n) ω)
    (T : WithTop ℝ≥0)).untopA

omit [IsFiniteMeasure μ] in
/-- Clamping makes every rational passage no later than the deterministic
horizon. -/
theorem passageGraph_le
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    passageGraph H T n ω ≤ T := by
  have hne : min
      (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter H
        (rationalLevel n) ω)
      (T : WithTop ℝ≥0) ≠ ⊤ := by
    exact ne_of_lt ((min_le_right _ _).trans_lt (WithTop.coe_lt_top T))
  unfold passageGraph
  rw [WithTop.untopA_eq_untop hne]
  apply WithTop.coe_le_coe.mp
  rw [WithTop.coe_untop _ hne]
  exact min_le_right _ _

omit [IsFiniteMeasure μ] in
/-- Positive variation levels and a positive clamp horizon make every passage
graph strictly positive.  This removes the initial-time obstruction to a
strict announcing sequence. -/
theorem passageGraph_pos
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (ω : Ω) :
    0 < passageGraph H T n ω := by
  let V := SIntegrableFiniteVariationBridge.cumulativeVariation H
  let c := rationalLevel n
  have hVzero : V 0 ω = 0 := by
    simp [V, SIntegrableFiniteVariationBridge.cumulativeVariation]
  have hVRight :=
    SIntegrableFiniteVariationBridge.cumulativeVariation_rightContinuous
      H hRight ω 0
  have hVContinuousAt : ContinuousAt (fun t => V t ω) 0 := by
    have hIci : Set.Ici (0 : ℝ≥0) = Set.univ := by
      ext t
      simp
    rw [hIci] at hVRight
    simpa only [V, continuousWithinAt_univ] using hVRight
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ≥0), V t ω < c := by
    have : Set.Iio c ∈ 𝓝 (V 0 ω) := by
      rw [hVzero]
      exact Iio_mem_nhds (rationalLevel_pos n)
    exact hVContinuousAt.eventually this
  obtain ⟨d, hdpos, hd⟩ :=
    exists_Ico_subset_of_mem_nhds hNear ⟨1, zero_lt_one⟩
  have hHitPos : (0 : WithTop ℝ≥0) <
      SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
        H c ω := by
    have hnot : ¬SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
        H c ω < (d : WithTop ℝ≥0) := by
      intro hlt
      rw [SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter,
        RightContinuousHittingTime.strictHittingAfter,
        MeasureTheory.hittingAfter_lt_iff] at hlt
      obtain ⟨j, hj, hjump⟩ := hlt
      have hjless : V j ω < c := hd hj
      change c < V j ω at hjump
      exact (not_lt_of_ge hjump.le) hjless
    exact (WithTop.coe_lt_coe.mpr hdpos).trans_le (le_of_not_gt hnot)
  have hminPos : (0 : WithTop ℝ≥0) < min
      (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
        H c ω) (T : WithTop ℝ≥0) :=
    lt_min hHitPos (WithTop.coe_pos.mpr hT)
  have hne : min
      (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
        H c ω) (T : WithTop ℝ≥0) ≠ ⊤ :=
    ne_of_lt ((min_le_right _ _).trans_lt (WithTop.coe_lt_top T))
  unfold passageGraph
  rw [WithTop.untopA_eq_untop hne]
  apply WithTop.coe_lt_coe.mp
  rw [WithTop.coe_zero, WithTop.coe_untop _ hne]
  exact hminPos

omit [IsFiniteMeasure μ] in
/-- Immediately before `t`, cumulative total variation converges to its
value at `t` minus the size of the left jump of the path. -/
theorem tendsto_cumulativeVariation_left
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) {t : ℝ≥0} (ht : t ≠ 0) :
    Tendsto
      (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω)
      (𝓝[<] t)
      (𝓝 (SIntegrableFiniteVariationBridge.cumulativeVariation H t ω -
        |processLeftJump H.finiteVariationPart t ω|)) := by
  let A : ℝ≥0 → ℝ := fun s => H.finiteVariationPart s ω
  let V : ℝ≥0 → ℝ := variationOnFromTo A Set.univ 0
  have hVEq :
      (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) =
        V := by
    funext s
    exact FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
      (H.finiteVariationPart_isBoundedVariation ω)
      (hRight ω) bot_le |>.symm
  have htpos : (0 : ℝ≥0) < t := (pos_iff_ne_zero).2 ht
  let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hLeft : Tendsto A (𝓝[<] t) (𝓝 (Function.leftLim A t)) := by
    simpa [A] using
      ((H.finiteVariationPart_isBoundedVariation ω).tendsto_leftLim t)
  have hV := variationOnFromTo.tendsto_left
    (f := A) (s := Set.univ) (l := Function.leftLim A t)
    (a := (0 : ℝ≥0)) (b := t)
    (Set.mem_univ 0) (Set.mem_univ t)
    (H.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
    (by simpa only [Set.univ_inter] using hLeft)
  rw [hVEq, congrFun hVEq t]
  simpa only [Set.univ_inter, V, A, processLeftJump, Real.dist_eq] using hV

omit [IsFiniteMeasure μ] in
/-- Every earlier cumulative-variation value is below the selected left
limit at `t`. -/
theorem cumulativeVariation_le_sub_abs_leftJump_of_lt
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) {s t : ℝ≥0} (hst : s < t) :
    SIntegrableFiniteVariationBridge.cumulativeVariation H s ω ≤
      SIntegrableFiniteVariationBridge.cumulativeVariation H t ω -
        |processLeftJump H.finiteVariationPart t ω| := by
  have htpos : (0 : ℝ≥0) < t := bot_le.trans_lt hst
  have ht : t ≠ 0 := ne_of_gt htpos
  let : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨0, (pos_iff_ne_zero).2 ht⟩
  apply ge_of_tendsto (tendsto_cumulativeVariation_left H hRight ω ht)
  filter_upwards [Ioo_mem_nhdsLT hst] with u hu
  have hmono := variationOnFromTo.monotoneOn
    (H.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
    (Set.mem_univ 0) (Set.mem_univ s) (Set.mem_univ u) hu.1.le
  rw [show SIntegrableFiniteVariationBridge.cumulativeVariation H s ω =
        variationOnFromTo (fun v => H.finiteVariationPart v ω) Set.univ 0 s from
      (FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
        (H.finiteVariationPart_isBoundedVariation ω) (hRight ω) bot_le).symm,
    show SIntegrableFiniteVariationBridge.cumulativeVariation H u ω =
        variationOnFromTo (fun v => H.finiteVariationPart v ω) Set.univ 0 u from
      (FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
        (H.finiteVariationPart_isBoundedVariation ω) (hRight ω) bot_le).symm]
  exact hmono

omit [IsFiniteMeasure μ] in
/-- The selected left limit of cumulative total variation is its current
value minus the absolute left jump of the finite-variation path. -/
theorem leftLim_cumulativeVariation_eq_sub_abs_leftJump
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) (t : ℝ≥0) :
    Function.leftLim
        (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) t =
      SIntegrableFiniteVariationBridge.cumulativeVariation H t ω -
        |processLeftJump H.finiteVariationPart t ω| := by
  by_cases ht : t = 0
  · subst t
    have hleftA : Function.leftLim
        (fun s => H.finiteVariationPart s ω) 0 =
          H.finiteVariationPart 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    have hleftV : Function.leftLim
        (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) 0 =
          SIntegrableFiniteVariationBridge.cumulativeVariation H 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    rw [hleftV]
    simp only [processLeftJump, hleftA, sub_self, abs_zero, sub_zero]
  · have htpos : (0 : ℝ≥0) < t := (pos_iff_ne_zero).2 ht
    let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    exact leftLim_eq_of_tendsto
      (tendsto_cumulativeVariation_left H hRight ω ht)

omit [IsFiniteMeasure μ] in
/-- Cumulative total variation has left limits on every sample path. -/
theorem cumulativeVariation_hasLeftLimits
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    ProcessHasLeftLimits
      (SIntegrableFiniteVariationBridge.cumulativeVariation H) := by
  intro ω t
  by_cases ht : t = 0
  · subst t
    have hbot : 𝓝[<] (0 : ℝ≥0) = ⊥ := by simp
    rw [hbot]
    exact tendsto_bot
  · rw [leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω t]
    exact tendsto_cumulativeVariation_left H hRight ω ht

omit [IsFiniteMeasure μ] in
/-- The left jump of cumulative total variation is the absolute left jump of
the finite-variation path. -/
theorem processLeftJump_cumulativeVariation_eq_abs
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (t : ℝ≥0) (ω : Ω) :
    processLeftJump
        (SIntegrableFiniteVariationBridge.cumulativeVariation H) t ω =
      |processLeftJump H.finiteVariationPart t ω| := by
  unfold processLeftJump
  rw [leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω t]
  simp only [processLeftJump]
  ring

omit [IsFiniteMeasure μ] in
/-- For a predictable finite-variation process, its cumulative total
variation is predictable.  Pathwise, it is the sum of its predictable left
limit and the absolute predictable jump. -/
theorem cumulativeVariation_isStronglyPredictable
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    IsStronglyPredictable ℱ
      (SIntegrableFiniteVariationBridge.cumulativeVariation H) := by
  let V := SIntegrableFiniteVariationBridge.cumulativeVariation H
  have hVLeft : IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim (V · ω) t) :=
    (cumulativeVariation_hasLeftLimits H hRight).stronglyPredictable_leftLim
      (SIntegrableFiniteVariationBridge.cumulativeVariation_stronglyAdapted
        H hRight)
  have hJump : IsStronglyPredictable ℱ
      (fun t ω => |processLeftJump H.finiteVariationPart t ω|) :=
    by
      unfold IsStronglyPredictable
      have h := H.processLeftJump_finiteVariationPart_isPredictable.norm
      simp only [Real.norm_eq_abs] at h
      convert h using 1
      funext p
      rcases p with ⟨t, ω⟩
      rfl
  change StronglyMeasurable[ℱ.predictable] (Function.uncurry V)
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry fun t ω => Function.leftLim (V · ω) t) at hVLeft
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry fun t ω => |processLeftJump H.finiteVariationPart t ω|) at hJump
  rw [show Function.uncurry V =
      Function.uncurry (fun t ω => Function.leftLim (V · ω) t) +
        Function.uncurry
          (fun t ω => |processLeftJump H.finiteVariationPart t ω|) by
    funext p
    rcases p with ⟨t, ω⟩
    change V t ω = Function.leftLim (V · ω) t +
      |processLeftJump H.finiteVariationPart t ω|
    rw [← processLeftJump_cumulativeVariation_eq_abs H hRight t ω]
    simp only [V, processLeftJump]
    ring]
  exact hVLeft.add hJump

/-- The predictable set on which cumulative total variation jumps strictly
across the `n`-th positive rational level. -/
noncomputable def jumpCrossingSet
    (H : SIntegrableStrategy D) (n : ℕ) : Set (ℝ≥0 × Ω) :=
  {p |
    Function.leftLim
        (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s p.2)
        p.1 < rationalLevel n ∧
      rationalLevel n <
        SIntegrableFiniteVariationBridge.cumulativeVariation H p.1 p.2}

omit [IsFiniteMeasure μ] in
/-- A rational jump-crossing set is predictable. -/
theorem measurableSet_jumpCrossingSet
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (n : ℕ) :
    MeasurableSet[ℱ.predictable] (jumpCrossingSet H n) := by
  have hV := cumulativeVariation_isStronglyPredictable H hRight
  have hVLeft : IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim
        (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) t) :=
    (cumulativeVariation_hasLeftLimits H hRight).stronglyPredictable_leftLim
      (SIntegrableFiniteVariationBridge.cumulativeVariation_stronglyAdapted
        H hRight)
  exact (hVLeft.measurableSet_lt stronglyMeasurable_const).inter
    (stronglyMeasurable_const.measurableSet_lt hV)

/-- The predictable rational crossing set restricted to a deterministic
horizon. -/
noncomputable def jumpCrossingSetUpTo
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) : Set (ℝ≥0 × Ω) :=
  jumpCrossingSet H n ∩ (Set.Iic T ×ˢ Set.univ)

omit [IsFiniteMeasure μ] in
/-- Restricting a rational jump-crossing set to a deterministic horizon
preserves predictability. -/
theorem measurableSet_jumpCrossingSetUpTo
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    MeasurableSet[ℱ.predictable] (jumpCrossingSetUpTo H T n) := by
  apply (measurableSet_jumpCrossingSet H hRight n).inter
  have htail : MeasurableSet[ℱ.predictable]
      (Set.Ioi T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  have hEq : (Set.Ioi T ×ˢ (Set.univ : Set Ω))ᶜ =
      Set.Iic T ×ˢ Set.univ := by
    ext p
    simp
  rw [← hEq]
  exact htail.compl

omit [IsFiniteMeasure μ] in
/-- Each rational jump-crossing set has at most one time in every sample
section. -/
theorem jumpCrossingSet_section_subsingleton
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (n : ℕ) (ω : Ω) :
    {t | (t, ω) ∈ jumpCrossingSet H n}.Subsingleton := by
  intro s hs t ht
  rcases lt_trichotomy s t with hst | hst | hst
  · have hle := cumulativeVariation_le_sub_abs_leftJump_of_lt
      H hRight ω hst
    rw [← leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω t] at hle
    have : rationalLevel n < rationalLevel n :=
      hs.2.trans_le hle |>.trans ht.1
    exact (lt_irrefl _ this).elim
  · exact hst
  · have hle := cumulativeVariation_le_sub_abs_leftJump_of_lt
      H hRight ω hst
    rw [← leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω s] at hle
    have : rationalLevel n < rationalLevel n :=
      ht.2.trans_le hle |>.trans hs.1
    exact (lt_irrefl _ this).elim

omit [IsFiniteMeasure μ] in
/-- A point of a rational jump-crossing set is exactly the strict passage of
that level. -/
theorem cumulativeVariationHittingAfter_eq_of_mem_jumpCrossingSet
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    {n : ℕ} {t : ℝ≥0} {ω : Ω} (ht : (t, ω) ∈ jumpCrossingSet H n) :
    SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter H
      (rationalLevel n) ω = t := by
  apply strictHittingAfter_eq_of_forall_lt_le
    (SIntegrableFiniteVariationBridge.cumulativeVariation H) ω
    (l := Function.leftLim
      (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) t)
  · intro s hst
    have hle := cumulativeVariation_le_sub_abs_leftJump_of_lt
      H hRight ω hst
    rwa [← leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω t] at hle
  · exact ht.1
  · exact ht.2

omit [IsFiniteMeasure μ] in
/-- A jump crossing before the horizon lies on the corresponding clamped
passage graph. -/
theorem passageGraph_eq_of_mem_jumpCrossingSetUpTo
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    {T : ℝ≥0} {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (ht : (t, ω) ∈ jumpCrossingSetUpTo H T n) :
    passageGraph H T n ω = t := by
  have hhit := cumulativeVariationHittingAfter_eq_of_mem_jumpCrossingSet
    H hRight ht.1
  unfold passageGraph
  rw [hhit, min_eq_left]
  · rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    exact WithTop.untop_coe t
  · exact_mod_cast ht.2.1

omit [IsFiniteMeasure μ] in
/-- The predictable jump-crossing sets cover every nonzero left jump of the
realized finite-variation component up to the horizon. -/
theorem coversLeftJumpsUpTo_jumpCrossingSetUpTo
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) :
    ∀ ω t, t ≤ T → processLeftJump H.finiteVariationPart t ω ≠ 0 →
      ∃ n, (t, ω) ∈ jumpCrossingSetUpTo H T n := by
  intro ω t htT hjump
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    have hleft : Function.leftLim
        (fun s => H.finiteVariationPart s ω) (0 : ℝ≥0) =
        H.finiteVariationPart 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    exact hjump (by simp [processLeftJump, hleft])
  let Vt := SIntegrableFiniteVariationBridge.cumulativeVariation H t ω
  let L := Vt - |processLeftJump H.finiteVariationPart t ω|
  have habs : 0 < |processLeftJump H.finiteVariationPart t ω| :=
    abs_pos.mpr hjump
  have hLV : L < Vt := by
    dsimp only [L]
    exact sub_lt_self Vt habs
  have hbefore : ∀ s, s < t →
      SIntegrableFiniteVariationBridge.cumulativeVariation H s ω ≤ L := by
    intro s hst
    exact cumulativeVariation_le_sub_abs_leftJump_of_lt
      H hRight ω hst
  have hLNonnegative : 0 ≤ L := by
    have hzero := hbefore 0 ((pos_iff_ne_zero).2 ht0)
    simpa [SIntegrableFiniteVariationBridge.cumulativeVariation] using hzero
  obtain ⟨q, hLq, hqV⟩ := exists_rat_btwn hLV
  have hqPositive : 0 < q := by
    exact_mod_cast hLNonnegative.trans_lt hLq
  obtain ⟨n, hn⟩ := exists_rationalLevel_eq q hqPositive
  refine ⟨n, ?_, htT, Set.mem_univ ω⟩
  change Function.leftLim
      (fun s => SIntegrableFiniteVariationBridge.cumulativeVariation H s ω) t <
        rationalLevel n ∧
    rationalLevel n <
      SIntegrableFiniteVariationBridge.cumulativeVariation H t ω
  rw [leftLim_cumulativeVariation_eq_sub_abs_leftJump H hRight ω t, hn]
  exact ⟨hLq, hqV⟩

omit [IsFiniteMeasure μ] in
/-- Every clamped rational passage graph is a finite stopping time. -/
theorem passageGraph_isStoppingTime
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (passageGraph H T n ω : WithTop ℝ≥0)) := by
  have hσ :=
    (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter_isStoppingTime
      H hRight (rationalLevel n)).min
      (isStoppingTime_const ℱ T)
  convert hσ using 1
  funext ω
  have hne : min
      (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter H
        (rationalLevel n) ω)
      (T : WithTop ℝ≥0) ≠ ⊤ := by
    exact ne_of_lt ((min_le_right _ _).trans_lt (WithTop.coe_lt_top T))
  rw [passageGraph, WithTop.untopA_eq_untop hne,
    WithTop.coe_untop _ hne]

/-- The event that the `n`-th rational level is crossed by a variation jump
before the deterministic horizon. -/
noncomputable def jumpCrossingEvent
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | (passageGraph H T n ω, ω) ∈ jumpCrossingSetUpTo H T n}

omit [IsFiniteMeasure μ] in
/-- The crossing event is exactly the projection of the corresponding thin
predictable set. -/
theorem mem_jumpCrossingEvent_iff
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    ω ∈ jumpCrossingEvent H T n ↔
      ∃ t, (t, ω) ∈ jumpCrossingSetUpTo H T n := by
  constructor
  · intro hω
    exact ⟨passageGraph H T n ω, hω⟩
  · rintro ⟨t, ht⟩
    change (passageGraph H T n ω, ω) ∈ jumpCrossingSetUpTo H T n
    rwa [passageGraph_eq_of_mem_jumpCrossingSetUpTo H hRight ht]

omit [IsFiniteMeasure μ] in
/-- The crossing event is measurable in the stopping-time σ-algebra of
the clamped passage. -/
theorem measurableSet_jumpCrossingEvent_stoppingTime
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    MeasurableSet[(passageGraph_isStoppingTime H hRight T n).measurableSpace]
      (jumpCrossingEvent H T n) := by
  let τ := passageGraph H T n
  have hτ := passageGraph_isStoppingTime H hRight T n
  have hpullback : MeasurableSet[predictableGraphMeasurableSpace ℱ τ]
      (jumpCrossingEvent H T n) := by
    apply MeasurableSpace.measurableSet_comap.2
    refine ⟨jumpCrossingSetUpTo H T n,
      measurableSet_jumpCrossingSetUpTo H hRight T n, ?_⟩
    rfl
  exact
    (IsStoppingTime.predictableGraphMeasurableSpace_le_measurableSpace hτ) _
      hpullback

omit [IsFiniteMeasure μ] in
/-- The event that a rational jump crossing occurs by `T` is known at `T`. -/
theorem measurableSet_jumpCrossingEvent
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    MeasurableSet[ℱ T] (jumpCrossingEvent H T n) := by
  let hτ := passageGraph_isStoppingTime H hRight T n
  have hle : ∀ ω, (passageGraph H T n ω : WithTop ℝ≥0) ≤
      (T : WithTop ℝ≥0) := by
    intro ω
    exact_mod_cast passageGraph_le H T n ω
  exact (hτ.measurableSpace_le_of_le_const hle) _
    (measurableSet_jumpCrossingEvent_stoppingTime H hRight T n)

/-- A predictable singleton graph at `t` may carry an event already known at
a strictly earlier deterministic time `s`. -/
theorem measurableSet_predictable_singleton_prod_of_lt
    {s t : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[ℱ.predictable] ({t} ×ˢ A) := by
  let a : ℕ → ℝ≥0 := fun r =>
    max s (LeftContinuousPredictable.approx r t)
  have ht0 : t ≠ 0 := ne_of_gt (bot_le.trans_lt hst)
  have ha_lt : ∀ r, a r < t := by
    intro r
    exact max_lt hst (LeftContinuousPredictable.approx_lt ht0 r)
  have heq : (⋂ r, Set.Ioc (a r) t ×ˢ A) = {t} ×ˢ A := by
    ext p
    constructor
    · intro hp
      have hp0 := Set.mem_iInter.mp hp 0
      have hpt : p.1 ≤ t := hp0.1.2
      have hpA : p.2 ∈ A := hp0.2
      have htp : t ≤ p.1 := by
        by_contra hnot
        have hptlt : p.1 < t := lt_of_not_ge hnot
        have heventually : ∀ᶠ r in Filter.atTop,
            p.1 < LeftContinuousPredictable.approx r t :=
          (LeftContinuousPredictable.tendsto_approx t).eventually
            (Ioi_mem_nhds hptlt)
        obtain ⟨r, hr⟩ := heventually.exists
        have hmember := Set.mem_iInter.mp hp r
        have hirrefl : LeftContinuousPredictable.approx r t <
            LeftContinuousPredictable.approx r t :=
          (le_max_right s (LeftContinuousPredictable.approx r t)).trans_lt
            (hmember.1.1.trans hr)
        exact (lt_irrefl _ hirrefl).elim
      exact ⟨le_antisymm hpt htp, hpA⟩
    · rintro ⟨rfl, hpA⟩
      apply Set.mem_iInter.2
      intro r
      exact ⟨⟨ha_lt r, le_rfl⟩, hpA⟩
  rw [← heq]
  apply MeasurableSet.iInter
  intro r
  apply measurableSet_predictable_Ioc_prod
  exact ℱ.mono (le_max_left s
    (LeftContinuousPredictable.approx r t)) _ hA

/-- The finite completion of a thin jump-crossing graph.  If no crossing
occurs, the time is moved to the deterministic dummy time `T + 1`. -/
noncomputable def jumpCrossingTime
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) : Ω → ℝ≥0 :=
  by
    classical
    exact fun ω => if ω ∈ jumpCrossingEvent H T n then
      passageGraph H T n ω else T + 1

omit [IsFiniteMeasure μ] in
/-- A completed jump-crossing time is no later than its dummy time. -/
theorem jumpCrossingTime_le
    (H : SIntegrableStrategy D) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    jumpCrossingTime H T n ω ≤ T + 1 := by
  classical
  unfold jumpCrossingTime
  split_ifs
  · exact (passageGraph_le H T n ω).trans (le_add_right le_rfl)
  · exact le_rfl

omit [IsFiniteMeasure μ] in
/-- Positive horizons make completed jump-crossing times strictly positive. -/
theorem jumpCrossingTime_pos
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (ω : Ω) :
    0 < jumpCrossingTime H T n ω := by
  classical
  unfold jumpCrossingTime
  split_ifs
  · exact passageGraph_pos H hRight hT n ω
  · exact add_pos_of_nonneg_of_pos bot_le zero_lt_one

omit [IsFiniteMeasure μ] in
/-- The finite completion of a jump-crossing graph is a stopping time. -/
theorem jumpCrossingTime_isStoppingTime
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (jumpCrossingTime H T n ω : WithTop ℝ≥0)) := by
  classical
  let τ := passageGraph H T n
  let B := jumpCrossingEvent H T n
  have hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) :=
    passageGraph_isStoppingTime H hRight T n
  have hB : MeasurableSet[hτ.measurableSpace] B :=
    measurableSet_jumpCrossingEvent_stoppingTime H hRight T n
  intro t
  by_cases hDummy : T + 1 ≤ t
  · have heq : {ω | (jumpCrossingTime H T n ω : WithTop ℝ≥0) ≤ t} =
        Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact_mod_cast (jumpCrossingTime_le H T n ω).trans hDummy
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {ω | (jumpCrossingTime H T n ω : WithTop ℝ≥0) ≤ t} =
        B ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      by_cases hω : ω ∈ B
      · simp [jumpCrossingTime, B, τ, hω]
      · change ((jumpCrossingTime H T n ω : ℝ≥0) : WithTop ℝ≥0) ≤ t ↔
          ω ∈ B ∧ (τ ω : WithTop ℝ≥0) ≤ t
        constructor
        · intro hle
          have hvalue : jumpCrossingTime H T n ω = T + 1 := by
            rw [jumpCrossingTime, ite_eq_right hω]
          rw [hvalue] at hle
          exact (hDummy (WithTop.coe_le_coe.mp hle)).elim
        · intro hright
          exact (hω hright.1).elim
    rw [heq]
    exact ((hτ.measurableSet B).1 hB).2 t

omit [IsFiniteMeasure μ] in
/-- The graph of the completed time is the genuine crossing graph together
with a predictable dummy graph on the no-crossing event. -/
theorem finiteStoppingTimeGraph_jumpCrossingTime
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    finiteStoppingTimeGraph (jumpCrossingTime H T n) =
      jumpCrossingSetUpTo H T n ∪
        ({T + 1} ×ˢ (jumpCrossingEvent H T n)ᶜ) := by
  classical
  ext p
  rcases p with ⟨t, ω⟩
  by_cases hω : ω ∈ jumpCrossingEvent H T n
  · have hmem : (passageGraph H T n ω, ω) ∈
        jumpCrossingSetUpTo H T n := hω
    have hsection := jumpCrossingSet_section_subsingleton H hRight n ω
    simp only [finiteStoppingTimeGraph, Set.mem_ofPred_eq,
      jumpCrossingTime, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_compl_iff, hω, not_true_eq_false,
      and_false, or_false]
    constructor
    · intro ht
      subst t
      exact hmem
    · intro ht
      have hfirst : t ∈ {s | (s, ω) ∈ jumpCrossingSet H n} := ht.1
      have hsecond : passageGraph H T n ω ∈
          {s | (s, ω) ∈ jumpCrossingSet H n} := hmem.1
      exact hsection hfirst hsecond
  · change t = jumpCrossingTime H T n ω ↔
        (t, ω) ∈ jumpCrossingSetUpTo H T n ∨
          (t = T + 1 ∧ ω ∈ (jumpCrossingEvent H T n)ᶜ)
    rw [jumpCrossingTime, ite_eq_right hω]
    constructor
    · intro ht
      exact Or.inr ⟨ht, hω⟩
    · rintro (ht | ht)
      · exact (hω ((mem_jumpCrossingEvent_iff H hRight T n ω).2
          ⟨t, ht⟩)).elim
      · exact ht.1

omit [IsFiniteMeasure μ] in
/-- Rational jump-crossing graphs provide genuinely predictable finite
stopping-time completions. -/
theorem jumpCrossingTime_isPredictableStoppingTime
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    IsPredictableStoppingTime ℱ (jumpCrossingTime H T n) := by
  refine ⟨jumpCrossingTime_isStoppingTime H hRight T n, ?_⟩
  rw [finiteStoppingTimeGraph_jumpCrossingTime H hRight T n]
  apply (measurableSet_jumpCrossingSetUpTo H hRight T n).union
  apply measurableSet_predictable_singleton_prod_of_lt
    (show T < T + 1 by exact lt_add_of_pos_right T zero_lt_one)
  exact (measurableSet_jumpCrossingEvent H hRight T n).compl

omit [IsFiniteMeasure μ] in
/-- The genuinely predictable crossing times still cover every nonzero left
jump up to the horizon. -/
theorem coversLeftJumpsUpTo_jumpCrossingTime
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (T : ℝ≥0) :
    CoversLeftJumpsUpTo H.finiteVariationPart T (jumpCrossingTime H T) := by
  classical
  intro ω t htT hjump
  obtain ⟨n, hn⟩ :=
    coversLeftJumpsUpTo_jumpCrossingSetUpTo H hRight T ω t htT hjump
  refine ⟨n, ?_⟩
  have hevent : ω ∈ jumpCrossingEvent H T n :=
    (mem_jumpCrossingEvent_iff H hRight T n ω).2 ⟨t, hn⟩
  have htime : jumpCrossingTime H T n ω = t := by
    rw [jumpCrossingTime, ite_eq_left hevent]
    exact passageGraph_eq_of_mem_jumpCrossingSetUpTo H hRight hn
  rw [htime]

end CumulativeVariationJumpEnumeration

/-!
## Announcements of cumulative-variation jump crossings

The completed rational jump-crossing times have predictable graphs.  For a
positive horizon they are also strictly positive, so the predictable-section
theorem supplies the ordinary announcements consumed by Lemma 4.7.
-/

namespace CumulativeVariationJumpEnumeration

variable
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Every completed positive-horizon jump-crossing graph has a strict
announcing sequence. -/
noncomputable def jumpCrossingTime_announcement
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    {T : ℝ≥0} (hT : 0 < T) (n : ℕ) :
    StoppingTimeAnnouncement ℱ (jumpCrossingTime H T n) :=
  PredictableGraphForetelling.IsPredictableStoppingTime.announcement
    hUsual (jumpCrossingTime_isPredictableStoppingTime H hRight T n)
      (jumpCrossingTime_pos H hRight hT n)

end CumulativeVariationJumpEnumeration

end FTAPTheorem42
