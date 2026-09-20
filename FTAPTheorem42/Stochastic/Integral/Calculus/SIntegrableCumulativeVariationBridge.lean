/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationBridge
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Foundations.RightContinuousHittingTime

/-!
# Canonical cumulative variation for a realized strategy

The finite-variation bridge uses the cumulative total-variation mass on
`(0,t]` as its variation process.  Factorial-grid approximation derives its
fixed-time measurability from right continuity and fixed-time measurability of
the finite-variation component.  Measure additivity then supplies every
`(a,b]` increment, so no separate measurability or endpoint decomposition
needs to be assumed.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

namespace SIntegrableFiniteVariationBridge

/-- Cumulative pathwise total variation on `(0,t]`. -/
noncomputable def cumulativeVariation
    (H : SIntegrableStrategy D) : ℝ≥0 → Ω → ℝ :=
  fun t ω =>
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        (Ioc 0 t)

omit [IsFiniteMeasure μ] in
/-- Strong predictability of the realized finite-variation component supplies
its fixed-time measurability. -/
theorem finiteVariationPart_measurable
    (H : SIntegrableStrategy D) (t : ℝ≥0) :
    Measurable (H.finiteVariationPart t) :=
  (H.finiteVariationPart_isPredictable.stronglyAdapted t).measurable.mono
    (ℱ.le t) le_rfl

omit [IsFiniteMeasure μ] in
/-- The cumulative variation process is adapted.  At horizon `t`, every
factorial-grid point lies before `t`, so predictability of the realized
finite-variation component supplies measurability in `ℱ t`. -/
theorem cumulativeVariation_stronglyAdapted
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    StronglyAdapted ℱ (cumulativeVariation H) := by
  intro t
  apply Measurable.stronglyMeasurable
  have hEq : cumulativeVariation H t =
      fun ω => variationOnFromTo
        (fun u => H.finiteVariationPart u ω) Set.univ 0 t := by
    funext ω
    exact (FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
      (H.finiteVariationPart_isBoundedVariation ω) (hRight ω) bot_le).symm
  rw [hEq]
  exact @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
    Ω ℝ (ℱ t) inferInstance inferInstance inferInstance inferInstance
    H.finiteVariationPart t
    (fun s hst =>
      (H.finiteVariationPart_isPredictable.stronglyAdapted
        |>.stronglyMeasurable_le hst).measurable)
    hRight

omit [IsFiniteMeasure μ] in
/-- Right continuity and fixed-time measurability of the finite-variation
component imply fixed-time measurability of its cumulative variation. -/
theorem measurable_cumulativeVariation
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (t : ℝ≥0) :
    Measurable (cumulativeVariation H t) := by
  exact (cumulativeVariation_stronglyAdapted H hRight t).measurable.mono
    (ℱ.le t) le_rfl

omit [IsFiniteMeasure μ] in
/-- The cumulative total variation is right-continuous. -/
theorem cumulativeVariation_rightContinuous
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => cumulativeVariation H u ω) (Set.Ici t) t := by
  have hEq : (fun u => cumulativeVariation H u ω) =
      variationOnFromTo (fun u => H.finiteVariationPart u ω) Set.univ 0 := by
    funext u
    exact FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
      (H.finiteVariationPart_isBoundedVariation ω) (hRight ω) bot_le |>.symm
  rw [hEq]
  exact (H.finiteVariationPart_isBoundedVariation ω
    |>.continuousWithinAt_variationOnFromTo_Ici (hRight ω t))

/-- First time at which the cumulative variation is strictly above `c`. -/
noncomputable def cumulativeVariationHittingAfter
    (H : SIntegrableStrategy D) (c : ℝ) : Ω → WithTop ℝ≥0 :=
  RightContinuousHittingTime.strictHittingAfter (cumulativeVariation H) c

omit [IsFiniteMeasure μ] in
/-- Under the usual right-continuity condition on the filtration, cumulative
variation can be localized at a stopping time. -/
theorem cumulativeVariationHittingAfter_isStoppingTime
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (c : ℝ) :
    IsStoppingTime ℱ (cumulativeVariationHittingAfter H c) := by
  exact RightContinuousHittingTime.strictHittingAfter_isStoppingTime
    (cumulativeVariation_stronglyAdapted H hRight)
    (cumulativeVariation_rightContinuous H hRight) c

omit [IsFiniteMeasure μ] in
/-- Strictly before the cumulative-variation passage time, variation has not
exceeded the localization level. -/
theorem cumulativeVariation_le_of_lt_hittingAfter
    (H : SIntegrableStrategy D) (c : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < cumulativeVariationHittingAfter H c ω) :
    cumulativeVariation H t ω ≤ c := by
  have hnot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := cumulativeVariation H) (s := Set.Ioi c) (n := (0 : ℝ≥0))
    (ω := ω) (k := t) ht bot_le
  exact le_of_not_gt hnot

omit [IsFiniteMeasure μ] in
/-- At a finite strict passage time, cumulative variation can overshoot the
localization level only by the left jump of the finite-variation path. -/
theorem cumulativeVariation_untopA_le_add_leftJump
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (c : ℝ) (hc : 0 ≤ c) (ω : Ω)
    (hτ : cumulativeVariationHittingAfter H c ω ≠ ⊤) :
    cumulativeVariation H
        ((cumulativeVariationHittingAfter H c ω).untopA) ω ≤
      c + |H.finiteVariationPart
          ((cumulativeVariationHittingAfter H c ω).untopA) ω -
        Function.leftLim (fun t => H.finiteVariationPart t ω)
          ((cumulativeVariationHittingAfter H c ω).untopA)| := by
  let τ := (cumulativeVariationHittingAfter H c ω).untopA
  let A : ℝ≥0 → ℝ := fun t => H.finiteVariationPart t ω
  change cumulativeVariation H τ ω ≤
    c + |A τ - Function.leftLim A τ|
  have hτcoe : (τ : WithTop ℝ≥0) =
      cumulativeVariationHittingAfter H c ω := by
    dsimp only [τ]
    rw [WithTop.untopA_eq_untop hτ]
    exact WithTop.coe_untop _ hτ
  by_cases hτ0 : τ = 0
  · have hleft : Function.leftLim A τ = A τ := by
      rw [hτ0]
      exact leftLim_eq_of_isBot isBot_bot
    have hzero : cumulativeVariation H τ ω = 0 := by
      rw [hτ0]
      simp [cumulativeVariation]
    rw [hzero, hleft, sub_self, abs_zero, add_zero]
    exact hc
  · have hτpos : (0 : ℝ≥0) < τ := (pos_iff_ne_zero).2 hτ0
    let V : ℝ≥0 → ℝ := variationOnFromTo A Set.univ 0
    have hVEq : (fun t => cumulativeVariation H t ω) = V := by
      funext t
      exact FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
        (H.finiteVariationPart_isBoundedVariation ω)
        (hRight ω) bot_le |>.symm
    let : NeBot (𝓝[<] τ) := nhdsLT_neBot_of_exists_lt ⟨0, hτpos⟩
    have hTendsto : Tendsto V (𝓝[<] τ)
        (𝓝 (V τ - dist (A τ) (Function.leftLim A τ))) := by
      have hLeft : Tendsto A (𝓝[<] τ)
          (𝓝 (Function.leftLim A τ)) := by
        simpa [A] using
          ((H.finiteVariationPart_isBoundedVariation ω).tendsto_leftLim τ)
      have h := variationOnFromTo.tendsto_left
        (f := A) (s := Set.univ) (l := Function.leftLim A τ)
        (a := (0 : ℝ≥0)) (b := τ)
        (Set.mem_univ 0) (Set.mem_univ τ)
        (H.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
        (by simpa only [Set.univ_inter] using hLeft)
      simpa only [Set.univ_inter] using h
    have hVle : V τ - dist (A τ) (Function.leftLim A τ) ≤ c := by
      apply le_of_tendsto hTendsto
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hVEq]
      apply cumulativeVariation_le_of_lt_hittingAfter H c ω t
      rw [← hτcoe]
      exact WithTop.coe_lt_coe.mpr ht
    rw [show cumulativeVariation H τ ω = V τ from congrFun hVEq τ]
    change V τ ≤ c + |A τ - Function.leftLim A τ|
    rw [← Real.dist_eq]
    linarith

omit [IsFiniteMeasure μ] in
/-- The Stieltjes total variation of a right-continuous path has no atom at
the initial time `0`. -/
theorem totalVariation_singleton_zero
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) :
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
        ({0} : Set ℝ≥0) = 0 := by
  let hA := H.finiteVariationPart_isBoundedVariation ω
  rw [signedMeasure_totalVariation_eq_variation,
    FiniteVariationPath.signedMeasure_eq_vectorMeasure]
  apply (VectorMeasure.variation_apply_eq_zero (MeasurableSet.singleton 0)).2
  intro s hs hMeas
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simp
  · have ht0 : t = 0 := hs ht
    have h0s : (0 : ℝ≥0) ∈ s := ht0 ▸ ht
    have hseq : s = ({0} : Set ℝ≥0) := by
      apply Set.Subset.antisymm hs
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      simpa [hx0] using h0s
    rw [hseq, hA.vectorMeasure_singleton]
    rw [(hRight ω 0).rightLim_eq]
    have hleft : Function.leftLim
        (fun t => H.finiteVariationPart t ω) (0 : ℝ≥0) =
        H.finiteVariationPart 0 ω :=
      leftLim_eq_of_isBot isBot_bot
    rw [hleft, sub_self]

omit [IsFiniteMeasure μ] in
/-- Cumulative variation along the natural-number horizons converges to the
total variation of the whole nonnegative time axis. -/
theorem tendsto_cumulativeVariation_natCast_atTop
    (H : SIntegrableStrategy D)
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t)
    (ω : Ω) :
    Tendsto (fun n : ℕ => cumulativeVariation H n ω) atTop
      (𝓝 ((FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ)) := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    constructor
    change (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ < ∞
    rw [SignedMeasure.totalVariation, Measure.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ≥0) (n : ℝ≥0)) := by
    intro m n hmn
    exact Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ≥0) (n : ℝ≥0)) = Ioi 0 := by
    rw [iUnion_Ioc_eq_Ioi_self_iff]
    intro x hx
    exact ⟨⌈(x : ℝ)⌉₊, by exact_mod_cast Nat.le_ceil x⟩
  have hlim : Tendsto (fun n : ℕ => ν (Ioc 0 (n : ℝ≥0))) atTop
      (𝓝 (ν (Ioi 0))) := by
    simpa [Function.comp_def, hunion] using
      (tendsto_measure_iUnion_atTop (μ := ν) hmono)
  have hdisjoint : Disjoint ({0} : Set ℝ≥0) (Ioi 0) := by
    apply Set.disjoint_left.2
    intro x hx0 hxpos
    have hx : x = 0 := by simpa using hx0
    subst x
    change (0 : ℝ≥0) < 0 at hxpos
    exact (lt_irrefl 0) hxpos
  have huniv : ({0} : Set ℝ≥0) ∪ Ioi 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, mem_Ioi, mem_univ,
      iff_true]
    rcases (bot_le : (0 : ℝ≥0) ≤ x).eq_or_lt with hx | hx
    · exact Or.inl hx.symm
    · exact Or.inr hx
  have hνuniv : ν (Ioi 0) = ν Set.univ := by
    rw [← huniv, measure_union hdisjoint measurableSet_Ioi,
      totalVariation_singleton_zero H hRight ω, zero_add]
  rw [hνuniv] at hlim
  change Tendsto (fun n : ℕ => (ν (Ioc 0 (n : ℝ≥0))).toReal) atTop
    (𝓝 (ν Set.univ).toReal)
  exact (ENNReal.tendsto_toReal (measure_ne_top ν Set.univ)).comp hlim

omit [IsFiniteMeasure μ] in
/-- Measurability of the cumulative variation at finite times supplies
measurability of the total variation on the whole nonnegative time axis. -/
theorem measurable_totalVariation_univ_of_cumulativeVariation
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ := by
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ => measurable_cumulativeVariation H hRight (n : ℝ≥0))
  rw [tendsto_pi_nhds]
  intro ω
  exact tendsto_cumulativeVariation_natCast_atTop H hRight ω

omit [IsFiniteMeasure μ] in
/- Total variation on `(a,b]` is the increment of cumulative variation. -/
theorem totalVariation_real_Ioc_eq_cumulativeVariation_sub
    (H : SIntegrableStrategy D) (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b) :
    (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          (Ioc a b) =
      cumulativeVariation H b ω - cumulativeVariation H a ω := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    constructor
    change (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ < ∞
    rw [SignedMeasure.totalVariation, Measure.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  have hdisjoint : Disjoint (Ioc (0 : ℝ≥0) a) (Ioc a b) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Ioc (0 : ℝ≥0) a ∪ Ioc a b = Ioc 0 b :=
    Ioc_union_Ioc_eq_Ioc bot_le hab
  have hadd : ν.real (Ioc 0 b) =
      ν.real (Ioc 0 a) + ν.real (Ioc a b) := by
    rw [← hunion, measureReal_union hdisjoint measurableSet_Ioc]
  change ν.real (Ioc a b) = ν.real (Ioc 0 b) - ν.real (Ioc 0 a)
  linarith

omit [IsFiniteMeasure μ] in
/-- A strictly positive sample density that makes both path variation and its
square integrable.  The square in the denominator is what supplies the
`L²` bound needed by finite-variation martingale rigidity. -/
noncomputable def normalizedVariationReferenceDensity
    (H : SIntegrableStrategy D) : Ω → ℝ≥0 := fun ω =>
  ⟨((1 + (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ) ^ 2)⁻¹,
    inv_nonneg.2 (sq_nonneg _)⟩

omit [IsFiniteMeasure μ] in
@[simp]
theorem coe_normalizedVariationReferenceDensity
    (H : SIntegrableStrategy D) (ω : Ω) :
    (normalizedVariationReferenceDensity H ω : ℝ) =
      ((1 + (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ) ^ 2)⁻¹ :=
  rfl

omit [IsFiniteMeasure μ] in
theorem normalizedVariationReferenceDensity_measurable
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    Measurable (normalizedVariationReferenceDensity H) := by
  apply Measurable.nnreal_mk
  exact ((measurable_const.add
    (measurable_totalVariation_univ_of_cumulativeVariation hRight)).pow_const 2).inv

omit [IsFiniteMeasure μ] in
theorem normalizedVariationReferenceDensity_pos
    (H : SIntegrableStrategy D) (ω : Ω) :
    0 < normalizedVariationReferenceDensity H ω := by
  change 0 < (((1 + (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
      Set.univ) ^ 2)⁻¹ : ℝ)
  positivity

omit [IsFiniteMeasure μ] in
theorem normalizedVariationReferenceDensity_le_one
    (H : SIntegrableStrategy D) (ω : Ω) :
    normalizedVariationReferenceDensity H ω ≤ 1 := by
  change (((1 + (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
      Set.univ) ^ 2)⁻¹ : ℝ) ≤ 1
  apply inv_le_one_of_one_le₀
  have hnonneg : 0 ≤ (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ := measureReal_nonneg
  nlinarith [sq_nonneg ((FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
      Set.univ)]

omit [IsFiniteMeasure μ] in
theorem normalizedVariationReferenceDensity_mul_variation_le_one
    (H : SIntegrableStrategy D) (ω : Ω) :
    (normalizedVariationReferenceDensity H ω : ℝ≥0∞) *
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
            Set.univ ≤ 1 := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top ν Set.univ))
    ENNReal.one_ne_top).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_one]
  change (((1 + ν.real Set.univ) ^ 2)⁻¹ : ℝ) *
    ν.real Set.univ ≤ 1
  rw [mul_comm]
  apply mul_inv_le_one_of_le₀
  · have hnonneg : 0 ≤ ν.real Set.univ := measureReal_nonneg
    nlinarith [sq_nonneg (ν.real Set.univ)]
  · positivity

/-- The total path variation belongs to `L²` under the normalized
equivalent reference measure. -/
theorem totalVariation_memLp_two_normalizedReferenceMeasure
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    MemLp (fun ω =>
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ) (2 : ℝ≥0∞)
      (μ.withDensity fun ω =>
        (normalizedVariationReferenceDensity H ω : ℝ≥0∞)) := by
  let V : Ω → ℝ := fun ω =>
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ
  have hVMeas : Measurable V :=
    measurable_totalVariation_univ_of_cumulativeVariation hRight
  have hDensityMeas := normalizedVariationReferenceDensity_measurable hRight
  apply (memLp_two_iff_integrable_sq hVMeas.aestronglyMeasurable).2
  rw [integrable_withDensity_iff_integrable_smul hDensityMeas]
  apply (integrable_const (1 : ℝ)).mono'
    (hDensityMeas.coe_nnreal_real.mul (hVMeas.pow_const 2)
      |>.aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  change |((normalizedVariationReferenceDensity H ω : ℝ) *
    V ω ^ 2)| ≤ 1
  rw [abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _)),
    coe_normalizedVariationReferenceDensity]
  rw [mul_comm]
  apply mul_inv_le_one_of_le₀
  · have hnonneg : 0 ≤ V ω := measureReal_nonneg
    nlinarith [sq_nonneg (V ω)]
  · positivity

/-- Build a finite-variation bridge for an arbitrary realized
finite-variation component.  A strictly positive density replaces the
unavailable deterministic pathwise variation bound. -/
noncomputable def ofCumulativeVariationNormalized
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t) :
    SIntegrableFiniteVariationBridge H where
  rightContinuous := hRight
  fixedTimeMeasurable := finiteVariationPart_measurable H
  variationProcess := cumulativeVariation H
  variationProcess_measurable := measurable_cumulativeVariation H hRight
  variation_Ioc := totalVariation_real_Ioc_eq_cumulativeVariation_sub H
  variationTerminal := fun ω =>
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real Set.univ
  variationInitial := fun _ => 0
  variationTerminal_measurable :=
    measurable_totalVariation_univ_of_cumulativeVariation hRight
  variationInitial_measurable := measurable_const
  referenceDensity := normalizedVariationReferenceDensity H
  referenceDensity_measurable :=
    normalizedVariationReferenceDensity_measurable hRight
  referenceDensity_pos := normalizedVariationReferenceDensity_pos H
  referenceDensity_le_one := normalizedVariationReferenceDensity_le_one H
  bound := 1
  bound_lt_top := by simp
  variation_univ := by simp
  weightedVariationBound := by
    simpa using normalizedVariationReferenceDensity_mul_variation_le_one H
  variationMemLpTwo :=
    totalVariation_memLp_two_normalizedReferenceMeasure hRight

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
