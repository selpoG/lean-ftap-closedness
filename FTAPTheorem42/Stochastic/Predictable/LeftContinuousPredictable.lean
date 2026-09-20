/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Process.Predictable
import Mathlib.Analysis.SpecificLimits.Basic
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Left-continuous adapted processes are predictable

The proof rounds time strictly to the left on factorial grids.  Each rounded
process is constant on predictable intervals `(k/r!, (k+1)/r!]`, and the
left-continuity assumption identifies its pointwise limit.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace LeftContinuousPredictable

/-- The positive factorial mesh denominator used at level `r`. -/
def denominator (r : ℕ) : ℕ := (r + 1).factorial

/-- A deterministic point on the level-`r` factorial grid. -/
noncomputable def gridPoint (r k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (denominator r : ℝ≥0)

/-- Index of the grid point immediately to the left of `t`, with zero kept
at zero. -/
noncomputable def leftIndex (r : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.ceil (t * (denominator r : ℝ≥0)) - 1

/-- Factorial-grid approximation from the left. -/
noncomputable def approx (r : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  gridPoint r (leftIndex r t)

theorem approx_eq_gridPoint_of_mem_Ioc
    {r k : ℕ} {t : ℝ≥0}
    (ht : t ∈ Set.Ioc (gridPoint r k) (gridPoint r (k + 1))) :
    approx r t = gridPoint r k := by
  have hd : (0 : ℝ≥0) < (denominator r : ℝ≥0) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  have hlower : (k : ℝ≥0) < t * (denominator r : ℝ≥0) := by
    exact (div_lt_iff₀ hd).mp ht.1
  have hupper : t * (denominator r : ℝ≥0) ≤ (k + 1 : ℕ) := by
    exact_mod_cast (le_div_iff₀ hd).mp ht.2
  have hceil : Nat.ceil (t * (denominator r : ℝ≥0)) = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
    constructor
    · simpa only [Nat.succ_sub_one, Nat.cast_id] using hlower
    · exact_mod_cast hupper
  simp only [approx, leftIndex, hceil, Nat.add_sub_cancel]

theorem exists_mem_Ioc_gridPoint {t : ℝ≥0} (ht : t ≠ 0) (r : ℕ) :
    ∃ k, t ∈ Set.Ioc (gridPoint r k) (gridPoint r (k + 1)) := by
  let c := Nat.ceil (t * (denominator r : ℝ≥0))
  let k := c - 1
  have hd : (0 : ℝ≥0) < (denominator r : ℝ≥0) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  have htc : 0 < t * (denominator r : ℝ≥0) :=
    mul_pos (pos_iff_ne_zero.mpr ht) hd
  have hcpos : 0 < c := Nat.ceil_pos.mpr htc
  have hkltc : k < c := Nat.sub_lt hcpos zero_lt_one
  have hlowerMul : (k : ℝ≥0) < t * (denominator r : ℝ≥0) :=
    (Nat.lt_ceil (α := ℝ≥0)).mp hkltc
  have hcEq : k + 1 = c := Nat.sub_add_cancel hcpos
  have hupperMul : t * (denominator r : ℝ≥0) ≤ (c : ℕ) :=
    Nat.le_ceil _
  refine ⟨k, ?_, ?_⟩
  · exact (div_lt_iff₀ hd).2 hlowerMul
  · rw [gridPoint, hcEq]
    exact (le_div_iff₀ hd).2 (by exact_mod_cast hupperMul)

theorem approx_le (r : ℕ) (t : ℝ≥0) : approx r t ≤ t := by
  by_cases ht : t = 0
  · subst t
    simp [approx, leftIndex, gridPoint]
  · obtain ⟨k, hk⟩ := exists_mem_Ioc_gridPoint ht r
    rw [approx_eq_gridPoint_of_mem_Ioc hk]
    exact hk.1.le

theorem approx_lt {t : ℝ≥0} (ht : t ≠ 0) (r : ℕ) : approx r t < t := by
  obtain ⟨k, hk⟩ := exists_mem_Ioc_gridPoint ht r
  rw [approx_eq_gridPoint_of_mem_Ioc hk]
  exact hk.1

theorem le_approx_add_inv (r : ℕ) (t : ℝ≥0) :
    t ≤ approx r t + (denominator r : ℝ≥0)⁻¹ := by
  by_cases ht : t = 0
  · subst t
    exact bot_le
  · obtain ⟨k, hk⟩ := exists_mem_Ioc_gridPoint ht r
    rw [approx_eq_gridPoint_of_mem_Ioc hk]
    calc
      t ≤ gridPoint r (k + 1) := hk.2
      _ = gridPoint r k + (denominator r : ℝ≥0)⁻¹ := by
        simp only [gridPoint, Nat.cast_add, Nat.cast_one, add_div]
        rw [one_div]

theorem tendsto_approx (t : ℝ≥0) :
    Tendsto (fun r => approx r t) atTop (𝓝 t) := by
  have hdenom : Tendsto (fun r : ℕ => (denominator r : ℝ≥0))
      atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    have hadd : Tendsto (fun r : ℕ => r + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro n
      filter_upwards [eventually_ge_atTop n] with r hr
      exact hr.trans (Nat.le_succ r)
    change Tendsto (fun r : ℕ => (r + 1).factorial) atTop atTop
    exact factorial_tendsto_atTop.comp hadd
  have hinv : Tendsto (fun r : ℕ => (denominator r : ℝ≥0)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hdenom
  have hlower : Tendsto
      (fun r : ℕ => t - (denominator r : ℝ≥0)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun r =>
      tsub_le_iff_right.mpr (le_approx_add_inv r t)
  · exact Filter.Eventually.of_forall fun r => approx_le r t

/-- The predictable left-grid step approximation to a process. -/
noncomputable def step (r : ℕ) (X : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => X (approx r t) ω

omit [MeasurableSpace Ω] in
theorem step_eq_of_mem_Ioc
    (X : ℝ≥0 → Ω → ℝ) {r k : ℕ} {t : ℝ≥0}
    (ht : t ∈ Set.Ioc (gridPoint r k) (gridPoint r (k + 1))) :
    step r X t = X (gridPoint r k) := by
  funext ω
  rw [step, approx_eq_gridPoint_of_mem_Ioc ht]

/-- Every left-grid step approximation of an adapted process is predictable. -/
theorem stronglyPredictable_step
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X) (r : ℕ) :
    IsStronglyPredictable ℱ (step r X) := by
  apply Measurable.stronglyMeasurable
  intro s hs
  have hpre : Function.uncurry (step r X) ⁻¹' s =
      ({0} : Set ℝ≥0) ×ˢ (X 0 ⁻¹' s) ∪
        ⋃ k : ℕ, Set.Ioc (gridPoint r k) (gridPoint r (k + 1)) ×ˢ
          (X (gridPoint r k) ⁻¹' s) := by
    ext p
    rcases p with ⟨t, ω⟩
    simp only [Function.uncurry_apply_pair, Set.mem_preimage, Set.mem_union,
      Set.mem_prod, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hvalue
      by_cases ht : t = 0
      · left
        subst t
        simpa [step, approx, leftIndex, gridPoint] using hvalue
      · right
        obtain ⟨k, hk⟩ := exists_mem_Ioc_gridPoint ht r
        exact ⟨k, hk, by simpa only [step_eq_of_mem_Ioc X hk] using hvalue⟩
    · rintro (⟨rfl, hvalue⟩ | ⟨k, hk, hvalue⟩)
      · simpa [step, approx, leftIndex, gridPoint] using hvalue
      · simpa only [step_eq_of_mem_Ioc X hk] using hvalue
  rw [hpre]
  apply MeasurableSet.union
  · apply measurableSet_predictable_singleton_bot_prod
    exact (hX 0).measurable hs
  · apply MeasurableSet.iUnion
    intro k
    apply measurableSet_predictable_Ioc_prod
    exact (hX (gridPoint r k)).measurable hs

/-- A strongly adapted process with left-continuous sample paths is strongly
predictable. -/
theorem stronglyPredictable_of_leftContinuous
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    (hleft : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Iic t) t) :
    IsStronglyPredictable ℱ X := by
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun r => Function.uncurry (step r X))
    (g := Function.uncurry X) ?_ ?_
  · exact fun r => stronglyPredictable_step hX r
  · rw [tendsto_pi_nhds]
    rintro ⟨t, ω⟩
    apply (hleft ω t).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_approx t,
      Filter.Eventually.of_forall fun r => approx_le r t⟩

end LeftContinuousPredictable

/-- The left-limit process of an adapted process with left limits is
predictable. -/
theorem ProcessHasLeftLimits.stronglyPredictable_leftLim
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hXLeft : ProcessHasLeftLimits X)
    (hXAdapted : StronglyAdapted ℱ X) :
    IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim (X · ω) t) := by
  have hAdaptedLeft : StronglyAdapted ℱ
      (fun t ω => Function.leftLim (X · ω) t) := by
    intro t
    by_cases ht : t = 0
    · subst t
      convert hXAdapted 0 using 1
      funext ω
      exact leftLim_eq_of_isBot isBot_bot
    · refine stronglyMeasurable_of_tendsto atTop
        (f := fun r ω => X (LeftContinuousPredictable.approx r t) ω)
        (g := fun ω => Function.leftLim (X · ω) t) ?_ ?_
      · intro r
        exact (hXAdapted (LeftContinuousPredictable.approx r t)).mono
          (ℱ.mono (LeftContinuousPredictable.approx_le r t))
      · rw [tendsto_pi_nhds]
        intro ω
        apply (hXLeft ω t).comp
        apply tendsto_nhdsWithin_iff.mpr
        exact ⟨LeftContinuousPredictable.tendsto_approx t,
          Filter.Eventually.of_forall fun r =>
            LeftContinuousPredictable.approx_lt ht r⟩
  apply LeftContinuousPredictable.stronglyPredictable_of_leftContinuous
    hAdaptedLeft
  intro ω t
  exact continuousWithinAt_leftLim_Iic (hXLeft ω t)

/-- The left-jump process of the predictable finite-variation component is
predictable; no separate jump-predictability input is needed. -/
theorem SIntegrableStrategy.processLeftJump_finiteVariationPart_isPredictable
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D) :
    IsStronglyPredictable ℱ (processLeftJump H.finiteVariationPart) := by
  have hleftPredictable : IsStronglyPredictable ℱ
      (fun t ω => Function.leftLim (H.finiteVariationPart · ω) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim
      H.finiteVariationPart_hasLeftLimits
      H.finiteVariationPart_isPredictable.stronglyAdapted
  exact H.finiteVariationPart_isPredictable.sub hleftPredictable

end FTAPTheorem42
