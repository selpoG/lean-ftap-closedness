/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph

/-!
# Predictability of stopped processes

The predictable σ-algebra is stable under stopping.  We record the small
measurability bridge needed by the finite-variation localization argument:
if `X` is strongly predictable and `τ` is a finite stopping time, then the
usual stopped process `X^τ` is strongly predictable.  The proof works on the
generators of the predictable σ-algebra; it does not infer predictability from
adaptedness or càdlàg regularity.
-/

open MeasureTheory Set
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace IsStronglyPredictable

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! The stopped process is indexed by finite times, so even an infinite-valued
stopping time is sampled through a finite `min`. -/

/-- A strongly predictable process remains strongly predictable after a
`WithTop`-valued stopping time. -/
theorem stoppedProcess_of_stoppingTime_withTop
    {X : Process Ω} (hX : IsStronglyPredictable ℱ X)
    (ρ : Ω → WithTop ℝ≥0)
    (hρ : IsStoppingTime ℱ ρ) :
    IsStronglyPredictable ℱ
      (MeasureTheory.stoppedProcess X ρ) := by
  have hClamp :
      @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) ℱ.predictable ℱ.predictable
        (fun p =>
          ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) := by
    refine @measurable_generateFrom (ℝ≥0 × Ω) (ℝ≥0 × Ω)
      ℱ.predictable _ (fun p =>
        ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) ?_
    rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
    · change MeasurableSet[ℱ.predictable]
        ((fun p : ℝ≥0 × Ω =>
          ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) ⁻¹'
          ({(0 : ℝ≥0)} ×ˢ A))
      have hρ0 : MeasurableSet[ℱ 0]
          {ω | ρ ω = (0 : WithTop ℝ≥0)} := by
        exact hρ.measurableSet_eq 0
      rw [show (fun p : ℝ≥0 × Ω =>
          ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) ⁻¹'
          ({(0 : ℝ≥0)} ×ˢ A) =
          ({(0 : ℝ≥0)} ×ˢ A) ∪
            (Set.Ioi (0 : ℝ≥0) ×ˢ
              ({ω | ρ ω = (0 : WithTop ℝ≥0)} ∩ A)) by
        ext p
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
          Set.mem_union, Set.mem_Ioi, Set.mem_inter_iff]
        have hmin_ne_top :
            min (p.1 : WithTop ℝ≥0) (ρ p.2) ≠ ⊤ :=
          ne_top_of_le_ne_top (WithTop.coe_ne_top) (min_le_left _ _)
        have hcoe :
            (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                WithTop ℝ≥0) = min (p.1 : WithTop ℝ≥0) (ρ p.2) := by
          rw [WithTop.untopA_eq_untop hmin_ne_top]
          exact WithTop.coe_untop _ hmin_ne_top
        constructor
        · intro hp
          by_cases hp0 : p.1 = 0
          · exact Or.inl ⟨hp0, hp.2⟩
          · right
            have hpgt : 0 < p.1 := lt_of_le_of_ne bot_le (Ne.symm hp0)
            have hmin : min (p.1 : WithTop ℝ≥0) (ρ p.2) = 0 := by
              calc
                min (p.1 : WithTop ℝ≥0) (ρ p.2) =
                    (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                      WithTop ℝ≥0) := hcoe.symm
                _ = 0 := by
                  rw [hp.1]
                  exact WithTop.coe_zero
            have hρzero : ρ p.2 = 0 := by
              exact (min_eq_zero.mp hmin).resolve_left
                (by intro hpzero
                    exact hp0 (WithTop.coe_eq_coe.mp hpzero))
            exact ⟨hpgt, hρzero, hp.2⟩
        · intro hp
          rcases hp with hp | hp
          · have hc :
                (min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA = 0 := by
              have hc_coe :
                  (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                      WithTop ℝ≥0) = 0 := by
                rw [hcoe, hp.1]
                rw [WithTop.coe_zero]
                exact min_eq_left bot_le
              exact WithTop.coe_eq_coe.mp hc_coe
            exact ⟨hc, hp.2⟩
          · have hc :
                (min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA = 0 := by
              have hc_coe :
                  (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                      WithTop ℝ≥0) = 0 := by
                rw [hcoe, hp.2.1]
                exact min_eq_right bot_le
              exact WithTop.coe_eq_coe.mp hc_coe
            exact ⟨hc, hp.2.2⟩]
      exact (measurableSet_predictable_singleton_bot_prod hA).union
        (measurableSet_predictable_Ioi_prod (hρ0.inter hA))
    · have hρi : MeasurableSet[ℱ i] {ω | (i : WithTop ℝ≥0) < ρ ω} :=
        hρ.measurableSet_gt i
      rw [show (fun p : ℝ≥0 × Ω =>
          ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) ⁻¹'
          (Set.Ioi i ×ˢ A) =
          Set.Ioi i ×ˢ ({ω | (i : WithTop ℝ≥0) < ρ ω} ∩ A) by
        ext p
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi,
          Set.mem_inter_iff]
        have hmin_ne_top :
            min (p.1 : WithTop ℝ≥0) (ρ p.2) ≠ ⊤ :=
          ne_top_of_le_ne_top (WithTop.coe_ne_top) (min_le_left _ _)
        have hcoe :
            (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                WithTop ℝ≥0) = min (p.1 : WithTop ℝ≥0) (ρ p.2) := by
          rw [WithTop.untopA_eq_untop hmin_ne_top]
          exact WithTop.coe_untop _ hmin_ne_top
        constructor
        · rintro ⟨hp, hpA⟩
          have hmin : (i : WithTop ℝ≥0) <
              min (p.1 : WithTop ℝ≥0) (ρ p.2) := by
            calc
              (i : WithTop ℝ≥0) <
                  (((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA : ℝ≥0) :
                    WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hp
              _ = min (p.1 : WithTop ℝ≥0) (ρ p.2) := hcoe
          exact ⟨WithTop.coe_lt_coe.mp (lt_min_iff.mp hmin).1,
            (lt_min_iff.mp hmin).2, hpA⟩
        · rintro ⟨hp, hρp, hpA⟩
          have hmin : (i : WithTop ℝ≥0) <
              min (p.1 : WithTop ℝ≥0) (ρ p.2) :=
            lt_min (WithTop.coe_lt_coe.mpr hp) hρp
          have hc : i <
              (min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA := by
            apply WithTop.coe_lt_coe.mp
            exact hmin.trans_eq hcoe.symm
          exact ⟨hc, hpA⟩]
      exact measurableSet_predictable_Ioi_prod (hρi.inter hA)
  change StronglyMeasurable[ℱ.predictable]
    (fun p : ℝ≥0 × Ω =>
      X (min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA p.2)
  have hcomp :=
    @StronglyMeasurable.comp_measurable
      (ℝ≥0 × Ω) ℝ (ℝ≥0 × Ω) _ ℱ.predictable ℱ.predictable
      (Function.uncurry X)
      (fun p =>
        ((min (p.1 : WithTop ℝ≥0) (ρ p.2)).untopA, p.2)) hX hClamp
  exact hcomp

/-- A strongly predictable process remains strongly predictable after a finite
stopping time. -/
theorem stoppedProcess_of_stoppingTime
    {X : Process Ω} (hX : IsStronglyPredictable ℱ X)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    IsStronglyPredictable ℱ
      (MeasureTheory.stoppedProcess X (fun ω => (τ ω : WithTop ℝ≥0))) := by
  exact stoppedProcess_of_stoppingTime_withTop hX
    (fun ω => (τ ω : WithTop ℝ≥0)) hτ

end IsStronglyPredictable

end FTAPTheorem42
