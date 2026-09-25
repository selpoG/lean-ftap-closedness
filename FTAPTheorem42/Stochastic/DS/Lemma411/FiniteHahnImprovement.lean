/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.DownsideStopping
import FTAPTheorem42.Foundations.HahnStopping

/-! # Finite-horizon Hahn improvements

The selected input jump controls the closed downside stop. On survival,
the baseline resumes after the control horizon, preserving the lower bound
and retaining the Hahn bonus at a later finite terminal horizon. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*}

/-- A bound before a finite stop extends across its jump when the stopped
gain inherits the jump of one of the two admissible input gains. This is a
pathwise statement, independent of a source or a stopping calculus. -/
theorem finiteStopped_lower_bound_of_selectedJump
    {X Y R : Process Ω} (τ : Ω → NNReal) {a δ : Real}
    (hX : ProcessHasLeftLimits X) (hY : ProcessHasLeftLimits Y)
    (hR : ProcessHasLeftLimits R) (ω : Ω)
    (hXLower : ∀ t, -a ≤ X t ω) (hYLower : ∀ t, -a ≤ Y t ω)
    (hRZero : -(a + δ) ≤ R 0 ω)
    (hBefore : ∀ t, t < τ ω → max (X t ω) (Y t ω) - δ ≤ R t ω)
    (hJump : processLeftJump R (τ ω) ω = processLeftJump X (τ ω) ω ∨
      processLeftJump R (τ ω) ω = processLeftJump Y (τ ω) ω) :
    ∀ t, -(a + δ) ≤ R (min t (τ ω)) ω := by
  intro t
  rcases (min_le_right t (τ ω)).eq_or_lt with heq | hlt
  · rw [heq]
    by_cases hz : τ ω = 0
    · simpa only [hz] using hRZero
    have hpos : 0 < τ ω := (pos_iff_ne_zero).2 hz
    let : NeBot (𝓝[<] τ ω) := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    have hLeft : -δ ≤ Function.leftLim (R · ω) (τ ω) -
        max (Function.leftLim (X · ω) (τ ω)) (Function.leftLim (Y · ω) (τ ω)) := by
      apply ge_of_tendsto ((hR ω (τ ω)).sub ((hX ω (τ ω)).max (hY ω (τ ω))))
      filter_upwards [self_mem_nhdsWithin] with s hs
      have := hBefore s hs
      linarith
    rcases hJump with hj | hj
    · unfold processLeftJump at hj
      have := le_max_left (Function.leftLim (X · ω) (τ ω))
        (Function.leftLim (Y · ω) (τ ω))
      linarith [hXLower (τ ω)]
    · unfold processLeftJump at hj
      have := le_max_right (Function.leftLim (X · ω) (τ ω))
        (Function.leftLim (Y · ω) (τ ω))
      linarith [hYLower (τ ω)]
  · have := hBefore (min t (τ ω)) hlt
    have := le_max_left (X (min t (τ ω)) ω) (Y (min t (τ ω)) ω)
    linarith [hXLower (min t (τ ω))]

/-! ## Finite-horizon downside stopping of a Hahn improvement -/

/-- The finite downside time is a stopping time for adapted right-continuous
martingale components, without a source-specific calculus. -/
theorem finiteHahnDownsideTime_isStoppingTime
    [MeasurableSpace Ω] {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    [F.IsRightContinuous] {N M : Process Ω}
    (hN : StronglyAdapted F N) (hM : StronglyAdapted F M)
    (hNR : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t)
    (hMR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    (δ : Real) (T : NNReal) :
    IsStoppingTime F (fun ω => (finiteHahnDownsideTime N M δ T ω : WithTop NNReal)) := by
  apply RightContinuousStoppedMartingale.boundedTime_isStoppingTime
  apply lowerStrictHittingAfter_isStoppingTime
  · exact fun t => (hN t).sub (((hM t).measurable.max measurable_const).stronglyMeasurable)
  · exact fun ω t => (hNR ω t).sub ((hMR ω t).max continuousWithinAt_const)

/-- Positive variation increments and the selected-input jump identity
give the full closed-stop lower bound, including a jump at the horizon. -/
theorem finiteHahnBestOf_lower_bound
    {X Y MX MY AX AY V N C : Process Ω} (T : NNReal) {δ : Real} (hδ : 0 ≤ δ)
    (hXL : ProcessHasLeftLimits X) (hYL : ProcessHasLeftLimits Y)
    (hVL : ProcessHasLeftLimits V) (ω : Ω)
    (hXLower : ∀ t, (-1 : Real) ≤ X t ω) (hYLower : ∀ t, (-1 : Real) ≤ Y t ω)
    (hY0 : Y 0 ω = 0) (hV0 : V 0 ω = 0)
    (hX : ∀ t, X t ω = MX t ω + AX t ω)
    (hY : ∀ t, Y t ω = MY t ω + AY t ω)
    (hV : ∀ t, V t ω = N t ω + C t ω)
    (hFV : ∀ t, t ≤ T → 0 ≤ C t ω ∧ AX t ω - AY t ω ≤ C t ω)
    (hJump : ∀ t, t ≤ T → processLeftJump V t ω = processLeftJump (X - Y) t ω ∨
      processLeftJump V t ω = 0) :
    ∀ t, -(1 + δ) ≤ (Y + V) (min t (finiteHahnDownsideTime N (MX - MY) δ T ω)) ω := by
  let τ := finiteHahnDownsideTime N (MX - MY) δ T
  have hτT : τ ω ≤ T := RightContinuousStoppedMartingale.boundedTime_le _ _ _
  apply finiteStopped_lower_bound_of_selectedJump τ hXL hYL (hYL.add hVL) ω
    hXLower hYLower
  · rw [hY0, hV0]
    linarith
  · intro t ht
    have hBefore : (t : WithTop NNReal) <
        lowerStrictHittingAfter (hahnMartingaleAdvantage N (MX - MY)) δ ω := by
      have h := WithTop.coe_lt_coe.mpr ht
      rw [show τ = finiteHahnDownsideTime N (MX - MY) δ T from rfl,
        finiteHahnDownsideTime, RightContinuousStoppedMartingale.coe_boundedTime] at h
      exact lt_of_lt_of_le h (min_le_right _ _)
    have hm := neg_le_of_lt_lowerStrictHittingAfter
      (hahnMartingaleAdvantage N (MX - MY)) δ ω t hBefore
    have hf := hFV t (ht.le.trans hτT)
    change -δ ≤ N t ω - max (MX t ω - MY t ω) 0 at hm
    change max (X t ω) (Y t ω) - δ ≤ Y t ω + V t ω
    rw [← max_sub_sub_right]
    apply max_le
    · have := le_max_left (MX t ω - MY t ω) 0
      rw [hX t, hY t, hV t]
      linarith
    · have := le_max_right (MX t ω - MY t ω) 0
      rw [hV t]
      linarith
  · rw [processLeftJump_add hYL hVL]
    rcases hJump (τ ω) hτT with hj | hj
    · left
      rw [hj]
      change processLeftJump Y (τ ω) ω +
        processLeftJump (fun s x => X s x - Y s x) (τ ω) ω = _
      rw [processLeftJump_sub hXL hYL]
      ring
    · right
      rw [hj, add_zero]

/-- Resuming the admissible baseline keeps the same lower bound. -/
theorem finiteHahnPastedGain_lower_bound {Y V N M C : Process Ω}
    {T U : NNReal} (hTU : T ≤ U) {δ : Real} (ω : Ω)
    (hY : ∀ t, (-1 : Real) ≤ Y t ω)
    (hStop : ∀ t, -(1 + δ) ≤ (Y + V) (min t (finiteHahnDownsideTime N M δ T ω)) ω)
    (hV : V T ω = N T ω + C T ω) (hC : 0 ≤ C T ω) :
    ∀ t, -(1 + δ) ≤ finiteHahnPastedGain Y V N M δ T U t ω := by
  intro t
  unfold finiteHahnPastedGain
  by_cases he : (T : WithTop NNReal) < lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω
  · rw [ite_eq_left he]
    by_cases ht : t ≤ T
    · rw [min_eq_left (ht.trans hTU), min_eq_left ht, sub_self, add_zero]
      exact hStop t
    · have hTt := le_of_not_ge ht
      have hσ : finiteHahnDownsideTime N M δ T ω = T := by
        apply WithTop.coe_injective
        rw [finiteHahnDownsideTime, RightContinuousStoppedMartingale.coe_boundedTime,
          min_eq_left he.le]
      rw [hσ, min_eq_right hTt]
      have hn := neg_le_of_lt_lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω T he
      change -δ ≤ N T ω - max (M T ω) 0 at hn
      have := le_max_right (M T ω) 0
      change -(1 + δ) ≤ Y T ω + V T ω + (Y (min t U) ω - Y T ω)
      linarith [hY (min t U)]
  · rw [ite_eq_right he, add_zero]
    exact hStop t
/-- The pasted process is constant after its finite terminal horizon. -/
theorem finiteHahnPastedGain_eventually_constant (Y V N M : Process Ω)
    {T U : NNReal} (hTU : T ≤ U) (δ : Real) (ω : Ω) :
    ∀ t, U ≤ t → finiteHahnPastedGain Y V N M δ T U t ω =
      finiteHahnPastedGain Y V N M δ T U U ω := by
  intro t ht
  have hσ : finiteHahnDownsideTime N M δ T ω ≤ T :=
    RightContinuousStoppedMartingale.boundedTime_le _ _ _
  simp only [finiteHahnPastedGain, min_eq_right (hσ.trans (hTU.trans ht)),
    min_eq_right (hσ.trans hTU), min_eq_right ht, min_self,
    min_eq_right (hTU.trans ht), min_eq_right hTU]

end FTAPTheorem42
