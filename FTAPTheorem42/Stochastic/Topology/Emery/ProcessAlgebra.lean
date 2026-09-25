/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessCauchy
import FTAPTheorem42.Stochastic.Topology.Emery.FiniteStopping
import FTAPTheorem42.Stochastic.Topology.Emery.Completion

/-! # Elementary-test estimates respect indistinguishability -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}

theorem elementaryEmeryTestError_congr {X X' Y Y' : Process Ω}
    (hX : ProcessIndistinguishable μ X X') (hY : ProcessIndistinguishable μ Y Y')
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    elementaryEmeryTestError X Y J T =ᵐ[μ] elementaryEmeryTestError X' Y' J T := by
  filter_upwards [hX, hY] with w hwX hwY
  unfold elementaryEmeryTestError FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  congr 2
  apply iSup_congr
  intro r
  congr 1
  unfold FactorialChronologicalGrid.factorialRunningMax
  apply Finset.sup'_congr
  · rfl
  · intro k hk
    simp only [ChronologicalGrid.natSample]
    rw [J.strategy.toElementary.gain_congr_price _ w hwX,
      J.strategy.toElementary.gain_congr_price _ w hwY]

/-- Both rows may be replaced before taking the common test supremum. -/
theorem ElementaryEmeryCauchy.congr {X X' : Nat → Process Ω}
    (h : ElementaryEmeryCauchy μ F X)
    (hEq : ∀ n, ProcessIndistinguishable μ (X n) (X' n)) :
    ElementaryEmeryCauchy μ F X' := by
  intro T ε hε
  obtain ⟨N, hN⟩ := h T ε hε
  refine ⟨N, fun m hm n hn J => ?_⟩
  rw [← integral_congr_ae (elementaryEmeryTestError_congr (hEq m) (hEq n) J T)]
  exact hN m hm n hn J

theorem ElementaryEmeryConverges.congr_limit {X : Nat → Process Ω} {Y Y' : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y) (hEq : ProcessIndistinguishable μ Y Y') :
    ElementaryEmeryConverges μ F X Y' := by
  intro T ε hε
  filter_upwards [h T ε hε] with n hn
  intro J
  change ∫ w, elementaryEmeryTestError (X n) Y' J T w ∂μ ≤ ε
  rw [← integral_congr_ae (elementaryEmeryTestError_congr
    (ProcessIndistinguishable.refl μ (X n)) hEq J T)]
  exact hn J

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Addition in the process elementary-test topology -/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The capped test error is subadditive in both source processes. -/
theorem elementaryEmeryTestError_add_le (X U Y V : Process Ω)
    (J : BoundedPredictableElementaryMultiplier F) (T : NNReal) (w : Ω) :
    elementaryEmeryTestError (X + U) (Y + V) J T w ≤
      elementaryEmeryTestError X Y J T w + elementaryEmeryTestError U V J T w := by
  have h := SIntegrableFiniteVariationBridge.cappedFiniteHorizonAbsoluteEnvelope_add_le
    (fun t w => ElementaryStrategy.gain X J.strategy.toElementary t w -
      ElementaryStrategy.gain Y J.strategy.toElementary t w)
    (fun t w => ElementaryStrategy.gain U J.strategy.toElementary t w -
      ElementaryStrategy.gain V J.strategy.toElementary t w) T w
  have hEq : (fun t w => ElementaryStrategy.gain (X + U) J.strategy.toElementary t w -
      ElementaryStrategy.gain (Y + V) J.strategy.toElementary t w) =
    (fun t w => (ElementaryStrategy.gain X J.strategy.toElementary t w -
      ElementaryStrategy.gain Y J.strategy.toElementary t w) +
      (ElementaryStrategy.gain U J.strategy.toElementary t w -
      ElementaryStrategy.gain V J.strategy.toElementary t w)) := by
    funext t w
    simp only [Pi.add_def, ElementaryStrategy.gain_add_price]
    ring
  simpa only [elementaryEmeryTestError, hEq] using h

/-- Addition preserves uniform elementary-test convergence. -/
theorem ElementaryEmeryConverges.add {X U : Nat → Process Ω} {Y V : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hU : ∀ n, IsStronglyProgressive F (U n))
    (hY : IsStronglyProgressive F Y) (hV : IsStronglyProgressive F V)
    (hXY : ElementaryEmeryConverges μ F X Y) (hUV : ElementaryEmeryConverges μ F U V) :
    ElementaryEmeryConverges μ F (fun n => X n + U n) (Y + V) := by
  intro T ε hε
  filter_upwards [hXY T (ε / 2) (half_pos hε), hUV T (ε / 2) (half_pos hε)] with n hn hm
  intro J
  have hPoint w := elementaryEmeryTestError_add_le (X n) (U n) Y V J T w
  have hInt := integral_mono_ae
    (elementaryEmeryTestError_integrable (μ := μ) ((hX n).add (hU n)) (hY.add hV) J T)
    ((elementaryEmeryTestError_integrable (hX n) hY J T).add
      (elementaryEmeryTestError_integrable (hU n) hV J T)) (Eventually.of_forall hPoint)
  simp only [Pi.add_apply] at hInt
  rw [integral_add (elementaryEmeryTestError_integrable (hX n) hY J T)
    (elementaryEmeryTestError_integrable (hU n) hV J T)] at hInt
  exact hInt.trans ((add_le_add (hn J) (hm J)).trans_eq (add_halves ε))

omit [IsProbabilityMeasure μ] in
/-- Negation preserves every capped elementary test error. -/
theorem ElementaryEmeryConverges.neg {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y) :
    ElementaryEmeryConverges μ F (fun n => -X n) (-Y) := by
  have hEq n (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) T :
      elementaryEmeryTestError (-X n) (-Y) J T = elementaryEmeryTestError (X n) Y J T := by
    unfold elementaryEmeryTestError
    have hNeg (Z : Process Ω) : ElementaryStrategy.gain (-Z) J.strategy.toElementary =
        -ElementaryStrategy.gain Z J.strategy.toElementary := by
      exact (show ElementaryStrategy.gain (fun t ω => -Z t ω) J.strategy.toElementary =
        (fun t ω => -ElementaryStrategy.gain Z J.strategy.toElementary t ω) from by
        simpa only [PredictableElementaryEmery.elementaryGain, neg_one_mul] using
          PredictableElementaryEmery.elementaryGain_smul_source (-1) Z J.strategy)
    have hg : (fun t ω => ElementaryStrategy.gain (-X n) J.strategy.toElementary t ω -
        ElementaryStrategy.gain (-Y) J.strategy.toElementary t ω) =
        (fun t ω => -(ElementaryStrategy.gain (X n) J.strategy.toElementary t ω -
          ElementaryStrategy.gain Y J.strategy.toElementary t ω)) := by
      rw [hNeg, hNeg]
      funext t ω
      change -_ - -_ = -(_ - _)
      ring
    rw [hg]
    funext ω
    exact PredictableElementaryEmery.cappedFiniteHorizonAbsoluteEnvelope_neg _ T ω
  intro T ε hε
  filter_upwards [h T ε hε] with n hn
  intro J
  change ∫ ω, elementaryEmeryTestError (-X n) (-Y) J T ω ∂μ ≤ ε
  rw [hEq]
  exact hn J

/-- Subtraction preserves uniform elementary-test convergence. -/
theorem ElementaryEmeryConverges.sub {X U : Nat → Process Ω} {Y V : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hU : ∀ n, IsStronglyProgressive F (U n))
    (hY : IsStronglyProgressive F Y) (hV : IsStronglyProgressive F V)
    (hXY : ElementaryEmeryConverges μ F X Y) (hUV : ElementaryEmeryConverges μ F U V) :
    ElementaryEmeryConverges μ F (fun n => X n - U n) (Y - V) := by
  rw [show (fun n => X n - U n) = (fun n => X n + -U n) from by
    funext n; exact sub_eq_add_neg _ _, sub_eq_add_neg Y V]
  exact hXY.add hX (fun n => (hU n).neg) hY hV.neg hUV.neg

omit [IsProbabilityMeasure μ] in
/-- Convergence is unchanged when its limit is moved to the left side. -/
theorem elementaryEmeryConverges_iff_sub_zero {X : Nat → Process Ω} {Y : Process Ω} :
    ElementaryEmeryConverges μ F X Y ↔
      ElementaryEmeryConverges μ F (fun n => X n - Y) 0 := by
  have hGain (n : Nat) (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
      (fun t w => ElementaryStrategy.gain (X n - Y) J.strategy.toElementary t w -
        ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary t w) =
      (fun t w => ElementaryStrategy.gain (X n) J.strategy.toElementary t w -
        ElementaryStrategy.gain Y J.strategy.toElementary t w) := by
    funext t w
    have h := PredictableElementaryEmery.elementaryGain_source_sub (X n) Y J.strategy
    have hZero : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary t w = 0 := by
      simp [ElementaryStrategy.gain, ElementaryInterval.gain]
    rw [hZero, sub_zero]
    exact congrFun (congrFun h t) w
  simp only [ElementaryEmeryConverges, hGain]

omit [IsProbabilityMeasure μ] in
/-- The difference may equally be taken in the opposite order. -/
theorem elementaryEmeryConverges_iff_reverse_sub_zero {X : Nat → Process Ω} {Y : Process Ω} :
    ElementaryEmeryConverges μ F X Y ↔
      ElementaryEmeryConverges μ F (fun n => Y - X n) 0 := by
  have hEq n (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) T :
      elementaryEmeryTestError (Y - X n) 0 J T = elementaryEmeryTestError (X n) Y J T := by
    rw [elementaryEmeryTestError_comm (X n) Y]
    unfold elementaryEmeryTestError
    congr 1
    have h := PredictableElementaryEmery.elementaryGain_source_sub Y (X n) J.strategy
    have hZero : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
      funext t w
      simp [ElementaryStrategy.gain, ElementaryInterval.gain]
    simp only [hZero, Pi.zero_apply, sub_zero]
    exact h
  change (∀ T ε, 0 < ε → ∀ᶠ n in atTop, ∀ J,
    ∫ w, elementaryEmeryTestError (X n) Y J T w ∂μ ≤ ε) ↔
    (∀ T ε, 0 < ε → ∀ᶠ n in atTop, ∀ J,
    ∫ w, elementaryEmeryTestError (Y - X n) 0 J T w ∂μ ≤ ε)
  simp only [hEq]

end FTAPTheorem42
