import FTAPTheorem42.Stochastic.Topology.Emery.TerminalSwitching
import FTAPTheorem42.Stochastic.Topology.Emery.PositiveScalar

/-! # Finite-horizon realized gains of one fixed price

The predicate records an actual original-price realization and eventual
constancy. Numerical component records can use this range without being
asserted to be actual integrals over their bookkeeping source.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S X Y : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A gain in the actual range of the fixed original price that is constant
after some deterministic finite horizon. -/
def HasFiniteRealizedGain (μ : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (S X : Process Ω) : Prop :=
  ∃ R : RealizedStrategy (ℱ := F) μ S,
    ProcessIndistinguishable μ X R.gain ∧
    ∃ T : NNReal, ∀ᵐ ω ∂μ, ∀ t, T ≤ t → X t ω = X T ω

omit [IsProbabilityMeasure μ] in
/-- The gain representative may be changed on one common null set. -/
theorem HasFiniteRealizedGain.congr
    (h : HasFiniteRealizedGain μ F S X) (hXY : ProcessIndistinguishable μ Y X) :
    HasFiniteRealizedGain μ F S Y := by
  obtain ⟨R, hR, T, hT⟩ := h
  refine ⟨R, hXY.trans hR, T, ?_⟩
  filter_upwards [hXY, hT] with ω hω hConst
  intro t ht
  rw [hω t, hω T, hConst t ht]

/-- The zero strategy is an original-price realization. -/
theorem hasFiniteRealizedGain_zero (hS : IsStronglyProgressive F S) :
    HasFiniteRealizedGain μ F S 0 := by
  refine ⟨RealizedStrategy.zero S hS, ?_, 0, Eventually.of_forall (fun _ _ _ => rfl)⟩
  exact Eventually.of_forall fun _ _ => rfl

/-- Addition uses the existing realized sum, with the larger finite horizon. -/
theorem HasFiniteRealizedGain.add (hS : IsStronglyProgressive F S)
    (hX : HasFiniteRealizedGain μ F S X) (hY : HasFiniteRealizedGain μ F S Y) :
    HasFiniteRealizedGain μ F S (X + Y) := by
  obtain ⟨R, hR, T, hT⟩ := hX
  obtain ⟨U, hU, V, hV⟩ := hY
  refine ⟨R.add S hS U, hR.add hU, max T V, ?_⟩
  filter_upwards [hT, hV] with ω hTω hVω
  intro t ht
  change X t ω + Y t ω = X (max T V) ω + Y (max T V) ω
  rw [hTω t ((le_max_left _ _).trans ht), hVω t ((le_max_right _ _).trans ht),
    hTω _ (le_max_left _ _), hVω _ (le_max_right _ _)]

/-- Negation also stays in the same original-price range. -/
theorem HasFiniteRealizedGain.neg (hS : IsStronglyProgressive F S)
    (h : HasFiniteRealizedGain μ F S X) : HasFiniteRealizedGain μ F S (-X) := by
  obtain ⟨R, hR, T, hT⟩ := h
  refine ⟨R.neg S hS, ?_, T, ?_⟩
  · filter_upwards [hR] with ω hω
    exact fun t => congrArg Neg.neg (hω t)
  · filter_upwards [hT] with ω hω
    exact fun t ht => congrArg Neg.neg (hω t ht)

/-- Positive normalization is realized by scaling elementary representatives. -/
theorem HasFiniteRealizedGain.posSMul (hS : IsStronglyProgressive F S)
    (h : HasFiniteRealizedGain μ F S X) {c : Real} (hc : 0 < c) :
    HasFiniteRealizedGain μ F S (c • X) := by
  obtain ⟨R, hR, T, hT⟩ := h
  refine ⟨R.posSMul S hS c hc, ?_, T, ?_⟩
  · filter_upwards [hR] with ω hω
    exact fun t => congrArg (fun x => c * x) (hω t)
  · filter_upwards [hT] with ω hω
    exact fun t ht => congrArg (fun x => c * x) (hω t ht)

/-- Every real scalar is handled by zero, positive scaling, and negation. -/
theorem HasFiniteRealizedGain.smul (hS : IsStronglyProgressive F S)
    (h : HasFiniteRealizedGain μ F S X) (c : Real) :
    HasFiniteRealizedGain μ F S (c • X) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hScaled := (h.neg hS).posSMul hS (neg_pos.mpr hc)
    apply hScaled.congr
    apply Eventually.of_forall
    intro ω t
    change c * X t ω = -c * -X t ω
    ring
  · simpa only [zero_smul] using hasFiniteRealizedGain_zero (μ := μ) hS
  · exact h.posSMul hS hc

/-- A possibly infinite stop can be capped at the known finite horizon.
Thus the existing bounded stopping construction suffices for this range. -/
theorem HasFiniteRealizedGain.stoppedProcess
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (h : HasFiniteRealizedGain μ F S X)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ) :
    HasFiniteRealizedGain μ F S (MeasureTheory.stoppedProcess X τ) := by
  obtain ⟨R, hR, T, hT⟩ := h
  let cap : Ω → WithTop NNReal := fun ω => min (τ ω) (T : WithTop NNReal)
  let value : Ω → NNReal := fun ω => (cap ω).untopA
  have hCapT ω : cap ω ≤ (T : WithTop NNReal) := min_le_right _ _
  have hFinite ω : cap ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hCapT ω)
  have hValue ω : (value ω : WithTop NNReal) = cap ω := by
    dsimp only [value]
    rw [WithTop.untopA_eq_untop (hFinite ω), WithTop.coe_untop]
  have hValueFun : (fun ω => (value ω : WithTop NNReal)) = cap := funext hValue
  have hValueStop : IsStoppingTime F (fun ω => (value ω : WithTop NNReal)) := by
    rw [hValueFun]
    exact hτ.min (isStoppingTime_const F T)
  have hValueT ω : value ω ≤ T := WithTop.untopA_le (hCapT ω)
  have hCapped : HasFiniteRealizedGain μ F S (MeasureTheory.stoppedProcess X cap) := by
    refine ⟨R.stopAt S hS hSR value hValueStop T hValueT, ?_, T, ?_⟩
    · simpa only [RealizedStrategy.stopAt_gain, hValueFun] using hR.stoppedProcess cap
    · apply Eventually.of_forall
      intro ω t ht
      rw [stoppedProcess_eq_of_ge ((hCapT ω).trans (WithTop.coe_le_coe.mpr ht)),
        stoppedProcess_eq_of_ge (hCapT ω)]
  have hXT : ProcessIndistinguishable μ
      (MeasureTheory.stoppedProcess X (fun _ => (T : WithTop NNReal))) X := by
    filter_upwards [hT] with ω hω
    intro t
    rw [stoppedProcess_const_apply]
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht), hω t (le_of_not_ge ht)]
  have hEq := hXT.stoppedProcess τ
  rw [stoppedProcess_stoppedProcess'] at hEq
  exact hCapped.congr hEq.symm

end FTAPTheorem42.PredictableElementaryEmery
