/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.EmeryAlgebra
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessUniqueness

/-! # Elementary-test errors and Cauchy sequences

Finite-horizon test errors respect path agreement up to the horizon. Uniform
control over all tests identifies ucp limits and is stable under uniformly
small approximation errors. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The constant depends on this fixed test; it is never maximized over
the elementary-test class. -/
theorem elementaryEmeryTestError_tendstoInMeasure_of_ucp
    {X : Nat → Process Ω} {Y : Process Ω}
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hUcp : ∀ T : NNReal, TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X n t w - Y t w) T) atTop (fun _ => (0 : Real)))
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    TendstoInMeasure μ (fun n => elementaryEmeryTestError (X n) Y J T)
      atTop (fun _ => (0 : Real)) := by
  open PredictableElementaryEmery in
  have hBound n w : elementaryEmeryTestError (X n) Y J T w ≤
      max (8 * (J.strategy.length : Real) * 1) 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t w => X n t w - Y t w) T w := by
    unfold elementaryEmeryTestError
    change FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t w => elementaryGain (X n) J.strategy t w - elementaryGain Y J.strategy t w) T w ≤ _
    rw [← elementaryGain_source_sub]
    exact cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_le_of_integrand_bound
      _ (fun w t => (hXR n w t).sub (hYR w t)) J.strategy 1 zero_le_one
      J.abs_integrand_le_one T w
  have hScaled := tendstoInMeasure_smul_const
    (max (8 * (J.strategy.length : Real) * 1) 1) (hUcp T)
  simp only [mul_zero] at hScaled
  exact PredictableElementaryEmery.tendstoInMeasure_of_nonneg_le
    (fun n w => ⟨(elementaryEmeryTestError_bounds (X n) Y J T w).1, hBound n w⟩) hScaled

/-- Uniform Cauchy control passes from a cofinal subsequence to its regular
ucp limit for the entire sequence. The common
threshold is fixed before the test and the auxiliary limiting row. -/
theorem ElementaryEmeryCauchy.converges_of_subsequence_ucp
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryCauchy μ F X)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (f : Nat → Nat) (hf : Tendsto f atTop atTop)
    (hUcp : ∀ T : NNReal, TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X (f n) t w - Y t w) T) atTop (fun _ => (0 : Real))) :
    ElementaryEmeryConverges μ F X Y := by
  intro T ε hε
  obtain ⟨N, hN⟩ := h T ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  intro J
  have hLim : Tendsto (fun m => ∫ w, elementaryEmeryTestError (X (f m)) Y J T w ∂μ)
      atTop (𝓝 0) :=
    PredictableElementaryEmery.integral_tendsto_zero_of_tendstoInMeasure_of_bounded
      (fun m => elementaryEmeryTestError_measurable (hX (f m)) hY J T)
      (fun m w => elementaryEmeryTestError_bounds (X (f m)) Y J T w)
      (elementaryEmeryTestError_tendstoInMeasure_of_ucp (fun m => hXR (f m)) hYR hUcp J T)
  have hLe : ∀ᶠ m in atTop, (∫ w, elementaryEmeryTestError (X n) Y J T w ∂μ) ≤
      ε + ∫ w, elementaryEmeryTestError (X (f m)) Y J T w ∂μ := by
    filter_upwards [hf.eventually (eventually_ge_atTop N)] with m hm
    have hPoint w : elementaryEmeryTestError (X n) Y J T w ≤
        elementaryEmeryTestError (X (f m)) (X n) J T w +
          elementaryEmeryTestError (X (f m)) Y J T w :=
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
        (ElementaryStrategy.gain (X n) J.strategy.toElementary)
        (ElementaryStrategy.gain Y J.strategy.toElementary)
        (ElementaryStrategy.gain (X (f m)) J.strategy.toElementary) T w
    have hInt := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) (hX n) hY J T)
      ((elementaryEmeryTestError_integrable (hX (f m)) (hX n) J T).add
        (elementaryEmeryTestError_integrable (hX (f m)) hY J T)) (Eventually.of_forall hPoint)
    simp only [Pi.add_apply] at hInt
    rw [integral_add (elementaryEmeryTestError_integrable (hX (f m)) (hX n) J T)
      (elementaryEmeryTestError_integrable (hX (f m)) hY J T)] at hInt
    exact hInt.trans (add_le_add (hN (f m) hm n hn J) le_rfl)
  simpa only [add_zero, elementaryEmeryTestError] using
    ge_of_tendsto (tendsto_const_nhds.add hLim) hLe

/-- Uniform Cauchy control passes to a supplied regular ucp limit. -/
theorem ElementaryEmeryCauchy.converges_of_ucp
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryCauchy μ F X)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hXR : ∀ n w t, ContinuousWithinAt (X n · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hUcp : ∀ T : NNReal, TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t w => X n t w - Y t w) T) atTop (fun _ => (0 : Real))) :
    ElementaryEmeryConverges μ F X Y :=
  h.converges_of_subsequence_ucp hX hY hXR hYR id tendsto_id hUcp

theorem elementaryEmeryTestError_comm (X Y : Process Ω)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    elementaryEmeryTestError X Y J T = elementaryEmeryTestError Y X J T := by
  funext w
  simp only [elementaryEmeryTestError,
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope]
  congr 2
  apply congrArg (fun Z : Process Ω =>
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope Z T w)
  funext t w
  exact abs_sub_comm _ _

theorem ElementaryEmeryConverges.cauchy {X : Nat → Process Ω} {Y : Process Ω}
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (h : ElementaryEmeryConverges μ F X Y) : ElementaryEmeryCauchy μ F X := by
  intro T ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h T (ε / 2) (half_pos hε))
  refine ⟨N, ?_⟩
  intro m hm n hn J
  have hPoint w : elementaryEmeryTestError (X m) (X n) J T w ≤
      elementaryEmeryTestError Y (X m) J T w + elementaryEmeryTestError Y (X n) J T w :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (ElementaryStrategy.gain (X m) J.strategy.toElementary)
      (ElementaryStrategy.gain (X n) J.strategy.toElementary)
      (ElementaryStrategy.gain Y J.strategy.toElementary) T w
  have hInt := integral_mono_ae
    (elementaryEmeryTestError_integrable (μ := μ) (hX m) (hX n) J T)
    ((elementaryEmeryTestError_integrable hY (hX m) J T).add
      (elementaryEmeryTestError_integrable hY (hX n) J T)) (Eventually.of_forall hPoint)
  simp only [Pi.add_apply] at hInt
  rw [integral_add (elementaryEmeryTestError_integrable hY (hX m) J T)
    (elementaryEmeryTestError_integrable hY (hX n) J T),
    elementaryEmeryTestError_comm Y (X m), elementaryEmeryTestError_comm Y (X n)] at hInt
  exact hInt.trans ((add_le_add (hN m hm J) (hN n hn J)).trans_eq (add_halves ε))

end FTAPTheorem42

namespace FTAPTheorem42

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}

end FTAPTheorem42

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_elementaryEmeryTestError_triangle {X Y Z : Process Ω}
    (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    (hZ : IsStronglyProgressive F Z)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    (∫ ω, elementaryEmeryTestError X Y J T ω ∂μ) ≤
      (∫ ω, elementaryEmeryTestError X Z J T ω ∂μ) +
        ∫ ω, elementaryEmeryTestError Z Y J T ω ∂μ := by
  have hPoint ω : elementaryEmeryTestError X Y J T ω ≤
      elementaryEmeryTestError Z X J T ω + elementaryEmeryTestError Z Y J T ω :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (ElementaryStrategy.gain X J.strategy.toElementary)
      (ElementaryStrategy.gain Y J.strategy.toElementary)
      (ElementaryStrategy.gain Z J.strategy.toElementary) T ω
  have h := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) hX hY J T)
    ((elementaryEmeryTestError_integrable hZ hX J T).add
      (elementaryEmeryTestError_integrable hZ hY J T)) (Eventually.of_forall hPoint)
  simp only [Pi.add_apply] at h
  rwa [integral_add (elementaryEmeryTestError_integrable hZ hX J T)
    (elementaryEmeryTestError_integrable hZ hY J T), elementaryEmeryTestError_comm Z X] at h

/-- A common elementary-test bound passes to a process Émery limit. -/
theorem ElementaryEmeryConverges.testError_bound
    {X : Nat → Process Ω} {Y : Process Ω}
    (h : ElementaryEmeryConverges μ F X Y)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (T : NNReal) (b : Real)
    (hBound : ∀ n, ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError (X n) 0 J T ω ∂μ) ≤ b) :
    ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError Y 0 J T ω ∂μ) ≤ b := by
  intro J
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, hn⟩ := (h T δ hδ).exists
  have hnJ : (∫ ω, elementaryEmeryTestError (X n) Y J T ω ∂μ) ≤ δ := hn J
  have hTri := integral_elementaryEmeryTestError_triangle (μ := μ) hY
    (show IsStronglyProgressive F (0 : Process Ω) from fun _ => stronglyMeasurable_zero)
    (hX n) J T
  rw [elementaryEmeryTestError_comm Y (X n)] at hTri
  linarith only [hTri, hnJ, hBound n J]

/-- A sequence is Cauchy when, on each horizon, it is uniformly approximated
by a sequence which is Cauchy on that horizon. All cutoffs precede the test. -/
theorem elementaryEmeryCauchy_of_uniform_approximations
    {X : Nat → Process Ω} (hX : ∀ n, IsStronglyProgressive F (X n))
    (hApprox : ∀ T : NNReal, ∀ ε : Real, 0 < ε →
      ∃ Y : Nat → Process Ω,
        (∀ n, IsStronglyProgressive F (Y n)) ∧
        (∀ n, ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
          (∫ ω, elementaryEmeryTestError (X n) (Y n) J T ω ∂μ) ≤ ε) ∧
        (∀ δ : Real, 0 < δ → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
          ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
            (∫ ω, elementaryEmeryTestError (Y n) (Y k) J T ω ∂μ) ≤ δ)) :
    ElementaryEmeryCauchy μ F X := by
  intro T ε hε
  obtain ⟨Y, hY, hError, hCauchy⟩ := hApprox T (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := hCauchy (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn k hk J => ?_⟩
  have h₁ := integral_elementaryEmeryTestError_triangle (μ := μ) (hX n) (hX k) (hY n) J T
  have h₂ := integral_elementaryEmeryTestError_triangle (μ := μ) (hY n) (hX k) (hY k) J T
  have h₃ := hError k J
  rw [elementaryEmeryTestError_comm (X k) (Y k)] at h₃
  linarith only [h₁, h₂, hError n J, h₃, hN n hn k hk J]

end FTAPTheorem42
