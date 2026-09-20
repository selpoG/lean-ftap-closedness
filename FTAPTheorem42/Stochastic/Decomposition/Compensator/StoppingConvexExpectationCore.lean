/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingOptionalSamplingCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingTimeRoundingCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Source-independent stopping-time convex expectations

This module contains the rounding, finite-sum, squeeze, and dominated
convergence algebra for a common tail-convexification at a bounded stopping
time.  It does not know how the rows were constructed.  A row enters only
through a finite-grid stopping-time expectation certificate.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

/-! ## The source assumptions used by the common algebra -/

/-- The part of an increasing source needed by stopping-time rounding.

The source is deliberately bounded only by its terminal value in this
interface.  In particular, no deterministic source bound occurs here.
-/
structure StoppingConvexSourceData
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (V : Process Ω) (T : NNReal) : Prop where
  stronglyAdapted : StronglyAdapted F V
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (V · omega) (Ici t) t
  monotone : ∀ omega, Monotone (V · omega)
  value_nonnegative : ∀ {t : NNReal}, t ≤ T → ∀ omega, 0 ≤ V t omega

namespace StoppingConvexSourceData

omit [IsProbabilityMeasure mu] in
theorem value_le_terminal
    (hV : StoppingConvexSourceData F V T)
    {t : NNReal} (ht : t ≤ T) (omega : Ω) :
    V t omega ≤ V T omega :=
  hV.monotone omega ht

end StoppingConvexSourceData

/-! ## Rounded source and row samples -/

noncomputable def roundedSourceConvexSampleCore
    (V : Process Ω) (T : NNReal) (τ : Ω → NNReal)
    (w : TailConvexWeights n) : Ω → Real :=
  w.apply (fun r => fun omega =>
    V (rightRoundedTime T τ r omega) omega)

noncomputable def processConvexSampleCore
    (row : Nat → Process Ω) (τ : Ω → NNReal)
    (w : TailConvexWeights n) : Ω → Real :=
  w.apply (fun r => fun omega => row r (τ omega) omega)

omit [MeasurableSpace Ω] in
theorem roundedSourceConvexSampleCore_eq_weighted_sum
    (V : Process Ω) (T : NNReal) (τ : Ω → NNReal)
    (w : TailConvexWeights n) :
    roundedSourceConvexSampleCore V T τ w =
      fun omega => ∑ r ∈ w.support, w.weight r *
        V (rightRoundedTime T τ r omega) omega :=
  rfl

omit [MeasurableSpace Ω] in
theorem processConvexSampleCore_eq_weighted_sum
    (row : Nat → Process Ω) (τ : Ω → NNReal)
    (w : TailConvexWeights n) :
    processConvexSampleCore row τ w =
      fun omega => ∑ r ∈ w.support, w.weight r * row r (τ omega) omega :=
  rfl

/-! ## Pathwise squeeze and pointwise convergence -/

omit [IsProbabilityMeasure mu] in
theorem source_at_tau_le_roundedSourceConvexSampleCore
    (hV : StoppingConvexSourceData F V T)
    (w : TailConvexWeights n) (τ : Ω → NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (omega : Ω) :
    V (τ omega) omega ≤
      roundedSourceConvexSampleCore V T τ w omega := by
  rw [roundedSourceConvexSampleCore_eq_weighted_sum V T τ w]
  calc
    V (τ omega) omega = ∑ r ∈ w.support,
        w.weight r * V (τ omega) omega := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
    _ ≤ ∑ r ∈ w.support,
        w.weight r * V (rightRoundedTime T τ r omega) omega := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (hV.monotone omega
          (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).1)
        (w.nonneg r hr)

omit [IsProbabilityMeasure mu] in
theorem roundedSourceConvexSampleCore_le_source_at_tau_add_mesh
    (hV : StoppingConvexSourceData F V T)
    (w : TailConvexWeights n) (τ : Ω → NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (omega : Ω) :
    roundedSourceConvexSampleCore V T τ w omega ≤
      V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega := by
  rw [roundedSourceConvexSampleCore_eq_weighted_sum V T τ w]
  calc
    (∑ r ∈ w.support, w.weight r *
        V (rightRoundedTime T τ r omega) omega) ≤
        ∑ r ∈ w.support, w.weight r *
          V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (w.nonneg r hr)
      apply hV.monotone omega
      exact le_min
        (rightRoundedTime_mesh_bound_of_le
          (T := T) (τ := τ) n r (w.tail r hr) omega)
        (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).2
    _ = V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

omit [IsProbabilityMeasure mu] in
theorem roundedSourceConvexSampleCore_squeeze
    (hV : StoppingConvexSourceData F V T)
    (w : TailConvexWeights n) (τ : Ω → NNReal)
    (hτT : ∀ omega, τ omega ≤ T) (omega : Ω) :
    V (τ omega) omega ≤ roundedSourceConvexSampleCore V T τ w omega ∧
      roundedSourceConvexSampleCore V T τ w omega ≤
        V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ∧
      V (min (τ omega + (n.factorial : NNReal)⁻¹) T) omega ≤ V T omega := by
  refine ⟨source_at_tau_le_roundedSourceConvexSampleCore
      (F := F) hV w τ hτT omega,
    roundedSourceConvexSampleCore_le_source_at_tau_add_mesh
      (F := F) hV w τ hτT omega, ?_⟩
  exact hV.value_le_terminal (min_le_right _ _) omega

private theorem cutoff_mesh_zero_core
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) :
    Tendsto (fun n => (cutoff n).factorial⁻¹ : Nat → NNReal) atTop
      (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp
      (factorial_tendsto_atTop.comp hCutoff.tendsto_atTop))

omit [MeasurableSpace Ω] in
private theorem source_upper_time_tendsto_core
    (τ : Ω → NNReal) (hτT : ∀ omega, τ omega ≤ T)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) (omega : Ω) :
    Tendsto (fun n => min (τ omega +
      ((cutoff n).factorial : NNReal)⁻¹) T) atTop (𝓝 (τ omega)) := by
  have hmesh := cutoff_mesh_zero_core hCutoff
  have hadd : Tendsto (fun n => τ omega +
      ((cutoff n).factorial : NNReal)⁻¹) atTop (𝓝 (τ omega)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hmesh
  have hmin := hadd.min (tendsto_const_nhds :
    Tendsto (fun _ : Nat => T) atTop (𝓝 T))
  simpa only [min_eq_left (hτT omega)] using hmin

omit [MeasurableSpace Ω] in
private theorem source_upper_time_tendsto_nhdsWithin_core
    (τ : Ω → NNReal) (hτT : ∀ omega, τ omega ≤ T)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) (omega : Ω) :
    Tendsto (fun n => min (τ omega +
      ((cutoff n).factorial : NNReal)⁻¹) T) atTop
      (𝓝[Set.Ici (τ omega)] (τ omega)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨source_upper_time_tendsto_core τ hτT hCutoff omega, ?_⟩
  filter_upwards [] with n
  exact le_min (le_add_of_nonneg_right (by positivity)) (hτT omega)

omit [IsProbabilityMeasure mu] in
theorem tendsto_roundedSourceConvexSampleCore
    (hV : StoppingConvexSourceData F V T)
    {w : ∀ n, TailConvexWeights n}
    (τ : Ω → NNReal) (hτT : ∀ omega, τ omega ≤ T)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) (omega : Ω) :
    Tendsto
      (fun n => roundedSourceConvexSampleCore V T τ
        (w (cutoff n)) omega) atTop
      (𝓝 (V (τ omega) omega)) := by
  have hLower : Tendsto (fun _ : Nat => V (τ omega) omega)
      atTop (𝓝 (V (τ omega) omega)) := tendsto_const_nhds
  have hUpperTime := source_upper_time_tendsto_nhdsWithin_core
    (T := T) τ hτT hCutoff omega
  have hUpper := (hV.rightContinuous omega (τ omega)).tendsto.comp hUpperTime
  have hUpper' : Tendsto
      (fun n => V (min (τ omega +
        ((cutoff n).factorial : NNReal)⁻¹) T) omega) atTop
      (𝓝 (V (τ omega) omega)) := by
    exact hUpper.congr' (Filter.Eventually.of_forall fun n => rfl)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper'
  · exact Filter.Eventually.of_forall fun n =>
      source_at_tau_le_roundedSourceConvexSampleCore
        (F := F) hV (w (cutoff n)) τ hτT omega
  · exact Filter.Eventually.of_forall fun n =>
      roundedSourceConvexSampleCore_le_source_at_tau_add_mesh
        (F := F) hV (w (cutoff n)) τ hτT omega

/-! ## Integrability of rounded source samples -/

theorem integrable_source_at_rightRoundedTime_core
    (hV : StoppingConvexSourceData F V T)
    (hTerminal : MemLp (V T) (2 : ENNReal) mu)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (r : Nat) :
    Integrable (fun omega =>
      V (rightRoundedTime T τ r omega) omega) mu := by
  let sigma : Ω → WithTop NNReal := fun omega =>
    (rightRoundedTime T τ r omega : WithTop NNReal)
  have hsigma : IsStoppingTime F sigma := by
    simpa only [sigma] using
      rightRoundedTime_isStoppingTime (T := T) (τ := τ) hτ r
  have hsigma_le : ∀ omega, sigma omega ≤ (T : WithTop NNReal) := by
    intro omega
    exact WithTop.coe_le_coe.mpr
      ((rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).2)
  have hProgressive : IsStronglyProgressive F V :=
    FTAPTheorem42.StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hV.stronglyAdapted hV.rightContinuous
  have hMeas : StronglyMeasurable[hsigma.measurableSpace]
      (MeasureTheory.stoppedValue V sigma) :=
    MeasureTheory.measurable_stoppedValue hProgressive hsigma |>.stronglyMeasurable
  have hMem : MemLp (MeasureTheory.stoppedValue V sigma)
      (2 : ENNReal) mu := by
    apply MemLp.of_le hTerminal
      (hMeas.mono hsigma.measurableSpace_le).aestronglyMeasurable
    filter_upwards with omega
    change ‖V (sigma omega).untopA omega‖ ≤ ‖V T omega‖
    have hne : sigma omega ≠ ⊤ := WithTop.coe_ne_top
    have htime : (sigma omega).untopA = rightRoundedTime T τ r omega := by
      rw [show sigma omega =
        (rightRoundedTime T τ r omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    have htime_le : (sigma omega).untopA ≤ T := by
      rw [htime]
      exact (rightRoundedTime_bounds (T := T) (τ := τ) hτT r omega).2
    rw [Real.norm_eq_abs, abs_of_nonneg (hV.value_nonnegative htime_le omega),
      Real.norm_eq_abs, abs_of_nonneg
        (hV.value_nonnegative (t := T) le_rfl omega)]
    exact hV.value_le_terminal htime_le omega
  have hEq : MeasureTheory.stoppedValue V sigma =
      (fun omega => V (rightRoundedTime T τ r omega) omega) := by
    funext omega
    change V (sigma omega).untopA omega = V (rightRoundedTime T τ r omega) omega
    have hne : sigma omega ≠ ⊤ := WithTop.coe_ne_top
    have htime : (sigma omega).untopA = rightRoundedTime T τ r omega := by
      rw [show sigma omega =
        (rightRoundedTime T τ r omega : WithTop NNReal) by rfl,
        WithTop.untopA_eq_untop hne]
      rfl
    rw [htime]
  rw [← hEq]
  exact hMem.integrable (by norm_num)

theorem roundedSourceConvexSampleCore_integrable
    (hV : StoppingConvexSourceData F V T)
    (hTerminal : MemLp (V T) (2 : ENNReal) mu)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T) (w : TailConvexWeights n) :
    Integrable (roundedSourceConvexSampleCore V T τ w) mu := by
  rw [roundedSourceConvexSampleCore_eq_weighted_sum V T τ w]
  apply integrable_finsetSum
  intro r hr
  exact (integrable_source_at_rightRoundedTime_core
    (F := F) (mu := mu) hV hTerminal hτ hτT r).const_mul (w.weight r)

/-! ## Generic row certificates and finite-sum identity -/

/-- The row-level information needed to sum optional-sampling identities. -/
structure StoppingRowExpectationCertificate
    (row : Nat → Process Ω)
    (sourceRounded : Nat → Ω → Real)
    (τ : Ω → NNReal) : Prop where
  row_integrable : ∀ r, Integrable
    (fun omega => row r (τ omega) omega) mu
  source_integrable : ∀ r, Integrable (sourceRounded r) mu
  integral_row_eq_source : ∀ r,
    (∫ omega, row r (τ omega) omega ∂mu) =
      ∫ omega, sourceRounded r omega ∂mu

omit [IsProbabilityMeasure mu] in
theorem processConvexSampleCore_integrable
    (row : Nat → Process Ω) (τ : Ω → NNReal)
    (hCert : StoppingRowExpectationCertificate (mu := mu)
      row (fun r omega => V (rightRoundedTime T τ r omega) omega) τ)
    (w : TailConvexWeights n) :
    Integrable (processConvexSampleCore row τ w) mu := by
  rw [processConvexSampleCore_eq_weighted_sum row τ w]
  apply integrable_finsetSum
  intro r hr
  exact (hCert.row_integrable r).const_mul (w.weight r)

omit [IsProbabilityMeasure mu] in
theorem processConvexSampleCore_integral_eq_roundedSourceConvexSampleCore_integral
    (row : Nat → Process Ω) (τ : Ω → NNReal)
    (hCert : StoppingRowExpectationCertificate (mu := mu)
      row (fun r omega => V (rightRoundedTime T τ r omega) omega) τ)
    (w : TailConvexWeights n) :
    (∫ omega, processConvexSampleCore row τ w omega ∂mu) =
      ∫ omega, roundedSourceConvexSampleCore V T τ w omega ∂mu := by
  rw [processConvexSampleCore_eq_weighted_sum row τ w]
  rw [roundedSourceConvexSampleCore_eq_weighted_sum V T τ w]
  rw [integral_finsetSum]
  · rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [integral_const_mul, hCert.integral_row_eq_source r]
      exact (integral_const_mul (μ := mu) (w.weight r)
        (fun omega => V (rightRoundedTime T τ r omega) omega)).symm
    · intro r hr
      exact (hCert.source_integrable r).const_mul (w.weight r)
  · intro r hr
    exact (hCert.row_integrable r).const_mul (w.weight r)

theorem integral_processConvexSampleCore_at_stopping_tendsto
    (hV : StoppingConvexSourceData F V T)
    (hTerminal : MemLp (V T) (2 : ENNReal) mu)
    (row : Nat → Process Ω) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hCert : StoppingRowExpectationCertificate (mu := mu)
      row (fun r omega => V (rightRoundedTime T τ r omega) omega) τ)
    (w : ∀ n, TailConvexWeights n)
    (cutoff : Nat → Nat) (hCutoff : StrictMono cutoff) :
    Tendsto (fun n =>
      ∫ omega, processConvexSampleCore row τ (w (cutoff n)) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu)) := by
  have hSourceInt : ∀ n, Integrable
      (roundedSourceConvexSampleCore V T τ (w (cutoff n))) mu := by
    intro n
    exact roundedSourceConvexSampleCore_integrable
      (F := F) (mu := mu) hV hTerminal hτ hτT (w (cutoff n))
  have hRowInt : ∀ n, Integrable
      (processConvexSampleCore row τ (w (cutoff n))) mu := by
    intro n
    exact processConvexSampleCore_integrable
      (mu := mu) row τ hCert (w (cutoff n))
  have hIntegralEq : ∀ n,
      (∫ omega, processConvexSampleCore row τ (w (cutoff n)) omega ∂mu) =
        ∫ omega, roundedSourceConvexSampleCore V T τ
          (w (cutoff n)) omega ∂mu := by
    intro n
    exact processConvexSampleCore_integral_eq_roundedSourceConvexSampleCore_integral
      (mu := mu) row τ hCert (w (cutoff n))
  have hSourceMeas : ∀ n, AEStronglyMeasurable
      (roundedSourceConvexSampleCore V T τ (w (cutoff n))) mu :=
    fun n => (hSourceInt n).aestronglyMeasurable
  have hSourceBound : ∀ n, ∀ᵐ omega ∂mu,
      ‖roundedSourceConvexSampleCore V T τ
        (w (cutoff n)) omega‖ ≤ V T omega := by
    intro n
    filter_upwards [] with omega
    have hSqueeze := roundedSourceConvexSampleCore_squeeze
      (F := F) hV (w (cutoff n)) τ hτT omega
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hSqueeze.2.1.trans hSqueeze.2.2
    · exact (hV.value_nonnegative (hτT omega) omega).trans hSqueeze.1
  have hSourceTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n => roundedSourceConvexSampleCore V T τ
        (w (cutoff n)) omega) atTop (𝓝 (V (τ omega) omega)) := by
    filter_upwards [] with omega
    exact tendsto_roundedSourceConvexSampleCore
      (F := F) hV τ hτT hCutoff omega
  have hSourceIntegralTendsto : Tendsto (fun n =>
      ∫ omega, roundedSourceConvexSampleCore V T τ
        (w (cutoff n)) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun omega => V T omega) hSourceMeas
      (hTerminal.integrable (by norm_num)) hSourceBound hSourceTendsto
  exact hSourceIntegralTendsto.congr'
    (Filter.Eventually.of_forall fun n => (hIntegralEq n).symm)

end HorizonFactorialGrid

end FTAPTheorem42
