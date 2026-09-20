/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryGainExtensionality
import FTAPTheorem42.Stochastic.Topology.Emery.Multiplier
import FTAPTheorem42.Stochastic.Topology.Emery.Realization
import FTAPTheorem42.Stochastic.DS.Lemma411.MaximalApproximation

/-!
# Direct elementary-test bounds for realized gains

The good-integrator condition is stated for elementary tests whose summed
integrand is uniformly small.  Such a test need not have a uniformly bounded
sum of the absolute values of its block coefficients.  This file therefore
uses the pathwise endpoint regrouping of finite elementary gains: for one
fixed row, a bound on the step function controls every endpoint jump, and
hence the tested gain, without imposing a coefficient-sum bound on the row.

The resulting envelope estimate is the first, fixed-row part of the direct
triangle argument for semimartingale inheritance of a realized gain.  The
row length occurs in the constant, so the estimate is used after fixing the
outer test index and selecting the inner approximation index; it is not a
uniform estimate over a growing family of rows.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! ## Monotonicity in the deterministic horizon -/

omit [MeasurableSpace Ω] in
theorem cappedFiniteHorizonAbsoluteEnvelope_mono_of_rightContinuous
    (X : Process Ω)
    (hXRight : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t)
    {T U : ℝ≥0} (hTU : T ≤ U) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω ≤
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X U ω := by
  have hRightAbs : ∀ ω t,
      ContinuousWithinAt ((fun s => |X s ω|)) (Set.Ici t) t := by
    intro ω t
    exact (hXRight ω t).abs
  have hE :
      FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t ω => |X t ω|) T ω ≤
        FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t ω => |X t ω|) U ω := by
    apply iSup_le
    intro r
    obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (r * r.factorial + 1))
      Finset.nonempty_range_add_one
      (fun j =>
        (FactorialChronologicalGrid.stoppedGrid T r).natSample
          (fun t ω => |X t ω|) j ω)
    rw [show FactorialChronologicalGrid.factorialRunningMax
        (fun t ω => |X t ω|) T r ω =
        (FactorialChronologicalGrid.stoppedGrid T r).natSample
          (fun t ω => |X t ω|) k ω by exact hkEq]
    change ENNReal.ofReal
        |X ((FactorialChronologicalGrid.stoppedGrid T r).sampledTime k) ω| ≤ _
    apply FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
      (fun t ω => |X t ω|) U hRightAbs ω
    exact (by
      simp only [ChronologicalGrid.sampledTime,
        FactorialChronologicalGrid.stoppedGrid_time]
      exact (min_le_right _ _).trans hTU)
  unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by finiteness)
      (min_le_right
        (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
          (fun t ω => |X t ω|) U ω) 1))
  exact min_le_min hE le_rfl

/-- The stored-gain approximation converges on every finite horizon, not only
on the integer horizons used in the completion carrier. -/
theorem RealizedStrategy.gain_convergence_at_horizon
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S) (T : ℝ≥0) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        T)
      atTop (fun _ => (0 : ℝ)) := by
  let U : ℝ≥0 := ((Nat.ceil T + 1 : ℕ) : ℝ≥0)
  have hTU : T ≤ U := by
    exact ((Nat.le_ceil T).trans (Nat.cast_le.mpr (Nat.le_succ _)))
  have hUpper : TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        U)
      atTop (fun _ => (0 : ℝ)) := by
    simpa only [U] using H.gain_convergence (Nat.ceil T)
  apply tendstoInMeasure_of_nonneg_le
  · intro n ω
    refine ⟨?_, ?_⟩
    · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
        _ _ _
    · apply cappedFiniteHorizonAbsoluteEnvelope_mono_of_rightContinuous
        (X := fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
        (fun ω t =>
          (PredictableElementaryStrategy.rightContinuous_gain S hSRight
            (H.representative n) ω t).sub (H.gain_rightContinuous ω t))
        hTU ω
  exact hUpper

/-- A fixed predictable elementary row with a pointwise bounded step function
has a capped envelope controlled by the source envelope.  The estimate uses
the finite endpoint representation and does not assume a deterministic bound
on the row's absolute coefficient sum. -/
theorem cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_le_of_integrand_bound
    (X : Process Ω)
    (hXRight : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (J : PredictableElementaryStrategy ℱ) (ε : ℝ) (hε : 0 ≤ ε)
    (hJ : ∀ t ω, |J.integrand t ω| ≤ ε)
    (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (elementaryGain X J) T ω ≤
      max (8 * (J.length : ℝ) * ε) 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω := by
  let E := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    (fun t ω => |X t ω|) T ω
  by_cases hE : E = ∞
  · have hCapOut :=
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
        (elementaryGain X J) T ω
    have hCapIn :
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω = 1 := by
      unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      simp only [E, hE]
      rfl
    rw [hCapIn]
    exact hCapOut.trans (le_mul_of_one_le_left (by positivity)
      (le_max_right (8 * (J.length : ℝ) * ε) 1))
  · have hRightAbs : ∀ ω t,
        ContinuousWithinAt ((fun s => |X s ω|)) (Set.Ici t) t := by
      intro ω t
      exact (hXRight ω t).abs
    have hXBound : ∀ u, u ≤ T → |X u ω| ≤ E.toReal := by
      intro u hu
      have hValue :=
        FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
          (fun t ω => |X t ω|) T hRightAbs ω hu
      have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hE).2 hValue
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using hReal
    have hOutBound : ∀ u, u ≤ T →
        |elementaryGain X J u ω| ≤
          8 * (J.length : ℝ) * ε * E.toReal := by
      intro u hu
      change |ElementaryStrategy.gain X J.toElementary u ω| ≤
        8 * (J.length : ℝ) * ε * E.toReal
      exact PredictableElementaryStrategy.abs_gain_le_of_integrand_bound
        X J u ω ε E.toReal hε ENNReal.toReal_nonneg
        (fun s => hJ s ω)
        (fun v hv => hXBound v (hv.trans hu))
    have hOutE :=
      FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_le_of_bound
        (elementaryGain X J) T hOutBound
    unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    have hMin := min_le_min_right (1 : ℝ≥0∞) hOutE
    have hMinReal := ENNReal.toReal_mono
      (ne_top_of_le_ne_top (by finiteness)
        (min_le_right
          (ENNReal.ofReal (8 * (J.length : ℝ) * ε * E.toReal)) 1)) hMin
    calc
      (min
          (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
            (fun t ω => |elementaryGain X J t ω|) T ω) 1).toReal ≤
          (min (ENNReal.ofReal
            (8 * (J.length : ℝ) * ε * E.toReal)) 1).toReal := hMinReal
      _ ≤ max (8 * (J.length : ℝ) * ε) 1 * (min E 1).toReal := by
        have hScale : 0 ≤ 8 * (J.length : ℝ) * ε := by positivity
        have hCap := SemimartingaleQuasiNorm.cappedEnvelope_cap_scale
          (8 * (J.length : ℝ) * ε) hScale E
        convert hCap using 1
        rw [ENNReal.ofReal_mul hScale, ENNReal.ofReal_toReal hE]

/-- A fixed elementary test sends the stored-gain approximation error to zero.
The estimate is deliberately row-dependent: its constant contains the finite
length of the fixed test, while the integrand bound is the only hypothesis on
that row. -/
theorem RealizedStrategy.transformed_gain_error_convergence_at_horizon
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (J : PredictableElementaryStrategy ℱ) (ε : ℝ) (hε : 0 ≤ ε)
    (hJ : ∀ t ω, |J.integrand t ω| ≤ ε) (T : ℝ≥0) :
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (J.mul (H.representative n)) t ω -
          elementaryGain H.gain J t ω) T)
      atTop (fun _ => (0 : ℝ)) := by
  have hError (n : ℕ) :
      (fun t ω => elementaryGain S (J.mul (H.representative n)) t ω -
        elementaryGain H.gain J t ω) =
        elementaryGain
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          J := by
    exact elementaryGain_transform_error S
      (H.representative n) H.gain J
  have hUpper : TendstoInMeasure μ
      (fun n ω => max (8 * (J.length : ℝ) * ε) 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω' => elementaryGain S (H.representative n) t ω' - H.gain t ω')
          T ω)
      atTop (fun _ => (0 : ℝ)) := by
    have hScaled := FTAPTheorem42.tendstoInMeasure_smul_const
      (max (8 * (J.length : ℝ) * ε) 1)
      (H.gain_convergence_at_horizon S hSRight T)
    simpa only [mul_zero] using hScaled
  refine tendstoInMeasure_of_nonneg_le
    (f := fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (fun t ω => elementaryGain S (J.mul (H.representative n)) t ω -
        elementaryGain H.gain J t ω) T)
    (g := fun n ω => max (8 * (J.length : ℝ) * ε) 1 *
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω' => elementaryGain S (H.representative n) t ω' - H.gain t ω')
        T ω) ?_ hUpper
  · intro n ω
    refine ⟨?_, ?_⟩
    · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
        _ _ _
    · rw [hError n]
      exact cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_le_of_integrand_bound
        (elementaryGain S (H.representative n) - H.gain)
        (fun ω t =>
          (PredictableElementaryStrategy.rightContinuous_gain S hSRight
            (H.representative n) ω t).sub (H.gain_rightContinuous ω t))
        J ε hε hJ T ω

end PredictableElementaryEmery

end FTAPTheorem42
