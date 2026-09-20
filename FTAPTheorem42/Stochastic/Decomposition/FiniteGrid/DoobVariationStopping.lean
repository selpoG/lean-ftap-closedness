/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobL2

/-!
# Stopping finite-grid Doob variation

The predictable sign is switched off once the already accumulated
predictable variation reaches a fixed level.  The switching decision is
known at the left endpoint of the next grid interval.  The stopped variation
therefore overshoots its threshold by at most one source-increment bound, and
the corresponding transform of the Doob martingale remains a true
martingale.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The accumulated predictable variation is adapted to the sampled
filtration. -/
theorem stronglyAdapted_doobPredictableVariation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsFiniteMeasure mu] :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobPredictableVariation S F mu) := by
  intro n
  unfold doobPredictableVariation doobPredictableIncrement
  have hSum : StronglyMeasurable[G.sampledFiltration F n]
      ((∑ k ∈ Finset.range n, fun omega =>
        |G.doobPredictablePart S F mu (k + 1) omega -
          G.doobPredictablePart S F mu k omega|) : Omega → Real) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hNext : StronglyMeasurable[G.sampledFiltration F k]
        (G.doobPredictablePart S F mu (k + 1)) :=
      stronglyAdapted_predictablePart (f := G.natSample S)
        (ℱ := G.sampledFiltration F) (μ := mu) k
    have hNow : StronglyMeasurable[G.sampledFiltration F k]
        (G.doobPredictablePart S F mu k) :=
      stronglyAdapted_predictablePart' (f := G.natSample S)
        (ℱ := G.sampledFiltration F) (μ := mu) k
    have hDiff : StronglyMeasurable[G.sampledFiltration F n]
        (fun omega =>
          |G.doobPredictablePart S F mu (k + 1) omega -
            G.doobPredictablePart S F mu k omega|) := by
      convert ((hNext.sub hNow).norm).mono
        ((G.sampledFiltration F).mono hk.le) using 1
    exact hDiff
  convert hSum using 1
  funext omega
  simp only [Finset.sum_apply, Pi.sub_apply]

/-- The predictable sign switched off after the accumulated predictable
variation reaches `a`. -/
noncomputable def doobVariationStoppedSign
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  fun n omega =>
    if G.doobPredictableVariation S F mu n omega < a then
      G.doobPredictableSign S F mu n omega
    else 0

/-- The variation-stopped sign is adapted to the sampled filtration. -/
theorem stronglyAdapted_doobVariationStoppedSign
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) [IsFiniteMeasure mu] (a : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobVariationStoppedSign S F mu a) := by
  intro n
  let B : Set Omega :=
    {omega | G.doobPredictableVariation S F mu n omega < a}
  have hB : MeasurableSet[G.sampledFiltration F n] B := by
    change MeasurableSet[G.sampledFiltration F n]
      ((G.doobPredictableVariation S F mu n) ⁻¹' Iio a)
    exact (G.stronglyAdapted_doobPredictableVariation S F mu n).measurable
      measurableSet_Iio
  change StronglyMeasurable[G.sampledFiltration F n]
    (B.piecewise (G.doobPredictableSign S F mu n) 0)
  exact StronglyMeasurable.piecewise hB
    (G.stronglyAdapted_doobPredictableSign n) stronglyMeasurable_zero

/-- Variation stopping preserves the unit bound on the sign coefficient. -/
theorem abs_doobVariationStoppedSign_le_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) (omega : Omega) :
    |G.doobVariationStoppedSign S F mu a n omega| ≤ 1 := by
  by_cases h : G.doobPredictableVariation S F mu n omega < a
  · simp [doobVariationStoppedSign, h]
  · simp [doobVariationStoppedSign, h]

/-- Predictable variation accumulated before the variation threshold is
reached. -/
noncomputable def doobVariationStoppedAccumulation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) (n : Nat) : Omega → Real :=
  fun omega => ∑ k ∈ Finset.range n,
    if G.doobPredictableVariation S F mu k omega < a then
      |G.doobPredictableIncrement S F mu k omega|
    else 0

/-- The stopped accumulation reaches every level reached by the original
variation, up to the stopping threshold itself. -/
theorem min_le_doobVariationStoppedAccumulation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) {a : Real} (ha : 0 ≤ a) :
    ∀ n omega,
      min a (G.doobPredictableVariation S F mu n omega) ≤
        G.doobVariationStoppedAccumulation S F mu a n omega := by
  intro n
  induction n with
  | zero =>
      intro omega
      simp [doobPredictableVariation, doobVariationStoppedAccumulation,
        min_eq_right ha]
  | succ n ih =>
      intro omega
      rw [show G.doobPredictableVariation S F mu (n + 1) omega =
          G.doobPredictableVariation S F mu n omega +
            |G.doobPredictableIncrement S F mu n omega| by
        simp [doobPredictableVariation, Finset.sum_range_succ]]
      rw [show G.doobVariationStoppedAccumulation S F mu a (n + 1) omega =
          G.doobVariationStoppedAccumulation S F mu a n omega +
            (if G.doobPredictableVariation S F mu n omega < a then
              |G.doobPredictableIncrement S F mu n omega| else 0) by
        simp [doobVariationStoppedAccumulation, Finset.sum_range_succ]]
      by_cases hLevel : G.doobPredictableVariation S F mu n omega < a
      · rw [ite_eq_left hLevel]
        have hPrevious : G.doobPredictableVariation S F mu n omega ≤
            G.doobVariationStoppedAccumulation S F mu a n omega := by
          simpa [min_eq_right hLevel.le] using ih omega
        exact (min_le_right _ _).trans
          (add_le_add hPrevious le_rfl)
      · rw [ite_eq_right hLevel, add_zero]
        have haPrevious : a ≤ G.doobPredictableVariation S F mu n omega :=
          le_of_not_gt hLevel
        have haNext : a ≤ G.doobPredictableVariation S F mu n omega +
            |G.doobPredictableIncrement S F mu n omega| :=
          haPrevious.trans (le_add_of_nonneg_right (abs_nonneg _))
        rw [min_eq_left haNext]
        simpa [min_eq_left haPrevious] using ih omega

/-- Reaching the threshold in the original predictable variation forces the
stopped accumulation to reach the same threshold. -/
theorem le_doobVariationStoppedAccumulation_of_le_variation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) {a : Real} (ha : 0 ≤ a) (n : Nat) (omega : Omega)
    (hLevel : a ≤ G.doobPredictableVariation S F mu n omega) :
    a ≤ G.doobVariationStoppedAccumulation S F mu a n omega := by
  simpa [min_eq_left hLevel] using
    G.min_le_doobVariationStoppedAccumulation S F mu ha n omega

/-- If every predictable increment has size at most `B`, stopping before
level `a` limits the accumulated variation by `a + B`. -/
theorem doobVariationStoppedAccumulation_le
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (omega : Omega) {a B : Real} (ha : 0 ≤ a)
    (hIncrement : ∀ k,
      |G.doobPredictableIncrement S F mu k omega| ≤ B) :
    ∀ n,
      G.doobVariationStoppedAccumulation S F mu a n omega ≤ a + B := by
  intro n
  induction n with
  | zero =>
      simp [doobVariationStoppedAccumulation]
      have hB := hIncrement 0
      have hBnonneg : 0 ≤ B :=
        (abs_nonneg (G.doobPredictableIncrement S F mu 0 omega)).trans hB
      linarith [abs_nonneg (G.doobPredictableIncrement S F mu 0 omega)]
  | succ n ih =>
      rw [show G.doobVariationStoppedAccumulation S F mu a (n + 1) omega =
          G.doobVariationStoppedAccumulation S F mu a n omega +
            (if G.doobPredictableVariation S F mu n omega < a then
              |G.doobPredictableIncrement S F mu n omega| else 0) by
        simp [doobVariationStoppedAccumulation, Finset.sum_range_succ]]
      by_cases hLevel : G.doobPredictableVariation S F mu n omega < a
      · rw [ite_eq_left hLevel]
        have hStoppedLe :
            G.doobVariationStoppedAccumulation S F mu a n omega ≤
              G.doobPredictableVariation S F mu n omega := by
          unfold doobVariationStoppedAccumulation doobPredictableVariation
          apply Finset.sum_le_sum
          intro k _hk
          split_ifs
          · exact le_rfl
          · exact abs_nonneg _
        exact (add_le_add hStoppedLe (hIncrement n)).trans
          (by linarith)
      · rw [ite_eq_right hLevel]
        simpa using ih

/-- For a bounded source, variation stopping has a deterministic one-step
overshoot bound almost surely. -/
theorem ae_doobVariationStoppedAccumulation_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) {a : Real} (ha : 0 ≤ a) :
    ∀ᵐ omega ∂mu, ∀ n,
      G.doobVariationStoppedAccumulation S F mu a n omega ≤
        a + 2 * max source.bound 0 := by
  filter_upwards [G.ae_norm_predictablePart_increment_le source] with
      omega hIncrement
  intro n
  apply G.doobVariationStoppedAccumulation_le S F mu omega ha
    (B := 2 * max source.bound 0)
    (hIncrement := fun k => by
      rw [← Real.norm_eq_abs]
      exact hIncrement k) n

end ChronologicalGrid

end FTAPTheorem42
