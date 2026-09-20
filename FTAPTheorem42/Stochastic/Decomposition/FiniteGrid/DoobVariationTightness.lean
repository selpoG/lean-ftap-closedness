/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobDoubleStopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Tightness of finite-grid predictable Doob variation

The doubly stopped source integral splits into a true martingale transform
and a nonnegative predictable accumulation.  Its deterministic exit
overshoot bound therefore controls the expectation of that accumulation.
Together with boundedness in probability of all unit-bounded elementary
gains, this yields a grid-uniform tail estimate for the predictable Doob
variation.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- Finite-grid predictable variation is pointwise nonnegative. -/
theorem doobPredictableVariation_nonneg
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (n : Nat) (omega : Omega) :
    0 ≤ G.doobPredictableVariation S F mu n omega := by
  unfold doobPredictableVariation
  exact Finset.sum_nonneg fun k _hk => abs_nonneg _

/-- Predictable variation accumulated while both stopping gates remain
open. -/
noncomputable def doobDoublyStoppedAccumulation
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) : Omega → Real :=
  fun omega => ∑ k ∈ Finset.range n,
    G.doobSourceFirstExitGate S F mu a b k omega *
      (if G.doobPredictableVariation S F mu k omega < a then
        |G.doobPredictableIncrement S F mu k omega|
      else 0)

/-- The doubly stopped sign integrates the predictable Doob component to
the doubly stopped accumulation. -/
theorem discretePredictableIntegral_doobDoublyStoppedSign_predictablePart
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) :
    discretePredictableIntegral
        (G.doobDoublyStoppedSign S F mu a b)
        (G.doobPredictablePart S F mu) n =
      G.doobDoublyStoppedAccumulation S F mu a b n := by
  funext omega
  unfold discretePredictableIntegral doobDoublyStoppedAccumulation
    doobDoublyStoppedSign doobVariationStoppedSign
    doobPredictableIncrement
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hLevel : G.doobPredictableVariation S F mu k omega < a
  · simp only [Pi.mul_apply, hLevel, ite_true, mul_assoc]
    have hSign := G.doobPredictableSign_mul_increment S F mu k omega
    unfold doobPredictableIncrement at hSign
    simpa only [Pi.sub_apply] using congrArg
      (fun x => G.doobSourceFirstExitGate S F mu a b k omega * x) hSign
  · simp [hLevel]

/-- The doubly stopped source integral is the sum of its martingale
transform and predictable accumulation. -/
theorem discretePredictableIntegral_doobDoublyStoppedSign_source
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) :
    G.doobDoublyStoppedSourceIntegral S F mu a b n =
      discretePredictableIntegral
          (G.doobDoublyStoppedSign S F mu a b)
          (G.doobMartingalePart S F mu) n +
        G.doobDoublyStoppedAccumulation S F mu a b n := by
  rw [← G.discretePredictableIntegral_doobDoublyStoppedSign_predictablePart
    S F mu a b n]
  funext omega
  unfold doobDoublyStoppedSourceIntegral discretePredictableIntegral
    doobMartingalePart martingalePart doobPredictablePart
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The doubly stopped predictable accumulation is nonnegative. -/
theorem doobDoublyStoppedAccumulation_nonneg
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega) :
    0 ≤ G.doobDoublyStoppedAccumulation S F mu a b n omega := by
  unfold doobDoublyStoppedAccumulation
  apply Finset.sum_nonneg
  intro k _hk
  rcases G.doobSourceFirstExitGate_eq_zero_or_one
      S F mu a b k omega with hGate | hGate
  · simp [hGate]
  · simp only [hGate, one_mul]
    split_ifs <;> positivity

/-- The doubly stopped transform of the finite-grid Doob martingale is a
true martingale. -/
theorem martingale_discretePredictableIntegral_doobDoublyStoppedSign_martingalePart
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a b : Real) :
    Martingale
      (discretePredictableIntegral
        (G.doobDoublyStoppedSign S F mu a b)
        (G.doobMartingalePart S F mu))
      (G.sampledFiltration F) mu := by
  apply DiscretePredictableIntegral.isMartingale
    (C := fun _ => 1)
    (G.martingale_martingalePart_natSample_boundedSemimartingaleSource source)
    (G.memLp_two_doobMartingalePart source)
    (G.stronglyAdapted_doobDoublyStoppedSign source.stronglyAdapted a b)
  intro n
  exact ae_of_all mu fun omega =>
    G.abs_doobDoublyStoppedSign_le_one S F mu a b n omega

/-- The doubly stopped source integral is integrable at every grid index. -/
theorem integrable_doobDoublyStoppedSourceIntegral
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real)
    {b : Real} (hb : 0 ≤ b) (n : Nat) :
    Integrable (G.doobDoublyStoppedSourceIntegral S F mu a b n) mu := by
  have hAdapted : StronglyAdapted (G.sampledFiltration F)
      (G.doobDoublyStoppedSourceIntegral S F mu a b) :=
    DiscretePredictableIntegral.stronglyAdapted_of_stronglyAdapted
      (G.stronglyAdapted_doobDoublyStoppedSign source.stronglyAdapted a b)
      (fun k => source.stronglyAdapted (G.sampledTime k))
  apply Integrable.of_bound
    ((hAdapted n).mono ((G.sampledFiltration F).le n)).aestronglyMeasurable
    (b + 2 * max source.bound 0)
  filter_upwards [G.ae_abs_doobDoublyStoppedSourceIntegral_le source a hb] with
      omega hBound
  simpa only [Real.norm_eq_abs] using hBound n

/-- The doubly stopped predictable accumulation is integrable. -/
theorem integrable_doobDoublyStoppedAccumulation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real)
    {b : Real} (hb : 0 ≤ b) (n : Nat) :
    Integrable (G.doobDoublyStoppedAccumulation S F mu a b n) mu := by
  have hDifference : Integrable
      (G.doobDoublyStoppedSourceIntegral S F mu a b n -
        discretePredictableIntegral
          (G.doobDoublyStoppedSign S F mu a b)
          (G.doobMartingalePart S F mu) n) mu :=
    (G.integrable_doobDoublyStoppedSourceIntegral source a hb n).sub
      ((G.martingale_discretePredictableIntegral_doobDoublyStoppedSign_martingalePart
        source a b).integrable n)
  refine hDifference.congr (ae_of_all mu fun omega => ?_)
  have hDecomposition := congrFun
    (G.discretePredictableIntegral_doobDoublyStoppedSign_source
      S F mu a b n) omega
  simp only [Pi.add_apply, Pi.sub_apply] at hDecomposition ⊢
  linarith

/-- The expected doubly stopped source integral is exactly the expected
predictable accumulation. -/
theorem integral_doobDoublyStoppedSourceIntegral_eq_accumulation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real)
    {b : Real} (hb : 0 ≤ b) (n : Nat) :
    ∫ omega, G.doobDoublyStoppedSourceIntegral S F mu a b n omega ∂mu =
      ∫ omega, G.doobDoublyStoppedAccumulation S F mu a b n omega ∂mu := by
  rw [G.discretePredictableIntegral_doobDoublyStoppedSign_source
    S F mu a b n]
  simp only [Pi.add_apply]
  rw [integral_add
    ((G.martingale_discretePredictableIntegral_doobDoublyStoppedSign_martingalePart
      source a b).integrable n)
    (G.integrable_doobDoublyStoppedAccumulation source a hb n)]
  have hMartingale :=
    G.martingale_discretePredictableIntegral_doobDoublyStoppedSign_martingalePart
      source a b
  have hZero : ∫ omega,
      discretePredictableIntegral
        (G.doobDoublyStoppedSign S F mu a b)
        (G.doobMartingalePart S F mu) n omega ∂mu = 0 := by
    simpa using
      (hMartingale.setIntegral_eq (Nat.zero_le n)
        (s := Set.univ) MeasurableSet.univ).symm
  rw [hZero, zero_add]

/-- The expected doubly stopped predictable accumulation is controlled by
the source-integral exit level and one source increment. -/
theorem integral_doobDoublyStoppedAccumulation_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real)
    {b : Real} (hb : 0 ≤ b) (n : Nat) :
    ∫ omega, G.doobDoublyStoppedAccumulation S F mu a b n omega ∂mu ≤
      b + 2 * max source.bound 0 := by
  rw [← G.integral_doobDoublyStoppedSourceIntegral_eq_accumulation
    source a hb n]
  have hIntegrable := G.integrable_doobDoublyStoppedSourceIntegral
    source a hb n
  calc
    ∫ omega, G.doobDoublyStoppedSourceIntegral S F mu a b n omega ∂mu ≤
        ∫ _ : Omega, (b + 2 * max source.bound 0) ∂mu := by
      apply integral_mono_ae hIntegrable (integrable_const _)
      filter_upwards [G.ae_abs_doobDoublyStoppedSourceIntegral_le
        source a hb] with omega hBound
      exact (le_abs_self _).trans (hBound n)
    _ = b + 2 * max source.bound 0 := by simp

/-- If the first-exit gate is still open at index `n`, the doubly stopped
and variation-stopped predictable accumulations agree at that index. -/
theorem doobDoublyStoppedAccumulation_eq_of_gate_eq_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega)
    (hGate : G.doobSourceFirstExitGate S F mu a b n omega = 1) :
    G.doobDoublyStoppedAccumulation S F mu a b n omega =
      G.doobVariationStoppedAccumulation S F mu a n omega := by
  unfold doobDoublyStoppedAccumulation doobVariationStoppedAccumulation
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hInside := (G.doobSourceFirstExitGate_eq_one_iff
    S F mu a b n omega).1 hGate
  have hGateK : G.doobSourceFirstExitGate S F mu a b k omega = 1 :=
    (G.doobSourceFirstExitGate_eq_one_iff S F mu a b k omega).2 fun j hj =>
      hInside j (Finset.mem_range.2
        ((Finset.mem_range.1 hj).trans_le (Nat.succ_le_succ hk.le)))
  rw [hGateK, one_mul]

/-- A large original predictable variation forces either a source-integral
exit or a large doubly stopped predictable accumulation. -/
theorem doobPredictableVariation_level_subset_doubleStopping
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) {a : Real} (ha : 0 ≤ a) (b : Real) (n : Nat) :
    {omega | a ≤ G.doobPredictableVariation S F mu n omega} ⊆
      {omega | b ≤
        |G.doobDoublyStoppedSourceIntegral S F mu a b n omega|} ∪
      {omega | a ≤
        G.doobDoublyStoppedAccumulation S F mu a b n omega} := by
  intro omega hVariation
  rcases G.doobSourceFirstExitGate_eq_zero_or_one
      S F mu a b n omega with hGate | hGate
  · left
    exact G.le_abs_doobDoublyStoppedSourceIntegral_of_gate_eq_zero
      S F mu a b n omega hGate
  · right
    change a ≤ G.doobDoublyStoppedAccumulation S F mu a b n omega
    change a ≤ G.doobPredictableVariation S F mu n omega at hVariation
    rw [G.doobDoublyStoppedAccumulation_eq_of_gate_eq_one
      S F mu a b n omega hGate]
    exact G.le_doobVariationStoppedAccumulation_of_le_variation
      S F mu ha n omega hVariation

/-- Markov's inequality for the doubly stopped predictable accumulation in
the normalization needed by the grid-uniform variation estimate. -/
theorem measure_doobDoublyStoppedAccumulation_ge_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a b : Real} (ha : 0 < a) (hb : 0 ≤ b) (n : Nat) :
    mu {omega | a ≤
        G.doobDoublyStoppedAccumulation S F mu a b n omega} ≤
      ENNReal.ofReal ((b + 2 * max source.bound 0) / a) := by
  let W : Omega → Real :=
    G.doobDoublyStoppedAccumulation S F mu a b n
  let f : Omega → ENNReal := fun omega => ENNReal.ofReal (W omega)
  have hWInt : Integrable W mu :=
    G.integrable_doobDoublyStoppedAccumulation source a hb n
  have hWNonneg : ∀ omega, 0 ≤ W omega := fun omega =>
    G.doobDoublyStoppedAccumulation_nonneg S F mu a b n omega
  have hf : AEMeasurable f mu := hWInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hMarkov := meas_ge_le_lintegral_div hf
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
  calc
    mu {omega | a ≤
        G.doobDoublyStoppedAccumulation S F mu a b n omega} =
        mu {omega | ENNReal.ofReal a ≤ f omega} := by
      congr 1
      ext omega
      simp only [Set.mem_ofPred_eq, f, W]
      exact (ENNReal.ofReal_le_ofReal_iff (hWNonneg omega)).symm
    _ ≤ (∫⁻ omega, f omega ∂mu) / ENNReal.ofReal a := hMarkov
    _ = ENNReal.ofReal (∫ omega, W omega ∂mu) /
        ENNReal.ofReal a := by
      rw [ofReal_integral_eq_lintegral_ofReal hWInt
        (ae_of_all mu hWNonneg)]
    _ ≤ ENNReal.ofReal (b + 2 * max source.bound 0) /
        ENNReal.ofReal a := by
      apply ENNReal.div_le_div_right
      exact ENNReal.ofReal_le_ofReal
        (G.integral_doobDoublyStoppedAccumulation_le source a hb n)
    _ = ENNReal.ofReal ((b + 2 * max source.bound 0) / a) := by
      rw [ENNReal.ofReal_div_of_pos ha]

end ChronologicalGrid

namespace IsSemimartingale

/-- On all chronological grids with a common terminal time, the terminal
predictable variations of the sampled Doob decompositions are uniformly
bounded in probability. -/
theorem uniformly_boundedInProbability_doobPredictableVariations
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu) (T : NNReal) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R : Real, 0 ≤ R ∧
        ∀ {M : Nat} (G : ChronologicalGrid NNReal M),
          G.sampledTime M = T →
          mu {omega | R <
            |G.doobPredictableVariation S F mu M omega|} ≤
            ENNReal.ofReal epsilon := by
  intro epsilon hepsilon
  have hHalf : 0 < epsilon / 2 := by linarith
  obtain ⟨R₀, hR₀, hTail⟩ :=
    hS.uniformly_boundedInProbability_doobDoublyStoppedSourceIntegrals
      source T (epsilon / 2) hHalf
  let b : Real := R₀ + 1
  let C : Real := b + 2 * max source.bound 0
  let a : Real := 2 * C / epsilon
  have hb : 0 < b := by dsimp [b]; linarith
  have hC : 0 < C := by
    dsimp [C]
    have hIncrementBound : 0 ≤ 2 * max source.bound 0 := by positivity
    linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  refine ⟨a, ha.le, ?_⟩
  intro M G hLast
  let Y : Omega → Real := fun omega =>
    G.doobDoublyStoppedSourceIntegral S F mu a b M omega
  let W : Omega → Real :=
    G.doobDoublyStoppedAccumulation S F mu a b M
  have hExit : mu {omega | b ≤ |Y omega|} ≤ ENNReal.ofReal (epsilon / 2) := by
    refine (measure_mono ?_).trans (hTail G a b hLast)
    intro omega homega
    change b ≤ |Y omega| at homega
    change R₀ < |Y omega|
    dsimp [b] at homega
    linarith
  have hAccumulation :
      mu {omega | a ≤ W omega} ≤ ENNReal.ofReal (epsilon / 2) := by
    have hMarkov := G.measure_doobDoublyStoppedAccumulation_ge_le
      source ha hb.le M
    change mu {omega | a ≤ W omega} ≤ _
    calc
      mu {omega | a ≤ W omega} ≤ ENNReal.ofReal (C / a) := by
        simpa only [C] using hMarkov
      _ = ENNReal.ofReal (epsilon / 2) := by
        congr 1
        dsimp [a]
        field_simp
  calc
    mu {omega | a <
        |G.doobPredictableVariation S F mu M omega|} ≤
        mu {omega | a ≤ G.doobPredictableVariation S F mu M omega} := by
      apply measure_mono
      intro omega homega
      change a < |G.doobPredictableVariation S F mu M omega| at homega
      change a ≤ G.doobPredictableVariation S F mu M omega
      rw [abs_of_nonneg
        (G.doobPredictableVariation_nonneg S F mu M omega)] at homega
      exact homega.le
    _ ≤ mu ({omega | b ≤ |Y omega|} ∪ {omega | a ≤ W omega}) :=
      measure_mono (by
        simpa only [Y, W] using
          G.doobPredictableVariation_level_subset_doubleStopping
            S F mu ha.le b M)
    _ ≤ mu {omega | b ≤ |Y omega|} + mu {omega | a ≤ W omega} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (epsilon / 2) + ENNReal.ofReal (epsilon / 2) :=
      add_le_add hExit hAccumulation
    _ = ENNReal.ofReal epsilon := by
      rw [← ENNReal.ofReal_add hHalf.le hHalf.le]
      congr 1
      ring

end IsSemimartingale

end FTAPTheorem42
