/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobVariationTightness

/-!
# Tightness of finite-grid predictable Doob variation under an L² envelope

This module supplies the random-envelope version of the finite-grid estimate.
The bounded-source module remains the implementation of the deterministic
bound version and is imported only for the shared finite-grid API.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- With a pathwise envelope, a doubly stopped source integral has only the
corresponding random one-step overshoot. -/
theorem ae_abs_doobDoublyStoppedSourceIntegral_le_of_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (ξ : Omega → Real)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) {b : Real} (hb : 0 ≤ b) :
    ∀ᵐ omega ∂mu, ∀ n,
      |G.doobDoublyStoppedSourceIntegral S F mu a b n omega| ≤
        b + 2 * ‖ξ omega‖ := by
  filter_upwards [hSBound] with omega hBound
  have hIncrement : ∀ n,
      ‖G.natSample S (n + 1) omega - G.natSample S n omega‖ ≤
        2 * ‖ξ omega‖ := by
    intro n
    rw [Real.norm_eq_abs]
    calc
      |G.natSample S (n + 1) omega - G.natSample S n omega| ≤
          |G.natSample S (n + 1) omega| +
            |G.natSample S n omega| := abs_sub _ _
      _ ≤ ‖ξ omega‖ + ‖ξ omega‖ := by
        exact add_le_add (hBound (G.sampledTime (n + 1)))
          (hBound (G.sampledTime n))
      _ = 2 * ‖ξ omega‖ := by ring
  intro n
  induction n with
  | zero =>
      have hZero :
          G.doobDoublyStoppedSourceIntegral S F mu a b 0 omega = 0 := by
        simp [doobDoublyStoppedSourceIntegral, discretePredictableIntegral]
      rw [hZero, abs_zero]
      exact add_nonneg hb (by positivity)
  | succ n ih =>
      rw [show G.doobDoublyStoppedSourceIntegral S F mu a b (n + 1) omega =
          G.doobDoublyStoppedSourceIntegral S F mu a b n omega +
            G.doobDoublyStoppedSign S F mu a b n omega *
              (G.natSample S (n + 1) omega - G.natSample S n omega) by
        simp [doobDoublyStoppedSourceIntegral,
          discretePredictableIntegral_succ]]
      rcases G.doobSourceFirstExitGate_eq_zero_or_one
          S F mu a b n omega with hGate | hGate
      · have hSignZero :
            G.doobDoublyStoppedSign S F mu a b n omega = 0 := by
          simp [doobDoublyStoppedSign, hGate]
        rw [hSignZero, zero_mul, add_zero]
        simpa only [Real.norm_eq_abs] using ih
      · have hCurrent :
            G.doobDoublyStoppedSourceIntegral S F mu a b n omega =
              G.doobVariationStoppedSourceIntegral S F mu a n omega :=
          G.doobDoublyStoppedSourceIntegral_eq_of_gate_eq_one
            S F mu a b n omega hGate
        have hInside := (G.doobSourceFirstExitGate_eq_one_iff
          S F mu a b n omega).1 hGate n (Finset.mem_range.2 (Nat.lt_add_one n))
        exact (calc
          |G.doobDoublyStoppedSourceIntegral S F mu a b n omega +
              G.doobDoublyStoppedSign S F mu a b n omega *
                (G.natSample S (n + 1) omega - G.natSample S n omega)| ≤
              |G.doobDoublyStoppedSourceIntegral S F mu a b n omega| +
                |G.doobDoublyStoppedSign S F mu a b n omega| *
                  |G.natSample S (n + 1) omega - G.natSample S n omega| := by
            calc
              _ ≤ |G.doobDoublyStoppedSourceIntegral S F mu a b n omega| +
                  |G.doobDoublyStoppedSign S F mu a b n omega *
                    (G.natSample S (n + 1) omega -
                      G.natSample S n omega)| := abs_add_le _ _
              _ = _ := by rw [abs_mul]
          _ < b + 1 * (2 * ‖ξ omega‖) := by
            apply add_lt_add_of_lt_of_le
            · simpa [hCurrent] using hInside
            · exact mul_le_mul
                (G.abs_doobDoublyStoppedSign_le_one S F mu a b n omega)
                (by simpa only [Real.norm_eq_abs] using hIncrement n)
                (abs_nonneg _) zero_le_one
          _ = b + 2 * ‖ξ omega‖ := by ring).le

/-- Markov's inequality for any integrable nonnegative real-valued random
variable, with a real upper bound on its expectation. -/
theorem measure_ge_le_of_integrable_nonneg
    {mu : Measure Omega} {W : Omega → Real} {a C : Real}
    [IsProbabilityMeasure mu]
    (hWInt : Integrable W mu) (hWNonneg : ∀ omega, 0 ≤ W omega)
    (ha : 0 < a) (hIntegral : ∫ omega, W omega ∂mu ≤ C) :
    mu {omega | a ≤ W omega} ≤ ENNReal.ofReal (C / a) := by
  let f : Omega → ENNReal := fun omega => ENNReal.ofReal (W omega)
  have hf : AEMeasurable f mu :=
    hWInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hMarkov := meas_ge_le_lintegral_div hf
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
  calc
    mu {omega | a ≤ W omega} =
        mu {omega | ENNReal.ofReal a ≤ f omega} := by
      congr 1
      ext omega
      simp only [Set.mem_ofPred_eq, f]
      exact (ENNReal.ofReal_le_ofReal_iff (hWNonneg omega)).symm
    _ ≤ (∫⁻ omega, f omega ∂mu) / ENNReal.ofReal a := hMarkov
    _ = ENNReal.ofReal (∫ omega, W omega ∂mu) /
        ENNReal.ofReal a := by
      rw [ofReal_integral_eq_lintegral_ofReal hWInt
        (ae_of_all mu hWNonneg)]
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal a := by
      apply ENNReal.div_le_div_right
      exact ENNReal.ofReal_le_ofReal hIntegral
    _ = ENNReal.ofReal (C / a) := by
      rw [ENNReal.ofReal_div_of_pos ha]

end ChronologicalGrid

namespace IsSemimartingale

/-- On all chronological grids with a common terminal time, the terminal
predictable variations of the sampled Doob decompositions are uniformly
bounded in probability when the source has a common square-integrable
random envelope. -/
theorem uniformly_boundedInProbability_doobPredictableVariations_of_memLp_two_envelope
    {X : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    (hX : IsSemimartingale X F Q)
    (hXAdapted : StronglyAdapted F X)
    (ξ : Omega → Real)
    (hξ : MemLp ξ (2 : ENNReal) Q)
    (hXBound : ∀ᵐ omega ∂Q, ∀ t, |X t omega| ≤ ‖ξ omega‖)
    (T : NNReal) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R : Real, 0 ≤ R ∧
        ∀ {M : Nat} (G : ChronologicalGrid NNReal M),
          G.sampledTime M = T →
          Q {omega | R <
            |G.doobPredictableVariation X F Q M omega|} ≤
            ENNReal.ofReal epsilon := by
  intro epsilon hepsilon
  have hHalf : 0 < epsilon / 2 := by linarith
  obtain ⟨R₀, hR₀, hTail⟩ :=
    hX.claimSetBoundedInProbability_unitBoundedElementaryGainSet T
      (epsilon / 2) hHalf
  have hξNorm : MemLp (fun omega => ‖ξ omega‖) (2 : ENNReal) Q := hξ.norm
  have hξNormInt : Integrable (fun omega => ‖ξ omega‖) Q :=
    hξNorm.integrable (by norm_num)
  let Iξ : Real := ∫ omega, ‖ξ omega‖ ∂Q
  have hIξ : 0 ≤ Iξ := by
    dsimp [Iξ]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun omega => norm_nonneg (ξ omega))
  let b : Real := R₀ + 1
  let C : Real := b + 2 * Iξ
  let a : Real := 2 * C / epsilon
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have hIξ' : 0 ≤ 2 * Iξ := by positivity
    linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  refine ⟨a, ha.le, ?_⟩
  intro M G hLast
  have hSampleAdapted :
      StronglyAdapted (G.sampledFiltration F) (G.natSample X) := by
    intro n
    exact hXAdapted (G.sampledTime n)
  have hSampleMem : ∀ n, MemLp (G.natSample X n) (2 : ENNReal) Q := by
    intro n
    apply MemLp.of_le hξNorm
      ((hSampleAdapted n).mono
        ((G.sampledFiltration F).le n)).aestronglyMeasurable
    filter_upwards [hXBound] with omega hBound
    simpa only [ChronologicalGrid.natSample, Real.norm_eq_abs,
      abs_abs] using
      hBound (G.sampledTime n)
  have hSampleIntegrable : ∀ n, Integrable (G.natSample X n) Q := by
    intro n
    exact (hSampleMem n).integrable (by norm_num)
  have hM : Martingale (G.doobMartingalePart X F Q)
      (G.sampledFiltration F) Q := by
    exact martingale_martingalePart hSampleAdapted hSampleIntegrable
  have hPredictableMem : ∀ n,
      MemLp (G.doobPredictablePart X F Q n) (2 : ENNReal) Q := by
    intro n
    change MemLp
      (predictablePart (G.natSample X) (G.sampledFiltration F) Q n)
      (2 : ENNReal) Q
    unfold predictablePart
    apply memLp_finsetSum'
    intro k hk
    exact ((hSampleMem (k + 1)).sub (hSampleMem k)).condExp (by norm_num)
  have hMMem : ∀ n,
      MemLp (G.doobMartingalePart X F Q n) (2 : ENNReal) Q := by
    intro n
    change MemLp
      (martingalePart (G.natSample X) (G.sampledFiltration F) Q n)
      (2 : ENNReal) Q
    unfold martingalePart
    exact (hSampleMem n).sub (hPredictableMem n)
  have hSignAdapted : StronglyAdapted (G.sampledFiltration F)
      (G.doobDoublyStoppedSign X F Q a b) :=
    G.stronglyAdapted_doobDoublyStoppedSign
      (mu := Q) hXAdapted a b
  have hSourceIntegralAdapted : StronglyAdapted (G.sampledFiltration F)
      (G.doobDoublyStoppedSourceIntegral X F Q a b) :=
    DiscretePredictableIntegral.stronglyAdapted_of_stronglyAdapted
      hSignAdapted (fun n => hXAdapted (G.sampledTime n))
  have hMartingaleTransform : Martingale
      (discretePredictableIntegral
        (G.doobDoublyStoppedSign X F Q a b)
        (G.doobMartingalePart X F Q))
      (G.sampledFiltration F) Q := by
    refine DiscretePredictableIntegral.isMartingale (C := fun _ => 1)
      hM hMMem hSignAdapted ?_
    intro n
    exact ae_of_all Q fun omega => by
      simpa using G.abs_doobDoublyStoppedSign_le_one X F Q a b n omega
  let Y : Omega → Real := fun omega =>
    G.doobDoublyStoppedSourceIntegral X F Q a b M omega
  let W : Omega → Real :=
    G.doobDoublyStoppedAccumulation X F Q a b M
  have hYBound : ∀ᵐ omega ∂Q, |Y omega| ≤
      b + 2 * ‖ξ omega‖ := by
    filter_upwards [G.ae_abs_doobDoublyStoppedSourceIntegral_le_of_envelope
      (S := X) (F := F) (mu := Q) ξ hXBound a (b := b) hb.le] with omega hBound
    simpa only [Y] using hBound M
  have hBoundInt : Integrable
      (fun omega => b + 2 * ‖ξ omega‖) Q := by
    exact (integrable_const b).add (hξNormInt.const_mul 2)
  have hYInt : Integrable Y Q := by
    apply hBoundInt.mono'
      ((hSourceIntegralAdapted M).mono
        ((G.sampledFiltration F).le M)).aestronglyMeasurable
    filter_upwards [hYBound] with omega hBound
    simpa only [Real.norm_eq_abs] using hBound
  have hWNonneg : ∀ omega, 0 ≤ W omega := fun omega =>
    G.doobDoublyStoppedAccumulation_nonneg X F Q a b M omega
  have hWInt : Integrable W Q := by
    have hDifference : Integrable
        (Y - discretePredictableIntegral
          (G.doobDoublyStoppedSign X F Q a b)
          (G.doobMartingalePart X F Q) M) Q :=
      hYInt.sub (hMartingaleTransform.integrable M)
    refine hDifference.congr (ae_of_all Q fun omega => ?_)
    have hDecomposition := congrFun
      (G.discretePredictableIntegral_doobDoublyStoppedSign_source
        X F Q a b M) omega
    simp only [Y, W, Pi.add_apply, Pi.sub_apply] at hDecomposition ⊢
    linarith
  have hIntegralEq :
      (∫ omega, Y omega ∂Q) = ∫ omega, W omega ∂Q := by
    have hPointwise :
        Y = discretePredictableIntegral
          (G.doobDoublyStoppedSign X F Q a b)
          (G.doobMartingalePart X F Q) M + W := by
      funext omega
      exact congrFun
        (G.discretePredictableIntegral_doobDoublyStoppedSign_source
          X F Q a b M) omega
    rw [hPointwise]
    simp only [Pi.add_apply]
    rw [integral_add (hMartingaleTransform.integrable M) hWInt]
    have hZero : ∫ omega,
        discretePredictableIntegral
          (G.doobDoublyStoppedSign X F Q a b)
          (G.doobMartingalePart X F Q) M omega ∂Q = 0 := by
      simpa using
        (hMartingaleTransform.setIntegral_eq (Nat.zero_le M)
          (s := Set.univ) MeasurableSet.univ).symm
    rw [hZero, zero_add]
  have hIntegralW : ∫ omega, W omega ∂Q ≤ C := by
    calc
      ∫ omega, W omega ∂Q ≤ ∫ omega, Y omega ∂Q := hIntegralEq.symm.le
      _ ≤ ∫ omega, (b + 2 * ‖ξ omega‖) ∂Q := by
        apply integral_mono_ae hYInt hBoundInt
        filter_upwards [hYBound] with omega hBound
        exact (le_abs_self _).trans hBound
      _ = b + 2 * Iξ := by
        rw [integral_add (integrable_const b) (hξNormInt.const_mul 2)]
        rw [integral_const_mul]
        simp [Iξ]
      _ = C := by rfl
  have hTailY : Q {omega | R₀ < |Y omega|} ≤
      ENNReal.ofReal (epsilon / 2) := by
    have hMem :=
      G.doobDoublyStoppedSourceIntegral_gain_mem_unitBounded
        (mu := Q) hXAdapted a b
    rw [hLast] at hMem
    simpa only [Y] using hTail _ hMem
  have hExit : Q {omega | b ≤ |Y omega|} ≤
      ENNReal.ofReal (epsilon / 2) := by
    refine (measure_mono ?_).trans hTailY
    intro omega hω
    change b ≤ |Y omega| at hω
    change R₀ < |Y omega|
    dsimp [b] at hω
    linarith
  have hAccumulation : Q {omega | a ≤ W omega} ≤
      ENNReal.ofReal (epsilon / 2) := by
    have hMarkov := ChronologicalGrid.measure_ge_le_of_integrable_nonneg
      hWInt hWNonneg ha hIntegralW
    calc
      Q {omega | a ≤ W omega} ≤ ENNReal.ofReal (C / a) := hMarkov
      _ = ENNReal.ofReal (epsilon / 2) := by
        congr 1
        dsimp [a]
        field_simp
  calc
    Q {omega | a <
        |G.doobPredictableVariation X F Q M omega|} ≤
        Q {omega | a ≤ G.doobPredictableVariation X F Q M omega} := by
      apply measure_mono
      intro omega hω
      change a < |G.doobPredictableVariation X F Q M omega| at hω
      change a ≤ G.doobPredictableVariation X F Q M omega
      rw [abs_of_nonneg
        (G.doobPredictableVariation_nonneg X F Q M omega)] at hω
      exact hω.le
    _ ≤ Q ({omega | b ≤ |Y omega|} ∪ {omega | a ≤ W omega}) :=
      measure_mono (by
        simpa only [Y, W] using
          G.doobPredictableVariation_level_subset_doubleStopping
            X F Q ha.le b M)
    _ ≤ Q {omega | b ≤ |Y omega|} + Q {omega | a ≤ W omega} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (epsilon / 2) +
        ENNReal.ofReal (epsilon / 2) :=
      add_le_add hExit hAccumulation
    _ = ENNReal.ofReal epsilon := by
      rw [← ENNReal.ofReal_add hHalf.le hHalf.le]
      congr 1
      ring

end IsSemimartingale

end FTAPTheorem42
