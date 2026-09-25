/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.FiniteGridAdaptedElementaryStrategy
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobVariationStopping

/-!
# Double stopping of finite-grid Doob sign integrals

After stopping the predictable sign at a variation level, we stop it once
more at the first exit of its source integral from a symmetric interval.
The first-exit gate is a finite product of past-event indicators, hence is
known at the left endpoint of the next grid interval.  This module records
the gate semantics and the deterministic one-step overshoot bound for the
doubly stopped source integral.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The source integral whose sign has already been stopped at variation
level `a`. -/
noncomputable def doobVariationStoppedSourceIntegral
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a : Real) : Nat → Omega → Real :=
  discretePredictableIntegral
    (G.doobVariationStoppedSign S F mu a) (G.natSample S)

/-- The variation-stopped source integral is adapted to the sampled
filtration. -/
theorem stronglyAdapted_doobVariationStoppedSourceIntegral
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hSAdapted : StronglyAdapted F S) (a : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobVariationStoppedSourceIntegral S F mu a) := by
  exact DiscretePredictableIntegral.stronglyAdapted_of_stronglyAdapted
    (G.stronglyAdapted_doobVariationStoppedSign S F mu a)
    (fun n => hSAdapted (G.sampledTime n))

/-- Indicator that the variation-stopped source integral has stayed inside
`(-b,b)` through grid index `n`. -/
noncomputable def doobSourceFirstExitGate
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) : Nat → Omega → Real :=
  fun n omega => ∏ j ∈ Finset.range (n + 1),
    if |G.doobVariationStoppedSourceIntegral S F mu a j omega| < b then
      1
    else 0

/-- The first-exit gate equals one exactly while all preceding values of the
variation-stopped source integral lie inside `(-b,b)`. -/
theorem doobSourceFirstExitGate_eq_one_iff
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega) :
    G.doobSourceFirstExitGate S F mu a b n omega = 1 ↔
      ∀ j ∈ Finset.range (n + 1),
        |G.doobVariationStoppedSourceIntegral S F mu a j omega| < b := by
  classical
  unfold doobSourceFirstExitGate
  constructor
  · intro hGate j hj
    by_contra hnot
    have hZero : (∏ k ∈ Finset.range (n + 1),
        if |G.doobVariationStoppedSourceIntegral S F mu a k omega| < b then
          (1 : Real) else 0) = 0 := by
      apply Finset.prod_eq_zero hj
      simp [hnot]
    exact zero_ne_one (hZero.symm.trans hGate)
  · intro hInside
    apply Finset.prod_eq_one
    intro j hj
    simp [hInside j hj]

/-- The first-exit gate only takes the values zero and one. -/
theorem doobSourceFirstExitGate_eq_zero_or_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega) :
    G.doobSourceFirstExitGate S F mu a b n omega = 0 ∨
      G.doobSourceFirstExitGate S F mu a b n omega = 1 := by
  classical
  by_cases hInside : ∀ j ∈ Finset.range (n + 1),
      |G.doobVariationStoppedSourceIntegral S F mu a j omega| < b
  · exact Or.inr ((G.doobSourceFirstExitGate_eq_one_iff
      S F mu a b n omega).2 hInside)
  · left
    push Not at hInside
    obtain ⟨j, hj, hnot⟩ := hInside
    unfold doobSourceFirstExitGate
    apply Finset.prod_eq_zero hj
    simp [hnot]

/-- The first-exit gate is adapted to the sampled filtration. -/
theorem stronglyAdapted_doobSourceFirstExitGate
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hSAdapted : StronglyAdapted F S) (a b : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobSourceFirstExitGate S F mu a b) := by
  intro n
  unfold doobSourceFirstExitGate
  have hProd : StronglyMeasurable[G.sampledFiltration F n]
      ((∏ j ∈ Finset.range (n + 1), fun omega =>
        if |G.doobVariationStoppedSourceIntegral S F mu a j omega| < b then
          1
        else 0) : Omega → Real) := by
    apply Finset.stronglyMeasurable_prod
    intro j hj
    rw [Finset.mem_range] at hj
    have hX : StronglyMeasurable[G.sampledFiltration F n]
        (G.doobVariationStoppedSourceIntegral S F mu a j) :=
      (G.stronglyAdapted_doobVariationStoppedSourceIntegral hSAdapted a j).mono
        ((G.sampledFiltration F).mono (Nat.lt_succ_iff.mp hj))
    let B : Set Omega :=
      {omega | |G.doobVariationStoppedSourceIntegral S F mu a j omega| < b}
    have hB : MeasurableSet[G.sampledFiltration F n] B := by
      change MeasurableSet[G.sampledFiltration F n]
        ((fun omega =>
          |G.doobVariationStoppedSourceIntegral S F mu a j omega|) ⁻¹' Iio b)
      exact (by
        simpa only [Real.norm_eq_abs] using hX.norm.measurable measurableSet_Iio)
    exact StronglyMeasurable.piecewise hB stronglyMeasurable_const
      stronglyMeasurable_const
  convert hProd using 1
  funext omega
  simp only [Finset.prod_apply]

/-- The predictable sign stopped both at variation level `a` and at the
first source-integral exit from `(-b,b)`. -/
noncomputable def doobDoublyStoppedSign
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) : Nat → Omega → Real :=
  G.doobSourceFirstExitGate S F mu a b *
    G.doobVariationStoppedSign S F mu a

/-- The doubly stopped sign is adapted. -/
theorem stronglyAdapted_doobDoublyStoppedSign
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hSAdapted : StronglyAdapted F S) (a b : Real) :
    StronglyAdapted (G.sampledFiltration F)
      (G.doobDoublyStoppedSign S F mu a b) :=
  (G.stronglyAdapted_doobSourceFirstExitGate hSAdapted a b).mul
    (G.stronglyAdapted_doobVariationStoppedSign S F mu a)

/-- The doubly stopped sign remains bounded by one. -/
theorem abs_doobDoublyStoppedSign_le_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega) :
    |G.doobDoublyStoppedSign S F mu a b n omega| ≤ 1 := by
  rcases G.doobSourceFirstExitGate_eq_zero_or_one
      S F mu a b n omega with hGate | hGate
  · simp [doobDoublyStoppedSign, hGate]
  · simpa [doobDoublyStoppedSign, hGate] using
      G.abs_doobVariationStoppedSign_le_one S F mu a n omega

/-- The source integral of the doubly stopped sign. -/
noncomputable def doobDoublyStoppedSourceIntegral
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) : Nat → Omega → Real :=
  discretePredictableIntegral
    (G.doobDoublyStoppedSign S F mu a b) (G.natSample S)

/-- While the first-exit gate is one, the doubly stopped source integral
equals the variation-stopped source integral. -/
theorem doobDoublyStoppedSourceIntegral_eq_of_gate_eq_one
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) (n : Nat) (omega : Omega)
    (hGate : G.doobSourceFirstExitGate S F mu a b n omega = 1) :
    G.doobDoublyStoppedSourceIntegral S F mu a b n omega =
      G.doobVariationStoppedSourceIntegral S F mu a n omega := by
  unfold doobDoublyStoppedSourceIntegral
    doobVariationStoppedSourceIntegral discretePredictableIntegral
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hInside := (G.doobSourceFirstExitGate_eq_one_iff
    S F mu a b n omega).1 hGate
  have hGateK : G.doobSourceFirstExitGate S F mu a b k omega = 1 :=
    (G.doobSourceFirstExitGate_eq_one_iff S F mu a b k omega).2 fun j hj =>
      hInside j (Finset.mem_range.2
        ((Finset.mem_range.1 hj).trans_le (Nat.succ_le_succ hk.le)))
  simp [doobDoublyStoppedSign, hGateK]

/-- The doubly stopped source integral has only a one-increment overshoot
beyond its exit level. -/
theorem ae_abs_doobDoublyStoppedSourceIntegral_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu) (a : Real)
    {b : Real} (hb : 0 ≤ b) :
    ∀ᵐ omega ∂mu, ∀ n,
      |G.doobDoublyStoppedSourceIntegral S F mu a b n omega| ≤
        b + 2 * max source.bound 0 := by
  filter_upwards [G.ae_norm_natSample_increment_le source] with
      omega hIncrement
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
      · simp [doobDoublyStoppedSign, hGate, ih]
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
          _ < b + 1 * (2 * max source.bound 0) := by
            apply add_lt_add_of_lt_of_le
            · simpa [hCurrent] using hInside
            · exact mul_le_mul
                (G.abs_doobDoublyStoppedSign_le_one S F mu a b n omega)
                (by simpa only [Real.norm_eq_abs] using hIncrement n)
                (abs_nonneg _) zero_le_one
          _ = b + 2 * max source.bound 0 := by ring).le

/-- If the first-exit gate has vanished, the frozen doubly stopped integral
has absolute value at least the exit level. -/
theorem le_abs_doobDoublyStoppedSourceIntegral_of_gate_eq_zero
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) (a b : Real) :
    ∀ n omega,
      G.doobSourceFirstExitGate S F mu a b n omega = 0 →
        b ≤ |G.doobDoublyStoppedSourceIntegral S F mu a b n omega| := by
  intro n
  induction n with
  | zero =>
      intro omega hGate
      have hnot : ¬|G.doobVariationStoppedSourceIntegral S F mu a 0 omega| < b := by
        intro hInside
        have hOne := (G.doobSourceFirstExitGate_eq_one_iff
          S F mu a b 0 omega).2 fun j hj => by
            have hjZero : j = 0 := by simpa using Finset.mem_range.1 hj
            simpa [hjZero] using hInside
        rw [hGate] at hOne
        norm_num at hOne
      have hb : b ≤ 0 := by
        simpa [doobVariationStoppedSourceIntegral,
          discretePredictableIntegral] using le_of_not_gt hnot
      simpa [doobDoublyStoppedSourceIntegral,
        discretePredictableIntegral] using hb
  | succ n ih =>
      intro omega hGateSucc
      rcases G.doobSourceFirstExitGate_eq_zero_or_one
          S F mu a b n omega with hGate | hGate
      · have hIntegral :
            G.doobDoublyStoppedSourceIntegral S F mu a b (n + 1) omega =
              G.doobDoublyStoppedSourceIntegral S F mu a b n omega := by
          rw [show G.doobDoublyStoppedSourceIntegral S F mu a b (n + 1) omega =
              G.doobDoublyStoppedSourceIntegral S F mu a b n omega +
                G.doobDoublyStoppedSign S F mu a b n omega *
                  (G.natSample S (n + 1) omega - G.natSample S n omega) by
            simp [doobDoublyStoppedSourceIntegral,
              discretePredictableIntegral_succ]]
          simp [doobDoublyStoppedSign, hGate]
        rw [hIntegral]
        exact ih omega hGate
      · have hInsideN := (G.doobSourceFirstExitGate_eq_one_iff
          S F mu a b n omega).1 hGate
        have hnotNext :
            ¬|G.doobVariationStoppedSourceIntegral S F mu a (n + 1) omega| < b := by
          intro hNext
          have hOneSucc := (G.doobSourceFirstExitGate_eq_one_iff
            S F mu a b (n + 1) omega).2 fun j hj => by
              rw [Finset.mem_range] at hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjn | rfl
              · exact hInsideN j (Finset.mem_range.2 hjn)
              · exact hNext
          rw [hGateSucc] at hOneSucc
          norm_num at hOneSucc
        have hIntegral :
            G.doobDoublyStoppedSourceIntegral S F mu a b (n + 1) omega =
              G.doobVariationStoppedSourceIntegral S F mu a (n + 1) omega := by
          rw [show G.doobDoublyStoppedSourceIntegral S F mu a b (n + 1) omega =
              G.doobDoublyStoppedSourceIntegral S F mu a b n omega +
                G.doobDoublyStoppedSign S F mu a b n omega *
                  (G.natSample S (n + 1) omega - G.natSample S n omega) by
            simp [doobDoublyStoppedSourceIntegral,
              discretePredictableIntegral_succ]]
          rw [G.doobDoublyStoppedSourceIntegral_eq_of_gate_eq_one
            S F mu a b n omega hGate]
          simp [doobDoublyStoppedSign, hGate,
            doobVariationStoppedSourceIntegral,
            discretePredictableIntegral_succ]
        rw [hIntegral]
        exact le_of_not_gt hnotNext

/-- The doubly stopped source integral is realized by a unit-bounded
predictable elementary strategy on the grid. -/
theorem doobDoublyStoppedSourceIntegral_gain_mem_unitBounded
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hSAdapted : StronglyAdapted F S) (a b : Real) :
    (fun omega => G.doobDoublyStoppedSourceIntegral S F mu a b N omega) ∈
      UnitBoundedElementaryGainSet S F (G.sampledTime N) := by
  let hK := G.stronglyAdapted_doobDoublyStoppedSign (mu := mu) hSAdapted a b
  refine ⟨G.adaptedElementaryStrategy F
    (G.doobDoublyStoppedSign S F mu a b) hK, ?_, ?_⟩
  · exact G.abs_adaptedElementaryStrategy_integrand_le F
      (G.doobDoublyStoppedSign S F mu a b) hK zero_le_one
      (G.abs_doobDoublyStoppedSign_le_one S F mu a b)
  · funext omega
    exact (G.adaptedElementaryStrategy_gain_last S F
      (G.doobDoublyStoppedSign S F mu a b) hK omega).symm

end ChronologicalGrid

namespace IsSemimartingale

/-- Doubly stopped source integrals over all grids and stopping levels with
a common terminal time are uniformly bounded in probability. -/
theorem uniformly_boundedInProbability_doobDoublyStoppedSourceIntegrals
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hS : IsSemimartingale S F mu) (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R : Real, 0 ≤ R ∧
        ∀ {M : Nat} (G : ChronologicalGrid NNReal M) (a b : Real),
          G.sampledTime M = T →
          mu {omega | R <
            |G.doobDoublyStoppedSourceIntegral S F mu a b M omega|} ≤
            ENNReal.ofReal epsilon := by
  intro epsilon hepsilon
  obtain ⟨R, hR, hTail⟩ :=
    hS.claimSetBoundedInProbability_unitBoundedElementaryGainSet T
      epsilon hepsilon
  refine ⟨R, hR, ?_⟩
  intro M G a b hLast
  have hMem := G.doobDoublyStoppedSourceIntegral_gain_mem_unitBounded (mu := mu)
    source.stronglyAdapted a b
  rw [hLast] at hMem
  exact hTail _ hMem

end IsSemimartingale

end FTAPTheorem42
