/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleControl
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Continuous-time martingale processes on finite predictable grids

The finite-grid terminal integral has already been constructed from the
predictable energy measure.  This module constructs its process-valued
counterpart for bounded strongly predictable coefficients.  One grid block
is the coefficient known at the left endpoint multiplied by the difference
of two deterministic stopped martingales.  Its martingale property is proved
directly, including the case where the conditioning time lies before the
left endpoint.  Finite summation then gives a right-continuous martingale
which is constant after the last grid time and whose terminal value is the
discrete predictable integral used by the completed terminal operator.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous-time gain of one bounded predictable coefficient on a
deterministic interval `[s,t]`. -/
noncomputable def deterministicIntervalMartingaleTransform
    (K M : Process Ω) (s t : ℝ≥0) : Process Ω :=
  fun u ω => K s ω *
    (MeasureTheory.stoppedProcess M (fun _ : Ω => (t : WithTop ℝ≥0)) u ω -
      MeasureTheory.stoppedProcess M (fun _ : Ω => (s : WithTop ℝ≥0)) u ω)

/-- A square-integrable terminal value controls all deterministic stopped values. -/
theorem stoppedProcess_const_memLp_two
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : Process Ω} (hM : Martingale M F μ)
    (T : ℝ≥0) (hMT : MemLp (M T) (2 : ENNReal) μ) (t : ℝ≥0) :
    MemLp (MeasureTheory.stoppedProcess M (fun _ => (T : WithTop ℝ≥0)) t)
      (2 : ENNReal) μ := by
  have hEq : MeasureTheory.stoppedProcess M (fun _ => (T : WithTop ℝ≥0)) t =
      M (min t T) := by
    funext ω
    exact stoppedProcess_const_apply M T t ω
  rw [hEq]
  exact (MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
    hM (min_le_right t T) hMT).1

omit [MeasurableSpace Ω] in
/-- Before the left endpoint, one deterministic interval transform is zero. -/
theorem deterministicIntervalMartingaleTransform_eq_zero_of_le
    (K M : Process Ω) {s t u : ℝ≥0} (hst : s ≤ t) (hu : u ≤ s) :
    deterministicIntervalMartingaleTransform K M s t u = 0 := by
  funext ω
  simp only [deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply, Pi.zero_apply,
    min_eq_left (hu.trans hst), min_eq_left hu]
  ring

omit [MeasurableSpace Ω] in
/-- At and after the right endpoint, one interval transform equals its
fully matured weighted increment. -/
theorem deterministicIntervalMartingaleTransform_eq_of_le
    (K M : Process Ω) {s t u : ℝ≥0} (hst : s ≤ t) (hu : t ≤ u) :
    deterministicIntervalMartingaleTransform K M s t u =
      fun ω => K s ω * (M t ω - M s ω) := by
  funext ω
  simp only [deterministicIntervalMartingaleTransform,
    stoppedProcess_const_apply,
    min_eq_right hu, min_eq_right (hst.trans hu)]

/-- The difference of the two deterministic stops appearing in one interval
transform is a true martingale. -/
theorem deterministicStoppedIncrement_isMartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {M : Process Ω} (hM : Martingale M ℱ μ)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u)
    (s t : ℝ≥0) :
    Martingale
      (MeasureTheory.stoppedProcess M (fun _ : Ω => (t : WithTop ℝ≥0)) -
        MeasureTheory.stoppedProcess M (fun _ : Ω => (s : WithTop ℝ≥0)))
      ℱ μ := by
  exact
    (RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hM (isStoppingTime_const ℱ t) hMRight).sub
      (RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        hM (isStoppingTime_const ℱ s) hMRight)

/-- One bounded adapted coefficient, sampled at the deterministic left
endpoint, transforms a right-continuous martingale into a true martingale. -/
theorem deterministicIntervalMartingaleTransform_isMartingale_of_stronglyAdapted
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {K M : Process Ω} {s t : ℝ≥0} {C : ℝ}
    (hst : s ≤ t) (hM : Martingale M ℱ μ)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ᵐ ω ∂μ, |K s ω| ≤ C) :
    Martingale (deterministicIntervalMartingaleTransform K M s t) ℱ μ := by
  let D : Process Ω :=
    MeasureTheory.stoppedProcess M (fun _ : Ω => (t : WithTop ℝ≥0)) -
      MeasureTheory.stoppedProcess M (fun _ : Ω => (s : WithTop ℝ≥0))
  have hD : Martingale D ℱ μ :=
    deterministicStoppedIncrement_isMartingale hM hMRight s t
  have hStrong : StronglyAdapted ℱ
      (deterministicIntervalMartingaleTransform K M s t) := by
    intro u
    by_cases hus : u ≤ s
    · rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
        K M hst hus]
      exact stronglyMeasurable_zero
    · have hsu : s ≤ u := le_of_not_ge hus
      exact ((hK s).mono (ℱ.mono hsu)).mul (hD.stronglyMeasurable u)
  refine ⟨hStrong, ?_⟩
  intro i j hij
  by_cases hjs : j ≤ s
  · rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
      K M hst hjs,
      deterministicIntervalMartingaleTransform_eq_zero_of_le
        K M hst (hij.trans hjs)]
    simp
  by_cases hsi : s ≤ i
  · have hKMeas : StronglyMeasurable[ℱ i] (K s) :=
      (hK s).mono (ℱ.mono hsi)
    have hPull := condExp_stronglyMeasurable_mul_of_bound
      (ℱ.le i) hKMeas (hD.integrable j) C (by
        simpa only [Real.norm_eq_abs] using hKBound)
    filter_upwards [hPull, hD.condExp_ae_eq hij] with ω hPullω hDω
    change μ[K s * D j | ℱ i] ω = K s ω * D i ω
    rw [hPullω, Pi.mul_apply, hDω]
  · have his : i ≤ s := le_of_not_ge hsi
    have hsj : s ≤ j := le_of_not_ge hjs
    have hKMeas : StronglyMeasurable[ℱ s] (K s) :=
      hK s
    have hPull := condExp_stronglyMeasurable_mul_of_bound
      (ℱ.le s) hKMeas (hD.integrable j) C (by
        simpa only [Real.norm_eq_abs] using hKBound)
    have hInnerZero :
        μ[deterministicIntervalMartingaleTransform K M s t j | ℱ s] =ᵐ[μ]
          0 := by
      filter_upwards [hPull, hD.condExp_ae_eq hsj] with ω hPullω hDω
      change μ[K s * D j | ℱ s] ω = 0
      rw [hPullω, Pi.mul_apply, hDω]
      change K s ω *
        (MeasureTheory.stoppedProcess M
            (fun _ : Ω => (t : WithTop ℝ≥0)) s ω -
          MeasureTheory.stoppedProcess M
            (fun _ : Ω => (s : WithTop ℝ≥0)) s ω) = 0
      rw [stoppedProcess_const_apply, stoppedProcess_const_apply,
        min_eq_left hst, min_self]
      simp
    have hTower := condExp_condExp_of_le
      (μ := μ) (m₁ := ℱ i) (m₂ := ℱ s)
      (m₀ := inferInstance) (ℱ.mono his) (ℱ.le s)
      (f := deterministicIntervalMartingaleTransform K M s t j)
    have hOuterZero :
        μ[μ[deterministicIntervalMartingaleTransform K M s t j | ℱ s] |
            ℱ i] =ᵐ[μ] 0 := by
      exact (condExp_congr_ae hInnerZero).trans (by simp)
    have hDirectZero :
        μ[deterministicIntervalMartingaleTransform K M s t j | ℱ i] =ᵐ[μ]
          0 := hTower.symm.trans hOuterZero
    rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
      K M hst his]
    exact hDirectZero

omit [MeasurableSpace Ω] in
/-- One interval transform inherits right continuity from its integrator. -/
theorem deterministicIntervalMartingaleTransform_rightContinuous
    (K M : Process Ω) (s t : ℝ≥0)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u) :
    ∀ ω u, ContinuousWithinAt
      (deterministicIntervalMartingaleTransform K M s t · ω)
      (Set.Ici u) u := by
  intro ω u
  exact ((RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      M hMRight ω u).sub
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
          M hMRight ω u)).const_mul (K s ω)

namespace ChronologicalGrid

variable {N : ℕ} (G : ChronologicalGrid ℝ≥0 N)

/-- The continuous-time finite-grid predictable integral. -/
noncomputable def martingaleIntegralProcess
    (K M : Process Ω) : Process Ω :=
  ∑ k ∈ Finset.range N,
    deterministicIntervalMartingaleTransform K M
      (G.sampledTime k) (G.sampledTime (k + 1))

/-- A bounded strongly adapted coefficient, sampled at the grid's left
endpoints, gives a true continuous-time martingale integral. -/
theorem martingaleIntegralProcess_isMartingale_of_stronglyAdapted
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {K M : Process Ω} {C : ℝ≥0 → ℝ}
    (hM : Martingale M ℱ μ)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u)
    (hK : StronglyAdapted ℱ K)
    (hKBound : ∀ u, ∀ᵐ ω ∂μ, |K u ω| ≤ C u) :
    Martingale (G.martingaleIntegralProcess K M) ℱ μ := by
  unfold martingaleIntegralProcess
  exact Finset.sum_induction
    (fun k => deterministicIntervalMartingaleTransform K M
      (G.sampledTime k) (G.sampledTime (k + 1)))
    (fun X : Process Ω => Martingale X ℱ μ)
    (fun _ _ hA hB => hA.add hB)
    (martingale_zero ℝ ℱ μ)
    (fun k _ => deterministicIntervalMartingaleTransform_isMartingale_of_stronglyAdapted
      (G.sampledTime_mono (Nat.le_succ k)) hM hMRight hK
      (hKBound (G.sampledTime k)))

/-- A bounded strongly predictable finite-grid integral is a true
continuous-time martingale. -/
theorem martingaleIntegralProcess_isMartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {K M : Process Ω} {C : ℝ≥0 → ℝ}
    (hM : Martingale M ℱ μ)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u)
    (hK : IsStronglyPredictable ℱ K)
    (hKBound : ∀ u, ∀ᵐ ω ∂μ, |K u ω| ≤ C u) :
    Martingale (G.martingaleIntegralProcess K M) ℱ μ :=
  G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted
    hM hMRight hK.stronglyAdapted hKBound

omit [MeasurableSpace Ω] in
/-- The finite-grid integral is right-continuous pathwise. -/
theorem martingaleIntegralProcess_rightContinuous
    (K M : Process Ω)
    (hMRight : ∀ ω u,
      ContinuousWithinAt (M · ω) (Set.Ici u) u) :
    ∀ ω u, ContinuousWithinAt (G.martingaleIntegralProcess K M · ω)
      (Set.Ici u) u := by
  intro ω u
  unfold martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply tendsto_finsetSum
  intro k _
  exact deterministicIntervalMartingaleTransform_rightContinuous
    K M (G.sampledTime k) (G.sampledTime (k + 1)) hMRight ω u

omit [MeasurableSpace Ω] in
/-- At the last grid time, the continuous-time integral is exactly the
discrete predictable terminal integral. -/
theorem martingaleIntegralProcess_last
    (K M : Process Ω) :
    G.martingaleIntegralProcess K M (G.sampledTime N) =
      discretePredictableIntegral (G.natSample K) (G.natSample M) N := by
  funext ω
  unfold martingaleIntegralProcess discretePredictableIntegral
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [deterministicIntervalMartingaleTransform_eq_of_le K M
    (G.sampledTime_mono (Nat.le_succ k))
    (G.sampledTime_mono (Nat.succ_le_of_lt hk))]
  rfl

omit [MeasurableSpace Ω] in
/-- The finite-grid integral is constant after the last grid time. -/
theorem martingaleIntegralProcess_eq_last_of_le
    (K M : Process Ω) {u : ℝ≥0} (hu : G.sampledTime N ≤ u) :
    G.martingaleIntegralProcess K M u =
      G.martingaleIntegralProcess K M (G.sampledTime N) := by
  funext ω
  unfold martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [deterministicIntervalMartingaleTransform_eq_of_le K M
      (G.sampledTime_mono (Nat.le_succ k))
      ((G.sampledTime_mono (Nat.succ_le_of_lt hk)).trans hu),
    deterministicIntervalMartingaleTransform_eq_of_le K M
      (G.sampledTime_mono (Nat.le_succ k))
      (G.sampledTime_mono (Nat.succ_le_of_lt hk))]

end ChronologicalGrid

end FTAPTheorem42
