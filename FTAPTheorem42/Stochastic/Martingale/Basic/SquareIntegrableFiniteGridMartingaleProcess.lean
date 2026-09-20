/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcess

/-!
# Finite-grid transforms with square-integrable coefficients

A coefficient sampled at the left endpoint of a deterministic interval need
not be bounded in order to define a true martingale transform.  It is enough
that both the coefficient and every value of the source martingale belong to
`L²`: Holder's inequality then makes each transformed value integrable, and
the conditional-expectation pull-out identity proves the martingale property.

This is the `L¹` finite-grid input needed by quadratic approximations of a
general finite-horizon `M²` martingale.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- One square-integrable adapted coefficient, sampled at a deterministic
left endpoint, transforms a right-continuous `M²` martingale into a true
martingale. -/
theorem deterministicIntervalMartingaleTransform_isMartingale_of_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {K M : Process Omega} {s t : NNReal}
    (hst : s <= t) (hM : Martingale M F mu)
    (hMRight : forall omega u,
      ContinuousWithinAt (M · omega) (Ici u) u)
    (hMLp : forall u, MemLp (M u) (2 : ENNReal) mu)
    (hK : StronglyAdapted F K)
    (hKLp : MemLp (K s) (2 : ENNReal) mu) :
    Martingale (deterministicIntervalMartingaleTransform K M s t) F mu := by
  let D : Process Omega :=
    MeasureTheory.stoppedProcess M (fun _ : Omega => (t : WithTop NNReal)) -
      MeasureTheory.stoppedProcess M (fun _ : Omega => (s : WithTop NNReal))
  have hD : Martingale D F mu :=
    deterministicStoppedIncrement_isMartingale hM hMRight s t
  have hStoppedMemLp (c u : NNReal) : MemLp
      (MeasureTheory.stoppedProcess M
        (fun _ : Omega => (c : WithTop NNReal)) u)
      (2 : ENNReal) mu := by
    rw [show MeasureTheory.stoppedProcess M
        (fun _ : Omega => (c : WithTop NNReal)) u = M (min u c) by
      funext omega
      exact stoppedProcess_const_apply M c u omega]
    exact hMLp (min u c)
  have hDMemLp (u : NNReal) : MemLp (D u) (2 : ENNReal) mu := by
    exact (hStoppedMemLp t u).sub (hStoppedMemLp s u)
  have hProductIntegrable (u : NNReal) : Integrable (K s * D u) mu :=
    hKLp.integrable_mul (hDMemLp u)
  have hStrong : StronglyAdapted F
      (deterministicIntervalMartingaleTransform K M s t) := by
    intro u
    by_cases hus : u <= s
    · rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
        K M hst hus]
      exact stronglyMeasurable_zero
    · have hsu : s <= u := le_of_not_ge hus
      exact ((hK s).mono (F.mono hsu)).mul (hD.stronglyMeasurable u)
  refine ⟨hStrong, ?_⟩
  intro i j hij
  by_cases hjs : j <= s
  · rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
      K M hst hjs,
      deterministicIntervalMartingaleTransform_eq_zero_of_le
        K M hst (hij.trans hjs)]
    simp
  by_cases hsi : s <= i
  · have hKMeas : StronglyMeasurable[F i] (K s) :=
      (hK s).mono (F.mono hsi)
    have hPull := condExp_mul_of_stronglyMeasurable_left
      hKMeas (hProductIntegrable j)
      ((hDMemLp j).integrable (by norm_num))
    filter_upwards [hPull, hD.condExp_ae_eq hij] with omega hPullOmega hDOmega
    change mu[K s * D j | F i] omega = K s omega * D i omega
    rw [hPullOmega, Pi.mul_apply, hDOmega]
  · have his : i <= s := le_of_not_ge hsi
    have hsj : s <= j := le_of_not_ge hjs
    have hPull := condExp_mul_of_stronglyMeasurable_left
      (hK s) (hProductIntegrable j)
      ((hDMemLp j).integrable (by norm_num))
    have hInnerZero :
        mu[deterministicIntervalMartingaleTransform K M s t j | F s] =ᵐ[mu]
          0 := by
      filter_upwards [hPull, hD.condExp_ae_eq hsj]
        with omega hPullOmega hDOmega
      change mu[K s * D j | F s] omega = 0
      rw [hPullOmega, Pi.mul_apply, hDOmega]
      change K s omega *
        (MeasureTheory.stoppedProcess M
            (fun _ : Omega => (t : WithTop NNReal)) s omega -
          MeasureTheory.stoppedProcess M
            (fun _ : Omega => (s : WithTop NNReal)) s omega) = 0
      rw [stoppedProcess_const_apply, stoppedProcess_const_apply,
        min_eq_left hst, min_self]
      simp
    have hTower := condExp_condExp_of_le
      (μ := mu) (m₁ := F i) (m₂ := F s)
      (m₀ := inferInstance) (F.mono his) (F.le s)
      (f := deterministicIntervalMartingaleTransform K M s t j)
    have hOuterZero :
        mu[mu[deterministicIntervalMartingaleTransform K M s t j | F s] |
            F i] =ᵐ[mu] 0 :=
      (condExp_congr_ae hInnerZero).trans (by simp)
    have hDirectZero :
        mu[deterministicIntervalMartingaleTransform K M s t j | F i] =ᵐ[mu]
          0 :=
      hTower.symm.trans hOuterZero
    rw [deterministicIntervalMartingaleTransform_eq_zero_of_le
      K M hst his]
    exact hDirectZero

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- A finite-grid transform with square-integrable adapted coefficients is a
true martingale.  No deterministic coefficient bound is used. -/
theorem martingaleIntegralProcess_isMartingale_of_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {K M : Process Omega}
    (hM : Martingale M F mu)
    (hMRight : forall omega u,
      ContinuousWithinAt (M · omega) (Ici u) u)
    (hMLp : forall u, MemLp (M u) (2 : ENNReal) mu)
    (hK : StronglyAdapted F K)
    (hKLp : forall u, MemLp (K u) (2 : ENNReal) mu) :
    Martingale (G.martingaleIntegralProcess K M) F mu := by
  unfold martingaleIntegralProcess
  exact Finset.sum_induction
    (fun k => deterministicIntervalMartingaleTransform K M
      (G.sampledTime k) (G.sampledTime (k + 1)))
    (fun X : Process Omega => Martingale X F mu)
    (fun _ _ hA hB => hA.add hB)
    (martingale_zero Real F mu)
    (fun k _ =>
      deterministicIntervalMartingaleTransform_isMartingale_of_memLp_two
        (G.sampledTime_mono (Nat.le_succ k)) hM hMRight hMLp hK
        (hKLp (G.sampledTime k)))

end ChronologicalGrid

end FTAPTheorem42
