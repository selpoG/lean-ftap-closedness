/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ResidualMartingale
import FTAPTheorem42.Stochastic.Decomposition.Source.CompensatorKernel
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeRightApproximation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Stopping

/-!
# Source-independent finite-grid optional sampling

This module contains the discrete optional-sampling and integral algebra used
by both finite-grid compensator constructions.  The source-specific adapters
only provide the sampled residual, its terminal zero-expectation identity, and
the left-endpoint activation formula.  No source bound, convexification, or
continuous-time process identification is used here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {mu : Measure Ω} [IsFiniteMeasure mu]
  {ℱ : Filtration Nat (inferInstance : MeasurableSpace Ω)}
  {R : Nat → Ω → Real}

/-! ## Pointwise stopped-value bridge -/

omit [MeasurableSpace Ω] [IsFiniteMeasure mu] in
theorem stoppedValue_at_nat_stoppingIndex
    (q : Ω → Nat) :
    MeasureTheory.stoppedValue R
        (fun omega => (q omega : WithTop Nat)) =
      (fun omega => R (q omega) omega) := by
  funext omega
  change R ((q omega : WithTop Nat).untopA) omega = R (q omega) omega
  have hne : (q omega : WithTop Nat) ≠ ⊤ := WithTop.coe_ne_top
  have hindex : (q omega : WithTop Nat).untopA = q omega := by
    rw [WithTop.untopA_eq_untop hne]
    rfl
  rw [hindex]

/-! ## Integrability of a bounded discrete stop -/

theorem integrable_stoppedValue_of_memLp_two
    (hMem : ∀ i, MemLp (R i) (2 : ENNReal) mu)
    (q : Ω → WithTop Nat)
    (hq : IsStoppingTime ℱ q)
    (N : Nat) (hq_le : ∀ omega, q omega ≤ (N : WithTop Nat)) :
    Integrable (MeasureTheory.stoppedValue R q) mu := by
  exact MeasureTheory.integrable_stoppedValue ℕ hq
    (fun i => (hMem i).integrable (by norm_num)) hq_le

/-! ## Zero expectation at a bounded discrete stop -/

theorem integral_stoppedValue_eq_zero_of_martingale
    (hMart : Martingale R ℱ mu)
    (N : Nat) (hTerminalZero : (∫ omega, R N omega ∂mu) = 0)
    (q : Ω → WithTop Nat)
    (hq : IsStoppingTime ℱ q)
    (hq_le : ∀ omega, q omega ≤ (N : WithTop Nat)) :
    (∫ omega, MeasureTheory.stoppedValue R q omega ∂mu) = 0 := by
  have hStopEq : MeasureTheory.stoppedValue R q =ᵐ[mu]
      mu[R N | hq.measurableSpace] := by
    exact hMart.stoppedValue_ae_eq_condExp_of_le_const hq hq_le
  have hIntegralStop :
      (∫ omega, MeasureTheory.stoppedValue R q omega ∂mu) =
        ∫ omega, R N omega ∂mu := by
    calc
      (∫ omega, MeasureTheory.stoppedValue R q omega ∂mu) =
          ∫ omega, mu[R N | hq.measurableSpace] omega ∂mu :=
        integral_congr_ae hStopEq
      _ = ∫ omega, R N omega ∂mu :=
        integral_condExp hq.measurableSpace_le
  rw [hIntegralStop, hTerminalZero]

/-! ## The source/row integral algebra -/

omit [IsFiniteMeasure mu] in
theorem integrable_and_integral_eq_of_activation
    {pTau pSigma sourceSigma residualSigma : Ω → Real}
    (hResidualInt : Integrable residualSigma mu)
    (hSourceInt : Integrable sourceSigma mu)
    (hResidualZero : (∫ omega, residualSigma omega ∂mu) = 0)
    (hActivation : pTau = pSigma)
    (hResidualEq : residualSigma = sourceSigma - pSigma) :
    Integrable pTau mu ∧
      (∫ omega, pTau omega ∂mu) = ∫ omega, sourceSigma omega ∂mu := by
  have hPInt : Integrable pTau mu := by
    have hEq : pTau =ᵐ[mu] sourceSigma - residualSigma := by
      filter_upwards [] with omega
      rw [hActivation, hResidualEq]
      simp only [Pi.sub_apply]
      ring
    exact (hSourceInt.sub hResidualInt).congr hEq.symm
  refine ⟨hPInt, ?_⟩
  have hPointwise : pTau =ᵐ[mu] sourceSigma - residualSigma := by
    filter_upwards [] with omega
    rw [hActivation, hResidualEq]
    simp only [Pi.sub_apply]
    ring
  calc
    (∫ omega, pTau omega ∂mu) =
        ∫ omega, (sourceSigma omega - residualSigma omega) ∂mu :=
      integral_congr_ae hPointwise
    _ = (∫ omega, sourceSigma omega ∂mu) -
        ∫ omega, residualSigma omega ∂mu :=
      integral_sub hSourceInt hResidualInt
    _ = ∫ omega, sourceSigma omega ∂mu := by
        rw [hResidualZero, sub_zero]

/-! ## Source-independent left-endpoint activation -/

omit [MeasurableSpace Ω] [IsFiniteMeasure mu] in
theorem finiteGridPredictableCompensatorProcess_at_tau_eq_at_gridTime
    (T : NNReal) (τ σ : Ω → NNReal) (q : Ω → Nat)
    (d : Nat → Ω → Real) (r : Nat) (omega : Ω)
    (hSigmaGrid : ∀ omega, σ omega =
      (grid T r).sampledTime (q omega))
    (hTauSigma : ∀ omega, τ omega ≤
      (grid T r).sampledTime (q omega))
    (hIndexLe : ∀ omega, q omega ≤ size T r)
    (hIndexCeil : ∀ omega, q omega =
      Nat.ceil (τ omega * (r.factorial : NNReal)))
    (hZero : ∀ k, k < size T r →
      (grid T r).sampledTime k = (grid T r).sampledTime (k + 1) →
        d k = 0) :
    finiteGridPredictableCompensatorProcess T d r (τ omega) omega =
      finiteGridPredictableCompensatorProcess T d r
        (σ omega) omega := by
  let qω := q omega
  have hqle : qω ≤ size T r := hIndexLe omega
  have hqceil : qω = Nat.ceil (τ omega * (r.factorial : NNReal)) :=
    hIndexCeil omega
  have hSigmaGridω : σ omega = (grid T r).sampledTime qω :=
    hSigmaGrid omega
  have hTauSigmaω : τ omega ≤ (grid T r).sampledTime qω :=
    hTauSigma omega
  rw [hSigmaGridω]
  unfold finiteGridPredictableCompensatorProcess
  apply Finset.sum_congr rfl
  intro k hk
  have hkSize : k < size T r := Finset.mem_range.mp hk
  by_cases hkq : k < qω
  · have hkceil : k < Nat.ceil (τ omega * (r.factorial : NNReal)) := by
      simpa only [← hqceil] using hkq
    have hkreal : (k : NNReal) <
        τ omega * (r.factorial : NNReal) :=
      (Nat.lt_ceil (α := NNReal)).mp hkceil
    have hkdiv : (k : NNReal) / (r.factorial : NNReal) < τ omega := by
      apply (div_lt_iff₀ (show (0 : NNReal) <
        (r.factorial : NNReal) by positivity)).2
      simpa [mul_comm] using hkreal
    have hGridK : (grid T r).sampledTime k < τ omega := by
      unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
      simp only [min_eq_left hkSize.le, grid_time]
      exact min_lt_of_left_lt hkdiv
    have hGridKQ : (grid T r).sampledTime k <
        (grid T r).sampledTime qω :=
      hGridK.trans_le hTauSigmaω
    simp only [finiteGridCompensatorStepTerm,
      ite_eq_left hGridK, ite_eq_left hGridKQ]
  · have hqk : qω ≤ k := Nat.le_of_not_gt hkq
    have hGridQK : (grid T r).sampledTime qω ≤
        (grid T r).sampledTime k :=
      (grid T r).sampledTime_mono hqk
    have hGridK_not_tau : ¬(grid T r).sampledTime k < τ omega :=
      not_lt_of_ge (hTauSigmaω.trans hGridQK)
    have hGridK_not_q : ¬(grid T r).sampledTime k <
        (grid T r).sampledTime qω := not_lt_of_ge hGridQK
    by_cases hGridEq : (grid T r).sampledTime k =
        (grid T r).sampledTime (k + 1)
    · have hdk := hZero k hkSize hGridEq
      simp only [finiteGridCompensatorStepTerm,
        ite_eq_right hGridK_not_tau, ite_eq_right hGridK_not_q, hdk]
    · simp only [finiteGridCompensatorStepTerm,
        ite_eq_right hGridK_not_tau,
        ite_eq_right hGridK_not_q]

end HorizonFactorialGrid

end FTAPTheorem42
