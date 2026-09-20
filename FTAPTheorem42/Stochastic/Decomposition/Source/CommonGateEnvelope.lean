/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobVariationEnvelopeTightness
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGate

/-!
# Common gates under a square-integrable envelope

This module consumes the envelope finite-grid variation estimate to construct
one common stopping-time gate and one forward-convex coefficient family.  The
bounded-source common-stop row decomposition remains a separate boundary: no
deterministic source bound is introduced here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-!
The row-free part of the envelope common-stop boundary.  The gate, its
forward-convex coefficients, and the common stopping times are all results of
the producer below.  Stopped martingale/residual rows are deliberately not
fields here: their analytic estimates are supplied by subsequent row constructions.
-/

structure EnvelopeDominatedCommonGateEndpoint
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (ξ : Omega → Real) (eta : Real)
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (R : Omega → Real) : Prop where
  eta_pos : 0 < eta
  a_pos : 0 < a
  envelope_memLp : MemLp ξ (2 : ENNReal) mu
  envelope_bound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖
  selection_strictMono : StrictMono selection
  selection_error : ∀ k, mu {omega |
      (1 / 6 : Real) ≤ dist (((u (selection k)).apply (fun r =>
        variationGateTerminal a T r S F mu)) omega) (R omega)} ≤
      ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1)))
  alphaSeq_eq : ∀ k omega, alphaSeq k omega = min (T : WithTop NNReal)
    (LeftContinuousHittingTime.strictHittingAfter
      (fun t omega => -variationGateConvexRow u (selection k) a T S F mu t omega)
      (-1 / 2) omega)
  alphaSeq_le_T : ∀ k omega, alphaSeq k omega ≤ (T : WithTop NNReal)
  alphaSeq_stopping : ∀ k, IsStoppingTime F (alphaSeq k)
  alpha_stopping : IsStoppingTime F alpha
  alpha_eq_iInf : ∀ omega, alpha omega = ⨅ k, alphaSeq k omega
  alpha_le_alphaSeq : ∀ k omega, alpha omega ≤ alphaSeq k omega
  alpha_measure : mu {omega | alpha omega < (T : WithTop NNReal)} ≤
    ENNReal.ofReal (4 * eta)
  gate_terminal_nonneg_le_one : ∀ n omega,
    0 ≤ (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∧
      (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ≤ 1
  gate_terminal_memLp : ∀ n,
    MemLp ((u n).apply (fun r => variationGateTerminal a T r S F mu))
      (2 : ENNReal) mu
  gate_limit_inMeasure : TendstoInMeasure mu
    (fun n omega => (u n).apply
      (fun r => variationGateTerminal a T r S F mu) omega)
    atTop R
  gate_limit_ae : ∀ᵐ omega ∂mu, Tendsto
    (fun n => (u n).apply (fun r => variationGateTerminal a T r S F mu) omega)
    atTop (𝓝 (R omega))

theorem exists_commonGate_of_memLp_two_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real)
    (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      EnvelopeDominatedCommonGateEndpoint
        (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R := by
  classical
  let hBIP : BoundedInProbability mu
      (fun r => terminalDoobVariation T r S F mu) := by
    intro epsilon hepsilon
    obtain ⟨R, hR, hTail⟩ :=
      hS.uniformly_boundedInProbability_doobPredictableVariations_of_memLp_two_envelope
        hSAdapted ξ hξ hSBound T epsilon hepsilon
    refine ⟨R, hR, ?_⟩
    intro r
    exact hTail (grid T r) (sampledTime_size T r)
  obtain ⟨B, hB, hTail⟩ := hBIP eta heta
  let a : Real := B + 1
  have ha : 0 ≤ a := by linarith
  have haPos : 0 < a := by linarith
  have hGateTail : ∀ r, mu {omega |
      variationGateTerminal a T r S F mu omega = 0} ≤
      ENNReal.ofReal eta := by
    intro r
    apply measure_variationGateTerminal_zero_le
      ha T r
    intro r
    simpa [a] using hTail r
  let x : Nat → Lp Real 2 mu := fun r =>
    variationGateTerminalToLp (S := S) (F := F) (mu := mu)
      a T r
  have hx : ∀ r, ‖x r‖ ≤ 1 := by
    intro r
    exact variationGateTerminalToLp_norm_le a T r
  obtain ⟨gLimit, hgLimit⟩ :=
    TailConvexWeights.exists_tendsto_tailNormSqNearMinimizers hx (by norm_num)
  let v₀ : ∀ n, TailConvexWeights n :=
    TailConvexWeights.tailNormSqNearMinimizers x
  have hg₀ : Tendsto (fun n => (v₀ n).applyVector x)
      atTop (𝓝 gLimit) := hgLimit
  have hInMeasure₀ : TendstoInMeasure mu
      (fun n => (v₀ n).apply (fun r =>
        variationGateTerminal a T r S F mu))
      atTop (gLimit : Omega → Real) := by
    have hLp := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hg₀
    refine TendstoInMeasure.congr_left ?_ hLp
    intro n
    exact (v₀ n).applyVector_coeFn_ae x
      (fun r => variationGateTerminal a T r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_variationGateTerminal a T r))
  obtain ⟨cutoff, hcutoff, hAE₀⟩ :=
    exists_strictMono_tendstoAE_of_countable_tendstoInMeasure
      (f := fun n _ => (v₀ n).apply
        (fun r => variationGateTerminal a T r S F mu))
      (g := fun _ => (gLimit : Omega → Real))
      (fun _ => hInMeasure₀)
  have hcut_ge : ∀ n, n ≤ cutoff n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ihn =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ihn
          (hcutoff (Nat.lt_succ_self n)))
  let u : ∀ n, TailConvexWeights n := fun n =>
    (v₀ (cutoff n)).mono (hcut_ge n)
  have hAE : ∀ᵐ omega ∂mu, Tendsto
      (fun n => (u n).apply
        (fun r => variationGateTerminal a T r S F mu) omega)
      atTop (𝓝 ((gLimit : Omega → Real) omega)) := by
    filter_upwards [hAE₀ 0] with omega homega
    simpa [u, TailConvexWeights.mono_apply] using homega
  have hLpU : Tendsto (fun n => (u n).applyVector x)
      atTop (𝓝 gLimit) := by
    simpa [Function.comp_def, u, TailConvexWeights.applyVector_mono] using
      hg₀.comp hcutoff.tendsto_atTop
  have hInMeasureU : TendstoInMeasure mu
      (fun n omega => (u n).apply
        (fun r => variationGateTerminal a T r S F mu) omega)
      atTop (gLimit : Omega → Real) := by
    have hLp := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLpU
    refine TendstoInMeasure.congr_left ?_ hLp
    intro n
    exact (u n).applyVector_coeFn_ae x
      (fun r => variationGateTerminal a T r S F mu)
      (fun r => MemLp.coeFn_toLp
        (memLp_two_variationGateTerminal a T r))
  let R : Omega → Real := gLimit
  have hRbounds : ∀ᵐ omega ∂mu, 0 ≤ R omega ∧ R omega ≤ 1 := by
    filter_upwards [hAE] with omega hω
    have hrowBounds : ∀ n, 0 ≤
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∧
        (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ≤ 1 := by
      intro n
      exact variationGateConvexRow_nonneg_le_one u n a T S F mu T omega
    exact ⟨ge_of_tendsto hω (Filter.Eventually.of_forall fun n =>
      (hrowBounds n).1), le_of_tendsto hω (Filter.Eventually.of_forall fun n =>
      (hrowBounds n).2)⟩
  have hGateIntegral : ∀ r, 1 - eta ≤
      ∫ omega, variationGateTerminal a T r S F mu omega ∂mu := by
    intro r
    let Z : Set Omega := {omega |
      variationGateTerminal a T r S F mu omega = 0}
    have hZ : MeasurableSet Z := by
      change MeasurableSet (variationGateTerminal a T r S F mu ⁻¹' ({0} : Set Real))
      exact (stronglyMeasurable_variationGateTerminal a T r).measurable
        (measurableSet_singleton 0)
    have hZbound : mu.real Z ≤ eta := by
      rw [measureReal_def]
      have hto : (mu Z).toReal ≤ (ENNReal.ofReal eta).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _)
          ENNReal.ofReal_ne_top).2 (by simpa [Z] using hGateTail r)
      simpa [heta.le] using hto
    have hInd : variationGateTerminal a T r S F mu =
        Zᶜ.indicator (fun _ => (1 : Real)) := by
      funext omega
      by_cases hz : variationGateTerminal a T r S F mu omega = 0
      · simp [Z, hz]
      · have h01 := variationGateProcess_eq_zero_or_one
          a T r S F mu T omega
        rcases h01 with h0 | h1
        · exact False.elim (hz h0)
        · rw [variationGateTerminal]
          simp [Z, hz, h1]
    rw [hInd]
    have hIntInd : (∫ omega, Zᶜ.indicator (fun _ => (1 : Real)) omega ∂mu) =
        mu.real Zᶜ := by
      change (∫ omega, Zᶜ.indicator (1 : Omega → Real) omega ∂mu) = mu.real Zᶜ
      exact integral_indicator_one hZ.compl
    rw [hIntInd, measureReal_compl hZ]
    simp
    linarith
  have hRowMem : ∀ n, MemLp
      ((u n).apply (fun r => variationGateTerminal a T r S F mu))
      (2 : ENNReal) mu := by
    intro n
    have hRawAe : ∀ᵐ omega ∂mu,
        (((u n).applyVector x : Lp Real 2 mu) : Omega → Real) omega =
          (u n).apply (fun r => variationGateTerminal a T r S F mu) omega := by
      exact (u n).applyVector_coeFn_ae x
        (fun r => variationGateTerminal a T r S F mu)
        (fun r => MemLp.coeFn_toLp
          (memLp_two_variationGateTerminal a T r))
    exact (memLp_congr_ae hRawAe).mp (Lp.memLp ((u n).applyVector x))
  have hRInt : Integrable R mu :=
    (Lp.memLp gLimit).integrable (by norm_num)
  have hIntegralTendsto : Tendsto (fun n => ∫ omega,
      (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∂mu)
      atTop (𝓝 (∫ omega, R omega ∂mu)) := by
    have hRowInt : ∀ n, Integrable
        ((u n).apply (fun r => variationGateTerminal a T r S F mu)) mu :=
      fun n => (hRowMem n).integrable (by norm_num)
    have hLp2 : Tendsto (fun n => eLpNorm
        (((u n).apply (fun r => variationGateTerminal a T r S F mu)) - R)
        (2 : ENNReal) mu) atTop (𝓝 0) := by
      have hRawAe : ∀ n, ∀ᵐ omega ∂mu,
          (((u n).applyVector x : Lp Real 2 mu) : Omega → Real) omega =
            (u n).apply (fun r => variationGateTerminal a T r S F mu) omega := by
        intro n
        exact (u n).applyVector_coeFn_ae x
          (fun r => variationGateTerminal a T r S F mu)
          (fun r => MemLp.coeFn_toLp
            (memLp_two_variationGateTerminal a T r))
      have hLp2' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
        (fun n => (u n).applyVector x) gLimit).mp hLpU
      apply hLp2'.congr'
      filter_upwards [] with n
      apply eLpNorm_congr_ae
      filter_upwards [hRawAe n] with omega homega
      simp only [Pi.sub_apply, R]
      rw [homega]
    have hLp1 : Tendsto (fun n => eLpNorm
        (((u n).apply (fun r => variationGateTerminal a T r S F mu)) - R)
        (1 : ENNReal) mu) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hLp2 ?_ ?_
      · exact fun _ => bot_le
      · intro n
        exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    exact tendsto_integral_of_L1' R
      (Filter.Eventually.of_forall (fun n =>
        (hRowMem n).integrable (by norm_num))) hLp1
  have hRowLower : ∀ n, 1 - eta ≤ ∫ omega,
      (u n).apply (fun r => variationGateTerminal a T r S F mu) omega ∂mu := by
    intro n
    change 1 - eta ≤ ∫ omega, ∑ r ∈ (u n).support,
      (u n).weight r * variationGateTerminal a T r S F mu omega ∂mu
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      calc
        1 - eta = ∑ r ∈ (u n).support,
            (u n).weight r * (1 - eta) := by
              rw [← Finset.sum_mul, (u n).sum_eq_one]
              simp
        _ ≤ ∑ r ∈ (u n).support,
            (u n).weight r *
              ∫ omega, variationGateTerminal a T r S F mu omega ∂mu := by
              apply Finset.sum_le_sum
              intro r hr
              exact mul_le_mul_of_nonneg_left (hGateIntegral r)
                ((u n).nonneg r hr)
    · intro r hr
      exact ((memLp_two_variationGateTerminal a T r).integrable
        (by norm_num)).const_mul ((u n).weight r)
  have hExpectation : 1 - eta ≤ ∫ omega, R omega ∂mu :=
    ge_of_tendsto hIntegralTendsto (Filter.Eventually.of_forall hRowLower)
  let errorSet : Nat → Set Omega := fun n => {omega |
    (1 / 6 : Real) ≤ dist (((u n).apply
      (fun r => variationGateTerminal a T r S F mu)) omega) (R omega)}
  have hErrorMeasureTendsto : Tendsto (fun n => mu.real (errorSet n))
      atTop (𝓝 0) := by
    have hdist := (tendstoInMeasure_iff_measureReal_dist.mp hInMeasureU)
      (1 / 6 : Real) (by norm_num)
    simpa [errorSet] using hdist
  obtain ⟨selection, hselection, hselectionError⟩ :=
    exists_strictMono_subsequence_lt_of_tendsto_zero
      (δ := fun n => mu.real (errorSet n))
      (r := fun k => eta * ((1 / 2 : Real) ^ (k + 1)))
      hErrorMeasureTendsto
      (by intro k; positivity)
  have hSelectionError : ∀ k, mu (errorSet (selection k)) ≤
      ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) := by
    intro k
    calc
      mu (errorSet (selection k)) =
          ENNReal.ofReal (mu.real (errorSet (selection k))) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) :=
        ENNReal.ofReal_le_ofReal (hselectionError k).le
  let gateRow : Nat → Process Omega := fun n =>
    variationGateConvexRow u n a T S F mu
  let alphaSeq : Nat → Omega → WithTop NNReal := fun k omega =>
    min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -gateRow (selection k) t omega)
        (-1 / 2) omega)
  let alpha : Omega → WithTop NNReal := fun omega => ⨅ k, alphaSeq k omega
  let : F.IsRightContinuous := hUsual.rightContinuous
  have hAlphaSeqStopping : ∀ k, IsStoppingTime F (alphaSeq k) := by
    intro k
    have hAdapt : StronglyAdapted F (gateRow (selection k)) := by
      exact stronglyAdapted_variationGateConvexRow
        u (selection k) a T
    have hLeft : ∀ omega s, ContinuousWithinAt
        ((gateRow (selection k)) · omega) (Set.Iic s) s := by
      intro omega s
      exact continuousWithinAt_variationGateConvexRow_Iic u (selection k)
        a T S F mu omega s
    have hHit : IsStoppingTime F
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -gateRow (selection k) t omega) (-1 / 2)) := by
      apply LeftContinuousHittingTime.strictHittingAfter_isStoppingTime
        (hAdapt.neg)
      intro omega s
      exact (hLeft omega s).neg
    simpa [alphaSeq] using (isStoppingTime_const F T).min hHit
  have hAlphaStopping : IsStoppingTime F alpha :=
    IsStoppingTime.iInf hAlphaSeqStopping
  have hAlphaLe : ∀ k omega, alpha omega ≤ alphaSeq k omega := by
    intro k omega
    exact iInf_le (fun j => alphaSeq j omega) k
  have hAlphaSeqTerminal : ∀ k omega, alphaSeq k omega <
      (T : WithTop NNReal) → gateRow (selection k) T omega < 1 / 2 := by
    intro k omega hk
    have hHit :
        LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -gateRow (selection k) t omega) (-1 / 2) omega <
          (T : WithTop NNReal) := by
      by_cases hTh : (T : WithTop NNReal) ≤
          LeftContinuousHittingTime.strictHittingAfter
            (fun t omega => -gateRow (selection k) t omega) (-1 / 2) omega
      · have hEq : min (T : WithTop NNReal)
            (LeftContinuousHittingTime.strictHittingAfter
              (fun t omega => -gateRow (selection k) t omega)
              (-1 / 2) omega) = (T : WithTop NNReal) := min_eq_left hTh
        rw [← hEq] at hk
        exact False.elim ((not_lt_of_ge le_rfl) hk)
      · exact lt_of_not_ge hTh
    have hHit' : MeasureTheory.hittingAfter
          (fun t omega => -gateRow (selection k) t omega)
          (Set.Ioi (-1 / 2)) 0 omega < T := hHit
    rw [MeasureTheory.hittingAfter_lt_iff] at hHit'
    obtain ⟨s, hs, hsGate⟩ := hHit'
    have hs_le : s ≤ T := hs.2.le
    have hmono := monotone_variationGateConvexRow u (selection k)
      a T S F mu hs_le omega
    have hsGate' : -1 / 2 < -gateRow (selection k) s omega := by
      simpa [gateRow] using hsGate
    dsimp [gateRow] at hmono ⊢
    linarith
  have hErrorSetSummable :
      (∑' k : Nat, ENNReal.ofReal
        (eta * ((1 / 2 : Real) ^ (k + 1)))) ≤ ENNReal.ofReal eta := by
    have hsum : Summable (fun k : Nat =>
        eta * ((1 / 2 : Real) ^ (k + 1))) := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using summable_geometric_two.mul_left (eta / 2)
    rw [← ENNReal.ofReal_tsum_of_nonneg (by intro k; positivity) hsum]
    have : (∑' k : Nat, eta * ((1 / 2 : Real) ^ (k + 1))) = eta := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using tsum_geometric_two' eta
    rw [this]
  have hRBad : mu {omega | R omega ≤ 2 / 3} ≤
      ENNReal.ofReal (3 * eta) := by
    let f : Omega → Real := fun omega => 3 * (1 - R omega)
    have hf : Integrable f mu := by
      have h := ((integrable_const (1 : Real)).sub hRInt).const_mul (3 : Real)
      simpa [f] using h
    have hf_nonneg : 0 ≤ᵐ[mu] f := by
      filter_upwards [hRbounds] with omega hω
      dsimp [f]
      linarith [hω.2]
    have hmeasure : mu {omega | R omega ≤ 2 / 3} ≤
        ENNReal.ofReal (∫ omega, f omega ∂mu) :=
      hf.measure_le_integral hf_nonneg
        (fun omega homega => by
          dsimp [f] at *
          linarith [homega])
    have hIntegralF : (∫ omega, f omega ∂mu) =
        3 * (1 - ∫ omega, R omega ∂mu) := by
      dsimp [f]
      rw [integral_const_mul, integral_sub (integrable_const _) hRInt,
        integral_const]
      have hmuReal : mu.real Set.univ = 1 := by simp [measureReal_def]
      rw [hmuReal]
      ring
    rw [hIntegralF] at hmeasure
    apply hmeasure.trans
    exact ENNReal.ofReal_le_ofReal (by linarith [hExpectation])
  have hAlphaEventSubset : {omega | alpha omega < (T : WithTop NNReal)} ⊆
      {omega | R omega ≤ 2 / 3} ∪ ⋃ k, errorSet (selection k) := by
    intro omega hω
    change (⨅ k, alphaSeq k omega) < (T : WithTop NNReal) at hω
    obtain ⟨k, hk⟩ := (iInf_lt_iff.mp hω)
    by_cases hR : R omega ≤ 2 / 3
    · exact Or.inl hR
    · right
      apply mem_iUnion.2 ⟨k, ?_⟩
      by_contra hnot
      have hErr : dist
          (((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega)
          (R omega) < 1 / 6 := lt_of_not_ge hnot
      have hGate := hAlphaSeqTerminal k omega hk
      have hrowR :
          ((u (selection k)).apply (fun r => variationGateTerminal a T r S F mu))
            omega < 1 / 2 + 1 / 6 := by
        have hGate' :
            ((u (selection k)).apply
              (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 2 := by
          change ((u (selection k)).apply
            (fun r => variationGateProcess a T r S F mu T)) omega < 1 / 2 at hGate
          simpa [variationGateTerminal] using hGate
        exact hGate'.trans (by norm_num)
      have hupper : R omega -
          ((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 6 := by
        have hdist : |((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega - R omega| <
            1 / 6 := by
          simpa [Real.dist_eq] using hErr
        have habs : |R omega -
            ((u (selection k)).apply
              (fun r => variationGateTerminal a T r S F mu)) omega| <
            1 / 6 := by
          simpa [abs_sub_comm] using hdist
        exact (le_abs_self _).trans_lt habs
      have hR' : (2 / 3 : Real) < R omega := lt_of_not_ge hR
      have hGate' :
          ((u (selection k)).apply
            (fun r => variationGateTerminal a T r S F mu)) omega < 1 / 2 := by
        change ((u (selection k)).apply
          (fun r => variationGateProcess a T r S F mu T)) omega < 1 / 2 at hGate
        simpa [variationGateTerminal] using hGate
      linarith [hR', hGate', hupper]
  have hAlphaMeasure : mu {omega | alpha omega < (T : WithTop NNReal)} ≤
      ENNReal.ofReal (4 * eta) := by
    calc
      mu {omega | alpha omega < (T : WithTop NNReal)} ≤
          mu ({omega | R omega ≤ 2 / 3} ∪ ⋃ k, errorSet (selection k)) :=
        measure_mono hAlphaEventSubset
      _ ≤ mu {omega | R omega ≤ 2 / 3} +
          mu (⋃ k, errorSet (selection k)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (3 * eta) +
          ∑' k, ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) := by
        refine add_le_add hRBad ?_
        exact (measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun k => hSelectionError k)
      _ ≤ ENNReal.ofReal (4 * eta) := by
        calc
          ENNReal.ofReal (3 * eta) +
              ∑' k, ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1))) ≤
            ENNReal.ofReal (3 * eta) + ENNReal.ofReal eta :=
              add_le_add (le_refl _) hErrorSetSummable
          _ = ENNReal.ofReal (4 * eta) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
  refine ⟨a, u, selection, alphaSeq, alpha, R, ?_⟩
  refine
    { eta_pos := heta
      a_pos := haPos
      envelope_memLp := hξ
      envelope_bound := hSBound
      selection_strictMono := hselection
      selection_error := ?_
      alphaSeq_eq := ?_
      alphaSeq_le_T := ?_
      alphaSeq_stopping := hAlphaSeqStopping
      alpha_stopping := hAlphaStopping
      alpha_eq_iInf := fun _ => rfl
      alpha_le_alphaSeq := hAlphaLe
      alpha_measure := hAlphaMeasure
      gate_terminal_nonneg_le_one := ?_
      gate_terminal_memLp := hRowMem
      gate_limit_inMeasure := hInMeasureU
      gate_limit_ae := ?_ }
  · intro k
    simpa [errorSet] using hSelectionError k
  · intro k omega
    simp [alphaSeq, gateRow]
  · intro k omega
    exact min_le_left _ _
  · intro k omega
    exact variationGateConvexRow_nonneg_le_one u k a T S F mu T omega
  · simpa [R] using hAE

end HorizonFactorialGrid

end FTAPTheorem42
