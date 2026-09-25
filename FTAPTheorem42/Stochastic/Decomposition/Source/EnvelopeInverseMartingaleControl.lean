/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.EnvelopeUniformControl

/-!
# Inverse martingale terminal control for envelope-dominated stopped rows

This module consumes the native uniform-control certificate.  It retains the
same feasibility witness and proves the selected inverse martingale terminals,
including their common-stop versions, have a row-uniform square-integrable
bound.  Residual finite-variation estimates remain a later boundary.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

private theorem uniformEnvelope_nativeMartingaleProcess_terminal_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) :
    envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r T =ᵐ[mu]
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real) := by
  let G := grid T r
  have hPartMem : MemLp
      (G.doobVariationStoppedMartingalePart S F mu a (size T r))
      (2 : ENNReal) mu :=
    envelope_doobVariationStoppedMartingalePart_memLp_two
      hSAdapted ξ hξ hSBound G a (size T r)
  have hDoobM : Martingale (G.doobMartingalePart S F mu)
      (G.sampledFiltration F) mu :=
    envelope_doobMartingalePart_martingale
      hSAdapted ξ hξ hSBound G
  have hStoppedM : Martingale
      (G.doobVariationStoppedMartingalePart S F mu a)
      (G.sampledFiltration F) mu := by
    unfold ChronologicalGrid.doobVariationStoppedMartingalePart
    apply DiscretePredictableIntegral.isMartingale (C := fun _ => 1)
      hDoobM
      (fun k => envelope_doobMartingalePart_memLp_two
        hSAdapted ξ hξ hSBound G k)
      (G.stronglyAdapted_doobVariationGate S F mu a)
    intro k
    exact ae_of_all mu fun omega =>
      G.abs_doobVariationGate_le_one S F mu a k omega
  have hPartMeas : StronglyMeasurable[F T]
      (G.doobVariationStoppedMartingalePart S F mu a (size T r)) := by
    have hPartMeas' := hStoppedM.stronglyMeasurable (size T r)
    rw [ChronologicalGrid.sampledFiltration_apply, sampledTime_size] at hPartMeas'
    exact hPartMeas'
  have hCoe :
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real) =ᵐ[mu]
        G.doobVariationStoppedMartingalePart S F mu a (size T r) := by
    simpa [envelopeNativeMartingaleTerminal, G] using
      (MemLp.coeFn_toLp hPartMem)
  have hTerminalMeas : AEStronglyMeasurable[F T]
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real) mu :=
    (aestronglyMeasurable_congr hCoe).2 hPartMeas.aestronglyMeasurable
  have hCond :
      condExpMartingaleProcess mu F
          (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) T =ᵐ[mu]
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real) := by
    change mu[(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
      Omega → Real) | F T] =ᵐ[mu]
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real)
    exact condExp_of_aestronglyMeasurable' (F.le T) hTerminalMeas
      ((Lp.memLp _).integrable (by norm_num))
  have hVersion := (Classical.choose_spec
    (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r))).2.2.2 T
  simpa [envelopeNativeMartingaleProcess] using hVersion.trans hCond

theorem uniformEnvelope_nativeMartingaleProcess_at_sampledTime_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r k : Nat)
    (hk : k ≤ size T r) :
    envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T r).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedMartingalePart S F mu a k := by
  let G := grid T r
  have hPartMem : MemLp
      (G.doobVariationStoppedMartingalePart S F mu a (size T r))
      (2 : ENNReal) mu :=
    envelope_doobVariationStoppedMartingalePart_memLp_two
      hSAdapted ξ hξ hSBound G a (size T r)
  have hDoobM : Martingale (G.doobMartingalePart S F mu)
      (G.sampledFiltration F) mu :=
    envelope_doobMartingalePart_martingale
      hSAdapted ξ hξ hSBound G
  have hStoppedM : Martingale
      (G.doobVariationStoppedMartingalePart S F mu a)
      (G.sampledFiltration F) mu := by
    unfold ChronologicalGrid.doobVariationStoppedMartingalePart
    apply DiscretePredictableIntegral.isMartingale (C := fun _ => 1)
      hDoobM
      (fun j => envelope_doobMartingalePart_memLp_two
        hSAdapted ξ hξ hSBound G j)
      (G.stronglyAdapted_doobVariationGate S F mu a)
    intro j
    exact ae_of_all mu fun omega =>
      G.abs_doobVariationGate_le_one S F mu a j omega
  have hCoe :
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real) =ᵐ[mu]
        G.doobVariationStoppedMartingalePart S F mu a (size T r) := by
    simpa [envelopeNativeMartingaleTerminal, G] using
      (MemLp.coeFn_toLp hPartMem)
  have hCond :
      condExpMartingaleProcess mu F
          (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
          (G.sampledTime k) =ᵐ[mu]
        G.doobVariationStoppedMartingalePart S F mu a k := by
    change mu[(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
      Omega → Real) | F (G.sampledTime k)] =ᵐ[mu]
      G.doobVariationStoppedMartingalePart S F mu a k
    have hMartingaleCond := hStoppedM.condExp_ae_eq hk
    rw [ChronologicalGrid.sampledFiltration_apply] at hMartingaleCond
    exact (condExp_congr_ae hCoe).trans hMartingaleCond
  have hVersion := (Classical.choose_spec
    (exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r))).2.2.2
        (G.sampledTime k)
  simpa [envelopeNativeMartingaleProcess] using hVersion.trans hCond

private theorem uniformEnvelope_nativeMartingaleConvexRow_terminal_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) :
    envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T T =ᵐ[mu]
      (u n).apply (fun r =>
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real)) := by
  have hAll : ∀ᵐ omega ∂mu, ∀ r ∈ (u n).support,
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r T omega =
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real) omega := by
    exact (u n).support.eventually_all.mpr
      (fun r hr => uniformEnvelope_nativeMartingaleProcess_terminal_ae_eq
        hUsual hSAdapted ξ hξ hSBound a T r)
  filter_upwards [hAll] with omega hOmega
  unfold envelopeNativeMartingaleConvexRow TailConvexWeights.apply
  apply Finset.sum_congr rfl
  intro r hr
  change (u n).weight r *
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r T omega =
    (u n).weight r *
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real) omega
  rw [hOmega r hr]

private theorem uniformEnvelope_nativeMartingaleConvexRow_zero_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) :
    envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T 0 =ᵐ[mu]
      0 := by
  have hAll : ∀ᵐ omega ∂mu, ∀ r,
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r 0 omega =
        0 := by
    apply ae_all_iff.2
    intro r
    have hAt := uniformEnvelope_nativeMartingaleProcess_at_sampledTime_ae_eq
      hUsual hSAdapted ξ hξ hSBound a T r 0 (Nat.zero_le _)
    have hzero : (grid T r).sampledTime 0 = 0 := by
      simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
    rw [hzero] at hAt
    filter_upwards [hAt] with omega hOmega
    rw [hOmega]
    simp [ChronologicalGrid.doobVariationStoppedMartingalePart]
  filter_upwards [hAll] with omega hOmega
  unfold envelopeNativeMartingaleConvexRow TailConvexWeights.apply
  simp only [Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro r hr
  rw [hOmega r]
  simp

private theorem uniformEnvelope_inverse_terminal_memLp_two_and_eLpNorm_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlpha : ∀ omega, alpha omega ≤ min (T : WithTop NNReal)
      (LeftContinuousHittingTime.strictHittingAfter
        (fun t omega => -variationGateConvexRow u n a T S F mu t omega)
        (-1 / 2) omega))
    (C : Omega → Real) (hCMem : MemLp C (2 : ENNReal) mu)
    (hCNonneg : ∀ omega, 0 ≤ C omega)
    (hMZero : envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ
        hSBound a T 0 =ᵐ[mu] 0)
    (hMTBound : ∀ᵐ omega ∂mu,
      |envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T T omega| ≤
        C omega) :
    MemLp
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T)
        (2 : ENNReal) mu ∧
      eLpNorm
          (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
            u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T)
          (2 : ENNReal) mu ≤
        2 * eLpNorm C (2 : ENNReal) mu := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  have hM : Martingale M F mu := by
    exact envelopeNativeMartingaleConvexRow_martingale
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T
  have hMLp : ∀ k, MemLp (G.natSample M k) (2 : ENNReal) mu := by
    intro k
    change MemLp (M (G.sampledTime k)) (2 : ENNReal) mu
    exact envelopeNativeMartingaleConvexRow_memLp_two
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound
      a T (G.sampledTime k)
  have hK : StronglyAdapted F K := by
    exact rowInverseCoefficientProcess_stronglyAdapted
      (S := S) (F := F) (mu := mu) u n a T alpha hAlphaStop
  have hKBound : ∀ k, ∀ᵐ omega ∂mu, |G.natSample K k omega| ≤ (2 : Real) := by
    intro k
    exact ae_of_all mu (fun omega => by
      change |K (G.sampledTime k) omega| ≤ (2 : Real)
      exact rowInverseCoefficientProcess_abs_le_two
        (S := S) (F := F) (mu := mu) u n a T alpha hAlpha
        (G.sampledTime k) omega)
  have hDiscrete : MemLp
      (discretePredictableIntegral (G.natSample K) (G.natSample M)
        (size T q)) (2 : ENNReal) mu :=
    DiscretePredictableIntegral.memLp_two
      (ChronologicalGrid.Martingale.natSample (G := G) hM)
      hMLp (G.stronglyAdapted_natSample hK)
      (fun k => hKBound k) (size T q)
  have hTerminal :
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T =
        discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) := by
    have hTerminalAt :
        envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
            u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop
              (G.sampledTime (size T q)) =
          discretePredictableIntegral (G.natSample K) (G.natSample M)
            (size T q) := by
      change G.martingaleIntegralProcess K M
          (G.sampledTime (size T q)) = _
      exact G.martingaleIntegralProcess_last K M
    simpa [G] using hTerminalAt
  have hNMem : MemLp
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T)
      (2 : ENNReal) mu := by
    rw [hTerminal]
    exact hDiscrete
  have hContract :
      (∫ omega,
        (discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) omega) ^ 2 ∂mu) ≤
        (2 : Real) ^ 2 *
          (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) := by
    have hContract0 := DiscretePredictableIntegral.integral_sq_le_mul_terminalIncrement_sq
      (ChronologicalGrid.Martingale.natSample (G := G) hM)
      hMLp (G.stronglyAdapted_natSample hK) (by norm_num)
      (fun k => hKBound k) (size T q)
    have hLast : G.sampledTime (size T q) = T := sampledTime_size T q
    have hZero : G.sampledTime 0 = 0 := by
      simp [G, ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
    have hIncrement :
        (fun omega =>
          (G.natSample M (size T q) omega - G.natSample M 0 omega) ^ 2) =
        (fun omega => (M T omega - M 0 omega) ^ 2) := by
      funext omega
      simp only [ChronologicalGrid.natSample, hLast, hZero]
    rw [hIncrement] at hContract0
    exact hContract0
  have hMTMem : MemLp (M T) (2 : ENNReal) mu := by
    exact envelopeNativeMartingaleConvexRow_memLp_two
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T T
  have hMZeroMem : MemLp (M 0) (2 : ENNReal) mu := by
    exact envelopeNativeMartingaleConvexRow_memLp_two
      (S := S) (F := F) (mu := mu) u n hUsual hSAdapted ξ hξ hSBound a T 0
  have hDiffInt : Integrable (fun omega => (M T omega - M 0 omega) ^ 2) mu :=
    (hMTMem.sub hMZeroMem).integrable_sq
  have hCInt : Integrable (fun omega => (C omega) ^ 2) mu :=
    hCMem.integrable_sq
  have hDiffBound :
      (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) ≤
        ∫ omega, (C omega) ^ 2 ∂mu := by
    apply integral_mono_ae hDiffInt hCInt
    filter_upwards [hMTBound, hMZero] with omega hT h0
    have hT' : |M T omega| ≤ C omega := by
      simpa [M] using hT
    have h0' : M 0 omega = 0 := by
      simpa [M] using h0
    rw [h0', sub_zero]
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (hCNonneg omega)).2 hT'
  have hContract' :
      (∫ omega,
        (discretePredictableIntegral (G.natSample K) (G.natSample M)
          (size T q) omega) ^ 2 ∂mu) ≤
        4 * (∫ omega, (C omega) ^ 2 ∂mu) := by
    calc
      _ ≤ (2 : Real) ^ 2 * (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) :=
        hContract
      _ ≤ 4 * (∫ omega, (C omega) ^ 2 ∂mu) := by
        calc
          (2 : Real) ^ 2 * (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) =
              4 * (∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu) := by norm_num
          _ ≤ 4 * (∫ omega, (C omega) ^ 2 ∂mu) :=
            mul_le_mul_of_nonneg_left hDiffBound (by norm_num)
  have hNSecond :
      (∫ omega,
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega) ^ 2 ∂mu) ≤
        4 * (∫ omega, (C omega) ^ 2 ∂mu) := by
    rw [hTerminal]
    exact hContract'
  have hNSecond' :
      (∫ omega,
        ‖envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega‖ ^ 2 ∂mu) ≤
        4 * (∫ omega, ‖C omega‖ ^ 2 ∂mu) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hNSecond
  have hNTo := eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hNMem
  have hCTo := eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hCMem
  have hNNonneg :
      0 ≤ ∫ omega, ‖envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae (ae_of_all mu (fun omega : Omega =>
      sq_nonneg (‖envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega‖ : Real)))
  have hCNonnegInt : 0 ≤ ∫ omega, ‖C omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae (ae_of_all mu (fun omega : Omega =>
      sq_nonneg (‖C omega‖ : Real)))
  have hReal :
      (eLpNorm
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T)
        (2 : ENNReal) mu).toReal ≤
        2 * (eLpNorm C (2 : ENNReal) mu).toReal := by
    rw [hNTo, hCTo]
    have hNRootNonneg : 0 ≤ Real.sqrt
        (∫ omega, ‖envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega‖ ^ 2 ∂mu) :=
      Real.sqrt_nonneg _
    have hCRootNonneg : 0 ≤ Real.sqrt (∫ omega, ‖C omega‖ ^ 2 ∂mu) :=
      Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hNNonneg, Real.sq_sqrt hCNonnegInt, hNSecond']
  refine ⟨hNMem, ?_⟩
  apply (ENNReal.toReal_le_toReal hNMem.eLpNorm_ne_top
    (ENNReal.mul_ne_top (by norm_num) hCMem.eLpNorm_ne_top)).mp
  rw [ENNReal.toReal_mul]
  norm_num
  exact hReal

private theorem uniformEnvelope_inverseGain_constant_after_horizon
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha) :
    ∀ omega,
      envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop (T + 1) omega =
        envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u n hUsual hSAdapted ξ hξ hSBound a T alpha hAlphaStop T omega := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
  have hLast : G.martingaleIntegralProcess K M (T + 1) =
      G.martingaleIntegralProcess K M (G.sampledTime (size T q)) := by
    rw [G.martingaleIntegralProcess_eq_last_of_le K M]
    simp [G]
  have hSize : G.sampledTime (size T q) = T := sampledTime_size T q
  intro omega
  change G.martingaleIntegralProcess K M (T + 1) omega =
    G.martingaleIntegralProcess K M T omega
  rw [hLast, hSize]

private theorem uniformEnvelope_stopped_inverse_terminal_memLp_two_and_eLpNorm_le
    {N : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal} {T : NNReal}
    (hM : Martingale N F mu)
    (hMRight : ∀ omega t, ContinuousWithinAt (N · omega) (Ici t) t)
    (hAlphaStop : IsStoppingTime F alpha)
    (hNT : MemLp (N T) (2 : ENNReal) mu)
    (hMConstant : ∀ omega, N (T + 1) omega = N T omega)
    (C : Omega → Real)
    (hNNorm : eLpNorm (N T) (2 : ENNReal) mu ≤
      2 * eLpNorm C (2 : ENNReal) mu) :
    MemLp (MeasureTheory.stoppedProcess N alpha T) (2 : ENNReal) mu ∧
      eLpNorm (MeasureTheory.stoppedProcess N alpha T) (2 : ENNReal) mu ≤
        2 * eLpNorm C (2 : ENNReal) mu := by
  have hStopped := martingale_stoppedProcess_memLp_two_and_integral_sq_le
    hM hMRight hAlphaStop hNT hMConstant
  have hStopMem : MemLp (MeasureTheory.stoppedProcess N alpha T)
      (2 : ENNReal) mu := hStopped.1
  have hStopSq :
      (∫ omega, ‖MeasureTheory.stoppedProcess N alpha T omega‖ ^ 2 ∂mu) ≤
        ∫ omega, ‖N T omega‖ ^ 2 ∂mu := by
    simpa only [Real.norm_eq_abs, sq_abs] using hStopped.2
  have hStopTo := eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hStopMem
  have hNTo := eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hNT
  have hStopNonneg :
      0 ≤ ∫ omega, ‖MeasureTheory.stoppedProcess N alpha T omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae (ae_of_all mu (fun omega : Omega =>
      sq_nonneg (‖MeasureTheory.stoppedProcess N alpha T omega‖ : Real)))
  have hNNonneg : 0 ≤ ∫ omega, ‖N T omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae (ae_of_all mu (fun omega : Omega =>
      sq_nonneg (‖N T omega‖ : Real)))
  have hReal :
      (eLpNorm (MeasureTheory.stoppedProcess N alpha T) (2 : ENNReal) mu).toReal ≤
        (eLpNorm (N T) (2 : ENNReal) mu).toReal := by
    rw [hStopTo, hNTo]
    have hStopRootNonneg : 0 ≤ Real.sqrt
        (∫ omega, ‖MeasureTheory.stoppedProcess N alpha T omega‖ ^ 2 ∂mu) :=
      Real.sqrt_nonneg _
    have hNRootNonneg : 0 ≤ Real.sqrt (∫ omega, ‖N T omega‖ ^ 2 ∂mu) :=
      Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hStopNonneg, Real.sq_sqrt hNNonneg, hStopSq]
  have hStopNorm :
      eLpNorm (MeasureTheory.stoppedProcess N alpha T) (2 : ENNReal) mu ≤
        eLpNorm (N T) (2 : ENNReal) mu := by
    apply (ENNReal.toReal_le_toReal hStopMem.eLpNorm_ne_top
      hNT.eLpNorm_ne_top).mp
    exact hReal
  exact ⟨hStopMem, hStopNorm.trans hNNorm⟩

/-- Envelope-specific inverse martingale terminal control attached to a
native uniform-control certificate.  The native certificate retains the
common feasibility witness, so all rows use its original coefficients and
stopping times.  Residual finite-variation control is not part of this
endpoint. -/
structure EnvelopeStoppedRowsInverseMartingaleControlData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (eta : Real) (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real) : Prop where
  nativeControl :
    EnvelopeStoppedRowsNativeUniformControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z Γ hEnvelope eta u selection a
        alphaSeq alpha R hUsual hSAdapted hSBound C
  nativeTerminalProcess_ae_eq : ∀ n,
    envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T T =ᵐ[mu]
      (u n).apply (fun r =>
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real))
  nativeInitialProcess_ae_eq : ∀ n,
    envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T 0 =ᵐ[mu]
      0
  inverseTerminal_memLp : ∀ k, MemLp
    (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
      u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
        (nativeControl.feasibility.commonGate.alphaSeq_stopping k) T)
      (2 : ENNReal) mu
  inverseTerminal_eLpNorm_le : ∀ k,
    eLpNorm
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
          (nativeControl.feasibility.commonGate.alphaSeq_stopping k) T)
        (2 : ENNReal) mu ≤ 2 * eLpNorm C (2 : ENNReal) mu
  stoppedInverseTerminal_memLp : ∀ k, MemLp
    (MeasureTheory.stoppedProcess
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
          (nativeControl.feasibility.commonGate.alphaSeq_stopping k))
      alpha T)
      (2 : ENNReal) mu
  stoppedInverseTerminal_eLpNorm_le : ∀ k,
    eLpNorm
      (MeasureTheory.stoppedProcess
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
            (nativeControl.feasibility.commonGate.alphaSeq_stopping k))
        alpha T)
      (2 : ENNReal) mu ≤ 2 * eLpNorm C (2 : ENNReal) mu

/-- The native uniform-control certificate directly produces uniform inverse
martingale terminal data.  The feasibility witness, coefficients, and stops
are inherited from nativeControl without any commutation assumption. -/
theorem exists_envelopeStoppedRowsInverseMartingaleControlData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (nativeControl :
      EnvelopeStoppedRowsNativeUniformControlData
        (S := S) (F := F) (mu := mu) ξ hξ T Z Γ hEnvelope eta u selection a
          alphaSeq alpha R hUsual hSAdapted hSBound C) :
    EnvelopeStoppedRowsInverseMartingaleControlData
      (S := S) (F := F) (mu := mu) ξ hξ T Z Γ hEnvelope eta u selection a
        alphaSeq alpha R hUsual hSAdapted hSBound C := by
  let hEndpoint := nativeControl.feasibility
  have hCMem := nativeControl.control_memLp
  have hCNonneg := nativeControl.control_nonneg
  have hNativeConvexBound := nativeControl.nativeTerminalConvex_abs_le
  have hNativeProcessTerminalEq : ∀ n,
      envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T T =ᵐ[mu]
        (u n).apply (fun r =>
          (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
            Omega → Real)) := by
    intro n
    exact uniformEnvelope_nativeMartingaleConvexRow_terminal_ae_eq
      u n hUsual hSAdapted ξ hξ hSBound a T
  have hNativeProcessInitialEq : ∀ n,
      envelopeNativeMartingaleConvexRow u n hUsual hSAdapted ξ hξ hSBound a T 0 =ᵐ[mu]
        0 := by
    intro n
    exact uniformEnvelope_nativeMartingaleConvexRow_zero_ae_eq
      u n hUsual hSAdapted ξ hξ hSBound a T
  have hInverseMem : ∀ k, MemLp
      (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
        u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
          (hEndpoint.commonGate.alphaSeq_stopping k) T)
      (2 : ENNReal) mu := by
    intro k
    have hHit : ∀ omega, alphaSeq k omega ≤ min (T : WithTop NNReal)
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -variationGateConvexRow u (selection k) a T S F mu t omega)
          (-1 / 2) omega) := by
      intro omega
      exact le_of_eq (hEndpoint.commonGate.alphaSeq_eq k omega)
    have hZero := hNativeProcessInitialEq (selection k)
    have hTerminalBound : ∀ᵐ omega ∂mu,
        |envelopeNativeMartingaleConvexRow u (selection k) hUsual hSAdapted ξ hξ
          hSBound a T T omega| ≤ C omega := by
      filter_upwards [hNativeProcessTerminalEq (selection k),
        hNativeConvexBound (selection k)] with omega hEq hBound
      rw [hEq]
      exact hBound
    exact (uniformEnvelope_inverse_terminal_memLp_two_and_eLpNorm_le
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k) hHit C hCMem
      hCNonneg hZero hTerminalBound).1
  have hInverseNorm : ∀ k,
      eLpNorm
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
            (hEndpoint.commonGate.alphaSeq_stopping k) T)
        (2 : ENNReal) mu ≤ 2 * eLpNorm C (2 : ENNReal) mu := by
    intro k
    have hHit : ∀ omega, alphaSeq k omega ≤ min (T : WithTop NNReal)
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega => -variationGateConvexRow u (selection k) a T S F mu t omega)
          (-1 / 2) omega) := by
      intro omega
      exact le_of_eq (hEndpoint.commonGate.alphaSeq_eq k omega)
    have hZero := hNativeProcessInitialEq (selection k)
    have hTerminalBound : ∀ᵐ omega ∂mu,
        |envelopeNativeMartingaleConvexRow u (selection k) hUsual hSAdapted ξ hξ
          hSBound a T T omega| ≤ C omega := by
      filter_upwards [hNativeProcessTerminalEq (selection k),
        hNativeConvexBound (selection k)] with omega hEq hBound
      rw [hEq]
      exact hBound
    exact (uniformEnvelope_inverse_terminal_memLp_two_and_eLpNorm_le
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k) hHit C hCMem
      hCNonneg hZero hTerminalBound).2
  have hStoppedInverseMem : ∀ k, MemLp
      (MeasureTheory.stoppedProcess
        (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
          u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
            (hEndpoint.commonGate.alphaSeq_stopping k))
        alpha T)
      (2 : ENNReal) mu := by
    intro k
    have hConst := uniformEnvelope_inverseGain_constant_after_horizon
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k)
    have hRight := envelopeRowInverseMartingaleGain_rightContinuous
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k)
    exact (uniformEnvelope_stopped_inverse_terminal_memLp_two_and_eLpNorm_le
      (hEndpoint.rowData k).row_martingale hRight hEndpoint.commonGate.alpha_stopping
      (hInverseMem k) hConst C (hInverseNorm k)).1
  have hStoppedInverseNorm : ∀ k,
      eLpNorm
        (MeasureTheory.stoppedProcess
          (envelopeRowInverseMartingaleGain (S := S) (F := F) (mu := mu)
            u (selection k) hUsual hSAdapted ξ hξ hSBound a T (alphaSeq k)
              (hEndpoint.commonGate.alphaSeq_stopping k))
          alpha T)
        (2 : ENNReal) mu ≤ 2 * eLpNorm C (2 : ENNReal) mu := by
    intro k
    have hConst := uniformEnvelope_inverseGain_constant_after_horizon
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k)
    have hRight := envelopeRowInverseMartingaleGain_rightContinuous
      (S := S) (F := F) (mu := mu) u (selection k) hUsual hSAdapted ξ hξ hSBound
      a T (alphaSeq k) (hEndpoint.commonGate.alphaSeq_stopping k)
    exact (uniformEnvelope_stopped_inverse_terminal_memLp_two_and_eLpNorm_le
      (hEndpoint.rowData k).row_martingale hRight hEndpoint.commonGate.alpha_stopping
      (hInverseMem k) hConst C (hInverseNorm k)).2
  exact
    { nativeControl := nativeControl
      nativeTerminalProcess_ae_eq := hNativeProcessTerminalEq
      nativeInitialProcess_ae_eq := hNativeProcessInitialEq
      inverseTerminal_memLp := hInverseMem
      inverseTerminal_eLpNorm_le := hInverseNorm
      stoppedInverseTerminal_memLp := hStoppedInverseMem
      stoppedInverseTerminal_eLpNorm_le := hStoppedInverseNorm }

end HorizonFactorialGrid

end FTAPTheorem42
