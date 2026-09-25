/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupFoundationCore
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Source-independent stopped equality for the predictable-limsup foundation

This module is the terminal-difference Fatou consumer for
`CommonHilbertRowsData`.  It applies Fatou only to the nonnegative terminal
differences retained by the foundation and does not introduce a general
reverse-Fatou theorem or a process-level section argument.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

namespace CommonHilbertRowsData

/-! ## The two scalar facts used by this consumer -/

private theorem liminf_sub_eq_of_tendsto_of_nonnegative_of_bounded
    {x y : Nat → Real} {a : Real}
    (hy : Tendsto y atTop (𝓝 a))
    (hxUpper : IsBoundedUnder (· ≤ ·) atTop x)
    (hxNonnegative : ∀ n, 0 ≤ x n) :
    liminf (fun n => y n - x n) atTop =
      a - limsup x atTop := by
  have hxLower : IsBoundedUnder (· ≥ ·) atTop x :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hxNonnegative)
  have hxCobdd : IsCoboundedUnder (· ≤ ·) atTop x :=
    hxLower.isCoboundedUnder_le
  have hzUpper : IsBoundedUnder (· ≤ ·) atTop (fun n => a - x n) :=
    isBoundedUnder_of_eventually_le <|
      Filter.Eventually.of_forall (fun n => sub_le_self a (hxNonnegative n))
  obtain ⟨b, hb⟩ := hxUpper.eventually_le
  have hzLower : IsBoundedUnder (· ≥ ·) atTop (fun n => a - x n) :=
    isBoundedUnder_of_eventually_ge <|
      hb.mono (fun n hn => sub_le_sub_left hn a)
  have he : Tendsto (fun n => y n - a) atTop (𝓝 0) := by
    simpa only [sub_self] using hy.sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => a) atTop (𝓝 a))
  have heInf : liminf (fun n => y n - a) atTop = 0 := he.liminf_eq
  have heSup : limsup (fun n => y n - a) atTop = 0 := he.limsup_eq
  have hzInf : liminf (fun n => a - x n) atTop =
      a - limsup x atTop :=
    liminf_const_sub atTop x a hxUpper hxCobdd
  have hLower := le_liminf_add
    (f := atTop) (u := fun n => y n - a) (v := fun n => a - x n)
    he.isBoundedUnder_ge he.isBoundedUnder_le hzLower hzUpper.isCoboundedUnder_ge
  have hUpper := liminf_add_le
    (f := atTop) (u := fun n => y n - a) (v := fun n => a - x n)
    he.isBoundedUnder_ge he.isBoundedUnder_le hzLower hzUpper.isCoboundedUnder_ge
  have hDecomp : (fun n => y n - x n) =
      (fun n => (y n - a) + (a - x n)) := by
    funext n
    ring
  have hAdd : (fun n => y n - a) + (fun n => a - x n) =
      (fun n => (y n - a) + (a - x n)) := by
    funext n
    rfl
  rw [hDecomp] at *
  rw [hAdd] at hLower hUpper
  rw [heInf, hzInf] at hLower
  rw [heSup, hzInf] at hUpper
  apply le_antisymm
  · simpa only [Pi.add_apply, zero_add] using hUpper
  · simpa only [Pi.add_apply, zero_add] using hLower

private theorem integral_liminf_le_of_nonnegative_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Nat → Ω → Real}
    (hf : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω)
    (hlim : Integrable (fun ω => liminf (fun n => f n ω) atTop) μ)
    (hlimn : ∀ᵐ ω ∂μ, 0 ≤ liminf (fun n => f n ω) atTop)
    (hfb : ∀ᵐ ω ∂μ,
      IsBoundedUnder (· ≤ ·) atTop (fun n => f n ω))
    {I : Real}
    (hIt : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 I)) :
    (∫ ω, liminf (fun n => f n ω) atTop ∂μ) ≤ I := by
  have hFatou := MeasureTheory.lintegral_liminf_le'
    (μ := μ) (f := fun n ω => ENNReal.ofReal (f n ω))
    (u := atTop)
    (fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hfn_all : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ f n ω := by
    rw [ae_all_iff]
    intro n
    exact hfn n
  have hLeft : ENNReal.ofReal
      (∫ ω, liminf (fun n => f n ω) atTop ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (liminf (fun n => f n ω) atTop) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hlim hlimn
  have hEach (n : Nat) : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hf n) (hfn n)
  have hOfRealLiminf : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (liminf (fun n => f n ω) atTop) =
        liminf (fun n => ENNReal.ofReal (f n ω)) atTop := by
    filter_upwards [hfn_all, hfb] with ω hnonneg hbound
    have hlower : IsBoundedUnder (· ≥ ·) atTop (fun n => f n ω) :=
      isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hnonneg)
    exact ENNReal.ofReal_mono.map_liminf_of_continuousAt
      (fun n => f n ω) ENNReal.continuous_ofReal.continuousAt
      hbound.isCoboundedUnder_ge hlower
  have hFatou' : ENNReal.ofReal
      (∫ ω, liminf (fun n => f n ω) atTop ∂μ) ≤
      liminf (fun n => ENNReal.ofReal (∫ ω, f n ω ∂μ)) atTop := by
    calc
      ENNReal.ofReal (∫ ω, liminf (fun n => f n ω) atTop ∂μ) =
          ∫⁻ ω, ENNReal.ofReal (liminf (fun n => f n ω) atTop) ∂μ := hLeft
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ :=
        lintegral_congr_ae hOfRealLiminf
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop := hFatou
      _ = liminf (fun n => ENNReal.ofReal (∫ ω, f n ω ∂μ)) atTop := by
        simp_rw [← hEach]
  have hRight : liminf (fun n => ENNReal.ofReal
      (∫ ω, f n ω ∂μ)) atTop = ENNReal.ofReal I := by
    exact (ENNReal.tendsto_ofReal hIt).liminf_eq
  rw [hRight] at hFatou'
  have hI_nonneg : 0 ≤ I := by
    exact ge_of_tendsto hIt
      (Filter.Eventually.of_forall fun n => integral_nonneg_of_ae (hfn n))
  exact (ENNReal.ofReal_le_ofReal_iff hI_nonneg).mp hFatou'

/-! ## The generic stopped equality certificate -/

structure StoppingLimsupEqualityData
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {cutoff : Nat → Nat}
    {hData : CommonAESubsequenceData h w y hCommon cutoff}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    {bad : Set Ω} {Preg : Process Ω}
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : PredictableLimsupData hCad hReg cutoff hData Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : StoppingConvexExpectationCertificate h w cutoff X τ)
    (hCandidate : CandidateOptionalSamplingData (F := F) (mu := mu)
      X M Preg τ hτ hτT)
    (hFoundation : StoppingLimsupFoundationData hCad hReg Ppred hLimsup τ hτ hτT
      hStop hCandidate) : Prop where
  terminal_difference_liminf_eq : ∀ᵐ omega ∂mu,
    liminf (fun n => terminalDifference h w τ cutoff n omega) atTop =
      Preg T omega - Ppred (τ omega) omega
  terminal_difference_integral_le :
    (∫ omega, liminf (fun n => terminalDifference h w τ cutoff n omega)
      atTop ∂mu) ≤
      (∫ omega, Preg T omega ∂mu) -
        ∫ omega, Preg (τ omega) omega ∂mu
  stopped_sample_ae_eq :
    (fun omega => Ppred (τ omega) omega) =ᵐ[mu]
      (fun omega => Preg (τ omega) omega)

/-! ## The terminal-difference consumer -/

omit [SigmaFiniteFiltration mu F] in
theorem stoppingLimsupEquality_producer
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : PredictableLimsupData hCad hReg cutoff hData Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : StoppingConvexExpectationCertificate h w cutoff X τ)
    (hCandidate : CandidateOptionalSamplingData (F := F) (mu := mu)
      X M Preg τ hτ hτT)
    (hTerminalCandidate : CandidateOptionalSamplingData (F := F) (mu := mu)
      X M Preg (fun _ : Ω => T) (isStoppingTime_const F T) (fun _ => le_rfl))
    (hFoundation : StoppingLimsupFoundationData hCad hReg Ppred hLimsup τ hτ hτT
      hStop hCandidate) :
    StoppingLimsupEqualityData hCad hReg Ppred hLimsup τ hτ hτT hStop hCandidate
      hFoundation := by
  have hPregTerminalIntegral :
      (∫ omega, Preg T omega ∂mu) = ∫ omega, X T omega ∂mu := by
    simpa using hTerminalCandidate.candidate_sample_integral_eq_source
  have hDiffIntegrable : ∀ n,
      Integrable (terminalDifference h w τ cutoff n) mu :=
    hFoundation.terminal_difference_integrable
  have hDiffIntegralEq (n : Nat) :
      (∫ omega, terminalDifference h w τ cutoff n omega ∂mu) =
        (∫ omega, X T omega ∂mu) -
          ∫ omega, h.convexRow (w (cutoff n)) (τ omega) omega ∂mu := by
    have hEq := integral_sub
      (hFoundation.terminal_row_integrable n)
      (hStop.row_integrable n)
    change (∫ omega, h.convexRow (w (cutoff n)) T omega -
      h.convexRow (w (cutoff n)) (τ omega) omega ∂mu) = _
    rw [hEq, hCommon.row_terminal_expectation]
    rw [integral_congr_ae hSource.source_terminal_ae]
  have hDiffIntegralTendsto : Tendsto
      (fun n => ∫ omega, terminalDifference h w τ cutoff n omega ∂mu)
      atTop (𝓝 ((∫ omega, Preg T omega ∂mu) -
        ∫ omega, Preg (τ omega) omega ∂mu)) := by
    have hSub : Tendsto
        (fun n => (∫ omega, X T omega ∂mu) -
          ∫ omega, h.convexRow (w (cutoff n)) (τ omega) omega ∂mu) atTop
        (𝓝 ((∫ omega, X T omega ∂mu) -
          ∫ omega, X (τ omega) omega ∂mu)) :=
      tendsto_const_nhds.sub hStop.integral_tendsto
    have hSub' : Tendsto
        (fun n => (∫ omega, X T omega ∂mu) -
          ∫ omega, h.convexRow (w (cutoff n)) (τ omega) omega ∂mu) atTop
        (𝓝 ((∫ omega, Preg T omega ∂mu) -
          ∫ omega, Preg (τ omega) omega ∂mu)) := by
      simpa [hPregTerminalIntegral,
        hCandidate.candidate_sample_integral_eq_source] using hSub
    exact hSub'.congr' (Filter.Eventually.of_forall fun n =>
      (hDiffIntegralEq n).symm)
  have hTauUpper : ∀ᵐ omega ∂mu, IsBoundedUnder (· ≤ ·) atTop
      (fun n => h.convexRow (w (cutoff n)) (τ omega) omega) := by
    filter_upwards [hFoundation.terminal_row_tendstoAE] with omega hTendsto
    obtain ⟨b, hb⟩ := hTendsto.isBoundedUnder_le.eventually_le
    exact isBoundedUnder_of_eventually_le <|
      hb.mono (fun n hn =>
        (hData.row_mono n omega (hτT omega)).trans hn)
  have hDiffLiminfEq : ∀ᵐ omega ∂mu,
      liminf (fun n => terminalDifference h w τ cutoff n omega) atTop =
        Preg T omega - Ppred (τ omega) omega := by
    have hScalar : ∀ᵐ omega ∂mu,
        liminf (fun n => terminalDifference h w τ cutoff n omega) atTop =
          Preg T omega -
            limsup (fun n => h.convexRow (w (cutoff n)) (τ omega) omega)
              atTop := by
      filter_upwards [hFoundation.terminal_row_tendstoAE, hTauUpper]
        with omega hTendsto hUpper
      exact liminf_sub_eq_of_tendsto_of_nonnegative_of_bounded hTendsto hUpper
        (fun n => hData.row_nonnegative n (τ omega) omega)
    have hRaw : ∀ omega,
        Ppred (τ omega) omega =
          limsup (fun n => h.convexRow (w (cutoff n)) (τ omega) omega) atTop := by
      intro omega
      have hDef := congrArg (fun p : Process Ω => p (τ omega) omega)
        hLimsup.Ppred_definition
      simpa only [predictableLimsup] using hDef
    filter_upwards [hScalar] with omega hω
    calc
      liminf (fun n => terminalDifference h w τ cutoff n omega) atTop =
          Preg T omega -
            limsup (fun n => h.convexRow (w (cutoff n)) (τ omega) omega) atTop := hω
      _ = Preg T omega - Ppred (τ omega) omega := by rw [← hRaw]
  have hDiffLiminfEqFun :
      (fun omega => liminf (fun n => terminalDifference h w τ cutoff n omega)
        atTop) =ᵐ[mu]
      (fun omega => Preg T omega - Ppred (τ omega) omega) := hDiffLiminfEq
  have hDiffLiminfNonnegative : ∀ᵐ omega ∂mu, 0 ≤
      liminf (fun n => terminalDifference h w τ cutoff n omega) atTop := by
    filter_upwards [hDiffLiminfEq, hLimsup.Ppred_le_Preg] with omega hEq hPred
    rw [hEq]
    exact sub_nonneg.mpr ((hPred (τ omega)).trans
      (hReg.Preg_monotone omega (hτT omega)))
  have hDiffUpper : ∀ᵐ omega ∂mu, IsBoundedUnder (· ≤ ·) atTop
      (fun n => terminalDifference h w τ cutoff n omega) := by
    filter_upwards [hFoundation.terminal_row_tendstoAE] with omega hTendsto
    obtain ⟨b, hb⟩ := hTendsto.isBoundedUnder_le.eventually_le
    exact isBoundedUnder_of_eventually_le <|
      hb.mono (fun n hn =>
        (sub_le_self _ (hData.row_nonnegative n (τ omega) omega)).trans hn)
  have hFatou :
      (∫ omega, liminf (fun n => terminalDifference h w τ cutoff n omega)
        atTop ∂mu) ≤
        (∫ omega, Preg T omega ∂mu) -
          ∫ omega, Preg (τ omega) omega ∂mu := by
    apply integral_liminf_le_of_nonnegative_of_bounded
      hDiffIntegrable
      (fun n => ae_of_all mu (hFoundation.terminal_difference_nonnegative n))
      ((hFoundation.Preg_terminal_integrable.sub
        hFoundation.Ppred_sample_integrable).congr hDiffLiminfEqFun.symm)
      hDiffLiminfNonnegative
    · exact hDiffUpper
    · exact hDiffIntegralTendsto
  have hIntegralLiminfEq :
      (∫ omega, liminf (fun n => terminalDifference h w τ cutoff n omega)
        atTop ∂mu) =
      (∫ omega, Preg T omega ∂mu) -
        ∫ omega, Ppred (τ omega) omega ∂mu := by
    calc
      (∫ omega, liminf (fun n => terminalDifference h w τ cutoff n omega)
          atTop ∂mu) =
          ∫ omega, Preg T omega - Ppred (τ omega) omega ∂mu :=
        integral_congr_ae hDiffLiminfEqFun
      _ = (∫ omega, Preg T omega ∂mu) -
          ∫ omega, Ppred (τ omega) omega ∂mu :=
        integral_sub hFoundation.Preg_terminal_integrable
          hFoundation.Ppred_sample_integrable
  have hPpredLeIntegral :
      (∫ omega, Preg T omega ∂mu) -
        ∫ omega, Ppred (τ omega) omega ∂mu ≤
      (∫ omega, Preg T omega ∂mu) -
        ∫ omega, Preg (τ omega) omega ∂mu := by
    rw [← hIntegralLiminfEq]
    exact hFatou
  have hSampleIntegralLe :
      ∫ omega, Preg (τ omega) omega ∂mu ≤
        ∫ omega, Ppred (τ omega) omega ∂mu := by
    linarith
  have hSampleIntegralGe :
      ∫ omega, Ppred (τ omega) omega ∂mu ≤
        ∫ omega, Preg (τ omega) omega ∂mu := by
    exact integral_mono_ae hFoundation.Ppred_sample_integrable
      hCandidate.candidate_sample_integrable <| by
      filter_upwards [hLimsup.Ppred_le_Preg] with omega hω
      exact hω (τ omega)
  have hSampleIntegralEq :
      (∫ omega, Ppred (τ omega) omega ∂mu) =
        ∫ omega, Preg (τ omega) omega ∂mu :=
    le_antisymm hSampleIntegralGe hSampleIntegralLe
  have hSampleAE :
      (fun omega => Ppred (τ omega) omega) =ᵐ[mu]
        (fun omega => Preg (τ omega) omega) := by
    apply (integral_eq_iff_of_ae_le
      hFoundation.Ppred_sample_integrable hCandidate.candidate_sample_integrable ?_).mp
    · exact hSampleIntegralEq
    · filter_upwards [hLimsup.Ppred_le_Preg] with omega hω
      exact hω (τ omega)
  exact {
    terminal_difference_liminf_eq := hDiffLiminfEq
    terminal_difference_integral_le := hFatou
    stopped_sample_ae_eq := hSampleAE }

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
