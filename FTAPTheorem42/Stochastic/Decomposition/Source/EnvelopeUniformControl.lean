/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsEnvelope
import FTAPTheorem42.Stochastic.Decomposition.Source.EnvelopeFoundation

/-!
# Uniform analytic control for envelope-dominated stopped rows

This module records the first level-independent analytic consequences of the
common gate and the conditional-expectation envelope.  The random control is
kept as data, rather than being put into a deterministic bounded-source
wrapper.  The endpoint deliberately stops before the inverse-row finite
variation estimates, which require a further uniform argument.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

private theorem uniformEnvelope_stoppedSourcePart_abs_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (ξ : Omega → Real)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (a : Real) :
    ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedSourcePart S F mu a n omega| ≤
        2 * ‖ξ omega‖ := by
  filter_upwards [hSBound] with omega hBound
  intro r n
  obtain ⟨k, _hk, hEq⟩ :=
    (grid T r).exists_doobVariationStoppedSourcePart_eq S F mu a n omega
  rw [hEq]
  calc
    |(grid T r).natSample S k omega - (grid T r).natSample S 0 omega| ≤
        |(grid T r).natSample S k omega| +
          |(grid T r).natSample S 0 omega| := abs_sub _ _
    _ ≤ ‖ξ omega‖ + ‖ξ omega‖ := by
      apply add_le_add
      · simpa only [ChronologicalGrid.natSample, Real.norm_eq_abs, abs_abs] using
          hBound ((grid T r).sampledTime k)
      · simpa only [ChronologicalGrid.natSample, Real.norm_eq_abs, abs_abs] using
          hBound ((grid T r).sampledTime 0)
    _ = 2 * ‖ξ omega‖ := by ring

private theorem uniformEnvelope_stoppedAccumulation_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (a : Real) (ha : 0 ≤ a)
    (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ) :
    ∀ᵐ omega ∂mu, ∀ r n,
      (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤
        a + 2 * Γ omega := by
  have hIncrement :=
    ae_forall_doobPredictableIncrement_le_two_mul_condExpEnvelope
      ξ hξ hSAdapted hSBound T Z Γ hEnvelope
  filter_upwards [hIncrement] with omega hIncrementOmega
  intro r n
  apply (grid T r).doobVariationStoppedAccumulation_le S F mu omega ha
    (B := 2 * Γ omega)
  intro k
  exact hIncrementOmega r k

private theorem uniformEnvelope_stoppedPredictablePart_abs_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (a : Real) (ha : 0 ≤ a)
    (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ) :
    ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤
        a + 2 * Γ omega := by
  have hAccum := uniformEnvelope_stoppedAccumulation_le ξ hξ hSAdapted
    hSBound T a ha Z Γ hEnvelope
  filter_upwards [hAccum] with omega hAccumOmega
  intro r n
  exact ((grid T r).abs_doobVariationStoppedPredictablePart_le_accumulation
    S F mu a n omega).trans (hAccumOmega r n)

private theorem uniformEnvelope_stoppedMartingalePart_abs_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (a : Real) (ha : 0 ≤ a)
    (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ) :
    ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedMartingalePart S F mu a n omega| ≤
        a + 2 * Γ omega + 2 * ‖ξ omega‖ := by
  have hSource := uniformEnvelope_stoppedSourcePart_abs_le
    (S := S) (F := F) (mu := mu) ξ hSBound T a
  have hPredictable := uniformEnvelope_stoppedPredictablePart_abs_le ξ hξ
    hSAdapted hSBound T a ha Z Γ hEnvelope
  filter_upwards [hSource, hPredictable] with omega hSourceOmega hPredictableOmega
  intro r n
  have hDecomposition := congrFun
    ((grid T r).doobVariationStoppedSourcePart_eq_add S F mu a n) omega
  simp only [Pi.add_apply] at hDecomposition
  have hEq :
      (grid T r).doobVariationStoppedMartingalePart S F mu a n omega =
        (grid T r).doobVariationStoppedSourcePart S F mu a n omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a n omega := by
    linarith
  rw [hEq]
  calc
    |(grid T r).doobVariationStoppedSourcePart S F mu a n omega -
        (grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤
      |(grid T r).doobVariationStoppedSourcePart S F mu a n omega| +
        |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| :=
      abs_sub _ _
    _ ≤ 2 * ‖ξ omega‖ + (a + 2 * Γ omega) :=
      add_le_add (hSourceOmega r n) (hPredictableOmega r n)
    _ = a + 2 * Γ omega + 2 * ‖ξ omega‖ := by ring

/-! ## The first envelope-specific uniform analytic endpoint -/

/-- Envelope-specific uniform control attached to a common stopped-row
witness.

The feasibility endpoint is retained as data, while the certificate adds
the common random control and the native fixed-grid `L²` facts.  In
particular, the inverse-row estimates, special decomposition, and eventual
limiting conclusion remain supplied by their respective producers and
consumers. -/
structure EnvelopeStoppedRowsNativeUniformControlData
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
  feasibility : EnvelopeDominatedCommonStoppedRowsFeasibilityEndpoint
    (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R
    hUsual hSAdapted hξ hSBound
  control_eq : ∀ omega, C omega = a + 2 * Γ omega + 2 * ‖ξ omega‖
  control_nonneg : ∀ omega, 0 ≤ C omega
  control_memLp : MemLp C (2 : ENNReal) mu
  control_integrable : Integrable C mu
  stoppedAccumulation_le : ∀ᵐ omega ∂mu, ∀ r n,
    (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤ C omega
  stoppedPredictablePart_abs_le : ∀ᵐ omega ∂mu, ∀ r n,
    |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega
  stoppedMartingalePart_abs_le : ∀ᵐ omega ∂mu, ∀ r n,
    |(grid T r).doobVariationStoppedMartingalePart S F mu a n omega| ≤ C omega
  nativeTerminal_memLp : ∀ r, MemLp
    (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
      (2 : ENNReal) mu
  nativeTerminal_abs_le : ∀ r, ∀ᵐ omega ∂mu,
    |(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) omega| ≤
      C omega
  nativeTerminal_eLpNorm_le : ∀ r,
    eLpNorm (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
      (2 : ENNReal) mu ≤ eLpNorm C (2 : ENNReal) mu
  nativeTerminalConvex_memLp : ∀ n, MemLp
    ((u n).apply (fun r =>
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real))) (2 : ENNReal) mu
  nativeTerminalConvex_abs_le : ∀ n, ∀ᵐ omega ∂mu,
    |(u n).apply (fun r =>
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real)) omega| ≤ C omega
  nativeTerminalConvex_eLpNorm_le : ∀ n,
    eLpNorm ((u n).apply (fun r =>
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
        Omega → Real))) (2 : ENNReal) mu ≤ eLpNorm C (2 : ENNReal) mu

/-- The common-gate feasibility endpoint and the càdlàg envelope produce a
single random control for all fixed-horizon grid rows.  The same
`u`, `selection`, `alphaSeq`, and `alpha` supplied by the feasibility
endpoint occur in the returned certificate. -/
theorem exists_envelopeStoppedRowsNativeUniformControlData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    {eta : Real} (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal) (R : Omega → Real)
    (hEndpoint : EnvelopeDominatedCommonStoppedRowsFeasibilityEndpoint
      (S := S) (F := F) (mu := mu) ξ eta u selection a T alphaSeq alpha R
      hUsual hSAdapted hξ hSBound)
    (ha : 0 ≤ a) :
    ∃ C : Omega → Real,
      EnvelopeStoppedRowsNativeUniformControlData ξ hξ T Z Γ hEnvelope eta u selection a
        alphaSeq alpha R hUsual hSAdapted hSBound C := by
  let C : Omega → Real := fun omega =>
    a + 2 * Γ omega + 2 * ‖ξ omega‖
  have hConst : MemLp (fun _omega : Omega => a) (2 : ENNReal) mu :=
    memLp_const a
  have hGamma : MemLp (fun omega => 2 * Γ omega) (2 : ENNReal) mu := by
    simpa only [smul_eq_mul] using hEnvelope.Gamma_memLp.const_mul (2 : Real)
  have hXi : MemLp (fun omega => 2 * ‖ξ omega‖) (2 : ENNReal) mu := by
    simpa only [smul_eq_mul] using hξ.norm.const_mul (2 : Real)
  have hCMem : MemLp C (2 : ENNReal) mu := by
    have hAdd := hConst.add (hGamma.add hXi)
    convert hAdd using 1
    funext omega
    dsimp [C]
    ring
  have hCInt : Integrable C mu := hCMem.integrable (by norm_num)
  have hCNonneg : ∀ omega, 0 ≤ C omega := by
    intro omega
    calc
      0 ≤ a + 2 * Γ omega := add_nonneg ha
        (mul_nonneg zero_le_two (hEnvelope.Gamma_nonneg omega))
      _ ≤ C omega := by
        change a + 2 * Γ omega ≤ a + 2 * Γ omega + 2 * ‖ξ omega‖
        exact le_add_of_nonneg_right
          (mul_nonneg zero_le_two (norm_nonneg (ξ omega)))
  have hAccum := uniformEnvelope_stoppedAccumulation_le
    (S := S) (F := F) (mu := mu) ξ hξ hSAdapted hSBound T a ha Z Γ hEnvelope
  have hPredictable := uniformEnvelope_stoppedPredictablePart_abs_le
    (S := S) (F := F) (mu := mu) ξ hξ hSAdapted hSBound T a ha Z Γ hEnvelope
  have hMartingale := uniformEnvelope_stoppedMartingalePart_abs_le
    (S := S) (F := F) (mu := mu) ξ hξ hSAdapted hSBound T a ha Z Γ hEnvelope
  have hAccumC : ∀ᵐ omega ∂mu, ∀ r n,
      (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤ C omega := by
    filter_upwards [hAccum] with omega hOmega
    intro r n
    calc
      (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤
          a + 2 * Γ omega := hOmega r n
      _ ≤ C omega := by
        change a + 2 * Γ omega ≤ a + 2 * Γ omega + 2 * ‖ξ omega‖
        exact le_add_of_nonneg_right
          (mul_nonneg zero_le_two (norm_nonneg (ξ omega)))
  have hPredictableC : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤
        C omega := by
    filter_upwards [hPredictable] with omega hOmega
    intro r n
    calc
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤
          a + 2 * Γ omega := hOmega r n
      _ ≤ C omega := by
        change a + 2 * Γ omega ≤ a + 2 * Γ omega + 2 * ‖ξ omega‖
        exact le_add_of_nonneg_right
          (mul_nonneg zero_le_two (norm_nonneg (ξ omega)))
  have hMartingaleC : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedMartingalePart S F mu a n omega| ≤
        C omega := by
    filter_upwards [hMartingale] with omega hOmega
    intro r n
    simpa [C] using hOmega r n
  have hNativeMem : ∀ r, MemLp
      (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
      (2 : ENNReal) mu := by
    intro r
    exact Lp.memLp _
  have hNativeBound : ∀ r, ∀ᵐ omega ∂mu,
      |(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) omega| ≤
        C omega := by
    intro r
    let G := grid T r
    have hPartMem : MemLp
        (G.doobVariationStoppedMartingalePart S F mu a (size T r))
        (2 : ENNReal) mu :=
      envelope_doobVariationStoppedMartingalePart_memLp_two
        hSAdapted ξ hξ hSBound G a (size T r)
    have hPartEq :
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real) =ᵐ[mu]
          G.doobVariationStoppedMartingalePart S F mu a (size T r) := by
      simpa [envelopeNativeMartingaleTerminal, G] using
        (MemLp.coeFn_toLp hPartMem)
    have hPartBound : ∀ᵐ omega ∂mu,
        |G.doobVariationStoppedMartingalePart S F mu a (size T r) omega| ≤
          C omega := by
      filter_upwards [hMartingaleC] with omega hOmega
      exact hOmega r (size T r)
    filter_upwards [hPartEq, hPartBound] with omega hEq hBound
    rw [hEq]
    exact hBound
  have hNativeNorm : ∀ r,
      eLpNorm (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
        (2 : ENNReal) mu ≤ eLpNorm C (2 : ENNReal) mu := by
    intro r
    apply eLpNorm_mono_ae_real (Lp.aestronglyMeasurable _)
    filter_upwards [hNativeBound r] with omega hBound
    simpa only [Real.norm_eq_abs] using hBound
  have hNativeConvexMem : ∀ n, MemLp
      ((u n).apply (fun r =>
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real))) (2 : ENNReal) mu := by
    intro n
    have hsum : MemLp
        (∑ r ∈ (u n).support,
          (u n).weight r •
            (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
              Omega → Real)) (2 : ENNReal) mu := by
      apply memLp_finsetSum'
      intro r hr
      exact (hNativeMem r).const_smul ((u n).weight r)
    convert hsum using 1
    ext omega
    simp [TailConvexWeights.apply, smul_eq_mul]
  have hNativeAll : ∀ᵐ omega ∂mu, ∀ r,
      |(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r) omega| ≤
        C omega := by
    apply ae_all_iff.2
    intro r
    exact hNativeBound r
  have hNativeConvexBound : ∀ n, ∀ᵐ omega ∂mu,
      |(u n).apply (fun r =>
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real)) omega| ≤ C omega := by
    intro n
    filter_upwards [hNativeAll] with omega hAll
    unfold TailConvexWeights.apply
    calc
      |∑ r ∈ (u n).support,
          (u n).weight r *
            (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
              omega| ≤
          ∑ r ∈ (u n).support,
            |(u n).weight r *
              (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
                omega| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ (u n).support,
          (u n).weight r *
            |(envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r)
              omega| := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
      _ ≤ ∑ r ∈ (u n).support, (u n).weight r * C omega := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hAll r) ((u n).nonneg r hr)
      _ = C omega := by
        rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]
  have hNativeConvexNorm : ∀ n,
      eLpNorm ((u n).apply (fun r =>
        (envelopeNativeMartingaleTerminal hSAdapted ξ hξ hSBound a T r :
          Omega → Real))) (2 : ENNReal) mu ≤ eLpNorm C (2 : ENNReal) mu := by
    intro n
    apply eLpNorm_mono_ae_real (hNativeConvexMem n).aestronglyMeasurable
    filter_upwards [hNativeConvexBound n] with omega hBound
    simpa only [Real.norm_eq_abs] using hBound
  refine ⟨C, ?_⟩
  exact
    { feasibility := hEndpoint
      control_eq := by intro omega; rfl
      control_nonneg := hCNonneg
      control_memLp := hCMem
      control_integrable := hCInt
      stoppedAccumulation_le := hAccumC
      stoppedPredictablePart_abs_le := hPredictableC
      stoppedMartingalePart_abs_le := hMartingaleC
      nativeTerminal_memLp := hNativeMem
      nativeTerminal_abs_le := hNativeBound
      nativeTerminal_eLpNorm_le := hNativeNorm
      nativeTerminalConvex_memLp := hNativeConvexMem
      nativeTerminalConvex_abs_le := hNativeConvexBound
      nativeTerminalConvex_eLpNorm_le := hNativeConvexNorm }

end HorizonFactorialGrid

end FTAPTheorem42
