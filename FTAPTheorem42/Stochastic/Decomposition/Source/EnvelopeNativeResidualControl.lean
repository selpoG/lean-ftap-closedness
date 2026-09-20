/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.EnvelopeInverseMartingaleControl

/-!
# Native residual control under an `L²` envelope

This module supplies the native residual estimate which is needed before an
inverse-row transform can be controlled.  It keeps the same envelope, gate,
and convex rows as the preceding certificates.  The random control is the
existing native control (with a harmless factor two); no deterministic source
wrapper is introduced.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

noncomputable def envelopeNativeResidual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) : Process Omega :=
  nativeGateGain a T r S F mu -
    envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r

theorem envelopeNativeResidualConvexRow_eq_weighted_sum
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T t : NNReal) (omega : Omega) :
    envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega =
      ∑ r ∈ (u n).support, (u n).weight r *
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega := by
  unfold envelopeNativeResidualConvexRow envelopeNativeResidual
    nativeGateGainConvexRow envelopeNativeMartingaleConvexRow
    TailConvexWeights.apply
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private theorem envelope_nativeGateGain_ae_abs_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (ξ : Omega → Real)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) :
    ∀ᵐ omega ∂mu, ∀ t,
      |nativeGateGain a T r S F mu t omega| ≤
        (size T r : Real) * (2 * ‖ξ omega‖) := by
  filter_upwards [hSBound] with omega hS t
  rw [nativeGateGain_sum]
  calc
    |∑ j ∈ Finset.range (size T r),
        (grid T r).doobVariationGate S F mu a j omega *
          (S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega)| ≤
      ∑ j ∈ Finset.range (size T r),
        |(grid T r).doobVariationGate S F mu a j omega| *
          |S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega| := by
      calc
        _ ≤ ∑ j ∈ Finset.range (size T r),
            |(grid T r).doobVariationGate S F mu a j omega *
              (S (min t ((grid T r).sampledTime (j + 1))) omega -
                S (min t ((grid T r).sampledTime j)) omega)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_mul]
    _ ≤ ∑ _j ∈ Finset.range (size T r), 2 * ‖ξ omega‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hGate := (grid T r).abs_doobVariationGate_le_one
        S F mu a j omega
      have hDiff :
          |S (min t ((grid T r).sampledTime (j + 1))) omega -
            S (min t ((grid T r).sampledTime j)) omega| ≤
          2 * ‖ξ omega‖ := by
        calc
          _ ≤ |S (min t ((grid T r).sampledTime (j + 1))) omega| +
              |S (min t ((grid T r).sampledTime j)) omega| := abs_sub _ _
          _ ≤ ‖ξ omega‖ + ‖ξ omega‖ := by
            exact add_le_add (hS _) (hS _)
          _ = 2 * ‖ξ omega‖ := by ring
      calc
        |(grid T r).doobVariationGate S F mu a j omega| *
            |S (min t ((grid T r).sampledTime (j + 1))) omega -
              S (min t ((grid T r).sampledTime j)) omega| ≤
            1 * (2 * ‖ξ omega‖) := by
          exact mul_le_mul hGate hDiff (abs_nonneg _) (by norm_num)
        _ = 2 * ‖ξ omega‖ := by ring
    _ = (size T r : Real) * (2 * ‖ξ omega‖) := by simp

private theorem envelope_nativeGateGain_stronglyMeasurable_at
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) :
    StronglyMeasurable[F t] (nativeGateGain a T r S F mu t) := by
  have hProgressive : IsStronglyProgressive F S :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous hSAdapted hSRight
  simpa [nativeGateGain] using
    (PredictableElementaryStrategy.stronglyAdapted_gain S hProgressive
      (nativeGateStrategy a T r S F mu) t)

private theorem envelope_nativeGateGain_memLp_two
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) (t : NNReal) :
    MemLp (nativeGateGain a T r S F mu t) (2 : ENNReal) mu := by
  have hBoundMem : MemLp
      (fun omega => (size T r : Real) * (2 * ‖ξ omega‖))
      (2 : ENNReal) mu := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hξ.norm.const_mul ((size T r : Real) * 2)
  apply MemLp.of_le hBoundMem
    ((envelope_nativeGateGain_stronglyMeasurable_at hSAdapted hSRight a T r t).mono
      (F.le t)).aestronglyMeasurable
  filter_upwards [envelope_nativeGateGain_ae_abs_le (F := F) (mu := mu)
    ξ hSBound a T r] with omega hBound
  change |nativeGateGain a T r S F mu t omega| ≤
    |(size T r : Real) * (2 * ‖ξ omega‖)|
  have hRhs : |(size T r : Real) * (2 * ‖ξ omega‖)| =
      (size T r : Real) * (2 * ‖ξ omega‖) := by
    rw [abs_of_nonneg]
    positivity
  rw [hRhs]
  exact hBound t

private theorem envelope_doobVariationStoppedPredictablePart_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (a : Real) (T : NNReal) (r : Nat) :
    StronglyAdapted ((grid T r).sampledFiltration F)
      ((grid T r).doobVariationStoppedPredictablePart S F mu a) := by
  exact DiscretePredictableIntegral.stronglyAdapted_of_stronglyAdapted
    ((grid T r).stronglyAdapted_doobVariationGate S F mu a)
    stronglyAdapted_predictablePart'

private theorem envelope_residual_cell_bound_of_condExp
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Y m A : Process Omega} {t q : NNReal} {D B : Omega → Real}
    (hM : Martingale m F mu)
    (hYtMeas : StronglyMeasurable[F t] (Y t))
    (hYtInt : Integrable (Y t) mu)
    (hYqInt : Integrable (Y q) mu)
    (hmqInt : Integrable (m q) mu)
    (hAInt : Integrable (A q) mu)
    (hAMeas : StronglyMeasurable[F t] (A q))
    (hEq : Y q =ᵐ[mu] m q + A q)
    (htq : t ≤ q)
    (hDiff : ∀ᵐ omega ∂mu, ‖(Y t - Y q) omega‖ ≤ D omega)
    (hDInt : Integrable D mu)
    (hDCond : ∀ᵐ omega ∂mu, mu[D | F t] omega ≤ B omega) :
    ∀ᵐ omega ∂mu,
      |(Y t omega - m t omega) - (Y q omega - m q omega)| ≤ B omega := by
  have hMRel : mu[m q | F t] =ᵐ[mu] m t := hM.condExp_ae_eq htq
  have hACond : mu[A q | F t] =ᵐ[mu] A q :=
    Filter.Eventually.of_forall
      (fun omega => congrFun
        (condExp_of_stronglyMeasurable (F.le t) hAMeas hAInt) omega)
  have hCEY : mu[Y q | F t] =ᵐ[mu] m t + A q := by
    exact (condExp_congr_ae hEq).trans <|
      (condExp_add hmqInt hAInt (F t)).trans <| hMRel.add hACond
  have hYtCond : mu[Y t | F t] =ᵐ[mu] Y t :=
    Filter.Eventually.of_forall
      (fun omega => congrFun
        (condExp_of_stronglyMeasurable (F.le t) hYtMeas hYtInt) omega)
  have hCEdiff : mu[Y t - Y q | F t] =ᵐ[mu]
      Y t - mu[Y q | F t] := by
    exact (condExp_sub hYtInt hYqInt (F t)).trans <|
      hYtCond.sub EventuallyEq.rfl
  have hDiffInt : Integrable (Y t - Y q) mu := hYtInt.sub hYqInt
  have hCondNorm := norm_condExp_le (μ := mu) (m := F t) (Y t - Y q)
  have hCondMono := condExp_mono
    (f := fun omega => ‖(Y t - Y q) omega‖) (g := D)
    (m₀ := (inferInstance : MeasurableSpace Omega))
    (m := (F t : MeasurableSpace Omega)) hDiffInt.norm hDInt hDiff
  filter_upwards [hEq, hCEY, hCEdiff, hCondNorm, hCondMono, hDCond]
    with omega hEqOmega hCEYOmega hCEdiffOmega hNormOmega hMonoOmega hDCondOmega
  have hResidual :
      (Y t omega - m t omega) - (Y q omega - m q omega) =
        mu[Y t - Y q | F t] omega := by
    calc
      (Y t omega - m t omega) - (Y q omega - m q omega) =
          (Y t - mu[Y q | F t]) omega := by
        rw [Pi.sub_apply, hCEYOmega, hEqOmega]
        simp only [Pi.add_apply]
        ring
      _ = mu[Y t - Y q | F t] omega := hCEdiffOmega.symm
  rw [hResidual]
  calc
    |mu[Y t - Y q | F t] omega| ≤
        ‖mu[Y t - Y q | F t] omega‖ := by
          simp only [Real.norm_eq_abs]
          exact le_rfl
    _ ≤ mu[(fun omega => ‖(Y t - Y q) omega‖) | F t] omega := hNormOmega
    _ ≤ mu[D | F t] omega := hMonoOmega
    _ ≤ B omega := hDCondOmega

private theorem envelope_condExp_two_norm_le_two_gamma
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (t : NNReal) (ht : t ≤ T) :
    ∀ᵐ omega ∂mu,
      mu[(fun omega => (2 : Real) * ‖ξ omega‖) | F t] omega ≤
        2 * Γ omega := by
  have hCoe : (condExpEnvelopeTerminal ξ hξ : Omega → Real) =ᵐ[mu]
      (fun omega => ‖ξ omega‖) := MemLp.coeFn_toLp hξ.norm
  have hCond : condExpMartingaleProcess mu F
      (condExpEnvelopeTerminal ξ hξ) t =ᵐ[mu]
        mu[(fun omega => ‖ξ omega‖) | F t] := by
    simpa [condExpMartingaleProcess] using (condExp_congr_ae hCoe)
  have hZ : Z t =ᵐ[mu]
      mu[(fun omega => ‖ξ omega‖) | F t] :=
    (hEnvelope.Z_condExp t).trans hCond
  have hScale := condExp_smul (μ := mu) (m := F t)
    (2 : Real) (fun omega => ‖ξ omega‖)
  have hInput : (2 : Real) • (fun omega => ‖ξ omega‖) =
      (fun omega => (2 : Real) * ‖ξ omega‖) := by
    funext omega
    simp only [Pi.smul_apply, smul_eq_mul]
  have hScale' :
      mu[(fun omega => (2 : Real) * ‖ξ omega‖) | F t] =ᵐ[mu]
        (fun omega => 2 * mu[(fun omega => ‖ξ omega‖) | F t] omega) := by
    rw [← hInput]
    filter_upwards [hScale] with omega hOmega
    simpa only [Pi.smul_apply, smul_eq_mul] using hOmega
  have hGamma : ∀ᵐ omega ∂mu, ‖Z t omega‖ ≤ Γ omega := by
    filter_upwards [hEnvelope.Gamma_dominates] with omega hOmega
    exact hOmega t ht
  filter_upwards [hScale', hZ, hGamma] with omega hScaleOmega hZOmega hGammaOmega
  calc
    mu[(fun omega => (2 : Real) * ‖ξ omega‖) | F t] omega =
        2 * mu[(fun omega => ‖ξ omega‖) | F t] omega := hScaleOmega
    _ = 2 * Z t omega := by rw [← hZOmega]
    _ ≤ 2 * ‖Z t omega‖ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using le_abs_self (Z t omega))
        (by norm_num)
    _ ≤ 2 * Γ omega := by
      exact mul_le_mul_of_nonneg_left hGammaOmega (by norm_num)

theorem envelopeNativeResidual_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) :
    ∀ omega t, ContinuousWithinAt
      (envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r · omega)
      (Ici t) t := by
  intro omega t
  have hGate := PredictableElementaryStrategy.rightContinuous_gain S hSRight
    (nativeGateStrategy a T r S F mu) omega t
  have hMart := (envelopeNativeMartingaleProcess_spec hUsual hSAdapted ξ hξ
    hSBound a T r).2.1 omega t
  change ContinuousWithinAt
    ((fun s => nativeGateGain a T r S F mu s omega) -
      (fun s => envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound
        a T r s omega)) (Ici t) t
  exact hGate.sub hMart

private theorem envelopeNativeResidual_cell_bound_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r q : Nat) (t : NNReal)
    (hq : 0 < q) (hqN : q ≤ size T r)
    (hleft : (grid T r).sampledTime (q - 1) ≤ t)
    (hright : t ≤ (grid T r).sampledTime q)
    (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (C : Omega → Real) (hCMem : MemLp C (2 : ENNReal) mu)
    (hCNonneg : ∀ omega, 0 ≤ C omega)
    (hPredBound : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega) :
    ∀ᵐ omega ∂mu,
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime q) omega| ≤ 2 * Γ omega := by
  let A : Process Omega := fun _omega =>
    (grid T r).doobVariationStoppedPredictablePart S F mu a q
  let M : Process Omega :=
    envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r
  let Y : Process Omega := nativeGateGain a T r S F mu
  have hMspec := envelopeNativeMartingaleProcess_spec
    hUsual hSAdapted ξ hξ hSBound a T r
  have hYtMeas : StronglyMeasurable[F t] (Y t) := by
    simpa [Y] using
      (envelope_nativeGateGain_stronglyMeasurable_at hSAdapted hSRight a T r t)
  have hYtInt : Integrable (Y t) mu := by
    exact (envelope_nativeGateGain_memLp_two hSAdapted hSRight ξ hξ hSBound
      a T r t).integrable (by norm_num)
  have hYqInt : Integrable (Y ((grid T r).sampledTime q)) mu := by
    exact (envelope_nativeGateGain_memLp_two hSAdapted hSRight ξ hξ hSBound
      a T r ((grid T r).sampledTime q)).integrable (by norm_num)
  have hMqInt : Integrable (M ((grid T r).sampledTime q)) mu := by
    exact (envelopeNativeMartingaleProcess_memLp_two hUsual hSAdapted ξ hξ
      hSBound a T r ((grid T r).sampledTime q)).integrable (by norm_num)
  have hAAdapted : StronglyAdapted
      ((grid T r).sampledFiltration F)
      ((grid T r).doobVariationStoppedPredictablePart S F mu a) :=
    envelope_doobVariationStoppedPredictablePart_stronglyAdapted a T r
  have hAMem : MemLp (A ((grid T r).sampledTime q)) (2 : ENNReal) mu := by
    apply MemLp.of_le hCMem
      ((hAAdapted q).mono ((grid T r).sampledFiltration F |>.le q)).aestronglyMeasurable
    filter_upwards [hPredBound] with omega hBound
    have hCAbs : |C omega| = C omega := abs_of_nonneg (hCNonneg omega)
    simpa [A, Real.norm_eq_abs, hCAbs] using hBound r q
  have hAInt : Integrable (A ((grid T r).sampledTime q)) mu :=
    hAMem.integrable (by norm_num)
  have hAMeas : StronglyMeasurable[F t]
      (A ((grid T r).sampledTime q)) := by
    simpa [A] using
      (stoppedPredictablePart_stronglyMeasurable_at_cell
        a T t r q hq hleft)
  have hEq : Y ((grid T r).sampledTime q) =ᵐ[mu]
      M ((grid T r).sampledTime q) + A ((grid T r).sampledTime q) := by
    have hY := nativeGateGain_at_native_grid
      (S := S) (F := F) (mu := mu) a T r q hqN
    have hm := uniformEnvelope_nativeMartingaleProcess_at_sampledTime_ae_eq
      hUsual hSAdapted ξ hξ hSBound a T r q hqN
    have hDec := (grid T r).doobVariationStoppedSourcePart_eq_add S F mu a q
    filter_upwards [hm] with omega hmOmega
    have hDecOmega := congrFun hDec omega
    change nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega =
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T r).sampledTime q) omega +
        (grid T r).doobVariationStoppedPredictablePart S F mu a q omega
    rw [hY omega, hmOmega]
    exact hDecOmega
  have hDiff : ∀ᵐ omega ∂mu, ‖(Y t - Y ((grid T r).sampledTime q)) omega‖ ≤
      (fun omega => (2 : Real) * ‖ξ omega‖) omega := by
    filter_upwards [hSBound] with omega hS
    have hCellT := nativeGateGain_cell_eq
      (S := S) (F := F) (mu := mu) a T r q t omega hq hqN hleft hright
    have hCellQ := nativeGateGain_cell_eq
      (S := S) (F := F) (mu := mu) a T r q
        ((grid T r).sampledTime q) omega hq hqN
        ((grid T r).sampledTime_mono (Nat.sub_le q 1)) le_rfl
    have hDiffEq : nativeGateGain a T r S F mu t omega -
        nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega =
      (grid T r).doobVariationGate S F mu a (q - 1) omega *
        (S t omega - S ((grid T r).sampledTime q) omega) := by
      rw [hCellT, hCellQ]
      ring
    change |nativeGateGain a T r S F mu t omega -
      nativeGateGain a T r S F mu ((grid T r).sampledTime q) omega| ≤
      2 * ‖ξ omega‖
    rw [hDiffEq, abs_mul]
    have hGate := (grid T r).abs_doobVariationGate_le_one S F mu a (q - 1) omega
    have hSdiff : |S t omega - S ((grid T r).sampledTime q) omega| ≤
        2 * ‖ξ omega‖ := by
      calc
        _ ≤ |S t omega| + |S ((grid T r).sampledTime q) omega| := abs_sub _ _
        _ ≤ ‖ξ omega‖ + ‖ξ omega‖ := add_le_add (hS t) (hS _)
        _ = 2 * ‖ξ omega‖ := by ring
    calc
      |(grid T r).doobVariationGate S F mu a (q - 1) omega| *
          |S t omega - S ((grid T r).sampledTime q) omega| ≤
        1 * (2 * ‖ξ omega‖) := mul_le_mul hGate hSdiff (abs_nonneg _) (by norm_num)
      _ = 2 * ‖ξ omega‖ := by ring
  have hDInt : Integrable (fun omega => (2 : Real) * ‖ξ omega‖) mu := by
    simpa only [smul_eq_mul] using (hξ.norm.integrable (by norm_num)).const_mul (2 : Real)
  have hDCond := envelope_condExp_two_norm_le_two_gamma ξ hξ T Z Γ hEnvelope t
    (hright.trans ((grid T r).sampledTime_mono hqN |>.trans_eq (sampledTime_size T r)))
  have hCell := envelope_residual_cell_bound_of_condExp
    (F := F) (mu := mu) (Y := Y) (m := M) (A := A) (t := t)
    (q := (grid T r).sampledTime q)
    (D := fun omega => (2 : Real) * ‖ξ omega‖) (B := fun omega => 2 * Γ omega)
    hMspec.1 hYtMeas hYtInt hYqInt hMqInt hAInt hAMeas hEq hright
    hDiff hDInt hDCond
  simpa [envelopeNativeResidual, Y, M, A] using hCell

/-! The fixed-time estimate is synchronized on the canonical countable
right-dense skeleton before it is extended to all times. -/

theorem envelopeNativeResidual_cell_bound_ae_all
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat)
    (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (C : Omega → Real) (hCMem : MemLp C (2 : ENNReal) mu)
    (hCNonneg : ∀ omega, 0 ≤ C omega)
    (hPredBound : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega) :
    ∀ᵐ omega ∂mu, ∀ (t : NNReal) (ht : t ≤ T),
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime (approxIndex T t ht r).1) omega| ≤
        2 * Γ omega := by
  let D : Omega → Real := fun omega => 2 * Γ omega
  have hSkeleton : ∀ᵐ omega ∂mu, ∀ q i,
      0 < q → q ≤ size T r →
      (grid T r).sampledTime (q - 1) ≤ (stoppedLimitSkeleton T i).1 →
      (stoppedLimitSkeleton T i).1 ≤ (grid T r).sampledTime q →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          (stoppedLimitSkeleton T i).1 omega -
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T r).sampledTime q) omega| ≤ D omega := by
    apply ae_all_iff.2
    intro q
    apply ae_all_iff.2
    intro i
    by_cases hq : 0 < q
    · by_cases hqN : q ≤ size T r
      · by_cases hleft : (grid T r).sampledTime (q - 1) ≤
            (stoppedLimitSkeleton T i).1
        · by_cases hright : (stoppedLimitSkeleton T i).1 ≤
              (grid T r).sampledTime q
          · filter_upwards [envelopeNativeResidual_cell_bound_ae
                hUsual hSAdapted hSRight ξ hξ hSBound a T r q
                (stoppedLimitSkeleton T i).1 hq hqN hleft hright Z Γ
                hEnvelope C hCMem hCNonneg hPredBound] with omega hOmega
            exact fun _ _ _ _ => by simpa [D] using hOmega
          · exact Filter.Eventually.of_forall (fun _omega _ _ _ h =>
              (hright h).elim)
        · exact Filter.Eventually.of_forall (fun _omega _ _ h _ =>
            (hleft h).elim)
      · exact Filter.Eventually.of_forall (fun _omega _ h _ _ =>
          (hqN h).elim)
    · exact Filter.Eventually.of_forall (fun _omega h _ _ _ =>
        (hq h).elim)
  filter_upwards [hSkeleton] with omega hSkeletonOmega
  intro t ht
  have hCellQ : ∀ q, 0 < q → q ≤ size T r →
      (grid T r).sampledTime (q - 1) < t →
      t < (grid T r).sampledTime q →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime q) omega| ≤ D omega := by
    intro q hq hqN hleft hright
    by_contra hnot
    have hgt : D omega <
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime q) omega| := lt_of_not_ge hnot
    have hrightT : (grid T r).sampledTime q ≤ T :=
      (grid T r).sampledTime_mono hqN |>.trans_eq (sampledTime_size T r)
    have htT : t < T := hright.trans_le hrightT
    let tSub : Set.Iic T := ⟨t, htT.le⟩
    let right : NNReal := (grid T r).sampledTime q
    let rightSub : Set.Iic T := ⟨right, hrightT⟩
    have htrightSub : tSub < rightSub := hright
    have hBase : ContinuousWithinAt
        (fun u : Set.Iic T =>
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega)
        (Set.Ici tSub) tSub := by
      have hCont := envelopeNativeResidual_rightContinuous
        hUsual hSAdapted hSRight ξ hξ hSBound a T r omega t
      have hVal : ContinuousWithinAt
          ((↑) : Set.Iic T → NNReal) (Set.Ici tSub) tSub :=
        continuousAt_subtype_val.continuousWithinAt.mono (Set.subset_univ _)
      have hMaps : MapsTo ((↑) : Set.Iic T → NNReal)
          (Set.Ici tSub) (Set.Ici t) := by
        intro v hv
        exact hv
      change ContinuousWithinAt
        ((fun x => envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r x omega) ∘
          Subtype.val) (Set.Ici tSub) tSub
      exact hCont.comp hVal hMaps
    have hContDiff : ContinuousWithinAt
        (fun u : Set.Iic T =>
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r right omega)
        (Set.Ici tSub) tSub := hBase.sub continuousWithinAt_const
    have hNorm : ContinuousWithinAt
        (fun u : Set.Iic T => ‖
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r right omega‖)
        (Set.Ici tSub) tSub := hContDiff.norm
    have hEvNorm : ∀ᶠ u in 𝓝[Set.Ici tSub] tSub,
        D omega < ‖
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r right omega‖ := by
      apply hNorm.eventually
      have hgt' : D omega < ‖
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r right omega‖ := by
        simpa [right, Real.norm_eq_abs] using hgt
      exact Ioi_mem_nhds hgt'
    have hEvRight : ∀ᶠ u in 𝓝[Set.Ici tSub] tSub, u.1 ≤ right := by
      have hIic : Set.Iic rightSub ∈ 𝓝 tSub := Iic_mem_nhds htrightSub
      filter_upwards [mem_nhdsWithin_of_mem_nhds hIic] with u hu
      exact hu
    have hEv : ∀ᶠ u in
        𝓝[Set.range (stoppedLimitSkeleton T) ∩ Set.Ici tSub] tSub,
        D omega < ‖
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r right omega‖ ∧
          u.1 ≤ right :=
      Filter.Eventually.filter_mono
        (nhdsWithin_mono tSub Set.inter_subset_right) (hEvNorm.and hEvRight)
    have hDense := stoppedLimitSkeleton_rightDense T tSub
    have hNe : NeBot
        (𝓝[Set.range (stoppedLimitSkeleton T) ∩ Set.Ici tSub] tSub) :=
      mem_closure_iff_nhdsWithin_neBot.1 hDense
    obtain ⟨u', hu', huMem⟩ := (hEv.and self_mem_nhdsWithin).exists
    rcases huMem.1 with ⟨i, rfl⟩
    have hleftI : (grid T r).sampledTime (q - 1) ≤
        (stoppedLimitSkeleton T i).1 := hleft.le.trans huMem.2
    have hrightI : (stoppedLimitSkeleton T i).1 ≤
        (grid T r).sampledTime q := hu'.2
    have hGrid := hSkeletonOmega q i hq hqN hleftI hrightI
    apply (not_lt_of_ge hGrid)
    simpa [right, Real.norm_eq_abs] using hu'.1
  let q : Nat := (approxIndex T t ht r).1
  change |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
      envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T r).sampledTime q) omega| ≤ D omega
  have hqN : q ≤ size T r :=
    Nat.lt_succ_iff.mp (approxIndex T t ht r).isLt
  have hqTime : (grid T r).sampledTime q =
      (grid T r).time (approxIndex T t ht r) := by
    have hqIndex : (grid T r).natIndex q = approxIndex T t ht r := by
      ext
      change min q (size T r) = (approxIndex T t ht r).1
      exact min_eq_left hqN
    unfold ChronologicalGrid.sampledTime
    rw [hqIndex]
  have hright : t ≤ (grid T r).sampledTime q := by
    rw [hqTime, grid_time_approxIndex]
    exact le_min (FactorialChronologicalGrid.le_approx r t) ht
  by_cases hq0 : q = 0
  · have hceil : Nat.ceil (t * (r.factorial : NNReal)) = 0 := by
      simpa [q, approxIndex] using hq0
    have hmul : t * (r.factorial : NNReal) = 0 :=
      le_antisymm (Nat.ceil_eq_zero.mp hceil) (by positivity)
    have ht0 : t = 0 :=
      (mul_eq_zero.mp hmul).resolve_right (by positivity)
    have hqTime0 : (grid T r).sampledTime q = 0 := by
      rw [hq0]
      simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex, grid_time]
    have htime0 : t = (grid T r).sampledTime q := ht0.trans hqTime0.symm
    simp [htime0, D, hEnvelope.Gamma_nonneg omega]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    by_cases heq : t = (grid T r).sampledTime q
    · simp [heq, D, hEnvelope.Gamma_nonneg omega]
    · have hrightlt : t < (grid T r).sampledTime q := lt_of_le_of_ne hright heq
      have hrightT : (grid T r).sampledTime q ≤ T :=
        (grid T r).sampledTime_mono hqN |>.trans_eq (sampledTime_size T r)
      have htt : t < T := hrightlt.trans_le hrightT
      have hleft : (grid T r).sampledTime (q - 1) < t := by
        apply approxIndex_previous_time_lt T t ht r
        simpa [q] using (Nat.sub_add_cancel hqpos).symm
      simpa [q, D] using hCellQ q hqpos hqN hleft hrightlt

theorem envelopeNativeResidual_at_native_grid_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r k : Nat) (hk : k ≤ size T r) :
    envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T r).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedPredictablePart S F mu a k := by
  have hY := nativeGateGain_at_native_grid
    (S := S) (F := F) (mu := mu) a T r k hk
  have hm := uniformEnvelope_nativeMartingaleProcess_at_sampledTime_ae_eq
    hUsual hSAdapted ξ hξ hSBound a T r k hk
  have hDec := (grid T r).doobVariationStoppedSourcePart_eq_add S F mu a k
  filter_upwards [hm] with omega hmOmega
  have hDecOmega := congrFun hDec omega
  change nativeGateGain a T r S F mu ((grid T r).sampledTime k) omega -
      envelopeNativeMartingaleProcess hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T r).sampledTime k) omega =
    (grid T r).doobVariationStoppedPredictablePart S F mu a k omega
  rw [hY omega, hmOmega]
  simp only [Pi.add_apply] at hDecOmega
  linarith

theorem envelopeNativeResidual_at_base_grid_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (n r k : Nat)
    (hnr : n ≤ r) (hk : k ≤ size T n) :
    envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T n).sampledTime k) =ᵐ[mu]
      (grid T r).doobVariationStoppedPredictablePart S F mu a
        (factorialRatio n r * k) := by
  have hl : factorialRatio n r * k ≤ size T r := by
    rw [← factorialRatio_mul_size T n r hnr]
    exact Nat.mul_le_mul_left _ hk
  have htime : (grid T r).sampledTime (factorialRatio n r * k) =
      (grid T n).sampledTime k := by
    simpa [factorialGridEmbedding] using
      (factorialGridEmbedding_sampledTime T n r hnr k hk)
  have hnative := envelopeNativeResidual_at_native_grid_ae
    hUsual hSAdapted ξ hξ hSBound a T r (factorialRatio n r * k) hl
  filter_upwards [hnative] with omega hOmega
  rw [← htime]
  exact hOmega

theorem envelopeNativeResidual_native_grid_abs_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat) (C : Omega → Real)
    (hPredBound : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega) :
    ∀ᵐ omega ∂mu, ∀ k, k ≤ size T r →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T r).sampledTime k) omega| ≤ C omega := by
  have hGridEq : ∀ᵐ omega ∂mu, ∀ k, k ≤ size T r →
      envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T r).sampledTime k) omega =
        (grid T r).doobVariationStoppedPredictablePart S F mu a k omega := by
    apply ae_all_iff.2
    intro k
    by_cases hk : k ≤ size T r
    · filter_upwards [envelopeNativeResidual_at_native_grid_ae
          hUsual hSAdapted ξ hξ hSBound a T r k hk] with omega hOmega
      intro _hk
      exact hOmega
    · exact Filter.Eventually.of_forall (fun _omega hk' => (hk hk').elim)
  filter_upwards [hGridEq, hPredBound] with omega hEq hBound
  intro k hk
  rw [hEq k hk]
  exact hBound r k

theorem envelopeNativeResidual_baseGridVariation_le_ae
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (n r : Nat) (hnr : n ≤ r)
    (C : Omega → Real)
    (hAccumBound : ∀ᵐ omega ∂mu, ∀ r n,
      (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤ C omega) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime k) omega|) ≤ C omega := by
  have hInc : ∀ k, k < size T n →
      envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime (k + 1)) -
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime k) =ᵐ[mu]
      (fun omega =>
        (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * (k + 1)) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a
            (factorialRatio n r * k) omega) := by
    intro k hk
    have hk0 : k ≤ size T n := hk.le
    have hk1 : k + 1 ≤ size T n := Nat.succ_le_iff.mpr hk
    have h1 := envelopeNativeResidual_at_base_grid_ae
      hUsual hSAdapted ξ hξ hSBound a T n r (k + 1) hnr hk1
    have h0 := envelopeNativeResidual_at_base_grid_ae
      hUsual hSAdapted ξ hξ hSBound a T n r k hnr hk0
    filter_upwards [h1, h0] with omega h1Omega h0Omega
    change envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T n).sampledTime (k + 1)) omega -
      envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
        ((grid T n).sampledTime k) omega = _
    rw [h1Omega, h0Omega]
  have hIncAll : ∀ᵐ omega ∂mu, ∀ k ∈ Finset.range (size T n),
      envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime (k + 1)) omega -
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime k) omega =
      (grid T r).doobVariationStoppedPredictablePart S F mu a
          (factorialRatio n r * (k + 1)) omega -
        (grid T r).doobVariationStoppedPredictablePart S F mu a
          (factorialRatio n r * k) omega := by
    apply ae_all_iff.2
    intro k
    by_cases hk : k < size T n
    · filter_upwards [hInc k hk] with omega hOmega
      intro _hkMem
      exact hOmega
    · exact Filter.Eventually.of_forall (fun _omega hkMem =>
        (hk (Finset.mem_range.mp hkMem)).elim)
  have hVar : ∀ᵐ omega ∂mu, ∀ m,
      (∑ i ∈ Finset.range (size T m),
        |(grid T m).doobVariationStoppedPredictablePart S F mu a (i + 1) omega -
          (grid T m).doobVariationStoppedPredictablePart S F mu a i omega|) ≤ C omega := by
    filter_upwards [hAccumBound] with omega hOmega
    intro m
    rw [(grid T m).sum_abs_doobVariationStoppedPredictablePart_increment]
    exact hOmega m (size T m)
  filter_upwards [hIncAll, hVar] with omega hIncOmega hVarOmega
  calc
    (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime k) omega|) =
      ∑ k ∈ Finset.range (size T n),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * (k + 1)) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a
              (factorialRatio n r * k) omega| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hIncOmega k hk]
    _ ≤ ∑ i ∈ Finset.range (factorialRatio n r * size T n),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a (i + 1) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a i omega| := by
        exact native_sum_abs_sub_mul_le (factorialRatio n r) (size T n)
          (fun i => (grid T r).doobVariationStoppedPredictablePart S F mu a i omega)
    _ = ∑ i ∈ Finset.range (size T r),
        |(grid T r).doobVariationStoppedPredictablePart S F mu a (i + 1) omega -
          (grid T r).doobVariationStoppedPredictablePart S F mu a i omega| := by
        rw [factorialRatio_mul_size T n r hnr]
    _ ≤ C omega := by simpa using hVarOmega r

theorem envelopeNativeResidual_ae_abs_le_on_horizon
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (r : Nat)
    (Z : Process Omega) (Γ C : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (hCMem : MemLp C (2 : ENNReal) mu)
    (hCNonneg : ∀ omega, 0 ≤ C omega)
    (hPredBound : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| ≤
        C omega + 2 * Γ omega := by
  have hGrid := envelopeNativeResidual_native_grid_abs_le_ae
    hUsual hSAdapted ξ hξ hSBound a T r C hPredBound
  have hCell := envelopeNativeResidual_cell_bound_ae_all
    hUsual hSAdapted hSRight ξ hξ hSBound a T r Z Γ hEnvelope C hCMem
    hCNonneg hPredBound
  filter_upwards [hGrid, hCell] with omega hGridOmega hCellOmega
  have hSkeleton : ∀ i, ‖envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound
        a T r (stoppedLimitSkeleton T i).1 omega‖ ≤ C omega + 2 * Γ omega := by
    intro i
    let q : Nat := (approxIndex T (stoppedLimitSkeleton T i).1
      (stoppedLimitSkeleton T i).2 r).1
    have hqN : q ≤ size T r :=
      Nat.lt_succ_iff.mp (approxIndex T (stoppedLimitSkeleton T i).1
        (stoppedLimitSkeleton T i).2 r).isLt
    have hEndpoint := hGridOmega q hqN
    have hCellI : |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound
          a T r (stoppedLimitSkeleton T i).1 omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime q) omega| ≤ 2 * Γ omega := by
      simpa [q] using hCellOmega
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2
    have hAbs : |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound
          a T r (stoppedLimitSkeleton T i).1 omega| ≤
        2 * Γ omega + C omega := by
      calc
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
              (stoppedLimitSkeleton T i).1 omega| =
            |(envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                (stoppedLimitSkeleton T i).1 omega -
              envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T r).sampledTime q) omega) +
              envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T r).sampledTime q) omega| := by
          congr 1
          ring
        _ ≤ |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                (stoppedLimitSkeleton T i).1 omega -
              envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T r).sampledTime q) omega| +
              |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T r).sampledTime q) omega| := abs_add_le _ _
        _ ≤ 2 * Γ omega + C omega := add_le_add hCellI hEndpoint
    simpa only [Real.norm_eq_abs, add_comm] using hAbs
  have hRightContSub : ∀ u : Set.Iic T,
      ContinuousWithinAt
        (fun v : Set.Iic T =>
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r v.1 omega)
        (Set.Ici u) u := by
    intro u
    have hCont := envelopeNativeResidual_rightContinuous
      hUsual hSAdapted hSRight ξ hξ hSBound a T r omega u.1
    have hVal : ContinuousWithinAt ((↑) : Set.Iic T → NNReal)
        (Set.Ici u) u := continuousAt_subtype_val.continuousWithinAt.mono
          (Set.subset_univ _)
    have hMaps : MapsTo ((↑) : Set.Iic T → NNReal)
        (Set.Ici u) (Set.Ici u.1) := by
      intro v hv
      exact hv
    change ContinuousWithinAt
      ((fun x => envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r x omega) ∘
        Subtype.val) (Set.Ici u) u
    exact hCont.comp hVal hMaps
  have hAllSub : ∀ u : Set.Iic T,
      ‖envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r u.1 omega‖ ≤
        C omega + 2 * Γ omega := by
    apply norm_le_of_rightDense_skeleton (stoppedLimitSkeleton T)
      (stoppedLimitSkeleton_rightDense T) _ hRightContSub
    intro i
    exact hSkeleton i
  intro t ht
  simpa only [Real.norm_eq_abs] using hAllSub ⟨t, ht⟩

theorem envelopeNativeResidualConvexRow_ae_abs_le_on_horizon
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (Z : Process Omega) (Γ C : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := mu) ξ hξ T Z Γ)
    (hCMem : MemLp C (2 : ENNReal) mu)
    (hCNonneg : ∀ omega, 0 ≤ C omega)
    (hPredBound : ∀ᵐ omega ∂mu, ∀ r n,
      |(grid T r).doobVariationStoppedPredictablePart S F mu a n omega| ≤ C omega) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega| ≤
        C omega + 2 * Γ omega := by
  have hSupport : ∀ r ∈ (u n).support, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| ≤
        C omega + 2 * Γ omega := by
    intro r hr
    exact envelopeNativeResidual_ae_abs_le_on_horizon hUsual hSAdapted hSRight ξ hξ
      hSBound a T r Z Γ C hEnvelope hCMem hCNonneg hPredBound
  have hAll := (u n).support.eventually_all.mpr hSupport
  filter_upwards [hAll] with omega hOmega t ht
  rw [envelopeNativeResidualConvexRow_eq_weighted_sum]
  calc
    |∑ r ∈ (u n).support, (u n).weight r *
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| ≤
      ∑ r ∈ (u n).support,
        |(u n).weight r *
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ (u n).support, (u n).weight r *
        (C omega + 2 * Γ omega) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
      exact mul_le_mul_of_nonneg_left (hOmega r hr t ht) ((u n).nonneg r hr)
    _ = C omega + 2 * Γ omega := by
      rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]

theorem envelopeNativeResidualConvexRow_baseGridVariation_le_ae
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) mu)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (a : Real) (T : NNReal) (C : Omega → Real)
    (hAccumBound : ∀ᵐ omega ∂mu, ∀ r n,
      (grid T r).doobVariationStoppedAccumulation S F mu a n omega ≤ C omega) :
    ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime k) omega|) ≤ C omega := by
  have hVar : ∀ r ∈ (u n).support, ∀ᵐ omega ∂mu,
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime k) omega|) ≤ C omega := by
    intro r hr
    exact envelopeNativeResidual_baseGridVariation_le_ae hUsual hSAdapted ξ hξ
      hSBound a T n r (by exact (u n).tail r hr) C hAccumBound
  have hAll := (u n).support.eventually_all.mpr hVar
  filter_upwards [hAll] with omega hOmega
  calc
    (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime k) omega|) ≤
      ∑ k ∈ Finset.range (size T n),
        ∑ r ∈ (u n).support, (u n).weight r *
          |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
              ((grid T n).sampledTime (k + 1)) omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
              ((grid T n).sampledTime k) omega| := by
      apply Finset.sum_le_sum
      intro k hk
      have hPoint :
          |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T n).sampledTime (k + 1)) omega -
            envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
              ((grid T n).sampledTime k) omega| ≤
          ∑ r ∈ (u n).support, (u n).weight r *
            |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T n).sampledTime (k + 1)) omega -
              envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                ((grid T n).sampledTime k) omega| := by
        rw [envelopeNativeResidualConvexRow_eq_weighted_sum,
          envelopeNativeResidualConvexRow_eq_weighted_sum]
        rw [← Finset.sum_sub_distrib]
        simp_rw [← mul_sub]
        calc
          _ ≤ ∑ r ∈ (u n).support,
              |(u n).weight r *
                (envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                    ((grid T n).sampledTime (k + 1)) omega -
                  envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
                    ((grid T n).sampledTime k) omega)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
      exact hPoint
    _ = ∑ r ∈ (u n).support, (u n).weight r *
        (∑ k ∈ Finset.range (size T n),
          |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
              ((grid T n).sampledTime (k + 1)) omega -
            envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
              ((grid T n).sampledTime k) omega|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum]
    _ ≤ ∑ r ∈ (u n).support, (u n).weight r * C omega := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hOmega r hr) ((u n).nonneg r hr)
    _ = C omega := by
      rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]

/-! ## Native residual certificate

The certificate below is still envelope-specific.  Its feasibility field is
the preceding native-control certificate, so the gate, convex rows, and all
stopping data are kept unchanged.  It records only the native residual
estimates proved in this module; inverse transforms and common-alpha
residuals are intentionally not fields here.
-/

structure EnvelopeStoppedRowsNativeResidualControlData
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
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real) : Prop where
  nativeControl : EnvelopeStoppedRowsNativeUniformControlData ξ hξ T Z Γ hEnvelope eta u
    selection a alphaSeq alpha R hUsual hSAdapted hSBound C
  residualControl_memLp : MemLp (fun omega => C omega + 2 * Γ omega)
    (2 : ENNReal) mu
  residualControl_integrable : Integrable (fun omega => C omega + 2 * Γ omega) mu
  residualControl_nonneg : ∀ omega, 0 ≤ C omega + 2 * Γ omega
  nativeResidual_cell_bound : ∀ᵐ omega ∂mu, ∀ r (t : NNReal) (ht : t ≤ T),
    |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T r).sampledTime (approxIndex T t ht r).1) omega| ≤ 2 * Γ omega
  nativeResidual_horizon_bound : ∀ᵐ omega ∂mu, ∀ r (t : NNReal), t ≤ T →
    |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| ≤
      C omega + 2 * Γ omega
  nativeResidual_baseGridVariation : ∀ᵐ omega ∂mu, ∀ n r, n ≤ r →
    (∑ k ∈ Finset.range (size T n),
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime (k + 1)) omega -
        envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
          ((grid T n).sampledTime k) omega|) ≤ C omega
  convexResidual_horizon_bound : ∀ᵐ omega ∂mu, ∀ n (t : NNReal), t ≤ T →
    |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega| ≤
      C omega + 2 * Γ omega
  convexResidual_baseGridVariation : ∀ᵐ omega ∂mu, ∀ n,
    (∑ k ∈ Finset.range (size T n),
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
          ((grid T n).sampledTime (k + 1)) omega -
        envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
          ((grid T n).sampledTime k) omega|) ≤ C omega

/-- Consume the native envelope certificate and add the common-AE native
residual bounds, without changing its convex weights or stopping data. -/
theorem exists_envelopeStoppedRowsNativeResidualControlData
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
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (C : Omega → Real)
    (hNativeControl : EnvelopeStoppedRowsNativeUniformControlData ξ hξ T Z Γ hEnvelope eta u
      selection a alphaSeq alpha R hUsual hSAdapted hSBound C) :
    EnvelopeStoppedRowsNativeResidualControlData ξ hξ T Z Γ hEnvelope eta u selection a
      alphaSeq alpha R hUsual hSAdapted hSRight hSBound C := by
  have hGammaMem : MemLp (fun omega => 2 * Γ omega) (2 : ENNReal) mu := by
    simpa only [smul_eq_mul] using hEnvelope.Gamma_memLp.const_mul (2 : Real)
  have hResidualMem : MemLp (fun omega => C omega + 2 * Γ omega)
      (2 : ENNReal) mu := by
    exact hNativeControl.control_memLp.add hGammaMem
  have hResidualInt : Integrable (fun omega => C omega + 2 * Γ omega) mu :=
    hResidualMem.integrable (by norm_num)
  have hResidualNonneg : ∀ omega, 0 ≤ C omega + 2 * Γ omega := by
    intro omega
    exact add_nonneg (hNativeControl.control_nonneg omega)
      (mul_nonneg zero_le_two (hEnvelope.Gamma_nonneg omega))
  have hCell : ∀ᵐ omega ∂mu, ∀ r (t : NNReal) (ht : t ≤ T),
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T r).sampledTime (approxIndex T t ht r).1) omega| ≤ 2 * Γ omega := by
    apply ae_all_iff.2
    intro r
    exact envelopeNativeResidual_cell_bound_ae_all hUsual hSAdapted hSRight ξ hξ hSBound
      a T r Z Γ hEnvelope C hNativeControl.control_memLp hNativeControl.control_nonneg
      hNativeControl.stoppedPredictablePart_abs_le
  have hHorizon : ∀ᵐ omega ∂mu, ∀ r (t : NNReal), t ≤ T →
      |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r t omega| ≤
        C omega + 2 * Γ omega := by
    apply ae_all_iff.2
    intro r
    exact envelopeNativeResidual_ae_abs_le_on_horizon hUsual hSAdapted hSRight ξ hξ
      hSBound a T r Z Γ C hEnvelope hNativeControl.control_memLp
      hNativeControl.control_nonneg hNativeControl.stoppedPredictablePart_abs_le
  have hVariation : ∀ᵐ omega ∂mu, ∀ n r, n ≤ r →
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidual hUsual hSAdapted ξ hξ hSBound a T r
            ((grid T n).sampledTime k) omega|) ≤ C omega := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro r
    by_cases hnr : n ≤ r
    · filter_upwards [envelopeNativeResidual_baseGridVariation_le_ae hUsual hSAdapted ξ hξ
          hSBound a T n r hnr C hNativeControl.stoppedAccumulation_le] with omega hOmega hnr'
      exact hOmega
    · exact Filter.Eventually.of_forall (fun _omega hnr' => (hnr hnr').elim)
  have hConvexHorizon : ∀ᵐ omega ∂mu, ∀ n (t : NNReal), t ≤ T →
      |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T t omega| ≤
        C omega + 2 * Γ omega := by
    apply ae_all_iff.2
    intro n
    exact envelopeNativeResidualConvexRow_ae_abs_le_on_horizon u n hUsual hSAdapted hSRight
      ξ hξ hSBound a T Z Γ C hEnvelope hNativeControl.control_memLp
      hNativeControl.control_nonneg hNativeControl.stoppedPredictablePart_abs_le
  have hConvexVariation : ∀ᵐ omega ∂mu, ∀ n,
      (∑ k ∈ Finset.range (size T n),
        |envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime (k + 1)) omega -
          envelopeNativeResidualConvexRow u n hUsual hSAdapted ξ hξ hSBound a T
            ((grid T n).sampledTime k) omega|) ≤ C omega := by
    apply ae_all_iff.2
    intro n
    exact envelopeNativeResidualConvexRow_baseGridVariation_le_ae u n hUsual hSAdapted ξ hξ
      hSBound a T C hNativeControl.stoppedAccumulation_le
  exact
    { nativeControl := hNativeControl
      residualControl_memLp := hResidualMem
      residualControl_integrable := hResidualInt
      residualControl_nonneg := hResidualNonneg
      nativeResidual_cell_bound := hCell
      nativeResidual_horizon_bound := hHorizon
      nativeResidual_baseGridVariation := hVariation
      convexResidual_horizon_bound := hConvexHorizon
      convexResidual_baseGridVariation := hConvexVariation }

end HorizonFactorialGrid

end FTAPTheorem42
