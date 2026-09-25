/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationCadlagRegularization
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Decomposition.Source.Variation

/-!
# A càdlàg `L²` envelope for finite-horizon Doob coordinates

For a square-integrable random envelope, the conditional expectation of its
absolute value is represented by one càdlàg true martingale.  The continuous
time factorial-grid maximal estimate then supplies one square-integrable
random variable which dominates all values before a fixed horizon.  This
module also records the corresponding conditional-expectation estimate for
one-step predictable Doob increments, without replacing the random envelope
by a deterministic bounded-source record.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- The `L²` terminal variable used to generate the absolute-value
conditional-expectation martingale. -/
noncomputable def condExpEnvelopeTerminal
    {Q : Measure Omega}
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q) : Lp Real 2 Q :=
  hξ.norm.toLp (fun omega => ‖ξ omega‖)

/-- The data supplied by the càdlàg conditional-expectation version and its
finite-horizon maximal envelope.  The fields are all analytic facts proved
by the producer below; no stopped-row or final-decomposition conclusion is
assumed here. -/
structure CondExpEnvelopeData
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    [SigmaFiniteFiltration Q F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real) : Prop where
  Z_martingale : Martingale Z F Q
  Z_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Z · omega) (Ici t) t
  Z_leftLimits : ProcessHasLeftLimits Z
  Z_condExp : ∀ t, Z t =ᵐ[Q]
    condExpMartingaleProcess Q F (condExpEnvelopeTerminal ξ hξ) t
  Z_terminal_memLp : MemLp (Z T) (2 : ENNReal) Q
  Gamma_memLp : MemLp Γ (2 : ENNReal) Q
  Gamma_nonneg : ∀ omega, 0 ≤ Γ omega
  Gamma_dominates : ∀ᵐ omega ∂Q, ∀ t, t ≤ T → ‖Z t omega‖ ≤ Γ omega
  Gamma_eLpNorm_le :
    eLpNorm Γ (2 : ENNReal) Q ≤ 2 * eLpNorm (Z T) (2 : ENNReal) Q

/-- A càdlàg conditional-expectation martingale and a square-integrable
maximal envelope exist for every `L²` random variable. -/
theorem exists_cadlag_condExpEnvelopeData_of_memLp_two
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    [SigmaFiniteFiltration Q F]
    (hUsual : Filtration.UsualConditions Q F)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q) (T : NNReal) :
    ∃ (Z : Process Omega) (Γ : Omega → Real),
      CondExpEnvelopeData (F := F) (Q := Q) ξ hξ T Z Γ := by
  let terminal : Lp Real 2 Q := condExpEnvelopeTerminal ξ hξ
  obtain ⟨Z, hZMartingale, hZRight, hZLeft, hZCondExp⟩ :=
    exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual terminal
  have hZTerminal : MemLp (Z T) (2 : ENNReal) Q := by
    have hCond : MemLp
        (condExpMartingaleProcess Q F terminal T)
        (2 : ENNReal) Q := by
      change MemLp (Q[(terminal : Omega → Real) | F T])
        (2 : ENNReal) Q
      exact (Lp.memLp terminal).condExp (by norm_num)
    exact hCond.ae_eq (hZCondExp T).symm
  let Γ : Omega → Real :=
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope Z T
  have hGammaMem : MemLp Γ (2 : ENNReal) Q := by
    exact FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hZMartingale T hZTerminal
  have hGammaBound : ∀ᵐ omega ∂Q, ∀ t, t ≤ T → ‖Z t omega‖ ≤ Γ omega := by
    exact FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hZMartingale T hZTerminal hZRight
  have hGammaNorm :
      eLpNorm Γ (2 : ENNReal) Q ≤ 2 * eLpNorm (Z T) (2 : ENNReal) Q := by
    exact FactorialChronologicalGrid.Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
      hZMartingale T hZTerminal
  refine ⟨Z, Γ, ?_⟩
  refine ⟨hZMartingale, hZRight, hZLeft, ?_, hZTerminal, hGammaMem, ?_,
    hGammaBound, hGammaNorm⟩
  · simpa [terminal, condExpEnvelopeTerminal] using hZCondExp
  · intro omega
    exact Real.sqrt_nonneg _

end HorizonFactorialGrid

namespace ChronologicalGrid

variable {N : Nat} (G : ChronologicalGrid NNReal N)

/-- The one-step predictable Doob increment is controlled by the conditional
expectation of twice the source envelope. -/
private theorem ae_norm_doobPredictableIncrement_le_two_condExpEnvelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    (hSAdapted : StronglyAdapted F S)
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (hSBound : ∀ᵐ omega ∂Q, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (n : Nat) :
    (fun omega => ‖G.doobPredictableIncrement S F Q n omega‖) ≤ᵐ[Q]
      2 * Q[(fun omega => ‖ξ omega‖) |
        G.sampledFiltration F n] := by
  have hSampleMem : ∀ k, MemLp (G.natSample S k) (2 : ENNReal) Q := by
    intro k
    exact sample_memLp_two_of_memLp_two_envelope G hSAdapted ξ hξ hSBound k
  have hIncrementMem : MemLp
      (G.natSample S (n + 1) - G.natSample S n)
      (2 : ENNReal) Q :=
    (hSampleMem (n + 1)).sub (hSampleMem n)
  have hIncrementInt : Integrable
      (G.natSample S (n + 1) - G.natSample S n) Q :=
    hIncrementMem.integrable (by norm_num)
  have hξNorm : MemLp (fun omega => ‖ξ omega‖) (2 : ENNReal) Q := hξ.norm
  have hξNormInt : Integrable (fun omega => ‖ξ omega‖) Q :=
    hξNorm.integrable (by norm_num)
  have hScaledInt : Integrable
      (fun omega => (2 : Real) * ‖ξ omega‖) Q := by
    simpa only [smul_eq_mul] using hξNormInt.const_mul 2
  have hIncrementBound : ∀ᵐ omega ∂Q,
      ‖G.natSample S (n + 1) omega - G.natSample S n omega‖ ≤
        2 * ‖ξ omega‖ := by
    filter_upwards [hSBound] with omega hBound
    rw [Real.norm_eq_abs]
    calc
      |G.natSample S (n + 1) omega - G.natSample S n omega| ≤
          |G.natSample S (n + 1) omega| +
            |G.natSample S n omega| := abs_sub _ _
      _ ≤ ‖ξ omega‖ + ‖ξ omega‖ := by
        exact add_le_add (hBound (G.sampledTime (n + 1)))
          (hBound (G.sampledTime n))
      _ = 2 * ‖ξ omega‖ := by ring
  have hCondNorm :=
    norm_condExp_le (μ := Q) (m := G.sampledFiltration F n)
      (G.natSample S (n + 1) - G.natSample S n)
  have hCondMono :=
    condExp_mono (f := fun omega =>
      ‖G.natSample S (n + 1) omega - G.natSample S n omega‖)
      (g := fun omega => (2 : Real) * ‖ξ omega‖)
      (m₀ := (inferInstance : MeasurableSpace Omega))
      (m := (G.sampledFiltration F n : MeasurableSpace Omega))
      hIncrementInt.norm hScaledInt hIncrementBound
  have hScaledCond :=
    condExp_smul (μ := Q) (m := G.sampledFiltration F n)
      (2 : Real) (fun omega => ‖ξ omega‖)
  have hIncrementEq :
      G.doobPredictableIncrement S F Q n =
        Q[G.natSample S (n + 1) - G.natSample S n |
          G.sampledFiltration F n] := by
    funext omega
    unfold doobPredictableIncrement doobPredictablePart
    rw [predictablePart_add_one]
    simp
  filter_upwards [hCondNorm, hCondMono, hScaledCond] with omega hNorm hMono hScale
  have hEq := congrFun hIncrementEq omega
  calc
    ‖G.doobPredictableIncrement S F Q n omega‖ =
        ‖Q[G.natSample S (n + 1) - G.natSample S n |
          G.sampledFiltration F n] omega‖ := by rw [hEq]
    _ ≤
        Q[(fun omega => ‖G.natSample S (n + 1) omega -
          G.natSample S n omega‖) |
          G.sampledFiltration F n] omega := hNorm
    _ ≤ Q[(fun omega => (2 : Real) * ‖ξ omega‖) |
        G.sampledFiltration F n] omega := hMono
    _ = 2 * Q[(fun omega => ‖ξ omega‖) |
        G.sampledFiltration F n] omega := by
      exact hScale

/-- The conditional expectation appearing in the increment estimate is the
càdlàg envelope martingale at the current grid time, almost everywhere. -/
private theorem ae_eq_condExpEnvelope_at_sampledTime
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    [SigmaFiniteFiltration Q F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (Z : Process Omega)
    (hZCondExp : ∀ t, Z t =ᵐ[Q]
      condExpMartingaleProcess Q F (HorizonFactorialGrid.condExpEnvelopeTerminal ξ hξ) t)
    (t : NNReal) :
    Z t =ᵐ[Q] Q[(fun omega => ‖ξ omega‖) | F t] := by
  have hCoe :
      (HorizonFactorialGrid.condExpEnvelopeTerminal ξ hξ : Omega → Real) =ᵐ[Q]
        (fun omega => ‖ξ omega‖) := by
    exact MemLp.coeFn_toLp hξ.norm
  have hCond :
      condExpMartingaleProcess Q F
          (HorizonFactorialGrid.condExpEnvelopeTerminal ξ hξ) t =ᵐ[Q]
        Q[(fun omega => ‖ξ omega‖) | F t] := by
    simpa [condExpMartingaleProcess] using (condExp_congr_ae hCoe)
  exact (hZCondExp t).trans hCond

end ChronologicalGrid

namespace HorizonFactorialGrid

/-- On a fixed-horizon factorial grid, the predictable increment is bounded
by twice the common càdlàg `L²` envelope. -/
theorem ae_norm_doobPredictableIncrement_le_two_mul_condExpEnvelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    [SigmaFiniteFiltration Q F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂Q, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (r n : Nat)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := Q) ξ hξ T Z Γ) :
    ∀ᵐ omega ∂Q,
      |(grid T r).doobPredictableIncrement S F Q n omega| ≤ 2 * Γ omega := by
  have hTime : (grid T r).sampledTime n ≤ T := by
    unfold ChronologicalGrid.sampledTime
    rw [grid_time]
    exact min_le_right _ _
  have hIncrement :=
    ChronologicalGrid.ae_norm_doobPredictableIncrement_le_two_condExpEnvelope
      (grid T r) hSAdapted ξ hξ hSBound n
  have hZCond :=
    ChronologicalGrid.ae_eq_condExpEnvelope_at_sampledTime ξ hξ
      Z hEnvelope.Z_condExp ((grid T r).sampledTime n)
  have hCondNonneg : ∀ᵐ omega ∂Q,
      0 ≤ Q[(fun omega => ‖ξ omega‖) |
        F ((grid T r).sampledTime n)] omega :=
    condExp_nonneg (m := F ((grid T r).sampledTime n))
      (Filter.Eventually.of_forall fun omega => norm_nonneg (ξ omega))
  filter_upwards [hIncrement, hZCond, hCondNonneg,
    hEnvelope.Gamma_dominates] with omega hInc hZ hCondNonnegOmega hGamma
  have hGammaAt := hGamma ((grid T r).sampledTime n) hTime
  have hZNonneg : 0 ≤ Z ((grid T r).sampledTime n) omega := by
    rw [hZ]
    exact hCondNonnegOmega
  have hZle : Z ((grid T r).sampledTime n) omega ≤ Γ omega := by
    simpa only [Real.norm_of_nonneg hZNonneg] using hGammaAt
  have hBoundAtTime :
      2 * Q[(fun omega => ‖ξ omega‖) |
        F ((grid T r).sampledTime n)] omega ≤ 2 * Γ omega := by
    rw [← hZ]
    exact mul_le_mul_of_nonneg_left hZle (by norm_num)
  have hBound :
      2 * Q[(fun omega => ‖ξ omega‖) |
        (grid T r).sampledFiltration F n] omega ≤ 2 * Γ omega := by
    simpa only [ChronologicalGrid.sampledFiltration_apply] using hBoundAtTime
  simpa only [Real.norm_eq_abs] using hInc.trans hBound

/-- One null set works simultaneously for all levels and all indices of the
fixed-horizon factorial grids. -/
theorem ae_forall_doobPredictableIncrement_le_two_mul_condExpEnvelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {Q : Measure Omega} [IsProbabilityMeasure Q]
    [SigmaFiniteFiltration Q F]
    (ξ : Omega → Real) (hξ : MemLp ξ (2 : ENNReal) Q)
    (hSAdapted : StronglyAdapted F S)
    (hSBound : ∀ᵐ omega ∂Q, ∀ t, |S t omega| ≤ ‖ξ omega‖)
    (T : NNReal) (Z : Process Omega) (Γ : Omega → Real)
    (hEnvelope : CondExpEnvelopeData (F := F) (Q := Q) ξ hξ T Z Γ) :
    ∀ᵐ omega ∂Q, ∀ r n,
      |(grid T r).doobPredictableIncrement S F Q n omega| ≤ 2 * Γ omega := by
  apply ae_all_iff.2
  intro r
  apply ae_all_iff.2
  intro n
  exact ae_norm_doobPredictableIncrement_le_two_mul_condExpEnvelope
    ξ hξ hSAdapted hSBound T r n hEnvelope

end HorizonFactorialGrid

end FTAPTheorem42
