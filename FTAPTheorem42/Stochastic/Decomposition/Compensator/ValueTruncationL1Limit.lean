/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncation

/-!
# Terminal `L¹` limit of value-truncated projections

The nested value-truncation projections have a common almost-everywhere
process order.  Their terminal expectations are bounded by the integrable
terminal value of the original increasing source.  This module turns those
facts into a concrete real-valued terminal limit and records the `L¹`
convergence of both the projections and the residuals.

Only terminal-time statements are made here.  No process-level regularity or
martingale assertion is inferred for the limiting residual.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Terminal limit certificate -/

/-- Terminal `L¹` data extracted from a nested value-truncation projection
family.  The limit is a raw real-valued representative; no process version is
chosen for it. -/
structure ValueTruncationProjectionTerminalL1Limit
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T) where
  limit : Ω → Real
  limit_integrable : Integrable limit mu
  source_terminal_l1_tendsto : Tendsto
    (fun n => eLpNorm (fun omega =>
      valueTruncation U n T omega - U T omega) 1 mu)
    atTop (𝓝 0)
  projection_terminal_tendsto_ae : ∀ᵐ omega ∂mu, Tendsto
    (fun n => (family.data n).Vp T omega) atTop (𝓝 (limit omega))
  projection_terminal_l1_tendsto : Tendsto
    (fun n => eLpNorm (fun omega =>
      (family.data n).Vp T omega - limit omega) 1 mu)
    atTop (𝓝 0)
  projection_terminal_integral_eq_source :
    (∫ omega, limit omega ∂mu) = ∫ omega, U T omega ∂mu
  residual_terminal_limit_integrable : Integrable (fun omega =>
    U T omega - limit omega) mu
  residual_terminal_integrable : ∀ n, Integrable (fun omega =>
    valueTruncation U n T omega - (family.data n).Vp T omega) mu
  residual_terminal_tendsto_ae : ∀ᵐ omega ∂mu, Tendsto
    (fun n => valueTruncation U n T omega - (family.data n).Vp T omega)
      atTop (𝓝 (U T omega - limit omega))
  residual_terminal_integral_eq_zero :
    (∫ omega, U T omega - limit omega ∂mu) = 0
  residual_terminal_l1_tendsto : Tendsto
    (fun n => eLpNorm (fun omega =>
      (valueTruncation U n T omega - (family.data n).Vp T omega) -
        (U T omega - limit omega)) 1 mu)
    atTop (𝓝 0)

/-! ## Source and projection terminal limits -/

omit [SigmaFiniteFiltration mu F] in
theorem ValueTruncationProjectionFamily.exists_terminalL1Limit
    [F.IsRightContinuous]
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F)
    (hUT : Integrable (U T) mu) :
    Nonempty (ValueTruncationProjectionTerminalL1Limit
      (F := F) (mu := mu) family) := by
  let p : ℕ → Ω → Real := fun n omega => (family.data n).Vp T omega
  let s : Ω → ENNReal := fun omega => ⨆ n, ENNReal.ofReal (p n omega)
  let limit : Ω → Real := fun omega => ⨆ n, p n omega
  have hpInt : ∀ n, Integrable (p n) mu := by
    intro n
    exact (family.data n).projection.Vp_terminal_integrable
  have hpNonneg : ∀ n omega, 0 ≤ p n omega := by
    intro n omega
    exact ((family.data n).projection.projection_ready.predictable_version.Vp_nonnegative)
      omega T
  have hpMono : ∀ᵐ omega ∂mu, Monotone (fun n => p n omega) := by
    have hsucc : ∀ᵐ omega ∂mu, ∀ n, p n omega ≤ p (n + 1) omega := by
      apply ae_all_iff.mpr
      intro n
      filter_upwards [family.projection_order hU hUsual (Nat.le_succ n)] with omega hω
      exact hω T
    filter_upwards [hsucc] with omega hω
    exact monotone_nat_of_le_succ hω
  have hqMeas : ∀ n, AEMeasurable
      (fun omega => ENNReal.ofReal (p n omega)) mu := by
    intro n
    exact (hpInt n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hqMono : ∀ᵐ omega ∂mu,
      Monotone (fun n => ENNReal.ofReal (p n omega)) := by
    filter_upwards [hpMono] with omega hω n m hnm
    exact ENNReal.ofReal_le_ofReal (hω hnm)
  have hsMeas : AEMeasurable s mu := by
    exact AEMeasurable.iSup hqMeas
  have hSourceInt : ∀ n, Integrable (valueTruncation U n T) mu := by
    intro n
    apply hUT.mono_nonneg
      ((hU.valueTruncation_stronglyAdapted n T).mono (F.le T)).aestronglyMeasurable
    · exact Eventually.of_forall (fun omega => hU.valueTruncation_nonneg n T omega)
    · exact Eventually.of_forall (fun omega => hU.valueTruncation_le_source n T omega)
  have hSourceIntTendsto : Tendsto
      (fun n => ∫ omega, valueTruncation U n T omega ∂mu) atTop
      (𝓝 (∫ omega, U T omega ∂mu)) := by
    apply integral_tendsto_of_tendsto_of_monotone hSourceInt hUT
    · exact Eventually.of_forall (fun omega n m hnm =>
        NormalizedAdaptedCadlagIncreasingProcessData.valueTruncation_mono_level
          hnm T omega)
    · exact Eventually.of_forall (fun omega =>
        NormalizedAdaptedCadlagIncreasingProcessData.valueTruncation_tendsto_source
          T omega)
  have hProjectionIntTendsto : Tendsto
      (fun n => ∫ omega, p n omega ∂mu) atTop
      (𝓝 (∫ omega, U T omega ∂mu)) := by
    apply Filter.Tendsto.congr (fun n => by
      exact (family.projection_terminal_integral_eq_source n).symm) hSourceIntTendsto
  have hqIntegralLe : ∀ n,
      (∫⁻ omega, ENNReal.ofReal (p n omega) ∂mu) ≤
        ENNReal.ofReal (∫ omega, U T omega ∂mu) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hpInt n)
      (Eventually.of_forall (hpNonneg n))]
    rw [family.projection_terminal_integral_eq_source n]
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono_ae (hSourceInt n) hUT
    exact Eventually.of_forall (fun omega => hU.valueTruncation_le_source n T omega)
  have hsIntegralEq :
      (∫⁻ omega, s omega ∂mu) = ⨆ n, ∫⁻ omega, ENNReal.ofReal (p n omega) ∂mu := by
    exact lintegral_iSup' hqMeas hqMono
  have hsFinite : (∫⁻ omega, s omega ∂mu) ≠ ∞ := by
    rw [hsIntegralEq]
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact iSup_le hqIntegralLe
  have hsFiniteAE : ∀ᵐ omega ∂mu, s omega < ∞ :=
    ae_lt_top' hsMeas hsFinite
  have hLimitMeas : AEMeasurable limit mu := by
    exact AEMeasurable.iSup (fun n => (hpInt n).aestronglyMeasurable.aemeasurable)
  have hpLimitAE : ∀ᵐ omega ∂mu, Tendsto
      (fun n => p n omega) atTop (𝓝 (limit omega)) := by
    filter_upwards [hpMono, hsFiniteAE] with omega hmono hsfinite
    have hbound : BddAbove (Set.range (fun n => p n omega)) := by
      refine ⟨(s omega).toReal, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa only [ENNReal.toReal_ofReal (hpNonneg n omega)] using
        ENNReal.toReal_mono hsfinite.ne
          (le_iSup (fun n => ENNReal.ofReal (p n omega)) n)
    simpa [limit] using tendsto_atTop_ciSup hmono hbound
  have hLimitNonneg : ∀ᵐ omega ∂mu, 0 ≤ limit omega := by
    filter_upwards [hpLimitAE] with omega hω
    exact ge_of_tendsto' hω (fun n => hpNonneg n omega)
  have hOfRealLimitAE : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (limit omega) = s omega := by
    filter_upwards [hpLimitAE, hqMono] with omega hplimit hqmono
    apply tendsto_nhds_unique
      ((ENNReal.continuous_ofReal.tendsto _).comp hplimit)
      (tendsto_atTop_iSup hqmono)
  have hLimitOfRealFinite :
      (∫⁻ omega, ENNReal.ofReal (limit omega) ∂mu) ≠ ∞ := by
    have hEq : (∫⁻ omega, ENNReal.ofReal (limit omega) ∂mu) =
        ∫⁻ omega, s omega ∂mu := lintegral_congr_ae hOfRealLimitAE
    rw [hEq]
    exact hsFinite
  have hLimitInt : Integrable limit mu := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hLimitMeas.aestronglyMeasurable hLimitNonneg).mp
    exact hLimitOfRealFinite
  have hLimitIntegralEq :
      (∫ omega, limit omega ∂mu) = ∫ omega, U T omega ∂mu := by
    have hLimitIntTendsto : Tendsto
        (fun n => ∫ omega, p n omega ∂mu) atTop
        (𝓝 (∫ omega, limit omega ∂mu)) :=
      integral_tendsto_of_tendsto_of_monotone hpInt hLimitInt hpMono hpLimitAE
    exact tendsto_nhds_unique hLimitIntTendsto hProjectionIntTendsto
  have hpLeLimit : ∀ᵐ omega ∂mu, ∀ n, p n omega ≤ limit omega := by
    filter_upwards [hpLimitAE, hpMono] with omega hω hmono n
    exact hmono.ge_of_tendsto hω n
  have hSourceBoundIntegral :
      (∫⁻ omega, ENNReal.ofReal (U T omega) ∂mu) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hUT
      (Eventually.of_forall (fun omega => hU.value_nonneg T omega))]
    exact ENNReal.ofReal_ne_top
  have hSourceDiffMeas : ∀ n, AEMeasurable
      (fun omega => ENNReal.ofReal
        (|valueTruncation U n T omega - U T omega|)) mu := by
    intro n
    exact ((hSourceInt n).sub hUT).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hSourceDiffBound : ∀ n, ∀ᵐ omega ∂mu,
      ENNReal.ofReal (|valueTruncation U n T omega - U T omega|) ≤
        ENNReal.ofReal (U T omega) := by
    intro n
    filter_upwards [] with omega
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonpos (sub_nonpos.mpr
      (hU.valueTruncation_le_source n T omega))]
    linarith [hU.valueTruncation_nonneg n T omega]
  have hSourceDiffTendsto : ∀ᵐ omega ∂mu, Tendsto
      (fun n => ENNReal.ofReal
        (|valueTruncation U n T omega - U T omega|)) atTop (𝓝 0) := by
    filter_upwards [] with omega
    have hReal : Tendsto
        (fun n => |valueTruncation U n T omega - U T omega|)
        atTop (𝓝 0) := by
      have h := (NormalizedAdaptedCadlagIncreasingProcessData.valueTruncation_tendsto_source
        (U := U) T omega).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => U T omega)
            atTop (𝓝 (U T omega)))
      simpa only [Real.norm_eq_abs, sub_self, norm_zero] using h.norm
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hReal
  have hSourceDiffL1 : Tendsto
      (fun n => eLpNorm (fun omega =>
        valueTruncation U n T omega - U T omega) 1 mu) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun omega => ENNReal.ofReal (U T omega)) hSourceDiffMeas
      hSourceDiffBound hSourceBoundIntegral hSourceDiffTendsto
    have h' : Tendsto (fun n => ∫⁻ omega,
        ENNReal.ofReal |valueTruncation U n T omega - U T omega| ∂mu)
        atTop (𝓝 0) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    rw [eLpNorm_one_eq_lintegral_enorm (f := fun omega => valueTruncation U n T omega - U T omega)
      (by exact ((hSourceInt n).sub hUT).aestronglyMeasurable)]
    simp only [Real.enorm_eq_ofReal_abs]
  have hProjectionBoundIntegral :
      (∫⁻ omega, ENNReal.ofReal (limit omega) ∂mu) ≠ ∞ := by
    exact hLimitOfRealFinite
  have hProjectionDiffMeas : ∀ n, AEMeasurable
      (fun omega => ENNReal.ofReal (|p n omega - limit omega|)) mu := by
    intro n
    exact ((hpInt n).sub hLimitInt).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hProjectionDiffBound : ∀ n, ∀ᵐ omega ∂mu,
      ENNReal.ofReal (|p n omega - limit omega|) ≤
        ENNReal.ofReal (limit omega) := by
    intro n
    filter_upwards [hpLeLimit, hLimitNonneg] with omega hle hlim
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonpos (sub_nonpos.mpr (hle n))]
    linarith [hpNonneg n omega]
  have hProjectionDiffTendsto : ∀ᵐ omega ∂mu, Tendsto
      (fun n => ENNReal.ofReal (|p n omega - limit omega|)) atTop (𝓝 0) := by
    filter_upwards [hpLimitAE] with omega hω
    have hReal : Tendsto (fun n => |p n omega - limit omega|)
        atTop (𝓝 0) := by
      have h := hω.sub (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => limit omega) atTop (𝓝 (limit omega)))
      simpa only [Real.norm_eq_abs, sub_self, norm_zero] using h.norm
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hReal
  have hProjectionL1 : Tendsto
      (fun n => eLpNorm (fun omega => p n omega - limit omega) 1 mu)
        atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun omega => ENNReal.ofReal (limit omega)) hProjectionDiffMeas
      hProjectionDiffBound hProjectionBoundIntegral hProjectionDiffTendsto
    have h' : Tendsto (fun n => ∫⁻ omega, ENNReal.ofReal |p n omega - limit omega| ∂mu)
        atTop (𝓝 0) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    rw [eLpNorm_one_eq_lintegral_enorm (f := fun omega => p n omega - limit omega)
      (by exact ((hpInt n).sub hLimitInt).aestronglyMeasurable)]
    simp only [Real.enorm_eq_ofReal_abs]
  have hResidualAE : ∀ᵐ omega ∂mu, Tendsto
      (fun n => valueTruncation U n T omega - p n omega) atTop
        (𝓝 (U T omega - limit omega)) := by
    filter_upwards [Eventually.of_forall (fun omega =>
        NormalizedAdaptedCadlagIncreasingProcessData.valueTruncation_tendsto_source
          (U := U) T omega), hpLimitAE] with omega hSource hProjection
    exact hSource.sub hProjection
  have hResidualBound : ∀ n,
      eLpNorm (fun omega =>
        (valueTruncation U n T omega - p n omega) -
          (U T omega - limit omega)) 1 mu ≤
        eLpNorm (fun omega => valueTruncation U n T omega - U T omega)
          1 mu +
        eLpNorm (fun omega => p n omega - limit omega) 1 mu := by
    intro n
    have hRewrite : (fun omega =>
        (valueTruncation U n T omega - p n omega) -
          (U T omega - limit omega)) =
        (fun omega => (valueTruncation U n T omega - U T omega) -
          (p n omega - limit omega)) := by
      funext omega
      ring
    rw [hRewrite]
    exact eLpNorm_sub_le (by norm_num)
  have hResidualL1 : Tendsto
      (fun n => eLpNorm (fun omega =>
        (valueTruncation U n T omega - p n omega) -
          (U T omega - limit omega)) 1 mu) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n =>
        eLpNorm (fun omega => valueTruncation U n T omega - U T omega)
          1 mu +
        eLpNorm (fun omega => p n omega - limit omega) 1 mu)
        atTop (𝓝 0) := by
      simpa only [zero_add] using hSourceDiffL1.add hProjectionL1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal))
        atTop (𝓝 0)) hsum
      (fun _ => bot_le) hResidualBound
  have hResidualInt : ∀ n, Integrable (fun omega =>
      valueTruncation U n T omega - p n omega) mu := by
    intro n
    exact (hSourceInt n).sub (hpInt n)
  have hResidualIntegralEqZero :
      (∫ omega, U T omega - limit omega ∂mu) = 0 := by
    rw [integral_sub hUT hLimitInt, hLimitIntegralEq]
    ring
  exact ⟨{
    limit := limit
    limit_integrable := hLimitInt
    source_terminal_l1_tendsto := hSourceDiffL1
    projection_terminal_tendsto_ae := hpLimitAE
    projection_terminal_l1_tendsto := hProjectionL1
    projection_terminal_integral_eq_source := hLimitIntegralEq
    residual_terminal_limit_integrable := hUT.sub hLimitInt
    residual_terminal_integrable := hResidualInt
    residual_terminal_tendsto_ae := hResidualAE
    residual_terminal_integral_eq_zero := hResidualIntegralEqZero
    residual_terminal_l1_tendsto := hResidualL1 }⟩

end HorizonFactorialGrid

end FTAPTheorem42
