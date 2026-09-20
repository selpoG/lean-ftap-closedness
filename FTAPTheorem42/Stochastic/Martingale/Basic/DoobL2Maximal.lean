/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Envelope
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Doob's finite-horizon `L²` maximal inequality

The pinned mathlib version provides Doob's weak maximal inequality but not
its `Lᵖ` consequence.  This module derives the `p = 2` estimate needed for
the jump control in Delbaen--Schachermayer Corollary 2.4.  The first theorem
is the layer-cake core; its constant is independent of the horizon.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finiteRunningMax_memLp_two
    {μ : Measure Ω} (f : ℕ → Ω → ℝ) (n : ℕ)
    (hf_nonneg : 0 ≤ f)
    (hmeas : ∀ k, k ≤ n → Measurable (f k))
    (hf : ∀ k, k ≤ n → MemLp (f k) (2 : ℝ≥0∞) μ) :
    MemLp (finiteRunningMax f n) (2 : ℝ≥0∞) μ := by
  let M : Ω → ℝ := finiteRunningMax f n
  let sumFn : Ω → ℝ := fun ω =>
    ∑ k ∈ Finset.range (n + 1), |f k ω|
  have hM_meas : AEStronglyMeasurable M μ :=
    (measurable_finiteRunningMax f n hmeas).aestronglyMeasurable
  have hsum_mem : MemLp sumFn (2 : ℝ≥0∞) μ := by
    have hsumEq : sumFn =
        ∑ k ∈ Finset.range (n + 1), fun ω => |f k ω| := by
      funext ω
      simp [sumFn, Finset.sum_apply]
    rw [hsumEq]
    exact memLp_finsetSum' (s := Finset.range (n + 1))
      (fun k hk => (hf k (Nat.le_of_lt_succ (Finset.mem_range.1 hk))).abs)
  apply MemLp.of_le hsum_mem hM_meas
  exact Filter.Eventually.of_forall fun ω => by
    have hM_nonneg : 0 ≤ M ω := finiteRunningMax_nonneg f n hf_nonneg ω
    have hsum_nonneg : 0 ≤ sumFn ω := by
      exact Finset.sum_nonneg fun k hk => abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hM_nonneg,
      Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k => f k ω)
    rw [show M ω = f k ω by simp [M, finiteRunningMax, hkEq]]
    exact (le_abs_self _).trans (Finset.single_le_sum
      (fun j _ => abs_nonneg (f j ω)) hk)

/-- Layer-cake form of the sharp finite-horizon estimate. -/
theorem lintegral_sq_finiteRunningMax_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((finiteRunningMax f n ω) ^ (2 : ℝ)) ∂μ) ≤
      2 * ∫⁻ ω, ENNReal.ofReal
        (finiteRunningMax f n ω * f n ω) ∂μ := by
  let M : Ω → ℝ := finiteRunningMax f n
  let Z : Ω → ℝ := f n
  have hM_meas : Measurable M := by
    exact measurable_finiteRunningMax f n fun k hk =>
      (hf.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hM_nonneg : 0 ≤ M := finiteRunningMax_nonneg f n hf_nonneg
  have hZ_meas : Measurable Z :=
    (hf.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hZ_nonneg : 0 ≤ Z := hf_nonneg n
  let ν : Measure Ω := μ.withDensity fun ω => ENNReal.ofReal (Z ω)
  have : IsFiniteMeasure ν := by
    dsimp [ν]
    exact isFiniteMeasure_withDensity_ofReal (hf.integrable n).hasFiniteIntegral
  have hTail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤ ν {ω | t ≤ M ω} := by
    intro t ht
    let ε : ℝ≥0 := ⟨t, ht.le⟩
    have hMax := MeasureTheory.maximal_ineq hf hf_nonneg (ε := ε) n
    have hEvent : MeasurableSet {ω | t ≤ M ω} :=
      measurableSet_le measurable_const hM_meas
    have hν : ν {ω | t ≤ M ω} =
        ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, Z ω ∂μ) := by
      rw [show ν {ω | t ≤ M ω} =
          ∫⁻ ω in {ω | t ≤ M ω}, ENNReal.ofReal (Z ω) ∂μ by
        exact MeasureTheory.withDensity_apply _ hEvent]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · exact (hf.integrable n).integrableOn
      · exact Filter.Eventually.of_forall fun ω => hZ_nonneg ω
    have hEventEq :
        {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one fun k => f k ω} =
        {ω | t ≤ M ω} := by
      rfl
    rw [hEventEq] at hMax
    have hε : (ε : ℝ≥0∞) = ENNReal.ofReal t := by
      change ENNReal.ofNNReal (⟨t, ht.le⟩ : ℝ≥0) = ENNReal.ofReal t
      exact (ENNReal.ofReal_eq_coe_nnreal ht.le).symm
    rw [hε] at hMax
    calc
      ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤
          ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, Z ω ∂μ) := by
        simpa [ε, Z] using hMax
      _ = ν {ω | t ≤ M ω} := hν.symm
  have hLayerM := MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul
    μ (Filter.Eventually.of_forall hM_nonneg) hM_meas.aemeasurable
    (p_pos := show (0 : ℝ) < 2 by norm_num)
  have hLayerν := MeasureTheory.lintegral_eq_lintegral_meas_le
    ν (Filter.Eventually.of_forall hM_nonneg) hM_meas.aemeasurable
  have hPow : ∀ t : ℝ, t ^ ((2 : ℝ) - 1) = t := by
    intro t
    norm_num [Real.rpow_one]
  have hTailIntegral :
      (∫⁻ t in Ioi (0 : ℝ),
        μ {ω | t ≤ M ω} * ENNReal.ofReal t) ≤
      ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ M ω} := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [mul_comm]
    exact hTail t ht
  rw [show (∫⁻ ω, ENNReal.ofReal ((finiteRunningMax f n ω) ^ (2 : ℝ)) ∂μ) =
      2 * ∫⁻ t in Ioi (0 : ℝ),
        μ {ω | t ≤ M ω} * ENNReal.ofReal t by
    simpa only [M, ENNReal.ofReal_ofNat, hPow] using hLayerM]
  calc
    2 * ∫⁻ t in Ioi (0 : ℝ),
        μ {ω | t ≤ M ω} * ENNReal.ofReal t ≤
        2 * ∫⁻ t in Ioi (0 : ℝ), ν {ω | t ≤ M ω} :=
      by gcongr
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (M ω) ∂ν := by rw [hLayerν]
    _ = 2 * ∫⁻ ω,
        ENNReal.ofReal (M ω) * ENNReal.ofReal (Z ω) ∂μ := by
      rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul μ
        hZ_meas.ennreal_ofReal hM_meas.ennreal_ofReal]
      congr 2
      funext ω
      change ENNReal.ofReal (Z ω) * ENNReal.ofReal (M ω) =
        ENNReal.ofReal (M ω) * ENNReal.ofReal (Z ω)
      exact mul_comm _ _
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (M ω * Z ω) ∂μ := by
      congr 1
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_mul (hM_nonneg ω)]
    _ = 2 * ∫⁻ ω, ENNReal.ofReal
        (finiteRunningMax f n ω * f n ω) ∂μ := rfl

/-- Real-integral form of the layer-cake core. -/
theorem integral_sq_finiteRunningMax_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (n : ℕ) (hcoord : ∀ k, k ≤ n → MemLp (f k) (2 : ℝ≥0∞) μ) :
    (∫ ω, (finiteRunningMax f n ω) ^ 2 ∂μ) ≤
      2 * ∫ ω, finiteRunningMax f n ω * f n ω ∂μ := by
  let M : Ω → ℝ := finiteRunningMax f n
  let Z : Ω → ℝ := f n
  have hM : MemLp M (2 : ℝ≥0∞) μ :=
    finiteRunningMax_memLp_two f n hf_nonneg
      (fun k hk => (hf.stronglyMeasurable k).measurable.le (ℱ.le k)) hcoord
  have hZ : MemLp Z (2 : ℝ≥0∞) μ := hcoord n le_rfl
  have hM_nonneg : 0 ≤ M := finiteRunningMax_nonneg f n hf_nonneg
  have hZ_nonneg : 0 ≤ Z := hf_nonneg n
  have hM2_int : Integrable (fun ω => M ω ^ 2) μ := by
    exact (hM.integrable_mul hM).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hMZ_int : Integrable (fun ω => M ω * Z ω) μ := by
    exact (hM.integrable_mul hZ).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hCore := lintegral_sq_finiteRunningMax_le hf hf_nonneg n
  change (∫ ω, M ω ^ 2 ∂μ) ≤ 2 * ∫ ω, M ω * Z ω ∂μ
  have hM2_nonneg : ∀ᵐ ω ∂μ, 0 ≤ M ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (M ω)
  have hMZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ M ω * Z ω :=
    Filter.Eventually.of_forall fun ω =>
      mul_nonneg (hM_nonneg ω) (hZ_nonneg ω)
  have hCore' : ENNReal.ofReal (∫ ω, M ω ^ 2 ∂μ) ≤
      ENNReal.ofReal (2 * ∫ ω, M ω * Z ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hM2_int hM2_nonneg,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
      ofReal_integral_eq_lintegral_ofReal hMZ_int hMZ_nonneg]
    simpa [M, Z] using hCore
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num) (integral_nonneg_of_ae hMZ_nonneg))).mp hCore'

theorem eLpNorm_two_toReal_eq_sqrt_integral_norm_sq
    {μ : Measure Ω} {g : Ω → ℝ}
    (hg : MemLp g (2 : ℝ≥0∞) μ) :
    (eLpNorm g (2 : ℝ≥0∞) μ).toReal =
      Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have heq := MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
    hp0 hpTop hg
  rw [heq]
  have hInt :
      (∫ ω, ‖g ω‖ ^ (2 : ℝ≥0∞).toReal ∂μ) =
        ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
    norm_num
  rw [hInt]
  have hnonneg : 0 ≤ ∫ ω, ‖g ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖g ω‖)
  rw [ENNReal.toReal_ofReal]
  · rw [Real.sqrt_eq_rpow]
    norm_num
  · exact Real.rpow_nonneg hnonneg _

/-- Doob's finite-horizon `L²` inequality for a nonnegative submartingale. -/
theorem eLpNorm_finiteRunningMax_le_two_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (n : ℕ) (hcoord : ∀ k, k ≤ n → MemLp (f k) (2 : ℝ≥0∞) μ) :
    eLpNorm (finiteRunningMax f n) (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (f n) (2 : ℝ≥0∞) μ := by
  let M : Ω → ℝ := finiteRunningMax f n
  let Z : Ω → ℝ := f n
  have hM : MemLp M (2 : ℝ≥0∞) μ :=
    finiteRunningMax_memLp_two f n hf_nonneg
      (fun k hk => (hf.stronglyMeasurable k).measurable.le (ℱ.le k)) hcoord
  have hZ : MemLp Z (2 : ℝ≥0∞) μ := hcoord n le_rfl
  have hM_nonneg : 0 ≤ M := finiteRunningMax_nonneg f n hf_nonneg
  have hZ_nonneg : 0 ≤ Z := hf_nonneg n
  let a : ℝ := ∫ ω, M ω ^ 2 ∂μ
  let b : ℝ := ∫ ω, Z ω ^ 2 ∂μ
  have ha0 : 0 ≤ a := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (M ω))
  have hb0 : 0 ≤ b := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (Z ω))
  have hcore : a ≤ 2 * ∫ ω, M ω * Z ω ∂μ := by
    simpa [a, M, Z] using
      integral_sq_finiteRunningMax_le hf hf_nonneg n hcoord
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := M) (g := Z)
    Real.HolderConjugate.two_two
      (show MemLp M (ENNReal.ofReal 2) μ by simpa using hM)
      (show MemLp Z (ENNReal.ofReal 2) μ by simpa using hZ)
  have hholder' : (∫ ω, M ω * Z ω ∂μ) ≤
      Real.sqrt a * Real.sqrt b := by
    have hleft : (∫ ω, ‖M ω‖ * ‖Z ω‖ ∂μ) =
        ∫ ω, M ω * Z ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |M ω| * |Z ω| = M ω * Z ω
        rw [abs_of_nonneg (hM_nonneg ω),
          abs_of_nonneg (hZ_nonneg ω)]
    have hrightM : (∫ ω, ‖M ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        Real.sqrt a := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      dsimp [a]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |M ω| ^ (2 : ℝ) = M ω ^ 2
        rw [abs_of_nonneg (hM_nonneg ω)]
        norm_num [Real.rpow_two]
    have hrightZ : (∫ ω, ‖Z ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        Real.sqrt b := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      dsimp [b]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |Z ω| ^ (2 : ℝ) = Z ω ^ 2
        rw [abs_of_nonneg (hZ_nonneg ω)]
        norm_num [Real.rpow_two]
    rw [hleft, hrightM, hrightZ] at hholder
    exact hholder
  have hsqA : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha0
  have hsqB : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb0
  have hsqrt : Real.sqrt a ≤ 2 * Real.sqrt b := by
    have hxy : a ≤ 2 * (Real.sqrt a * Real.sqrt b) :=
      hcore.trans (mul_le_mul_of_nonneg_left hholder' (by norm_num))
    by_cases hx : Real.sqrt a = 0
    · rw [hx]
      positivity
    · have hxpos : 0 < Real.sqrt a :=
        lt_of_le_of_ne (Real.sqrt_nonneg a) (Ne.symm hx)
      nlinarith [Real.sqrt_nonneg b]
  apply (ENNReal.toReal_le_toReal hM.eLpNorm_ne_top
    (ENNReal.mul_ne_top (by norm_num) hZ.eLpNorm_ne_top)).mp
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hM,
    ENNReal.toReal_mul,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hZ]
  norm_num only [ENNReal.toReal_ofNat]
  have hnormM : (∫ ω, ‖M ω‖ ^ 2 ∂μ) = a := by
    dsimp [a]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change |M ω| ^ 2 = M ω ^ 2
      rw [abs_of_nonneg (hM_nonneg ω)]
  have hnormZ : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = b := by
    dsimp [b]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change |Z ω| ^ 2 = Z ω ^ 2
      rw [abs_of_nonneg (hZ_nonneg ω)]
  rw [hnormM, hnormZ]
  exact hsqrt

/-- Terminal square integrability controls every earlier coordinate, and
hence the running maximum, for a nonnegative submartingale. -/
theorem Submartingale.eLpNorm_finiteRunningMax_le_two_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (n : ℕ) (hterminal : MemLp (f n) (2 : ℝ≥0∞) μ) :
    eLpNorm (finiteRunningMax f n) (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (f n) (2 : ℝ≥0∞) μ := by
  apply FTAPTheorem42.eLpNorm_finiteRunningMax_le_two_mul
    hf hf_nonneg n
  intro k hk
  have hcond : MemLp (μ[f n | ℱ k]) (2 : ℝ≥0∞) μ :=
    hterminal.condExp (by norm_num)
  apply MemLp.of_le hcond
    ((hf.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable
  filter_upwards [hf.ae_le_condExp hk,
    condExp_nonneg (Filter.Eventually.of_forall (hf_nonneg n))]
      with ω hle hcond_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg k ω),
    Real.norm_eq_abs, abs_of_nonneg hcond_nonneg]
  exact hle

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Source-independent L2 second-moment comparison

The L2 seminorm comparison used by both bounded and deterministic-bound-free
routes is independent of stopping-time or process structure. Keep this
conversion in a small neutral module so consumers do not inherit the bounded
stopping-time layer merely to compare second moments.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

omit [IsProbabilityMeasure mu] in
/-- An L2 seminorm comparison is equivalently a comparison of the
corresponding second moments. -/
theorem integral_norm_sq_le_of_eLpNorm_two_le
    {f g : Omega -> Real}
    (hf : MemLp f (2 : ENNReal) mu)
    (hg : MemLp g (2 : ENNReal) mu)
    (hfg : eLpNorm f (2 : ENNReal) mu <=
      eLpNorm g (2 : ENNReal) mu) :
    (∫ omega, ‖f omega‖ ^ 2 ∂mu) <=
      ∫ omega, ‖g omega‖ ^ 2 ∂mu := by
  have hReal := ENNReal.toReal_mono hg.eLpNorm_ne_top hfg
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hf,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hg] at hReal
  have hfNonnegative : 0 <= ∫ omega, ‖f omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun omega => sq_nonneg ‖f omega‖)
  have hgNonnegative : 0 <= ∫ omega, ‖g omega‖ ^ 2 ∂mu :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun omega => sq_nonneg ‖g omega‖)
  have hfSqrtNonnegative := Real.sqrt_nonneg
    (∫ omega, ‖f omega‖ ^ 2 ∂mu)
  have hgSqrtNonnegative := Real.sqrt_nonneg
    (∫ omega, ‖g omega‖ ^ 2 ∂mu)
  nlinarith [Real.sq_sqrt hfNonnegative, Real.sq_sqrt hgNonnegative]

end FTAPTheorem42
