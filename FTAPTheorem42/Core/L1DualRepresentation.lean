/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.VectorMeasure.AddContent
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import FTAPTheorem42.Core.WeakStar

/-!
# Set function induced by a continuous functional on `L¹`

For a finite measure, a continuous functional on `L¹` can be evaluated on
the characteristic function of a measurable set.  This file records the
elementary measure-like properties of that set function.  The full `L¹`
duality theorem is deliberately not assumed here.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The value of an `L¹` functional on the indicator of a measurable set. -/
noncomputable def l1DualSetValue (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) (s : Set Ω) (hs : MeasurableSet s) : ℝ :=
  Λ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))

theorem l1DualSetValue_union_of_disjoint (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    l1DualSetValue μ Λ (s ∪ t) (hs.union ht) =
      l1DualSetValue μ Λ s hs + l1DualSetValue μ Λ t ht := by
  change Λ (indicatorConstLp 1 (hs.union ht) (measure_ne_top μ (s ∪ t)) (1 : ℝ)) =
    Λ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) +
      Λ (indicatorConstLp 1 ht (measure_ne_top μ t) (1 : ℝ))
  rw [indicatorConstLp_disjoint_union hs ht (measure_ne_top μ s)
    (measure_ne_top μ t) hst (1 : ℝ), map_add]

theorem l1DualSetValue_abs_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s : Set Ω} (hs : MeasurableSet s) :
    |l1DualSetValue μ Λ s hs| ≤ ‖Λ‖ * μ.real s := by
  calc
    |l1DualSetValue μ Λ s hs| =
        ‖Λ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ‖Λ‖ * ‖indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)‖ :=
      Λ.le_opNorm _
    _ = ‖Λ‖ * μ.real s := by
      rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
      simp

theorem l1DualSetValue_eq_zero_of_measure_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s : Set Ω} (hs : MeasurableSet s)
    (hμs : μ s = 0) :
    l1DualSetValue μ Λ s hs = 0 := by
  have hnorm : ‖indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)‖ = 0 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [MeasureTheory.measureReal_def, hμs]
  have hzero : indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) = 0 :=
    norm_eq_zero.mp hnorm
  simp [l1DualSetValue, hzero]

/-- Extend the measurable-set value by zero to arbitrary sets. -/
noncomputable def l1DualSetFunction (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) (s : Set Ω) : ℝ :=
  by
    classical
    by_cases hs : MeasurableSet s
    · exact l1DualSetValue μ Λ s hs
    · exact 0

theorem l1DualSetFunction_union_of_disjoint (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    l1DualSetFunction μ Λ (s ∪ t) =
      l1DualSetFunction μ Λ s + l1DualSetFunction μ Λ t := by
  simp only [l1DualSetFunction, dite_eq_left hs, dite_eq_left ht, dite_eq_left (hs.union ht)]
  exact l1DualSetValue_union_of_disjoint μ Λ hs ht hst

theorem l1DualSetFunction_eq_zero_of_not_measurable
    (μ : Measure Ω) [IsFiniteMeasure μ] (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ)
    {s : Set Ω} (hs : ¬MeasurableSet s) : l1DualSetFunction μ Λ s = 0 := by
  simp [l1DualSetFunction, hs]

theorem l1DualSetFunction_enorm_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) (s : Set Ω) :
    ‖l1DualSetFunction μ Λ s‖ₑ ≤ (ENNReal.ofReal ‖Λ‖ • μ) s := by
  classical
  by_cases hs : MeasurableSet s
  · rw [l1DualSetFunction, dite_eq_left hs, Real.enorm_eq_ofReal_abs]
    calc
      ENNReal.ofReal |l1DualSetValue μ Λ s hs| ≤
          ENNReal.ofReal (‖Λ‖ * μ.real s) :=
        ENNReal.ofReal_le_ofReal (l1DualSetValue_abs_le μ Λ hs)
      _ = (ENNReal.ofReal ‖Λ‖ • μ) s := by
        rw [ENNReal.ofReal_mul (norm_nonneg _),
          MeasureTheory.measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ s)]
        simp [Measure.smul_apply, smul_eq_mul]
  · simp [l1DualSetFunction, hs]

/-- The signed measure obtained from an `L¹` functional by the dominated-content
construction. -/
noncomputable def l1DualSignedMeasure (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) : SignedMeasure Ω := by
  let ν : Measure Ω := ENNReal.ofReal ‖Λ‖ • μ
  letI : IsFiniteMeasure ν := Measure.smul_finite μ ENNReal.ofReal_ne_top
  exact VectorMeasure.of_additive_of_le_measure
    (μ := ν) (l1DualSetFunction μ Λ)
    (l1DualSetFunction_enorm_le μ Λ)
    (by
      intro s t hs ht hst
      exact l1DualSetFunction_union_of_disjoint μ Λ hs ht hst)
    (by
      intro s hs
      exact l1DualSetFunction_eq_zero_of_not_measurable μ Λ hs)

theorem l1DualSignedMeasure_apply_measurable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s : Set Ω} (hs : MeasurableSet s) :
    l1DualSignedMeasure μ Λ s = l1DualSetValue μ Λ s hs := by
  change l1DualSetFunction μ Λ s = l1DualSetValue μ Λ s hs
  simp [l1DualSetFunction, hs]

theorem l1DualSignedMeasure_absolutelyContinuous (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    l1DualSignedMeasure μ Λ ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hμs
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hμs
  rw [l1DualSignedMeasure_apply_measurable μ Λ hs]
  exact l1DualSetValue_eq_zero_of_measure_zero μ Λ hs hμs

/-- The signed Radon--Nikodym density associated with an `L¹` functional. -/
noncomputable def l1DualDensity (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) : Ω → ℝ :=
  (l1DualSignedMeasure μ Λ).rnDeriv μ

theorem integrable_l1DualDensity (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    Integrable (l1DualDensity μ Λ) μ := by
  simpa [l1DualDensity] using
    (SignedMeasure.integrable_rnDeriv (l1DualSignedMeasure μ Λ) μ)

theorem withDensityᵥ_l1DualDensity_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    μ.withDensityᵥ (l1DualDensity μ Λ) = l1DualSignedMeasure μ Λ := by
  simpa [l1DualDensity] using
    (SignedMeasure.withDensityᵥ_rnDeriv_eq (l1DualSignedMeasure μ Λ) μ
      (l1DualSignedMeasure_absolutelyContinuous μ Λ))

theorem setIntegral_l1DualDensity_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ ω in s, l1DualDensity μ Λ ω ∂μ = l1DualSetValue μ Λ s hs := by
  rw [← withDensityᵥ_apply (integrable_l1DualDensity μ Λ) hs,
    withDensityᵥ_l1DualDensity_eq μ Λ,
    l1DualSignedMeasure_apply_measurable μ Λ hs]

theorem l1DualDensity_abs_le_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    ∀ᵐ ω ∂μ, |l1DualDensity μ Λ ω| ≤ ‖Λ‖ := by
  have hd : Integrable (l1DualDensity μ Λ) μ := integrable_l1DualDensity μ Λ
  have hc : Integrable (fun _ : Ω => ‖Λ‖) μ := integrable_const _
  have hnc : Integrable (fun _ : Ω => -‖Λ‖) μ := integrable_const _
  have hup : l1DualDensity μ Λ ≤ᵐ[μ] (fun _ : Ω => ‖Λ‖) := by
    apply ae_le_of_forall_setIntegral_le hd hc
    intro s hs hμs
    calc
      ∫ ω in s, l1DualDensity μ Λ ω ∂μ = l1DualSetValue μ Λ s hs :=
        setIntegral_l1DualDensity_eq μ Λ hs
      _ ≤ |l1DualSetValue μ Λ s hs| := le_abs_self _
      _ ≤ ‖Λ‖ * μ.real s := l1DualSetValue_abs_le μ Λ hs
      _ = ∫ _ in s, ‖Λ‖ ∂μ := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]
  have hlo : (fun _ : Ω => -‖Λ‖) ≤ᵐ[μ] l1DualDensity μ Λ := by
    apply ae_le_of_forall_setIntegral_le hnc hd
    intro s hs hμs
    calc
      ∫ _ in s, (-‖Λ‖ : ℝ) ∂μ = -(‖Λ‖ * μ.real s) := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]
      _ ≤ -|l1DualSetValue μ Λ s hs| := by
        exact neg_le_neg (l1DualSetValue_abs_le μ Λ hs)
      _ ≤ l1DualSetValue μ Λ s hs := neg_abs_le _
      _ = ∫ ω in s, l1DualDensity μ Λ ω ∂μ :=
        (setIntegral_l1DualDensity_eq μ Λ hs).symm
  filter_upwards [hup, hlo] with ω hωup hωlo
  exact abs_le.mpr ⟨hωlo, hωup⟩

theorem l1DualDensity_memLp_top (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    MemLp (l1DualDensity μ Λ) ∞ μ := by
  apply memLp_top_of_bound
    (by
      simpa [l1DualDensity] using
        (SignedMeasure.measurable_rnDeriv (l1DualSignedMeasure μ Λ) μ).aestronglyMeasurable)
    ‖Λ‖
  exact (l1DualDensity_abs_le_ae μ Λ).mono fun ω hω => by
    simpa [Real.norm_eq_abs] using hω

/-- An `L∞` representative of the signed Radon--Nikodym density. -/
noncomputable def l1DualRepresentative (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) : Linfty (Ω := Ω) μ :=
  (l1DualDensity_memLp_top μ Λ).toLp (l1DualDensity μ Λ)

theorem norm_l1DualRepresentative_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    ‖l1DualRepresentative μ Λ‖ ≤ ‖Λ‖ := by
  rw [l1DualRepresentative, Lp.norm_toLp,
    eLpNorm_exponent_top (l1DualDensity_memLp_top μ Λ).aestronglyMeasurable]
  have hbound : ∀ᵐ ω ∂μ, ‖l1DualDensity μ Λ ω‖ ≤ ‖Λ‖ :=
    (l1DualDensity_abs_le_ae μ Λ).mono fun ω hω => by
      simpa [Real.norm_eq_abs] using hω
  have hEss : eLpNormEssSup (l1DualDensity μ Λ) μ ≤ ENNReal.ofReal ‖Λ‖ :=
    eLpNormEssSup_le_of_ae_bound hbound
  calc
    (eLpNormEssSup (l1DualDensity μ Λ) μ).toReal ≤
        (ENNReal.ofReal ‖Λ‖).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hEss
    _ = ‖Λ‖ := ENNReal.toReal_ofReal (norm_nonneg _)

theorem linftyL1PairingCLM_l1DualRepresentative_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (Λ : (Lp ℝ 1 μ) →L[ℝ] ℝ) :
    linftyL1PairingCLM μ (l1DualRepresentative μ Λ) = Λ := by
  apply ContinuousLinearMap.ext
  intro f
  induction f using Lp.induction (hp_ne_top := ENNReal.one_ne_top) with
  | @indicatorConst c s hs hμs =>
    have hsc :
        ((Lp.simpleFunc.indicatorConst 1 hs hμs.ne c : Lp.simpleFunc ℝ 1 μ) :
            Lp ℝ 1 μ) =
          c • ((Lp.simpleFunc.indicatorConst 1 hs hμs.ne (1 : ℝ) :
            Lp.simpleFunc ℝ 1 μ) : Lp ℝ 1 μ) := by
      rw [Lp.simpleFunc.coe_indicatorConst, Lp.simpleFunc.coe_indicatorConst,
        indicatorConstLp, indicatorConstLp, ← MemLp.toLp_const_smul]
      apply MemLp.toLp_congr
      filter_upwards with x
      simp [Set.indicator, Pi.smul_apply]
    have hbase :
        linftyL1PairingCLM μ (l1DualRepresentative μ Λ)
            (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) =
          Λ (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) := by
      change linftyL1Pairing μ (l1DualRepresentative μ Λ)
          (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) = _
      rw [linftyL1Pairing_eq_integral]
      calc
        (∫ ω, (l1DualRepresentative μ Λ) ω *
            indicatorConstLp 1 hs hμs.ne (1 : ℝ) ω ∂μ) =
            ∫ ω in s, (l1DualRepresentative μ Λ) ω ∂μ := by
          rw [← integral_indicator hs]
          apply integral_congr_ae
          filter_upwards [indicatorConstLp_coeFn (p := (1 : ℝ≥0∞))
            (μ := μ) (s := s) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))] with x hx
          by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs, hx]
        _ = ∫ ω in s, l1DualDensity μ Λ ω ∂μ := by
          apply setIntegral_congr_ae hs
          filter_upwards [(l1DualDensity_memLp_top μ Λ).coeFn_toLp] with x hx hxs
          exact hx
        _ = l1DualSetValue μ Λ s hs := setIntegral_l1DualDensity_eq μ Λ hs
        _ = Λ (indicatorConstLp 1 hs hμs.ne (1 : ℝ)) := by
          rfl
    rw [hsc, (linftyL1PairingCLM μ (l1DualRepresentative μ Λ)).map_smul,
      Λ.map_smul]
    simp only [Lp.simpleFunc.coe_indicatorConst]
    rw [hbase]
  | @add f g hf hg hdisj hf_eq hg_eq =>
    rw [(linftyL1PairingCLM μ (l1DualRepresentative μ Λ)).map_add, Λ.map_add]
    exact congrArg₂ (· + ·) hf_eq hg_eq
  | isClosed =>
    exact isClosed_eq (linftyL1PairingCLM μ (l1DualRepresentative μ Λ)).continuous
      Λ.continuous

theorem linftyL1PairingCLM_surjective (μ : Measure Ω) [IsFiniteMeasure μ] :
    Function.Surjective (linftyL1PairingCLM μ) := by
  intro Λ
  exact ⟨l1DualRepresentative μ Λ,
    linftyL1PairingCLM_l1DualRepresentative_eq μ Λ⟩

theorem norm_linftyL1PairingCLM_apply_apply_le
    (μ : Measure Ω)
    (F : Linfty (Ω := Ω) μ) (q : Lp ℝ 1 μ) :
    ‖linftyL1PairingCLM μ F q‖ ≤ ‖F‖ * ‖q‖ := by
  calc
    ‖linftyL1PairingCLM μ F q‖ =
        ‖L1.integralCLM' ℝ
          ((ContinuousLinearMap.lsmul ℝ ℝ).holder 1 F q)‖ := rfl
    _ ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ).holder 1 F q‖ :=
      by
        rw [← L1.integral_eq']
        exact L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.lsmul ℝ ℝ‖ * ‖F‖ * ‖q‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ = ‖F‖ * ‖q‖ := by simp

theorem norm_linftyL1PairingCLM_apply_le
    (μ : Measure Ω) (F : Linfty (Ω := Ω) μ) :
    ‖linftyL1PairingCLM μ F‖ ≤ ‖F‖ :=
  (linftyL1PairingCLM μ F).opNorm_le_bound (norm_nonneg F)
    (norm_linftyL1PairingCLM_apply_apply_le μ F)

theorem l1DualRepresentative_linftyL1PairingCLM
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Linfty (Ω := Ω) μ) :
    l1DualRepresentative μ (linftyL1PairingCLM μ F) = F := by
  apply linftyL1Pairing_injective μ
  change
    (linftyL1PairingCLM μ
      (l1DualRepresentative μ (linftyL1PairingCLM μ F))).toLinearMap =
      (linftyL1PairingCLM μ F).toLinearMap
  exact congrArg ContinuousLinearMap.toLinearMap
    (linftyL1PairingCLM_l1DualRepresentative_eq μ
      (linftyL1PairingCLM μ F))

theorem norm_linftyL1PairingCLM_apply
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Linfty (Ω := Ω) μ) :
    ‖linftyL1PairingCLM μ F‖ = ‖F‖ := by
  apply le_antisymm (norm_linftyL1PairingCLM_apply_le μ F)
  calc
    ‖F‖ = ‖l1DualRepresentative μ (linftyL1PairingCLM μ F)‖ := by
      rw [l1DualRepresentative_linftyL1PairingCLM μ F]
    _ ≤ ‖linftyL1PairingCLM μ F‖ :=
      norm_l1DualRepresentative_le μ (linftyL1PairingCLM μ F)

/-- The integral pairing identifies `L∞` isometrically with the norm dual of `L¹`. -/
noncomputable def linftyL1PairingLinearIsometry
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Linfty (Ω := Ω) μ →ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ) where
  __ := (linftyL1PairingCLM μ).toLinearMap
  norm_map' := norm_linftyL1PairingCLM_apply μ

/-- The isometric duality equivalence `L∞ ≃ₗᵢ (L¹)*` induced by integration. -/
noncomputable def linftyL1DualLinearIsometryEquiv
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Linfty (Ω := Ω) μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ) :=
  LinearIsometryEquiv.ofSurjective
    (linftyL1PairingLinearIsometry μ)
    (linftyL1PairingCLM_surjective μ)

/-- The linear equivalence underlying the identification of the concrete
`σ(L∞, L¹)` topology with the weak-star topology on `(L¹)*`. -/
noncomputable def linftyWeakStarWeakDualLinearEquiv
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    LinftyWeakStar μ ≃ₗ[ℝ] WeakDual ℝ (Lp ℝ 1 μ) :=
  (toLinftyWeakStar μ).symm.trans
    ((linftyL1DualLinearIsometryEquiv μ).toLinearEquiv.trans
      StrongDual.toWeakDual)

/-- The concrete weak-star copy of `L∞` is linearly homeomorphic to the
standard weak dual of `L¹`. -/
noncomputable def linftyWeakStarEquivWeakDual
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    LinftyWeakStar μ ≃L[ℝ] WeakDual ℝ (Lp ℝ 1 μ) where
  __ := linftyWeakStarWeakDualLinearEquiv μ
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro q
    change Continuous fun F : LinftyWeakStar μ =>
      linftyL1Pairing μ F q
    exact linftyWeakStar_eval_continuous μ q
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro q
    have heq :
        (fun Λ : WeakDual ℝ (Lp ℝ 1 μ) =>
          linftyL1Pairing μ
            ((linftyWeakStarWeakDualLinearEquiv μ).symm Λ) q) =
        fun Λ : WeakDual ℝ (Lp ℝ 1 μ) => Λ q := by
      funext Λ
      exact congrArg (fun Φ : WeakDual ℝ (Lp ℝ 1 μ) => Φ q)
        ((linftyWeakStarWeakDualLinearEquiv μ).apply_symm_apply Λ)
    change Continuous (fun Λ : WeakDual ℝ (Lp ℝ 1 μ) =>
      linftyL1Pairing μ
        ((linftyWeakStarWeakDualLinearEquiv μ).symm Λ) q)
    exact heq ▸ WeakDual.eval_continuous q

end FTAPTheorem42
