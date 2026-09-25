/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.PositiveTail.Komlos
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform integrability under forward convexification

Finite tail convex combinations preserve uniform integrability.  In the
`L^1` case their common norm bound also gives boundedness in probability.
Combining these two facts with the existing nonnegative Komlós extraction
upgrades the selected almost-everywhere limit to an `L^1` limit.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace ForwardConvexWeights

/-- Forward convex combinations preserve uniform integrability. -/
theorem uniformIntegrable_apply
    {mu : Measure Omega} {p : ENNReal} {f : Nat -> Omega -> Real}
    (W : ForwardConvexWeights) (hp : 1 <= p)
    (hf : UniformIntegrable f p mu) :
    UniformIntegrable (W.apply f) p mu := by
  obtain ⟨hfUniform, C, hC⟩ := hf
  have hApply (n : Nat) : W.apply f n =
      ∑ i ∈ W.support n, W.weight n i • f i := by
    funext omega
    simp only [ForwardConvexWeights.apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  refine ⟨unifIntegrable_iff.2 ?_, ⟨C, ?_⟩⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdeltaPositive, hdelta⟩ := unifIntegrable_iff.1 hfUniform epsilon hepsilon
    refine ⟨delta, hdeltaPositive, fun n s hmus => ?_⟩
    rw [hApply]
    refine (eLpNorm_sum_le hp).trans ?_
    simp_rw [eLpNorm_const_smul]
    calc
      (∑ i ∈ W.support n,
          ‖W.weight n i‖ₑ * eLpNorm (f i) p (mu.restrict s)) <=
          ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * epsilon := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.enorm_eq_ofReal (W.nonneg n i hi)]
        gcongr
        exact hdelta i s hmus
      _ = epsilon := by
        rw [← Finset.sum_mul]
        have hweights :
            ∑ i ∈ W.support n, ENNReal.ofReal (W.weight n i) = 1 := by
          rw [← ENNReal.ofReal_sum_of_nonneg (W.nonneg n),
            W.sum_eq_one, ENNReal.ofReal_one]
        rw [hweights, one_mul]
  · intro n
    rw [hApply]
    refine (eLpNorm_sum_le hp).trans ?_
    simp_rw [eLpNorm_const_smul]
    calc
      (∑ i ∈ W.support n, ‖W.weight n i‖ₑ * eLpNorm (f i) p mu) <=
          ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.enorm_eq_ofReal (W.nonneg n i hi)]
        gcongr
        exact hC i
      _ = C := by
        rw [← Finset.sum_mul]
        have hweights :
            ∑ i ∈ W.support n, ENNReal.ofReal (W.weight n i) = 1 := by
          rw [← ENNReal.ofReal_sum_of_nonneg (W.nonneg n),
            W.sum_eq_one, ENNReal.ofReal_one]
        rw [hweights, one_mul]

/-- Forward convexification preserves a common integral. -/
theorem integral_apply_eq_of_integral_eq
    {mu : Measure Omega} {f : Nat -> Omega -> Real}
    (W : ForwardConvexWeights) (hf : forall n, Integrable (f n) mu)
    {c : Real} (hIntegral : forall n, (∫ omega, f n omega ∂mu) = c)
    (n : Nat) :
    (∫ omega, W.apply f n omega ∂mu) = c := by
  unfold ForwardConvexWeights.apply
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hIntegral]
    rw [← Finset.sum_mul, W.sum_eq_one, one_mul]
  · intro i _hi
    exact (hf i).const_mul (W.weight n i)

/-- The elementary numerical estimate behind the uniform `L^1` Markov
bound. -/
theorem uniformL1_tail_numeric (C : NNReal) {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    (ENNReal.ofReal (((C : Real) + 1) / epsilon))⁻¹ * (C : ENNReal) <=
      ENNReal.ofReal epsilon := by
  have hCnonneg : (0 : Real) <= C := C.coe_nonneg
  have hCpos : 0 < (C : Real) + 1 := by positivity
  have hRpos : 0 < ((C : Real) + 1) / epsilon :=
    div_pos hCpos hepsilon
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hRpos.le, ENNReal.toReal_ofReal hepsilon.le]
  simp only [ENNReal.coe_toReal]
  rw [inv_div]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hCpos).2 (by
    calc
      epsilon * (C : Real) <= epsilon * ((C : Real) + 1) := by
        gcongr
        linarith
      _ = epsilon * ((C : Real) + 1) := rfl)

/-- A uniformly `L^1`-bounded family is bounded in probability. -/
theorem _root_.MeasureTheory.UniformIntegrable.boundedInProbability_one
    {mu : Measure Omega} {f : Nat -> Omega -> Real}
    (hf : UniformIntegrable f 1 mu) :
    BoundedInProbability mu f := by
  obtain ⟨C, hC⟩ := hf.2
  intro epsilon hepsilon
  let R : Real := ((C : Real) + 1) / epsilon
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hRpos.le, fun n => ?_⟩
  have hsubset : {omega | R < |f n omega|} ⊆
      {omega | ENNReal.ofReal R <= ‖f n omega‖ₑ} := by
    intro omega homega
    change R < |f n omega| at homega
    change ENNReal.ofReal R <= ‖f n omega‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal homega.le
  calc
    mu {omega | R < |f n omega|} <=
        mu {omega | ENNReal.ofReal R <= ‖f n omega‖ₑ} :=
      measure_mono hsubset
    _ <= (ENNReal.ofReal R)⁻¹ ^ (1 : ENNReal).toReal *
        eLpNorm (f n) 1 mu ^ (1 : ENNReal).toReal := by
      apply meas_ge_le_mul_pow_eLpNorm_enorm mu
        (p := (1 : ENNReal)) (by norm_num) (by norm_num)
      · exact ENNReal.ofReal_ne_zero_iff.mpr hRpos
      · simp
    _ <= (ENNReal.ofReal R)⁻¹ * (C : ENNReal) := by
      norm_num
      gcongr
      exact hC n
    _ <= ENNReal.ofReal epsilon := by
      simpa only [R] using uniformL1_tail_numeric C hepsilon

end ForwardConvexWeights

/-- A nonnegative uniformly integrable sequence admits forward convex
combinations converging both almost everywhere and in `L¹`. -/
theorem exists_forwardConvexWeights_tendstoAE_L1_of_uniformIntegrable_nonneg
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {f : Nat -> Omega -> Real}
    (hfMeas : ∀ n, StronglyMeasurable (f n))
    (hfNonneg : ∀ n, ∀ᵐ omega ∂mu, 0 <= f n omega)
    (hfUI : UniformIntegrable f 1 mu) :
    exists W : ForwardConvexWeights, exists g : Omega -> Real,
      TendstoAE mu (W.apply f) g /\
      MemLp g 1 mu /\
      (∀ᵐ omega ∂mu, 0 <= g omega) /\
      Tendsto (fun n => eLpNorm (W.apply f n - g) 1 mu)
        atTop (nhds 0) := by
  let eta : Nat -> Real := nearError 1
  have hetaPos : ∀ n, 0 < eta n := by
    intro n
    simpa [eta] using nearError_pos (a := (1 : Real)) (by norm_num) n
  have hetaNonneg : ∀ n, 0 <= eta n :=
    fun n => (hetaPos n).le
  have hetaTendsto : Tendsto eta atTop (nhds 0) := by
    simpa [eta] using tendsto_nearError_zero (a := (1 : Real)) (by norm_num)
  obtain ⟨w, hwNear⟩ :=
    exists_near_expTailUtilitySup_weights
      (μ := mu) (x := f) (η := eta) hetaPos
  have hSelectedUI :
      UniformIntegrable (fun n => (w n).apply f) 1 mu := by
    simpa only [TailConvexWeights.toForward_apply] using
      (TailConvexWeights.toForward w).uniformIntegrable_apply
        (by norm_num) hfUI
  have hSelectedBounded :
      BoundedInProbability mu (fun n => (w n).apply f) :=
    hSelectedUI.boundedInProbability_one
  obtain ⟨W, g, hTendstoAE⟩ :=
    hasForwardConvexAELimit_of_nearExpSup_of_boundedInProbability
      (μ := mu) (x := f) (η := eta)
      hfMeas hfNonneg hetaNonneg hetaTendsto w hwNear hSelectedBounded
  have hWUI : UniformIntegrable (W.apply f) 1 mu :=
    W.uniformIntegrable_apply (by norm_num) hfUI
  have hgMemLp : MemLp g 1 mu :=
    hWUI.memLp_of_ae_tendsto hTendstoAE
  have hgNonneg : ∀ᵐ omega ∂mu, 0 <= g omega := by
    have hAllNonneg : ∀ᵐ omega ∂mu,
        ∀ n, 0 <= W.apply f n omega :=
      ae_all_iff.mpr (W.apply_ae_nonneg hfNonneg)
    filter_upwards [hTendstoAE, hAllNonneg] with omega hTendsto hNonneg
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hTendsto
      (Filter.Eventually.of_forall hNonneg)
  refine ⟨W, g, hTendstoAE, hgMemLp, hgNonneg, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num) ENNReal.one_ne_top hWUI.aestronglyMeasurable hgMemLp
      hWUI.unifIntegrable hTendstoAE

end FTAPTheorem42
