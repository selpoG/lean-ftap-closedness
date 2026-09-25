/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.Closedness
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# The concrete `σ(L∞, L¹)` pairing

This module records the actual weak-star topology used by the
Delbaen--Schachermayer statement.  It is deliberately separate from
`WeakSpace ℝ (Lp ℝ ⊤ μ)`, whose dual family is the full continuous dual of
`L∞` and therefore gives the ordinary weak topology instead.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## The `L∞`--`L¹` integral pairing
-/

/-- The continuous bilinear map `(f, g) ↦ ∫ f g dμ` on `L∞ × L¹`. -/
noncomputable def linftyL1PairingCLM (μ : Measure Ω) :
    Linfty (Ω := Ω) μ →L[ℝ] (Lp ℝ 1 μ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ ⊤ 1

/-- The linear-map form of `linftyL1PairingCLM`, suitable for `WeakBilin`. -/
noncomputable def linftyL1Pairing (μ : Measure Ω) :
    Linfty (Ω := Ω) μ →ₗ[ℝ] (Lp ℝ 1 μ) →ₗ[ℝ] ℝ :=
  { toFun := fun f => (linftyL1PairingCLM μ f).toLinearMap
    map_add' := by
      intro f g
      ext h
      exact congrArg (fun q : (Lp ℝ 1 μ) →L[ℝ] ℝ => q h)
        ((linftyL1PairingCLM μ).map_add f g)
    map_smul' := by
      intro c f
      ext h
      exact congrArg (fun q : (Lp ℝ 1 μ) →L[ℝ] ℝ => q h)
        ((linftyL1PairingCLM μ).map_smul c f) }

@[simp]
theorem linftyL1Pairing_apply (μ : Measure Ω)
    (f : Linfty (Ω := Ω) μ) (g : Lp ℝ 1 μ) :
    linftyL1Pairing μ f g = linftyL1PairingCLM μ f g :=
  by rfl

theorem linftyL1Pairing_eq_integral (μ : Measure Ω)
    (f : Linfty (Ω := Ω) μ) (g : Lp ℝ 1 μ) :
    linftyL1Pairing μ f g = ∫ ω, f ω * g ω ∂μ := by
  change linftyL1PairingCLM μ f g = _
  simpa [linftyL1PairingCLM] using
    (ContinuousLinearMap.lpPairing_eq_integral
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (μ := μ) (p := ⊤) (q := 1) f g)

theorem linftyL1Pairing_injective (μ : Measure Ω) [IsFiniteMeasure μ] :
    Function.Injective (linftyL1Pairing μ) := by
  intro f g hfg
  let d : Ω → ℝ := fun ω => (f - g) ω
  have hdTop : MemLp d ⊤ μ := by
    simpa [d] using (Lp.memLp (f - g))
  have hdOne : MemLp d 1 μ :=
    hdTop.mono_exponent (by simp)
  let v : Lp ℝ 1 μ := hdOne.toLp d
  have hEval : linftyL1Pairing μ f v = linftyL1Pairing μ g v :=
    congrArg (fun q : (Lp ℝ 1 μ) →ₗ[ℝ] ℝ => q v) hfg
  have hPairZero : linftyL1Pairing μ (f - g) v = 0 := by
    simpa only [map_sub, LinearMap.sub_apply] using sub_eq_zero.mpr hEval
  have hv : (v : Ω → ℝ) =ᵐ[μ] d :=
    MemLp.coeFn_toLp _
  have hIntegralSquare : ∫ ω, d ω * d ω ∂μ = 0 := by
    calc
      ∫ ω, d ω * d ω ∂μ = ∫ ω, d ω * v ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hv] with ω hω
        rw [hω]
      _ = linftyL1Pairing μ (f - g) v := by
        symm
        simpa [d] using linftyL1Pairing_eq_integral μ (f - g) v
      _ = 0 := hPairZero
  have hIntegrableSquare : Integrable (fun ω => d ω * d ω) μ :=
    hdOne.integrable_mul hdTop
  have hSquareAE : (fun ω => d ω * d ω) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg (d ω))
      hIntegrableSquare).mp hIntegralSquare
  have hdAE : d =ᵐ[μ] 0 := by
    filter_upwards [hSquareAE] with ω hω
    exact mul_self_eq_zero.mp hω
  have hsub : f - g = (0 : Linfty (Ω := Ω) μ) := by
    apply Lp.ext
    filter_upwards [hdAE, MeasureTheory.Lp.coeFn_zero ℝ ⊤ μ] with ω hω hzero
    have hω' : (f - g : Linfty (Ω := Ω) μ) ω = 0 := by
      simpa [d] using hω
    calc
      (f - g : Linfty (Ω := Ω) μ) ω = 0 := hω'
      _ = (0 : Linfty (Ω := Ω) μ) ω := hzero.symm
  exact sub_eq_zero.mp hsub

/-!
## The induced weak-star topological type
-/

/-- `L∞` equipped with the topology of convergence against every `L¹` claim. -/
abbrev LinftyWeakStar (μ : Measure Ω) : Type _ :=
  WeakBilin (linftyL1Pairing μ)

/-- The identity linear equivalence from the normed `L∞` model to its weak-star copy. -/
def toLinftyWeakStar (μ : Measure Ω) :
    Linfty (Ω := Ω) μ ≃ₗ[ℝ] LinftyWeakStar μ :=
  LinearEquiv.refl ℝ _

theorem linftyWeakStar_eval_continuous (μ : Measure Ω) (g : Lp ℝ 1 μ) :
    Continuous fun f : LinftyWeakStar μ => linftyL1Pairing μ f g :=
  WeakBilin.eval_continuous (linftyL1Pairing μ) g

/-- A set of bounded claims is weak-star closed when its image in the concrete
`WeakBilin` copy is closed. -/
def LinftyWeakStarClosed (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  IsClosed ((toLinftyWeakStar μ) '' LinftyClaims μ D : Set (LinftyWeakStar μ))

/-- The explicit functional-analytic input needed for the concrete
`σ(L∞, L¹)` closedness theorem.  This is intentionally kept as a criterion:
the Fatou/solid/cone-to-weak-star theorem itself is not supplied by the
current mathlib API. -/
def LinftyWeakStarClosedFromFatouCone
    (μ : Measure Ω) (D : Set (Ω → ℝ)) : Prop :=
  FatouClosed μ D → ClaimCone D → Solid μ D → LinftyWeakStarClosed μ D

theorem linftyWeakStarClosed_of_fatouCone_criterion
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hCriterion : LinftyWeakStarClosedFromFatouCone μ D)
    (hFatou : FatouClosed μ D)
    (hCone : ClaimCone D)
    (hSolid : Solid μ D) :
    LinftyWeakStarClosed μ D :=
  hCriterion hFatou hCone hSolid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Bounded representatives of concrete `L∞` claims

This section selects uniformly bounded strongly measurable representatives without
using any compactness or forward-convex extraction theorem.
-/

open Filter MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Uniformly norm-bounded `L∞` claims admit strongly measurable representatives
in the underlying raw claim set, with the same common a.e. absolute bound.
-/
theorem exists_bounded_stronglyMeasurable_representatives
    {μ : Measure Ω} {D : Set (Ω → ℝ)}
    (hD_aeSat : AESaturated μ D)
    {u : ℕ → Linfty (Ω := Ω) μ} {C : ℝ}
    (hu : ∀ n, u n ∈ LinftyClaims μ D)
    (hu_norm : ∀ n, ‖u n‖ ≤ C) :
    ∃ f : ℕ → Ω → ℝ,
      (∀ n, f n ∈ D) ∧
      (∀ n, StronglyMeasurable (f n)) ∧
      (∀ n, ∀ᵐ ω ∂μ, |f n ω| ≤ C) ∧
      ∃ hfLp : ∀ n, MemLp (f n) ∞ μ,
        ∀ n, (hfLp n).toLp (f n) = u n := by
  choose f₀ hf₀D hf₀Lp hf₀eq using hu
  let f : ℕ → Ω → ℝ :=
    fun n => (hf₀Lp n).aestronglyMeasurable.mk (f₀ n)
  have hf₀_eq_f : ∀ n, f₀ n =ᵐ[μ] f n := by
    intro n
    dsimp [f]
    exact (hf₀Lp n).aestronglyMeasurable.ae_eq_mk
  have hfD : ∀ n, f n ∈ D := by
    intro n
    exact hD_aeSat (hf₀D n) (hf₀_eq_f n)
  have hfStrong : ∀ n, StronglyMeasurable (f n) := by
    intro n
    dsimp [f]
    exact (hf₀Lp n).aestronglyMeasurable.stronglyMeasurable_mk
  have hf₀_abs : ∀ n, ∀ᵐ ω ∂μ, |f₀ n ω| ≤ C := by
    intro n
    have hn : (eLpNormEssSup (f₀ n) μ).toReal ≤ C := by
      have hnorm := hu_norm n
      rw [← hf₀eq n, MeasureTheory.Lp.norm_toLp,
        eLpNorm_exponent_top (hf₀Lp n).aestronglyMeasurable] at hnorm
      exact hnorm
    have hne : eLpNormEssSup (f₀ n) μ ≠ ⊤ := by
      rw [← eLpNorm_exponent_top (hf₀Lp n).aestronglyMeasurable]
      exact (hf₀Lp n).eLpNorm_ne_top
    filter_upwards [ae_le_eLpNormEssSup (f := f₀ n)] with ω hω
    have hω' := ENNReal.toReal_mono hne hω
    have hω'' : ‖f₀ n ω‖ ≤ (eLpNormEssSup (f₀ n) μ).toReal := by
      simpa using hω'
    simpa [Real.norm_eq_abs] using hω''.trans hn
  have hf_abs : ∀ n, ∀ᵐ ω ∂μ, |f n ω| ≤ C := by
    intro n
    filter_upwards [hf₀_abs n, hf₀_eq_f n] with ω hω hEq
    rw [← hEq]
    exact hω
  have hfLp : ∀ n, MemLp (f n) ∞ μ := by
    intro n
    exact (hf₀Lp n).ae_eq (hf₀_eq_f n)
  have hfEq : ∀ n, (hfLp n).toLp (f n) = u n := by
    intro n
    exact (MemLp.toLp_congr (hfLp n) (hf₀Lp n) (hf₀_eq_f n).symm).trans (hf₀eq n)
  exact ⟨f, hfD, hfStrong, hf_abs, hfLp, hfEq⟩

end FTAPTheorem42
