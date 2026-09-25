/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.Scalar
import FTAPTheorem42.Stochastic.Topology.R1.Complete
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Sequences

/-! # Scalar continuity from a fixed finite-cost decomposition -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω} [IsProbabilityMeasure mu]

theorem J1Decomposition.tendsto_smul_capped_clock (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu)
    {a : Nat → Real} (ha : Tendsto a atTop (𝓝 0)) (T : NNReal) :
    Tendsto (fun k => ∫⁻ w,
      min ((D.smul (a k)).clock (Q.smul D.leftN (a k)) T w) 1 ∂mu) atTop (𝓝 0) := by
  have haE : Tendsto (fun k => ENNReal.ofReal |a k|) atTop (𝓝 0) := by
    simpa only [abs_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ha.abs
  have hPoint : ∀ᵐ w ∂mu, Tendsto
      (fun k => min (ENNReal.ofReal |a k| * D.clock Q T w) 1) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro w
    have hm := ENNReal.Tendsto.mul_const haE (Or.inr (D.clock_ne_top Q T w))
    simpa only [zero_mul, min_eq_left (show (0 : ENNReal) ≤ 1 from bot_le)] using
      hm.min (tendsto_const_nhds (x := (1 : ENNReal)))
  have hInt := tendsto_lintegral_of_dominated_convergence' (fun _ : Ω => (1 : ENNReal))
    (fun k => ((measurable_const.mul (D.clock_measurable Q T)).min
      measurable_const).aemeasurable)
    (fun _ => Eventually.of_forall (fun _ => min_le_right _ _))
    (by simp : (∫⁻ _ : Ω, (1 : ENNReal) ∂mu) ≠ ∞) hPoint
  simp only [lintegral_zero] at hInt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hInt (fun _ => bot_le)
  intro k
  exact lintegral_mono (fun w => min_le_min (D.smul_clock_le Q (a k) T w) le_rfl)

theorem J1Decomposition.tendsto_smul_r1Cost (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu)
    (hJump : boundedStoppingJumpCost D.N F mu ≠ ∞)
    {a : Nat → Real} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => (D.smul (a k)).r1Cost (Q.smul D.leftN (a k))) atTop (𝓝 0) := by
  apply J1Decomposition.tendsto_r1Cost_of_coordinates
  · have haE : Tendsto (fun k => ENNReal.ofReal |a k|) atTop (𝓝 0) := by
      simpa only [abs_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ha.abs
    simpa only [J1Decomposition.smul, boundedStoppingJumpCost_smul D.leftN, zero_mul] using
      ENNReal.Tendsto.mul_const haE (Or.inr hJump)
  · intro T
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (D.tendsto_smul_capped_clock Q ha T) (fun _ => bot_le)
    intro k
    exact lintegral_mono (fun _ => min_le_min (le_add_right le_rfl) le_rfl)
  · intro T
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (D.tendsto_smul_capped_clock Q ha T) (fun _ => bot_le)
    intro k
    exact lintegral_mono (fun _ => min_le_min (le_add_left le_rfl) le_rfl)

/-- Scalar continuity uses a new finite-jump-cost decomposition of the fixed
target. The bound by `max 1 |a|` alone cannot prove this limit. -/
theorem tendsto_semimartingaleR1_smul_zero [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (D : J1Decomposition X F mu) {a : Nat → Real} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => semimartingaleR1 (a k • X) F mu) atTop (𝓝 0) := by
  obtain ⟨E, Q, hCost⟩ := D.exists_bounded_r1Cost hUsual
  have hJump : boundedStoppingJumpCost E.N F mu ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num : (3 : ENNReal) ≠ ∞)
      ((le_add_right le_rfl).trans hCost)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (E.tendsto_smul_r1Cost Q hJump ha) (fun _ => bot_le)
  intro k
  exact iInf_le_of_le (E.smul (a k)) (iInf_le _ (Q.smul E.leftN (a k)))

/-- Joint sequential continuity on the decomposable process space. -/
theorem tendsto_semimartingaleR1_smul [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F) (D : J1Decomposition X F mu)
    {Z : Nat → Process Ω} {a : Nat → Real} {c : Real}
    (ha : Tendsto a atTop (𝓝 c))
    (hZ : Tendsto (fun k => semimartingaleR1 (Z k - X) F mu) atTop (𝓝 0)) :
    Tendsto (fun k => semimartingaleR1 (a k • Z k - c • X) F mu) atTop (𝓝 0) := by
  have hFactor : Tendsto (fun k => ENNReal.ofReal (max 1 |a k|)) atTop
      (𝓝 (ENNReal.ofReal (max 1 |c|))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.max ha.abs)
  have hProduct := ENNReal.Tendsto.mul hFactor (Or.inr ENNReal.zero_ne_top)
    hZ (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hProduct
  have hDifference : Tendsto (fun k => a k - c) atTop (𝓝 0) := by
    simpa only [sub_self] using ha.sub (tendsto_const_nhds (x := c))
  have hUpper := hProduct.add (tendsto_semimartingaleR1_smul_zero hUsual D hDifference)
  simp only [zero_add] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _ => bot_le)
  intro k
  dsimp only
  have hEq : a k • Z k - c • X = a k • (Z k - X) + (a k - c) • X := by
    module
  rw [hEq]
  exact (semimartingaleR1_add_le hUsual).trans
    (add_le_add (semimartingaleR1_smul_le (a k)) le_rfl)

end FTAPTheorem42

namespace FTAPTheorem42.R1Process

/-! ## Continuous scalar multiplication on the r1 separation quotient -/

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

instance : SMul Real (R1Process F mu) where
  smul c X := ⟨c • X.val, X.property.map (fun D => D.smul c)⟩

@[simp]
theorem smul_val (c : Real) (X : R1Process F mu) : (c • X).val = c • X.val := rfl

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [hUsual : Fact (Filtration.UsualConditions mu F)]

instance : ContinuousSMul Real (R1Process F mu) where
  continuous_smul := by
    apply continuous_iff_seqContinuous.mpr
    intro u p hu
    rw [tendsto_iff_edist_tendsto_0]
    simp only [edist_eq, smul_val]
    obtain ⟨D⟩ := p.2.property
    apply tendsto_semimartingaleR1_smul hUsual.out D ((continuous_fst.tendsto p).comp hu)
    have h := (continuous_snd.tendsto p).comp hu
    rw [tendsto_iff_edist_tendsto_0] at h
    exact h

end FTAPTheorem42.R1Process
