/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.ElementaryMetric
import Mathlib.Analysis.Normed.Group.Tannery
import FTAPTheorem42.Stochastic.Topology.R1.VectorTopology

/-! # Completeness of the elementary metric, independently of the R1 topology -/

namespace FTAPTheorem42.ElementaryMetricProcess

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

theorem gauge_cauchy_of_cauchySeq (X : Nat → ElementaryMetricProcess F μ)
    (hX : CauchySeq X) :
    ∀ T : NNReal, ∀ ε > (0 : Real), ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      R1Process.elementaryGauge T (X m) (X n) ≤ ENNReal.ofReal ε := by
  intro T ε hε
  let k := Nat.ceil T
  let w : ENNReal := (2⁻¹) ^ (k + 1)
  have hw : w ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hX (w * ENNReal.ofReal ε)
    (pos_iff_ne_zero.mpr (mul_ne_zero hw (ne_of_gt (ENNReal.ofReal_pos.mpr hε))))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hT : T ≤ (k : NNReal) + 1 :=
    (Nat.le_ceil T).trans (by simp [k])
  have hTerm : w * R1Process.elementaryGauge T (X m) (X n) ≤ edist (X m) (X n) := by
    exact (mul_le_mul' le_rfl (R1Process.elementaryGauge_mono hT _ _)).trans
      (ENNReal.le_tsum (f := fun k : Nat => (2 : ENNReal)⁻¹ ^ (k + 1) *
        R1Process.elementaryGauge (k + 1) (X m) (X n)) k)
  by_contra h
  have hLower := mul_le_mul' (le_rfl : w ≤ w) (le_of_not_ge h)
  exact (not_le_of_gt (hN m hm n hn)) (hLower.trans hTerm)

theorem tendsto_of_gauge (X : Nat → ElementaryMetricProcess F μ)
    (Y : ElementaryMetricProcess F μ)
    (hX : ∀ T : NNReal, ∀ ε > (0 : Real), ∀ᶠ n in atTop,
      R1Process.elementaryGauge T (X n) Y ≤ ENNReal.ofReal ε) :
    Tendsto X atTop (𝓝 Y) := by
  have hGauge (T : NNReal) : Tendsto
      (fun n => (R1Process.elementaryGauge T (X n) Y).toReal) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun _ => ha.trans_le ENNReal.toReal_nonneg
    · intro b hb
      filter_upwards [hX T (b / 2) (by positivity)] with n hn
      exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hn).trans_lt (by linarith)
  have hSum : Summable (fun k : Nat => ((2 : Real)⁻¹) ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_two.mul_left ((2 : Real)⁻¹))
  have hLimit := tendsto_tsum_of_dominated_convergence hSum
    (f := fun (n k : Nat) => ((2 : Real)⁻¹) ^ (k + 1) *
      (R1Process.elementaryGauge (k + 1) (X n) Y).toReal)
    (g := fun _ => 0)
    (fun k => by simpa using (hGauge (k + 1)).const_mul (((2 : Real)⁻¹) ^ (k + 1)))
    (Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity)
        (ENNReal.toReal_le_of_le_ofReal zero_le_one
          (by simpa using R1Process.elementaryGauge_le_one (k + 1) (X n) Y)))
  apply tendsto_iff_dist_tendsto_zero.mpr
  convert hLimit using 1
  · ext n
    change (∑' k : Nat, ((2 : ENNReal)⁻¹) ^ (k + 1) *
      R1Process.elementaryGauge (k + 1) (X n) Y).toReal = _
    rw [ENNReal.tsum_toReal_eq]
    · simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_ofNat]
    · intro k
      exact ne_top_of_le_ne_top (by finiteness)
        ((ENNReal.le_tsum (f := fun k : Nat => (2 : ENNReal)⁻¹ ^ (k + 1) *
          R1Process.elementaryGauge (k + 1) (X n) Y) k).trans
            (R1Process.elementaryEDist_le_one (X n) Y))
  · simp

instance : CompleteSpace (ElementaryMetricProcess F μ) :=
  EMetric.complete_of_cauchySeq_tendsto fun X hX => by
    obtain ⟨Y, hY⟩ := R1Process.exists_elementaryGauge_limit X (gauge_cauchy_of_cauchySeq X hX)
    exact ⟨Y, tendsto_of_gauge X Y hY⟩

end FTAPTheorem42.ElementaryMetricProcess

namespace FTAPTheorem42

/-! ## The elementary metric as a complete uniform additive group -/

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [Fact (Filtration.UsualConditions μ F)]

namespace R1Process

theorem elementaryGauge_add_right (T : NNReal)
    (X Y Z : SeparationQuotient (R1Process F μ)) :
    elementaryGauge T (X + Z) (Y + Z) = elementaryGauge T X Y := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨Z, rfl⟩ := SeparationQuotient.surjective_mk Z
  rw [← SeparationQuotient.mk_add, ← SeparationQuotient.mk_add]
  simp only [elementaryGauge_mk]
  apply iSup_congr
  intro J
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    unfold elementaryEmeryTestError
    congr 1
    funext t w
    change ElementaryStrategy.gain (fun t w => X.val t w + Z.val t w) _ t w -
      ElementaryStrategy.gain (fun t w => Y.val t w + Z.val t w) _ t w = _
    rw [ElementaryStrategy.gain_add_price, ElementaryStrategy.gain_add_price]
    abel

theorem elementaryEDist_add_right (X Y Z : SeparationQuotient (R1Process F μ)) :
    elementaryEDist (X + Z) (Y + Z) = elementaryEDist X Y := by
  simp only [elementaryEDist, elementaryGauge_add_right]

end R1Process

namespace ElementaryMetricProcess

noncomputable instance : AddCommGroup (ElementaryMetricProcess F μ) :=
  inferInstanceAs (AddCommGroup (SeparationQuotient (R1Process F μ)))

noncomputable instance : Module Real (ElementaryMetricProcess F μ) :=
  inferInstanceAs (Module Real (SeparationQuotient (R1Process F μ)))

theorem edist_add_right (X Y Z : ElementaryMetricProcess F μ) :
    edist (X + Z) (Y + Z) = edist X Y :=
  R1Process.elementaryEDist_add_right X Y Z

theorem edist_neg (X Y : ElementaryMetricProcess F μ) : edist (-X) (-Y) = edist X Y := by
  have h := edist_add_right (-X) (-Y) (X + Y)
  rw [show -X + (X + Y) = Y by abel, show -Y + (X + Y) = X by abel] at h
  exact h.symm.trans (edist_comm Y X)

theorem edist_add_le (X Y Z W : ElementaryMetricProcess F μ) :
    edist (X + Y) (Z + W) ≤ edist X Z + edist Y W := by
  have h := edist_triangle (X + Y) (Z + Y) (Z + W)
  rw [edist_add_right, add_comm Z Y, add_comm Z W, edist_add_right] at h
  simpa only [add_comm W Z] using h

theorem lipschitzWith_sub : LipschitzWith 2
    (fun p : ElementaryMetricProcess F μ × ElementaryMetricProcess F μ => p.1 - p.2) := by
  intro p q
  calc
    edist (p.1 - p.2) (q.1 - q.2) ≤ edist p.1 q.1 + edist p.2 q.2 := by
      simpa only [sub_eq_add_neg, edist_neg] using edist_add_le p.1 (-p.2) q.1 (-q.2)
    _ ≤ (2 : ENNReal) * edist p q := by
      change _ ≤ 2 * max (edist p.1 q.1) (edist p.2 q.2)
      rw [two_mul]
      exact add_le_add (le_max_left _ _) (le_max_right _ _)

instance : IsUniformAddGroup (ElementaryMetricProcess F μ) where
  uniformContinuous_sub := lipschitzWith_sub.uniformContinuous

end ElementaryMetricProcess

end FTAPTheorem42
