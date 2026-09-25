/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.ElementaryQuotient

/-! # Bounds and triangle inequalities for the elementary quotient gauges -/

namespace FTAPTheorem42.R1Process

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [hUsual : Fact (Filtration.UsualConditions μ F)]

omit [SigmaFiniteFiltration μ F] hUsual in
/-- Raw values need not be measurable everywhere; regular representatives
supply integrability of their indistinguishable test errors. -/
theorem testError_integrable (X Y : R1Process F μ)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    Integrable (elementaryEmeryTestError X.val Y.val J T) μ := by
  obtain ⟨X', hX, hXP, _⟩ := X.exists_regular_representative
  obtain ⟨Y', hY, hYP, _⟩ := Y.exists_regular_representative
  exact (elementaryEmeryTestError_integrable hXP hYP J T).congr
    (elementaryEmeryTestError_congr hX hY J T).symm

theorem elementaryGauge_le_one (T : NNReal)
    (X Y : SeparationQuotient (R1Process F μ)) : elementaryGauge T X Y ≤ 1 := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  rw [← ENNReal.ofReal_one, elementaryGauge_mk_le_iff T X Y zero_le_one]
  intro J
  have h := integral_mono_ae (testError_integrable X Y J T) (integrable_const (1 : Real))
    (Eventually.of_forall fun w => (elementaryEmeryTestError_bounds X.val Y.val J T w).2)
  simpa using h

@[simp] theorem elementaryGauge_self (T : NNReal)
    (X : SeparationQuotient (R1Process F μ)) : elementaryGauge T X X = 0 := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  simp [elementaryGauge_mk, elementaryEmeryTestError,
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope,
    FactorialChronologicalGrid.eFactorialRunningMaxEnvelope,
    FactorialChronologicalGrid.factorialRunningMax, finiteRunningMax, ChronologicalGrid.natSample]

theorem elementaryGauge_comm (T : NNReal)
    (X Y : SeparationQuotient (R1Process F μ)) : elementaryGauge T X Y = elementaryGauge T Y X := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  simp only [elementaryGauge_mk, elementaryEmeryTestError_comm X.val Y.val]

theorem elementaryGauge_triangle (T : NNReal)
    (X Y Z : SeparationQuotient (R1Process F μ)) :
    elementaryGauge T X Z ≤ elementaryGauge T X Y + elementaryGauge T Y Z := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨Z, rfl⟩ := SeparationQuotient.surjective_mk Z
  rw [elementaryGauge_mk, elementaryGauge_mk, elementaryGauge_mk]
  apply iSup_le
  intro J
  have hPoint w : elementaryEmeryTestError X.val Z.val J T w ≤
      elementaryEmeryTestError X.val Y.val J T w + elementaryEmeryTestError Y.val Z.val J T w := by
    rw [elementaryEmeryTestError_comm X.val Y.val J T]
    exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (ElementaryStrategy.gain X.val J.strategy.toElementary)
      (ElementaryStrategy.gain Z.val J.strategy.toElementary)
      (ElementaryStrategy.gain Y.val J.strategy.toElementary) T w
  have hInt := integral_mono_ae (testError_integrable X Z J T)
    ((testError_integrable X Y J T).add (testError_integrable Y Z J T))
    (Eventually.of_forall hPoint)
  simp only [Pi.add_apply] at hInt
  rw [integral_add (testError_integrable X Y J T) (testError_integrable Y Z J T)] at hInt
  have hAdd := ENNReal.ofReal_le_ofReal hInt
  rw [ENNReal.ofReal_add
    (integral_nonneg fun w => (elementaryEmeryTestError_bounds X.val Y.val J T w).1)
    (integral_nonneg fun w => (elementaryEmeryTestError_bounds Y.val Z.val J T w).1)] at hAdd
  exact hAdd.trans (add_le_add
    (le_iSup (fun K : BoundedPredictableElementaryMultiplier (Ω := Ω) F =>
      ENNReal.ofReal (∫ w, elementaryEmeryTestError X.val Y.val K T w ∂μ)) J)
    (le_iSup (fun K : BoundedPredictableElementaryMultiplier (Ω := Ω) F =>
      ENNReal.ofReal (∫ w, elementaryEmeryTestError Y.val Z.val K T w ∂μ)) J))

theorem elementaryGauge_mono {T U : NNReal} (hTU : T ≤ U)
    (X Y : SeparationQuotient (R1Process F μ)) : elementaryGauge T X Y ≤ elementaryGauge U X Y := by
  obtain ⟨X, rfl⟩ := SeparationQuotient.surjective_mk X
  obtain ⟨Y, rfl⟩ := SeparationQuotient.surjective_mk Y
  obtain ⟨X', hX, hXP, hXR, _⟩ := X.exists_regular_representative
  obtain ⟨Y', hY, hYP, hYR, _⟩ := Y.exists_regular_representative
  rw [(quotient_eq_iff X X').mpr hX, (quotient_eq_iff Y Y').mpr hY]
  simp only [elementaryGauge_mk]
  apply iSup_mono
  intro J
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono_ae (testError_integrable X' Y' J T) (testError_integrable X' Y' J U)
  apply Eventually.of_forall
  intro w
  exact PredictableElementaryEmery.cappedFiniteHorizonAbsoluteEnvelope_mono_of_rightContinuous
    _ (fun w t => (PredictableElementaryStrategy.rightContinuous_gain _ hXR J.strategy w t).sub
      (PredictableElementaryStrategy.rightContinuous_gain _ hYR J.strategy w t)) hTU w

end FTAPTheorem42.R1Process

namespace FTAPTheorem42

/-! ## A bounded elementary-test metric on decomposable process classes -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [hUsual : Fact (Filtration.UsualConditions μ F)]

namespace R1Process

noncomputable def elementaryEDist
    (X Y : SeparationQuotient (R1Process F μ)) : ENNReal :=
  ∑' n : Nat, ((2 : ENNReal)⁻¹) ^ (n + 1) * elementaryGauge (n + 1) X Y

theorem elementaryEDist_le_one (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X Y ≤ 1 := by
  have hSum : (∑' n : Nat, ((2 : ENNReal)⁻¹) ^ (n + 1)) = 1 := by
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    elementaryEDist X Y ≤ ∑' n : Nat, ((2 : ENNReal)⁻¹) ^ (n + 1) :=
      ENNReal.tsum_le_tsum fun n => by
        simpa only [mul_one] using mul_le_mul'
          (le_rfl : ((2 : ENNReal)⁻¹) ^ (n + 1) ≤ ((2 : ENNReal)⁻¹) ^ (n + 1))
          (elementaryGauge_le_one (n + 1) X Y)
    _ = 1 := hSum

theorem elementaryEDist_ne_top (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X Y ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (elementaryEDist_le_one X Y)

@[simp] theorem elementaryEDist_self (X : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X X = 0 := by simp [elementaryEDist]

theorem elementaryEDist_comm (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X Y = elementaryEDist Y X := by
  simp only [elementaryEDist, elementaryGauge_comm _ X Y]

theorem elementaryEDist_triangle (X Y Z : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X Z ≤ elementaryEDist X Y + elementaryEDist Y Z := by
  unfold elementaryEDist
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← mul_add]
  exact mul_le_mul' le_rfl (elementaryGauge_triangle (n + 1) X Y Z)

theorem elementaryEDist_eq_zero_iff (X Y : SeparationQuotient (R1Process F μ)) :
    elementaryEDist X Y = 0 ↔ X = Y := by
  constructor
  · intro h
    have hNat (n : Nat) : elementaryGauge (n + 1) X Y = 0 := by
      have hn := ENNReal.tsum_eq_zero.mp h n
      exact (mul_eq_zero.mp hn).resolve_left
        (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num)))
    have hAll (T : NNReal) : elementaryGauge T X Y = 0 := by
      apply le_antisymm _ bot_le
      have hT : T ≤ ((Nat.ceil T + 1 : Nat) : NNReal) :=
        (Nat.le_ceil T).trans (by exact_mod_cast Nat.le_succ (Nat.ceil T))
      exact (elementaryGauge_mono hT X Y).trans_eq (by simpa using hNat (Nat.ceil T))
    apply elementaryGauge_limit_unique (fun _ => X) X Y
    · intro T ε _
      exact Eventually.of_forall fun _ => by simp
    · intro T ε _
      exact Eventually.of_forall fun _ => by rw [hAll T]; exact bot_le
  · rintro rfl
    exact elementaryEDist_self X

end R1Process

/-- A type synonym equips the same process classes with the elementary
metric without replacing their existing R1 metric instance. -/
def ElementaryMetricProcess
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
    [Fact (Filtration.UsualConditions μ F)] := SeparationQuotient (R1Process F μ)

namespace ElementaryMetricProcess

noncomputable instance : MetricSpace (ElementaryMetricProcess F μ) where
  dist X Y := (R1Process.elementaryEDist X Y).toReal
  dist_self X := congrArg ENNReal.toReal (R1Process.elementaryEDist_self X)
  dist_comm X Y := congrArg ENNReal.toReal (R1Process.elementaryEDist_comm X Y)
  dist_triangle X Y Z := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨R1Process.elementaryEDist_ne_top X Y,
        R1Process.elementaryEDist_ne_top Y Z⟩) (R1Process.elementaryEDist_triangle X Y Z)
    simpa only [ENNReal.toReal_add (R1Process.elementaryEDist_ne_top X Y)
      (R1Process.elementaryEDist_ne_top Y Z)] using h
  eq_of_dist_eq_zero := by
    intro X Y h
    exact (R1Process.elementaryEDist_eq_zero_iff X Y).mp
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (R1Process.elementaryEDist_ne_top X Y))
  edist X Y := R1Process.elementaryEDist X Y
  edist_dist X Y := (ENNReal.ofReal_toReal (R1Process.elementaryEDist_ne_top X Y)).symm

end ElementaryMetricProcess

end FTAPTheorem42
