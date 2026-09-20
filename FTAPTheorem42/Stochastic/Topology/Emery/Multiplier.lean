/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Realization
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct

/-!
# Products of predictable elementary multipliers

Products preserve the unit bound; coefficient-bounded multipliers also retain the
coefficient-sum bound needed by realized integral rows.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! A multiplier with the coefficient-sum invariant needed by realized rows. -/
structure CoefficientBoundedPredictableElementaryMultiplier
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    extends BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ where
  coefficientAbsSumBound : ℝ≥0
  coefficientAbsSum_le : ∀ ω,
    toBoundedPredictableElementaryMultiplier.strategy.coefficientAbsSum ω ≤
      coefficientAbsSumBound

namespace BoundedPredictableElementaryMultiplier

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-! Product of two ordinary bounded elementary tests. -/
noncomputable def mul
    (J K : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) :
    BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ where
  strategy := J.strategy.mul K.strategy
  abs_integrand_le_one := by
    intro t ω
    rw [PredictableElementaryStrategy.mul_integrand]
    change |J.strategy.integrand t ω * K.strategy.integrand t ω| ≤ 1
    rw [abs_mul]
    calc
      |J.strategy.integrand t ω| * |K.strategy.integrand t ω| ≤
          1 * 1 := mul_le_mul (J.abs_integrand_le_one t ω)
            (K.abs_integrand_le_one t ω) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num

@[simp]
theorem mul_strategy
    (J K : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) :
    (J.mul K).strategy = J.strategy.mul K.strategy :=
  rfl

end BoundedPredictableElementaryMultiplier

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem coefficientAbsSum_mul_le
    (J : CoefficientBoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) (C : ℝ≥0)
    (hH : ∀ ω, H.coefficientAbsSum ω ≤ C) :
    ∀ ω, (J.strategy.mul H).coefficientAbsSum ω ≤
      J.coefficientAbsSumBound * C := by
  intro ω
  rw [PredictableElementaryStrategy.coefficientAbsSum_mul]
  calc
    J.strategy.coefficientAbsSum ω * H.coefficientAbsSum ω ≤
        (J.coefficientAbsSumBound : ℝ) * H.coefficientAbsSum ω :=
      mul_le_mul_of_nonneg_right (J.coefficientAbsSum_le ω)
        (H.coefficientAbsSum_nonneg ω)
    _ ≤ (J.coefficientAbsSumBound : ℝ) * (C : ℝ) :=
      mul_le_mul_of_nonneg_left (hH ω) (by positivity)
    _ = ((J.coefficientAbsSumBound * C : ℝ≥0) : ℝ) := by
      norm_num

private theorem interval_gain_mul_overlap_test
    (S : Process Ω) (B C : PredictableElementaryInterval ℱ)
    (t : ℝ≥0) (ω : Ω) :
    ElementaryInterval.gain S (B.mul C).interval t ω =
      if max (B.interval.startTime ω) (C.interval.startTime ω) <
          min (B.interval.stopTime ω) (C.interval.stopTime ω) then
        (B.interval.coefficient ω * C.interval.coefficient ω) *
          (S (min t (min (B.interval.stopTime ω)
              (C.interval.stopTime ω))) ω -
            S (min t (max (B.interval.startTime ω)
              (C.interval.startTime ω))) ω)
      else 0 := by
  simp only [PredictableElementaryInterval.mul, ElementaryInterval.gain]
  by_cases hOverlap :
      max (B.interval.startTime ω) (C.interval.startTime ω) <
        min (B.interval.stopTime ω) (C.interval.stopTime ω)
  · rw [ite_eq_left hOverlap]
    simp only [max_eq_right hOverlap.le, mul_sub]
  · rw [ite_eq_right hOverlap]
    have hOrder :
        min (B.interval.stopTime ω) (C.interval.stopTime ω) ≤
          max (B.interval.startTime ω) (C.interval.startTime ω) :=
      le_of_not_gt hOverlap
    simp only [max_eq_left hOrder, sub_self, mul_zero]

private theorem interval_increment_intersection
    (f : ℝ≥0 → ℝ) {a b c d t : ℝ≥0}
    (hab : a ≤ b) (hcd : c ≤ d) :
    (f (min (min t b) d) - f (min (min t b) c)) -
        (f (min (min t a) d) - f (min (min t a) c)) =
      if max a c < min b d then
        f (min t (min b d)) - f (min t (max a c))
      else 0 := by
  rcases le_total a c with hac | hca
  · rcases le_total b d with hbd | hdb
    · by_cases hcb : c < b
      · have hOverlap : max a c < min b d := by
          simp only [max_eq_right hac, min_eq_left hbd]
          exact hcb
        rw [ite_eq_left hOverlap]
        have h1 : min (min t b) d = min t b := by
          rw [min_assoc, min_eq_left hbd]
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right hcb.le]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hac.trans hcb.le |>.trans hbd)]
        have h4 : min (min t a) c = min t a := by
          rw [min_assoc, min_eq_left hac]
        rw [h1, h2, h3, h4, min_eq_left hbd, max_eq_right hac]
        ring
      · have hbc : b ≤ c := le_of_not_gt hcb
        have hNo : ¬ max a c < min b d := by
          intro h
          exact (not_lt_of_ge hbc)
            ((le_max_right _ _).trans_lt (h.trans_le (min_le_left _ _)))
        rw [ite_eq_right hNo]
        have h1 : min (min t b) d = min t b := by
          rw [min_assoc, min_eq_left hbd]
        have h2 : min (min t b) c = min t b := by
          rw [min_assoc, min_eq_left hbc]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hab.trans hbd)]
        have h4 : min (min t a) c = min t a := by
          rw [min_assoc, min_eq_left (hab.trans hbc)]
        rw [h1, h2, h3, h4]
        ring
    · have hdb' : d ≤ b := hdb
      by_cases hcd' : c < d
      · have hOverlap : max a c < min b d := by
          simp only [max_eq_right hac, min_eq_right hdb']
          exact hcd'
        rw [ite_eq_left hOverlap]
        have h1 : min (min t b) d = min t d := by
          rw [min_assoc, min_eq_right hdb']
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hcd'.le.trans hdb')]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hac.trans hcd)]
        have h4 : min (min t a) c = min t a := by
          rw [min_assoc, min_eq_left hac]
        rw [h1, h2, h3, h4, min_eq_right hdb', max_eq_right hac]
        ring
      · have hcd_eq : c = d := le_antisymm hcd (le_of_not_gt hcd')
        have hNo : ¬ max a c < min b d := by
          apply not_lt_of_ge
          rw [max_eq_right hac]
          exact (min_le_right _ _).trans_eq hcd_eq.symm
        rw [ite_eq_right hNo]
        have h1 : min (min t b) d = min t d := by
          rw [min_assoc, min_eq_right hdb']
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hcd.trans hdb')]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hac.trans hcd)]
        have h4 : min (min t a) c = min t a := by
          rw [min_assoc, min_eq_left hac]
        rw [h1, h2, h3, h4]
        rw [hcd_eq]
        ring
  · rcases le_total b d with hbd | hdb
    · by_cases hab' : a < b
      · have hOverlap : max a c < min b d := by
          simp only [max_eq_left hca, min_eq_left hbd]
          exact hab'
        rw [ite_eq_left hOverlap]
        have h1 : min (min t b) d = min t b := by
          rw [min_assoc, min_eq_left hbd]
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hca.trans hab'.le)]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hab'.le.trans hbd)]
        have h4 : min (min t a) c = min t c := by
          rw [min_assoc, min_eq_right hca]
        rw [h1, h2, h3, h4, min_eq_left hbd, max_eq_left hca]
        ring
      · have hba : b ≤ a := le_of_not_gt hab'
        have hNo : ¬ max a c < min b d := by
          intro h
          exact (not_lt_of_ge hba)
            ((le_max_left _ _).trans_lt (h.trans_le (min_le_left _ _)))
        rw [ite_eq_right hNo]
        have hab_eq : a = b := le_antisymm hab hba
        have h1 : min (min t b) d = min t b := by
          rw [min_assoc, min_eq_left hbd]
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hca.trans hab)]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left (hab.trans hbd)]
        have h4 : min (min t a) c = min t c := by
          rw [min_assoc, min_eq_right hca]
        rw [h1, h2, h3, h4, hab_eq]
        ring
    · have hdb' : d ≤ b := hdb
      by_cases had : a < d
      · have hOverlap : max a c < min b d := by
          simp only [max_eq_left hca, min_eq_right hdb']
          exact had
        rw [ite_eq_left hOverlap]
        have h1 : min (min t b) d = min t d := by
          rw [min_assoc, min_eq_right hdb']
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hca.trans hab)]
        have h3 : min (min t a) d = min t a := by
          rw [min_assoc, min_eq_left had.le]
        have h4 : min (min t a) c = min t c := by
          rw [min_assoc, min_eq_right hca]
        rw [h1, h2, h3, h4, min_eq_right hdb', max_eq_left hca]
        ring
      · have hda : d ≤ a := le_of_not_gt had
        have hNo : ¬ max a c < min b d := by
          intro h
          exact (not_lt_of_ge hda)
            ((le_max_left _ _).trans_lt (h.trans_le (min_le_right _ _)))
        rw [ite_eq_right hNo]
        have h1 : min (min t b) d = min t d := by
          rw [min_assoc, min_eq_right hdb']
        have h2 : min (min t b) c = min t c := by
          rw [min_assoc, min_eq_right (hca.trans hab)]
        have h3 : min (min t a) d = min t d := by
          rw [min_assoc, min_eq_right hda]
        have h4 : min (min t a) c = min t c := by
          rw [min_assoc, min_eq_right hca]
        rw [h1, h2, h3, h4]
        ring

private theorem elementaryInterval_gain_source_mul
    (S : Process Ω) (B C : PredictableElementaryInterval ℱ)
    (t : ℝ≥0) (ω : Ω) :
    ElementaryInterval.gain
        (fun s ω' => ElementaryInterval.gain S C.interval s ω')
        B.interval t ω =
      ElementaryInterval.gain S (B.mul C).interval t ω := by
  rw [interval_gain_mul_overlap_test S B C t ω]
  unfold ElementaryInterval.gain
  have hInc := interval_increment_intersection
    (fun s => S s ω)
    (a := B.interval.startTime ω) (b := B.interval.stopTime ω)
    (c := C.interval.startTime ω) (d := C.interval.stopTime ω)
    (t := t) (B.interval.start_le_stop ω) (C.interval.start_le_stop ω)
  simp only
  rw [← mul_sub]
  rw [hInc]
  split_ifs <;> ring

private theorem elementaryInterval_gain_source_elementaryGain
    (S : Process Ω) (B : PredictableElementaryInterval ℱ)
    (H : PredictableElementaryStrategy ℱ) (t : ℝ≥0) (ω : Ω) :
    ElementaryInterval.gain (elementaryGain S H) B.interval t ω =
      elementaryGain S
        (PredictableElementaryStrategy.mul
          ([B] : PredictableElementaryStrategy ℱ) H) t ω := by
  induction H with
  | nil =>
      simp [elementaryGain, PredictableElementaryStrategy.mul,
        PredictableElementaryStrategy.toElementary, ElementaryStrategy.gain,
        ElementaryInterval.gain]
  | cons C H ih =>
      change ElementaryInterval.gain
          (fun s ω' => elementaryGain S (C :: H) s ω') B.interval t ω =
          elementaryGain S
          (PredictableElementaryStrategy.mul
            ([B] : PredictableElementaryStrategy ℱ) (C :: H)) t ω
      rw [show (fun s ω' => elementaryGain S (C :: H) s ω') =
          (fun s ω' => elementaryGain S [C] s ω' + elementaryGain S H s ω') by
            funext s ω'
            simp [elementaryGain, PredictableElementaryStrategy.toElementary,
              ElementaryStrategy.gain]]
      rw [ElementaryInterval.gain_add_price]
      have hC := elementaryInterval_gain_source_mul S B C t ω
      have hC' : elementaryGain S [C] =
          (fun s ω' => ElementaryInterval.gain S C.interval s ω') := by
        funext s ω'
        simp [elementaryGain, PredictableElementaryStrategy.toElementary,
          ElementaryStrategy.gain]
      rw [hC']
      rw [hC]
      rw [ih]
      rfl

theorem elementaryGain_source_mul
    (S : Process Ω) (J H : PredictableElementaryStrategy ℱ) :
    elementaryGain (elementaryGain S H) J =
      elementaryGain S (J.mul H) := by
  induction J with
  | nil =>
      funext t ω
      simp [elementaryGain, PredictableElementaryStrategy.mul,
        PredictableElementaryStrategy.toElementary, ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      change ElementaryInterval.gain (elementaryGain S H) B.interval t ω +
          elementaryGain (elementaryGain S H) J t ω =
          elementaryGain S
            (PredictableElementaryStrategy.mul (B :: J) H) t ω
      rw [elementaryInterval_gain_source_elementaryGain]
      rw [congrFun (congrFun ih t) ω]
      have hmul :
          PredictableElementaryStrategy.mul (B :: J) H =
            PredictableElementaryStrategy.mul [B] H ++
              PredictableElementaryStrategy.mul J H := by
        simp [PredictableElementaryStrategy.mul]
      rw [hmul]
      have hgain_append (K L : PredictableElementaryStrategy ℱ) :
          elementaryGain S (K ++ L) t ω =
            elementaryGain S K t ω + elementaryGain S L t ω := by
        simp [elementaryGain, PredictableElementaryStrategy.toElementary,
          ElementaryStrategy.gain_append]
      rw [hgain_append]

theorem elementaryGain_source_sub
    (X Y : Process Ω) (J : PredictableElementaryStrategy ℱ) :
    elementaryGain (fun t ω => X t ω - Y t ω) J =
      (fun t ω => elementaryGain X J t ω - elementaryGain Y J t ω) := by
  induction J with
  | nil =>
      funext t ω
      simp [elementaryGain, PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      change ElementaryInterval.gain
          (fun s ω' => X s ω' - Y s ω') B.interval t ω +
          elementaryGain (fun s ω' => X s ω' - Y s ω') J t ω =
        (ElementaryInterval.gain X B.interval t ω + elementaryGain X J t ω) -
          (ElementaryInterval.gain Y B.interval t ω + elementaryGain Y J t ω)
      have hB : ElementaryInterval.gain
            (fun s ω' => X s ω' - Y s ω') B.interval t ω =
          ElementaryInterval.gain X B.interval t ω -
            ElementaryInterval.gain Y B.interval t ω := by
        simp [ElementaryInterval.gain]
        ring
      rw [hB, congrFun (congrFun ih t) ω]
      ring

theorem elementaryGain_transform_error
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (X : Process Ω) (J : PredictableElementaryStrategy ℱ) :
    (fun t ω => elementaryGain S (J.mul H) t ω -
      elementaryGain X J t ω) =
      elementaryGain
        (fun t ω => elementaryGain S H t ω - X t ω) J := by
  funext t ω
  have hSub := congrFun (congrFun
    (elementaryGain_source_sub (elementaryGain S H) X J) t) ω
  have hAssoc := congrFun (congrFun (elementaryGain_source_mul S J H) t) ω
  symm
  calc
    elementaryGain
        (fun t ω => elementaryGain S H t ω - X t ω) J t ω =
        elementaryGain (elementaryGain S H) J t ω -
          elementaryGain X J t ω := hSub
    _ = elementaryGain S (J.mul H) t ω -
          elementaryGain X J t ω := by rw [hAssoc]

private theorem abs_elementaryGain_le_coefficientAbsSum_mul
    (X : Process Ω) (H : PredictableElementaryStrategy ℱ)
    (T t : ℝ≥0) (ht : t ≤ T) (ω : Ω) (E : ℝ)
    (hX : ∀ u, u ≤ T → |X u ω| ≤ E) :
    |elementaryGain X H t ω| ≤
      2 * H.coefficientAbsSum ω * E := by
  have hE : 0 ≤ E :=
    (abs_nonneg (X 0 ω)).trans (hX 0 (bot_le.trans ht))
  induction H with
  | nil =>
      simp [elementaryGain, PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain, PredictableElementaryStrategy.coefficientAbsSum]
  | cons B H ih =>
      have hBlock : |B.interval.gain X t ω| ≤
          2 * |B.interval.coefficient ω| * E := by
        unfold ElementaryInterval.gain
        calc
          |B.interval.coefficient ω *
              (X (min t (B.interval.stopTime ω)) ω -
                X (min t (B.interval.startTime ω)) ω)| =
              |B.interval.coefficient ω| *
                |X (min t (B.interval.stopTime ω)) ω -
                  X (min t (B.interval.startTime ω)) ω| := by
            rw [abs_mul]
          _ ≤ |B.interval.coefficient ω| * (E + E) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (abs_sub _ _).trans (add_le_add
              (hX _ ((min_le_left _ _).trans ht))
              (hX _ ((min_le_left _ _).trans ht)))
          _ = 2 * |B.interval.coefficient ω| * E := by ring
      change |B.interval.gain X t ω + elementaryGain X H t ω| ≤ _
      calc
        |B.interval.gain X t ω + elementaryGain X H t ω| ≤
            |B.interval.gain X t ω| + |elementaryGain X H t ω| :=
          abs_add_le _ _
        _ ≤ 2 * |B.interval.coefficient ω| * E +
            2 * PredictableElementaryStrategy.coefficientAbsSum H ω * E :=
          add_le_add hBlock ih
        _ = 2 * (|B.interval.coefficient ω| +
            PredictableElementaryStrategy.coefficientAbsSum H ω) * E := by
          ring

private theorem cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_le
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (J : PredictableElementaryStrategy ℱ) (C : ℝ≥0)
    (hJ : ∀ ω, J.coefficientAbsSum ω ≤ C)
    (T : ℝ≥0) (ω : Ω) :
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (elementaryGain X J) T ω ≤
      max (2 * (C : ℝ)) 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω := by
  let E := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
    (fun t ω => |X t ω|) T ω
  by_cases hE : E = ∞
  · have hCapOut :=
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_le_one
        (elementaryGain X J) T ω
    have hCapIn :
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope X T ω = 1 := by
      unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      simp only [E, hE]
      rfl
    rw [hCapIn]
    exact hCapOut.trans (le_mul_of_one_le_left (by positivity)
      (le_max_right (2 * (C : ℝ)) 1))
  · have hRightAbs : ∀ ω t,
        ContinuousWithinAt ((fun s => |X s ω|)) (Set.Ici t) t := by
      intro ω t
      exact (hXRight ω t).abs
    have hXBound : ∀ u, u ≤ T → |X u ω| ≤ E.toReal := by
      intro u hu
      have hValue := FactorialChronologicalGrid.ofReal_le_eFactorialRunningMaxEnvelope
        (fun t ω => |X t ω|) T hRightAbs ω hu
      have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hE).2 hValue
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using hReal
    have hOutBound : ∀ u, u ≤ T →
        |elementaryGain X J u ω| ≤ 2 * (C : ℝ) * E.toReal := by
      intro u hu
      calc
        |elementaryGain X J u ω| ≤
            2 * J.coefficientAbsSum ω * E.toReal :=
          abs_elementaryGain_le_coefficientAbsSum_mul X J T u hu ω E.toReal hXBound
        _ = (2 * E.toReal) * J.coefficientAbsSum ω := by ring
        _ ≤ (2 * E.toReal) * (C : ℝ) := by
          exact mul_le_mul_of_nonneg_left (hJ ω) (by positivity)
        _ = 2 * (C : ℝ) * E.toReal := by ring
    have hOutE := FactorialChronologicalGrid.eFactorialRunningMaxEnvelope_abs_le_of_bound
      (elementaryGain X J) T hOutBound
    unfold FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    have hMin := min_le_min_right (1 : ℝ≥0∞) hOutE
    have hMinReal := ENNReal.toReal_mono
      (ne_top_of_le_ne_top (by finiteness)
        (min_le_right
          (ENNReal.ofReal (2 * (C : ℝ) * E.toReal)) 1)) hMin
    calc
      (min
          (FactorialChronologicalGrid.eFactorialRunningMaxEnvelope
            (fun t ω => |elementaryGain X J t ω|) T ω) 1).toReal ≤
          (min (ENNReal.ofReal (2 * (C : ℝ) * E.toReal)) 1).toReal := hMinReal
      _ ≤ max (2 * (C : ℝ)) 1 * (min E 1).toReal := by
        have hCap := SemimartingaleQuasiNorm.cappedEnvelope_cap_scale
          (2 * (C : ℝ)) (by positivity) E
        convert hCap using 1
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hE]

private theorem left_nested_overlap_iff_test
    {a b c d e f : ℝ≥0} :
    max (max a c) e < min (max (max a c) (min b d)) f ↔
      max a (max c e) < min b (min d f) := by
  by_cases hbc : max a c ≤ min b d
  · rw [max_eq_right hbc]
    simp only [max_assoc, min_assoc]
  · constructor
    · intro h
      have hBad : max (max a c) e < max a c := by
        rw [max_eq_left (le_of_not_ge hbc)] at h
        exact lt_of_lt_of_le h (min_le_left _ _)
      exact False.elim ((not_lt_of_ge (le_max_left _ _)) hBad)
    · intro h
      have hFalse : max a c < min b d := by
        apply lt_min
        · calc
            max a c ≤ max a (max c e) := max_le_max_left _ (le_max_left _ _)
            _ < b := lt_of_lt_of_le h (min_le_left _ _)
        · calc
            max a c ≤ max a (max c e) := max_le_max_left _ (le_max_left _ _)
            _ < d := lt_of_lt_of_le h
              ((min_le_right _ _).trans (min_le_left _ _))
      exact False.elim (hbc (le_of_lt hFalse))

private theorem interval_gain_mul_assoc_test
    (S : Process Ω) (B C D : PredictableElementaryInterval ℱ)
    (t : ℝ≥0) (ω : Ω) :
    ElementaryInterval.gain S ((B.mul C).mul D).interval t ω =
      ElementaryInterval.gain S (B.mul (C.mul D)).interval t ω := by
  have hLeftIff := left_nested_overlap_iff_test
    (a := B.interval.startTime ω) (b := B.interval.stopTime ω)
    (c := C.interval.startTime ω) (d := C.interval.stopTime ω)
    (e := D.interval.startTime ω) (f := D.interval.stopTime ω)
  have hRightRev := left_nested_overlap_iff_test
    (a := D.interval.startTime ω) (b := D.interval.stopTime ω)
    (c := C.interval.startTime ω) (d := C.interval.stopTime ω)
    (e := B.interval.startTime ω) (f := B.interval.stopTime ω)
  have hRightIff :
      max (B.interval.startTime ω)
          (max (C.interval.startTime ω) (D.interval.startTime ω)) <
        min (B.interval.stopTime ω)
          (max (max (C.interval.startTime ω) (D.interval.startTime ω))
            (min (C.interval.stopTime ω) (D.interval.stopTime ω))) ↔
      max (B.interval.startTime ω)
          (max (C.interval.startTime ω) (D.interval.startTime ω)) <
        min (B.interval.stopTime ω)
          (min (C.interval.stopTime ω) (D.interval.stopTime ω)) := by
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm,
      min_assoc] using hRightRev
  rw [interval_gain_mul_overlap_test S (B.mul C) D t ω,
    interval_gain_mul_overlap_test S B (C.mul D) t ω]
  by_cases h :
      max (B.interval.startTime ω) (max (C.interval.startTime ω)
        (D.interval.startTime ω)) <
        min (B.interval.stopTime ω) (min (C.interval.stopTime ω)
          (D.interval.stopTime ω))
  · have hLeft' :
        max ((B.mul C).interval.startTime ω) (D.interval.startTime ω) <
          min ((B.mul C).interval.stopTime ω) (D.interval.stopTime ω) := by
      change
        max (max (B.interval.startTime ω) (C.interval.startTime ω))
            (D.interval.startTime ω) <
          min (max (max (B.interval.startTime ω) (C.interval.startTime ω))
              (min (B.interval.stopTime ω) (C.interval.stopTime ω)))
            (D.interval.stopTime ω)
      exact hLeftIff.mpr h
    have hRight' :
        max (B.interval.startTime ω) ((C.mul D).interval.startTime ω) <
          min (B.interval.stopTime ω) ((C.mul D).interval.stopTime ω) := by
      change
        max (B.interval.startTime ω)
            (max (C.interval.startTime ω) (D.interval.startTime ω)) <
          min (B.interval.stopTime ω)
          (max (max (C.interval.startTime ω) (D.interval.startTime ω))
            (min (C.interval.stopTime ω) (D.interval.stopTime ω)))
      exact hRightIff.mpr h
    rw [ite_eq_left hLeft', ite_eq_left hRight']
    simp only [PredictableElementaryInterval.mul]
    have hs :
        max (max (B.interval.startTime ω) (C.interval.startTime ω))
            (D.interval.startTime ω) =
          max (B.interval.startTime ω)
            (max (C.interval.startTime ω) (D.interval.startTime ω)) := by
      ac_rfl
    have huBC :
        max (B.interval.startTime ω) (C.interval.startTime ω) ≤
          min (B.interval.stopTime ω) (C.interval.stopTime ω) := by
      have hltB :
          max (B.interval.startTime ω)
              (max (C.interval.startTime ω) (D.interval.startTime ω)) <
            B.interval.stopTime ω :=
        (lt_min_iff.mp h).1
      have hltC :
          max (B.interval.startTime ω)
              (max (C.interval.startTime ω) (D.interval.startTime ω)) <
            C.interval.stopTime ω :=
        (lt_min_iff.mp (lt_min_iff.mp h).2).1
      apply le_min
      · exact (max_le_max_left _ (le_max_left _ _)).trans (le_of_lt hltB)
      · exact (max_le_max_left _ (le_max_left _ _)).trans (le_of_lt hltC)
    have huCD :
        max (C.interval.startTime ω) (D.interval.startTime ω) ≤
          min (C.interval.stopTime ω) (D.interval.stopTime ω) := by
      have hltC :
          max (B.interval.startTime ω)
              (max (C.interval.startTime ω) (D.interval.startTime ω)) <
            C.interval.stopTime ω :=
        (lt_min_iff.mp (lt_min_iff.mp h).2).1
      have hltD :
          max (B.interval.startTime ω)
              (max (C.interval.startTime ω) (D.interval.startTime ω)) <
            D.interval.stopTime ω :=
        (lt_min_iff.mp (lt_min_iff.mp h).2).2
      apply le_min
      · exact (le_max_right _ _).trans (le_of_lt hltC)
      · exact (le_max_right _ _).trans (le_of_lt hltD)
    rw [max_eq_right huBC, max_eq_right huCD]
    simp only [hs, min_assoc]
    ring
  · have hL : ¬
        max (max (B.interval.startTime ω) (C.interval.startTime ω))
            (D.interval.startTime ω) <
          min (min (B.interval.stopTime ω) (C.interval.stopTime ω))
            (D.interval.stopTime ω) := by
      intro hL
      exact h (by simpa only [max_assoc, min_assoc] using hL)
    have hR : ¬
        max (B.interval.startTime ω)
            (max (C.interval.startTime ω) (D.interval.startTime ω)) <
          min (B.interval.stopTime ω)
            (min (C.interval.stopTime ω) (D.interval.stopTime ω)) := by
      intro hR
      exact h (by simpa only [max_assoc, min_assoc] using hR)
    have hLeft' : ¬
        max ((B.mul C).interval.startTime ω) (D.interval.startTime ω) <
          min ((B.mul C).interval.stopTime ω) (D.interval.stopTime ω) := by
      intro hBad
      change
        max (max (B.interval.startTime ω) (C.interval.startTime ω))
            (D.interval.startTime ω) <
          min (max (max (B.interval.startTime ω) (C.interval.startTime ω))
              (min (B.interval.stopTime ω) (C.interval.stopTime ω)))
            (D.interval.stopTime ω) at hBad
      exact h (hLeftIff.mp hBad)
    have hRight' : ¬
        max (B.interval.startTime ω) ((C.mul D).interval.startTime ω) <
          min (B.interval.stopTime ω) ((C.mul D).interval.stopTime ω) := by
      intro hBad
      change
        max (B.interval.startTime ω)
            (max (C.interval.startTime ω) (D.interval.startTime ω)) <
          min (B.interval.stopTime ω)
            (max (max (C.interval.startTime ω) (D.interval.startTime ω))
              (min (C.interval.stopTime ω) (D.interval.stopTime ω))) at hBad
      exact h (hRightIff.mp hBad)
    rw [ite_eq_right hLeft', ite_eq_right hRight']

private theorem elementaryGain_map_interval_mul_assoc_test
    (S : Process Ω) (B C : PredictableElementaryInterval ℱ)
    (H : PredictableElementaryStrategy ℱ) (t : ℝ≥0) (ω : Ω) :
    ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (H.map C.mul |>.map B.mul)) t ω =
      ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (H.map fun D => (B.mul C).mul D)) t ω := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.toElementary,
      ElementaryStrategy.gain]
  | cons D H ih =>
      change ElementaryInterval.gain S
          (B.mul (C.mul D)).interval t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (H.map C.mul |>.map B.mul)) t ω =
        ElementaryInterval.gain S
            ((B.mul C).mul D).interval t ω +
          ElementaryStrategy.gain S
            (PredictableElementaryStrategy.toElementary
              (H.map fun E => (B.mul C).mul E)) t ω
      rw [interval_gain_mul_assoc_test S B C D t ω, ih]

private theorem elementaryGain_map_mul_assoc_test
    (S : Process Ω) (B : PredictableElementaryInterval ℱ)
    (K H : PredictableElementaryStrategy ℱ) (t : ℝ≥0) (ω : Ω) :
    ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          (K.mul H |>.map B.mul)) t ω =
      ElementaryStrategy.gain S
        (PredictableElementaryStrategy.toElementary
          ((K.map B.mul).flatMap fun C => H.map C.mul)) t ω := by
  induction K with
  | nil => simp [PredictableElementaryStrategy.mul,
      PredictableElementaryStrategy.toElementary,
      ElementaryStrategy.gain]
  | cons C K ih =>
      simp only [PredictableElementaryStrategy.mul, List.flatMap_cons,
        List.map_append]
      change ElementaryStrategy.gain S
          (PredictableElementaryStrategy.toElementary
            (List.map B.mul (H.map C.mul) ++
              List.map B.mul (List.flatMap (fun C => H.map C.mul) K))) t ω =
        ElementaryStrategy.gain S
          (PredictableElementaryStrategy.toElementary
            (List.flatMap (fun C => H.map C.mul) (List.map B.mul (C :: K)))) t ω
      rw [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      simp only [List.map_cons, List.flatMap_cons]
      rw [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      have hHead := elementaryGain_map_interval_mul_assoc_test S B C H t ω
      rw [hHead]
      have hTail :
          ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.map B.mul (List.flatMap (fun C => H.map C.mul) K))) t ω =
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.flatMap (fun C => H.map C.mul) (List.map B.mul K))) t ω := by
        simpa only [PredictableElementaryStrategy.mul] using ih
      rw [hTail]

private theorem elementaryGain_mul_assoc_test
    (S : Process Ω)
    (J K H : PredictableElementaryStrategy ℱ) :
    elementaryGain S (J.mul (K.mul H)) =
      elementaryGain S ((J.mul K).mul H) := by
  induction J with
  | nil =>
      funext t ω
      simp [PredictableElementaryStrategy.mul, elementaryGain,
        PredictableElementaryStrategy.toElementary, ElementaryStrategy.gain]
  | cons B J ih =>
      funext t ω
      unfold PredictableElementaryStrategy.mul elementaryGain
      simp only [List.flatMap_cons]
      rw [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      simp only [List.flatMap_append]
      rw [PredictableElementaryStrategy.toElementary_append,
        ElementaryStrategy.gain_append]
      have hHead :
          ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.map B.mul (List.flatMap
                  (fun C => H.map C.mul) K))) t ω =
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.flatMap (fun C => H.map C.mul)
                  (List.map B.mul K))) t ω := by
        simpa only [PredictableElementaryStrategy.mul] using
          elementaryGain_map_mul_assoc_test S B K H t ω
      have hTail := congrFun (congrFun ih t) ω
      have hTail' :
          ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.flatMap
                  (fun B => List.map B.mul
                    (List.flatMap (fun C => H.map C.mul) K)) J)) t ω =
            ElementaryStrategy.gain S
              (PredictableElementaryStrategy.toElementary
                (List.flatMap (fun B => H.map B.mul)
                  (List.flatMap (fun B => List.map B.mul K) J))) t ω := by
        simpa only [PredictableElementaryStrategy.mul, elementaryGain] using hTail
      rw [hHead, hTail']

/-! Product associativity at the finite gain level. -/
theorem elementaryGain_mul_assoc
    (S : Process Ω)
    (J K H : PredictableElementaryStrategy ℱ) :
    elementaryGain S (J.mul (K.mul H)) =
      elementaryGain S ((J.mul K).mul H) := by
  exact elementaryGain_mul_assoc_test S J K H

theorem testedGain_mul_right_assoc
    (S : Process Ω)
    (L J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : PredictableElementaryStrategy ℱ) :
      testedGain S L (J.strategy.mul H) =
      testedGain S (L.mul J) H := by
  change elementaryGain S (L.strategy.mul (J.strategy.mul H)) =
    elementaryGain S ((L.mul J).strategy.mul H)
  rw [BoundedPredictableElementaryMultiplier.mul_strategy,
    elementaryGain_mul_assoc]

theorem testedDifference_mul_right_assoc
    (S : Process Ω)
    (L J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) :
    testedDifference S L (J.strategy.mul H) (J.strategy.mul K) =
      testedDifference S (L.mul J) H K := by
  unfold testedDifference
  rw [testedGain_mul_right_assoc, testedGain_mul_right_assoc]

theorem testValue_mul_right_assoc
    (μ : Measure Ω) (S : Process Ω)
    (L J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    testValue μ S L (J.strategy.mul H) (J.strategy.mul K) T =
      testValue μ S (L.mul J) H K T := by
  unfold testValue
  rw [show testedDifference S L (J.strategy.mul H) (J.strategy.mul K) =
      testedDifference S (L.mul J) H K by
    exact testedDifference_mul_right_assoc S L J H K]

theorem gauge_mul_right_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H K : PredictableElementaryStrategy ℱ) (T : ℝ≥0) :
    gauge μ S (J.strategy.mul H) (J.strategy.mul K) T ≤
      gauge μ S H K T := by
  have hNonneg := gauge_nonnegative (μ := μ) (ℱ := ℱ) S hS H K T
  unfold gauge
  apply csSup_le (Set.insert_nonempty 0 _)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | ⟨L, rfl⟩
  · exact hNonneg
  · change testValue μ S L (J.strategy.mul H) (J.strategy.mul K) T ≤ _
    rw [testValue_mul_right_assoc]
    exact le_csSup (gauge_bddAbove (μ := μ) (ℱ := ℱ) S hS H K T)
      (Set.mem_insert_of_mem 0 (Set.mem_range_self (L.mul J)))

theorem isCauchy_mul_right
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) ℱ)
    (H : ℕ → PredictableElementaryStrategy ℱ)
    (hH : IsCauchy μ S H) :
    IsCauchy μ S (fun n => J.strategy.mul (H n)) := by
  intro T
  have hUpper : Tendsto
      (fun p : ℕ × ℕ => gauge μ S (H p.1) (H p.2) T)
      atTop (𝓝 0) := hH T
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds) hUpper
  · filter_upwards [] with p
    exact gauge_nonnegative S hS
      (J.strategy.mul (H p.1)) (J.strategy.mul (H p.2)) T
  · filter_upwards [] with p
    exact gauge_mul_right_le S hS J (H p.1) (H p.2) T

noncomputable def RealizedStrategy.transform
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : RealizedStrategy (ℱ := ℱ) μ S)
    (J : CoefficientBoundedPredictableElementaryMultiplier (Ω := Ω) ℱ) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun n => J.strategy.mul (H.representative n)
  representativeBound := fun n =>
    J.coefficientAbsSumBound * H.representativeBound n
  representative_coefficientAbsSum_le := by
    intro n ω
    exact coefficientAbsSum_mul_le J (H.representative n)
      (H.representativeBound n)
      (H.representative_coefficientAbsSum_le n) ω
  gain := elementaryGain H.gain J.strategy
  gain_stronglyAdapted := by
    exact PredictableElementaryStrategy.stronglyAdapted_gain H.gain
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous
        H.gain_stronglyAdapted H.gain_rightContinuous) J.strategy
  gain_rightContinuous := by
    exact PredictableElementaryStrategy.rightContinuous_gain H.gain
      H.gain_rightContinuous J.strategy
  gain_hasLeftLimits := by
    exact ElementaryStrategy.gain_hasLeftLimits H.gain
      H.gain_hasLeftLimits J.strategy.toElementary
  gain_convergence := by
    intro r
    refine tendstoInMeasure_of_nonneg_le
      (f := fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S
            (J.strategy.mul (H.representative n)) t ω -
          elementaryGain H.gain J.strategy t ω)
        ((r + 1 : ℕ) : ℝ≥0))
      (g := fun n ω => max (2 * (J.coefficientAbsSumBound : ℝ)) 1 *
        FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          ((r + 1 : ℕ) : ℝ≥0) ω) ?_ ?_
    · intro n ω
      constructor
      · exact FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_nonneg
          _ _ _
      · have hError :
            (fun t ω => elementaryGain S
                (J.strategy.mul (H.representative n)) t ω -
              elementaryGain H.gain J.strategy t ω) =
              elementaryGain
                (fun t ω => elementaryGain S (H.representative n) t ω -
                  H.gain t ω) J.strategy :=
          elementaryGain_transform_error S (H.representative n) H.gain J.strategy
        rw [hError]
        exact cappedFiniteHorizonAbsoluteEnvelope_elementaryGain_le
          (fun t ω => elementaryGain S (H.representative n) t ω - H.gain t ω)
          (fun ω t =>
            (PredictableElementaryStrategy.rightContinuous_gain S hSRight
              (H.representative n) ω t).sub (H.gain_rightContinuous ω t))
          J.strategy J.coefficientAbsSumBound J.coefficientAbsSum_le
          ((r + 1 : ℕ) : ℝ≥0) ω
    · have hScaled := FTAPTheorem42.tendstoInMeasure_smul_const
        (max (2 * (J.coefficientAbsSumBound : ℝ)) 1)
        (H.gain_convergence r)
      simpa only [mul_zero] using hScaled
  isCauchy := by
    exact isCauchy_mul_right S hS
      J.toBoundedPredictableElementaryMultiplier H.representative H.isCauchy

end PredictableElementaryEmery

end FTAPTheorem42
