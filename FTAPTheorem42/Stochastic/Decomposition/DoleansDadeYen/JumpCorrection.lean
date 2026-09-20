/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CorrectedNonnegative
import FTAPTheorem42.Stochastic.Process.SummableJumpCumulative

/-!
# Absolute convergence of the DDY jump correction

Both correction sums are indexed directly by times in `(0,T]`. This
establishes convergence and variation bounds, not their identification
with limits of quadratic sums along partitions.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- The same DDY components have absolutely convergent cross-jump and
square-jump sums on every finite horizon, on one common event. -/
theorem DoleansDadeYenData.jump_correction_summable
    (d : DoleansDadeYenData X F mu c) :
    ∀ᵐ omega ∂mu, ∀ T : NNReal,
      Summable (fun t : Ioc (0 : NNReal) T =>
        processLeftJump d.L t omega * processLeftJump d.Q t omega) ∧
      Summable (fun t : Ioc (0 : NNReal) T => (processLeftJump d.Q t omega) ^ 2) ∧
      (∑' t : Ioc (0 : NNReal) T,
        |processLeftJump d.L t omega * processLeftJump d.Q t omega|) ≤
          2 * c * variationOnFromTo (d.Q · omega) univ 0 T ∧
      (∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2) ≤
        (variationOnFromTo (d.Q · omega) univ 0 T) ^ 2 := by
  filter_upwards [d.L_jump_bound] with omega hL
  intro T
  obtain ⟨hAbs, hVar⟩ := summable_abs_processLeftJump_Ioc d.Q
    d.Q_locallyBoundedVariation d.Q_rightContinuous d.Q_leftLimits T omega
  let V := variationOnFromTo (d.Q · omega) univ 0 T
  have hV : 0 ≤ V := (tsum_nonneg (fun _ => abs_nonneg _)).trans hVar
  have hC : 0 ≤ 2 * c := (abs_nonneg _).trans (hL 0)
  have hPoint : ∀ t : Ioc (0 : NNReal) T, |processLeftJump d.Q t omega| ≤ V := by
    intro t
    exact (hAbs.le_tsum t (fun _ _ => abs_nonneg _)).trans hVar
  have hCross : ∀ t : Ioc (0 : NNReal) T,
      |processLeftJump d.L t omega * processLeftJump d.Q t omega| ≤
        (2 * c) * |processLeftJump d.Q t omega| := by
    intro t
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hL t) (abs_nonneg _)
  have hCrossSum := (hAbs.mul_left (2 * c)).of_nonneg_of_le (fun _ => abs_nonneg _) hCross
  have hSquare : ∀ t : Ioc (0 : NNReal) T,
      (processLeftJump d.Q t omega) ^ 2 ≤ V * |processLeftJump d.Q t omega| := by
    intro t
    nlinarith [mul_le_mul_of_nonneg_right (hPoint t) (abs_nonneg (processLeftJump d.Q t omega)),
      sq_abs (processLeftJump d.Q t omega)]
  have hSquareSum := (hAbs.mul_left V).of_nonneg_of_le (fun _ => sq_nonneg _) hSquare
  refine ⟨?_, hSquareSum, ?_, ?_⟩
  · exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using hCrossSum)
  · calc
      _ ≤ ∑' t : Ioc (0 : NNReal) T, (2 * c) * |processLeftJump d.Q t omega| :=
        Summable.tsum_le_tsum hCross hCrossSum (hAbs.mul_left (2 * c))
      _ = (2 * c) * ∑' t : Ioc (0 : NNReal) T, |processLeftJump d.Q t omega| := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hVar hC
  · calc
      _ ≤ ∑' t : Ioc (0 : NNReal) T, V * |processLeftJump d.Q t omega| :=
        Summable.tsum_le_tsum hSquare hSquareSum (hAbs.mul_left V)
      _ = V * ∑' t : Ioc (0 : NNReal) T, |processLeftJump d.Q t omega| := tsum_mul_left
      _ ≤ V * V := mul_le_mul_of_nonneg_left hVar hV
      _ = _ := (pow_two V).symm

/-- The convergent correction is the sum of the jump-square differences
of the original source and the same bounded-jump component. -/
theorem DoleansDadeYenData.jump_correction_identity
    (d : DoleansDadeYenData X F mu c) :
    ∀ᵐ omega ∂mu, ∀ T : NNReal,
      Summable (fun t : Ioc (0 : NNReal) T =>
        (processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2) ∧
      (∑' t : Ioc (0 : NNReal) T,
        ((processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2)) =
        2 * (∑' t : Ioc (0 : NNReal) T,
          processLeftJump d.L t omega * processLeftJump d.Q t omega) +
          ∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2 ∧
      |∑' t : Ioc (0 : NNReal) T,
        ((processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2)| ≤
        4 * c * variationOnFromTo (d.Q · omega) univ 0 T +
          (variationOnFromTo (d.Q · omega) univ 0 T) ^ 2 := by
  filter_upwards [d.jump_correction_summable] with omega hOmega
  intro T
  obtain ⟨hCross, hSquare, hCrossBound, hSquareBound⟩ := hOmega T
  have hEq : (fun t : Ioc (0 : NNReal) T =>
      (processLeftJump X t omega) ^ 2 - (processLeftJump d.L t omega) ^ 2) =
      fun t : Ioc (0 : NNReal) T =>
        2 * (processLeftJump d.L t omega * processLeftJump d.Q t omega) +
        (processLeftJump d.Q t omega) ^ 2 := by
    funext t
    have h := congrArg (fun Y => processLeftJump Y t omega) d.decomposition
    rw [processLeftJump_add d.L_leftLimits d.Q_leftLimits] at h
    rw [h]
    ring
  rw [hEq]
  have hSum := (hCross.mul_left 2).add hSquare
  have hValue := (hCross.mul_left 2).tsum_add hSquare
  rw [tsum_mul_left] at hValue
  refine ⟨hSum, hValue, ?_⟩
  rw [hValue]
  have hCrossAbs : |∑' t : Ioc (0 : NNReal) T,
      processLeftJump d.L t omega * processLeftJump d.Q t omega| ≤
      ∑' t : Ioc (0 : NNReal) T,
        |processLeftJump d.L t omega * processLeftJump d.Q t omega| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hCross.norm
  have hSquareNonneg : 0 ≤ ∑' t : Ioc (0 : NNReal) T,
      (processLeftJump d.Q t omega) ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  have hTriangle := abs_add_le
    (2 * ∑' t : Ioc (0 : NNReal) T,
      processLeftJump d.L t omega * processLeftJump d.Q t omega)
    (∑' t : Ioc (0 : NNReal) T, (processLeftJump d.Q t omega) ^ 2)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
    abs_of_nonneg hSquareNonneg] at hTriangle
  nlinarith

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Regularity of the same DDY-corrected quadratic candidate -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

theorem DoleansDadeYenData.quadraticCorrection_regular
    (d : DoleansDadeYenData X F mu c) :
    ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (d.quadraticCorrection · omega) (Ici t) t) ∧
      LocallyBoundedVariationOn (d.quadraticCorrection · omega) univ := by
  filter_upwards [d.jump_correction_summable] with omega hSum
  let a : NNReal → Real := fun s =>
    2 * (processLeftJump d.L s omega * processLeftJump d.Q s omega) +
      (processLeftJump d.Q s omega) ^ 2
  have ha : ∀ T, Summable (fun s : Ioc (0 : NNReal) T => a s) := fun T =>
    ((hSum T).1.mul_left 2).add (hSum T).2.1
  have hEq : (d.quadraticCorrection · omega) = fun t => ∑' s : Ioc (0 : NNReal) t, a s := by
    funext t
    dsimp only [quadraticCorrection, a]
    rw [((hSum t).1.mul_left 2).tsum_add (hSum t).2.1, tsum_mul_left]
  rw [hEq]
  exact ⟨SummableJumpCumulative.rightContinuous_Ioc a ha,
    SummableJumpCumulative.locallyBoundedVariation_Ioc a ha⟩

/-- Adaptedness follows from the exact original grid limit, so it does not
require a measurable enumeration of jump times. -/
theorem DoleansDadeYenData.quadraticCorrection_stronglyAdapted
    (d : DoleansDadeYenData X F mu c) : StronglyAdapted F d.quadraticCorrection := by
  have hX : StronglyAdapted F X := by
    rw [d.decomposition]
    exact d.L_isStronglyAdapted.add d.Q_isStronglyAdapted
  have hGrid : ∀ {Y : Process Ω}, StronglyAdapted F Y →
      ∀ {n} (G : ChronologicalGrid NNReal n) t,
        StronglyMeasurable[F t] (G.squaredIncrementProcess Y t) := by
    intro Y hY n G t
    unfold ChronologicalGrid.squaredIncrementProcess
    apply Finset.stronglyMeasurable_fun_sum
    intro k _
    have hNext : StronglyMeasurable[F t] (Y (min t (G.sampledTime (k + 1)))) :=
      (hY (min t (G.sampledTime (k + 1)))).mono (F.mono (min_le_left _ _))
    have hCurrent : StronglyMeasurable[F t] (Y (min t (G.sampledTime k))) :=
      (hY (min t (G.sampledTime k))).mono (F.mono (min_le_left _ _))
    exact (hNext.sub hCurrent).pow 2
  intro t
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun r omega =>
      (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess X t omega -
      (FactorialChronologicalGrid.grid (r + 1)).squaredIncrementProcess d.L t omega) ?_ ?_
  · exact fun r => (hGrid hX _ t).sub (hGrid d.L_isStronglyAdapted _ t)
  · rw [tendsto_pi_nhds]
    exact fun omega => d.finiteGrid_correction_tendsto_jumpSum t omega

/-- The existing glued process plus the exact correction is adapted and
has right-continuous locally bounded-variation paths on one common event. -/
theorem DoleansDadeYenData.corrected_regular
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C) :
    StronglyAdapted F (fun t omega => QC.variation t omega + d.quadraticCorrection t omega) ∧
      ∀ᵐ omega ∂mu,
        (∀ t, ContinuousWithinAt
          (fun s => QC.variation s omega + d.quadraticCorrection s omega) (Ici t) t) ∧
        LocallyBoundedVariationOn
          (fun s => QC.variation s omega + d.quadraticCorrection s omega) univ := by
  refine ⟨QC.variation_isStronglyAdapted.add d.quadraticCorrection_stronglyAdapted, ?_⟩
  filter_upwards [d.quadraticCorrection_regular] with omega hReg
  refine ⟨fun t => (QC.variation_rightContinuous omega t).add (hReg.1 t), ?_⟩
  intro s t hs ht
  exact boundedVariationOn_add (QC.variation_locallyBoundedVariation omega s t hs ht)
    (hReg.2 s t hs ht)

end FTAPTheorem42
