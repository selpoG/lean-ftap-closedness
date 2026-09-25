/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.RealizedR1EnvelopeSelection
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepMartingaleApproximation
import FTAPTheorem42.Stochastic.Topology.J1.WitnessExtension

/-! # Joint prelocal and boundary-jump control

The summable inner selection controls boundary jumps on the same sequence.
Combining this with the prelocal witnesses gives one original-source selection
and one equivalent measure for both costs. -/

namespace FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The finite prefix is controlled by bounded prices; the tail uses the
summable growing-horizon error. Stopping times may depend on the index. -/
theorem boundary_jump_tsum_ne_top_of_error_sum
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits S) (B : NNReal) (hB : ∀ᵐ w ∂μ, ∀ t, |S t w| ≤ B)
    (H : RealizedStrategy (ℱ := F) μ S) (f : Nat → Nat)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (elementaryGain S (H.representative (f k)) - H.gain)
        ((k + 1 : Nat) : NNReal) w) ∂μ) ≤ 1)
    (T : NNReal) (τ : Nat → Ω → NNReal) (hτ : ∀ k w, τ k w ≤ T) :
    (∑' k, ∫⁻ w, ENNReal.ofReal |processLeftJump
      (elementaryGain S (H.representative (f (k + 1))) -
        elementaryGain S (H.representative (f k))) (τ k w) w| ∂μ) ≠ ∞ := by
  let G := fun k => elementaryGain S (H.representative (f k))
  let E := fun k => G k - H.gain
  let a := fun k => FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
    (E k) ((k + 1 : Nat) : NNReal)
  let j := fun k => ∫⁻ w, ENNReal.ofReal |processLeftJump (G (k + 1) - G k) (τ k w) w| ∂μ
  let c := fun k => ∫⁻ w, ENNReal.ofReal (a k w) ∂μ
  have hNonneg : ∀ k w, 0 ≤ a k w := fun _ _ => Real.sqrt_nonneg _
  have hGL : ∀ k, ProcessHasLeftLimits (G k) := fun k =>
    ElementaryStrategy.gain_hasLeftLimits S hLeft (H.representative (f k)).toElementary
  have hER : ∀ k w t, ContinuousWithinAt (E k · w) (Ici t) t := fun k w t =>
    (PredictableElementaryStrategy.rightContinuous_gain S hRight
      (H.representative (f k)) w t).sub (H.gain_rightContinuous w t)
  have hEL : ∀ k, ProcessHasLeftLimits (E k) := fun k => (hGL k).sub H.gain_hasLeftLimits
  have hMeas : ∀ k, Measurable (fun w => ENNReal.ofReal (a k w)) := fun k =>
    ((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      ((PredictableElementaryStrategy.stronglyAdapted_gain S hS
        (H.representative (f k))).sub H.gain_stronglyAdapted) _).mono (F.le _)).measurable
      |>.ennreal_ofReal
  have hTail : ∀ k, Nat.ceil T ≤ k → j k ≤ 2 * (c (k + 1) + c k) := by
    intro k hk
    have hTk : T ≤ ((k + 1 : Nat) : NNReal) :=
      (Nat.le_ceil T).trans (by exact_mod_cast hk.trans (Nat.le_succ k))
    have hPoint : ∀ w, ENNReal.ofReal
        |processLeftJump (G (k + 1) - G k) (τ k w) w| ≤
        2 * (ENNReal.ofReal (a (k + 1) w) + ENNReal.ofReal (a k w)) := by
      intro w
      have hPath : ∀ t, t ≤ ((k + 1 : Nat) : NNReal) →
          |(G (k + 1) - G k) t w| ≤ a (k + 1) w + a k w := by
        intro t ht
        have hNext := FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
          (hER (k + 1)) (hEL (k + 1)) (((k + 1) + 1 : Nat) : NNReal) t
          (ht.trans (by exact_mod_cast Nat.le_succ (k + 1))) (ω := w)
        have hNow := FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
          (hER k) (hEL k) ((k + 1 : Nat) : NNReal) t ht (ω := w)
        have heq : (G (k + 1) - G k) t w = E (k + 1) t w - E k t w := by
          dsimp [E]; ring
        rw [heq]
        exact (abs_sub _ _).trans (add_le_add hNext hNow)
      have hj := abs_processLeftJump_le_two_mul_of_bound_upTo
        (G (k + 1) - G k) hPath ((hτ k w).trans hTk) ((hGL (k + 1)).sub (hGL k) w _)
      apply (ENNReal.ofReal_le_ofReal hj).trans_eq
      rw [ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_add (hNonneg (k + 1) w) (hNonneg k w)]
      norm_num
    calc
      j k ≤ ∫⁻ w, 2 * (ENNReal.ofReal (a (k + 1) w) + ENNReal.ofReal (a k w)) ∂μ :=
        lintegral_mono hPoint
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hMeas (k + 1))]
  have hFinite : ∀ k, j k ≠ ∞ := by
    intro k
    let C := fun n => 2 * (H.representativeBound (f n) : Real) * B
    have hG : ∀ᵐ w ∂μ, ∀ n t, |G n t w| ≤ C n := by
      filter_upwards [hB] with w hw
      intro n t
      have h := (H.representative (f n)).norm_gain_le_coefficientAbsSum_mul S t w B
        (fun s _ => by simpa only [Real.norm_eq_abs] using hw s)
      apply (show |G n t w| ≤ 2 * (H.representative (f n)).coefficientAbsSum w * B from h).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (H.representative_coefficientAbsSum_le _ _) (by norm_num))
        B.coe_nonneg
    have hJ : ∀ᵐ w ∂μ,
        |processLeftJump (G (k + 1) - G k) (τ k w) w| ≤ 2 * (C (k + 1) + C k) := by
      filter_upwards [hG] with w hw
      apply abs_processLeftJump_le_two_mul_of_bound_upTo (G (k + 1) - G k)
        (fun t _ => (abs_sub _ _).trans (add_le_add (hw _ t) (hw _ t))) (hτ k w)
        ((hGL (k + 1)).sub (hGL k) w _)
    apply ne_top_of_le_ne_top
      (show ENNReal.ofReal (2 * (C (k + 1) + C k)) ≠ ∞ from ENNReal.ofReal_ne_top)
    exact (lintegral_mono_ae (hJ.mono fun _ hw => ENNReal.ofReal_le_ofReal hw)).trans_eq (by simp)
  have hTailSum : (∑' k, j (k + Nat.ceil T)) ≤ 4 := by
    calc
      _ ≤ ∑' k, (2 * (c (k + Nat.ceil T + 1) + c (k + Nat.ceil T))) :=
        ENNReal.tsum_le_tsum fun k => hTail _ (Nat.le_add_left _ _)
      _ = 2 * ((∑' k, c (k + Nat.ceil T + 1)) + ∑' k, c (k + Nat.ceil T)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ 2 * (1 + 1) := mul_le_mul' le_rfl (add_le_add
        ((ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun k : Nat => k + Nat.ceil T + 1)
          (by intro i j hij; dsimp at hij; omega) c).trans hSum)
        ((ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun k : Nat => k + Nat.ceil T)
          (by intro i j hij; dsimp at hij; omega) c).trans hSum))
      _ = 4 := by norm_num
  change (∑' k, j k) ≠ ∞
  have hHas : HasSum (fun k => j (k + Nat.ceil T)) (∑' k, j (k + Nat.ceil T)) :=
    ENNReal.summable.hasSum
  rw [hHas.sum_range_add.tsum_eq]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr (fun k _ => hFinite k),
    ne_top_of_le_ne_top (by norm_num) hTailSum⟩

end FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

namespace FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- One original-source selection simultaneously controls prelocal costs and
closed-stop boundary jumps under one equivalent measure. The tilt and L2
error envelope remain available for the component-limit construction. -/
theorem exists_joint_prelocal_jump_localization
    (hUsual : Filtration.UsualConditions μ F)
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits S) (hGI : IsSemimartingale S F μ)
    (B : NNReal) (hB : ∀ᵐ w ∂μ, ∀ t, |S t w| ≤ B) (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (f : Nat → Nat) (Q : Measure Ω) (HQ : RealizedStrategy (ℱ := F) Q S)
        (τ : Nat → Ω → NNReal),
      StrictMono f ∧ IsProbabilityMeasure Q ∧ Q ≪ μ ∧ μ ≪ Q ∧
      Filtration.UsualConditions Q F ∧ IsSemimartingale S F Q ∧
      HQ.representative = H.representative ∧ HQ.gain = H.gain ∧
      IsLocalizingSequence F (fun r w => (τ r w : WithTop NNReal)) Q ∧
      (∀ r w, τ r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∃ η : Ω → Real, Measurable η ∧ (∀ w, 0 ≤ η w) ∧
      Q = CommonEnvelopeMeasure.tilted μ η ∧
      Q ≤ (CommonEnvelopeMeasure.normalizer μ η)⁻¹ • μ ∧ MemLp η 2 Q ∧
      (∀ ξ : Ω → Real, MemLp ξ 2 μ → MemLp (fun w => ξ w + η w) 2 Q) ∧
      (∀ᵐ w ∂Q, ∀ k,
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (elementaryGain S (HQ.representative (f k)) - HQ.gain)
          ((k + 1 : Nat) : NNReal) w ≤ η w) ∧
      (∑' k, ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (elementaryGain S (HQ.representative (f k)) - HQ.gain)
          ((k + 1 : Nat) : NNReal) w) ∂Q) ≤ 1 ∧
      ∀ r, ∃ R : ∀ k, EmeryPrelocalH1SupExactRepresentation (F := F) (mu := Q)
          (elementaryGain S (HQ.representative (f (k + 1))) -
            elementaryGain S (HQ.representative (f k))) (τ r) ((r + 1 : Nat) : NNReal),
        (∑' k, prelocalH1SupWitnessCost (R k).witness) ≤ 6 * (r + 5 : Nat) ∧
        (∑' k, prelocalH1SupWitnessCost (R k).witness) ≠ ∞ ∧
        (∑' k, ∫⁻ w, ENNReal.ofReal |processLeftJump
          (elementaryGain S (HQ.representative (f (k + 1))) -
            elementaryGain S (HQ.representative (f k))) (τ r w) w| ∂Q) ≠ ∞ ∧
        (∑' k, prelocalSemimartingaleJ1
          (elementaryGain S (HQ.representative (f (k + 1))) -
            elementaryGain S (HQ.representative (f k))) F Q
          (fun w => (τ r w : WithTop NNReal))) ≠ ∞ ∧
        ∃ hSF : SigmaFiniteFiltration Q F, letI := hSF
        ∃ V : ∀ k, LocalMartingaleQuadraticVariation
            (R k).witness.zeroInitialStoppedProcess F Q,
          (∑' k, ∫⁻ w, ENNReal.ofReal
            (Real.sqrt ((V k).variation ((r + 1 : Nat) : NNReal) w)) ∂Q) ≠ ∞ := by
  obtain ⟨f, Q, HQ, hf, hQ, hQμ, hμQ, hUsualQ, hSQ, hRep, hGain,
    η, hηMeas, hηPos, hTilt, hηL2, hDom, hSum, hError⟩ :=
    H.exists_summable_r1_and_error_envelope hUsual hS hRight hLeft hGI
  let : IsProbabilityMeasure Q := hQ
  let : F.IsRightContinuous := hUsualQ.rightContinuous
  let E := fun k => elementaryGain S (HQ.representative (f k)) - HQ.gain
  let Z := fun k => elementaryGain S (HQ.representative (f (k + 1))) -
    elementaryGain S (HQ.representative (f k))
  have hBound : (∑' k, semimartingaleR1 (Z k) F Q) ≤ 2 := by
    calc
      _ ≤ ∑' k, (semimartingaleR1 (E (k + 1)) F Q + semimartingaleR1 (E k) F Q) :=
        ENNReal.tsum_le_tsum fun k => by
          have heq : Z k = E (k + 1) - E k := by dsimp [Z, E]; abel
          rw [heq]
          exact semimartingaleR1_sub_le hUsualQ
      _ = (∑' k, semimartingaleR1 (E (k + 1)) F Q) +
          ∑' k, semimartingaleR1 (E k) F Q := ENNReal.tsum_add
      _ ≤ (1 : ENNReal) + 1 := add_le_add
        ((ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
          (fun k => semimartingaleR1 (E k) F Q)).trans hSum) hSum
      _ = 2 := by norm_num
  obtain ⟨τ, hLoc, hT, hRows⟩ := exists_common_summable_prelocalSupExactRepresentations_of_r1
    hUsualQ (ne_top_of_le_ne_top (by norm_num) hBound)
  refine ⟨f, Q, HQ, τ, hf, hQ, hQμ, hμQ, hUsualQ, hSQ, hRep, hGain, hLoc, hT,
    η, hηMeas, hηPos, hTilt, ?_, hηL2, ?_, hDom, hError, fun r => ?_⟩
  · rw [hTilt]
    exact CommonEnvelopeMeasure.tilted_le_smul hηPos
  · intro ξ hξ
    have hξQ : MemLp ξ 2 Q := by
      rw [hTilt]
      exact CommonEnvelopeMeasure.memLp_tilted hηMeas hηPos hξ
    exact hξQ.add hηL2
  · obtain ⟨R, hR, hFinite⟩ := hRows r
    refine ⟨R, hR.trans ?_, hFinite, ?_, ?_, ?_⟩
    · calc
        _ ≤ 6 * ((r + 1 : Nat) + (2 : ENNReal) + 2) :=
          mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl hBound) le_rfl)
        _ = 6 * (r + 5 : Nat) := by push_cast; congr 1; ring
    · exact HQ.boundary_jump_tsum_ne_top_of_error_sum hS hRight hLeft B (hQμ.ae_le hB) f hError
        ((r + 1 : Nat) : NNReal) (fun _ => τ r) (fun _ => hT r)
    · apply ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (a := (16 : ENNReal)) (by norm_num) hFinite)
      calc
        _ ≤ ∑' k, 16 * prelocalH1SupWitnessCost (R k).witness := by
          apply ENNReal.tsum_le_tsum
          intro k
          apply (R k).prelocalJ1_le_cost hUsualQ
          exact Eventually.of_forall (fun w => by
            simp [Z, elementaryGain, ElementaryStrategy.gain, ElementaryInterval.gain])
        _ = _ := ENNReal.tsum_mul_left
    · refine ⟨inferInstance, ?_⟩
      choose V hV using fun k => (R k).witness.exists_quadratic_root_le_cost hUsualQ
      refine ⟨V, ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (a := (14 : ENNReal)) (by norm_num) hFinite) ?_⟩
      calc
        _ ≤ ∑' k, 14 * prelocalH1SupWitnessCost (R k).witness :=
          ENNReal.tsum_le_tsum hV
        _ = _ := ENNReal.tsum_mul_left

end FTAPTheorem42.PredictableElementaryEmery.RealizedStrategy
