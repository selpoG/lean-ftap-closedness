/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.Witness
import FTAPTheorem42.Stochastic.Topology.Prelocal.BoundaryFixedSourceConsumer
import FTAPTheorem42.Stochastic.Topology.J1.WitnessExtension

/-! # Transferring j1 control to the finite-variation part of an actual integral -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X S : Process Ω} {T : NNReal}

omit [MeasurableSpace Ω] in
private theorem strictPrefix_after_constant
    (hConst : ∀ w t, T ≤ t → X t w = X T w) :
    strictPrefixProcess X (fun _ => T + 1) = X := by
  funext t w
  by_cases ht : t < T + 1
  · exact strictPrefixProcess_eq_of_lt X _ ht
  · have hTU : T < T + 1 := lt_add_one T
    have hU : 0 < T + 1 := (show (0 : NNReal) ≤ T from bot_le).trans_lt hTU
    let : NeBot (𝓝[<] (T + 1)) := nhdsLT_neBot_of_exists_lt ⟨0, hU⟩
    rw [strictPrefixProcess_eq_of_ge X _ (le_of_not_gt ht),
      hConst w t (hTU.le.trans (le_of_not_gt ht))]
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_gt_nhds hTU).filter_mono nhdsWithin_le_nhds] with s hs
    exact (hConst w s hs.le).symm

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {D0 : SpecialSemimartingaleDecomposition S F mu}
  {R : SIntegrableRealizationModel D0}

theorem ActualSIntegrableStrategy.expected_variation_le_j1_of_constant_after
    (H : ActualSIntegrableStrategy R) (hUsual : Filtration.UsualConditions mu F)
    (hIntegral : ProcessIndistinguishable mu X H.val.stochasticIntegral)
    (hConst : ∀ w t, T ≤ t → X t w = X T w) :
    (∫⁻ w, eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) ∂mu) ≤
      12 * semimartingaleJ1 X F mu := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  change _ ≤ 12 * ⨅ D : J1Decomposition X F mu, D.cost
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (12 : ENNReal) ≠ 0)
    (by norm_num : (12 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro D
  by_cases hFinite : D.cost = ∞
  · simp [hFinite]
  obtain ⟨W, hW⟩ := D.exists_prelocalSupExactRepresentation hUsual
    (isStoppingTime_const F (T + 1)) (fun _ => le_rfl)
    (Eventually.of_forall (fun _ _ _ => rfl)) hFinite
  have hPos : (0 : NNReal) < T + 1 := bot_le.trans_lt (lt_add_one T)
  have hTarget : strictPrefixProcess W.exactTarget (fun _ => T + 1) =
      strictPrefixProcess (fun t w => W.witness.N t w + W.witness.A t w) (fun _ => T + 1) := by
    funext t w
    exact (strictPrefixProcess_eq_of_agree_before
      (W.witness.martingale_hasLeftLimits.add W.witness.finiteVariation_hasLeftLimits) w
      (W.witness.agrees_on_strict_prefix 0 w hPos)
      (fun s hs => W.witness.agrees_on_strict_prefix s w hs) t).symm
  have hStrict : ProcessIndistinguishable mu
      (strictPrefixProcess W.exactTarget (fun _ => T + 1)) X := by
    filter_upwards [W.exactTarget_indistinguishable] with w hw
    intro t
    have hEq : strictPrefixProcess W.exactTarget (fun _ => T + 1) t w =
        strictPrefixProcess X (fun _ => T + 1) t w := by
      by_cases ht : t < T + 1
      · rw [strictPrefixProcess_eq_of_lt W.exactTarget (fun _ => T + 1) ht,
          strictPrefixProcess_eq_of_lt X (fun _ => T + 1) ht, hw t]
      · rw [strictPrefixProcess_eq_of_ge W.exactTarget (fun _ => T + 1) (le_of_not_gt ht),
          strictPrefixProcess_eq_of_ge X (fun _ => T + 1) (le_of_not_gt ht)]
        exact congrArg (fun f => Function.leftLim f (T + 1)) (funext hw)
    rw [hEq, strictPrefix_after_constant hConst]
  obtain ⟨B, hBA, _⟩ := exists_fixedSource_centeredBoundaryComponentAgreement
    D0 W.witness H.val hUsual hTarget
    (hStrict.trans (hIntegral.trans H.val.integral_decomposition))
  have hVar : (∫⁻ w, eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) ∂mu) ≤
      ∫⁻ w, eVariationOn (B.A · w) (Icc 0 (T + 1)) ∂mu := by
    apply lintegral_mono_ae
    filter_upwards [hBA] with w hw
    have hEq : eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) =
        eVariationOn (B.A · w) (Icc 0 T) := by
      rw [← pathVariation_sub_const _ (H.val.finiteVariationPart 0 w),
        ← pathVariation_sub_const (B.A · w) (B.A 0 w)]
      exact eVariationOn.congr (fun t _ => (hw t).symm)
    rw [hEq]
    exact eVariationOn.mono _ (Icc_subset_Icc_right (le_add_of_nonneg_right zero_le_one))
  apply hVar.trans (B.A_expected_variation_le.trans _)
  calc
    _ ≤ 2 * prelocalH1SupWitnessCost W.witness := by
      unfold prelocalH1SupWitnessCost
      calc
        _ ≤ 2 * prelocalH1SupWitnessVariationCost W.witness +
            2 * prelocalH1SupWitnessMartingaleCost W.witness :=
          add_le_add (le_mul_of_one_le_left' (by norm_num)) le_rfl
        _ = _ := by rw [mul_add]; ac_rfl
    _ ≤ 2 * (6 * D.cost) := mul_le_mul le_rfl hW bot_le bot_le
    _ = 12 * D.cost := by rw [← mul_assoc]; norm_num

theorem ActualSIntegrableStrategy.centered_component_cost_le_j1_of_constant_after
    (H : ActualSIntegrableStrategy R) (hUsual : Filtration.UsualConditions mu F)
    (hIntegral : ProcessIndistinguishable mu X H.val.stochasticIntegral)
    (hConst : ∀ w t, T ≤ t → X t w = X T w) (hZero : X 0 = 0) :
    (∫⁻ w, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |H.val.centeredMartingalePart t.1 w| ∂mu) +
      (∫⁻ w, eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) ∂mu) ≤
        30 * semimartingaleJ1 X F mu := by
  have hPoint : ∀ᵐ w ∂mu, (⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |H.val.centeredMartingalePart t.1 w|) ≤
      (⨆ t : NNReal, ENNReal.ofReal |X t w|) +
        eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) := by
    filter_upwards [hIntegral.trans H.val.integral_decomposition] with w hw
    apply iSup_le
    intro t
    have hCentered : H.val.centeredMartingalePart t.1 w =
        X t.1 w - (H.val.finiteVariationPart t.1 w - H.val.finiteVariationPart 0 w) := by
      have ht := hw t.1
      have hz := hw 0
      rw [hZero] at hz
      dsimp only [SIntegrableStrategy.centeredMartingalePart, Pi.zero_apply] at hz ⊢
      linarith
    have hVar : ENNReal.ofReal
        |H.val.finiteVariationPart t.1 w - H.val.finiteVariationPart 0 w| ≤
        eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) := by
      simpa only [edist_dist, Real.dist_eq] using
        eVariationOn.edist_le (H.val.finiteVariationPart · w) t.2
          (show (0 : NNReal) ∈ Icc 0 T from ⟨le_rfl, bot_le⟩)
    rw [hCentered]
    exact (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans
      ((le_of_eq (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))).trans
        (add_le_add (le_iSup (fun s : NNReal => ENNReal.ofReal |X s w|) t.1) hVar))
  have hMeas := measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
    H.val.finiteVariationPart_isPredictable.stronglyAdapted
    H.val.finiteVariationPart_isRightContinuous (T := T)
  have hMax := lintegral_mono_ae hPoint
  rw [lintegral_add_right _ hMeas] at hMax
  have hV := H.expected_variation_le_j1_of_constant_after hUsual hIntegral hConst
  calc
    _ ≤ ((∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |X t w| ∂mu) +
        ∫⁻ w, eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) ∂mu) +
        ∫⁻ w, eVariationOn (H.val.finiteVariationPart · w) (Icc 0 T) ∂mu :=
      add_le_add hMax le_rfl
    _ ≤ (6 * semimartingaleJ1 X F mu + 12 * semimartingaleJ1 X F mu) +
        12 * semimartingaleJ1 X F mu :=
      add_le_add (add_le_add (lintegral_maximal_le_six_semimartingaleJ1 hUsual) hV) hV
    _ = _ := by rw [← add_mul, ← add_mul]; norm_num

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Consuming prelocal witnesses in actual closed-stop component estimates -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {S : Process Ω} {D : SpecialSemimartingaleDecomposition S F mu}
  {R : SIntegrableRealizationModel D}

/-- An independently constructed actual closed-stop graph suffices for the
component estimate; no operation on arbitrary raw strategies is required. -/
theorem ActualSIntegrableStrategy.centered_component_cost_le_witness_of_stopped
    (H : ActualSIntegrableStrategy R) (hUsual : Filtration.UsualConditions mu F)
    {X : Process Ω} (hZero : X 0 = 0) (hAdapted : StronglyAdapted F X)
    (hRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) {tau : Ω → NNReal} {T : NNReal}
    (W : EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu) X tau T)
    (hIntegral : ProcessIndistinguishable mu
      (stoppedProcess X (fun ω => (tau ω : WithTop NNReal))) H.val.stochasticIntegral) :
    (∫⁻ ω, ⨆ t : Icc (0 : NNReal) T,
      ENNReal.ofReal |H.val.centeredMartingalePart t.1 ω| ∂mu) +
      (∫⁻ ω, eVariationOn (H.val.finiteVariationPart · ω) (Icc 0 T) ∂mu) ≤
      30 * (32 * prelocalH1SupWitnessCost W.witness +
        ∫⁻ ω, ENNReal.ofReal |processLeftJump X (tau ω) ω| ∂mu) := by
  have hConst : ∀ ω t, T ≤ t →
      stoppedProcess X (fun ω => (tau ω : WithTop NNReal)) t ω =
        stoppedProcess X (fun ω => (tau ω : WithTop NNReal)) T ω := by
    intro ω t ht
    rw [stoppedProcess_eq_of_ge X tau
      ((W.witness.stoppingTime_le_horizon ω).trans ht),
      stoppedProcess_eq_of_ge X tau (W.witness.stoppingTime_le_horizon ω)]
  have hStoppedZero : stoppedProcess X (fun ω => (tau ω : WithTop NNReal)) 0 = 0 := by
    funext ω
    rw [stoppedProcess_eq_of_le (u := X) (τ := fun ω => (tau ω : WithTop NNReal))
      (show ((0 : NNReal) : WithTop NNReal) ≤ (tau ω : WithTop NNReal) from bot_le)]
    exact congrFun hZero ω
  apply (H.centered_component_cost_le_j1_of_constant_after
    hUsual hIntegral hConst hStoppedZero).trans
  apply mul_le_mul' le_rfl
  apply (semimartingaleJ1_stopped_le_two_mul_prelocal_add_jump hUsual hZero
    hAdapted hRight hLeft W.witness.stoppingTime W.witness.stoppingTime_le_horizon).trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ 2 * (16 * prelocalH1SupWitnessCost W.witness) := mul_le_mul' le_rfl
      (W.prelocalJ1_le_cost hUsual (Eventually.of_forall (fun ω => congrFun hZero ω)))
    _ = _ := by rw [← mul_assoc]; norm_num

end FTAPTheorem42
