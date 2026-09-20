/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Davis.LocalMartingaleReverseDavis
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticBoundaryRoot

/-!
# A prelocal-witness endpoint for the supplied quadratic schedule route

The bounded-jump schedule provider is now consumed directly by the main
prelocal `H¹` witness.  After zero-initial normalization and stopping, an
explicit horizon-wise left-jump bound produces a canonical countable schedule;
the supplied schedule is then glued into a global optional quadratic
variation, and the root/cost and one-sided Davis consumers are attached to
the same choices.

This is a specialized acceptance endpoint.  It does not provide a schedule
for an arbitrary local martingale, and it does not add the exact `j¹` or
auxiliary `r¹` construction.
-/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open SIntegrableProcessStoppingCalculus
open LocalMartingaleQuadratic

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The stopped source and its endpoint package -/

/-- The zero-initial stopped martingale carried by a prelocal witness. -/
noncomputable def EmeryPrelocalH1SupWitness.zeroInitialStoppedProcess
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SigmaFiniteFiltration mu F]
    {X : Process Omega} {tau : Omega → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) : Process Omega :=
  MeasureTheory.stoppedProcess w.zeroInitial.N
    (fun omega => (tau omega : WithTop NNReal))

end SIntegrableFiniteVariationBridge

end FTAPTheorem42

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## Reverse Davis control for normalized prelocal witnesses -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}

/-- General quadratic control of the normalized stopped martingale. No
bounded-jump assumption or supplied quadratic schedule is needed. -/
theorem EmeryPrelocalH1SupWitness.exists_quadratic_root_le_cost
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ Q : LocalMartingaleQuadraticVariation w.zeroInitialStoppedProcess F mu,
      (∫⁻ ω, ENNReal.ofReal (Real.sqrt (Q.variation T ω)) ∂mu) ≤
        14 * prelocalH1SupWitnessCost w := by
  let M := w.zeroInitialStoppedProcess
  have hM : LocalMartingale M F mu :=
    w.zeroInitial.martingale_isLocalMartingale.stoppedProcess_of_zero_of_rightContinuous
      w.zeroInitial_martingalePart_zero w.zeroInitial.martingale_isRightContinuous w.stoppingTime
  have hA : StronglyAdapted F M :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      w.zeroInitial.martingale_isStronglyAdapted w.stoppingTime
      w.zeroInitial.martingale_isRightContinuous
  have hR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      w.zeroInitial.N w.zeroInitial.martingale_isRightContinuous
  have hL : ProcessHasLeftLimits M :=
    w.zeroInitial.martingale_hasLeftLimits.stoppedProcess _
  have hZ : M 0 = 0 := by
    funext ω
    change stoppedProcess w.zeroInitial.N _ 0 ω = 0
    rw [stoppedProcess_eq_of_le bot_le]
    exact congrFun w.zeroInitial_martingalePart_zero ω
  obtain ⟨Q, _⟩ := exists_unique_localMartingaleQuadraticVariation hM hA hR hL hZ hUsual
  refine ⟨Q, (Q.lintegral_root_le_seven_maximal hM hA hR hL hZ hUsual T).trans ?_⟩
  have hEq : (∫⁻ ω, ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T ω) ∂mu) =
      prelocalH1SupWitnessMartingaleCost w.zeroInitial := by
    unfold prelocalH1SupWitnessMartingaleCost prelocalH1SupMartingaleRunningSupExpectation
    rw [eLpNorm_one_eq_lintegral_enorm
      w.zeroInitial.martingale_envelope_stronglyMeasurable.aestronglyMeasurable]
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal_abs]
    change ENNReal.ofReal (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T ω) =
      ENNReal.ofReal |FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T ω|
    rw [abs_of_nonneg (show 0 ≤ FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T ω
      from Real.sqrt_nonneg _)]
  rw [hEq]
  calc
    _ ≤ 7 * (2 * prelocalH1SupWitnessCost w) := mul_le_mul' le_rfl
      ((le_add_right le_rfl).trans (prelocalH1SupWitnessCost_zeroInitial_le_two_mul w))
    _ = _ := by rw [← mul_assoc]; norm_num

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## The centered strict-prefix finite-variation series at a common stopping stage -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}

/-- Centering removes the initial constant that variation does not control. -/
noncomputable def EmeryPrelocalH1SupWitness.centeredStrictPrefixA
    (W : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) : Process Ω :=
  fun t w => strictPrefixProcess W.A tau t w - strictPrefixProcess W.A tau 0 w

theorem EmeryPrelocalH1SupWitness.centeredStrictPrefixA_variation_le
    (W : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) (w : Ω) :
    eVariationOn (W.centeredStrictPrefixA · w) univ ≤
      eVariationOn (strictPrefixProcess W.A tau · w) (Icc 0 T) := by
  let P : NNReal → Real := fun t => strictPrefixProcess W.A tau t w
  have hCenter : eVariationOn (W.centeredStrictPrefixA · w) univ = eVariationOn P univ := by
    simp only [EmeryPrelocalH1SupWitness.centeredStrictPrefixA, P, eVariationOn, edist_sub_right]
  rw [hCenter]
  have hClip : P = P ∘ (fun t => min t T) := by
    funext t
    change P t = P (min t T)
    by_cases ht : t ≤ T
    · simp only [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht)]
      exact strictPrefixProcess_constant_after W.A tau (W.stoppingTime_le_horizon w)
        (le_of_not_ge ht)
  calc
    _ = eVariationOn (P ∘ (fun t => min t T)) univ := congrArg (eVariationOn · univ) hClip
    _ ≤ eVariationOn P (Icc 0 T) := eVariationOn.comp_le_of_monotoneOn P (fun t => min t T)
      ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ)
      (fun _ _ => ⟨bot_le, min_le_right _ _⟩)

end FTAPTheorem42.SIntegrableFiniteVariationBridge

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

/-! ## Extending prelocal witnesses to genuine J1 decompositions -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}

theorem EmeryPrelocalH1SupWitness.remainder_variation_le_cost
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (∫⁻ ω, eVariationOn (strictPrefixBoundaryRemainder w.N w.A tau · ω) univ ∂mu) ≤
      2 * prelocalH1SupWitnessCost w := by
  have hPoint (ω : Ω) :
      eVariationOn (strictPrefixBoundaryRemainder w.N w.A tau · ω) univ ≤
        eVariationOn (strictPrefixProcess w.A tau · ω) (Icc 0 T) +
          ENNReal.ofReal |boundaryJumpProcess w.N tau T ω| := by
    have hEq : (strictPrefixBoundaryRemainder w.N w.A tau · ω) =
        fun t => w.centeredStrictPrefixA t ω + -boundaryJumpProcess w.N tau t ω := by
      funext t
      simp only [strictPrefixBoundaryRemainder, EmeryPrelocalH1SupWitness.centeredStrictPrefixA,
        strictPrefixProcess_zero]
      ring
    rw [hEq]
    apply (eVariationOn_add_le_real _ _ _).trans
    have hNeg : eVariationOn (fun t => -boundaryJumpProcess w.N tau t ω) univ =
        eVariationOn (boundaryJumpProcess w.N tau · ω) univ := by
      simp only [eVariationOn, edist_neg_neg]
    rw [hNeg]
    exact add_le_add (w.centeredStrictPrefixA_variation_le ω)
      ((boundaryJumpProcess_eVariationOn_univ_le tau w.stoppingTime_le_horizon ω).trans_eq
        (by rw [boundaryJumpProcess_at_horizon_eq_processLeftJump w.stoppingTime_le_horizon]))
  calc
    _ ≤ ∫⁻ ω, eVariationOn (strictPrefixProcess w.A tau · ω) (Icc 0 T) +
        ENNReal.ofReal |boundaryJumpProcess w.N tau T ω| ∂mu := lintegral_mono hPoint
    _ = (∫⁻ ω, eVariationOn (strictPrefixProcess w.A tau · ω) (Icc 0 T) ∂mu) +
        ∫⁻ ω, ENNReal.ofReal |boundaryJumpProcess w.N tau T ω| ∂mu :=
      lintegral_add_left w.finiteVariation_measurable _
    _ ≤ prelocalH1SupWitnessVariationCost w + 2 * prelocalH1SupWitnessMartingaleCost w :=
      add_le_add le_rfl (boundaryJumpProcess_expected_abs_le_two_martingaleCost w)
    _ ≤ 2 * prelocalH1SupWitnessCost w := by
      unfold prelocalH1SupWitnessCost
      rw [mul_add]
      exact (add_le_add (le_mul_of_one_le_left' (by norm_num)) le_rfl).trans_eq (add_comm _ _)

/-- The strict-prefix proxy controls the genuine prelocal J1 infimum.
At a zero stopping time no initial agreement is required. -/
theorem EmeryPrelocalH1SupWitness.prelocalJ1_le_cost
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T)
    (hUsual : Filtration.UsualConditions mu F) (hZero : ∀ᵐ ω ∂mu, X 0 ω = 0) :
    prelocalSemimartingaleJ1 X F mu (fun ω => (tau ω : WithTop NNReal)) ≤
      16 * prelocalH1SupWitnessCost w := by
  let M := w.zeroInitialStoppedProcess
  let A := strictPrefixBoundaryRemainder w.N w.A tau
  let N := stoppedProcess M (fun _ => (T : WithTop NNReal))
  let Y : Process Ω := fun t ω => N t ω + A t ω
  have hMA : StronglyAdapted F M :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      w.zeroInitial.martingale_isStronglyAdapted w.stoppingTime
      w.zeroInitial.martingale_isRightContinuous
  have hMR : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      w.zeroInitial.N w.zeroInitial.martingale_isRightContinuous
  have hML : ProcessHasLeftLimits M := w.zeroInitial.martingale_hasLeftLimits.stoppedProcess _
  have hMZ : M 0 = 0 := by
    funext ω
    change stoppedProcess w.zeroInitial.N _ 0 ω = 0
    rw [stoppedProcess_eq_of_le bot_le]
    exact congrFun w.zeroInitial_martingalePart_zero ω
  have hMM : LocalMartingale M F mu :=
    w.zeroInitial.martingale_isLocalMartingale.stoppedProcess_of_zero_of_rightContinuous
      w.zeroInitial_martingalePart_zero w.zeroInitial.martingale_isRightContinuous w.stoppingTime
  let D : J1Decomposition Y F mu := {
    N := N
    A := A
    decomposition := Eventually.of_forall (fun _ _ => rfl)
    localMartingale := hMM.stoppedProcess_of_zero_of_rightContinuous hMZ hMR
      (isStoppingTime_const F T)
    adaptedN := RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hMA (isStoppingTime_const F T) hMR
    rightN := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hMR
    leftN := hML.stoppedProcess _
    zeroN := by
      funext ω
      change stoppedProcess M _ 0 ω = 0
      rw [stoppedProcess_eq_of_le bot_le]
      exact congrFun hMZ ω
    adaptedA := strictPrefixBoundaryRemainder_stronglyAdapted
      w.martingale_isStronglyAdapted w.martingale_isRightContinuous w.martingale_hasLeftLimits
      w.finiteVariation_isStronglyAdapted w.finiteVariation_isRightContinuous
      w.finiteVariation_hasLeftLimits w.stoppingTime
    rightA := strictPrefixBoundaryRemainder_rightContinuous w.finiteVariation_isRightContinuous
    leftA := strictPrefixBoundaryRemainder_hasLeftLimits w.finiteVariation_hasLeftLimits
    variationA := fun ω =>
      (strictPrefixBoundaryRemainder_boundedVariation (N := w.N) (tau := tau)
        w.finiteVariation_isBoundedVariation ω).locallyBoundedVariationOn
    zeroA := strictPrefixBoundaryRemainder_zero _ _ _ }
  have hPrefix : ∀ᵐ ω ∂mu, ∀ t : NNReal,
      (t : WithTop NNReal) < (tau ω : WithTop NNReal) → Y t ω = X t ω := by
    filter_upwards [hZero] with ω hz
    intro t ht
    have ht' : t < tau ω := WithTop.coe_lt_coe.mp ht
    have h0 := w.agrees_on_strict_prefix 0 ω (bot_le.trans_lt ht')
    have h := w.agrees_on_strict_prefix t ω ht'
    have hT : t ≤ T := ht'.le.trans (w.stoppingTime_le_horizon ω)
    change stoppedProcess M (fun _ => (T : WithTop NNReal)) t ω + A t ω = X t ω
    rw [stoppedProcess_const_apply, min_eq_left hT]
    change stoppedProcess w.zeroInitial.N (fun ω => (tau ω : WithTop NNReal)) t ω +
      strictPrefixBoundaryRemainder w.N w.A tau t ω = X t ω
    rw [stoppedProcess_eq_of_le (u := w.zeroInitial.N)
      (τ := fun ω => (tau ω : WithTop NNReal)) (ω := ω) (WithTop.coe_le_coe.mpr ht'.le)]
    rw [w.zeroInitial_N]
    simp only [strictPrefixBoundaryRemainder, strictPrefixProcess_eq_of_lt _ _ ht',
      boundaryJumpProcess, postStopSampled]
    simp only [not_le.mpr ht', ↓reduceIte]
    linarith
  apply iInf_le_of_le Y
  apply iInf_le_of_le hPrefix
  apply (iInf_le _ D).trans
  obtain ⟨Q, hQ⟩ := w.exists_quadratic_root_le_cost hUsual
  rw [D.cost_eq hUsual (Q.stopped hMR hML hMZ (isStoppingTime_const F T))]
  have hRoot : (∫⁻ ω, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt
      ((Q.stopped hMR hML hMZ (isStoppingTime_const F T)).variation t ω)) ∂mu) =
      ∫⁻ ω, ENNReal.ofReal (Real.sqrt (Q.variation T ω)) ∂mu := by
    apply lintegral_congr
    exact Q.stopped_allTimeRoot_eq hMR hML hMZ (isStoppingTime_const F T)
  rw [hRoot]
  exact (add_le_add hQ w.remainder_variation_le_cost).trans_eq (by rw [← add_mul]; norm_num)

theorem EmeryPrelocalH1SupExactRepresentation.prelocalJ1_le_cost
    (R : EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu) X tau T)
    (hUsual : Filtration.UsualConditions mu F) (hZero : ∀ᵐ ω ∂mu, X 0 ω = 0) :
    prelocalSemimartingaleJ1 X F mu (fun ω => (tau ω : WithTop NNReal)) ≤
      16 * prelocalH1SupWitnessCost R.witness := by
  have hCompare : prelocalSemimartingaleJ1 X F mu (fun ω => (tau ω : WithTop NNReal)) ≤
      prelocalSemimartingaleJ1 R.exactTarget F mu (fun ω => (tau ω : WithTop NNReal)) := by
    unfold prelocalSemimartingaleJ1
    apply le_iInf
    intro Y
    apply le_iInf
    intro hY
    apply iInf_le_of_le Y
    apply iInf_le_of_le ?_ le_rfl
    filter_upwards [hY, R.exactTarget_indistinguishable] with ω hy hr
    exact fun t ht => (hy t ht).trans (hr t)
  apply hCompare.trans (R.witness.prelocalJ1_le_cost hUsual ?_)
  filter_upwards [hZero, R.exactTarget_indistinguishable] with ω hz hr
  exact (hr 0).trans hz

end FTAPTheorem42.SIntegrableFiniteVariationBridge
