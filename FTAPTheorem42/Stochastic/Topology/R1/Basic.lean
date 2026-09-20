/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.CommonWitness

/-! # Selecting common-localization inputs from the zero-initial r1 infimum -/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

/-- Both coordinates use the same decomposition. Infinite costs are allowed. -/
noncomputable def J1Decomposition.r1Cost (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) : ENNReal :=
  boundedStoppingJumpCost D.N F mu +
    ∑' n : Nat, (2 : ENNReal)⁻¹ ^ (n + 1) *
      ∫⁻ w, min (D.clock Q (n : NNReal) w) 1 ∂mu

/-- The extended zero-initial core; no completeness or topology comparison is asserted here. -/
noncomputable def semimartingaleR1 (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) : ENNReal :=
  ⨅ (D : J1Decomposition X F mu) (Q : LocalMartingaleQuadraticVariation D.N F mu), D.r1Cost Q

theorem exists_summable_r1Cost_decompositions {Z : Nat → Process Ω}
    (hSum : (∑' k, semimartingaleR1 (Z k) F mu) ≠ ∞) :
    ∃ (D : ∀ k, J1Decomposition (Z k) F mu)
      (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu),
      (∑' k, (D k).r1Cost (Q k)) ≤ (∑' k, semimartingaleR1 (Z k) F mu) + 1 ∧
      (∑' k, (D k).r1Cost (Q k)) ≠ ∞ := by
  let e : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have he : ∀ k, 0 < e k := fun _ =>
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  have hSmall : ∀ k, semimartingaleR1 (Z k) F mu <
      semimartingaleR1 (Z k) F mu + e k := fun k =>
    ENNReal.lt_add_right (ne_top_of_le_ne_top hSum
      (ENNReal.le_tsum (f := fun k => semimartingaleR1 (Z k) F mu) k)) (he k).ne'
  have hChoice : ∀ k, ∃ (D : J1Decomposition (Z k) F mu)
      (Q : LocalMartingaleQuadraticVariation D.N F mu),
      D.r1Cost Q < semimartingaleR1 (Z k) F mu + e k := by
    intro k
    obtain ⟨D, hD⟩ := iInf_lt_iff.mp (hSmall k)
    obtain ⟨Q, hQ⟩ := iInf_lt_iff.mp hD
    exact ⟨D, Q, hQ⟩
  choose D Q hDQ using hChoice
  have heSum : (∑' k, e k) = 1 := by
    simp only [e]
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hBound : (∑' k, (D k).r1Cost (Q k)) ≤
      (∑' k, semimartingaleR1 (Z k) F mu) + 1 := by
    calc
      _ ≤ ∑' k, (semimartingaleR1 (Z k) F mu + e k) :=
        ENNReal.tsum_le_tsum (fun k => (hDQ k).le)
      _ = _ := by rw [ENNReal.tsum_add, heSum]
  exact ⟨D, Q, hBound,
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hSum, by norm_num⟩) hBound⟩

theorem J1Decomposition.capped_and_jump_summable_of_r1Cost
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hSum : (∑' k, (D k).r1Cost (Q k)) ≠ ∞) :
    (∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) ∧
      (∑' k, boundedStoppingJumpCost (D k).N F mu) ≠ ∞ := by
  constructor
  · intro n
    have hWeight : (2 : ENNReal)⁻¹ ^ (n + 1) ≠ 0 :=
      (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _).ne'
    have hWeighted : (2 : ENNReal)⁻¹ ^ (n + 1) *
        (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞ := by
      apply ne_top_of_le_ne_top hSum
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro k
      exact (ENNReal.le_tsum (f := fun n : Nat => (2 : ENNReal)⁻¹ ^ (n + 1) *
        ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) n).trans (le_add_left le_rfl)
    intro hTop
    rw [hTop, ENNReal.mul_top hWeight] at hWeighted
    exact hWeighted rfl
  · apply ne_top_of_le_ne_top hSum
    exact ENNReal.tsum_le_tsum (fun _ => le_add_right le_rfl)

open SIntegrableFiniteVariationBridge

theorem exists_common_summable_prelocalSupExactRepresentations_of_r1
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hSum : (∑' k, semimartingaleR1 (Z k) F mu) ≠ ∞) :
    ∃ tau : Nat → Ω → NNReal,
      IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
      (∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, ∃ R : ∀ k, EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu)
          (Z k) (tau r) ((r + 1 : Nat) : NNReal),
        (∑' k, prelocalH1SupWitnessCost (R k).witness) ≤
          6 * ((r + 1 : Nat) + (∑' k, semimartingaleR1 (Z k) F mu) + 2) ∧
        (∑' k, prelocalH1SupWitnessCost (R k).witness) ≠ ∞ := by
  obtain ⟨D, Q, hCost, hFinite⟩ := exists_summable_r1Cost_decompositions hSum
  obtain ⟨hCap, hJump⟩ := J1Decomposition.capped_and_jump_summable_of_r1Cost D Q hFinite
  obtain ⟨tau, hLoc, hT, hRows⟩ :=
    J1Decomposition.exists_common_summable_prelocalSupExactRepresentations hUsual D Q hCap hJump
  have hJumpBound : (∑' k, boundedStoppingJumpCost (D k).N F mu) ≤
      (∑' k, semimartingaleR1 (Z k) F mu) + 1 :=
    (ENNReal.tsum_le_tsum (fun _ => le_add_right le_rfl)).trans hCost
  refine ⟨tau, hLoc, hT, ?_⟩
  intro r
  obtain ⟨R, hR, hRFinite⟩ := (hRows r).2
  refine ⟨R, hR.trans ?_, hRFinite⟩
  have hAdd := add_le_add (add_le_add (le_rfl : ((r + 1 : Nat) : ENNReal) ≤ _) hJumpBound)
    (le_rfl : (1 : ENNReal) ≤ 1)
  have hMul := mul_le_mul (le_rfl : (6 : ENNReal) ≤ 6) hAdd bot_le bot_le
  simpa only [add_assoc, one_add_one_eq_two] using hMul

theorem exists_strictMono_summable_r1_of_tendsto_zero {Z : Nat → Process Ω}
    (hZero : Tendsto (fun k => semimartingaleR1 (Z k) F mu) atTop (𝓝 0)) :
    ∃ f : Nat → Nat, StrictMono f ∧ (∑' k, semimartingaleR1 (Z (f k)) F mu) ≤ 1 := by
  let e : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have hEventually : ∀ k, ∀ᶠ n in atTop, semimartingaleR1 (Z n) F mu < e k := by
    intro k
    exact hZero (Iio_mem_nhds
      (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _))
  obtain ⟨f, hf, hSmall⟩ := extraction_forall_of_eventually hEventually
  have hSum : (∑' k, semimartingaleR1 (Z (f k)) F mu) ≤ 1 := by
    calc
      _ ≤ ∑' k, e k := ENNReal.tsum_le_tsum (fun k => (hSmall k).le)
      _ = 1 := by
        simp only [e]
        rw [ENNReal.tsum_geometric_add_one]
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  exact ⟨f, hf, hSum⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## DDY gives finite r1 cost for every admissible decomposition -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.exists_bounded_r1Cost (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (E : J1Decomposition X F mu) (Q : LocalMartingaleQuadraticVariation E.N F mu),
      E.r1Cost Q ≤ 3 := by
  obtain ⟨B⟩ := HorizonFactorialGrid.exists_doleansDadeYenData
    D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN (show (0 : Real) < 1 by norm_num) hUsual
  let E : J1Decomposition X F mu := {
    N := B.L
    A := B.Q + D.A
    decomposition := by
      filter_upwards [D.decomposition] with w hw
      intro t
      have hN : D.N t w = B.L t w + B.Q t w := congrFun (congrFun B.decomposition t) w
      rw [hw t, hN]
      exact add_assoc _ _ _
    localMartingale := B.L_isLocalMartingale
    adaptedN := B.L_isStronglyAdapted
    rightN := B.L_rightContinuous
    leftN := B.L_leftLimits
    zeroN := B.L_zero
    adaptedA := B.Q_isStronglyAdapted.add D.adaptedA
    rightA := fun w t => (B.Q_rightContinuous w t).add (D.rightA w t)
    leftA := B.Q_leftLimits.add D.leftA
    variationA := fun w a b ha hb =>
      boundedVariationOn_add (B.Q_locallyBoundedVariation w a b ha hb) (D.variationA w a b ha hb)
    zeroA := by simp only [Pi.add_apply, B.Q_zero, D.zeroA, add_zero] }
  obtain ⟨Q, _⟩ := exists_unique_localMartingaleQuadraticVariation
    E.localMartingale E.adaptedN E.rightN E.leftN E.zeroN hUsual
  have hJump : boundedStoppingJumpCost E.N F mu ≤ 2 := by
    apply iSup_le
    intro T
    apply iSup_le
    intro tau
    apply iSup_le
    intro _
    apply iSup_le
    intro _
    calc
      _ ≤ ∫⁻ _ : Ω, (2 : ENNReal) ∂mu := by
        apply lintegral_mono_ae
        filter_upwards [B.L_jump_bound] with w hw
        simpa only [mul_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal (hw (tau w))
      _ = 2 := by simp
  have hInt (n : Nat) : (∫⁻ w, min (E.clock Q (n : NNReal) w) 1 ∂mu) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ : Ω, (1 : ENNReal) ∂mu := lintegral_mono (fun _ => min_le_right _ _)
      _ = 1 := by simp
  have hSeries : (∑' n : Nat, (2 : ENNReal)⁻¹ ^ (n + 1) *
      ∫⁻ w, min (E.clock Q (n : NNReal) w) 1 ∂mu) ≤ 1 := by
    calc
      _ ≤ ∑' n : Nat, (2 : ENNReal)⁻¹ ^ (n + 1) * 1 :=
        ENNReal.tsum_le_tsum (fun n => mul_le_mul le_rfl (hInt n) bot_le bot_le)
      _ = 1 := by
        simp only [mul_one]
        rw [ENNReal.tsum_geometric_add_one]
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  refine ⟨E, Q, (add_le_add hJump hSeries).trans_eq ?_⟩
  norm_num

theorem semimartingaleR1_le_three_of_decomposition (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F) : semimartingaleR1 X F mu ≤ 3 := by
  obtain ⟨E, Q, hCost⟩ := D.exists_bounded_r1Cost hUsual
  exact (iInf_le_of_le E (iInf_le _ Q)).trans hCost

theorem semimartingaleR1_ne_top_iff_decomposition (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleR1 X F mu ≠ ∞ ↔ Nonempty (J1Decomposition X F mu) := by
  constructor
  · intro hFinite
    obtain ⟨D, _⟩ := iInf_lt_iff.mp (lt_top_iff_ne_top.mpr hFinite)
    exact ⟨D⟩
  · rintro ⟨D⟩
    exact ne_top_of_le_ne_top (by norm_num) (semimartingaleR1_le_three_of_decomposition D hUsual)

end FTAPTheorem42
