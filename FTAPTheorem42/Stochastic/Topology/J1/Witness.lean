/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.Stopping
import FTAPTheorem42.Stochastic.Topology.Prelocal.Representation

/-! # Producing existing running-supremum witnesses from finite j1 cost -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

open SIntegrableFiniteVariationBridge RightContinuousStoppedMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X Y : Process Ω} {tau : Ω → NNReal} {T : NNReal}

theorem J1Decomposition.exists_prelocalSupExactRepresentation
    (D : J1Decomposition Y F mu) (hUsual : Filtration.UsualConditions mu F)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T)
    (hPrefix : ∀ᵐ w ∂mu, ∀ t : NNReal, t < tau w → Y t w = X t w)
    (hFinite : D.cost ≠ ∞) :
    ∃ R : EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu) X tau T,
      prelocalH1SupWitnessCost R.witness ≤ 6 * D.cost := by
  classical
  obtain ⟨Q, _⟩ := exists_unique_localMartingaleQuadraticVariation
    D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN hUsual
  let a := ∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu
  let b := ∫⁻ w, eVariationOn (D.A · w) univ ∂mu
  have hCost : D.cost = a + b := D.cost_eq hUsual Q
  have ha : a ≠ ∞ := (ENNReal.add_ne_top.mp (hCost ▸ hFinite)).1
  have hb : b ≠ ∞ := (ENNReal.add_ne_top.mp (hCost ▸ hFinite)).2
  let M := stoppedProcess D.N (fun w => (tau w : WithTop NNReal))
  let U := FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T
  have hMR := stoppedProcess_rightContinuous D.N D.rightN
    (τ := fun w => (tau w : WithTop NNReal))
  have hML := D.leftN.stoppedProcess (fun w => (tau w : WithTop NNReal))
  have hUM : StronglyMeasurable U :=
    (FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedN hTau D.rightN) T).mono (F.le T)
  have hUBound : (∫⁻ w, ENNReal.ofReal (U w) ∂mu) ≤ 6 * a := by
    apply le_trans _ (Q.lintegral_allTime_maximal_le_six_root
      D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN hUsual)
    apply lintegral_mono
    intro w
    change ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope M T w) ≤ _
    rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup hMR hML T]
    apply iSup_le
    intro t
    exact le_iSup (fun s : NNReal => ENNReal.ofReal |D.N s w|)
      (boundedTime t.1 (fun w => (tau w : WithTop NNReal)) w)
  have hUInt : Integrable U mu :=
    (lintegral_ofReal_ne_top_iff_integrable hUM.aestronglyMeasurable
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))).mp
        (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ha) hUBound)
  have hUNorm : eLpNorm U 1 mu ≤ 6 * a := by
    have hU : ∀ w, 0 ≤ U w := fun _ => Real.sqrt_nonneg _
    rw [eLpNorm_one_eq_lintegral_enorm hUM.aestronglyMeasurable]
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hU _)] using hUBound
  let A := deterministicallyStoppedProcess D.A T
  have hAA : StronglyAdapted F A :=
    StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedA (isStoppingTime_const F T) D.rightA
  have hAR : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t :=
    stoppedProcess_rightContinuous D.A D.rightA
  have hAL : ProcessHasLeftLimits A := D.leftA.stoppedProcess _
  have hAV : ∀ w, BoundedVariationOn (A · w) univ := by
    intro w
    exact FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (D.variationA w) T
  have hAVBound : ∀ w, eVariationOn (A · w) univ ≤ eVariationOn (D.A · w) univ := by
    intro w
    exact eVariationOn.comp_le_of_monotoneOn (D.A · w) (fun t => min t T)
      ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ) (mapsTo_univ _ _)
  have hStrict : ∀ w, eVariationOn (strictPrefixProcess A tau · w) (Icc 0 T) ≤
      eVariationOn (D.A · w) univ := by
    intro w
    have hBefore : ∀ t, t < tau w → variationOnFromTo (A · w) univ 0 t ≤
        (eVariationOn (A · w) univ).toReal := by
      intro t _
      rw [variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le)]
      exact ENNReal.toReal_mono (hAV w) (eVariationOn.mono _ inter_subset_left)
    exact (eVariationOn.mono _ (subset_univ _)).trans
      ((strictPrefixProcess_variation_le_of_before A tau w (hAV w) hBefore).trans
        ((le_of_eq (ENNReal.ofReal_toReal (hAV w))).trans (hAVBound w)))
  have hVBound : prelocalH1SupFiniteVariationExpectedVariation (mu := mu) A tau T ≤ b :=
    lintegral_mono hStrict
  let Z : Process Ω := fun t w => if t < tau w then D.N t w + A t w else X t w
  let W : EmeryPrelocalH1SupWitness (F := F) (mu := mu) Z tau T :=
    EmeryPrelocalH1SupWitness.ofComponents
      (fun t w ht => by simp only [Z, ite_eq_left ht]) D.localMartingale D.adaptedN D.rightN D.leftN
      hTau hTauT hAA hAR hAL hAV (memLp_one_iff_integrable.mpr hUInt)
      (measurable_strictPrefixVariation_of_regularProcess A tau T hAA hAR hAL hTau)
      (ne_top_of_le_ne_top hb hVBound)
  have hZX : ProcessIndistinguishable mu Z X := by
    filter_upwards [D.decomposition, hPrefix] with w hw hp
    intro t
    by_cases ht : t < tau w
    · dsimp only [Z]
      rw [ite_eq_left ht]
      change D.N t w + D.A (min t T) w = X t w
      rw [min_eq_left (ht.le.trans (hTauT w)), ← hw t, hp t ht]
    · exact ite_eq_right ht
  refine ⟨⟨Z, W, hZX⟩, ?_⟩
  change eLpNorm U 1 mu + prelocalH1SupFiniteVariationExpectedVariation (mu := mu) A tau T ≤ _
  rw [hCost, mul_add]
  exact add_le_add hUNorm (hVBound.trans (le_mul_of_one_le_left' (by norm_num)))

theorem exists_prelocalSupExactRepresentation_of_prelocalJ1_lt
    (hUsual : Filtration.UsualConditions mu F)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) {r : ENNReal}
    (hSmall : prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) < r) :
    ∃ R : EmeryPrelocalH1SupExactRepresentation (F := F) (mu := mu) X tau T,
      prelocalH1SupWitnessCost R.witness < 6 * r := by
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp hSmall
  obtain ⟨hPrefix, hJ⟩ := iInf_lt_iff.mp hY
  obtain ⟨D, hD⟩ := iInf_lt_iff.mp hJ
  obtain ⟨R, hR⟩ := D.exists_prelocalSupExactRepresentation hUsual hTau hTauT
    (by simpa only [WithTop.coe_lt_coe] using hPrefix) (ne_top_of_lt (hD.trans_le (le_top)))
  exact ⟨R, hR.trans_lt (ENNReal.mul_lt_mul_right
    (show (6 : ENNReal) ≠ 0 by norm_num) (by norm_num) hD)⟩

end FTAPTheorem42
