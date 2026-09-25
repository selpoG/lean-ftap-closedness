/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Decomposition
import FTAPTheorem42.Stochastic.Martingale.Davis.LocalMartingaleDavis

/-! # The zero-initial j1 cost over all adapted finite-variation decompositions -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

/-- Extended cost, with all intrinsic quadratic variations quantified.
Under usual conditions this family is nonempty and unique up to indistinguishability. -/
noncomputable def J1Decomposition.cost (D : J1Decomposition X F mu) : ENNReal :=
  ⨅ Q : LocalMartingaleQuadraticVariation D.N F mu,
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu) +
      ∫⁻ w, eVariationOn (D.A · w) univ ∂mu

/-- The zero-initial j1 gauge takes the infimum over all decompositions,
including those of infinite cost. -/
noncomputable def semimartingaleJ1 (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) : ENNReal :=
  ⨅ D : J1Decomposition X F mu, D.cost

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.cost_eq (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) :
    D.cost = (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu) +
      ∫⁻ w, eVariationOn (D.A · w) univ ∂mu := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  apply le_antisymm (iInf_le _ Q)
  apply le_iInf
  intro P
  have hEq := Q.unique hUsual D.rightN P
  have hRoot : (fun w => ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w))) =ᵐ[mu]
      (fun w => ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (P.variation t w))) := by
    filter_upwards [hEq] with w hw
    simp only [hw]
  exact le_of_eq (congrArg (fun a => a + ∫⁻ w, eVariationOn (D.A · w) univ ∂mu)
    (lintegral_congr_ae hRoot))

theorem J1Decomposition.cost_eq_lintegral (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) :
    D.cost = ∫⁻ w, (⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w))) +
      eVariationOn (D.A · w) univ ∂mu := by
  rw [D.cost_eq hUsual Q, lintegral_add_left Q.measurable_allTimeRoot]

theorem J1Decomposition.lintegral_maximal_le_six_cost (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F) :
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |X t w| ∂mu) ≤ 6 * D.cost := by
  obtain ⟨Q, _⟩ := exists_unique_localMartingaleQuadraticVariation
    D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN hUsual
  rw [D.cost_eq_lintegral hUsual Q, lintegral_add_left Q.measurable_allTimeRoot]
  have hPointwise : ∀ᵐ w ∂mu, (⨆ t : NNReal, ENNReal.ofReal |X t w|) ≤
      (⨆ t : NNReal, ENNReal.ofReal |D.N t w|) + eVariationOn (D.A · w) univ := by
    filter_upwards [D.decomposition] with w hw
    apply iSup_le
    intro t
    have hVar : ENNReal.ofReal |D.A t w| ≤ eVariationOn (D.A · w) univ := by
      have h := eVariationOn.edist_le (D.A · w) (mem_univ t) (mem_univ 0)
      simpa only [D.zeroA, Pi.zero_apply, edist_dist, Real.dist_eq, sub_zero] using h
    rw [hw t]
    exact (ENNReal.ofReal_le_ofReal (abs_add_le (D.N t w) (D.A t w))).trans
      ((le_of_eq (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))).trans
        (add_le_add (le_iSup (fun s : NNReal => ENNReal.ofReal |D.N s w|) t) hVar))
  calc
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |X t w| ∂mu) ≤
        ∫⁻ w, (⨆ t : NNReal, ENNReal.ofReal |D.N t w|) +
          eVariationOn (D.A · w) univ ∂mu := lintegral_mono_ae hPointwise
    _ = (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |D.N t w| ∂mu) +
        ∫⁻ w, eVariationOn (D.A · w) univ ∂mu :=
      lintegral_add_left (FactorialChronologicalGrid.measurable_iSup_ofReal_abs_of_cadlag
        D.adaptedN D.rightN D.leftN) _
    _ ≤ 6 * (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu) +
        6 * ∫⁻ w, eVariationOn (D.A · w) univ ∂mu :=
      add_le_add (Q.lintegral_allTime_maximal_le_six_root
        D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN hUsual)
        (le_mul_of_one_le_left' (by norm_num))
    _ = _ := (mul_add _ _ _).symm

theorem lintegral_maximal_le_six_semimartingaleJ1
    (hUsual : Filtration.UsualConditions mu F) :
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |X t w| ∂mu) ≤ 6 * semimartingaleJ1 X F mu := by
  rw [semimartingaleJ1, ENNReal.mul_iInf_of_ne (by norm_num : (6 : ENNReal) ≠ 0)
    (by norm_num : (6 : ENNReal) ≠ ∞)]
  exact le_iInf (fun D => D.lintegral_maximal_le_six_cost hUsual)

end FTAPTheorem42
