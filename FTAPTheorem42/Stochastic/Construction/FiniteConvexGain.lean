/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Market.Source.RealizedSpecialSource
import FTAPTheorem42.Stochastic.Topology.R1.Scalar
import FTAPTheorem42.Stochastic.Topology.Emery.Algebra
import FTAPTheorem42.Stochastic.Topology.Emery.PositiveScalar

/-! # Finite original-price sums with their specified components -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open PredictableElementaryEmery
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Nonnegative finite sums of original-price realizations retain exactly the
same finite sums of their normalized special components. -/
theorem exists_realized_finiteSum_with_components
    (hS : IsStronglyProgressive F S)
    (R : Nat → RealizedStrategy (ℱ := F) Q S)
    (D : ∀ i, J1Decomposition (R i).gain F Q)
    (hAP : ∀ i, IsStronglyPredictable F (D i).A)
    (s : Finset Nat) (a : Nat → Real) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∃ V : RealizedStrategy (ℱ := F) Q S,
      V.gain = (fun t ω => ∑ i ∈ s, a i * (R i).gain t ω) ∧
      ∃ E : J1Decomposition V.gain F Q,
        E.N = (fun t ω => ∑ i ∈ s, a i * (D i).N t ω) ∧
        E.A = (fun t ω => ∑ i ∈ s, a i * (D i).A t ω) ∧
        IsStronglyPredictable F E.A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      let V := RealizedStrategy.zero (μ := Q) S hS
      have hV : V.gain = 0 := by
        funext t ω
        simp [V, RealizedStrategy.zero]
      let E : J1Decomposition V.gain F Q := { (D 0).smul 0 with
        decomposition := by
          rw [hV]
          exact Eventually.of_forall fun ω t => by simp [J1Decomposition.smul] }
      refine ⟨V, ?_, E, ?_, ?_, ?_⟩
      · funext t ω
        simpa only [Finset.sum_empty, Pi.zero_apply] using congrFun (congrFun hV t) ω
      · funext t ω
        simp [E, J1Decomposition.smul]
      · funext t ω
        simp [E, J1Decomposition.smul]
      · exact (hAP 0).const_mul 0
  | @insert i s hi ih =>
      obtain ⟨V, hV, E, hN, hA, hEP⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai := ha i (Finset.mem_insert_self i s)
      by_cases hzero : a i = 0
      · refine ⟨V, ?_, E, ?_, ?_, hEP⟩
        · simpa only [Finset.sum_insert hi, hzero, zero_mul, zero_add] using hV
        · simpa only [Finset.sum_insert hi, hzero, zero_mul, zero_add] using hN
        · simpa only [Finset.sum_insert hi, hzero, zero_mul, zero_add] using hA
      · have hpos : 0 < a i := lt_of_le_of_ne hai (Ne.symm hzero)
        let W := (R i).posSMul S hS (a i) hpos
        let U := W.add S hS V
        let B : J1Decomposition U.gain F Q := ((D i).smul (a i)).add E
        refine ⟨U, ?_, B, ?_, ?_, ?_⟩
        · funext t ω
          change a i * (R i).gain t ω + V.gain t ω = _
          simp only [hV, Finset.sum_insert hi]
        · funext t ω
          simp only [B, J1Decomposition.add, J1Decomposition.smul, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul, hN, Finset.sum_insert hi]
        · funext t ω
          simp only [B, J1Decomposition.add, J1Decomposition.smul, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul, hA, Finset.sum_insert hi]
        · exact ((hAP i).const_mul (a i)).add hEP

end FTAPTheorem42.BoundedSourceIntegralMarket
