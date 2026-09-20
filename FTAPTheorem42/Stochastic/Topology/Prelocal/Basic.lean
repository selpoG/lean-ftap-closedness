/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.CompletedVariationStrictPrefix
import FTAPTheorem42.Stochastic.Topology.Emery.Completion

/-!
# Running-supremum and strict-prefix variation costs

This module proves measurability of finite-horizon variation for predictable
right-continuous processes. It also defines the two costs used by the
running-supremum prelocal H¹ witness: the expected running supremum of a
stopped martingale and the expected variation of the strict-prefix process
`A^{τ-}`. These costs are defined separately from the canonical j¹ cost.
-/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

/-! ## Measurability of the actual finite-horizon variation -/

theorem measurable_prelocalH1FiniteVariation
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (A : Process Omega) (T : NNReal)
    (hA : IsStronglyPredictable F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    : Measurable (fun omega => eVariationOn
      (A · omega) (Set.Icc 0 T)) := by
  have hPIcc : Measurable (fun omega => eVariationOn
      (A · omega) (Set.Icc 0 T)) := by
    have hEq : (fun omega => eVariationOn
        (A · omega) (Set.Icc 0 T)) =
        (fun omega => ⨆ r, FiniteVariationFactorialApproximation.eGridVariation
          (A · omega) T r) := by
      funext omega
      exact FiniteVariationFactorialApproximation.eVariationOn_Icc_eq_iSup_eGridVariation
        (A · omega) (hARight omega) T
    rw [hEq]
    apply Measurable.iSup
    intro r
    unfold FiniteVariationFactorialApproximation.eGridVariation
    apply Finset.measurable_fun_sum
    intro k hk
    apply Measurable.edist
    · exact ((hA.stronglyAdapted
        (FiniteVariationFactorialApproximation.point T r (k + 1))).mono
        (F.le (FiniteVariationFactorialApproximation.point T r (k + 1)))).measurable
    · exact ((hA.stronglyAdapted
        (FiniteVariationFactorialApproximation.point T r k)).mono
        (F.le (FiniteVariationFactorialApproximation.point T r k))).measurable
  exact hPIcc

/-! ## Expected component costs -/

/-- The finite-horizon cost of a stopped local-martingale component. -/
noncomputable def prelocalH1SupMartingaleRunningSupExpectation
    {mu : Measure Omega} (N : Process Omega) (tau : Omega → NNReal)
    (T : NNReal) : ENNReal :=
  eLpNorm
    (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (MeasureTheory.stoppedProcess N
        (fun omega => (tau omega : WithTop NNReal))) T) 1 mu

/-- The finite-horizon cost of the strict-prefix finite-variation component.
The use of `strictPrefixProcess` is the `A^{τ-}` term in Lemma 4(c). -/
noncomputable def prelocalH1SupFiniteVariationExpectedVariation
    {mu : Measure Omega} (A : Process Omega) (tau : Omega → NNReal)
    (T : NNReal) : ENNReal :=
  ∫⁻ omega, eVariationOn
    (strictPrefixProcess A tau · omega) (Set.Icc 0 T) ∂mu

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
