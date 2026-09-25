/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.BoundaryConsumer
import FTAPTheorem42.Stochastic.FiniteVariation.PredictableFiniteVariationLocalMartingale

/-!
# Fixed-source consumption of the strict-prefix boundary decomposition

This module consumes the process-level strict-prefix boundary certificate
against one raw `SIntegrableStrategy`. The candidate record is required
to decompose the same strict-prefix target globally; open-prefix agreement is
not used as a substitute for this hypothesis.  Predictable finite-variation
local-martingale rigidity then identifies the centered finite-variation and
martingale coordinates up to process indistinguishability.

The result is deliberately structural.  It does not transfer a running-supremum
`H¹` bound, summability, a Mémín limit, or stochastic-integral range closure.
In particular, neither the record nor `hActual` supplies realization-carrier
membership. A general strict prefix need not be an integral of the original
source; actual component transfer requires a separate closed-stop comparison
and control of the gain's boundary jump.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

/-! ## Centered candidate component comparison -/

/-- A raw candidate strategy and the boundary certificate have the same
centered components whenever they globally decompose the same strict-prefix
target.  Both equalities are process indistinguishability statements, so the
single exceptional set is retained throughout the argument. -/
theorem exists_fixedSource_centeredBoundaryComponentAgreement
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    {S : Process Ω}
    (D : SpecialSemimartingaleDecomposition S F mu)
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T)
    (H : SIntegrableStrategy D)
    (hUsual : Filtration.UsualConditions mu F)
    (hTarget : strictPrefixProcess X tau =
      strictPrefixProcess (fun t omega => w.N t omega + w.A t omega) tau)
    (hActual : ProcessIndistinguishable mu
      (strictPrefixProcess X tau)
      (fun t omega => H.martingalePart t omega + H.finiteVariationPart t omega)) :
    ∃ B : StrictPrefixBoundaryGlobalSpecialDecomposition
        (F := F) (mu := mu) X tau T w,
      ProcessIndistinguishable mu
        (fun t omega => B.A t omega - B.A 0 omega)
        (fun t omega => H.finiteVariationPart t omega -
          H.finiteVariationPart 0 omega) ∧
      ProcessIndistinguishable mu
        (fun t omega => B.M t omega - B.M 0 omega)
        H.centeredMartingalePart := by
  obtain ⟨B⟩ := exists_strictPrefixBoundaryGlobalSpecialDecomposition
    (F := F) (mu := mu) w hUsual hTarget
  have hGlobalActual : ProcessIndistinguishable mu
      (fun t omega => B.M t omega + B.A t omega)
      (fun t omega => H.martingalePart t omega + H.finiteVariationPart t omega) :=
    B.decomposition.symm.trans hActual
  let martingaleDifference : Process Ω := fun t omega =>
    H.martingalePart t omega - B.M t omega
  let finiteVariationDifference : Process Ω := fun t omega =>
    B.A t omega - H.finiteVariationPart t omega
  have hMartingaleDifferenceLocal :
      LocalMartingale martingaleDifference F mu := by
    have hRaw := H.martingalePart_isLocalMartingale.add_of_rightContinuous
      B.M_isLocalMartingale.neg
      H.martingalePart_isRightContinuous
      (fun omega t => (B.M_rightContinuous omega t).neg)
    simpa only [martingaleDifference, sub_eq_add_neg] using hRaw
  have hFiniteVariationDifferencePredictable :
      IsStronglyPredictable F finiteVariationDifference := by
    unfold IsStronglyPredictable
    rw [show Function.uncurry finiteVariationDifference =
        Function.uncurry B.A - Function.uncurry H.finiteVariationPart by
      funext x
      rfl]
    exact B.A_isStronglyPredictable.sub H.finiteVariationPart_isPredictable
  have hFiniteVariationDifferenceRight : ∀ omega t,
      ContinuousWithinAt (finiteVariationDifference · omega) (Ici t) t := by
    intro omega t
    exact (B.A_rightContinuous omega t).sub
      (H.finiteVariationPart_isRightContinuous omega t)
  have hFiniteVariationDifferenceBoundedVariation : ∀ omega,
      BoundedVariationOn (finiteVariationDifference · omega) Set.univ := by
    intro omega
    change BoundedVariationOn (fun t =>
      B.A t omega + -H.finiteVariationPart t omega) Set.univ
    exact boundedVariationOn_add (B.A_boundedVariation omega)
      (boundedVariationOn_neg (H.finiteVariationPart_isBoundedVariation omega))
  have hDifference : ProcessIndistinguishable mu
      martingaleDifference finiteVariationDifference := by
    filter_upwards [hGlobalActual] with omega hOmega
    intro t
    dsimp only [martingaleDifference, finiteVariationDifference]
    have h := hOmega t
    linarith
  have hFiniteVariationDifferenceLocal :
      LocalMartingale finiteVariationDifference F mu :=
    LocalMartingale.congr_indistinguishable
      hMartingaleDifferenceLocal
      hFiniteVariationDifferencePredictable.stronglyAdapted
      hFiniteVariationDifferenceRight hDifference
  have hConstant :=
    PredictableFiniteVariationLocalMartingale.indistinguishable_initial
      hUsual D finiteVariationDifference hFiniteVariationDifferenceLocal
      hFiniteVariationDifferencePredictable hFiniteVariationDifferenceRight
      hFiniteVariationDifferenceBoundedVariation
  have hCenteredVariation : ProcessIndistinguishable mu
      (fun t omega => B.A t omega - B.A 0 omega)
      (fun t omega => H.finiteVariationPart t omega -
        H.finiteVariationPart 0 omega) := by
    filter_upwards [hConstant] with omega hOmega
    intro t
    have hAt := hOmega t
    have hA0 := hOmega 0
    dsimp only [finiteVariationDifference] at hAt hA0
    linarith
  have hCenteredMartingale : ProcessIndistinguishable mu
      (fun t omega => B.M t omega - B.M 0 omega)
      H.centeredMartingalePart := by
    filter_upwards [hDifference, hConstant] with omega
      hDifferenceOmega hConstantOmega
    intro t
    have hDt := hDifferenceOmega t
    have hD0 := hDifferenceOmega 0
    have hCt := hConstantOmega t
    have hC0 := hConstantOmega 0
    dsimp only [martingaleDifference, finiteVariationDifference,
      SIntegrableStrategy.centeredMartingalePart] at hDt hD0 hCt hC0 ⊢
    linarith
  exact ⟨B, hCenteredVariation, hCenteredMartingale⟩

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
