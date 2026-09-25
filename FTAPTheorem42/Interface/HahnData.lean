/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Decomposition
import FTAPTheorem42.Foundations.HahnStopping
import FTAPTheorem42.Interface.IntegralClosure

/-! # The mathematical contract of an original-market Hahn improvement -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Mathematical data of the generated original-market Hahn improvement -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- These data are produced from the actual Hahn gain. The market remains
the original price; only the component estimates use the auxiliary measure. -/
structure OriginalHahnImprovement
    (source : BoundedSemimartingaleSource S F μ)
    (Q : Measure Ω) (Y M A : Process Ω) (T : NNReal) (b δ : Real) where
  gain : Process Ω
  martingale : Process Ω
  finiteVariation : Process Ω
  martingale_adapted : StronglyAdapted F martingale
  martingale_right : ∀ ω t, ContinuousWithinAt (martingale · ω) (Ici t) t
  finiteVariation_adapted : StronglyAdapted F finiteVariation
  decomposition : ProcessIndistinguishable Q gain (martingale + finiteVariation)
  finiteVariation_zero : finiteVariation 0 =ᵐ[Q] 0
  increment : ∀ᵐ ω ∂Q, ∀ a c : NNReal, a ≤ c →
    0 ≤ finiteVariation c ω - finiteVariation a ω ∧
    A (min c T) ω - A (min a T) ω ≤ finiteVariation c ω - finiteVariation a ω
  martingale_bound : (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
    martingale T ω ∂Q) ≤ b
  downside_probability : 0 < δ → δ ≤ 1 →
    Q.real {ω | lowerStrictHittingAfter (hahnMartingaleAdvantage martingale M) δ ω ≤
      (T : WithTop NNReal)} ≤ (b + b) / (δ / 4)
  terminal_mem : ∀ U : NNReal, T ≤ U →
    (finiteHahnPastedGain Y gain martingale M δ T U) U ∈
      generalAdmissibleClaims source (1 + δ)

/-! ## Orient variation events using the two improvements -/

/-- Both improvements retain their own original-market terminal claims. The
orientation is chosen only after the level of the variation event is specified. -/
def OriginalPairHahnOrientedImprovement
    (source : BoundedSemimartingaleSource S F μ)
    (Y Z : Process Ω)
    (D : J1Decomposition Y F Q) (E : J1Decomposition Z F Q)
    (T : NNReal) (b δ : Real) : Prop :=
  ∃ P : OriginalHahnImprovement source Q Z (D.N - E.N) (D.A - E.A) T b δ,
  ∃ P' : OriginalHahnImprovement source Q Y (E.N - D.N) (E.A - D.A) T b δ,
    ∀ α : Real,
      α < Q.real {ω | α < finiteHorizonPathVariation (D.A - E.A)
        (fun ω a c ha hc => by
          simpa only [Pi.sub_apply, sub_eq_add_neg] using
            boundedVariationOn_add (D.variationA ω a c ha hc)
              (boundedVariationOn_neg (E.variationA ω a c ha hc))) T ω} →
      α / 2 < Q.real {ω | α / 2 < P.finiteVariation T ω} ∨
        α / 2 < Q.real {ω | α / 2 < P'.finiteVariation T ω}

end FTAPTheorem42.BoundedSourceIntegralMarket
