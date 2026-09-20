/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.RawFiniteVariationRegularizationCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.ComponentPackage
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.JordanSignedProjection

/-!
# A square-integrable Jordan projection package for a bounded-variation path

This module is the deterministic-variation consumer for the generic
square-integrable compensator producer.  It starts with a zero-normalized,
strongly adapted càdlàg finite-variation process whose cumulative variation at
the fixed horizon is bounded by a deterministic constant.  The two Jordan
components are then supplied to the square-integrable increasing-process
producer, and the two resulting packages are consumed immediately by the
coherent Jordan projection certificate.

The input is deliberately stronger than an expected-variation hypothesis.
No level stopping or patching of an arbitrary `L¹` finite-variation process is
claimed here.  Predictability is also not assumed for the input finite-
variation process; it is produced by the two component projection
certificates.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The deterministic-variation input -/

structure AdaptedCadlagFiniteVariationData
    (A : Process Ω) (T C : NNReal) : Prop where
  stronglyAdapted : StronglyAdapted F A
  adapted : Adapted F A
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  hasLeftLimits : ProcessHasLeftLimits A
  boundedVariation : ∀ omega,
    BoundedVariationOn (A · omega) Set.univ
  zero : A 0 = 0
  constant_after : ∀ omega t, T ≤ t →
    A t omega = A T omega
  cumulativeVariation_bound : ∀ omega,
    localVariation A T omega ≤ (C : Real)

/-! The package returned below keeps the component certificates inside the
Jordan package.  Thus its `plus.hV` and `minus.hV` fields are the two
`SquareIntegrableIncreasingProcessData` certificates generated from the same
input path, while `pair` immediately consumes the two coherent component
packages. -/

structure SquareIntegrableJordanProjectionCertificate
    (A : Process Ω) (T : NNReal) where
  package : SquareIntegrablePredictableCompensatorJordanPackage
    (F := F) (mu := mu)
    (commonStopJordanPositive A) (commonStopJordanNegative A) T
  pair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
    package

namespace AdaptedCadlagFiniteVariationData

variable {A : Process Ω} {T C : NNReal}

private theorem cumulativeVariation_stronglyAdapted
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    StronglyAdapted F (localVariation A) := by
  intro t
  apply Measurable.stronglyMeasurable
  apply @FiniteVariationFactorialApproximation.measurable_variationOnFromTo_of_le
    Ω Real (F t) inferInstance inferInstance inferInstance inferInstance
    (fun s omega => A s omega) t
  · intro s hst
    exact (hA.stronglyAdapted.stronglyMeasurable_le hst).measurable
  · exact hA.rightContinuous

private theorem cumulativeVariation_rightContinuous
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t,
      ContinuousWithinAt (localVariation A · omega)
        (Ici t) t :=
  commonStopCumulativeVariation_rightContinuous
    hA.boundedVariation hA.rightContinuous

private theorem cumulativeVariation_constant_after
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t, T ≤ t →
      localVariation A t omega =
        localVariation A T omega :=
  commonStopCumulativeVariation_constant_after
    hA.boundedVariation hA.constant_after

private theorem jordanPositive_stronglyAdapted
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    StronglyAdapted F (commonStopJordanPositive A) := by
  have hCumulative := cumulativeVariation_stronglyAdapted hA
  intro t
  change StronglyMeasurable[F t]
    (fun x => (localVariation A t x + A t x) / 2)
  convert ((hCumulative t).add (hA.stronglyAdapted t)).const_smul
    (1 / 2 : Real) using 1
  ext x
  dsimp
  ring

private theorem jordanNegative_stronglyAdapted
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    StronglyAdapted F (commonStopJordanNegative A) := by
  have hCumulative := cumulativeVariation_stronglyAdapted hA
  intro t
  change StronglyMeasurable[F t]
    (fun x => (localVariation A t x - A t x) / 2)
  convert ((hCumulative t).sub (hA.stronglyAdapted t)).const_smul
    (1 / 2 : Real) using 1
  ext x
  dsimp
  ring

private theorem jordanPositive_rightContinuous
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t,
      ContinuousWithinAt (commonStopJordanPositive A · omega) (Ici t) t := by
  have hCumulative := cumulativeVariation_rightContinuous hA
  intro omega t
  change ContinuousWithinAt
    (fun s => (localVariation A s omega + A s omega) / 2)
    (Ici t) t
  exact ((hCumulative omega t).add (hA.rightContinuous omega t)).div_const 2

private theorem jordanNegative_rightContinuous
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t,
      ContinuousWithinAt (commonStopJordanNegative A · omega) (Ici t) t := by
  have hCumulative := cumulativeVariation_rightContinuous hA
  intro omega t
  change ContinuousWithinAt
    (fun s => (localVariation A s omega - A s omega) / 2)
    (Ici t) t
  exact ((hCumulative omega t).sub (hA.rightContinuous omega t)).div_const 2

private theorem jordanPositive_constant_after
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t, T ≤ t →
      commonStopJordanPositive A t omega =
        commonStopJordanPositive A T omega := by
  have hCumulative := cumulativeVariation_constant_after hA
  intro omega t htt
  rw [commonStopJordanPositive_apply, commonStopJordanPositive_apply,
    hCumulative omega t htt, hA.constant_after omega t htt]

private theorem jordanNegative_constant_after
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega t, T ≤ t →
      commonStopJordanNegative A t omega =
        commonStopJordanNegative A T omega := by
  have hCumulative := cumulativeVariation_constant_after hA
  intro omega t htt
  rw [commonStopJordanNegative_apply, commonStopJordanNegative_apply,
    hCumulative omega t htt, hA.constant_after omega t htt]

private theorem jordan_terminal_bounds
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    ∀ omega,
      (0 ≤ commonStopJordanPositive A T omega ∧
        commonStopJordanPositive A T omega ≤ (C : Real)) ∧
      (0 ≤ commonStopJordanNegative A T omega ∧
        commonStopJordanNegative A T omega ≤ (C : Real)) := by
  have hPlusMono := commonStopJordanPositive_monotone hA.boundedVariation
  have hMinusMono := commonStopJordanNegative_monotone hA.boundedVariation
  have hPlusZero := commonStopJordanPositive_zero hA.zero
  have hMinusZero := commonStopJordanNegative_zero hA.zero
  intro omega
  have hPlusNonneg : 0 ≤ commonStopJordanPositive A T omega := by
    have hmono := hPlusMono omega (show (0 : NNReal) ≤ T from bot_le)
    have hzero : commonStopJordanPositive A 0 omega = 0 := by
      simpa using congrFun hPlusZero omega
    linarith
  have hMinusNonneg : 0 ≤ commonStopJordanNegative A T omega := by
    have hmono := hMinusMono omega (show (0 : NNReal) ≤ T from bot_le)
    have hzero : commonStopJordanNegative A 0 omega = 0 := by
      simpa using congrFun hMinusZero omega
    linarith
  have hsum : commonStopJordanPositive A T omega +
      commonStopJordanNegative A T omega =
      localVariation A T omega := by
    rw [commonStopJordanPositive_apply, commonStopJordanNegative_apply]
    ring
  have hBound := hA.cumulativeVariation_bound omega
  exact ⟨⟨hPlusNonneg, by linarith⟩, ⟨hMinusNonneg, by linarith⟩⟩

omit [SigmaFiniteFiltration mu F] in
private theorem jordanPositive_terminal_memLp_two
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    MemLp (commonStopJordanPositive A T) (2 : ENNReal) mu := by
  apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    ((jordanPositive_stronglyAdapted hA T).mono (F.le T)).aestronglyMeasurable
    (C : Real)
  filter_upwards with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (jordan_terminal_bounds hA omega).1.1]
  exact (jordan_terminal_bounds hA omega).1.2

omit [SigmaFiniteFiltration mu F] in
private theorem jordanNegative_terminal_memLp_two
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C) :
    MemLp (commonStopJordanNegative A T) (2 : ENNReal) mu := by
  apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    ((jordanNegative_stronglyAdapted hA T).mono (F.le T)).aestronglyMeasurable
    (C : Real)
  filter_upwards with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (jordan_terminal_bounds hA omega).2.1]
  exact (jordan_terminal_bounds hA omega).2.2

/-! ## The two square-integrable increasing-process certificates -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableJordanProjectionCertificate
    (hA : AdaptedCadlagFiniteVariationData (F := F) (A := A) T C)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (SquareIntegrableJordanProjectionCertificate
      (F := F) (mu := mu) A T) := by
  let hPlus : SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) (commonStopJordanPositive A) T := {
    stronglyAdapted := jordanPositive_stronglyAdapted hA
    rightContinuous := jordanPositive_rightContinuous hA
    monotone := commonStopJordanPositive_monotone hA.boundedVariation
    zero := commonStopJordanPositive_zero hA.zero
    constant_after := jordanPositive_constant_after hA
    terminal_memLp_two := jordanPositive_terminal_memLp_two hA }
  let hMinus : SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) (commonStopJordanNegative A) T := {
    stronglyAdapted := jordanNegative_stronglyAdapted hA
    rightContinuous := jordanNegative_rightContinuous hA
    monotone := commonStopJordanNegative_monotone hA.boundedVariation
    zero := commonStopJordanNegative_zero hA.zero
    constant_after := jordanNegative_constant_after hA
    terminal_memLp_two := jordanNegative_terminal_memLp_two hA }
  obtain ⟨pkgPlus, badPlus, VpPlus, hProjectionPlus⟩ :=
    exists_squareIntegrablePredictableCompensatorDualProjection
      (F := F) (mu := mu) hPlus hUsual
  obtain ⟨pkgMinus, badMinus, VpMinus, hProjectionMinus⟩ :=
    exists_squareIntegrablePredictableCompensatorDualProjection
      (F := F) (mu := mu) hMinus hUsual
  let pkg : SquareIntegrablePredictableCompensatorJordanPackage
      (F := F) (mu := mu)
      (commonStopJordanPositive A) (commonStopJordanNegative A) T := {
    plus := pkgPlus
    minus := pkgMinus }
  have hPair : SquareIntegrablePredictableCompensatorJordanDualProjectionPairData
      pkg := by
    exact {
      plus := {
        badPred := badPlus
        Vp := VpPlus
        projection := hProjectionPlus }
      minus := {
        badPred := badMinus
        Vp := VpMinus
        projection := hProjectionMinus } }
  exact ⟨{ package := pkg, pair := hPair }⟩

end AdaptedCadlagFiniteVariationData

end HorizonFactorialGrid

end FTAPTheorem42
