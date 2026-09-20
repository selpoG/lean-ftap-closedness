/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualStopping
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairRefinement

/-!
# Scalar closure of the local-completed realization carrier

A realized local-completed graph retains its exhaustive schedule under a
deterministic scalar.  Scaling its coefficient at every coordinate and using
homogeneity of the concrete completed `M² + A¹` gain gives a new graph
witness.  Thus the intrinsic existential carrier supplies the actual scalar
calculus consumed by the Lemmas 4.7--4.11 pipeline.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- Deterministic scalar multiplication preserves the intrinsic
local-completed realization carrier. -/
theorem actualScalarCalculus (G : LocallySIntegrableStrategy D) :
    SIntegrableActualScalarCalculus (realizationModel G) where
  smul_isRealized := by
    intro c H
    obtain ⟨witness⟩ := H.property
    refine ⟨{
      schedule := witness.schedule
      coefficient := fun n => (witness.coefficient n).smul c
      coefficient_eq := fun n => ?_
      stoppedGain_eq := fun n => ?_ }⟩
    · change c • (witness.coefficient n).coefficient =
        Function.uncurry (c • H.val.integrand)
      rw [witness.coefficient_eq n]
      rfl
    · have hOld := (witness.stoppedGain_eq n).smul c
      have hCompleted := finiteHorizonCompletedM2AGain_smul
        witness.schedule.usualConditions
        (witness.schedule.quadraticKernel n)
        (witness.schedule.variationBridge n)
        (witness.schedule.martingale n)
        (witness.schedule.terminal_memLp n)
        (witness.coefficient n) c
      change ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess (c • H.val.stochasticIntegral)
          (witness.schedule.localizer n))
        (finiteHorizonCompletedM2AGain witness.schedule.usualConditions
          (witness.schedule.horizon n)
          (witness.schedule.quadraticKernel n)
          (witness.schedule.variationBridge n)
          (witness.schedule.martingale n)
          (witness.schedule.terminal_memLp n)
          ((witness.coefficient n).smul c))
      rw [MeasureTheory.stoppedProcess_const_smul]
      exact hOld.trans hCompleted.symm

end LocalCompletedM2A

/-!
## Convex combinations in the intrinsic local-completed carrier

Pairwise schedule refinement is enough for finite linear algebra. To add two
actual graphs, choose their intrinsic witnesses, refine only those two
schedules, and use completed additivity on the resulting common schedule.
Iterating this binary operation realizes the existing raw
`weightedPrefixSum`; no countable or finite-family schedule is selected.

The same binary addition, together with scalar negation and the concrete
stopping calculus, realizes the raw post-stopping tail. Thus the pairwise
refinement is consumed directly by the convexification and post-tail calculi
used in the Mémín pipeline.
-/

namespace LocalCompletedM2A

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- Add two intrinsic actual graphs after refining just their two witness
schedules. -/
noncomputable def actualAddOfPairRefinement
    (H K : ActualSIntegrableStrategy (realizationModel G)) :
    ActualSIntegrableStrategy (realizationModel G) :=
  let hH := (Classical.choice H.property).toScheduleGraphRepresentation
  let hK := (Classical.choice K.property).toScheduleGraphRepresentation
  let hCommon := exists_pairCommonScheduleRepresentations hH hK
  let representations := Classical.choose_spec hCommon
  actualAddOfCommonSchedule
    (Classical.choice representations.1)
    (Classical.choice representations.2)

@[simp]
theorem actualAddOfPairRefinement_val
    (H K : ActualSIntegrableStrategy (realizationModel G)) :
    (actualAddOfPairRefinement H K).val =
      H.val.add_of_rightContinuous K.val :=
  rfl

/-- Negation obtained from the concrete scalar calculus, with the canonical
raw negation restored as representative. -/
noncomputable def actualNeg
    (G : LocallySIntegrableStrategy D)
    (H : ActualSIntegrableStrategy (realizationModel G)) :
    ActualSIntegrableStrategy (realizationModel G) :=
  let K := (actualScalarCalculus G).smul (-1) H
  K.congr H.val.neg
    (by
      funext t omega
      change (-1 : Real) * H.val.integrand t omega =
        -H.val.integrand t omega
      ring)
    (by
      filter_upwards with omega
      intro t
      change (-1 : Real) * H.val.stochasticIntegral t omega =
        -H.val.stochasticIntegral t omega
      ring)

/-- The actual recursion matching the raw `weightedPrefixSum` exactly. At
each successor step only the current partial sum and the next summand are
pair-refined. -/
noncomputable def actualWeightedPrefixSum
    (H : Nat -> ActualSIntegrableStrategy (realizationModel G))
    (weight : Nat -> Real) :
    Nat -> ActualSIntegrableStrategy (realizationModel G)
  | 0 => (actualScalarCalculus G).smul 0 (H 0)
  | n + 1 => actualAddOfPairRefinement
      (actualWeightedPrefixSum H weight n)
      ((actualScalarCalculus G).smul (weight n) (H n))

@[simp]
theorem actualWeightedPrefixSum_val
    (H : Nat -> ActualSIntegrableStrategy (realizationModel G))
    (weight : Nat -> Real) (n : Nat) :
    (actualWeightedPrefixSum H weight n).val =
      SIntegrableStrategy.weightedPrefixSum
        (ActualSIntegrableStrategy.rawSequence H) weight n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [actualWeightedPrefixSum, actualAddOfPairRefinement_val,
        SIntegrableActualScalarCalculus.smul_val,
        SIntegrableStrategy.weightedPrefixSum, ih]

/-- Pairwise refinement and binary addition give the concrete finite tail
convex-combination calculus on the intrinsic carrier. -/
theorem actualConvexCombinationCalculus
    (G : LocallySIntegrableStrategy D) :
    SIntegrableActualConvexCombinationCalculus (realizationModel G) where
  tailConvexCombination_isRealized := by
    intro H n w
    rw [SIntegrableStrategy.tailConvexCombination,
      <- actualWeightedPrefixSum_val H w.coeff w.rangeSize]
    exact (actualWeightedPrefixSum H w.coeff w.rangeSize).property

end LocalCompletedM2A

end FTAPTheorem42
