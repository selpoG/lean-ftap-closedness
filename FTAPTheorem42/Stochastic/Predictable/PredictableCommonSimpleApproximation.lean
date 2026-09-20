/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcessCompletion
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansDensity

/-!
# Common simple approximations for predictable controls

The martingale and finite-variation components of one semimartingale
integral must be approximated by the same predictable sequence.
The standard `SimpleFunc.approxOn` sequence depends only on the raw
predictable function, not on a measure.  Consequently one sequence converges
simultaneously in every finite-exponent `Lᵖ` control to which the target
belongs.  This module records that fact on the predictable sigma algebra and
applies it to a finite-grid martingale-energy control together with a
canonical finite-variation control.
-/

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The measure-independent simple approximation of a strongly predictable
real process. -/
noncomputable def predictableCommonSimpleApproximationRaw
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    (ℝ≥0 × Ω) → ℝ := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  exact fun p => SimpleFunc.approxOn (Function.uncurry f) hf.measurable
    (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n p

/-- Curry the common raw simple approximation back into a process. -/
noncomputable def predictableCommonSimpleApproximation
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    Process Ω :=
  fun t ω => predictableCommonSimpleApproximationRaw f hf n (t, ω)

@[simp]
theorem uncurry_predictableCommonSimpleApproximation
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    Function.uncurry (predictableCommonSimpleApproximation f hf n) =
      predictableCommonSimpleApproximationRaw f hf n := by
  rfl

/-- Every common approximation remains strongly predictable. -/
theorem predictableCommonSimpleApproximation_isStronglyPredictable
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    IsStronglyPredictable ℱ
      (predictableCommonSimpleApproximation f hf n) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  change StronglyMeasurable[ℱ.predictable]
    (predictableCommonSimpleApproximationRaw f hf n)
  change StronglyMeasurable[ℱ.predictable]
    (SimpleFunc.approxOn (Function.uncurry f) hf.measurable
      (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n)
  exact (SimpleFunc.approxOn (Function.uncurry f) hf.measurable
    (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n).stronglyMeasurable

/-- Every common approximation has one deterministic pointwise bound. -/
theorem exists_predictableCommonSimpleApproximation_bound
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) :
    ∃ C : ℝ, ∀ t ω,
      |predictableCommonSimpleApproximation f hf n t ω| ≤ C := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  obtain ⟨C, hC⟩ :=
    (SimpleFunc.approxOn (Function.uncurry f) hf.measurable
      (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n
      ).exists_forall_norm_le
  refine ⟨C, fun t ω => ?_⟩
  simpa only [predictableCommonSimpleApproximation,
    predictableCommonSimpleApproximationRaw, Real.norm_eq_abs] using hC (t, ω)

/-- The common simple sequence converges pointwise to its predictable
target. -/
theorem predictableCommonSimpleApproximation_tendsto
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n =>
      predictableCommonSimpleApproximation f hf n t ω)
      atTop (𝓝 (f t ω)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  change Tendsto (fun n =>
    SimpleFunc.approxOn (Function.uncurry f) hf.measurable
      (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n (t, ω))
      atTop (𝓝 (Function.uncurry f (t, ω)))
  exact SimpleFunc.tendsto_approxOn hf.measurable
    (by simp : (0 : ℝ) ∈ Set.range (Function.uncurry f) ∪ {0})
    (subset_closure (by simp))

/-- The common approximation belongs to every finite-exponent control
`Lᵖ` space containing the target. -/
theorem predictableCommonSimpleApproximationRaw_memLp
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (ν : MeminPredictableControlMeasure ℱ) (p : ℝ≥0∞)
    (hfp : MemLp (Function.uncurry f) p ν) (n : ℕ) :
    MemLp (predictableCommonSimpleApproximationRaw f hf n) p ν := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  change MemLp
    (SimpleFunc.approxOn (Function.uncurry f) hf.measurable
      (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n) p ν
  exact SimpleFunc.memLp_approxOn_range hf.measurable hfp n

/-- The same simple sequence converges in any prescribed finite-exponent
predictable control. -/
theorem predictableCommonSimpleApproximationRaw_tendsto_eLpNorm
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (ν : MeminPredictableControlMeasure ℱ) (p : ℝ≥0∞)
    (hp : p ≠ ∞) (hfp : MemLp (Function.uncurry f) p ν) :
    Tendsto (fun n => eLpNorm
      (predictableCommonSimpleApproximationRaw f hf n -
        Function.uncurry f) p ν) atTop (𝓝 0) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : SeparableSpace
      (Set.range (Function.uncurry f) ∪ {0} : Set ℝ) :=
    hf.separableSpace_range_union_singleton
  change Tendsto (fun n => eLpNorm
    (⇑(SimpleFunc.approxOn (Function.uncurry f) hf.measurable
        (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n) -
      Function.uncurry f) p ν) atTop (𝓝 0)
  exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
    hp hf.measurable hfp.eLpNorm_lt_top

end FTAPTheorem42
