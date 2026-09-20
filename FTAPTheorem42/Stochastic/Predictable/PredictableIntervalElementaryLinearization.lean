/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalElementaryApproximation
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryProduct

/-!
# Linearizing predictable interval unions by elementary strategies

An interval-algebra carrier is a finite union, whereas an elementary
strategy is a finite sum of blocks.  Overlaps therefore have to be removed
algebraically.  This module implements the finite inclusion-exclusion
identity using intersections of foretold intervals, then replaces every
signed interval term by an actual elementary block.
-/

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega)}

namespace PredictableIntervalAlgebra

attribute [local instance] Classical.propDecidable

/-- A signed indicator of one foretold interval. -/
noncomputable def signedIntervalTermFunction
    (term : ℝ × Interval F) : ℝ≥0 × Omega → ℝ :=
  term.2.carrier.indicator fun _ => term.1

/-- The raw function represented by a finite signed list of foretold
intervals. -/
noncomputable def signedIntervalFunction
    (terms : List (ℝ × Interval F)) : ℝ≥0 × Omega → ℝ :=
  (terms.map signedIntervalTermFunction).sum

@[simp]
theorem signedIntervalFunction_nil :
    signedIntervalFunction ([] : List (ℝ × Interval F)) = 0 := by
  rfl

@[simp]
theorem signedIntervalFunction_cons
    (term : ℝ × Interval F) (terms : List (ℝ × Interval F)) :
    signedIntervalFunction (term :: terms) =
      signedIntervalTermFunction term + signedIntervalFunction terms := by
  rfl

@[simp]
theorem signedIntervalFunction_append
    (left right : List (ℝ × Interval F)) :
    signedIntervalFunction (left ++ right) =
      signedIntervalFunction left + signedIntervalFunction right := by
  unfold signedIntervalFunction
  rw [List.map_append, List.sum_append]

/-- Intersect every signed term with `I` and negate its coefficient. -/
noncomputable def negateIntersections
    (I : Interval F) (terms : List (ℝ × Interval F)) :
    List (ℝ × Interval F) :=
  terms.map fun term => (-term.1, Interval.inter I term.2)

/-- Intersecting and negating a signed interval function multiplies it by
`-1_I`. -/
theorem signedIntervalFunction_negateIntersections
    (I : Interval F) (terms : List (ℝ × Interval F)) :
    signedIntervalFunction (negateIntersections I terms) =
      fun p => if p ∈ I.carrier then -signedIntervalFunction terms p else 0 := by
  funext p
  induction terms with
  | nil => simp [negateIntersections]
  | cons term terms ih =>
      simp only [negateIntersections, List.map_cons,
        signedIntervalFunction_cons, signedIntervalTermFunction,
        Interval.carrier_inter, Pi.add_apply]
      change
        (I.carrier ∩ term.2.carrier).indicator (fun _ => -term.1) p +
            signedIntervalFunction (negateIntersections I terms) p = _
      rw [ih]
      by_cases hI : p ∈ I.carrier <;>
        by_cases hTerm : p ∈ term.2.carrier <;>
          simp [hI, hTerm]
      ring

/-- Inclusion-exclusion terms representing the indicator of a finite union
of foretold intervals. -/
noncomputable def unionIndicatorTerms :
    List (Interval F) → List (ℝ × Interval F)
  | [] => []
  | I :: intervals =>
      (1, I) :: unionIndicatorTerms intervals ++
        negateIntersections I (unionIndicatorTerms intervals)

/-- The inclusion-exclusion list represents the union indicator exactly. -/
theorem signedIntervalFunction_unionIndicatorTerms
    (intervals : List (Interval F)) :
    signedIntervalFunction (unionIndicatorTerms intervals) =
      (carrier intervals).indicator fun _ => 1 := by
  funext p
  induction intervals with
  | nil => simp [unionIndicatorTerms]
  | cons I intervals ih =>
      simp only [unionIndicatorTerms, signedIntervalFunction_cons,
        signedIntervalFunction_append, Pi.add_apply,
        signedIntervalTermFunction]
      rw [signedIntervalFunction_negateIntersections, ih]
      change
        I.carrier.indicator (fun _ => 1) p +
            (carrier intervals).indicator (fun _ => 1) p +
              (if p ∈ I.carrier then
                -signedIntervalFunction (unionIndicatorTerms intervals) p
              else 0) =
          (carrier (I :: intervals)).indicator (fun _ => 1) p
      rw [ih]
      by_cases hI : p ∈ I.carrier <;>
        by_cases hIntervals : p ∈ carrier intervals <;>
          simp [carrier_cons, hI, hIntervals]

/-- Multiply every coefficient in a signed interval list by one scalar. -/
noncomputable def scaleSignedIntervalTerms
    (c : ℝ) (terms : List (ℝ × Interval F)) :
    List (ℝ × Interval F) :=
  terms.map fun term => (c * term.1, term.2)

theorem signedIntervalFunction_scaleSignedIntervalTerms
    (c : ℝ) (terms : List (ℝ × Interval F)) :
    signedIntervalFunction (scaleSignedIntervalTerms c terms) =
      fun p => c * signedIntervalFunction terms p := by
  funext p
  induction terms with
  | nil => simp [scaleSignedIntervalTerms]
  | cons term terms ih =>
      simp only [scaleSignedIntervalTerms, List.map_cons,
        signedIntervalFunction_cons, signedIntervalTermFunction,
        Pi.add_apply]
      change
        term.2.carrier.indicator (fun _ => c * term.1) p +
            signedIntervalFunction (scaleSignedIntervalTerms c terms) p = _
      rw [ih]
      by_cases hTerm : p ∈ term.2.carrier <;> simp [hTerm]
      ring

/-- Flatten the interval-algebra normal form into one finite signed list of
single intervals. -/
noncomputable def linearizeIntervalSimpleTerms :
    List (ℝ × List (Interval F)) → List (ℝ × Interval F)
  | [] => []
  | term :: terms =>
      scaleSignedIntervalTerms term.1 (unionIndicatorTerms term.2) ++
        linearizeIntervalSimpleTerms terms

/-- Linearization preserves the interval-algebra simple function exactly. -/
theorem signedIntervalFunction_linearizeIntervalSimpleTerms
    (terms : List (ℝ × List (Interval F))) :
    signedIntervalFunction (linearizeIntervalSimpleTerms terms) =
      intervalSimpleFunction terms := by
  funext p
  induction terms with
  | nil => simp [linearizeIntervalSimpleTerms]
  | cons term terms ih =>
      simp only [linearizeIntervalSimpleTerms,
        signedIntervalFunction_append,
        signedIntervalFunction_scaleSignedIntervalTerms,
        signedIntervalFunction_unionIndicatorTerms,
        intervalSimpleFunction_cons, intervalTermFunction, Pi.add_apply]
      rw [ih]
      by_cases hCarrier : p ∈ carrier term.2 <;> simp [hCarrier]

namespace Interval

/-- Scale one elementary interval approximation by an arbitrary real
coefficient. -/
noncomputable def scaledElementaryApproximation
    (I : Interval F) (c : ℝ) (n : ℕ) :
    PredictableElementaryInterval F where
  interval :=
    { coefficient := fun _ => c
      startTime := I.left_foretelling.finiteTime n
      stopTime := fun omega => max
        (I.left_foretelling.finiteTime n omega)
        (I.right_foretelling.finiteTime n omega)
      start_le_stop := fun omega => le_max_left _ _ }
  startStopping := I.left_foretelling.finiteTime_isStoppingTime n
  stopStopping := by
    simpa only [WithTop.coe_max] using
      (I.left_foretelling.finiteTime_isStoppingTime n).max
        (I.right_foretelling.finiteTime_isStoppingTime n)
  coefficient_measurable := measurable_const

theorem scaledElementaryApproximation_integrand
    (I : Interval F) (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : Omega) :
    (I.scaledElementaryApproximation c n).integrand t omega =
      if (t, omega) ∈ I.elementaryApproximationCarrier n then c else 0 := by
  dsimp only [PredictableElementaryInterval.integrand,
    scaledElementaryApproximation]
  by_cases hactive :
      I.left_foretelling.finiteTime n omega < t ∧
        t ≤ max (I.left_foretelling.finiteTime n omega)
          (I.right_foretelling.finiteTime n omega)
  · have hmem : (t, omega) ∈ I.elementaryApproximationCarrier n := hactive
    rw [ite_eq_left hactive, ite_eq_left hmem]
  · have hmem : (t, omega) ∉ I.elementaryApproximationCarrier n := hactive
    rw [ite_eq_right hactive, ite_eq_right hmem]

end Interval

/-- Replace every signed foretold interval by its actual elementary block
at one common foretelling index. -/
noncomputable def signedElementaryApproximation
    (terms : List (ℝ × Interval F)) (n : ℕ) :
    PredictableElementaryStrategy F :=
  terms.map fun term => term.2.scaledElementaryApproximation term.1 n

/-- Away from time zero, the actual elementary strategy associated with a
finite signed interval list eventually equals its raw signed interval
function. -/
theorem eventually_signedElementaryApproximation_integrand_eq
    (terms : List (ℝ × Interval F))
    {t : ℝ≥0} (ht : t ≠ 0) (omega : Omega) :
    ∀ᶠ n in atTop,
      (signedElementaryApproximation terms n).integrand t omega =
        signedIntervalFunction terms (t, omega) := by
  induction terms with
  | nil =>
      exact Eventually.of_forall fun n => by
        simp [signedElementaryApproximation,
          PredictableElementaryStrategy.integrand]
  | cons term terms ih =>
      filter_upwards [term.2.eventually_mem_elementaryApproximationCarrier_iff
        ht omega, ih] with n hTerm hRest
      change
        (term.2.scaledElementaryApproximation term.1 n).integrand t omega +
            (signedElementaryApproximation terms n).integrand t omega =
          signedIntervalTermFunction term (t, omega) +
            signedIntervalFunction terms (t, omega)
      rw [term.2.scaledElementaryApproximation_integrand, hRest]
      by_cases hCarrier : (t, omega) ∈ term.2.carrier
      · rw [ite_eq_left (hTerm.mpr hCarrier)]
        simp [signedIntervalTermFunction, hCarrier]
      · rw [ite_eq_right (fun h => hCarrier (hTerm.mp h))]
        simp [signedIntervalTermFunction, hCarrier]

/-- The actual elementary strategy associated with one interval-algebra
simple function at a common foretelling index. -/
noncomputable def intervalSimpleElementaryApproximation
    (terms : List (ℝ × List (Interval F))) (n : ℕ) :
    PredictableElementaryStrategy F :=
  signedElementaryApproximation
    (linearizeIntervalSimpleTerms terms) n

/-- The raw function represented by a signed interval list is predictably
measurable. -/
theorem signedIntervalFunction_stronglyMeasurable
    (terms : List (ℝ × Interval F)) :
    StronglyMeasurable[F.predictable]
      (signedIntervalFunction terms) := by
  induction terms with
  | nil =>
      exact stronglyMeasurable_zero
  | cons term terms ih =>
      rw [signedIntervalFunction_cons]
      apply StronglyMeasurable.add
      · unfold signedIntervalTermFunction
        exact StronglyMeasurable.indicator stronglyMeasurable_const
          term.2.measurableSet_carrier
      · exact ih

/-- The predictable set on which an actual elementary approximation and
its raw signed interval function differ. -/
def signedElementaryMismatch
    (terms : List (ℝ × Interval F)) (n : ℕ) :
    Set (ℝ≥0 × Omega) :=
  {p | (signedElementaryApproximation terms n).integrand p.1 p.2 ≠
    signedIntervalFunction terms p}

/-- The mismatch set is predictable. -/
theorem measurableSet_signedElementaryMismatch
    (terms : List (ℝ × Interval F)) (n : ℕ) :
    MeasurableSet[F.predictable]
      (signedElementaryMismatch terms n) := by
  have hMeasurable : StronglyMeasurable[F.predictable] (fun p =>
      (signedElementaryApproximation terms n).integrand p.1 p.2 -
        signedIntervalFunction terms p) :=
    (signedElementaryApproximation terms n).integrand_isStronglyPredictable.sub
      (signedIntervalFunction_stronglyMeasurable terms)
  rw [show signedElementaryMismatch terms n =
      (fun p =>
        (signedElementaryApproximation terms n).integrand p.1 p.2 -
          signedIntervalFunction terms p) ⁻¹' ({0} : Set ℝ)ᶜ by
    ext p
    change
      ((signedElementaryApproximation terms n).integrand p.1 p.2 ≠
          signedIntervalFunction terms p) ↔
        (signedElementaryApproximation terms n).integrand p.1 p.2 -
            signedIntervalFunction terms p ∈ ({0} : Set ℝ)ᶜ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]]
  exact hMeasurable.measurable (measurableSet_singleton (0 : ℝ)).compl

/-- Under a finite control with no atom on the time-zero slice, the
mismatch sets of one finite signed interval list have vanishing measure. -/
theorem tendsto_measure_signedElementaryMismatch
    (terms : List (ℝ × Interval F))
    (nu : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu]
    (hzero : nu
      (Interval.timeZeroSlice : Set (ℝ≥0 × Omega)) = 0) :
    Tendsto (fun n => nu (signedElementaryMismatch terms n))
      atTop (𝓝 0) := by
  let : MeasurableSpace (ℝ≥0 × Omega) := F.predictable
  have hNonzero : ∀ᵐ p ∂nu, p.1 ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with p hp
    simpa only [Interval.mem_timeZeroSlice_iff] using hp
  have hEventually : ∀ᵐ p ∂nu, ∀ᶠ n in atTop,
      p ∈ signedElementaryMismatch terms n ↔
        p ∈ (∅ : Set (ℝ≥0 × Omega)) := by
    filter_upwards [hNonzero] with p hp
    filter_upwards [eventually_signedElementaryApproximation_integrand_eq
      terms hp p.2] with n hn
    simp only [signedElementaryMismatch, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false]
    exact not_ne_iff.mpr hn
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (L := atTop) MeasurableSet.empty
      (measurableSet_signedElementaryMismatch terms)
      hEventually

/-- The sum of the absolute coefficients in a finite signed interval
representation. -/
def signedIntervalCoefficientBound
    (terms : List (ℝ × Interval F)) : ℝ :=
  (terms.map fun term => |term.1|).sum

theorem signedIntervalCoefficientBound_nonneg
    (terms : List (ℝ × Interval F)) :
    0 ≤ signedIntervalCoefficientBound terms := by
  unfold signedIntervalCoefficientBound
  exact List.sum_nonneg fun value hvalue => by
    obtain ⟨term, -, rfl⟩ := List.mem_map.mp hvalue
    exact abs_nonneg term.1

/-- The blockwise absolute coefficient sum of a signed elementary
approximation is exactly the sum retained by its interval-algebra normal
form.  In particular, this stronger bound does not rely on cancellation in
the summed integrand. -/
theorem coefficientAbsSum_signedElementaryApproximation
    (terms : List (ℝ × Interval F)) (n : ℕ) (omega : Omega) :
    (signedElementaryApproximation terms n).coefficientAbsSum omega =
      signedIntervalCoefficientBound terms := by
  induction terms with
  | nil => simp [signedElementaryApproximation,
      signedIntervalCoefficientBound, PredictableElementaryStrategy.coefficientAbsSum]
  | cons term terms ih =>
      change
        |(term.2.scaledElementaryApproximation term.1 n).interval.coefficient
            omega| +
            (signedElementaryApproximation terms n).coefficientAbsSum omega =
          |term.1| + signedIntervalCoefficientBound terms
      change
        |term.1| +
            (signedElementaryApproximation terms n).coefficientAbsSum omega =
          |term.1| + signedIntervalCoefficientBound terms
      rw [ih]

/-- The raw signed interval function is uniformly bounded by the sum of
the absolute coefficients. -/
theorem abs_signedIntervalFunction_le
    (terms : List (ℝ × Interval F)) (p : ℝ≥0 × Omega) :
    |signedIntervalFunction terms p| ≤
      signedIntervalCoefficientBound terms := by
  induction terms with
  | nil => simp [signedIntervalCoefficientBound]
  | cons term terms ih =>
      change
        |signedIntervalTermFunction term p +
            signedIntervalFunction terms p| ≤
          |term.1| + signedIntervalCoefficientBound terms
      calc
        |signedIntervalTermFunction term p +
            signedIntervalFunction terms p| ≤
            |signedIntervalTermFunction term p| +
              |signedIntervalFunction terms p| := abs_add_le _ _
        _ ≤ |term.1| + signedIntervalCoefficientBound terms := by
          apply add_le_add
          · unfold signedIntervalTermFunction
            by_cases hp : p ∈ term.2.carrier <;> simp [hp]
          · exact ih

/-- Every actual elementary approximation has the same deterministic
coefficient bound as its raw signed interval function. -/
theorem abs_signedElementaryApproximation_integrand_le
    (terms : List (ℝ × Interval F)) (n : ℕ)
    (t : ℝ≥0) (omega : Omega) :
    |(signedElementaryApproximation terms n).integrand t omega| ≤
      signedIntervalCoefficientBound terms := by
  induction terms with
  | nil =>
      simp [signedElementaryApproximation,
        PredictableElementaryStrategy.integrand,
        signedIntervalCoefficientBound]
  | cons term terms ih =>
      change
        |(term.2.scaledElementaryApproximation term.1 n).integrand t omega +
            (signedElementaryApproximation terms n).integrand t omega| ≤
          |term.1| + signedIntervalCoefficientBound terms
      calc
        |(term.2.scaledElementaryApproximation term.1 n).integrand t omega +
            (signedElementaryApproximation terms n).integrand t omega| ≤
            |(term.2.scaledElementaryApproximation term.1 n).integrand t omega| +
              |(signedElementaryApproximation terms n).integrand t omega| :=
          abs_add_le _ _
        _ ≤ |term.1| + signedIntervalCoefficientBound terms := by
          apply add_le_add
          · rw [term.2.scaledElementaryApproximation_integrand]
            by_cases hp : (t, omega) ∈
                term.2.elementaryApproximationCarrier n <;> simp [hp]
          · exact ih

/-- The error between an actual approximation and its raw signed interval
function is bounded uniformly in the foretelling index. -/
theorem dist_signedElementaryApproximation_le
    (terms : List (ℝ × Interval F)) (n : ℕ)
    (p : ℝ≥0 × Omega) :
    dist ((signedElementaryApproximation terms n).integrand p.1 p.2)
        (signedIntervalFunction terms p) ≤
      2 * signedIntervalCoefficientBound terms := by
  rw [Real.dist_eq]
  calc
    |(signedElementaryApproximation terms n).integrand p.1 p.2 -
        signedIntervalFunction terms p| ≤
        |(signedElementaryApproximation terms n).integrand p.1 p.2| +
          |signedIntervalFunction terms p| := abs_sub _ _
    _ ≤ signedIntervalCoefficientBound terms +
        signedIntervalCoefficientBound terms :=
      add_le_add
        (abs_signedElementaryApproximation_integrand_le
          terms n p.1 p.2)
        (abs_signedIntervalFunction_le terms p)
    _ = 2 * signedIntervalCoefficientBound terms := by ring

/-- The approximation error is supported exactly on its predictable
mismatch set. -/
theorem signedElementaryApproximation_sub_eq_mismatchIndicator
    (terms : List (ℝ × Interval F)) (n : ℕ) :
    ((fun p =>
        (signedElementaryApproximation terms n).integrand p.1 p.2) -
          signedIntervalFunction terms) =
      (signedElementaryMismatch terms n).indicator (fun p =>
        (signedElementaryApproximation terms n).integrand p.1 p.2 -
          signedIntervalFunction terms p) := by
  funext p
  change
    (signedElementaryApproximation terms n).integrand p.1 p.2 -
        signedIntervalFunction terms p =
      (signedElementaryMismatch terms n).indicator (fun p =>
        (signedElementaryApproximation terms n).integrand p.1 p.2 -
          signedIntervalFunction terms p) p
  by_cases hp : p ∈ signedElementaryMismatch terms n
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp]
    have heq :
        (signedElementaryApproximation terms n).integrand p.1 p.2 =
          signedIntervalFunction terms p := by
      by_contra hne
      exact hp hne
    rw [heq, sub_self]

/-- Actual elementary approximations converge to their raw signed interval
function in every finite-exponent `L^p` control which does not charge the
time-zero slice. -/
theorem signedElementaryApproximation_tendsto_eLpNorm
    (terms : List (ℝ × Interval F))
    (nu : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu]
    (hzero : nu
      (Interval.timeZeroSlice : Set (ℝ≥0 × Omega)) = 0)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    Tendsto (fun n => eLpNorm
      ((fun x =>
        (signedElementaryApproximation terms n).integrand x.1 x.2) -
          signedIntervalFunction terms) p nu) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon hepsilon
  obtain ⟨eta, hetaPos, heta⟩ :=
    exists_eLpNorm_indicator_le (μ := nu) hp
      (2 * signedIntervalCoefficientBound terms) hepsilon.ne'
  have hMeasureEventually : ∀ᶠ n in atTop,
      nu (signedElementaryMismatch terms n) ≤ (eta : ℝ≥0∞) :=
    ENNReal.tendsto_nhds_zero.mp
      (tendsto_measure_signedElementaryMismatch terms nu hzero)
      (eta : ℝ≥0∞) (by exact_mod_cast hetaPos)
  filter_upwards [hMeasureEventually] with n hn
  rw [signedElementaryApproximation_sub_eq_mismatchIndicator]
  calc
    eLpNorm ((signedElementaryMismatch terms n).indicator (fun x =>
        (signedElementaryApproximation terms n).integrand x.1 x.2 -
          signedIntervalFunction terms x)) p nu ≤
        eLpNorm ((signedElementaryMismatch terms n).indicator
          (fun _ => 2 * signedIntervalCoefficientBound terms)) p nu := by
      apply eLpNorm_mono
        (((signedElementaryApproximation terms n).integrand_isStronglyPredictable.sub
          (signedIntervalFunction_stronglyMeasurable terms)).aestronglyMeasurable.indicator
            (measurableSet_signedElementaryMismatch terms n))
      intro x
      by_cases hx : x ∈ signedElementaryMismatch terms n
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        change
          |(signedElementaryApproximation terms n).integrand x.1 x.2 -
              signedIntervalFunction terms x| ≤
            |2 * signedIntervalCoefficientBound terms|
        rw [abs_of_nonneg (mul_nonneg (by norm_num)
          (signedIntervalCoefficientBound_nonneg terms))]
        simpa only [Real.dist_eq] using
          dist_signedElementaryApproximation_le terms n x
      · simp [Set.indicator_of_notMem hx]
    _ ≤ epsilon := heta _ hn
      (measurableSet_signedElementaryMismatch terms n).nullMeasurableSet

/-- One concrete predictable elementary strategy approximates a strongly
predictable integrand simultaneously for two finite controls and two
finite exponents.  Its blockwise absolute coefficient sum has one
deterministic bound, so the same witness can be passed to the elementary
`M² ⊕ A¹` realization rather than only used as a raw integrand. -/
theorem exists_elementary_eLpNorm_sub_lt_two_with_coefficientBound
    (nu rho : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    (hNuZero : nu
      (Interval.timeZeroSlice : Set (ℝ≥0 × Omega)) = 0)
    (hRhoZero : rho
      (Interval.timeZeroSlice : Set (ℝ≥0 × Omega)) = 0)
    (p q : ℝ≥0∞) (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : ℝ≥0 × Omega → ℝ)
    (hf : StronglyMeasurable[F.predictable] f)
    (hfP : MemLp f p nu) (hfQ : MemLp f q rho)
    {epsilon : ℝ≥0∞} (hepsilon : epsilon ≠ 0) :
    ∃ H : PredictableElementaryStrategy F,
      eLpNorm (f - Function.uncurry H.integrand) p nu < epsilon ∧
      eLpNorm (f - Function.uncurry H.integrand) q rho < epsilon ∧
      ∃ C : ℝ≥0, ∀ omega, H.coefficientAbsSum omega ≤ C := by
  let : MeasurableSpace (ℝ≥0 × Omega) := F.predictable
  obtain ⟨deltaP, hdeltaPPos, hdeltaP⟩ :=
    exists_Lp_half ℝ nu p hepsilon
  obtain ⟨deltaQ, hdeltaQPos, hdeltaQ⟩ :=
    exists_Lp_half ℝ rho q hepsilon
  let eta : ℝ≥0∞ := min deltaP deltaQ
  have hetaPos : 0 < eta := lt_min hdeltaPPos hdeltaQPos
  obtain ⟨terms, hRawP, hRawQ⟩ :=
    exists_intervalSimpleFunction_eLpNorm_sub_lt_two
      nu rho p q hp hq f hf hfP hfQ hetaPos.ne'
  have hApproxP : Tendsto (fun n => eLpNorm
      ((fun x =>
          (intervalSimpleElementaryApproximation terms n).integrand
            x.1 x.2) - intervalSimpleFunction terms) p nu)
      atTop (𝓝 0) := by
    simpa only [intervalSimpleElementaryApproximation,
      signedIntervalFunction_linearizeIntervalSimpleTerms,
      Pi.sub_apply] using
        signedElementaryApproximation_tendsto_eLpNorm
          (linearizeIntervalSimpleTerms terms) nu hNuZero p hp
  have hApproxQ : Tendsto (fun n => eLpNorm
      ((fun x =>
          (intervalSimpleElementaryApproximation terms n).integrand
            x.1 x.2) - intervalSimpleFunction terms) q rho)
      atTop (𝓝 0) := by
    simpa only [intervalSimpleElementaryApproximation,
      signedIntervalFunction_linearizeIntervalSimpleTerms,
      Pi.sub_apply] using
        signedElementaryApproximation_tendsto_eLpNorm
          (linearizeIntervalSimpleTerms terms) rho hRhoZero q hq
  have hEventuallyP : ∀ᶠ n in atTop,
      eLpNorm (intervalSimpleFunction terms - (fun x =>
        (intervalSimpleElementaryApproximation terms n).integrand
          x.1 x.2)) p nu ≤ eta := by
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hApproxP eta hetaPos] with n hn
    rw [eLpNorm_sub_comm]
    exact hn
  have hEventuallyQ : ∀ᶠ n in atTop,
      eLpNorm (intervalSimpleFunction terms - (fun x =>
        (intervalSimpleElementaryApproximation terms n).integrand
          x.1 x.2)) q rho ≤ eta := by
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hApproxQ eta hetaPos] with n hn
    rw [eLpNorm_sub_comm]
    exact hn
  obtain ⟨n, hnP, hnQ⟩ := (hEventuallyP.and hEventuallyQ).exists
  let H : PredictableElementaryStrategy F :=
    intervalSimpleElementaryApproximation terms n
  have hFirstMeasP : AEStronglyMeasurable
      (f - intervalSimpleFunction terms) nu :=
    hf.aestronglyMeasurable.sub
      (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable
  have hSecondMeasP : AEStronglyMeasurable
      (intervalSimpleFunction terms - Function.uncurry H.integrand) nu :=
    (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable.sub
      H.integrand_isStronglyPredictable.aestronglyMeasurable
  have hFirstMeasQ : AEStronglyMeasurable
      (f - intervalSimpleFunction terms) rho :=
    hf.aestronglyMeasurable.sub
      (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable
  have hSecondMeasQ : AEStronglyMeasurable
      (intervalSimpleFunction terms - Function.uncurry H.integrand) rho :=
    (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable.sub
      H.integrand_isStronglyPredictable.aestronglyMeasurable
  refine ⟨H, ?_, ?_, ?_⟩
  · have hError :
        f - Function.uncurry H.integrand =
          (f - intervalSimpleFunction terms) +
            (intervalSimpleFunction terms -
              Function.uncurry H.integrand) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hError]
    exact hdeltaP _ _
      (hRawP.le.trans (min_le_left _ _))
      (hnP.trans (min_le_left _ _))
  · have hError :
        f - Function.uncurry H.integrand =
          (f - intervalSimpleFunction terms) +
            (intervalSimpleFunction terms -
              Function.uncurry H.integrand) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hError]
    exact hdeltaQ _ _
      (hRawQ.le.trans (min_le_right _ _))
      (hnQ.trans (min_le_right _ _))
  · let C : ℝ≥0 := ⟨signedIntervalCoefficientBound
        (linearizeIntervalSimpleTerms terms),
      signedIntervalCoefficientBound_nonneg
        (linearizeIntervalSimpleTerms terms)⟩
    refine ⟨C, ?_⟩
    intro omega
    change
      (signedElementaryApproximation
          (linearizeIntervalSimpleTerms terms) n).coefficientAbsSum omega ≤
        (C : ℝ)
    rw [coefficientAbsSum_signedElementaryApproximation]
    exact le_rfl

end PredictableIntervalAlgebra

end FTAPTheorem42
