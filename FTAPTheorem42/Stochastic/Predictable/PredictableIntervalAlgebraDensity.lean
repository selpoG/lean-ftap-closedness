/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalAlgebra
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Density of predictable interval-algebra functions

Finite unions of foretold stochastic intervals generate the predictable
sigma algebra.  For every finite predictable control measure, this module
upgrades that generating statement to an `L^p` density theorem.

The approximating functions are concrete finite sums

`sum_j c_j 1_(carrier L_j)`,

where every `L_j` is a finite list of foretold stochastic intervals.  This
is the set-level normal form needed before replacing the foretold endpoints
by finite stopping-time elementary blocks.
-/

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal symmDiff

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableIntervalAlgebra

variable {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega)}

/-- One scalar multiple of the indicator of a finite interval-algebra
carrier. -/
noncomputable def intervalTermFunction
    (term : ℝ × List (Interval F)) : ℝ≥0 × Omega → ℝ :=
  (carrier term.2).indicator fun _ => term.1

/-- A finite linear combination of interval-algebra carriers. -/
noncomputable def intervalSimpleFunction
    (terms : List (ℝ × List (Interval F))) : ℝ≥0 × Omega → ℝ :=
  (terms.map intervalTermFunction).sum

@[simp]
theorem intervalSimpleFunction_nil :
    intervalSimpleFunction ([] : List (ℝ × List (Interval F))) = 0 := by
  rfl

@[simp]
theorem intervalSimpleFunction_cons
    (term : ℝ × List (Interval F))
    (terms : List (ℝ × List (Interval F))) :
    intervalSimpleFunction (term :: terms) =
      intervalTermFunction term + intervalSimpleFunction terms := by
  rfl

@[simp]
theorem intervalSimpleFunction_append
    (left right : List (ℝ × List (Interval F))) :
    intervalSimpleFunction (left ++ right) =
      intervalSimpleFunction left + intervalSimpleFunction right := by
  unfold intervalSimpleFunction
  rw [List.map_append, List.sum_append]

/-- Every interval-algebra simple function is strongly measurable for the
predictable sigma algebra. -/
theorem intervalSimpleFunction_stronglyMeasurable
    (terms : List (ℝ × List (Interval F))) :
    StronglyMeasurable[F.predictable]
      (intervalSimpleFunction terms) := by
  induction terms with
  | nil =>
      exact stronglyMeasurable_zero
  | cons term terms ih =>
      rw [intervalSimpleFunction_cons]
      apply StronglyMeasurable.add
      · unfold intervalTermFunction
        apply StronglyMeasurable.indicator stronglyMeasurable_const
        exact measurableSet_of_mem_sets (ℱ := F) (by
          exact ⟨term.2, rfl⟩)
      · exact ih

/-- Every predictable measurable set is approximable in symmetric-difference
measure by a finite union of foretold stochastic intervals. -/
theorem exists_intervalSet_measure_symmDiff_lt
    (nu : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu]
    {s : Set (ℝ≥0 × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ t, t ∈ sets F ∧ nu (t ∆ s) < epsilon := by
  let : MeasurableSpace (ℝ≥0 × Omega) := F.predictable
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (isSetAlgebra_sets F).isSetRing
  · refine ⟨({Set.univ} : Set (Set (ℝ≥0 × Omega))),
      Set.countable_singleton Set.univ, ?_, ?_⟩
    · intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact (isSetAlgebra_sets F).univ_mem
    · simp
  · exact (generateFrom_sets F).symm
  · exact hs
  · exact hepsilon

/-- One interval-algebra function approximates a predictable simple
function simultaneously for two finite control measures and two finite
exponents.  In particular, the two approximation witnesses cannot diverge
between the martingale and finite-variation components. -/
theorem exists_intervalSimpleFunction_eLpNorm_sub_le_two_of_simple
    (nu rho : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    (p q : ℝ≥0∞) (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : @SimpleFunc (ℝ≥0 × Omega) F.predictable ℝ)
    {epsilon : ℝ≥0∞} (hepsilon : epsilon ≠ 0) :
    ∃ terms : List (ℝ × List (Interval F)),
      eLpNorm ((f : ℝ≥0 × Omega → ℝ) -
        intervalSimpleFunction terms) p nu ≤ epsilon ∧
      eLpNorm ((f : ℝ≥0 × Omega → ℝ) -
        intervalSimpleFunction terms) q rho ≤ epsilon := by
  classical
  let : MeasurableSpace (ℝ≥0 × Omega) := F.predictable
  let motive : SimpleFunc (ℝ≥0 × Omega) ℝ → Prop := fun simple =>
    ∀ {delta : ℝ≥0∞}, delta ≠ 0 →
      ∃ terms : List (ℝ × List (Interval F)),
        eLpNorm ((simple : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction terms) p nu ≤ delta ∧
        eLpNorm ((simple : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction terms) q rho ≤ delta
  apply (SimpleFunc.induction (motive := motive) ?_ ?_ f) hepsilon
  · intro c s hs delta hdelta
    obtain ⟨etaP, hetaPPos, hetaP⟩ :=
      exists_eLpNorm_indicator_le (μ := nu) hp c hdelta
    obtain ⟨etaQ, hetaQPos, hetaQ⟩ :=
      exists_eLpNorm_indicator_le (μ := rho) hq c hdelta
    let sigma : Measure (ℝ≥0 × Omega) := nu + rho
    let : IsFiniteMeasure sigma := by
      dsimp only [sigma]
      infer_instance
    obtain ⟨t, htSets, htMeasure⟩ :=
      exists_intervalSet_measure_symmDiff_lt sigma hs
        (show 0 < ((min etaP etaQ : ℝ≥0) : ℝ≥0∞) by
          exact_mod_cast lt_min hetaPPos hetaQPos)
    obtain ⟨intervals, hIntervals⟩ := htSets
    have hNu : nu (s ∆ t) ≤ etaP := by
      calc
        nu (s ∆ t) ≤ sigma (s ∆ t) := by
          exact (Measure.le_add_right (le_refl nu)) (s ∆ t)
        _ = sigma (t ∆ s) := by rw [symmDiff_comm]
        _ ≤ (min etaP etaQ : ℝ≥0) := htMeasure.le
        _ ≤ etaP := by exact_mod_cast min_le_left etaP etaQ
    have hRho : rho (s ∆ t) ≤ etaQ := by
      calc
        rho (s ∆ t) ≤ sigma (s ∆ t) := by
          exact (Measure.le_add_left (le_refl rho)) (s ∆ t)
        _ = sigma (t ∆ s) := by rw [symmDiff_comm]
        _ ≤ (min etaP etaQ : ℝ≥0) := htMeasure.le
        _ ≤ etaQ := by exact_mod_cast min_le_right etaP etaQ
    have ht : MeasurableSet t :=
      hIntervals ▸ measurableSet_of_mem_sets ⟨intervals, rfl⟩
    have hPiecewise :
        s.piecewise (Function.const (ℝ≥0 × Omega) c)
            (Function.const (ℝ≥0 × Omega) 0) =
          s.indicator (fun _ => c) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    refine ⟨[(c, intervals)], ?_, ?_⟩
    · simp only [intervalSimpleFunction_cons,
        intervalSimpleFunction_nil, add_zero, intervalTermFunction,
        hIntervals, SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
      rw [hPiecewise]
      rw [eLpNorm_indicator_sub_indicator _ hs.nullMeasurableSet ht.nullMeasurableSet]
      exact hetaP (s ∆ t) hNu (hs.symmDiff
        (hIntervals ▸ measurableSet_of_mem_sets ⟨intervals, rfl⟩)).nullMeasurableSet
    · simp only [intervalSimpleFunction_cons,
        intervalSimpleFunction_nil, add_zero, intervalTermFunction,
        hIntervals, SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
      rw [hPiecewise]
      rw [eLpNorm_indicator_sub_indicator _ hs.nullMeasurableSet ht.nullMeasurableSet]
      exact hetaQ (s ∆ t) hRho (hs.symmDiff
        (hIntervals ▸ measurableSet_of_mem_sets ⟨intervals, rfl⟩)).nullMeasurableSet
  · intro left right _hDisjoint hleft hright delta hdelta
    obtain ⟨deltaP, hdeltaPPos, hdeltaP⟩ :=
      exists_Lp_half ℝ nu p hdelta
    obtain ⟨deltaQ, hdeltaQPos, hdeltaQ⟩ :=
      exists_Lp_half ℝ rho q hdelta
    let eta : ℝ≥0∞ := min deltaP deltaQ
    have heta : eta ≠ 0 :=
      ne_of_gt (lt_min hdeltaPPos hdeltaQPos)
    obtain ⟨leftTerms, hleftP, hleftQ⟩ := hleft heta
    obtain ⟨rightTerms, hrightP, hrightQ⟩ := hright heta
    have hLeftMeasP : AEStronglyMeasurable
        ((left : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction leftTerms) nu :=
      left.aestronglyMeasurable.sub
        (intervalSimpleFunction_stronglyMeasurable
          leftTerms).aestronglyMeasurable
    have hRightMeasP : AEStronglyMeasurable
        ((right : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction rightTerms) nu :=
      right.aestronglyMeasurable.sub
        (intervalSimpleFunction_stronglyMeasurable
          rightTerms).aestronglyMeasurable
    have hLeftMeasQ : AEStronglyMeasurable
        ((left : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction leftTerms) rho :=
      left.aestronglyMeasurable.sub
        (intervalSimpleFunction_stronglyMeasurable
          leftTerms).aestronglyMeasurable
    have hRightMeasQ : AEStronglyMeasurable
        ((right : ℝ≥0 × Omega → ℝ) -
          intervalSimpleFunction rightTerms) rho :=
      right.aestronglyMeasurable.sub
        (intervalSimpleFunction_stronglyMeasurable
          rightTerms).aestronglyMeasurable
    refine ⟨leftTerms ++ rightTerms, ?_, ?_⟩
    · rw [intervalSimpleFunction_append, SimpleFunc.coe_add]
      have hError :
          (⇑left + ⇑right -
              (intervalSimpleFunction leftTerms +
                intervalSimpleFunction rightTerms)) =
            ((⇑left - intervalSimpleFunction leftTerms) +
              (⇑right - intervalSimpleFunction rightTerms)) := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [hError]
      exact (hdeltaP _ _
        (hleftP.trans (min_le_left _ _))
        (hrightP.trans (min_le_left _ _))).le
    · rw [intervalSimpleFunction_append, SimpleFunc.coe_add]
      have hError :
          (⇑left + ⇑right -
              (intervalSimpleFunction leftTerms +
                intervalSimpleFunction rightTerms)) =
            ((⇑left - intervalSimpleFunction leftTerms) +
              (⇑right - intervalSimpleFunction rightTerms)) := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [hError]
      exact (hdeltaQ _ _
        (hleftQ.trans (min_le_right _ _))
        (hrightQ.trans (min_le_right _ _))).le

/-- A single interval-algebra function approximates a predictable function
simultaneously in two finite-exponent spaces over two finite controls.  The
proof first chooses one measure-independent simple approximation and then
replaces that simple function by one common interval-algebra function. -/
theorem exists_intervalSimpleFunction_eLpNorm_sub_lt_two
    (nu rho : @Measure (ℝ≥0 × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    (p q : ℝ≥0∞) (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : ℝ≥0 × Omega → ℝ)
    (hf : StronglyMeasurable[F.predictable] f)
    (hfP : MemLp f p nu) (hfQ : MemLp f q rho)
    {epsilon : ℝ≥0∞} (hepsilon : epsilon ≠ 0) :
    ∃ terms : List (ℝ × List (Interval F)),
      eLpNorm (f - intervalSimpleFunction terms) p nu < epsilon ∧
      eLpNorm (f - intervalSimpleFunction terms) q rho < epsilon := by
  classical
  let : MeasurableSpace (ℝ≥0 × Omega) := F.predictable
  let : SeparableSpace (Set.range f ∪ {0} : Set ℝ) :=
    (hf.isSeparable_range.union (Set.finite_singleton 0).isSeparable).separableSpace
  let simple (n : ℕ) : SimpleFunc (ℝ≥0 × Omega) ℝ :=
    SimpleFunc.approxOn f hf.measurable (Set.range f ∪ {0}) 0 (by simp) n
  have hApproxP : Tendsto (fun n =>
      eLpNorm ((simple n : ℝ≥0 × Omega → ℝ) - f) p nu)
      atTop (𝓝 0) := by
    exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      hp hf.measurable hfP.eLpNorm_lt_top
  have hApproxQ : Tendsto (fun n =>
      eLpNorm ((simple n : ℝ≥0 × Omega → ℝ) - f) q rho)
      atTop (𝓝 0) := by
    exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      hq hf.measurable hfQ.eLpNorm_lt_top
  obtain ⟨deltaP, hdeltaPPos, hdeltaP⟩ :=
    exists_Lp_half ℝ nu p hepsilon
  obtain ⟨deltaQ, hdeltaQPos, hdeltaQ⟩ :=
    exists_Lp_half ℝ rho q hepsilon
  let eta : ℝ≥0∞ := min deltaP deltaQ
  have hetaPos : 0 < eta := lt_min hdeltaPPos hdeltaQPos
  have hEventuallyP : ∀ᶠ n in atTop,
      eLpNorm ((simple n : ℝ≥0 × Omega → ℝ) - f) p nu ≤ eta :=
    ENNReal.tendsto_nhds_zero.mp hApproxP eta hetaPos
  have hEventuallyQ : ∀ᶠ n in atTop,
      eLpNorm ((simple n : ℝ≥0 × Omega → ℝ) - f) q rho ≤ eta :=
    ENNReal.tendsto_nhds_zero.mp hApproxQ eta hetaPos
  obtain ⟨n, hnP, hnQ⟩ := (hEventuallyP.and hEventuallyQ).exists
  obtain ⟨terms, hTermsP, hTermsQ⟩ :=
    exists_intervalSimpleFunction_eLpNorm_sub_le_two_of_simple
      nu rho p q hp hq (simple n) hetaPos.ne'
  have hFirstMeasP : AEStronglyMeasurable
      (f - (simple n : ℝ≥0 × Omega → ℝ)) nu :=
    hf.aestronglyMeasurable.sub (simple n).aestronglyMeasurable
  have hSecondMeasP : AEStronglyMeasurable
      ((simple n : ℝ≥0 × Omega → ℝ) -
        intervalSimpleFunction terms) nu :=
    (simple n).aestronglyMeasurable.sub
      (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable
  have hFirstMeasQ : AEStronglyMeasurable
      (f - (simple n : ℝ≥0 × Omega → ℝ)) rho :=
    hf.aestronglyMeasurable.sub (simple n).aestronglyMeasurable
  have hSecondMeasQ : AEStronglyMeasurable
      ((simple n : ℝ≥0 × Omega → ℝ) -
        intervalSimpleFunction terms) rho :=
    (simple n).aestronglyMeasurable.sub
      (intervalSimpleFunction_stronglyMeasurable
        terms).aestronglyMeasurable
  have hFirstP : eLpNorm
      (f - (simple n : ℝ≥0 × Omega → ℝ)) p nu ≤ eta := by
    rw [eLpNorm_sub_comm]
    exact hnP
  have hFirstQ : eLpNorm
      (f - (simple n : ℝ≥0 × Omega → ℝ)) q rho ≤ eta := by
    rw [eLpNorm_sub_comm]
    exact hnQ
  refine ⟨terms, ?_, ?_⟩
  · have hError :
        f - intervalSimpleFunction terms =
          (f - (simple n : ℝ≥0 × Omega → ℝ)) +
            ((simple n : ℝ≥0 × Omega → ℝ) -
              intervalSimpleFunction terms) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hError]
    exact hdeltaP _ _
      (hFirstP.trans (min_le_left _ _))
      (hTermsP.trans (min_le_left _ _))
  · have hError :
        f - intervalSimpleFunction terms =
          (f - (simple n : ℝ≥0 × Omega → ℝ)) +
            ((simple n : ℝ≥0 × Omega → ℝ) -
              intervalSimpleFunction terms) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hError]
    exact hdeltaQ _ _
      (hFirstQ.trans (min_le_right _ _))
      (hTermsQ.trans (min_le_right _ _))

end PredictableIntervalAlgebra

end FTAPTheorem42
