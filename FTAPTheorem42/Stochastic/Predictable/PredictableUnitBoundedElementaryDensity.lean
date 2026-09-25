/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.PredictableIndicatorRing
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralAlgebra
import FTAPTheorem42.Stochastic.Predictable.PredictableCommonSimpleApproximation
import FTAPTheorem42.Stochastic.Topology.Emery.Completion

/-!
# Unit-bounded predictable elementary density

This module contains the first concrete bridge from strongly predictable
unit-bounded controls to the finite-horizon elementary test class.  The
construction is set-theoretic: a finite-valued predictable function is
decomposed into disjoint level sets, each level set is approximated in the
predictable interval ring, and the approximations are disjointized before
the corresponding elementary strategies are added.  Thus the pointwise
unit bound is retained by the one resulting elementary strategy.

The module deliberately stops at this density boundary.  It does not add a
range-closedness or component-compactness hypothesis.
-/

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal ProbabilityTheory symmDiff

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace PredictableUnitBoundedElementaryDensity

attribute [local instance] Classical.propDecidable

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

private def horizon (T : NNReal) : Set (NNReal × Omega) :=
  FiniteHorizonPredictableIndicatorRing.horizonCarrier
    (Omega := Omega) T

/-- A predictable interval-ring set together with its finite-horizon
elementary indicator representation.  The wrapper is local to the
construction and carries no analytic or stochastic endpoint. -/
private structure RingSet (T : NNReal) where
  carrier : Set (NNReal × Omega)
  measurable : MeasurableSet[F.predictable] carrier
  representation :
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T carrier

namespace RingSet

noncomputable def empty (T : NNReal) : RingSet (F := F) T where
  carrier := ∅
  measurable := @MeasurableSet.empty _ F.predictable
  representation :=
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.empty
      (F := F) T

noncomputable def union {T : NNReal} (s u : RingSet (F := F) T) :
    RingSet (F := F) T where
  carrier := s.carrier ∪ u.carrier
  measurable := s.measurable.union u.measurable
  representation :=
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.union
      s.representation u.representation

noncomputable def sdiff {T : NNReal} (s u : RingSet (F := F) T) :
    RingSet (F := F) T where
  carrier := s.carrier \ u.carrier
  measurable := s.measurable.diff u.measurable
  representation :=
    FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.sdiff
      s.representation u.representation

end RingSet

/-- A unit-bounded elementary strategy together with a ring carrier outside
which it vanishes on the positive finite horizon. -/
private structure UnitElementary (T : NNReal) where
  strategy : PredictableElementaryStrategy F
  carrier : RingSet (F := F) T
  coefficientBound : NNReal
  coefficientAbsSum_le : ∀ omega, strategy.coefficientAbsSum omega ≤ coefficientBound
  abs_integrand_le_one : ∀ t omega, |strategy.integrand t omega| ≤ 1
  integrand_eq_zero_of_not_mem :
    ∀ p, p ∉ carrier.carrier ∩ horizon T →
      strategy.integrand p.1 p.2 = 0

namespace UnitElementary

private theorem representation_integrand_eq_indicator_apply
    {T : NNReal} (R : RingSet (F := F) T) (p : NNReal × Omega) :
    R.representation.strategy.integrand p.1 p.2 =
      FiniteHorizonPredictableIndicatorRing.indicatorProcess
        (R.carrier ∩ horizon T) p.1 p.2 := by
  exact congrFun (congrFun R.representation.integrand_eq p.1) p.2

private theorem representation_abs_integrand_le_one
    {T : NNReal} (R : RingSet (F := F) T) (t : NNReal) (omega : Omega) :
    |R.representation.strategy.integrand t omega| ≤ 1 := by
  rw [representation_integrand_eq_indicator_apply R (t, omega)]
  unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
  split <;> norm_num

private theorem representation_integrand_eq_zero_of_not_mem
    {T : NNReal} (R : RingSet (F := F) T) (p : NNReal × Omega)
    (hp : p ∉ R.carrier ∩ horizon T) :
    R.representation.strategy.integrand p.1 p.2 = 0 := by
  rw [representation_integrand_eq_indicator_apply R p]
  unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
  simp [hp]

noncomputable def ofScalar {T : NNReal} (c : Real) (hc : |c| ≤ 1)
    (R : RingSet (F := F) T) :
    UnitElementary (F := F) T where
  strategy := R.representation.strategy.realSMul c
  carrier := R
  coefficientBound := PredictableElementaryStrategy.realSMulCoefficientBound c
    R.representation.bound
  coefficientAbsSum_le := by
    intro omega
    exact PredictableElementaryStrategy.coefficientAbsSum_realSMul_le c
      R.representation.strategy R.representation.bound
      R.representation.coefficientAbsSum_le omega
  abs_integrand_le_one := by
    intro t omega
    rw [PredictableElementaryStrategy.realSMul_integrand]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    by_cases hp : (t, omega) ∈ R.carrier ∩ horizon T
    · rw [representation_integrand_eq_indicator_apply R (t, omega)]
      unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
      split_ifs with h
      · simpa [h] using hc
      · simpa using hc
    · rw [representation_integrand_eq_zero_of_not_mem R (t, omega) hp]
      simp
  integrand_eq_zero_of_not_mem := by
    intro p hp
    rw [PredictableElementaryStrategy.realSMul_integrand]
    change c * R.representation.strategy.integrand p.1 p.2 = 0
    rw [representation_integrand_eq_zero_of_not_mem R p hp]
    simp

noncomputable def addDisjoint {T : NNReal}
    (s u : UnitElementary (F := F) T) : UnitElementary (F := F) T := by
  let difference := RingSet.sdiff u.carrier s.carrier
  exact
    { strategy := s.strategy ++
        (u.strategy.mul difference.representation.strategy)
      carrier := RingSet.union s.carrier u.carrier
      coefficientBound := s.coefficientBound +
        u.coefficientBound * difference.representation.bound
      coefficientAbsSum_le := by
        intro omega
        rw [PredictableElementaryStrategy.coefficientAbsSum_append,
          PredictableElementaryStrategy.coefficientAbsSum_mul]
        have hMul := mul_le_mul (u.coefficientAbsSum_le omega)
          (difference.representation.coefficientAbsSum_le omega)
          (difference.representation.strategy.coefficientAbsSum_nonneg omega)
          (by positivity)
        calc
          s.strategy.coefficientAbsSum omega +
              u.strategy.coefficientAbsSum omega *
                difference.representation.strategy.coefficientAbsSum omega ≤
            (s.coefficientBound : Real) +
              (u.coefficientBound : Real) *
                (difference.representation.bound : Real) :=
            add_le_add (s.coefficientAbsSum_le omega) hMul
          _ = ((s.coefficientBound +
              u.coefficientBound * difference.representation.bound : NNReal) : Real) := by
            norm_cast
      abs_integrand_le_one := by
        intro t omega
        by_cases hp : (t, omega) ∈
            s.carrier.carrier ∩ horizon T
        · have hDiff : (t, omega) ∉
              difference.carrier ∩ horizon T := by
            intro h
            exact h.1.2 hp.1
          rw [PredictableElementaryStrategy.append_integrand,
            PredictableElementaryStrategy.mul_integrand]
          simp only [Pi.add_apply, Pi.mul_apply]
          have hdValue : difference.representation.strategy.integrand t omega =
              FiniteHorizonPredictableIndicatorRing.indicatorProcess
                (difference.carrier ∩ horizon T) t omega :=
            congrFun (congrFun difference.representation.integrand_eq t) omega
          rw [hdValue]
          unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
          rw [ite_eq_right hDiff, mul_zero, add_zero]
          exact s.abs_integrand_le_one t omega
        · have hsZero := s.integrand_eq_zero_of_not_mem
            (t, omega) hp
          rw [PredictableElementaryStrategy.append_integrand,
            PredictableElementaryStrategy.mul_integrand]
          simp only [Pi.add_apply, Pi.mul_apply, hsZero, zero_add]
          have hD : |difference.representation.strategy.integrand t omega| ≤ 1 :=
            representation_abs_integrand_le_one difference t omega
          calc
            |u.strategy.integrand t omega *
                difference.representation.strategy.integrand t omega| =
                |u.strategy.integrand t omega| *
                  |difference.representation.strategy.integrand t omega| := by
                    rw [abs_mul]
            _ ≤ |u.strategy.integrand t omega| * 1 :=
              mul_le_mul_of_nonneg_left hD (abs_nonneg _)
            _ = |u.strategy.integrand t omega| := by ring
            _ ≤ 1 := u.abs_integrand_le_one t omega
      integrand_eq_zero_of_not_mem := by
        intro p hp
        rw [PredictableElementaryStrategy.append_integrand,
          PredictableElementaryStrategy.mul_integrand]
        simp only [Pi.add_apply, Pi.mul_apply]
        have hsZero : s.strategy.integrand p.1 p.2 = 0 := by
          apply s.integrand_eq_zero_of_not_mem p
          intro h
          exact hp ⟨Or.inl h.1, h.2⟩
        have huZero : u.strategy.integrand p.1 p.2 = 0 := by
          apply u.integrand_eq_zero_of_not_mem p
          intro h
          exact hp ⟨Or.inr h.1, h.2⟩
        simp [hsZero, huZero] }

end UnitElementary

private theorem exists_ringSet_measure_symmDiff_lt
    (T : NNReal)
    (nu : @Measure (NNReal × Omega) F.predictable)
    [IsFiniteMeasure nu]
    {s : Set (NNReal × Omega)}
    (hs : MeasurableSet[F.predictable] s)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ R : RingSet (F := F) T, nu (R.carrier ∆ s) < epsilon := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  obtain ⟨t, htSets, htMeasure⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := nu)
      (FiniteHorizonPredictableIndicatorRing.isSetRing_sets
        (F := F) T)
      (by
        refine ⟨({Set.univ} : Set (Set (NNReal × Omega))),
          Set.countable_singleton Set.univ, ?_, ?_⟩
        · intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu]
          exact ⟨@MeasurableSet.univ _ F.predictable,
            ⟨FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation.univ
              (F := F) T⟩⟩
        · simp)
      (FiniteHorizonPredictableIndicatorRing.generateFrom_sets
        (F := F) T).symm hs hepsilon
  let R : FiniteHorizonPredictableIndicatorRing.BoundedIndicatorRepresentation
      (F := F) T t := Classical.choice htSets.2
  exact ⟨{ carrier := t, measurable := htSets.1, representation := R }, htMeasure⟩

private theorem exists_unitElementary_atom
    (T : NNReal)
    (nu rho : @Measure (NNReal × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    {s : Set (NNReal × Omega)} (hs : MeasurableSet[F.predictable] s)
    (hsH : s ⊆ horizon T) (c : Real) (hc : |c| ≤ 1)
    {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
    ∃ U : UnitElementary (F := F) T,
      eLpNorm (s.indicator (fun _ => c) -
        Function.uncurry U.strategy.integrand) 2 nu ≤ epsilon ∧
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - s.indicator (fun _ => (1 : Real)))
          2 nu ≤ epsilon ∧
      eLpNorm (s.indicator (fun _ => c) -
        Function.uncurry U.strategy.integrand) 1 rho ≤ epsilon ∧
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - s.indicator (fun _ => (1 : Real)))
          1 rho ≤ epsilon := by
  let sigma : @Measure (NNReal × Omega) F.predictable := nu + rho
  obtain ⟨etaP, hetaPPos, hetaP⟩ :=
    exists_eLpNorm_indicator_le (μ := nu) (p := (2 : ENNReal))
      (by norm_num) c hepsilon
  obtain ⟨etaQ, hetaQPos, hetaQ⟩ :=
    exists_eLpNorm_indicator_le (μ := rho) (p := (1 : ENNReal))
      (by norm_num) c hepsilon
  obtain ⟨etaPone, hetaPonePos, hetaPone⟩ :=
    exists_eLpNorm_indicator_le (μ := nu) (p := (2 : ENNReal))
      (by norm_num) (1 : Real) hepsilon
  obtain ⟨etaQone, hetaQonePos, hetaQone⟩ :=
    exists_eLpNorm_indicator_le (μ := rho) (p := (1 : ENNReal))
      (by norm_num) (1 : Real) hepsilon
  have hetaPPos' : (0 : ENNReal) < etaP := by exact_mod_cast hetaPPos
  have hetaQPos' : (0 : ENNReal) < etaQ := by exact_mod_cast hetaQPos
  have hetaPonePos' : (0 : ENNReal) < etaPone := by
    exact_mod_cast hetaPonePos
  have hetaQonePos' : (0 : ENNReal) < etaQone := by
    exact_mod_cast hetaQonePos
  let eta : ENNReal :=
    min (min (etaP : ENNReal) (etaQ : ENNReal))
      (min (etaPone : ENNReal) (etaQone : ENNReal))
  have hetaPos : 0 < eta := by
    exact lt_min (lt_min hetaPPos' hetaQPos')
      (lt_min hetaPonePos' hetaQonePos')
  obtain ⟨R, htMeasure⟩ :=
    exists_ringSet_measure_symmDiff_lt T sigma hs hetaPos
  have hNu : nu (s ∆ R.carrier) ≤ etaP := by
    calc
      nu (s ∆ R.carrier) ≤ sigma (s ∆ R.carrier) := by
        exact (Measure.le_add_right (le_refl nu)) (s ∆ R.carrier)
      _ = sigma (R.carrier ∆ s) := by rw [symmDiff_comm]
      _ ≤ eta := htMeasure.le
      _ ≤ etaP := (min_le_left _ _).trans (min_le_left _ _)
  have hRho : rho (s ∆ R.carrier) ≤ etaQ := by
    calc
      rho (s ∆ R.carrier) ≤ sigma (s ∆ R.carrier) := by
        exact (Measure.le_add_left (le_refl rho)) (s ∆ R.carrier)
      _ = sigma (R.carrier ∆ s) := by rw [symmDiff_comm]
      _ ≤ eta := htMeasure.le
      _ ≤ etaQ := (min_le_left _ _).trans (min_le_right _ _)
  have hNuOne : nu (s ∆ R.carrier) ≤ etaPone := by
    calc
      nu (s ∆ R.carrier) ≤ sigma (s ∆ R.carrier) := by
        exact (Measure.le_add_right (le_refl nu)) (s ∆ R.carrier)
      _ = sigma (R.carrier ∆ s) := by rw [symmDiff_comm]
      _ ≤ eta := htMeasure.le
      _ ≤ etaPone := (min_le_right _ _).trans (min_le_left _ _)
  have hRhoOne : rho (s ∆ R.carrier) ≤ etaQone := by
    calc
      rho (s ∆ R.carrier) ≤ sigma (s ∆ R.carrier) := by
        exact (Measure.le_add_left (le_refl rho)) (s ∆ R.carrier)
      _ = sigma (R.carrier ∆ s) := by rw [symmDiff_comm]
      _ ≤ eta := htMeasure.le
      _ ≤ etaQone := (min_le_right _ _).trans (min_le_right _ _)
  let U : UnitElementary (F := F) T := UnitElementary.ofScalar c hc R
  have hOutput :
      Function.uncurry U.strategy.integrand =
        (R.carrier ∩ horizon T).indicator (fun _ => c) := by
    funext p
    change (R.representation.strategy.realSMul c).integrand p.1 p.2 = _
    rw [PredictableElementaryStrategy.realSMul_integrand]
    change c * R.representation.strategy.integrand p.1 p.2 = _
    rw [R.representation.integrand_eq]
    unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
    split_ifs with h
    · simp [horizon, h]
    · simp [horizon, h]
  have hSub : s ∆ (R.carrier ∩ horizon T) ⊆ s ∆ R.carrier := by
    intro p hp
    rw [Set.mem_symmDiff] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl ⟨hp.1, fun hpr => hp.2 ⟨hpr, hsH hp.1⟩⟩
    · exact Or.inr ⟨hp.1.1, hp.2⟩
  have hNuInter : nu (s ∆ (R.carrier ∩ horizon T)) ≤ etaP :=
    (measure_mono hSub).trans hNu
  have hRhoInter : rho (s ∆ (R.carrier ∩ horizon T)) ≤ etaQ :=
    (measure_mono hSub).trans hRho
  have hNuOneInter : nu (s ∆ (R.carrier ∩ horizon T)) ≤ etaPone :=
    (measure_mono hSub).trans hNuOne
  have hRhoOneInter : rho (s ∆ (R.carrier ∩ horizon T)) ≤ etaQone :=
    (measure_mono hSub).trans hRhoOne
  have hRMeas : MeasurableSet[F.predictable] (R.carrier ∩ horizon T) :=
    R.measurable.inter (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T)
  have hErrP :
      eLpNorm (s.indicator (fun _ => c) -
        Function.uncurry U.strategy.integrand) 2 nu ≤ epsilon := by
    rw [hOutput, eLpNorm_indicator_sub_indicator _ hs.nullMeasurableSet hRMeas.nullMeasurableSet]
    exact hetaP _ hNuInter (hs.symmDiff hRMeas).nullMeasurableSet
  have hErrQ :
      eLpNorm (s.indicator (fun _ => c) -
        Function.uncurry U.strategy.integrand) 1 rho ≤ epsilon := by
    rw [hOutput, eLpNorm_indicator_sub_indicator _ hs.nullMeasurableSet hRMeas.nullMeasurableSet]
    exact hetaQ _ hRhoInter (hs.symmDiff hRMeas).nullMeasurableSet
  have hSupportP :
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - s.indicator (fun _ => (1 : Real)))
          2 nu ≤ epsilon := by
    change eLpNorm ((R.carrier ∩ horizon T).indicator (fun _ => (1 : Real)) -
      s.indicator (fun _ => (1 : Real))) _ _ ≤ epsilon
    rw [eLpNorm_indicator_sub_indicator _ hRMeas.nullMeasurableSet hs.nullMeasurableSet]
    exact hetaPone _ (by
      simpa [U, UnitElementary.ofScalar, symmDiff_comm] using hNuOneInter)
      (hRMeas.symmDiff hs).nullMeasurableSet
  have hSupportQ :
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - s.indicator (fun _ => (1 : Real)))
          1 rho ≤ epsilon := by
    change eLpNorm ((R.carrier ∩ horizon T).indicator (fun _ => (1 : Real)) -
      s.indicator (fun _ => (1 : Real))) _ _ ≤ epsilon
    rw [eLpNorm_indicator_sub_indicator _ hRMeas.nullMeasurableSet hs.nullMeasurableSet]
    exact hetaQone _ (by
      simpa [U, UnitElementary.ofScalar, symmDiff_comm] using hRhoOneInter)
      (hRMeas.symmDiff hs).nullMeasurableSet
  exact ⟨U, hErrP, hSupportP, hErrQ, hSupportQ⟩

private theorem exists_unitElementary_of_simple
    (T : NNReal)
    (nu rho : @Measure (NNReal × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    (s : @SimpleFunc (NNReal × Omega) F.predictable Real)
    (hsBound : ∀ p, |s p| ≤ 1)
    (hsH : ∀ p, p ∉ horizon T → s p = 0)
    {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
    ∃ U : UnitElementary (F := F) T,
      eLpNorm ((s : (NNReal × Omega) → Real) -
        Function.uncurry U.strategy.integrand) 2 nu ≤ epsilon ∧
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - (Function.support (s : (NNReal × Omega) → Real)).indicator
            (fun _ => (1 : Real))) 2 nu ≤ epsilon ∧
      eLpNorm ((s : (NNReal × Omega) → Real) -
        Function.uncurry U.strategy.integrand) 1 rho ≤ epsilon ∧
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
          (fun _ => (1 : Real))) - (Function.support (s : (NNReal × Omega) → Real)).indicator
            (fun _ => (1 : Real))) 1 rho ≤ epsilon := by
  let motive : @SimpleFunc (NNReal × Omega) F.predictable Real → Prop :=
    fun f =>
      ∀ {delta : ENNReal}, delta ≠ 0 →
        (∀ p, |f p| ≤ 1) →
        (∀ p, p ∉ horizon T → f p = 0) →
        ∃ U : UnitElementary (F := F) T,
          eLpNorm ((f : (NNReal × Omega) → Real) -
            Function.uncurry U.strategy.integrand) 2 nu ≤ delta ∧
          eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
              (fun _ => (1 : Real))) - (Function.support (f : (NNReal × Omega) → Real)).indicator
                (fun _ => (1 : Real))) 2 nu ≤ delta ∧
          eLpNorm ((f : (NNReal × Omega) → Real) -
            Function.uncurry U.strategy.integrand) 1 rho ≤ delta ∧
      eLpNorm (((U.carrier.carrier ∩ horizon T).indicator
              (fun _ => (1 : Real))) - (Function.support (f : (NNReal × Omega) → Real)).indicator
                (fun _ => (1 : Real))) 1 rho ≤ delta
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  refine (SimpleFunc.induction (motive := motive) ?_ ?_ s) hepsilon
    hsBound hsH
  · intro c A hA delta hdelta hfBound hfH
    by_cases hc0 : c = 0
    · let R := RingSet.empty (F := F) T
      let U : UnitElementary (F := F) T :=
        UnitElementary.ofScalar 0 (by norm_num) R
      have hZeroFun' :
          (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
              (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
            (NNReal × Omega) → Real) = 0 := by
        funext p
        simp [hc0]
      have hSupportZero :
          Function.support
              (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
                (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
                (NNReal × Omega) → Real) = ∅ := by
        rw [hZeroFun']
        simp
      have hIntegrandZero :
          Function.uncurry U.strategy.integrand = 0 := by
        funext p
        simp [U, R, UnitElementary.ofScalar, RingSet.empty, Function.uncurry]
      refine ⟨U, ?_, ?_, ?_, ?_⟩
      · rw [hZeroFun', hIntegrandZero]
        simp
      · rw [hSupportZero]
        simp [U, R, UnitElementary.ofScalar, RingSet.empty]
      · rw [hZeroFun', hIntegrandZero]
        simp
      · rw [hSupportZero]
        simp [U, R, UnitElementary.ofScalar, RingSet.empty]
    · by_cases hAempty : A.Nonempty
      · obtain ⟨x, hx⟩ := hAempty
        have hc : |c| ≤ 1 := by
          simpa [hx] using hfBound x
        have hAH : A ⊆ horizon T := by
          intro x hxA
          by_contra hxH
          have hzero := hfH x hxH
          have hconst : c = 0 := by
            simpa [SimpleFunc.coe_piecewise, hxA] using hzero
          exact hc0 hconst
        obtain ⟨U, hErrP, hSupportP, hErrQ, hSupportQ⟩ :=
          exists_unitElementary_atom T nu rho hA hAH c hc hdelta
        have hPiecewise :
            (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
                (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
              (NNReal × Omega) → Real) =
              A.indicator (fun _ => c) := by
          funext p
          by_cases hp : p ∈ A <;> simp [hp]
        have hSupportPiecewise :
            Function.support
                (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
                  (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
                  (NNReal × Omega) → Real) = A := by
          ext p
          by_cases hp : p ∈ A <;>
            simp [hp, hc0]
        refine ⟨U, ?_, ?_, ?_, ?_⟩
        · rw [hPiecewise]
          exact hErrP
        · rw [hSupportPiecewise]
          exact hSupportP
        · rw [hPiecewise]
          exact hErrQ
        · rw [hSupportPiecewise]
          exact hSupportQ
      · have hAeq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hAempty
        let R := RingSet.empty (F := F) T
        let U : UnitElementary (F := F) T :=
          UnitElementary.ofScalar 0 (by norm_num) R
        have hZeroFun' :
            (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
                (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
              (NNReal × Omega) → Real) = 0 := by
          funext p
          simp [hAeq]
        have hSupportZero :
            Function.support
                (SimpleFunc.piecewise A hA (SimpleFunc.const (NNReal × Omega) c)
                  (SimpleFunc.const (NNReal × Omega) (0 : Real)) :
                  (NNReal × Omega) → Real) = ∅ := by
          rw [hZeroFun']
          simp
        have hIntegrandZero :
            Function.uncurry U.strategy.integrand = 0 := by
          funext p
          simp [U, R, UnitElementary.ofScalar, RingSet.empty, Function.uncurry]
        refine ⟨U, ?_, ?_, ?_, ?_⟩
        · rw [hZeroFun', hIntegrandZero]
          simp
        · rw [hSupportZero]
          simp [U, R, UnitElementary.ofScalar, RingSet.empty]
        · rw [hZeroFun', hIntegrandZero]
          simp
        · rw [hSupportZero]
          simp [U, R, UnitElementary.ofScalar, RingSet.empty]
  · intro f g hfg hf hg delta hdelta hSumBound hSumH
    obtain ⟨deltaP, hdeltaPPos, hdeltaP⟩ :=
      exists_Lp_half Real nu (2 : ENNReal) hdelta
    obtain ⟨deltaQ, hdeltaQPos, hdeltaQ⟩ :=
      exists_Lp_half Real rho (1 : ENNReal) hdelta
    obtain ⟨etaPone, hetaPonePos, hetaPone⟩ :=
      exists_Lp_half Real nu (2 : ENNReal) hdeltaPPos.ne'
    obtain ⟨etaPtwo, hetaPtwoPos, hetaPtwo⟩ :=
      exists_Lp_half Real nu (2 : ENNReal) hdeltaPPos.ne'
    obtain ⟨etaQone, hetaQonePos, hetaQone⟩ :=
      exists_Lp_half Real rho (1 : ENNReal) hdeltaQPos.ne'
    obtain ⟨etaQtwo, hetaQtwoPos, hetaQtwo⟩ :=
      exists_Lp_half Real rho (1 : ENNReal) hdeltaQPos.ne'
    let eta : ENNReal :=
      min (min (min etaPone etaPtwo) (min deltaP deltaQ))
        (min (min etaQone etaQtwo) (min deltaP deltaQ))
    have hetaPos : 0 < eta := by
      exact lt_min
        (lt_min (lt_min hetaPonePos hetaPtwoPos)
          (lt_min hdeltaPPos hdeltaQPos))
        (lt_min (lt_min hetaQonePos hetaQtwoPos)
          (lt_min hdeltaPPos hdeltaQPos))
    have hEtaPone : eta ≤ etaPone := by
      dsimp [eta]
      exact (min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _))
    have hEtaPtwo : eta ≤ etaPtwo := by
      dsimp [eta]
      exact (min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _))
    have hEtaQone : eta ≤ etaQone := by
      dsimp [eta]
      exact (min_le_right _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _))
    have hEtaQtwo : eta ≤ etaQtwo := by
      dsimp [eta]
      exact (min_le_right _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _))
    have hEtaDeltaP : eta ≤ deltaP := by
      dsimp [eta]
      exact (min_le_left _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hEtaDeltaQ : eta ≤ deltaQ := by
      dsimp [eta]
      exact (min_le_left _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    have hSupportDisjoint :
        Disjoint (Function.support f) (Function.support g) := hfg
    have hfBound : ∀ p, |f p| ≤ 1 := by
      intro p
      by_cases hfp : f p = 0
      · simp [hfp]
      · have hgp : g p = 0 := by
          by_contra hgp
          exact Set.disjoint_left.1 hSupportDisjoint hfp hgp
        simpa [SimpleFunc.coe_add, hgp] using hSumBound p
    have hgBound : ∀ p, |g p| ≤ 1 := by
      intro p
      by_cases hgp : g p = 0
      · simp [hgp]
      · have hfp : f p = 0 := by
          by_contra hfp
          exact Set.disjoint_left.1 hSupportDisjoint hfp hgp
        simpa [SimpleFunc.coe_add, hfp] using hSumBound p
    have hfH : ∀ p, p ∉ horizon T → f p = 0 := by
      intro p hp
      by_contra hfp
      have hgp : g p = 0 := by
        by_contra hgp
        exact Set.disjoint_left.1 hSupportDisjoint hfp hgp
      have hsum := hSumH p hp
      exact hfp (by simpa [SimpleFunc.coe_add, hgp] using hsum)
    have hgH : ∀ p, p ∉ horizon T → g p = 0 := by
      intro p hp
      by_contra hgp
      have hfp : f p = 0 := by
        by_contra hfp
        exact Set.disjoint_left.1 hSupportDisjoint hfp hgp
      have hsum := hSumH p hp
      exact hgp (by simpa [SimpleFunc.coe_add, hfp] using hsum)
    obtain ⟨A, hErrAP, hSupportAP, hErrAQ, hSupportAQ⟩ :=
      hf hetaPos.ne' hfBound hfH
    obtain ⟨B, hErrBP, hSupportBP, hErrBQ, hSupportBQ⟩ :=
      hg hetaPos.ne' hgBound hgH
    let W := UnitElementary.addDisjoint A B
    let leftFun : (NNReal × Omega) → Real := f
    let rightFun : (NNReal × Omega) → Real := g
    let leftIntegrand : (NNReal × Omega) → Real :=
      Function.uncurry A.strategy.integrand
    let rightIntegrand : (NNReal × Omega) → Real :=
      Function.uncurry B.strategy.integrand
    let leftSupport : (NNReal × Omega) → Real :=
      (A.carrier.carrier ∩ horizon T).indicator (fun _ => (1 : Real))
    let rightSupport : (NNReal × Omega) → Real :=
      (B.carrier.carrier ∩ horizon T).indicator (fun _ => (1 : Real))
    let leftTargetSupport : (NNReal × Omega) → Real :=
      (Function.support (f : (NNReal × Omega) → Real)).indicator
        (fun _ => (1 : Real))
    let rightTargetSupport : (NNReal × Omega) → Real :=
      (Function.support (g : (NNReal × Omega) → Real)).indicator
        (fun _ => (1 : Real))
    let leftError : (NNReal × Omega) → Real := leftFun - leftIntegrand
    let rightError : (NNReal × Omega) → Real := rightFun - rightIntegrand
    have hLeftErrorMeasP :
        AEStronglyMeasurable leftError nu := by
      exact f.aestronglyMeasurable.sub
        A.strategy.integrand_isStronglyPredictable.aestronglyMeasurable
    have hRightErrorMeasP :
        AEStronglyMeasurable rightError nu := by
      exact g.aestronglyMeasurable.sub
        B.strategy.integrand_isStronglyPredictable.aestronglyMeasurable
    have hLeftErrorMeasQ :
        AEStronglyMeasurable leftError rho := by
      exact f.aestronglyMeasurable.sub
        A.strategy.integrand_isStronglyPredictable.aestronglyMeasurable
    have hRightErrorMeasQ :
        AEStronglyMeasurable rightError rho := by
      exact g.aestronglyMeasurable.sub
        B.strategy.integrand_isStronglyPredictable.aestronglyMeasurable
    have hLeftSupportMeasP :
        AEStronglyMeasurable leftSupport nu := by
      exact (stronglyMeasurable_const.indicator
        (A.carrier.measurable.inter
          (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier
            (F := F) T))).aestronglyMeasurable
    have hRightSupportMeasP :
        AEStronglyMeasurable rightSupport nu := by
      exact (stronglyMeasurable_const.indicator
        (B.carrier.measurable.inter
          (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier
            (F := F) T))).aestronglyMeasurable
    have hLeftSupportMeasQ :
        AEStronglyMeasurable leftSupport rho := by
      exact (stronglyMeasurable_const.indicator
        (A.carrier.measurable.inter
          (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier
            (F := F) T))).aestronglyMeasurable
    have hRightSupportMeasQ :
        AEStronglyMeasurable rightSupport rho := by
      exact (stronglyMeasurable_const.indicator
        (B.carrier.measurable.inter
          (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier
            (F := F) T))).aestronglyMeasurable
    have hLeftTargetSupportMeasP :
        AEStronglyMeasurable leftTargetSupport nu := by
      exact (stronglyMeasurable_const.indicator f.measurableSet_support).aestronglyMeasurable
    have hRightTargetSupportMeasP :
        AEStronglyMeasurable rightTargetSupport nu := by
      exact (stronglyMeasurable_const.indicator g.measurableSet_support).aestronglyMeasurable
    have hLeftTargetSupportMeasQ :
        AEStronglyMeasurable leftTargetSupport rho := by
      exact (stronglyMeasurable_const.indicator f.measurableSet_support).aestronglyMeasurable
    have hRightTargetSupportMeasQ :
        AEStronglyMeasurable rightTargetSupport rho := by
      exact (stronglyMeasurable_const.indicator g.measurableSet_support).aestronglyMeasurable
    have hLeftDiscMeasP :
        AEStronglyMeasurable (fun p => |leftSupport p - leftTargetSupport p|) nu := by
      exact (hLeftSupportMeasP.sub hLeftTargetSupportMeasP).norm
    have hRightDiscMeasP :
        AEStronglyMeasurable (fun p => |rightSupport p - rightTargetSupport p|) nu := by
      exact (hRightSupportMeasP.sub hRightTargetSupportMeasP).norm
    have hLeftDiscMeasQ :
        AEStronglyMeasurable (fun p => |leftSupport p - leftTargetSupport p|) rho := by
      exact (hLeftSupportMeasQ.sub hLeftTargetSupportMeasQ).norm
    have hRightDiscMeasQ :
        AEStronglyMeasurable (fun p => |rightSupport p - rightTargetSupport p|) rho := by
      exact (hRightSupportMeasQ.sub hRightTargetSupportMeasQ).norm
    have hErrAP' :
        eLpNorm (fun p => ‖leftError p‖) 2 nu ≤ etaPone := by
      simpa only [eLpNorm_norm _ hLeftErrorMeasP, leftError, leftFun, leftIntegrand] using
        (hErrAP.trans hEtaPone)
    have hErrBP' :
        eLpNorm (fun p => ‖rightError p‖) 2 nu ≤ etaPtwo := by
      simpa only [eLpNorm_norm _ hRightErrorMeasP, rightError, rightFun, rightIntegrand] using
        (hErrBP.trans hEtaPtwo)
    have hErrAQ' :
        eLpNorm (fun p => ‖leftError p‖) 1 rho ≤ etaQone := by
      simpa only [eLpNorm_norm _ hLeftErrorMeasQ, leftError, leftFun, leftIntegrand] using
        (hErrAQ.trans hEtaQone)
    have hErrBQ' :
        eLpNorm (fun p => ‖rightError p‖) 1 rho ≤ etaQtwo := by
      simpa only [eLpNorm_norm _ hRightErrorMeasQ, rightError, rightFun, rightIntegrand] using
        (hErrBQ.trans hEtaQtwo)
    have hSupportAP' :
        eLpNorm (fun p => ‖leftSupport p - leftTargetSupport p‖) 2 nu ≤ etaPone := by
      have h := hSupportAP.trans hEtaPone
      rw [← eLpNorm_norm _ (hLeftSupportMeasP.sub hLeftTargetSupportMeasP)] at h
      simpa [leftSupport, leftTargetSupport, Pi.sub_apply] using h
    have hSupportBP' :
        eLpNorm (fun p => ‖rightSupport p - rightTargetSupport p‖) 2 nu ≤ etaPone := by
      have h := hSupportBP.trans hEtaPone
      rw [← eLpNorm_norm _ (hRightSupportMeasP.sub hRightTargetSupportMeasP)] at h
      simpa [rightSupport, rightTargetSupport, Pi.sub_apply] using h
    have hSupportAQ' :
        eLpNorm (fun p => ‖leftSupport p - leftTargetSupport p‖) 1 rho ≤ etaQone := by
      have h := hSupportAQ.trans hEtaQone
      rw [← eLpNorm_norm _ (hLeftSupportMeasQ.sub hLeftTargetSupportMeasQ)] at h
      simpa [leftSupport, leftTargetSupport, Pi.sub_apply] using h
    have hSupportBQ' :
        eLpNorm (fun p => ‖rightSupport p - rightTargetSupport p‖) 1 rho ≤ etaQone := by
      have h := hSupportBQ.trans hEtaQone
      rw [← eLpNorm_norm _ (hRightSupportMeasQ.sub hRightTargetSupportMeasQ)] at h
      simpa [rightSupport, rightTargetSupport, Pi.sub_apply] using h
    have hLeftPairP :
        eLpNorm (fun p => |leftError p| +
          |leftSupport p - leftTargetSupport p|) 2 nu < deltaP := by
      have h := hetaPone (fun p => ‖leftError p‖)
          (fun p => ‖leftSupport p - leftTargetSupport p‖)
          hErrAP' hSupportAP'
      have hfun :
          (fun p => ‖leftError p‖) +
              (fun p => ‖leftSupport p - leftTargetSupport p‖) =
            (fun p => ‖leftError p‖ +
              ‖leftSupport p - leftTargetSupport p‖) := by
        funext p
        rfl
      have h' :
          eLpNorm (fun p => ‖leftError p‖ +
            ‖leftSupport p - leftTargetSupport p‖) 2 nu < deltaP := by
        rw [← hfun]
        exact h
      simpa [Real.norm_eq_abs] using h'
    have hRightPairP :
        eLpNorm (fun p => |rightError p| + |rightError p|) 2 nu < deltaP := by
      have h := hetaPtwo (fun p => ‖rightError p‖)
          (fun p => ‖rightError p‖)
          hErrBP' hErrBP'
      have hfun :
          (fun p => ‖rightError p‖) + (fun p => ‖rightError p‖) =
            (fun p => ‖rightError p‖ + ‖rightError p‖) := by
        funext p
        rfl
      have h' :
          eLpNorm (fun p => ‖rightError p‖ + ‖rightError p‖) 2 nu < deltaP := by
        rw [← hfun]
        exact h
      simpa [Real.norm_eq_abs] using h'
    have hLeftPairQ :
        eLpNorm (fun p => |leftError p| +
          |leftSupport p - leftTargetSupport p|) 1 rho < deltaQ := by
      have h := hetaQone (fun p => ‖leftError p‖)
          (fun p => ‖leftSupport p - leftTargetSupport p‖)
          hErrAQ' hSupportAQ'
      have hfun :
          (fun p => ‖leftError p‖) +
              (fun p => ‖leftSupport p - leftTargetSupport p‖) =
            (fun p => ‖leftError p‖ +
              ‖leftSupport p - leftTargetSupport p‖) := by
        funext p
        rfl
      have h' :
          eLpNorm (fun p => ‖leftError p‖ +
            ‖leftSupport p - leftTargetSupport p‖) 1 rho < deltaQ := by
        rw [← hfun]
        exact h
      simpa [Real.norm_eq_abs] using h'
    have hRightPairQ :
        eLpNorm (fun p => |rightError p| + |rightError p|) 1 rho < deltaQ := by
      have h := hetaQtwo (fun p => ‖rightError p‖)
          (fun p => ‖rightError p‖)
          hErrBQ' hErrBQ'
      have hfun :
          (fun p => ‖rightError p‖) + (fun p => ‖rightError p‖) =
            (fun p => ‖rightError p‖ + ‖rightError p‖) := by
        funext p
        rfl
      have h' :
          eLpNorm (fun p => ‖rightError p‖ + ‖rightError p‖) 1 rho < deltaQ := by
        rw [← hfun]
        exact h
      simpa [Real.norm_eq_abs] using h'
    have hTargetSupportEq :
        Function.support (f + g : (NNReal × Omega) → Real) =
          Function.support f ∪ Function.support g := by
      ext p
      by_cases hfp : f p = 0
      · by_cases hgp : g p = 0
        · simp [hfp, hgp]
        · simp [hfp, hgp]
      · by_cases hgp : g p = 0
        · simp [hfp, hgp]
        · exact (Set.disjoint_left.1 hSupportDisjoint hfp hgp).elim
    have hExtraBound : ∀ p,
        |rightIntegrand p *
            (1 - (Function.uncurry
              (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| ≤
          |rightError p| + |leftSupport p - leftTargetSupport p| := by
      intro p
      by_cases hpH : p ∈ horizon T
      · by_cases hpA : p ∈ A.carrier.carrier
        · by_cases hpG : p ∈ Function.support g
          · have hpF : p ∉ Function.support f := by
              intro hpf
              exact Set.disjoint_left.1 hSupportDisjoint hpf hpG
            have hpD : p ∉
                (RingSet.sdiff B.carrier A.carrier).carrier ∩ horizon T := by
              intro hpD
              exact hpD.1.2 hpA
            have hBnd := B.abs_integrand_le_one p.1 p.2
            have hSupportOne :
                |leftSupport p - leftTargetSupport p| = 1 := by
              simp [leftSupport, leftTargetSupport, hpH, hpA, hpF]
            rw [show (Function.uncurry
                (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p =
                FiniteHorizonPredictableIndicatorRing.indicatorProcess
                  ((RingSet.sdiff B.carrier A.carrier).carrier ∩ horizon T)
                    p.1 p.2 by
                exact congrFun (congrFun
                  (RingSet.sdiff B.carrier A.carrier).representation.integrand_eq
                  p.1) p.2]
            unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
            rw [ite_eq_right hpD, sub_zero, mul_one]
            exact hBnd.trans (by
              rw [hSupportOne]
              exact le_add_of_nonneg_left (abs_nonneg _))
          · have hgzero : g p = 0 := by
              by_contra hg
              exact hpG hg
            have hpD : p ∉
                (RingSet.sdiff B.carrier A.carrier).carrier ∩ horizon T := by
              intro hpD
              exact hpD.1.2 hpA
            have hRightIntegrand : rightIntegrand p = -rightError p := by
              change rightIntegrand p = -(g p - rightIntegrand p)
              rw [hgzero]
              ring
            rw [show (Function.uncurry
                (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p =
                FiniteHorizonPredictableIndicatorRing.indicatorProcess
                  ((RingSet.sdiff B.carrier A.carrier).carrier ∩ horizon T)
                    p.1 p.2 by
                exact congrFun (congrFun
                  (RingSet.sdiff B.carrier A.carrier).representation.integrand_eq
                  p.1) p.2]
            unfold FiniteHorizonPredictableIndicatorRing.indicatorProcess
            rw [ite_eq_right hpD, sub_zero, mul_one, hRightIntegrand, abs_neg]
            exact le_add_of_nonneg_right (abs_nonneg _)
        · have hpAzero : leftIntegrand p = 0 :=
            A.integrand_eq_zero_of_not_mem p (by
              intro hpA'
              exact hpA hpA'.1)
          have hpD :
              (Function.uncurry
                (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p =
                ((RingSet.sdiff B.carrier A.carrier).carrier ∩ horizon T).indicator
                  (fun _ => (1 : Real)) p := by
            exact congrFun (congrFun
              (RingSet.sdiff B.carrier A.carrier).representation.integrand_eq
              p.1) p.2
          by_cases hpB : p ∈ B.carrier.carrier
          · rw [hpD]
            simpa [FiniteHorizonPredictableIndicatorRing.indicatorProcess,
              RingSet.sdiff, hpA, hpB, hpH] using
              (add_nonneg (abs_nonneg (rightError p))
                (abs_nonneg (leftSupport p - leftTargetSupport p)))
          · have hpBzero : rightIntegrand p = 0 :=
              B.integrand_eq_zero_of_not_mem p (by
                intro hpB'
                exact hpB hpB'.1)
            rw [hpBzero, zero_mul]
            simpa using
              (add_nonneg (abs_nonneg (rightError p))
                (abs_nonneg (leftSupport p - leftTargetSupport p)))
      · have hpBzero : rightIntegrand p = 0 :=
          B.integrand_eq_zero_of_not_mem p (by
            intro hpB
            exact hpH hpB.2)
        rw [hpBzero, zero_mul]
        simpa using
          (add_nonneg (abs_nonneg (rightError p))
            (abs_nonneg (leftSupport p - leftTargetSupport p)))
    let leftMajor : (NNReal × Omega) → Real := fun p =>
      |leftError p| + |leftSupport p - leftTargetSupport p|
    let rightMajor : (NNReal × Omega) → Real := fun p =>
      |rightError p| + |rightError p|
    have hLeftMajorMeasP : AEStronglyMeasurable leftMajor nu := by
      exact (hLeftErrorMeasP.norm.add hLeftDiscMeasP)
    have hRightMajorMeasP : AEStronglyMeasurable rightMajor nu := by
      exact (hRightErrorMeasP.norm.add hRightErrorMeasP.norm)
    have hLeftMajorMeasQ : AEStronglyMeasurable leftMajor rho := by
      exact (hLeftErrorMeasQ.norm.add hLeftDiscMeasQ)
    have hRightMajorMeasQ : AEStronglyMeasurable rightMajor rho := by
      exact (hRightErrorMeasQ.norm.add hRightErrorMeasQ.norm)
    have hLeftMajorBoundP : eLpNorm leftMajor 2 nu < deltaP := by
      simpa [leftMajor] using hLeftPairP
    have hRightMajorBoundP : eLpNorm rightMajor 2 nu < deltaP := by
      simpa [rightMajor] using hRightPairP
    have hLeftMajorBoundQ : eLpNorm leftMajor 1 rho < deltaQ := by
      simpa [leftMajor] using hLeftPairQ
    have hRightMajorBoundQ : eLpNorm rightMajor 1 rho < deltaQ := by
      simpa [rightMajor] using hRightPairQ
    have hWpoint : ∀ p,
        Function.uncurry W.strategy.integrand p =
          leftIntegrand p + rightIntegrand p *
            (Function.uncurry
              (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p := by
      intro p
      change (A.strategy ++
          (B.strategy.mul
            (RingSet.sdiff B.carrier A.carrier).representation.strategy)).integrand
          p.1 p.2 = _
      rw [PredictableElementaryStrategy.append_integrand,
        PredictableElementaryStrategy.mul_integrand]
      rfl
    have hFullBound : ∀ p,
        |(f + g : (NNReal × Omega) → Real) p -
            Function.uncurry W.strategy.integrand p| ≤
          leftMajor p + rightMajor p := by
      intro p
      rw [hWpoint p]
      change |f p + g p -
          (leftIntegrand p + rightIntegrand p *
            (Function.uncurry
              (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| ≤ _
      have hDecomp :
          f p + g p -
              (leftIntegrand p + rightIntegrand p *
                (Function.uncurry
                  (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p) =
            leftError p + rightError p +
              rightIntegrand p *
                (1 - (Function.uncurry
                  (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p) := by
        dsimp [leftError, rightError, leftFun, rightFun]
        ring
      rw [hDecomp]
      calc
        |leftError p + rightError p +
            rightIntegrand p *
              (1 - (Function.uncurry
                (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| ≤
            |leftError p| + |rightError p| +
              |rightIntegrand p *
                (1 - (Function.uncurry
                  (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| := by
          calc
            |leftError p + rightError p +
                rightIntegrand p *
                  (1 - (Function.uncurry
                    (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| ≤
                |leftError p + rightError p| +
                  |rightIntegrand p *
                    (1 - (Function.uncurry
                      (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| :=
              abs_add_le _ _
            _ ≤ |leftError p| + |rightError p| +
                |rightIntegrand p *
                  (1 - (Function.uncurry
                    (RingSet.sdiff B.carrier A.carrier).representation.strategy.integrand) p)| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |leftError p| + |rightError p| +
            (|rightError p| + |leftSupport p - leftTargetSupport p|) := by
          linarith [hExtraBound p]
        _ = leftMajor p + rightMajor p := by
          ring
    have hFullNormBoundP :
        eLpNorm ((f + g : (NNReal × Omega) → Real) -
          Function.uncurry W.strategy.integrand) 2 nu ≤
          eLpNorm (leftMajor + rightMajor) 2 nu := by
      apply eLpNorm_mono_real
        ((f.stronglyMeasurable.add g.stronglyMeasurable).sub
          W.strategy.integrand_isStronglyPredictable).aestronglyMeasurable
      intro p
      simpa [Real.norm_eq_abs, Pi.add_apply] using hFullBound p
    have hFullNormBoundQ :
        eLpNorm ((f + g : (NNReal × Omega) → Real) -
          Function.uncurry W.strategy.integrand) 1 rho ≤
          eLpNorm (leftMajor + rightMajor) 1 rho := by
      apply eLpNorm_mono_real
        ((f.stronglyMeasurable.add g.stronglyMeasurable).sub
          W.strategy.integrand_isStronglyPredictable).aestronglyMeasurable
      intro p
      simpa [Real.norm_eq_abs, Pi.add_apply] using hFullBound p
    have hSumErrorP :
        eLpNorm ((f + g : (NNReal × Omega) → Real) -
          Function.uncurry W.strategy.integrand) 2 nu ≤ delta := by
      have h := hdeltaP leftMajor rightMajor hLeftMajorBoundP.le hRightMajorBoundP.le
      exact hFullNormBoundP.trans h.le
    have hSumErrorQ :
        eLpNorm ((f + g : (NNReal × Omega) → Real) -
          Function.uncurry W.strategy.integrand) 1 rho ≤ delta := by
      have h := hdeltaQ leftMajor rightMajor hLeftMajorBoundQ.le hRightMajorBoundQ.le
      exact hFullNormBoundQ.trans h.le
    have hWcarrier :
        W.carrier.carrier = A.carrier.carrier ∪ B.carrier.carrier := by
      rfl
    let leftDiscAbs : (NNReal × Omega) → Real := fun p =>
      |leftSupport p - leftTargetSupport p|
    let rightDiscAbs : (NNReal × Omega) → Real := fun p =>
      |rightSupport p - rightTargetSupport p|
    have hLeftDiscAbsMeasP : AEStronglyMeasurable leftDiscAbs nu := by
      simpa [leftDiscAbs] using hLeftDiscMeasP
    have hRightDiscAbsMeasP : AEStronglyMeasurable rightDiscAbs nu := by
      simpa [rightDiscAbs] using hRightDiscMeasP
    have hLeftDiscAbsMeasQ : AEStronglyMeasurable leftDiscAbs rho := by
      simpa [leftDiscAbs] using hLeftDiscMeasQ
    have hRightDiscAbsMeasQ : AEStronglyMeasurable rightDiscAbs rho := by
      simpa [rightDiscAbs] using hRightDiscMeasQ
    have hSupportBound : ∀ p,
        |((W.carrier.carrier ∩ horizon T).indicator
            (fun _ => (1 : Real)) -
          (Function.support (f + g : (NNReal × Omega) → Real)).indicator
            (fun _ => (1 : Real))) p| ≤
          leftDiscAbs p + rightDiscAbs p := by
      intro p
      rw [hWcarrier, hTargetSupportEq]
      by_cases hpH : p ∈ horizon T
      · by_cases hpA : p ∈ A.carrier.carrier <;>
          by_cases hpB : p ∈ B.carrier.carrier <;>
          by_cases hpF : p ∈ Function.support f <;>
          by_cases hpG : p ∈ Function.support g <;>
          simp [leftDiscAbs, rightDiscAbs, leftSupport, rightSupport,
            leftTargetSupport, rightTargetSupport, hpH, hpA, hpB, hpF, hpG]
      · have hfzero := hfH p hpH
        have hgzero := hgH p hpH
        simp [leftDiscAbs, rightDiscAbs, leftSupport, rightSupport,
          leftTargetSupport, rightTargetSupport, hpH, hfzero, hgzero]
    have hSupportAPDelta :
        eLpNorm (fun p => ‖leftSupport p - leftTargetSupport p‖) 2 nu ≤ deltaP := by
      have h := hSupportAP.trans hEtaDeltaP
      rw [← eLpNorm_norm _ (hLeftSupportMeasP.sub hLeftTargetSupportMeasP)] at h
      simpa [leftSupport, leftTargetSupport, Pi.sub_apply] using h
    have hSupportBPDelta :
        eLpNorm (fun p => ‖rightSupport p - rightTargetSupport p‖) 2 nu ≤ deltaP := by
      have h := hSupportBP.trans hEtaDeltaP
      rw [← eLpNorm_norm _ (hRightSupportMeasP.sub hRightTargetSupportMeasP)] at h
      simpa [rightSupport, rightTargetSupport, Pi.sub_apply] using h
    have hSupportAQDelta :
        eLpNorm (fun p => ‖leftSupport p - leftTargetSupport p‖) 1 rho ≤ deltaQ := by
      have h := hSupportAQ.trans hEtaDeltaQ
      rw [← eLpNorm_norm _ (hLeftSupportMeasQ.sub hLeftTargetSupportMeasQ)] at h
      simpa [leftSupport, leftTargetSupport, Pi.sub_apply] using h
    have hSupportBQDelta :
        eLpNorm (fun p => ‖rightSupport p - rightTargetSupport p‖) 1 rho ≤ deltaQ := by
      have h := hSupportBQ.trans hEtaDeltaQ
      rw [← eLpNorm_norm _ (hRightSupportMeasQ.sub hRightTargetSupportMeasQ)] at h
      simpa [rightSupport, rightTargetSupport, Pi.sub_apply] using h
    have hLeftDiscBoundP : eLpNorm leftDiscAbs 2 nu ≤ deltaP := by
      simpa [leftDiscAbs, Real.norm_eq_abs] using hSupportAPDelta
    have hRightDiscBoundP : eLpNorm rightDiscAbs 2 nu ≤ deltaP := by
      simpa [rightDiscAbs, Real.norm_eq_abs] using hSupportBPDelta
    have hLeftDiscBoundQ : eLpNorm leftDiscAbs 1 rho ≤ deltaQ := by
      simpa [leftDiscAbs, Real.norm_eq_abs] using hSupportAQDelta
    have hRightDiscBoundQ : eLpNorm rightDiscAbs 1 rho ≤ deltaQ := by
      simpa [rightDiscAbs, Real.norm_eq_abs] using hSupportBQDelta
    have hSupportNormBoundP :
        eLpNorm (((W.carrier.carrier ∩ horizon T).indicator
            (fun _ => (1 : Real))) -
          (Function.support (f + g : (NNReal × Omega) → Real)).indicator
              (fun _ => (1 : Real))) 2 nu ≤
          eLpNorm (leftDiscAbs + rightDiscAbs) 2 nu := by
      apply eLpNorm_mono_real
        ((stronglyMeasurable_const.indicator
          (W.carrier.measurable.inter
            (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T))).sub
          (stronglyMeasurable_const.indicator (f + g).measurableSet_support)).aestronglyMeasurable
      intro p
      simpa [Real.norm_eq_abs, Pi.add_apply, leftDiscAbs, rightDiscAbs,
        horizon, FiniteHorizonPredictableIndicatorRing.horizonCarrier] using
        hSupportBound p
    have hSupportNormBoundQ :
        eLpNorm (((W.carrier.carrier ∩ horizon T).indicator
            (fun _ => (1 : Real))) -
          (Function.support (f + g : (NNReal × Omega) → Real)).indicator
              (fun _ => (1 : Real))) 1 rho ≤
          eLpNorm (leftDiscAbs + rightDiscAbs) 1 rho := by
      apply eLpNorm_mono_real
        ((stronglyMeasurable_const.indicator
          (W.carrier.measurable.inter
            (FiniteHorizonPredictableIndicatorRing.measurableSet_horizonCarrier T))).sub
          (stronglyMeasurable_const.indicator (f + g).measurableSet_support)).aestronglyMeasurable
      intro p
      simpa [Real.norm_eq_abs, Pi.add_apply, leftDiscAbs, rightDiscAbs,
        horizon, FiniteHorizonPredictableIndicatorRing.horizonCarrier] using
        hSupportBound p
    have hSupportSumP : eLpNorm (leftDiscAbs + rightDiscAbs) 2 nu < delta := by
      have h := hdeltaP leftDiscAbs rightDiscAbs hLeftDiscBoundP hRightDiscBoundP
      exact h
    have hSupportSumQ : eLpNorm (leftDiscAbs + rightDiscAbs) 1 rho < delta := by
      have h := hdeltaQ leftDiscAbs rightDiscAbs hLeftDiscBoundQ hRightDiscBoundQ
      exact h
    have hSumSupportP :
        eLpNorm (((W.carrier.carrier ∩ horizon T).indicator
            (fun _ => (1 : Real))) -
          (Function.support (f + g : (NNReal × Omega) → Real)).indicator
              (fun _ => (1 : Real))) 2 nu ≤ delta := by
      exact hSupportNormBoundP.trans hSupportSumP.le
    have hSumSupportQ :
        eLpNorm (((W.carrier.carrier ∩ horizon T).indicator
            (fun _ => (1 : Real))) -
          (Function.support (f + g : (NNReal × Omega) → Real)).indicator
              (fun _ => (1 : Real))) 1 rho ≤ delta := by
      exact hSupportNormBoundQ.trans hSupportSumQ.le
    exact ⟨W, hSumErrorP, hSumSupportP, hSumErrorQ, hSumSupportQ⟩

/-! The private finite-valued construction is now applied to the common
simple approximation, so the resulting elementary test is independent of
which of the two finite controls is used. -/

theorem exists_boundedPredictableElementaryMultiplier_unit_approximation_with_coefficientBound
    (T : NNReal)
    (nu rho : @Measure (NNReal × Omega) F.predictable)
    [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    (f : Process Omega)
    (hf : IsStronglyPredictable F f)
    (hfBound : ∀ t omega, |f t omega| ≤ 1)
    (hfH : ∀ p, p ∉
      FiniteHorizonPredictableIndicatorRing.horizonCarrier (Omega := Omega) T →
        f p.1 p.2 = 0)
    {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
    ∃ J : BoundedPredictableElementaryMultiplier (Ω := Omega) F,
      eLpNorm (Function.uncurry J.strategy.integrand - Function.uncurry f)
          2 nu ≤ epsilon ∧
      eLpNorm (Function.uncurry J.strategy.integrand - Function.uncurry f)
          1 rho ≤ epsilon ∧
      (∀ p, p ∉
        FiniteHorizonPredictableIndicatorRing.horizonCarrier (Omega := Omega) T →
          J.strategy.integrand p.1 p.2 = 0) ∧
      ∃ C : NNReal, ∀ omega, J.strategy.coefficientAbsSum omega ≤ C := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let s : ℕ → @SimpleFunc (NNReal × Omega) F.predictable Real := fun n =>
    SimpleFunc.approxOn (Function.uncurry f) hf.measurable
      (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp) n
  have hs_eq (n : ℕ) :
      (s n : (NNReal × Omega) → Real) =
        predictableCommonSimpleApproximationRaw f hf n := by
    rfl
  have hfBound' : ∀ p : NNReal × Omega,
      ‖Function.uncurry f p‖ ≤ (1 : Real) := by
    intro p
    change |f p.1 p.2| ≤ 1
    exact hfBound p.1 p.2
  have hNuMem : MemLp (Function.uncurry f) 2 nu := by
    exact MemLp.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hfBound')
  have hRhoMem : MemLp (Function.uncurry f) 1 rho := by
    exact MemLp.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hfBound')
  have hNuT : Tendsto (fun n => eLpNorm
      (predictableCommonSimpleApproximationRaw f hf n -
        Function.uncurry f) 2 nu) atTop (𝓝 0) := by
    exact predictableCommonSimpleApproximationRaw_tendsto_eLpNorm
      f hf nu 2 (by norm_num) hNuMem
  have hRhoT : Tendsto (fun n => eLpNorm
      (predictableCommonSimpleApproximationRaw f hf n -
        Function.uncurry f) 1 rho) atTop (𝓝 0) := by
    exact predictableCommonSimpleApproximationRaw_tendsto_eLpNorm
      f hf rho 1 (by norm_num) hRhoMem
  have hNuEventually : ∀ᶠ n : ℕ in atTop,
      eLpNorm ((s n : (NNReal × Omega) → Real) -
        Function.uncurry f) 2 nu ≤ epsilon / 2 := by
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hNuT (epsilon / 2)
      (ENNReal.half_pos hepsilon)] with k hk
    rw [hs_eq k]
    exact hk
  have hRhoEventually : ∀ᶠ n : ℕ in atTop,
      eLpNorm ((s n : (NNReal × Omega) → Real) -
        Function.uncurry f) 1 rho ≤ epsilon / 2 := by
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hRhoT (epsilon / 2)
      (ENNReal.half_pos hepsilon)] with k hk
    rw [hs_eq k]
    exact hk
  obtain ⟨n, hnNu, hnRho⟩ := (hNuEventually.and hRhoEventually).exists
  have hsBound : ∀ p, |s n p| ≤ 1 := by
    intro p
    have hp := SimpleFunc.approxOn_mem hf.measurable
      (by simp : (0 : Real) ∈ Set.range (Function.uncurry f) ∪ {0}) n p
    rcases hp with ⟨q, hq⟩ | hp
    · rw [← hq]
      exact hfBound q.1 q.2
    · rw [hp]
      norm_num
  have hsH : ∀ p, p ∉ horizon T → s n p = 0 := by
    intro p hp
    have hfzero : Function.uncurry f p = 0 := by
      change f p.1 p.2 = 0
      exact hfH p hp
    have hd := SimpleFunc.edist_approxOn_le hf.measurable
      (by simp : (0 : Real) ∈ Set.range (Function.uncurry f) ∪ {0}) p n
    rw [hfzero] at hd
    change edist (s n p) 0 ≤ edist 0 0 at hd
    have hz : edist (s n p) 0 = 0 := by
      apply le_antisymm
      · simpa using hd
      · exact bot_le
    exact edist_eq_zero.mp hz
  have hhalf : 0 < epsilon / 2 := ENNReal.half_pos hepsilon
  obtain ⟨U, hUSimpleNu, _hUSupportNu, hUSimpleRho, _hUSupportRho⟩ :=
    exists_unitElementary_of_simple T nu rho (s n) hsBound hsH
      hhalf.ne'
  let J : BoundedPredictableElementaryMultiplier (Ω := Omega) F :=
    { strategy := U.strategy
      abs_integrand_le_one := U.abs_integrand_le_one }
  have hUApproxNu : eLpNorm
      (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real))
        2 nu ≤ epsilon / 2 := by
    change eLpNorm
      (Function.uncurry U.strategy.integrand - (s n : (NNReal × Omega) → Real))
        2 nu ≤ epsilon / 2
    rw [eLpNorm_sub_comm]
    exact hUSimpleNu
  have hUApproxRho : eLpNorm
      (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real))
        1 rho ≤ epsilon / 2 := by
    change eLpNorm
      (Function.uncurry U.strategy.integrand - (s n : (NNReal × Omega) → Real))
        1 rho ≤ epsilon / 2
    rw [eLpNorm_sub_comm]
    exact hUSimpleRho
  have hSimpleNu : eLpNorm
      ((s n : (NNReal × Omega) → Real) - Function.uncurry f) 2 nu ≤
        epsilon / 2 := hnNu
  have hSimpleRho : eLpNorm
      ((s n : (NNReal × Omega) → Real) - Function.uncurry f) 1 rho ≤
        epsilon / 2 := hnRho
  have hNuApprox : eLpNorm
      (Function.uncurry J.strategy.integrand - Function.uncurry f) 2 nu ≤
        epsilon := by
    have hAddMeas : AEStronglyMeasurable
        (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) nu :=
      J.strategy.integrand_isStronglyPredictable.aestronglyMeasurable.sub
        (s n).stronglyMeasurable.aestronglyMeasurable
    have hSimpleMeas : AEStronglyMeasurable
        ((s n : (NNReal × Omega) → Real) - Function.uncurry f) nu :=
      (s n).stronglyMeasurable.aestronglyMeasurable.sub
        hf.aestronglyMeasurable
    have hDecomp : Function.uncurry J.strategy.integrand - Function.uncurry f =
        (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) +
          ((s n : (NNReal × Omega) → Real) - Function.uncurry f) := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hDecomp]
    calc
      eLpNorm
          ((Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) +
            ((s n : (NNReal × Omega) → Real) - Function.uncurry f)) 2 nu ≤
          eLpNorm
              (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real))
            2 nu + eLpNorm ((s n : (NNReal × Omega) → Real) - Function.uncurry f) 2 nu :=
        eLpNorm_add_le (by norm_num)
      _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hUApproxNu hSimpleNu
      _ = epsilon := ENNReal.add_halves epsilon
  have hRhoApprox : eLpNorm
      (Function.uncurry J.strategy.integrand - Function.uncurry f) 1 rho ≤
        epsilon := by
    have hAddMeas : AEStronglyMeasurable
        (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) rho :=
      J.strategy.integrand_isStronglyPredictable.aestronglyMeasurable.sub
        (s n).stronglyMeasurable.aestronglyMeasurable
    have hSimpleMeas : AEStronglyMeasurable
        ((s n : (NNReal × Omega) → Real) - Function.uncurry f) rho :=
      (s n).stronglyMeasurable.aestronglyMeasurable.sub
        hf.aestronglyMeasurable
    have hDecomp : Function.uncurry J.strategy.integrand - Function.uncurry f =
        (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) +
          ((s n : (NNReal × Omega) → Real) - Function.uncurry f) := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hDecomp]
    calc
      eLpNorm
          ((Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real)) +
            ((s n : (NNReal × Omega) → Real) - Function.uncurry f)) 1 rho ≤
          eLpNorm
              (Function.uncurry J.strategy.integrand - (s n : (NNReal × Omega) → Real))
            1 rho + eLpNorm ((s n : (NNReal × Omega) → Real) - Function.uncurry f) 1 rho :=
        eLpNorm_add_le (by norm_num)
      _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hUApproxRho hSimpleRho
      _ = epsilon := ENNReal.add_halves epsilon
  refine ⟨J, hNuApprox, hRhoApprox, ?_, ?_⟩
  · intro p hp
    exact U.integrand_eq_zero_of_not_mem p (by
      intro h
      exact hp h.2)
  · exact ⟨U.coefficientBound, U.coefficientAbsSum_le⟩

end PredictableUnitBoundedElementaryDensity

end FTAPTheorem42
