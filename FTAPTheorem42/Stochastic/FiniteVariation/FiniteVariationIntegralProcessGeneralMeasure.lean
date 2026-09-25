/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionGeneralAgreement

/-!
# Recovering a finite-variation path from a Stieltjes density

Equality between a vector-valued density and the signed Stieltjes measure of
a right-continuous bounded-variation path determines every path increment.
This is the pathwise bridge from signed-measure identities to the cumulative
process identities used by stochastic-integral realization.
-/

namespace FTAPTheorem42.FiniteVariationPath

open MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {Time : Type*} [LinearOrder Time] [OrderBot Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]

omit [OrderBot Time] in
/-- The signed Stieltjes measure is independent of the proof and path
representative once the underlying paths are equal. -/
theorem signedMeasure_eq_of_eq
    {A B : Time -> Real} (hA : BoundedVariationOn A Set.univ)
    (hB : BoundedVariationOn B Set.univ) (hAB : A = B) :
    signedMeasure hA = signedMeasure hB := by
  subst B
  rfl

/-- A signed-density representation determines the path after centering at
the initial time. -/
theorem sub_initial_eq_setIntegral_of_withDensity_eq_signedMeasure
    {B : Time -> Real} (hB : BoundedVariationOn B Set.univ)
    (hBRight : forall t, ContinuousWithinAt B (Set.Ici t) t)
    (nu : Measure Time) {f : Time -> Real} (hf : Integrable f nu)
    (hDensity : nu.withDensityᵥ f = signedMeasure hB) (t : Time) :
    B t - B ⊥ = ∫ u in Set.Ioc ⊥ t, f u ∂nu := by
  have hInterval := congrArg (fun eta : SignedMeasure Time => eta (Set.Ioc ⊥ t))
    hDensity
  rw [withDensityᵥ_apply hf measurableSet_Ioc,
    signedMeasure_Ioc hB hBRight bot_le] at hInterval
  exact hInterval.symm

end FTAPTheorem42.FiniteVariationPath

namespace FTAPTheorem42

/-!
## Stieltjes measures of general variation-integrable coefficients

The bounded-coefficient Stieltjes theory identifies the signed measure of a
cumulative finite-variation integral directly.  Completed `A1` coefficients
need the same statement under pathwise `L1` integrability instead of a
uniform bound.  We only use it when a right-continuous bounded-variation
output path has already been identified with the cumulative integral, so no
new path regularization is required here.
-/

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

omit [SigmaFiniteFiltration mu F] in
/-- For a pathwise variation-integrable coefficient, increments of the raw
cumulative integral are the corresponding interval integrals. -/
theorem finiteVariationIntegralProcess_sub_of_integrable
    (E : SIntegrableFiniteVariationBridge G)
    {K : Process Omega} (hK : IsStronglyPredictable F K)
    (omega : Omega)
    (hIntegrable : Integrable (fun u => K u omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    {a b : NNReal} (hab : a <= b) :
    finiteVariationIntegralProcess E K b omega -
        finiteVariationIntegralProcess E K a omega =
      ∫ u in Ioc a b, finiteVariationIntegralDensity E K (u, omega)
        ∂(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  have hDensity : Integrable
      (fun u => finiteVariationIntegralDensity E K (u, omega)) nu :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hK omega hIntegrable
  have hSubset : Ioc (0 : NNReal) a ⊆ Ioc 0 b :=
    Ioc_subset_Ioc_right hab
  have hDifference : Ioc (0 : NNReal) b \ Ioc 0 a = Ioc a b := by
    ext u
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · rintro ⟨⟨hZero, hub⟩, hNot⟩
      exact ⟨lt_of_not_ge fun hua => hNot ⟨hZero, hua⟩, hub⟩
    · rintro ⟨hau, hub⟩
      refine ⟨⟨bot_le.trans_lt hau, hub⟩, ?_⟩
      rintro ⟨-, hua⟩
      exact (not_lt_of_ge hua) hau
  change (∫ u in Ioc 0 b,
      finiteVariationIntegralDensity E K (u, omega) ∂nu) -
      (∫ u in Ioc 0 a,
        finiteVariationIntegralDensity E K (u, omega) ∂nu) = _
  rw [<- setIntegral_sdiff measurableSet_Ioc hDensity.integrableOn hSubset,
    hDifference]

omit [SigmaFiniteFiltration mu F] in
/-- If the increments from the initial value of a right-continuous
bounded-variation path form the raw cumulative integral of a pathwise `L1`
coefficient, its signed Stieltjes measure is the corresponding oriented
density measure. -/
theorem withDensity_finiteVariationIntegralDensity_eq_signedMeasure_of_eq
    (E : SIntegrableFiniteVariationBridge G)
    {K : Process Omega} (hK : IsStronglyPredictable F K)
    (omega : Omega)
    (hIntegrable : Integrable (fun u => K u omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    {B : NNReal -> Real} (hB : BoundedVariationOn B Set.univ)
    (hBRight : forall t, ContinuousWithinAt B (Ici t) t)
    (hBIntegral : forall t,
      B t - B 0 = finiteVariationIntegralProcess E K t omega) :
    (FiniteVariationPath.signedMeasure
      (G.finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
        (fun u => finiteVariationIntegralDensity E K (u, omega)) =
      FiniteVariationPath.signedMeasure hB := by
  let nu := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  let g : NNReal -> Real := fun u => finiteVariationIntegralDensity E K (u, omega)
  have hDensity : Integrable g nu :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hK omega hIntegrable
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [withDensityᵥ_apply hDensity measurableSet_Ioc,
      FiniteVariationPath.signedMeasure_Ioc hB hBRight hab]
    rw [show B b - B a = (B b - B 0) - (B a - B 0) by ring,
      hBIntegral b, hBIntegral a]
    exact (finiteVariationIntegralProcess_sub_of_integrable
      E hK omega hIntegrable hab).symm
  · let : IsFiniteMeasure nu := by
      dsimp only [nu]
      unfold SignedMeasure.totalVariation
      infer_instance
    have hMonotone : Monotone fun T : NNReal => Ioc (0 : NNReal) T := by
      intro a b hab
      exact Ioc_subset_Ioc_right hab
    have hSetLimit : Tendsto
        (fun T : NNReal => ∫ u in Ioc 0 T, g u ∂nu) atTop
        (nhds (∫ u in ⋃ T : NNReal, Ioc 0 T, g u ∂nu)) :=
      tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc)
        hMonotone hDensity.integrableOn
    have hComplement : (Ioi (0 : NNReal))ᶜ = ({0} : Set NNReal) := by
      ext t
      simp
    have hSingleton : (∫ u in ({0} : Set NNReal), g u ∂nu) = 0 := by
      have hNuZero : nu ({0} : Set NNReal) = 0 :=
        totalVariation_singleton_zero G E.rightContinuous omega
      rw [integral_singleton, measureReal_def, hNuZero]
      simp
    have hIoi : (∫ u in Ioi (0 : NNReal), g u ∂nu) = ∫ u, g u ∂nu := by
      have hAdd := integral_add_compl (μ := nu) (s := Ioi (0 : NNReal))
        measurableSet_Ioi hDensity
      rw [hComplement, hSingleton, add_zero] at hAdd
      exact hAdd
    rw [iUnion_Ioc_right, hIoi] at hSetLimit
    have hRawTop : Tendsto
        (fun T => finiteVariationIntegralProcess E K T omega) atTop
        (nhds (∫ u, g u ∂nu)) := by
      simpa [g, nu, finiteVariationIntegralProcess,
        pathVariationMeasureUpTo] using hSetLimit
    have hTop : Tendsto B atTop (nhds ((∫ u, g u ∂nu) + B 0)) := by
      apply (hRawTop.add tendsto_const_nhds).congr'
      filter_upwards with t
      have h := hBIntegral t
      linarith
    have hBot : limUnder atBot B = B 0 := by
      rw [atBot_eq_pure_of_isBot isBot_bot]
      rw [(tendsto_pure_nhds B (⊥ : NNReal)).limUnder_eq]
      rfl
    rw [withDensityᵥ_apply hDensity MeasurableSet.univ, setIntegral_univ,
      FiniteVariationPath.signedMeasure_univ hB, hTop.limUnder_eq, hBot,
      add_sub_cancel_right]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
