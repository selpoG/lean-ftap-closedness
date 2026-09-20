/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.PiSystem

/-!
# Kernels of finite-variation path measures

The Jordan parts of a random signed Stieltjes measure must be measurable as
measure-valued maps before they can be integrated over the sample space.  On
an ordered Borel time space, it suffices to check measurability of their
masses on the generating half-open intervals and on the whole space.  This
file proves that generator criterion and applies it to the pathwise signed
measures of finite-variation processes.
-/

namespace FTAPTheorem42

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [LinearOrder Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]

namespace FiniteVariationKernel

/-! ## Measurability of Jordan masses -/

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- The real mass of the positive Jordan part is half the sum of total
variation and signed mass. -/
theorem two_mul_posPart_real
    (ν : SignedMeasure Time) {B : Set Time} (hB : MeasurableSet B) :
    2 * ν.toJordanDecomposition.posPart.real B =
      ν.totalVariation.real B + ν B := by
  have hsigned :
      ν.toJordanDecomposition.posPart.real B -
          ν.toJordanDecomposition.negPart.real B = ν B := by
    rw [← Measure.toSignedMeasure_sub_apply hB,
      ← JordanDecomposition.toSignedMeasure,
      SignedMeasure.toSignedMeasure_toJordanDecomposition]
  have hvariation :
      ν.totalVariation.real B =
        ν.toJordanDecomposition.posPart.real B +
          ν.toJordanDecomposition.negPart.real B := by
    rw [SignedMeasure.totalVariation, measureReal_add_apply]
  linarith

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- The real mass of the negative Jordan part is half the difference of total
variation and signed mass. -/
theorem two_mul_negPart_real
    (ν : SignedMeasure Time) {B : Set Time} (hB : MeasurableSet B) :
    2 * ν.toJordanDecomposition.negPart.real B =
      ν.totalVariation.real B - ν B := by
  simpa only [SignedMeasure.toJordanDecomposition_neg, JordanDecomposition.neg_posPart,
    SignedMeasure.totalVariation_neg, neg_apply, sub_eq_add_neg]
    using two_mul_posPart_real (-ν) hB

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- A nonpositive singleton mass carries no positive Jordan mass. -/
theorem posPart_singleton_eq_zero_of_nonpos
    [MeasurableSingletonClass Time]
    (ν : SignedMeasure Time) (x : Time) (hx : ν {x} ≤ 0) :
    ν.toJordanDecomposition.posPart {x} = 0 := by
  apply (measureReal_eq_zero_iff
    (μ := ν.toJordanDecomposition.posPart)).1
  have h := two_mul_posPart_real ν (MeasurableSet.singleton x)
  rw [signedMeasure_totalVariation_real_singleton,
    abs_of_nonpos hx] at h
  linarith

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- A nonnegative singleton mass carries no negative Jordan mass. -/
theorem negPart_singleton_eq_zero_of_nonneg
    [MeasurableSingletonClass Time]
    (ν : SignedMeasure Time) (x : Time) (hx : 0 ≤ ν {x}) :
    ν.toJordanDecomposition.negPart {x} = 0 := by
  apply (measureReal_eq_zero_iff
    (μ := ν.toJordanDecomposition.negPart)).1
  have h := two_mul_negPart_real ν (MeasurableSet.singleton x)
  rw [signedMeasure_totalVariation_real_singleton,
    abs_of_nonneg hx] at h
  linarith

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- Measurability of signed mass and total-variation mass implies
measurability of positive Jordan mass. -/
theorem measurable_posPart_apply
    {ν : Ω → SignedMeasure Time} {B : Set Time} (hB : MeasurableSet B)
    (hν : Measurable fun ω => ν ω B)
    (hvariation : Measurable fun ω => (ν ω).totalVariation.real B) :
    Measurable fun ω => (ν ω).toJordanDecomposition.posPart B := by
  have heq :
      (fun ω => (ν ω).toJordanDecomposition.posPart B) =
        fun ω => ENNReal.ofReal
          (((ν ω).totalVariation.real B + ν ω B) / 2) := by
    funext ω
    have hnonneg :
        0 ≤ ((ν ω).totalVariation.real B + ν ω B) / 2 := by
      linarith [two_mul_posPart_real (ν ω) hB,
        (measureReal_nonneg :
          0 ≤ (ν ω).toJordanDecomposition.posPart.real B)]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    change (ν ω).toJordanDecomposition.posPart.real B = _
    rw [ENNReal.toReal_ofReal hnonneg]
    linarith [two_mul_posPart_real (ν ω) hB]
  rw [heq]
  exact ((hvariation.add hν).div_const 2).ennreal_ofReal

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- Measurability of signed mass and total-variation mass implies
measurability of negative Jordan mass. -/
theorem measurable_negPart_apply
    {ν : Ω → SignedMeasure Time} {B : Set Time} (hB : MeasurableSet B)
    (hν : Measurable fun ω => ν ω B)
    (hvariation : Measurable fun ω => (ν ω).totalVariation.real B) :
    Measurable fun ω => (ν ω).toJordanDecomposition.negPart B := by
  have heq :
      (fun ω => (ν ω).toJordanDecomposition.negPart B) =
        fun ω => ENNReal.ofReal
          (((ν ω).totalVariation.real B - ν ω B) / 2) := by
    funext ω
    have hnonneg :
        0 ≤ ((ν ω).totalVariation.real B - ν ω B) / 2 := by
      linarith [two_mul_negPart_real (ν ω) hB,
        (measureReal_nonneg :
          0 ≤ (ν ω).toJordanDecomposition.negPart.real B)]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    change (ν ω).toJordanDecomposition.negPart.real B = _
    rw [ENNReal.toReal_ofReal hnonneg]
    linarith [two_mul_negPart_real (ν ω) hB]
  rw [heq]
  exact ((hvariation.sub hν).div_const 2).ennreal_ofReal

/-- A family of finite Borel measures on an ordered time space is a kernel as
soon as its masses on open-closed intervals and on the whole space are
measurable in the parameter. -/
noncomputable def ofFiniteMeasuresIoc
    (ρ : Ω → Measure Time) [∀ ω, IsFiniteMeasure (ρ ω)]
    (hIoc : ∀ a b, a < b → Measurable fun ω => ρ ω (Ioc a b))
    (huniv : Measurable fun ω => ρ ω Set.univ) :
    Kernel Ω Time :=
  ⟨ρ, Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc Time))
    (isPiSystem_Ioc id id)
    (by
      rintro s ⟨a, b, hab, rfl⟩
      simpa using hIoc a b hab)
    huniv⟩

omit [DenselyOrdered Time] [CompactIccSpace Time] in
/-- A uniform bound on the total masses upgrades the generator construction
to a finite kernel in mathlib's uniform sense. -/
theorem isFiniteKernel_ofFiniteMeasuresIoc
    (ρ : Ω → Measure Time) [∀ ω, IsFiniteMeasure (ρ ω)]
    (hIoc : ∀ a b, a < b → Measurable fun ω => ρ ω (Ioc a b))
    (huniv : Measurable fun ω => ρ ω Set.univ)
    {C : ℝ≥0∞} (hC : C < ∞) (hbound : ∀ ω, ρ ω Set.univ ≤ C) :
    IsFiniteKernel (ofFiniteMeasuresIoc ρ hIoc huniv) :=
  ⟨C, hC, hbound⟩

omit [LinearOrder Time] [DenselyOrdered Time] [TopologicalSpace Time]
  [OrderTopology Time] [SecondCountableTopology Time]
  [CompactIccSpace Time] [BorelSpace Time] in
/-- A kernel whose every fibre is a finite measure is s-finite.  Unlike
`IsFiniteKernel`, no uniform bound on the fibre masses is needed. -/
theorem isSFiniteKernel_of_finiteMeasures
    (κ : Kernel Ω Time) [∀ ω, IsFiniteMeasure (κ ω)] :
    IsSFiniteKernel κ := by
  let level : Ω → ℕ := fun ω ↦ ⌈(κ ω Set.univ).toReal⌉₊
  have hlevel : Measurable level :=
    ((κ.measurable_coe MeasurableSet.univ).ennreal_toReal).nat_ceil
  let layer : ℕ → Set Ω := fun n ↦ {ω | level ω = n}
  have hlayer (n : ℕ) : MeasurableSet (layer n) :=
    hlevel (measurableSet_singleton n)
  let κs : ℕ → Kernel Ω Time := fun n ↦
    Kernel.piecewise (hlayer n) κ 0
  have hfinite (n : ℕ) : IsFiniteKernel (κs n) := by
    refine ⟨⟨n, ENNReal.coe_lt_top, fun ω ↦ ?_⟩⟩
    simp only [κs, Kernel.piecewise_apply']
    split_ifs with hω
    · have hmass : κ ω Set.univ ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast]
        apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
          (Nat.cast_nonneg n)).2
        have hlevelω : level ω = n := hω
        rw [← hlevelω]
        exact Nat.le_ceil _
      exact hmass
    · simp
  refine ⟨⟨κs, hfinite, ?_⟩⟩
  ext ω s hs
  rw [Kernel.sum_apply' κs ω hs]
  have heq : (fun n ↦ κs n ω s) =
      fun n ↦ if n = level ω then κ ω s else 0 := by
    funext n
    simp only [κs, Kernel.piecewise_apply']
    simp [layer, eq_comm]
  rw [heq, tsum_ite_eq]

variable {A : Time → Ω → ℝ}
  (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)

/-- The positive Jordan measure of each finite-variation path. -/
noncomputable def positivePathMeasure (ω : Ω) : Measure Time :=
  (FiniteVariationPath.signedMeasure (hA ω)).toJordanDecomposition.posPart

/-- The negative Jordan measure of each finite-variation path. -/
noncomputable def negativePathMeasure (ω : Ω) : Measure Time :=
  (FiniteVariationPath.signedMeasure (hA ω)).toJordanDecomposition.negPart

noncomputable instance positivePathMeasure.instIsFiniteMeasure (ω : Ω) :
    IsFiniteMeasure (positivePathMeasure hA ω) := by
  unfold positivePathMeasure
  infer_instance

noncomputable instance negativePathMeasure.instIsFiniteMeasure (ω : Ω) :
    IsFiniteMeasure (negativePathMeasure hA ω) := by
  unfold negativePathMeasure
  infer_instance

/-- Fixed-time measurability and right continuity make every signed
Stieltjes interval mass measurable in the sample parameter. -/
theorem measurable_signedMeasure_Ioc
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => A u ω) (Set.Ici t) t)
    (hMeas : ∀ t, Measurable (A t))
    {a b : Time} (hab : a ≤ b) :
    Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) (Ioc a b) := by
  have heq :
      (fun ω => FiniteVariationPath.signedMeasure (hA ω) (Ioc a b)) =
        fun ω => A b ω - A a ω := by
    funext ω
    exact FiniteVariationPath.signedMeasure_Ioc
      (hA ω) (hRight ω) hab
  rw [heq]
  exact (hMeas b).sub (hMeas a)

/-- Measurable limits at both ends make the total signed Stieltjes mass
measurable. -/
theorem measurable_signedMeasure_univ
    (hTop : Measurable fun ω =>
      limUnder atTop (fun t => A t ω))
    (hBot : Measurable fun ω =>
      limUnder atBot (fun t => A t ω)) :
    Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) Set.univ := by
  have heq :
      (fun ω => FiniteVariationPath.signedMeasure (hA ω) Set.univ) =
        fun ω => limUnder atTop (fun t => A t ω) -
          limUnder atBot (fun t => A t ω) := by
    funext ω
    rw [FiniteVariationPath.signedMeasure_eq_vectorMeasure (hA ω)]
    exact (hA ω).vectorMeasure_univ
  rw [heq]
  exact hTop.sub hBot

/-! ### Endpoint sequences -/

/-- Fixed-time measurability and explicit cofinal/coinitial sequences make the
endpoint limits, and hence the total signed Stieltjes mass, measurable. -/
theorem measurable_signedMeasure_univ_of_endpoint_sequences
    (hMeas : ∀ t, Measurable (A t))
    (uTop : ℕ → Time) (huTop : Tendsto uTop atTop atTop)
    (uBot : ℕ → Time) (huBot : Tendsto uBot atTop atBot) :
    Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) Set.univ := by
  apply measurable_signedMeasure_univ hA
  · exact FiniteVariationEndpoint.measurable_limUnder_atTop_of_boundedVariation
      hA hMeas uTop huTop
  · exact FiniteVariationEndpoint.measurable_limUnder_atBot_of_boundedVariation
      hA hMeas uBot huBot

/-- Measurability of total-variation interval masses supplies the positive
Jordan generator masses. -/
theorem measurable_positivePathMeasure_Ioc
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => A u ω) (Set.Ici t) t)
    (hMeas : ∀ t, Measurable (A t))
    (hVariation : ∀ a b, a < b → Measurable fun ω =>
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation.real (Ioc a b))
    (a b : Time) (hab : a < b) :
    Measurable fun ω => positivePathMeasure hA ω (Ioc a b) :=
  measurable_posPart_apply measurableSet_Ioc
    (measurable_signedMeasure_Ioc hA hRight hMeas hab.le)
    (hVariation a b hab)

/-- Measurability of total-variation interval masses supplies the negative
Jordan generator masses. -/
theorem measurable_negativePathMeasure_Ioc
    (hRight : ∀ ω t,
      ContinuousWithinAt (fun u => A u ω) (Set.Ici t) t)
    (hMeas : ∀ t, Measurable (A t))
    (hVariation : ∀ a b, a < b → Measurable fun ω =>
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation.real (Ioc a b))
    (a b : Time) (hab : a < b) :
    Measurable fun ω => negativePathMeasure hA ω (Ioc a b) :=
  measurable_negPart_apply measurableSet_Ioc
    (measurable_signedMeasure_Ioc hA hRight hMeas hab.le)
    (hVariation a b hab)

/-- Signed and total-variation measurability on the whole time space supply
the positive Jordan total mass. -/
theorem measurable_positivePathMeasure_univ
    (hSigned : Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) Set.univ)
    (hVariation : Measurable fun ω =>
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation.real Set.univ) :
    Measurable fun ω => positivePathMeasure hA ω Set.univ :=
  measurable_posPart_apply MeasurableSet.univ hSigned hVariation

/-- Signed and total-variation measurability on the whole time space supply
the negative Jordan total mass. -/
theorem measurable_negativePathMeasure_univ
    (hSigned : Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) Set.univ)
    (hVariation : Measurable fun ω =>
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation.real Set.univ) :
    Measurable fun ω => negativePathMeasure hA ω Set.univ :=
  measurable_negPart_apply MeasurableSet.univ hSigned hVariation

omit [MeasurableSpace Ω] in
/-- Each Jordan part is bounded above by total variation. -/
theorem positivePathMeasure_le_totalVariation (ω : Ω) :
    positivePathMeasure hA ω ≤
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation := by
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_right le_rfl

omit [MeasurableSpace Ω] in
/-- Each Jordan part is bounded above by total variation. -/
theorem negativePathMeasure_le_totalVariation (ω : Ω) :
    negativePathMeasure hA ω ≤
      (FiniteVariationPath.signedMeasure (hA ω)).totalVariation := by
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_left le_rfl

end FiniteVariationKernel

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Endpoint data for finite-variation paths on nonnegative real time

On `ℝ≥0`, the natural-number sequence is cofinal at the upper endpoint and
the constant zero sequence is coinitial at the lower endpoint.  Therefore the
endpoint measurability needed by the finite-variation signed-measure kernel
can be discharged from fixed-time measurability without supplying extra
endpoint sequences.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FiniteVariationKernel

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_signedMeasure_univ_nnreal
    {A : ℝ≥0 → Ω → ℝ}
    (hA : ∀ ω, BoundedVariationOn (fun t => A t ω) Set.univ)
    (hMeas : ∀ t, Measurable (A t)) :
    Measurable fun ω =>
      FiniteVariationPath.signedMeasure (hA ω) Set.univ := by
  apply measurable_signedMeasure_univ_of_endpoint_sequences hA hMeas
  · exact tendsto_natCast_atTop_atTop
  · exact tendsto_atBot.2 fun _ => Filter.Eventually.of_forall fun _ => bot_le

end FiniteVariationKernel

end FTAPTheorem42
