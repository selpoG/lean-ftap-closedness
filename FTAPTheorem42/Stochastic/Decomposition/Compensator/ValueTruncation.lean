/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.ComponentPackage
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore

/-!
# Value truncations and coherent compensator packages

An adapted increasing finite-variation process need not have a square-
integrable terminal value.  This module records the elementary value
truncations which do have a deterministic terminal bound.  Each truncation is
then sent directly to the existing coherent square-integrable compensator
producer.

The family compares projections at different truncation levels through the
explicitly increasing difference of two nested caps.  No order preservation
for arbitrary pointwise-ordered sources, nor any level-wise identification of
the underlying rows and weights, is asserted.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## Normalized increasing input -/

/--
The pathwise and filtration data needed for value truncation.  Nonnegativity
is a consequence of `zero` and `monotone`, but is exposed below as a theorem
because it is the key order fact used by the square-integrable adapter.
-/
structure NormalizedAdaptedCadlagIncreasingProcessData
    (U : Process Ω) (T : NNReal) : Prop where
  stronglyAdapted : StronglyAdapted F U
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (U · omega) (Ici t) t
  hasLeftLimits : ProcessHasLeftLimits U
  monotone : ∀ omega, Monotone (U · omega)
  zero : U 0 = 0
  constant_after : ∀ omega t, T ≤ t → U t omega = U T omega

namespace NormalizedAdaptedCadlagIncreasingProcessData

variable {U : Process Ω} {T : NNReal}

theorem value_nonneg
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (t : NNReal) (omega : Ω) :
    0 ≤ U t omega := by
  have hmono := hU.monotone omega (show (0 : NNReal) ≤ t from bot_le)
  have hzero : U 0 omega = 0 := congrFun hU.zero omega
  linarith

end NormalizedAdaptedCadlagIncreasingProcessData

/-! ## The truncation itself -/

/-- The deterministic cap used at level `n`. -/
def valueTruncationCap (n : ℕ) : Real := ((n + 1 : ℕ) : Real)

/-- Pointwise value truncation of an increasing source. -/
noncomputable def valueTruncation
    (U : Process Ω) (n : ℕ) : Process Ω :=
  fun t omega => min (U t omega) (valueTruncationCap n)

namespace NormalizedAdaptedCadlagIncreasingProcessData

variable {U : Process Ω} {T : NNReal}

theorem valueTruncation_stronglyAdapted
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    StronglyAdapted F (valueTruncation U n) := by
  intro t
  change StronglyMeasurable[F t]
    (fun omega => min (U t omega) (valueTruncationCap n))
  exact ((hU.stronglyAdapted t).measurable.min measurable_const).stronglyMeasurable

theorem valueTruncation_rightContinuous
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    ∀ omega t,
      ContinuousWithinAt (valueTruncation U n · omega) (Ici t) t := by
  intro omega t
  change ContinuousWithinAt
    (fun s => min (U s omega) (valueTruncationCap n)) (Ici t) t
  exact (hU.rightContinuous omega t).inf continuous_const.continuousWithinAt

theorem valueTruncation_monotone
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    ∀ omega, Monotone (valueTruncation U n · omega) := by
  intro omega
  change Monotone (fun t => min (U t omega) (valueTruncationCap n))
  exact (hU.monotone omega).min monotone_const

theorem valueTruncation_hasLeftLimits
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    ProcessHasLeftLimits (valueTruncation U n) := by
  intro omega t
  apply tendsto_leftLim_of_tendsto
  refine ⟨min (Function.leftLim (U · omega) t) (valueTruncationCap n), ?_⟩
  change Tendsto
    (fun s => min (U s omega) (valueTruncationCap n)) (𝓝[<] t)
      (𝓝 (min (Function.leftLim (U · omega) t) (valueTruncationCap n)))
  exact (hU.hasLeftLimits omega t).min tendsto_const_nhds

theorem valueTruncation_zero
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    valueTruncation U n 0 = 0 := by
  funext omega
  change min (U 0 omega) (valueTruncationCap n) = 0
  rw [congrFun hU.zero omega]
  exact min_eq_left (by
    dsimp [valueTruncationCap]
    exact_mod_cast Nat.zero_le (n + 1))

theorem valueTruncation_constant_after
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    ∀ omega t, T ≤ t →
      valueTruncation U n t omega = valueTruncation U n T omega := by
  intro omega t ht
  change min (U t omega) (valueTruncationCap n) =
    min (U T omega) (valueTruncationCap n)
  rw [hU.constant_after omega t ht]

theorem valueTruncation_nonneg
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) (t : NNReal) (omega : Ω) :
    0 ≤ valueTruncation U n t omega := by
  change 0 ≤ min (U t omega) (valueTruncationCap n)
  exact le_min (hU.value_nonneg t omega) (by
    dsimp [valueTruncationCap]
    positivity)

theorem valueTruncation_le_source
    (_hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) (t : NNReal) (omega : Ω) :
    valueTruncation U n t omega ≤ U t omega := by
  exact min_le_left _ _

theorem valueTruncation_le_cap
    (_hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) (t : NNReal) (omega : Ω) :
    valueTruncation U n t omega ≤ valueTruncationCap n := by
  exact min_le_right _ _

omit [SigmaFiniteFiltration mu F] in
theorem valueTruncation_terminal_memLp_two
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    MemLp (valueTruncation U n T) (2 : ENNReal) mu := by
  apply MemLp.of_bound (p := (2 : ENNReal)) (μ := mu)
    ((hU.valueTruncation_stronglyAdapted n T).mono (F.le T)).aestronglyMeasurable
    (valueTruncationCap n)
  filter_upwards with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (hU.valueTruncation_nonneg n T omega)]
  exact hU.valueTruncation_le_cap n T omega

/-! ## Source-order facts -/

omit [MeasurableSpace Ω] [SigmaFiniteFiltration mu F] in
theorem valueTruncation_mono_level
    {U : Process Ω} {m n : ℕ} (hmn : m ≤ n) (t : NNReal) (omega : Ω) :
    valueTruncation U m t omega ≤ valueTruncation U n t omega := by
  change min (U t omega) (valueTruncationCap m) ≤
    min (U t omega) (valueTruncationCap n)
  apply min_le_min_left
  dsimp [valueTruncationCap]
  exact_mod_cast Nat.add_le_add_right hmn 1

omit [MeasurableSpace Ω] [SigmaFiniteFiltration mu F] in
theorem valueTruncation_tendsto_source
    {U : Process Ω} (t : NNReal) (omega : Ω) :
    Tendsto (fun n => valueTruncation U n t omega) atTop
      (𝓝 (U t omega)) := by
  have hNat : Tendsto (fun n : ℕ => valueTruncationCap n)
      atTop atTop := by
    dsimp [valueTruncationCap]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hEventually :
      (fun n : ℕ => valueTruncation U n t omega) =ᶠ[atTop]
        (fun _ : ℕ => U t omega) := by
    have hCap : ∀ᶠ n : ℕ in atTop,
        U t omega ≤ valueTruncationCap n :=
      hNat.eventually_ge_atTop (U t omega)
    filter_upwards [hCap] with n hn
    change min (U t omega) (valueTruncationCap n) = U t omega
    exact min_eq_left hn
  exact hEventually.tendsto

/-! The increment between two nested caps is increasing as a function of the
source value.  This is the order input needed by the projection comparison
consumer below. -/

omit [MeasurableSpace Ω] [SigmaFiniteFiltration mu F] in
theorem valueTruncation_difference_mono
    {a b x y : Real} (hab : a ≤ b) (hxy : x ≤ y) :
    min x b - min x a ≤ min y b - min y a := by
  by_cases hyb : y ≤ a
  · have hxa : x ≤ a := hxy.trans hyb
    have hxb : x ≤ b := hxa.trans hab
    have hyb' : y ≤ b := hyb.trans hab
    rw [min_eq_left hxb, min_eq_left hxa,
      min_eq_left hyb', min_eq_left hyb]
    simp
  · have hay : a ≤ y := le_of_not_ge hyb
    by_cases hxa : x ≤ a
    · have hxb : x ≤ b := hxa.trans hab
      by_cases hyb' : y ≤ b
      · rw [min_eq_left hxb, min_eq_left hxa,
          min_eq_left hyb', min_eq_right hay]
        nlinarith
      · have hby : b ≤ y := le_of_not_ge hyb'
        rw [min_eq_left hxb, min_eq_left hxa,
          min_eq_right hby, min_eq_right hay]
        nlinarith
    · have hax : a ≤ x := le_of_not_ge hxa
      by_cases hyb' : y ≤ b
      · have hxb : x ≤ b := hxy.trans hyb'
        rw [min_eq_left hxb, min_eq_right hax,
          min_eq_left hyb', min_eq_right hay]
        exact sub_le_sub_right hxy a
      · have hby : b ≤ y := le_of_not_ge hyb'
        rw [min_eq_right hby, min_eq_right hay]
        by_cases hxb : x ≤ b
        · rw [min_eq_left hxb, min_eq_right hax]
          exact sub_le_sub_right hxb a
        · have hbx : b ≤ x := le_of_not_ge hxb
          rw [min_eq_right hbx, min_eq_right hax]

/-! ## The square-integrable adapter -/

omit [SigmaFiniteFiltration mu F] in
theorem valueTruncation_squareIntegrableIncreasingProcessData
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (n : ℕ) :
    SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) (valueTruncation U n) T := by
  exact {
    stronglyAdapted := hU.valueTruncation_stronglyAdapted n
    rightContinuous := hU.valueTruncation_rightContinuous n
    monotone := hU.valueTruncation_monotone n
    zero := hU.valueTruncation_zero n
    constant_after := hU.valueTruncation_constant_after n
    terminal_memLp_two := hU.valueTruncation_terminal_memLp_two n }

omit [SigmaFiniteFiltration mu F] in
theorem valueTruncation_difference_squareIntegrableIncreasingProcessData
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    {m n : ℕ} (hmn : m ≤ n) :
    SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu)
      (valueTruncation U n - valueTruncation U m) T := by
  let hVn := hU.valueTruncation_squareIntegrableIncreasingProcessData
    (mu := mu) n
  let hVm := hU.valueTruncation_squareIntegrableIncreasingProcessData
    (mu := mu) m
  refine {
    stronglyAdapted := hVn.stronglyAdapted.sub hVm.stronglyAdapted
    rightContinuous := fun omega t =>
      (hVn.rightContinuous omega t).sub (hVm.rightContinuous omega t)
    monotone := ?_
    zero := ?_
    constant_after := ?_
    terminal_memLp_two := hVn.terminal_memLp_two.sub hVm.terminal_memLp_two }
  · intro omega s t hst
    change valueTruncation U n s omega - valueTruncation U m s omega ≤
      valueTruncation U n t omega - valueTruncation U m t omega
    change min (U s omega) (valueTruncationCap n) -
        min (U s omega) (valueTruncationCap m) ≤
      min (U t omega) (valueTruncationCap n) -
        min (U t omega) (valueTruncationCap m)
    exact valueTruncation_difference_mono
      (a := valueTruncationCap m) (b := valueTruncationCap n)
      (by
        dsimp [valueTruncationCap]
        exact_mod_cast Nat.add_le_add_right hmn 1)
      (hU.monotone omega hst)
  · funext omega
    change valueTruncation U n 0 omega - valueTruncation U m 0 omega = 0
    rw [congrFun hVn.zero omega, congrFun hVm.zero omega]
    simp
  · intro omega t ht
    change valueTruncation U n t omega - valueTruncation U m t omega =
      valueTruncation U n T omega - valueTruncation U m T omega
    rw [hU.valueTruncation_constant_after n omega t ht,
      hU.valueTruncation_constant_after m omega t ht]

end NormalizedAdaptedCadlagIncreasingProcessData

/-! ## Level-wise coherent projection certificates -/

/-- The coherent square-integrable output at one value-truncation level. -/
structure ValueTruncationProjectionCertificate
    (U : Process Ω) (T : NNReal) (n : ℕ) where
  hV : SquareIntegrableIncreasingProcessData
    (F := F) (mu := mu) (valueTruncation U n) T
  package : SquareIntegrablePredictableCompensatorComponentPackage
    (F := F) (mu := mu) (valueTruncation U n) T
  badPred : Set Ω
  Vp : Process Ω
  projection : SquareIntegrablePredictableCompensatorDualProjectionData
    package badPred Vp

/-- A family of level-wise coherent projection certificates. -/
structure ValueTruncationProjectionFamily
    (U : Process Ω) (T : NNReal) where
  data : ∀ n : ℕ,
    ValueTruncationProjectionCertificate
      (F := F) (mu := mu) U T n

/-! ## Comparison through an increasing source difference -/

/-
The comparison is deliberately stated with the increasing difference as an
explicit hypothesis.  Pointwise order of two increasing paths alone does not
order their Stieltjes increments, so it is not enough for this argument.
-/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableDualProjection_order_of_increasing_difference
    [F.IsRightContinuous]
    {U V : Process Ω} {T : NNReal}
    {pkgU : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) U T}
    {pkgV : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T}
    {badU badV : Set Ω} {PU PV : Process Ω}
    (hP : SquareIntegrablePredictableCompensatorDualProjectionData
      pkgU badU PU)
    (hQ : SquareIntegrablePredictableCompensatorDualProjectionData
      pkgV badV PV)
    (hW : SquareIntegrableIncreasingProcessData (F := F) (mu := mu)
      (fun t omega => V t omega - U t omega) T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∀ᵐ omega ∂mu, ∀ t, PU t omega ≤ PV t omega := by
  obtain ⟨pkgW, badW, PW, hR⟩ :=
    exists_squareIntegrablePredictableCompensatorDualProjection
      (F := F) (mu := mu) hW hUsual
  have hDiffResidual : Martingale
      (fun t omega => (V t omega - PV t omega) -
        (U t omega - PU t omega)) F mu :=
    hQ.residual_martingale.sub hP.residual_martingale
  have hWResidual : Martingale
      (fun t omega => (V t omega - U t omega) - PW t omega) F mu :=
    hR.residual_martingale
  let A : Process Ω := fun t omega =>
    (PV t omega - PU t omega) - PW t omega
  have hAPredictable : IsStronglyPredictable F A := by
    unfold IsStronglyPredictable at ⊢
    dsimp [A]
    exact (hQ.projection_ready.predictable_version.Vp_isStronglyPredictable.sub
      hP.projection_ready.predictable_version.Vp_isStronglyPredictable).sub
      hR.projection_ready.predictable_version.Vp_isStronglyPredictable
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    intro omega t
    dsimp [A]
    exact ((hQ.projection_ready.predictable_version.Vp_rightContinuous omega t).sub
      (hP.projection_ready.predictable_version.Vp_rightContinuous omega t)).sub
      (hR.projection_ready.predictable_version.Vp_rightContinuous omega t)
  have hABV : ∀ omega, BoundedVariationOn (A · omega) Set.univ := by
    have hQBV : ∀ omega, BoundedVariationOn (PV · omega) Set.univ :=
      boundedVariationOn_of_monotone_nonnegative_constantAfter
        hQ.projection_ready.predictable_version.Vp_nonnegative
        hQ.projection_ready.predictable_version.Vp_monotone
        hQ.projection_ready.predictable_version.Vp_constant_after
    have hPBV : ∀ omega, BoundedVariationOn (PU · omega) Set.univ :=
      boundedVariationOn_of_monotone_nonnegative_constantAfter
        hP.projection_ready.predictable_version.Vp_nonnegative
        hP.projection_ready.predictable_version.Vp_monotone
        hP.projection_ready.predictable_version.Vp_constant_after
    have hWBV : ∀ omega, BoundedVariationOn (PW · omega) Set.univ :=
      boundedVariationOn_of_monotone_nonnegative_constantAfter
        hR.projection_ready.predictable_version.Vp_nonnegative
        hR.projection_ready.predictable_version.Vp_monotone
        hR.projection_ready.predictable_version.Vp_constant_after
    intro omega
    dsimp [A]
    exact boundedVariationOn_add
      (boundedVariationOn_add (hQBV omega)
        (boundedVariationOn_neg (hPBV omega)))
      (boundedVariationOn_neg (hWBV omega))
  have hAZero : A 0 = 0 := by
    funext omega
    dsimp [A]
    rw [congrFun hQ.projection_ready.predictable_version.Vp_zero omega,
      congrFun hP.projection_ready.predictable_version.Vp_zero omega,
      congrFun hR.projection_ready.predictable_version.Vp_zero omega]
    simp
  have hAResidual : Martingale A F mu := by
    apply (hWResidual.sub hDiffResidual).congr hAPredictable.stronglyAdapted
    intro t
    filter_upwards [] with omega
    dsimp [A]
    ring
  have hAZeroIndist : ProcessIndistinguishable mu A (fun _ _ => 0) :=
    predictableFiniteVariationLocalMartingale_eq_zero_of_zero
      hUsual (ProbabilityTheory.Locally.of_prop hAResidual)
      hAPredictable hARight hABV hAZero
  filter_upwards [hAZeroIndist] with omega hω
  intro t
  have hEq := hω t
  have hNonneg :=
    hR.projection_ready.predictable_version.Vp_nonnegative omega t
  dsimp [A] at hEq
  have hDiff : 0 ≤ PV t omega - PU t omega := by
    linarith
  exact sub_nonneg.mp hDiff

theorem squareIntegrableDualProjection_terminal_integral_eq_source
    {V : Process Ω} {T : NNReal}
    {pkg : SquareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) V T}
    {bad : Set Ω} {Vp : Process Ω}
    (hP : SquareIntegrablePredictableCompensatorDualProjectionData
      pkg bad Vp) :
    (∫ omega, Vp T omega ∂mu) = ∫ omega, V T omega ∂mu := by
  have hRes0 : Integrable (fun omega => V 0 omega - Vp 0 omega) mu :=
    hP.residual_integrable 0
  have hResT : Integrable (fun omega => V T omega - Vp T omega) mu :=
    hP.residual_integrable T
  have hSet := hP.residual_martingale.setIntegral_eq
    (i := (0 : NNReal)) (j := T) bot_le (MeasurableSet.univ)
  have hZero : (fun omega => V 0 omega - Vp 0 omega) =ᵐ[mu] 0 := by
    filter_upwards [] with omega
    rw [congrFun pkg.hV.zero omega,
      congrFun hP.projection_ready.predictable_version.Vp_zero omega]
    simp
  have hRes0Int : (∫ omega, V 0 omega - Vp 0 omega ∂mu) = 0 :=
    integral_eq_zero_of_ae hZero
  have hSet' : (∫ omega, V 0 omega - Vp 0 omega ∂mu) =
      ∫ omega, V T omega - Vp T omega ∂mu := by
    simpa only [Measure.restrict_univ] using hSet
  have hResTInt : (∫ omega, V T omega - Vp T omega ∂mu) = 0 := by
    rw [← hSet', hRes0Int]
  have hVT : Integrable (V T) mu :=
    pkg.hV.terminal_memLp_two.integrable (by norm_num)
  have hVpT : Integrable (Vp T) mu :=
    hP.Vp_terminal_memLp_two.integrable (by norm_num)
  have hSub : (∫ omega, V T omega - Vp T omega ∂mu) =
      (∫ omega, V T omega ∂mu) - ∫ omega, Vp T omega ∂mu :=
    integral_sub hVT hVpT
  rw [hSub] at hResTInt
  linarith

omit [SigmaFiniteFiltration mu F] in
theorem exists_valueTruncationProjectionCertificate
    (U : Process Ω) (T : NNReal)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F) (n : ℕ) :
    Nonempty (ValueTruncationProjectionCertificate
      (F := F) (mu := mu) U T n) := by
  let hV : SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) (valueTruncation U n) T :=
    hU.valueTruncation_squareIntegrableIncreasingProcessData n
  obtain ⟨pkg, badPred, Vp, hProjection⟩ :=
    exists_squareIntegrablePredictableCompensatorDualProjection
      (F := F) (mu := mu) hV hUsual
  exact ⟨{
    hV := hV
    package := pkg
    badPred := badPred
    Vp := Vp
    projection := hProjection }⟩

omit [SigmaFiniteFiltration mu F] in
theorem exists_valueTruncationProjectionFamily
    (U : Process Ω) (T : NNReal)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T) := by
  let data : ∀ n : ℕ,
      ValueTruncationProjectionCertificate
        (F := F) (mu := mu) U T n := fun n =>
    Classical.choice
      (exists_valueTruncationProjectionCertificate
        (F := F) (mu := mu) U T hU hUsual n)
  exact ⟨{ data := data }⟩

namespace ValueTruncationProjectionFamily

variable {U : Process Ω} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
theorem projection_order
    [F.IsRightContinuous]
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F)
    {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ omega ∂mu, ∀ t,
      (family.data m).Vp t omega ≤ (family.data n).Vp t omega := by
  let hM := family.data m
  let hN := family.data n
  exact squareIntegrableDualProjection_order_of_increasing_difference
    hM.projection hN.projection
    (hU.valueTruncation_difference_squareIntegrableIncreasingProcessData hmn)
    hUsual

theorem projection_terminal_integral_eq_source
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T) (n : ℕ) :
    (∫ omega, (family.data n).Vp T omega ∂mu) =
      ∫ omega, valueTruncation U n T omega ∂mu := by
  exact squareIntegrableDualProjection_terminal_integral_eq_source
    (family.data n).projection

end ValueTruncationProjectionFamily

end HorizonFactorialGrid

end FTAPTheorem42
