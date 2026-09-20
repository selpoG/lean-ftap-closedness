/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ValueTruncationCadlagLimit

/-!
# Predictable version of the value-truncation limit

The selected predictable projections in the càdlàg value-truncation
certificate have a raw predictable `limUnder` limit.  Their almost-everywhere
uniform convergence identifies that raw limit with the càdlàg candidate on a
single full-measure set.  The pathwise increasing and bounded-variation
properties can therefore be passed to the raw limit, after which the usual
null-set regularization supplies one everywhere right-continuous predictable
bounded-variation version.

The resulting certificate also records the decomposition and residual
martingale identities.  No fixed-time almost-everywhere equality is promoted
to indistinguishability without the common pathwise set supplied below.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-- The predictable, path-regular version of the value-truncation limit.
The raw `limUnder` process is retained so that its predictable construction
and its common pathwise identification with `Pcad` remain explicit. -/
structure ValueTruncationProjectionPredictableLimit
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (terminal : ValueTruncationProjectionTerminalL1Limit
      (F := F) (mu := mu) family)
    (cadlag : ValueTruncationProjectionCadlagLimit
      (F := F) (mu := mu) family terminal) where
  Praw : Process Ω
  Praw_definition : Praw = fun t omega =>
    limUnder atTop (fun n => (family.data (cadlag.cutoff n)).Vp t omega)
  Praw_stronglyPredictable : IsStronglyPredictable F Praw
  Praw_indistinguishable_Pcad : ProcessIndistinguishable mu Praw cadlag.Pcad
  Praw_nonnegative_ae : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Praw t omega
  Praw_monotone_ae : ∀ᵐ omega ∂mu, Monotone (Praw · omega)
  Praw_constant_after_ae : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
    Praw t omega = Praw T omega
  Praw_rightContinuous_ae : ∀ᵐ omega ∂mu, ∀ t,
    ContinuousWithinAt (Praw · omega) (Ici t) t
  Praw_boundedVariation_ae : ∀ᵐ omega ∂mu,
    BoundedVariationOn (Praw · omega) Set.univ
  Pp : Process Ω
  Pp_stronglyPredictable : IsStronglyPredictable F Pp
  Pp_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Pp · omega) (Ici t) t
  Pp_boundedVariation : ∀ omega,
    BoundedVariationOn (Pp · omega) Set.univ
  Pp_indistinguishable_Pcad : ProcessIndistinguishable mu Pp cadlag.Pcad
  Pp_nonnegative_ae : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Pp t omega
  Pp_monotone_ae : ∀ᵐ omega ∂mu, Monotone (Pp · omega)
  Pp_zero_ae : Pp 0 =ᵐ[mu] 0
  Pp_constant_after : ∀ t, T ≤ t → Pp t =ᵐ[mu] Pp T
  Pp_terminal_ae_eq_limit : Pp T =ᵐ[mu] terminal.limit
  decomposition : ProcessIndistinguishable mu
    (fun t omega => U t omega)
    (fun t omega => cadlag.M t omega + Pp t omega)
  residual_martingale : Martingale
    (fun t omega => U t omega - Pp t omega) F mu
  Pp_terminal_integrable : Integrable (Pp T) mu
  Pp_terminal_integral_eq_source :
    (∫ omega, Pp T omega ∂mu) = ∫ omega, U T omega ∂mu

omit [SigmaFiniteFiltration mu F] in
theorem ValueTruncationProjectionCadlagLimit.exists_predictableLimit
    [F.IsRightContinuous]
    {U : Process Ω} {T : NNReal}
    (family : ValueTruncationProjectionFamily
      (F := F) (mu := mu) U T)
    (hU : NormalizedAdaptedCadlagIncreasingProcessData (F := F) U T)
    (hUsual : Filtration.UsualConditions mu F)
    (terminal : ValueTruncationProjectionTerminalL1Limit
      (F := F) (mu := mu) family)
    (cadlag : ValueTruncationProjectionCadlagLimit
      (F := F) (mu := mu) family terminal) :
    Nonempty (ValueTruncationProjectionPredictableLimit
      (F := F) (mu := mu) family terminal cadlag) := by
  let Praw : Process Ω := fun t omega =>
    limUnder atTop (fun n => (family.data (cadlag.cutoff n)).Vp t omega)
  have hPrawPredictable : IsStronglyPredictable F Praw := by
    change StronglyMeasurable[F.predictable]
      (fun p : ℝ≥0 × Ω => limUnder atTop
        (fun n => (family.data (cadlag.cutoff n)).Vp p.1 p.2))
    exact @StronglyMeasurable.limUnder
      ℕ (ℝ≥0 × Ω) ℝ F.predictable _ _ atTop _
      (fun n p => (family.data (cadlag.cutoff n)).Vp p.1 p.2) _ _
      (fun n => by
        let hD := family.data (cadlag.cutoff n)
        exact hD.projection.projection_ready.predictable_version.Vp_isStronglyPredictable)
  have hRawPcad : ProcessIndistinguishable mu Praw cadlag.Pcad := by
    filter_upwards [cadlag.projection_uniform_ae] with omega hUniform
    intro t
    dsimp [Praw]
    exact (hUniform.tendsto_at t).limUnder_eq
  have hPrawLimit : ∀ᵐ omega ∂mu, ∀ t, Tendsto
      (fun n => (family.data (cadlag.cutoff n)).Vp t omega) atTop
        (𝓝 (Praw t omega)) := by
    filter_upwards [hRawPcad, cadlag.projection_uniform_ae] with omega hEq hUniform
    intro t
    rw [hEq t]
    exact hUniform.tendsto_at t
  have hPrawNonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Praw t omega := by
    filter_upwards [hPrawLimit] with omega hLimit
    intro t
    exact ge_of_tendsto' (hLimit t) (fun n =>
      (family.data (cadlag.cutoff n)).projection.projection_ready.predictable_version.Vp_nonnegative
        omega t)
  have hPrawMonotone : ∀ᵐ omega ∂mu, Monotone (Praw · omega) := by
    filter_upwards [hPrawLimit] with omega hLimit
    intro s t hst
    apply le_of_tendsto_of_tendsto (hLimit s) (hLimit t)
    exact Filter.Eventually.of_forall (fun n =>
      (family.data (cadlag.cutoff n)).projection.projection_ready.predictable_version.Vp_monotone
        omega hst)
  have hPrawConstant : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
      Praw t omega = Praw T omega := by
    filter_upwards [hPrawLimit] with omega hLimit
    intro t ht
    have hLimitT : Tendsto
        (fun n => (family.data (cadlag.cutoff n)).Vp t omega) atTop
          (𝓝 (Praw T omega)) := by
      have hEq : (fun n => (family.data (cadlag.cutoff n)).Vp t omega) =
          (fun n => (family.data (cadlag.cutoff n)).Vp T omega) := by
        funext n
        let hD := family.data (cadlag.cutoff n)
        exact hD.projection.projection_ready.predictable_version.Vp_constant_after omega t ht
      rw [hEq]
      exact hLimit T
    exact tendsto_nhds_unique (hLimit t) hLimitT
  have hPrawRight : ∀ᵐ omega ∂mu, ∀ t,
      ContinuousWithinAt (Praw · omega) (Ici t) t := by
    filter_upwards [hRawPcad] with omega hEq
    have hPathEq : (fun s => Praw s omega) =
        fun s => cadlag.Pcad s omega := by
      funext s
      exact hEq s
    rw [hPathEq]
    exact cadlag.Pcad_rightContinuous omega
  have hPrawBoundedVariation : ∀ᵐ omega ∂mu,
      BoundedVariationOn (Praw · omega) Set.univ := by
    filter_upwards [hPrawNonnegative, hPrawMonotone, hPrawConstant]
      with omega hNonnegative hMonotone hConstant
    apply (monotoneOn_univ.2 hMonotone).boundedVariationOn
      (C := Praw T omega)
    intro t _
    rw [abs_of_nonneg (hNonnegative t)]
    by_cases ht : t ≤ T
    · exact hMonotone ht
    · rw [hConstant t (le_of_not_ge ht)]
  have hPrawRegular : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (Praw · omega) (Ici t) t) ∧
        BoundedVariationOn (Praw · omega) Set.univ := by
    filter_upwards [hPrawRight, hPrawBoundedVariation] with omega hRight hBV
    exact ⟨hRight, hBV⟩
  obtain ⟨Pp, hPpPredictable, hPpRight, hPpBV, hPpRaw⟩ :=
    ProcessNullSetRegularization.exists_predictable_rightContinuous_boundedVariation_version
      hUsual hPrawPredictable hPrawRegular
  have hPpPcad : ProcessIndistinguishable mu Pp cadlag.Pcad :=
    hPpRaw.trans hRawPcad
  have hPpNonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Pp t omega := by
    filter_upwards [hPpRaw, hPrawNonnegative] with omega hEq hNonnegative
    intro t
    rw [hEq t]
    exact hNonnegative t
  have hPpMonotone : ∀ᵐ omega ∂mu, Monotone (Pp · omega) := by
    filter_upwards [hPpRaw, hPrawMonotone] with omega hEq hMonotone
    intro s t hst
    change Pp s omega ≤ Pp t omega
    rw [hEq s, hEq t]
    exact hMonotone hst
  have hPpZero : Pp 0 =ᵐ[mu] 0 := by
    exact (hPpPcad.eventuallyEq_at 0).trans cadlag.Pcad_zero_ae
  have hPpConstant : ∀ t, T ≤ t → Pp t =ᵐ[mu] Pp T := by
    intro t ht
    filter_upwards [hPpPcad.eventuallyEq_at t,
      hPpPcad.eventuallyEq_at T, cadlag.Pcad_constant_after t ht]
      with omega hPt hPT hCad
    rw [hPt, hPT, hCad]
  have hPpTerminal : Pp T =ᵐ[mu] terminal.limit := by
    exact (hPpPcad.eventuallyEq_at T).trans cadlag.Pcad_terminal_ae_eq_limit
  have hDecomposition : ProcessIndistinguishable mu
      (fun t omega => U t omega)
      (fun t omega => cadlag.M t omega + Pp t omega) := by
    have hBase : ProcessIndistinguishable mu
        (fun t omega => U t omega)
        (fun t omega => cadlag.M t omega + cadlag.Pcad t omega) := by
      filter_upwards [] with omega
      intro t
      rw [cadlag.Pcad_definition]
      ring
    have hSum : ProcessIndistinguishable mu
        (fun t omega => cadlag.M t omega + cadlag.Pcad t omega)
        (fun t omega => cadlag.M t omega + Pp t omega) :=
      ProcessIndistinguishable.add
        (ProcessIndistinguishable.refl mu cadlag.M) hPpPcad.symm
    exact hBase.trans hSum
  have hResidualIndist : ProcessIndistinguishable mu
      (fun t omega => U t omega - Pp t omega) cadlag.M := by
    filter_upwards [hPpPcad] with omega hEq
    intro t
    have hDef : cadlag.Pcad t omega =
        U t omega - cadlag.M t omega := by
      rw [cadlag.Pcad_definition]
    rw [hEq t, hDef]
    ring
  have hResidualMartingale : Martingale
      (fun t omega => U t omega - Pp t omega) F mu :=
    cadlag.M_martingale.congr (hU.stronglyAdapted.sub
      hPpPredictable.stronglyAdapted)
      (fun t => (hResidualIndist.eventuallyEq_at t).symm)
  have hPpTerminalIntegrable : Integrable (Pp T) mu :=
    terminal.limit_integrable.congr hPpTerminal.symm
  have hPpTerminalIntegral :
      (∫ omega, Pp T omega ∂mu) = ∫ omega, U T omega ∂mu := by
    calc
      (∫ omega, Pp T omega ∂mu) = ∫ omega, terminal.limit omega ∂mu :=
        integral_congr_ae hPpTerminal
      _ = ∫ omega, U T omega ∂mu :=
        terminal.projection_terminal_integral_eq_source
  exact ⟨{
    Praw := Praw
    Praw_definition := rfl
    Praw_stronglyPredictable := hPrawPredictable
    Praw_indistinguishable_Pcad := hRawPcad
    Praw_nonnegative_ae := hPrawNonnegative
    Praw_monotone_ae := hPrawMonotone
    Praw_constant_after_ae := hPrawConstant
    Praw_rightContinuous_ae := hPrawRight
    Praw_boundedVariation_ae := hPrawBoundedVariation
    Pp := Pp
    Pp_stronglyPredictable := hPpPredictable
    Pp_rightContinuous := hPpRight
    Pp_boundedVariation := hPpBV
    Pp_indistinguishable_Pcad := hPpPcad
    Pp_nonnegative_ae := hPpNonnegative
    Pp_monotone_ae := hPpMonotone
    Pp_zero_ae := hPpZero
    Pp_constant_after := hPpConstant
    Pp_terminal_ae_eq_limit := hPpTerminal
    decomposition := hDecomposition
    residual_martingale := hResidualMartingale
    Pp_terminal_integrable := hPpTerminalIntegrable
    Pp_terminal_integral_eq_source := hPpTerminalIntegral }⟩

end HorizonFactorialGrid

end FTAPTheorem42
