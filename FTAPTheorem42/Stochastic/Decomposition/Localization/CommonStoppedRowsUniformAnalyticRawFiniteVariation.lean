/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStoppedRowsUniformAnalyticNestedGridVariation
import FTAPTheorem42.Stochastic.Decomposition.Source.RawFiniteVariationCore

/-!
# Raw finite-variation residual for the source-independent analytic rows

This module consumes the generic nested-grid certificate and constructs the
raw residual `A = X^alpha - M`.  The finite-grid estimates are passed to the
continuous-time variation theorem only after right-continuity and constancy
after the horizon have been established.  No source-specific boundedness
record is used here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! ## The generic raw residual certificate -/

structure CommonStoppedRowsUniformAnalyticRawFiniteVariationData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B V L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega}
    {M : Process Omega} {cutoff : Nat → Nat}
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff)
    (A : Process Omega) : Prop where
  residual : A = commonStopRawFiniteVariation (S := S) alpha M
  source_decomposition : ∀ t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      M t omega + A t omega
  stronglyAdapted : StronglyAdapted F A
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  hasLeftLimits : ProcessHasLeftLimits A
  zero_ae : A 0 =ᵐ[mu] 0
  constant_after_ae : ∀ᵐ omega ∂mu, ∀ t, T ≤ t → A t omega = A T omega
  residual_tendstoUniformlyOn_ae : ∀ᵐ omega ∂mu,
    TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
      (fun t => A t omega) atTop (Iic T)
  grid_variation_bound_ae : ∀ᵐ omega ∂mu, ∀ r,
    commonStoppedRowsResidualGridVariation A T r omega ≤ V omega
  full_variation_bound_ae : ∀ᵐ omega ∂mu,
    eVariationOn (A · omega) Set.univ ≤ ENNReal.ofReal (V omega)

/-! ## Source-independent regularity and finite-grid bridges -/

private theorem commonStoppedRowsUniformAnalyticRawFiniteVariation_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    (M : Process Omega) (hM : StronglyAdapted F M)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t) :
    StronglyAdapted F (commonStopRawFiniteVariation (S := S) alpha M) := by
  have hStopped :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hSAdapted hAlphaStop hSRight
  have hInitial : StronglyAdapted F (fun _ omega => S 0 omega) := by
    intro t
    exact (hSAdapted 0).mono (F.mono bot_le)
  have hSub := (hStopped.sub hInitial).sub hM
  change StronglyAdapted F
    ((MeasureTheory.stoppedProcess S alpha - (fun _ omega => S 0 omega)) - M)
  exact hSub

private theorem commonStoppedRowsUniformAnalyticRawFiniteVariation_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    (M : Process Omega)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t) :
    ∀ omega t, ContinuousWithinAt
      (commonStopRawFiniteVariation (S := S) alpha M · omega) (Ici t) t := by
  have hStopped :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (τ := alpha) S hSRight
  intro omega t
  change ContinuousWithinAt
    (fun u => MeasureTheory.stoppedProcess S alpha u omega - S 0 omega - M u omega)
    (Ici t) t
  exact ((hStopped omega t).sub continuousWithinAt_const).sub (hMRight omega t)

private theorem commonStoppedRowsUniformAnalyticRawFiniteVariation_hasLeftLimits
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    (M : Process Omega) (hSLeft : ProcessHasLeftLimits S)
    (hMLeft : ProcessHasLeftLimits M) :
    ProcessHasLeftLimits (commonStopRawFiniteVariation (S := S) alpha M) := by
  have hStopped := hSLeft.stoppedProcess alpha
  have hInitial : ProcessHasLeftLimits (fun _ omega => S 0 omega) := by
    intro omega t
    apply tendsto_leftLim_of_tendsto
    exact ⟨S 0 omega, tendsto_const_nhds⟩
  change ProcessHasLeftLimits (fun t omega =>
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega - M t omega)
  exact (hStopped.sub hInitial).sub hMLeft

/-! ## Public raw finite-variation endpoint -/

theorem commonStoppedRowsUniformAnalytic_rawFiniteVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B V L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    (hSAdapted : StronglyAdapted F S)
    (hSRight : ∀ omega t, ContinuousWithinAt (S · omega) (Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff) :
    ∃ A : Process Omega,
      CommonStoppedRowsUniformAnalyticRawFiniteVariationData hNested A := by
  let A : Process Omega := commonStopRawFiniteVariation (S := S) alpha M
  have hMAdapted : StronglyAdapted F M :=
    hNested.cadlag.M_martingale.stronglyAdapted
  have hAAdapted : StronglyAdapted F A := by
    simpa only [A] using
      commonStoppedRowsUniformAnalyticRawFiniteVariation_stronglyAdapted
        (S := S) (F := F) (mu := mu) (alpha := alpha)
        (hAlphaStop := hAlphaStop) M hMAdapted hSAdapted hSRight
  have hARight : ∀ omega t, ContinuousWithinAt (A · omega) (Ici t) t := by
    simpa only [A] using
      commonStoppedRowsUniformAnalyticRawFiniteVariation_rightContinuous
        (S := S) (F := F) (mu := mu) (alpha := alpha)
        M hSRight hNested.cadlag.M_rightContinuous
  have hALeft : ProcessHasLeftLimits A := by
    simpa only [A] using
      commonStoppedRowsUniformAnalyticRawFiniteVariation_hasLeftLimits
        (S := S) (F := F) (mu := mu) (alpha := alpha)
        M hSLeft hNested.cadlag.M_leftLimits
  have hAZero : A 0 =ᵐ[mu] 0 := by
    simpa only [A] using commonStopRawFiniteVariation_zero_ae
      (S := S) (mu := mu) (alpha := alpha) (M := M) hNested.cadlag.M_zero
  have hAConst : ∀ᵐ omega ∂mu, ∀ t, T ≤ t → A t omega = A T omega := by
    simpa only [A] using commonStopRawFiniteVariation_constant_after_ae
      (F := F) (mu := mu) data.alpha_le_horizon
      hNested.cadlag.M_rightContinuous hNested.cadlag.M_constant_after
  have hAUniform : ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
        (fun t => A t omega) atTop (Iic T) := by
    simpa only [A] using
      commonStopRawFiniteVariation_residual_tendstoUniformlyOn_ae
        hNested.cadlag.rows_tendstoUniformlyOn_ae
        hNested.cadlag.convexification.stoppedSource_eq_add (by rfl)
  have hGrid : ∀ᵐ omega ∂mu, ∀ r,
      commonStoppedRowsResidualGridVariation A T r omega ≤ V omega :=
    commonStopRawFiniteVariation_grid_variation_bound_ae
      hNested.variation_bound_cutoff_grid hAUniform
  have hFull : ∀ᵐ omega ∂mu,
      eVariationOn (A · omega) Set.univ ≤ ENNReal.ofReal (V omega) := by
    filter_upwards [hAConst, hGrid] with omega hConst hGridOmega
    have hRight : ∀ t, ContinuousWithinAt (A · omega) (Ici t) t := hARight omega
    have hSet : (Set.Iic T : Set NNReal) = Set.Icc 0 T := by
      ext t
      constructor
      · intro ht
        exact ⟨bot_le, ht⟩
      · intro ht
        exact ht.2
    have hClamp :
        eVariationOn (A · omega) Set.univ ≤ eVariationOn (A · omega) (Set.Iic T) := by
      have hEq : (fun t => A t omega) =
          (fun t => A (min t T) omega) := by
        funext t
        by_cases ht : t ≤ T
        · simp [min_eq_left ht]
        · have hTt : T ≤ t := le_of_not_ge ht
          simpa [min_eq_right hTt] using hConst t hTt
      have hEq' : (A · omega) =
          (fun t : NNReal => A (min t T) omega) := by
        funext t
        exact congrFun hEq t
      have hComp := eVariationOn.comp_le_of_monotoneOn
        (f := fun t : NNReal => A t omega) (s := Set.Iic T) (t := Set.univ)
        (fun t : NNReal => min t T)
        ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn Set.univ)
        (fun t _ => show min t T ≤ T from min_le_right _ _)
      calc
        eVariationOn (A · omega) Set.univ =
            eVariationOn (fun t : NNReal => A (min t T) omega) Set.univ := by
          rw [hEq']
        _ ≤ eVariationOn (A · omega) (Set.Iic T) := hComp
    rw [hSet] at hClamp
    calc
      eVariationOn (A · omega) Set.univ ≤
          eVariationOn (A · omega) (Set.Icc 0 T) := hClamp
      _ = ⨆ r, FiniteVariationFactorialApproximation.eGridVariation (A · omega) T r :=
        FiniteVariationFactorialApproximation.eVariationOn_Icc_eq_iSup_eGridVariation
          (A · omega) hRight T
      _ ≤ ENNReal.ofReal (V omega) := by
        apply iSup_le
        intro r
        calc
          FiniteVariationFactorialApproximation.eGridVariation (A · omega) T r ≤
              ENNReal.ofReal
                (commonStoppedRowsResidualGridVariation A T
                  (max r (Nat.ceil T)) omega) :=
            commonStopRawFiniteVariation_eGridVariation_le_grid T r omega
          _ ≤ ENNReal.ofReal (V omega) :=
            ENNReal.ofReal_le_ofReal (hGridOmega (max r (Nat.ceil T)))
  refine ⟨A, ?_⟩
  exact
    { residual := rfl
      source_decomposition := commonStopRawFiniteVariation_source_decomposition M A rfl
      stronglyAdapted := hAAdapted
      rightContinuous := hARight
      hasLeftLimits := hALeft
      zero_ae := hAZero
      constant_after_ae := hAConst
      residual_tendstoUniformlyOn_ae := hAUniform
      grid_variation_bound_ae := hGrid
      full_variation_bound_ae := hFull }

end HorizonFactorialGrid

end FTAPTheorem42
