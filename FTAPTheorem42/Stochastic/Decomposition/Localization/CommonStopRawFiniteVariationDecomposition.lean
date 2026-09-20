/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.RawFiniteVariationCore
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopNestedGridVariation

/-!
# A raw finite-variation residual for the common-stop rows

The common-stop rows already carry one exact source decomposition. This
module uses the same strict subsequence as the cadlag martingale limit and
the nested-grid variation estimate to construct the full-path residual
A = X^alpha - M. The variation conclusion is retained almost everywhere;
the later null-set regularisation is responsible for changing this to an
everywhere statement.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

structure CommonStopRawFiniteVariationDecompositionData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
    (Nbar Bbar Xbar : Nat → Process Omega)
    (M : Process Omega) (cutoff : Nat → Nat)
    (A : Process Omega) : Prop where
  nestedGrid : CommonStoppedResidualConvexRowsNestedGridVariationData
    endpoint v Z Nbar Bbar Xbar M cutoff
  residual : A = commonStopRawFiniteVariation (S := S) alpha M
  source_decomposition : ∀ t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      M t omega + A t omega
  stronglyAdapted : StronglyAdapted F A
  adapted : Adapted F A
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  hasLeftLimits : ProcessHasLeftLimits A
  zero_ae : A 0 =ᵐ[mu] 0
  constant_after_ae : ∀ᵐ omega ∂mu, ∀ t, T ≤ t → A t omega = A T omega
  residual_tendstoUniformlyOn_ae : ∀ᵐ omega ∂mu,
    TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
      (fun t => A t omega) atTop (Iic T)
  grid_variation_bound_ae : ∀ᵐ omega ∂mu, ∀ r,
    commonStoppedRowsResidualGridVariation A T r omega ≤
      commonStoppedRowsResidualVariationBound a source.bound
  full_variation_bound_ae : ∀ᵐ omega ∂mu,
    eVariationOn (A · omega) Set.univ ≤
      ENNReal.ofReal (commonStoppedRowsResidualVariationBound a source.bound)

/-! ## Pointwise identities and path regularity -/

private theorem commonStopRawFiniteVariation_stronglyAdapted
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    {source : BoundedSemimartingaleSource S F mu}
    (M : Process Omega) (hM : StronglyAdapted F M)
    (hAlpha : IsStoppingTime F alpha) :
    StronglyAdapted F (commonStopRawFiniteVariation (S := S) alpha M) := by
  have hStopped :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      source.stronglyAdapted hAlpha source.rightContinuous
  have hInitial : StronglyAdapted F (fun _ omega => S 0 omega) := by
    intro t
    exact (source.stronglyAdapted 0).mono (F.mono bot_le)
  have hSub := (hStopped.sub hInitial).sub hM
  change StronglyAdapted F
    ((MeasureTheory.stoppedProcess S alpha - (fun _ omega => S 0 omega)) - M)
  exact hSub

private theorem commonStopRawFiniteVariation_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    {source : BoundedSemimartingaleSource S F mu}
    (M : Process Omega)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t) :
    ∀ omega t,
      ContinuousWithinAt
        (commonStopRawFiniteVariation (S := S) alpha M · omega) (Ici t) t := by
  have hStopped :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (τ := alpha) S source.rightContinuous
  intro omega t
  change ContinuousWithinAt
    (fun u => MeasureTheory.stoppedProcess S alpha u omega - S 0 omega - M u omega)
    (Ici t) t
  exact ((hStopped omega t).sub continuousWithinAt_const).sub (hMRight omega t)

private theorem commonStopRawFiniteVariation_hasLeftLimits
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {alpha : Omega → WithTop NNReal}
    {source : BoundedSemimartingaleSource S F mu}
    (M : Process Omega) (hMLeft : ProcessHasLeftLimits M) :
    ProcessHasLeftLimits (commonStopRawFiniteVariation (S := S) alpha M) := by
  have hStopped := source.hasLeftLimits.stoppedProcess alpha
  have hInitial : ProcessHasLeftLimits (fun _ omega => S 0 omega) := by
    intro omega t
    apply tendsto_leftLim_of_tendsto
    exact ⟨S 0 omega, tendsto_const_nhds⟩
  change ProcessHasLeftLimits (fun t omega =>
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega - M t omega)
  exact (hStopped.sub hInitial).sub hMLeft

/-! ## Public endpoint -/

theorem commonStop_rawFiniteVariationDecomposition
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Omega} {M : Process Omega}
    {cutoff : Nat → Nat}
    (hData : CommonStoppedResidualConvexRowsNestedGridVariationData
      endpoint v Z Nbar Bbar Xbar M cutoff) :
    ∃ A : Process Omega,
      CommonStopRawFiniteVariationDecompositionData
        endpoint v Z Nbar Bbar Xbar M cutoff A := by
  let A : Process Omega := commonStopRawFiniteVariation (S := S) alpha M
  have hMAdapted : StronglyAdapted F M := hData.cadlag.M_martingale.stronglyAdapted
  have hAAdapted : StronglyAdapted F A := by
    exact commonStopRawFiniteVariation_stronglyAdapted (source := source) M hMAdapted
      endpoint.alpha_stopping
  have hARight : ∀ omega t, ContinuousWithinAt (A · omega) (Ici t) t := by
    simpa only [A] using commonStopRawFiniteVariation_rightContinuous (source := source) M
      hData.cadlag.M_rightContinuous
  have hALeft : ProcessHasLeftLimits A := by
    simpa only [A] using commonStopRawFiniteVariation_hasLeftLimits (source := source) M
      hData.cadlag.M_leftLimits
  have hAZero : A 0 =ᵐ[mu] 0 := by
    simpa only [A] using commonStopRawFiniteVariation_zero_ae hData.cadlag.M_zero
  have hAlphaLeT : ∀ omega, alpha omega ≤ (T : WithTop NNReal) := by
    intro omega
    exact (endpoint.alpha_le_alphaSeq 0 omega).trans
      (endpoint.alphaSeq_le_T 0 omega)
  have hAConst : ∀ᵐ omega ∂mu, ∀ t, T ≤ t → A t omega = A T omega := by
    simpa only [A] using commonStopRawFiniteVariation_constant_after_ae
      (F := F) (mu := mu) hAlphaLeT hData.cadlag.M_rightContinuous
      hData.cadlag.M_constant_after
  have hAUniform : ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun q t => Bbar (cutoff q) t omega)
        (fun t => A t omega) atTop (Iic T) := by
    simpa only [A] using commonStopRawFiniteVariation_residual_tendstoUniformlyOn_ae
      hData.cadlag.rows_tendstoUniformlyOn_ae
      hData.cadlag.convexification.stoppedSource_eq_add (by rfl)
  have hGrid : ∀ᵐ omega ∂mu, ∀ r,
      commonStoppedRowsResidualGridVariation A T r omega ≤
        commonStoppedRowsResidualVariationBound a source.bound :=
    commonStopRawFiniteVariation_grid_variation_bound_ae
      hData.variation_bound_cutoff_grid hAUniform
  have hFull : ∀ᵐ omega ∂mu,
      eVariationOn (A · omega) Set.univ ≤
        ENNReal.ofReal (commonStoppedRowsResidualVariationBound a source.bound) := by
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
      _ ≤ ENNReal.ofReal
          (commonStoppedRowsResidualVariationBound a source.bound) := by
        apply iSup_le
        intro r
        calc
          FiniteVariationFactorialApproximation.eGridVariation (A · omega) T r ≤
              ENNReal.ofReal
                (commonStoppedRowsResidualGridVariation A T
                  (max r (Nat.ceil T)) omega) :=
            commonStopRawFiniteVariation_eGridVariation_le_grid T r omega
          _ ≤ ENNReal.ofReal
              (commonStoppedRowsResidualVariationBound a source.bound) :=
            ENNReal.ofReal_le_ofReal (hGridOmega (max r (Nat.ceil T)))
  refine ⟨A, ?_⟩
  exact
    { nestedGrid := hData
      residual := rfl
      source_decomposition := commonStopRawFiniteVariation_source_decomposition M A rfl
      stronglyAdapted := hAAdapted
      adapted := hAAdapted.adapted
      rightContinuous := hARight
      hasLeftLimits := hALeft
      zero_ae := hAZero
      constant_after_ae := hAConst
      residual_tendstoUniformlyOn_ae := hAUniform
      grid_variation_bound_ae := hGrid
      full_variation_bound_ae := hFull }

theorem exists_commonStop_rawFiniteVariationDecomposition
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      ∃ endpoint : CommonStoppedRowsEndpoint
        (eta := eta) u selection a T alphaSeq alpha R hUsual source,
        ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
          (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
          (cutoff : Nat → Nat) (A : Process Omega),
          CommonStopRawFiniteVariationDecompositionData endpoint v Z Nbar Bbar
            Xbar M cutoff A := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
      Nbar, Bbar, Xbar, M, cutoff, hData⟩ :=
    exists_commonStoppedResidualConvexRows_nestedGridVariation hUsual hS source T heta
  obtain ⟨A, hA⟩ := commonStop_rawFiniteVariationDecomposition endpoint hData
  exact ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
    Nbar, Bbar, Xbar, M, cutoff, A, hA⟩

end HorizonFactorialGrid

end FTAPTheorem42
