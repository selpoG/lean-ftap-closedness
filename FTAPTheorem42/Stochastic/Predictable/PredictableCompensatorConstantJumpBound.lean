/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.CumulativeVariationJumpEnumeration
import FTAPTheorem42.Stochastic.Martingale.Basic.LocalMartingaleAnnouncedJumpControl

/-!
# Constant jump bounds for predictable finite-variation components

Only the raw decomposition and its path regularity are used here. No
membership in a stochastic-integral realization carrier is asserted.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {S : Process Ω}
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- A constant bound on all jumps of a raw gain bounds its predictable
finite-variation jumps up to a positive horizon, on one common full-measure set.
The completed crossing times may take the dummy value `T + 1`. -/
theorem SIntegrableStrategy.abs_finiteVariationLeftJump_le_const
    (H : SIntegrableStrategy D)
    (hUsual : Filtration.UsualConditions mu F)
    (hMLeft : ProcessHasLeftLimits H.martingalePart)
    {c : Real} (hc : 0 ≤ c) {T : NNReal} (hT : 0 < T)
    (hJump : ∀ᵐ omega ∂mu, ∀ t,
      |processLeftJump H.stochasticIntegral t omega| ≤ c) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      |processLeftJump H.finiteVariationPart t omega| ≤ c := by
  let sigma := CumulativeVariationJumpEnumeration.jumpCrossingTime H T
  have hBound : ∀ n, ∀ᵐ omega ∂mu,
      |processLeftJump H.finiteVariationPart (sigma n omega) omega| ≤ c := by
    intro n
    have hStop := CumulativeVariationJumpEnumeration.jumpCrossingTime_isStoppingTime
      H H.finiteVariationPart_isRightContinuous T n
    have h := LocalMartingale.finiteVariationLeftJump_ae_le_condExp_of_announcement
      H.martingalePart_isLocalMartingale
      (CumulativeVariationJumpEnumeration.jumpCrossingTime_announcement
        hUsual H H.finiteVariationPart_isRightContinuous hT n)
      (T + 1) hStop
      (CumulativeVariationJumpEnumeration.jumpCrossingTime_le H T n)
      H.martingalePart_isRightContinuous hMLeft
      (IsStronglyPredictable.stronglyMeasurable_sampledLeftJump
        H.processLeftJump_finiteVariationPart_isPredictable (sigma n))
      (fun _ => c) (integrable_const c)
      (by
        filter_upwards [H.processLeftJump_eq_components hMLeft] with omega hOmega
        exact hOmega (sigma n omega))
      (by
        filter_upwards [hJump] with omega hOmega
        exact hOmega (sigma n omega))
    rw [condExp_const (IsStoppingTime.predictableGraphMeasurableSpace_le hStop) c] at h
    filter_upwards [h] with omega hOmega
    exact hOmega
  filter_upwards [ae_all_iff.2 hBound] with omega hOmega
  intro t ht
  by_cases hj : processLeftJump H.finiteVariationPart t omega = 0
  · simpa only [hj, abs_zero] using hc
  · obtain ⟨n, hn⟩ :=
      CumulativeVariationJumpEnumeration.coversLeftJumpsUpTo_jumpCrossingTime
        H H.finiteVariationPart_isRightContinuous T omega t ht hj
    simpa only [sigma, hn] using hOmega n

end FTAPTheorem42
