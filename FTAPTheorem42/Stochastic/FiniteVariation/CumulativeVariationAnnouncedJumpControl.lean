/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationFiltrationLimit
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.FiniteVariation.CumulativeVariationJumpEnumeration
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.Martingale.Basic.LocalMartingaleAnnouncedJumpControl
import FTAPTheorem42.Stochastic.Predictable.PredictableJumpEnvelope
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetelling
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeCondExpEnvelope

/-!
# Corollary 2.4 from announced cumulative-variation jump graphs

For a countable family of finite stopping times, announcements turn the
local-martingale property into the required conditional mean-zero jump
identities.  Pathwise sorting of finite stopping-time prefixes supplies a
common `L²` envelope without a countable-range restriction.  The older
rational-passage endpoints remain available alongside the predictable
completed jump-crossing times used by Lemma 4.7.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CumulativeVariationJumpEnumeration

variable
  {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- An announced family of finite stopping times supplies a quantitative
`L²` envelope for every finite-variation jump covered by that family.  The
terminal horizon `U` controlling the sampled times may be larger than the
horizon `T` on which jump coverage is required. -/
theorem LocalMartingale.finiteVariationLeftJumpEnvelope_with_norm_of_stoppingTimeAnnouncements
    [ℱ.IsRightContinuous]
    {A X M : Process Ω}
    (hAPredictable : IsStronglyPredictable ℱ (processLeftJump A))
    (hM : LocalMartingale M ℱ μ)
    (J : Ω → ℝ) (T U : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n,
      IsStoppingTime ℱ (fun ω ↦ (τ n ω : WithTop ℝ≥0)))
    (hτU : ∀ n ω, τ n ω ≤ U)
    (hcover : CoversLeftJumpsUpTo A T τ)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (announcement : ∀ n, StoppingTimeAnnouncement ℱ (τ n))
    (hJ : MemLp J (2 : ℝ≥0∞) μ)
    (hdecomp : ∀ n,
      (fun ω ↦ processLeftJump X (τ n ω) ω) =ᵐ[μ]
        fun ω ↦ processLeftJump M (τ n ω) ω +
          processLeftJump A (τ n ω) ω)
    (hXJ : ∀ n,
      (fun ω ↦ |processLeftJump X (τ n ω) ω|) ≤ᵐ[μ] J) :
    (MemLp (countableLeftJumpEnvelope A τ) (2 : ℝ≥0∞) μ ∧
        ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
          |processLeftJump A t ω| ≤ countableLeftJumpEnvelope A τ ω) ∧
      eLpNorm (countableLeftJumpEnvelope A τ) (2 : ℝ≥0∞) μ ≤
        2 * eLpNorm J (2 : ℝ≥0∞) μ := by
  have hsampledMeas : ∀ n, Measurable fun ω ↦
      processLeftJump A (τ n ω) ω := by
    intro n
    exact ((IsStronglyPredictable.stronglyMeasurable_sampledLeftJump
      hAPredictable (τ n)).mono
        (IsStoppingTime.predictableGraphMeasurableSpace_le (hτ n))).measurable
  have hlocal : ∀ n,
      (fun ω ↦ |processLeftJump A (τ n ω) ω|) ≤ᵐ[μ]
        μ[J | predictableGraphMeasurableSpace ℱ (τ n)] := by
    intro n
    have hAmeas :=
      IsStronglyPredictable.stronglyMeasurable_sampledLeftJump
        hAPredictable (τ n)
    exact LocalMartingale.finiteVariationLeftJump_ae_le_condExp_of_announcement
      hM (announcement n) U (hτ n) (hτU n) hMRight hMLeft hAmeas J
      (hJ.integrable (by norm_num)) (hdecomp n) (hXJ n)
  have hcond :=
    StoppingTimeCondExpEnvelope.condExp_graph_sq_le_envelope_ae
      (μ := μ) announcement (J := J)
  have hdom : countableLeftJumpSqEnvelope A τ ≤ᵐ[μ]
      StoppingTimeCondExpEnvelope.condExpSqEnvelope ℱ μ
        (StoppingTimeCondExpEnvelope.announcementTime announcement)
        (StoppingTimeCondExpEnvelope.announcementTime_isStoppingTime
          announcement) J := by
    filter_upwards [ae_all_iff.2 hlocal, ae_all_iff.2 hcond] with ω hlocalω hcondω
    apply iSup_le
    intro n
    have hnonneg : 0 ≤
        μ[J | predictableGraphMeasurableSpace ℱ (τ n)] ω :=
      (abs_nonneg _).trans (hlocalω n)
    have hsquare :
        (processLeftJump A (τ n ω) ω) ^ 2 ≤
          (μ[J | predictableGraphMeasurableSpace ℱ (τ n)] ω) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hnonneg).2 (hlocalω n)
    exact (ENNReal.ofReal_le_ofReal hsquare).trans (hcondω n)
  have hEnvelopeBound :=
    StoppingTimeCondExpEnvelope.lintegral_condExpSqEnvelope_le
      (StoppingTimeCondExpEnvelope.announcementTime_isStoppingTime
        announcement) hJ
  have hSqBound : (∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ :=
    (lintegral_mono_ae hdom).trans hEnvelopeBound
  have hJFinite : (∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ) < ∞ :=
    hJ.integrable_sq.lintegral_lt_top
  have hfinite : (∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ) ≠ ∞ := by
    exact ne_of_lt (hSqBound.trans_lt
      (ENNReal.mul_lt_top (by norm_num) hJFinite))
  have hEnvelope :=
    countableLeftJumpEnvelope_memLp A τ hsampledMeas hfinite
  exact ⟨⟨hEnvelope,
      abs_processLeftJump_le_countableLeftJumpEnvelope_ae
        A T τ hcover hsampledMeas hfinite⟩,
    eLpNorm_countableLeftJumpEnvelope_le_two_mul
      A τ J hEnvelope hJ hSqBound⟩

/-- Announced predictable jump-crossing times provide a quantitative
finite-variation jump envelope.  Dummy values lie at `T + 1`, while the
resulting envelope controls all jumps only up to `T`. -/
theorem LocalMartingale.finiteVariationLeftJumpEnvelope_with_norm_of_jumpCrossingAnnouncements
    [ℱ.IsRightContinuous]
    (H : SIntegrableStrategy D)
    (hRightA : ∀ ω t,
      ContinuousWithinAt (fun u ↦ H.finiteVariationPart u ω) (Set.Ici t) t)
    {X M : Process Ω} (hM : LocalMartingale M ℱ μ)
    (J : Ω → ℝ) (T : ℝ≥0)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (announcement : ∀ n,
      StoppingTimeAnnouncement ℱ (jumpCrossingTime H T n))
    (hJ : MemLp J (2 : ℝ≥0∞) μ)
    (hdecomp : ∀ n,
      (fun ω ↦ processLeftJump X (jumpCrossingTime H T n ω) ω) =ᵐ[μ]
        fun ω ↦ processLeftJump M (jumpCrossingTime H T n ω) ω +
          processLeftJump H.finiteVariationPart
            (jumpCrossingTime H T n ω) ω)
    (hXJ : ∀ n, (fun ω ↦
      |processLeftJump X (jumpCrossingTime H T n ω) ω|) ≤ᵐ[μ] J) :
    (MemLp (countableLeftJumpEnvelope H.finiteVariationPart
          (jumpCrossingTime H T)) (2 : ℝ≥0∞) μ ∧
        ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
          |processLeftJump H.finiteVariationPart t ω| ≤
            countableLeftJumpEnvelope H.finiteVariationPart
              (jumpCrossingTime H T) ω) ∧
      eLpNorm (countableLeftJumpEnvelope H.finiteVariationPart
          (jumpCrossingTime H T)) (2 : ℝ≥0∞) μ ≤
        2 * eLpNorm J (2 : ℝ≥0∞) μ := by
  exact LocalMartingale.finiteVariationLeftJumpEnvelope_with_norm_of_stoppingTimeAnnouncements
    H.processLeftJump_finiteVariationPart_isPredictable hM J T (T + 1)
    (jumpCrossingTime H T) (jumpCrossingTime_isStoppingTime H hRightA T)
    (jumpCrossingTime_le H T)
    (coversLeftJumpsUpTo_jumpCrossingTime H hRightA T)
    hMRight hMLeft announcement hJ hdecomp hXJ

end CumulativeVariationJumpEnumeration

end FTAPTheorem42
