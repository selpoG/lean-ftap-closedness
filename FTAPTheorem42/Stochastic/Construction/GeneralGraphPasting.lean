/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.GeneralGraphStopping
import FTAPTheorem42.Stochastic.Construction.IntegralGraphMeasureUniqueness
import FTAPTheorem42.Stochastic.Predictable.StoppingIntervalPasting
import FTAPTheorem42.Stochastic.Stopping.FiniteLocalizerRegularization

/-! # Removing localization from a fixed coefficient's integral graph

The original source constructs one bounded integral for each magnitude cut.
Stopped graph uniqueness identifies these rows with the local certificates;
uniform elementary-test localization then supplies the global graph.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Compatible stopped graphs of a fixed coefficient determine a whole-time
graph. Bounded approximants are supplied by the original source. -/
theorem truncated_integralGraph_of_stopped
    (source : BoundedSemimartingaleSource S F μ)
    {H X : Process Ω} (hH : IsStronglyPredictable F H)
    (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hX0 : X 0 =ᵐ[μ] 0)
    (τ : Nat → Ω → NNReal)
    (hτ : IsLocalizingSequence F (fun k ω => (τ k ω : WithTop NNReal)) μ)
    (hGraph : ∀ k, IsTruncatedIntegralGraph (unitSource source)
      (PredictableProcess.restrict
        (stochasticIntervalIocZeroTop (fun ω => (τ k ω : WithTop NNReal))) H)
      (stoppedProcess X (fun ω => (τ k ω : WithTop NNReal)))) :
    IsTruncatedIntegralGraph (unitSource source) H X := by
  classical
  have hBounded n := bounded_predictable_exists_integralGraph source
    (integralCoefficientTruncation H n)
    (PredictableProcess.isStronglyPredictable_restrict
      (hH.norm.measurableSet_le stronglyMeasurable_const) hH)
    ((n : Real) + 1) (integralCoefficientTruncation_abs_le H n)
  choose Y hY _hYT using hBounded
  let R n := (hY n).representative
  have hR n : (R n).val.integrand = integralCoefficientTruncation H n :=
    (hY n).representative_integrand
  have hProg n := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (R n).val.stochasticIntegral_isStronglyAdapted (R n).val.stochasticIntegral_isRightContinuous
  have hX := StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR
  refine ⟨{
    integrand_predictable := hH
    approximant := R
    approximant_integrand := hR
    regularGain := X
    regularGain_adapted := hXA
    regularGain_right := hXR
    regularGain_left := hXL
    regularGain_zero := hX0
    gain_indistinguishable := .refl μ _
    convergence := ?_ }⟩
  apply ElementaryEmeryConverges.of_localizingSequence hProg hX hτ.toIsPreLocalizingSequence
  intro k
  obtain ⟨A⟩ := hGraph k
  have hRows n : IsIntegralGraph (unitSource source)
      (integralCoefficientTruncation
        (PredictableProcess.restrict
          (stochasticIntervalIocZeroTop (fun ω => (τ k ω : WithTop NNReal))) H) n)
      (stoppedProcess (R n).val.stochasticIntegral
        (fun ω => (τ k ω : WithTop NNReal))) := by
    rw [integralCoefficientTruncation_restrict]
    exact bounded_integralGraph_stopped source ⟨⟨R n, hR n, .refl μ _⟩⟩
      ((n : Real) + 1) (integralCoefficientTruncation_abs_le H n)
      (fun ω => (τ k ω : WithTop NNReal)) (hτ.isStoppingTime k)
  have hEq n := IsIntegralGraph.gain_indistinguishable
    (show IsIntegralGraph (unitSource source) _ (A.approximant n).val.stochasticIntegral from
      ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩) (hRows n)
  exact (A.convergence.congr_sequence hEq).congr_limit A.gain_indistinguishable

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Transporting the general integral graph to the original probability

Bounded coefficients are constructed afresh in the target probability and
identified by common elementary approximations. General gains are transferred
through their bounded cuts and measure-invariant elementary-test convergence.
No special decomposition of an unbounded gain is transported.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration ν F]

/-- Bounded predictable integral certificates can be transferred: existence
is constructed in the target probability and the stored gain is identified
using a common elementary sequence. -/
theorem bounded_integralGraph_of_equivalentMeasure
    (source : BoundedSemimartingaleSource S F μ)
    (source' : BoundedSemimartingaleSource S F ν)
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {H X : Process Ω} (h : IsIntegralGraph (unitSource source) H X)
    (b : Real) (hBound : ∀ t ω, |H t ω| ≤ b) :
    IsIntegralGraph (unitSource source') H X := by
  have hH : IsStronglyPredictable F H :=
    h.representative_integrand ▸ h.representative.val.integrand_isPredictable
  obtain ⟨Y, hY, _hYTruncated⟩ := bounded_predictable_exists_integralGraph source' H hH b hBound
  have hCoeff : h.representative.val.integrand = hY.representative.val.integrand := by
    rw [h.representative_integrand, hY.representative_integrand]
  have hBoundR : ∀ t ω, |h.representative.val.integrand t ω| ≤ b := by
    simpa only [h.representative_integrand] using hBound
  have hGain := actualLocal_gain_indistinguishable_of_equivalentMeasure source source' hμν hνμ
    h.representative hY.representative hCoeff b hBoundR
  exact ⟨⟨hY.representative, hY.representative_integrand,
    hνμ.ae_le (hGain.symm.trans h.representative_gain)⟩⟩

/-- The general truncation graph is invariant under equivalent probabilities
for the same original bounded price. Its limiting gain need not be special
under the target probability. -/
theorem truncated_integralGraph_of_equivalentMeasure
    (source : BoundedSemimartingaleSource S F μ)
    (source' : BoundedSemimartingaleSource S F ν)
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    {H X : Process Ω} (h : IsTruncatedIntegralGraph (unitSource source) H X) :
    IsTruncatedIntegralGraph (unitSource source') H X :=
  h.of_boundedGraphTransfer hμν hνμ
    (fun b _hH _hX hBound hGraph =>
      bounded_integralGraph_of_equivalentMeasure source source' hμν hνμ hGraph b hBound)

/-- Stopped Mémín realizations return to the original probability and the
original price's general integral graph. No measure-transfer capability is
an input to this construction. -/
theorem exists_stopped_truncatedRealization_originalMeasure
    (source : BoundedSemimartingaleSource S F μ)
    (H : RealizedStrategy (ℱ := F) μ S) :
    ∃ (τ : Nat → Ω → NNReal) (K : Nat → Process Ω),
      IsLocalizingSequence F (fun r ω => (τ r ω : WithTop NNReal)) μ ∧
      (∀ r ω, τ r ω ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, IsTruncatedIntegralGraph (unitSource source) (K r)
        (stoppedProcess H.gain (fun ω => (τ r ω : WithTop NNReal))) := by
  obtain ⟨Q, hQ, sourceQ, τ, K, hQμ, hμQ, hLoc, hτT, hGraph⟩ :=
    exists_stopped_truncatedRealization source H
  let : IsProbabilityMeasure Q := hQ
  refine ⟨τ, K, ?_, hτT, ?_⟩
  · exact {
      isStoppingTime := hLoc.isStoppingTime
      tendsto_top := hμQ.ae_le hLoc.tendsto_top
      mono := hμQ.ae_le hLoc.mono }
  · intro r
    exact truncated_integralGraph_of_equivalentMeasure sourceQ source hQμ hμQ (hGraph r)

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Pasting the stopped realizations of the original bounded price

Successive intervals supply a single predictable coefficient. Its integral
has the original selected gain on every localizer and hence at all times.
No agreement of the coefficient values on overlapping coordinates is assumed.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open LocalCompletedM2A StoppingIntervalPasting

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

private theorem truncatedGraph_congr_gain {source : BoundedSemimartingaleSource S F μ}
    {H X Y : Process Ω} (h : IsTruncatedIntegralGraph (unitSource source) H X)
    (hXY : ProcessIndistinguishable μ X Y) :
    IsTruncatedIntegralGraph (unitSource source) H Y := by
  obtain ⟨A⟩ := h
  exact ⟨{ A with gain_indistinguishable := A.gain_indistinguishable.trans hXY }⟩

/-- Increasing finite stopping intervals paste the existing graphs even
when their coefficients disagree on overlaps. -/
theorem exists_truncatedGraph_of_stoppedRealizations
    (source : BoundedSemimartingaleSource S F μ)
    (X : Process Ω) (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXL : ProcessHasLeftLimits X)
    (τ : Nat → Ω → NNReal)
    (hτ : IsLocalizingSequence F (fun n ω => (τ n ω : WithTop NNReal)) μ)
    (K : Nat → Process Ω)
    (hGraph : ∀ n, IsTruncatedIntegralGraph (unitSource source) (K n)
      (stoppedProcess X (fun ω => (τ n ω : WithTop NNReal)))) :
    ∃ H : Process Ω, IsTruncatedIntegralGraph (unitSource source) H X := by
  obtain ⟨υ, hυstop, hυmono, hυtop, hυτ⟩ :=
    exists_everywhere_finiteLocalizer source.usualConditions τ hτ
  let υTop := fun n ω => (υ n ω : WithTop NNReal)
  have hυ : IsLocalizingSequence F υTop μ := {
    isStoppingTime := hυstop
    tendsto_top := Eventually.of_forall hυtop
    mono := Eventually.of_forall fun ω n m hnm => WithTop.coe_le_coe.mpr (hυmono ω hnm) }
  have hG n : IsTruncatedIntegralGraph (unitSource source) (K n) (stoppedProcess X (υTop n)) := by
    apply truncatedGraph_congr_gain (hGraph n)
    filter_upwards [hυτ] with ω hω
    intro t
    change X (min t (τ n ω)) ω = X (min t (υ n ω)) ω
    rw [hω n]
  have hK n : IsStronglyPredictable F (K n) := by
    obtain ⟨A⟩ := hG n
    exact A.integrand_predictable
  have hPrefix n : IsTruncatedIntegralGraph (unitSource source) (finitePrefix υ K n)
      (stoppedProcess X (υTop n)) := by
    induction n with
    | zero =>
      have h := truncated_integralGraph_finiteStopped source (hG 0) (υ 0) (hυstop 0)
      change IsTruncatedIntegralGraph (unitSource source) (finitePrefix υ K 0)
        (stoppedProcess (stoppedProcess X (υTop 0)) (υTop 0)) at h
      simpa only [stoppedProcess_stoppedProcess', min_self] using h
    | succ n ih =>
      have hInt := truncated_integralGraph_finiteInterval source (hG (n + 1))
        (υ n) (υ (n + 1)) (hυstop n) (hυstop (n + 1)) (fun ω => hυmono ω (Nat.le_succ n))
      have hMin : ∀ ω, υTop n ω ≤ υTop (n + 1) ω :=
        fun ω => WithTop.coe_le_coe.mpr (hυmono ω (Nat.le_succ n))
      have hInterval : IsTruncatedIntegralGraph (unitSource source)
          (PredictableProcess.restrict (interval υ (n + 1) \ interval υ n) (K (n + 1)))
          (stoppedProcess X (υTop (n + 1)) - stoppedProcess X (υTop n)) := by
        change IsTruncatedIntegralGraph (unitSource source)
          (PredictableProcess.restrict (interval υ (n + 1) \ interval υ n) (K (n + 1)))
          (stoppedProcess (stoppedProcess X (υTop (n + 1))) (υTop (n + 1)) -
            stoppedProcess (stoppedProcess X (υTop (n + 1))) (υTop n)) at hInt
        rw [stoppedProcess_stoppedProcess_of_le_right hMin,
          stoppedProcess_stoppedProcess'] at hInt
        simp only [min_self] at hInt
        exact hInt
      have h := ih.add_of_disjoint hInterval (prefix_disjoint_next hυmono K n)
      change IsTruncatedIntegralGraph (unitSource source) (finitePrefix υ K (n + 1)) _ at h
      apply truncatedGraph_congr_gain h
      exact Eventually.of_forall fun ω t => by
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
  have hX0 : X 0 =ᵐ[μ] 0 := by
    obtain ⟨A⟩ := hG 0
    have hz := (A.gain_indistinguishable.eventuallyEq_at 0).symm.trans A.regularGain_zero
    filter_upwards [hz] with ω hω
    change X (min 0 (υ 0 ω)) ω = 0 at hω
    have h0 : (0 : NNReal) ≤ υ 0 ω := zero_le
    rwa [min_eq_left h0] at hω
  refine ⟨paste υ K, truncated_integralGraph_of_stopped source
    (paste_predictable hυstop hK) hXA hXR hXL hX0 υ hυ ?_⟩
  intro n
  change IsTruncatedIntegralGraph (unitSource source)
    (PredictableProcess.restrict (interval υ n) (paste υ K)) (stoppedProcess X (υTop n))
  rw [paste_restrict hυmono K n]
  exact hPrefix n

/-- Every selected elementary-test realization has a general predictable
integral coefficient for the same original bounded price and probability. -/
theorem exists_realized_truncatedGraph
    (source : BoundedSemimartingaleSource S F μ)
    (H : PredictableElementaryEmery.RealizedStrategy (ℱ := F) μ S) :
    ∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K H.gain := by
  obtain ⟨τ, K, hτ, _hBound, hGraph⟩ := exists_stopped_truncatedRealization_originalMeasure source H
  exact exists_truncatedGraph_of_stoppedRealizations source H.gain H.gain_stronglyAdapted
    H.gain_rightContinuous H.gain_hasLeftLimits τ hτ K hGraph

end FTAPTheorem42.BoundedSourceIntegralMarket
