/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.BoundedSource
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Foundations.Variation
import FTAPTheorem42.Stochastic.Topology.Emery.TerminalMarket
import FTAPTheorem42.Stochastic.Construction.GeneralGraphApproximation
import FTAPTheorem42.Stochastic.Topology.Emery.ComponentCauchy
import FTAPTheorem42.Foundations.ConvexProcesses

/-! # Identifying the original price's general terminal market

The two gain domains have already been identified at all times. Here each
candidate's own terminal witness and admissible lower bound are preserved,
so the original general integral terminal sets equal the completion's sets.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- General integration against the original price. The internal unit-source
certificate is an implementation detail of this predicate. -/
def GeneralIntegralGraph (source : BoundedSemimartingaleSource S F μ)
    (H X : Process Ω) : Prop :=
  IsTruncatedIntegralGraph (unitSource source) H X

/-- Original-price terminal claims at a fixed admissibility level. -/
def generalAdmissibleClaims (source : BoundedSemimartingaleSource S F μ)
    (a : Real) : Set (Ω → Real) :=
  {f | 0 < a ∧ ∃ H X : Process Ω, GeneralIntegralGraph source H X ∧
    (∀ t, AELowerBoundedBy μ (-a) (X t)) ∧
    ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal => X t ω) atTop (𝓝 (f ω))}

/-- The union of original-price admissible terminal claims. -/
def generalTerminalClaims (source : BoundedSemimartingaleSource S F μ) : Set (Ω → Real) :=
  {f | ∃ a : Real, f ∈ generalAdmissibleClaims source a}

/-- The realized completion is used as a model of the same general
terminal-gain domain; the following equalities provide that identification. -/
noncomputable def generalMarket (source : BoundedSemimartingaleSource S F μ) :
    GainProcessModel Ω NNReal :=
  PredictableElementaryEmery.terminalGainProcessModel S
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous) (μ := μ)

/-- Fixed-level terminal claims preserve both the running lower bound and
the candidate-specific terminal limit under gain indistinguishability. -/
theorem truncatedTerminalClaimsBy_eq_generalMarket
    (source : BoundedSemimartingaleSource S F μ) (a : Real) :
    truncatedTerminalClaimsBy (unitSource source) a =
      (generalMarket source).TerminalGainsOf μ ((generalMarket source).AdmissibleBy μ a) := by
  ext f
  constructor
  · rintro ⟨ha, H, X, hGraph, hLower, hTerminal⟩
    obtain ⟨R, hR⟩ := truncated_integralGraph_exists_realizedStrategy source hGraph
    let V : PredictableElementaryEmery.TerminalStrategy (ℱ := F) μ S := {
      realized := R
      terminalGain := f
      terminalWitness := by
        filter_upwards [hTerminal, hR] with ω hω heq
        exact hω.congr (fun t => (heq t).symm) }
    refine ⟨V, ⟨ha, ?_⟩, rfl⟩
    intro t
    filter_upwards [hLower t, hR.eventuallyEq_at t] with ω hω heq
    change -a ≤ R.gain t ω
    rwa [heq]
  · rintro ⟨V, ⟨ha, hLower⟩, rfl⟩
    obtain ⟨H, hGraph⟩ := exists_realized_truncatedGraph source V.realized
    exact ⟨ha, H, V.realized.gain, hGraph, hLower, V.terminalWitness⟩

/-- The original general integral admissible terminal cone is exactly the
completion market's admissible cone, with the same terminal representatives. -/
theorem truncatedTerminalClaims_eq_generalMarket_K0
    (source : BoundedSemimartingaleSource S F μ) :
    truncatedTerminalClaims (unitSource source) =
      (generalMarket source).K0OfGainProcessModel μ := by
  ext f
  constructor
  · rintro ⟨a, ha⟩
    rw [truncatedTerminalClaimsBy_eq_generalMarket source a] at ha
    obtain ⟨V, hV, hTerminal⟩ := ha
    exact ⟨V, ⟨a, hV⟩, hTerminal⟩
  · rintro ⟨V, ⟨a, hV⟩, hTerminal⟩
    refine ⟨a, ?_⟩
    rw [truncatedTerminalClaimsBy_eq_generalMarket source a]
    exact ⟨V, hV, hTerminal⟩

/-- The unit-admissible domain used by the existing maximality and Fatou
consumers has the original general integral interpretation. -/
theorem truncatedTerminalClaims_one_eq_generalMarket_K1
    (source : BoundedSemimartingaleSource S F μ) :
    truncatedTerminalClaimsBy (unitSource source) 1 =
      (generalMarket source).K1OfGainProcessModel μ :=
  truncatedTerminalClaimsBy_eq_generalMarket source 1

/-! ## Closure of the original general integral gain domain

Elementary density and the completed realization theorem are consumed in
opposite directions. No special certificate is imposed on the limiting gain.
The terminal consumer keeps the independently supplied terminal witness.
-/

/-- A regular zero-initial Emery limit of general integral gains is again
an integral of the same original price. -/
theorem exists_truncatedIntegralGraph_of_emeryConverges
    (source : BoundedSemimartingaleSource S F μ)
    {K Y : Nat → Process Ω} {X : Process Ω}
    (hGraph : ∀ n, GeneralIntegralGraph source (K n) (Y n))
    (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hX0 : X 0 =ᵐ[μ] 0)
    (hConv : ElementaryEmeryConverges μ F Y X) :
    ∃ H, GeneralIntegralGraph source H X := by
  let A n := Classical.choice (hGraph n)
  have hRegConv : ElementaryEmeryConverges μ F (fun n => (A n).regularGain) X :=
    hConv.congr_sequence (fun n => (A n).gain_indistinguishable.symm)
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  have hApprox := ElementaryEmeryApproximable.of_converges hS source.rightContinuous
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (A n).regularGain_adapted (A n).regularGain_right)
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR)
    (fun n => truncatedGraphWitness_elementaryApproximable source (A n)) hRegConv
  obtain ⟨R, hR⟩ := hApprox.exists_realizedStrategy hS source.rightContinuous hXA hXR hXL hX0
  exact (exists_truncatedIntegralGraph_iff_exists_realizedStrategy source X).mpr
    ⟨R, hR ▸ ProcessIndistinguishable.refl μ X⟩

/-! ## Component estimates close a convexified original-price gain sequence

The auxiliary measure is used only for estimates. The same all-time limit and
its own terminal witness are retained under forward convexification; Emery
convergence is then transferred back to the original market measure.
-/

/-- Finite-horizon component probability estimates for an already selected
sequence imply attainment of the original path limit's terminal claim. The
martingale threshold is uniform over all elementary tests. -/
theorem truncatedTerminalClaims_one_of_component_estimates
    (source : BoundedSemimartingaleSource S F μ)
    {Q : Measure Ω} [IsProbabilityMeasure Q] (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    {K Y M A : Nat → Process Ω} {X : Process Ω} {h : Ω → ℝ}
    (hGraph : ∀ n, GeneralIntegralGraph source (K n) (Y n))
    (hYA : ∀ n, StronglyAdapted F (Y n))
    (hYR : ∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t)
    (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hX0 : X 0 =ᵐ[μ] 0)
    (hLower : ∀ t, AELowerBoundedBy μ (-1) (X t))
    (hUniform : ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => Y n t ω) (X · ω) atTop)
    (hTerminal : ∀ᵐ ω ∂μ, Tendsto (X · ω) atTop (𝓝 (h ω)))
    (hDecomp : ∀ n, ProcessIndistinguishable Q (Y n) (M n + A n))
    (hBV : ∀ m n ω, LocallyBoundedVariationOn ((A m - A n) · ω) univ)
    (hAR : ∀ n ω t, ContinuousWithinAt (A n · ω) (Ici t) t)
    (hM : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      ∀ J : BoundedPredictableElementaryMultiplier F,
        Q.real {ω | ε < elementaryEmeryTestError (M m) (M n) J T ω} ≤ ε)
    (hV : ∀ T ε, 0 < ε → ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N,
      Q.real {ω | ε < finiteHorizonPathVariation (A m - A n) (hBV m n) T ω} ≤ ε) :
    h ∈ generalAdmissibleClaims source 1 := by
  have hYProg n := StronglyAdapted.isStronglyProgressive_of_rightContinuous (hYA n) (hYR n)
  have hXProg := StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR
  have hCauchy := elementaryEmeryCauchy_of_local_component_estimates
    hYProg hDecomp hBV hAR hM hV
  have hConvQ := hCauchy.converges_of_ucp hYProg hXProg hYR hXR (by
    open FactorialChronologicalGrid in
    exact cappedFiniteHorizonAbsoluteEnvelope_tendstoInMeasure_zero_of_uniformAE
      hYA hXA (hQμ.ae_le hUniform))
  have hConvμ := hConvQ.of_equivalentMeasure hYProg hXProg hQμ hμQ
  obtain ⟨H, hH⟩ := exists_truncatedIntegralGraph_of_emeryConverges
    source hGraph hXA hXR hXL hX0 hConvμ
  exact ⟨zero_lt_one, H, X, hH, hLower, hTerminal⟩

/-- The public fixed-level market agrees with the gain-process model. -/
theorem generalAdmissibleClaims_eq_generalMarket
    (source : BoundedSemimartingaleSource S F μ) (a : Real) :
    generalAdmissibleClaims source a =
      (generalMarket source).TerminalGainsOf μ ((generalMarket source).AdmissibleBy μ a) :=
  truncatedTerminalClaimsBy_eq_generalMarket source a

/-- The public terminal market agrees with K0 of the gain-process model. -/
theorem generalTerminalClaims_eq_generalMarket_K0
    (source : BoundedSemimartingaleSource S F μ) :
    generalTerminalClaims source = (generalMarket source).K0OfGainProcessModel μ :=
  truncatedTerminalClaims_eq_generalMarket_K0 source

/-- Unit-admissible claims agree with K1 of the gain-process model. -/
theorem generalAdmissibleClaims_one_eq_generalMarket_K1
    (source : BoundedSemimartingaleSource S F μ) :
    generalAdmissibleClaims source 1 = (generalMarket source).K1OfGainProcessModel μ :=
  truncatedTerminalClaims_one_eq_generalMarket_K1 source

end FTAPTheorem42.BoundedSourceIntegralMarket
