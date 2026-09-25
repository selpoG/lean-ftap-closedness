/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Local.Construction.IntegralGraphAlgebra
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessAlgebra

/-! # Integral graphs defined by bounded coefficient truncations

Only the bounded approximating integrals carry special certificates. The
limiting gain carries a regular zero-initial representative and elementary
Emery convergence, but no special decomposition. Identifying this graph with
the full stochastic-integral domain, constructing its bounded certificates,
and transporting those certificates remain separate proof boundaries.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Truncate by the magnitude of the coefficient, not by a stopping time. -/
noncomputable def integralCoefficientTruncation (H : Process Ω) (n : Nat) : Process Ω :=
  fun t w => if |H t w| ≤ (n : Real) + 1 then H t w else 0

omit [MeasurableSpace Ω] in
theorem integralCoefficientTruncation_abs_le (H : Process Ω) (n : Nat) (t : NNReal) (w : Ω) :
    |integralCoefficientTruncation H n t w| ≤ (n : Real) + 1 := by
  unfold integralCoefficientTruncation
  split_ifs with h
  · exact h
  · simp only [abs_zero]
    positivity

namespace LocalCompletedM2A

variable {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {D : SpecialSemimartingaleDecomposition S F μ}

/-- A fixed-source bounded-truncation certificate. Raw gains may differ from
the regular representative on a single null set. The limit is not required
to have a predictable-FV decomposition. -/
structure TruncatedIntegralGraphWitness (G : LocallySIntegrableStrategy D)
    (integrand gain : Process Ω) where
  integrand_predictable : IsStronglyPredictable F integrand
  approximant : Nat → ActualLocallySIntegrableStrategy (realizationModel G)
  approximant_integrand : ∀ n,
    (approximant n).val.integrand = integralCoefficientTruncation integrand n
  regularGain : Process Ω
  regularGain_adapted : StronglyAdapted F regularGain
  regularGain_right : ∀ w t, ContinuousWithinAt (regularGain · w) (Ici t) t
  regularGain_left : ProcessHasLeftLimits regularGain
  regularGain_zero : regularGain 0 =ᵐ[μ] 0
  gain_indistinguishable : ProcessIndistinguishable μ regularGain gain
  convergence : ElementaryEmeryConverges μ F
    (fun n => (approximant n).val.stochasticIntegral) regularGain

def IsTruncatedIntegralGraph (G : LocallySIntegrableStrategy D)
    (integrand gain : Process Ω) : Prop :=
  Nonempty (TruncatedIntegralGraphWitness G integrand gain)

/-- Only bounded coefficient certificates are transferred as special graphs.
The limiting gain is transported using process convergence; no specialness
of that gain under the target measure is assumed or concluded. -/
theorem IsTruncatedIntegralGraph.of_boundedGraphTransfer
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Dν : SpecialSemimartingaleDecomposition S F ν}
    {G : LocallySIntegrableStrategy D} {Gν : LocallySIntegrableStrategy Dν}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ)
    (hBounded : ∀ (b : Real) {H X : Process Ω}, (∀ t w, |H t w| ≤ b) →
      IsIntegralGraph G H X → IsIntegralGraph Gν H X)
    {integrand gain : Process Ω} (h : IsTruncatedIntegralGraph G integrand gain) :
    IsTruncatedIntegralGraph Gν integrand gain := by
  classical
  obtain ⟨A⟩ := h
  have hRows n : IsIntegralGraph Gν (integralCoefficientTruncation integrand n)
      (A.approximant n).val.stochasticIntegral :=
    hBounded ((n : Real) + 1) (integralCoefficientTruncation_abs_le integrand n)
      ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩
  have hConv : ElementaryEmeryConverges ν F
      (fun n => (A.approximant n).val.stochasticIntegral) A.regularGain :=
    A.convergence.of_equivalentMeasure
      (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
        (A.approximant n).val.stochasticIntegral_isStronglyAdapted
        (A.approximant n).val.stochasticIntegral_isRightContinuous)
      (StronglyAdapted.isStronglyProgressive_of_rightContinuous
        A.regularGain_adapted A.regularGain_right) hμν hνμ
  exact ⟨{
    integrand_predictable := A.integrand_predictable
    approximant := fun n => (hRows n).representative
    approximant_integrand := fun n => (hRows n).representative_integrand
    regularGain := A.regularGain
    regularGain_adapted := A.regularGain_adapted
    regularGain_right := A.regularGain_right
    regularGain_left := A.regularGain_left
    regularGain_zero := hνμ.ae_le A.regularGain_zero
    gain_indistinguishable := hνμ.ae_le A.gain_indistinguishable
    convergence := hConv.congr_sequence (fun n => (hRows n).representative_gain.symm) }⟩

end LocalCompletedM2A

end FTAPTheorem42

namespace FTAPTheorem42.LocalCompletedM2A

/-! ## Addition of integral graphs with disjoint coefficients

Magnitude cuts commute with addition when the two coefficients never have
simultaneously nonzero values. This is the addition law needed for pasting
successive stopping intervals.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}
  {G : LocallySIntegrableStrategy D}

omit [SigmaFiniteFiltration μ F] in
/-- Disjoint coefficient addition uses actual row addition and convergence
of the sum, preserving both stored gains. -/
theorem IsTruncatedIntegralGraph.add_of_disjoint
    {H K X Y : Process Ω}
    (hH : IsTruncatedIntegralGraph G H X) (hK : IsTruncatedIntegralGraph G K Y)
    (hDisjoint : ∀ t ω, H t ω = 0 ∨ K t ω = 0) :
    IsTruncatedIntegralGraph G (H + K) (X + Y) := by
  obtain ⟨A⟩ := hH
  obtain ⟨B⟩ := hK
  have hCut n : integralCoefficientTruncation (H + K) n =
      integralCoefficientTruncation H n + integralCoefficientTruncation K n := by
    funext t ω
    rcases hDisjoint t ω with h | h
    · simp only [integralCoefficientTruncation, Pi.add_apply, h, zero_add, ite_self]
    · simp only [integralCoefficientTruncation, Pi.add_apply, h, add_zero, ite_self]
  have hRows n : IsIntegralGraph G (integralCoefficientTruncation (H + K) n)
      ((A.approximant n).val.stochasticIntegral + (B.approximant n).val.stochasticIntegral) := by
    rw [hCut n]
    exact IsIntegralGraph.add
      ⟨⟨A.approximant n, A.approximant_integrand n, .refl μ _⟩⟩
      ⟨⟨B.approximant n, B.approximant_integrand n, .refl μ _⟩⟩
  have hConv := A.convergence.add
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (A.approximant n).val.stochasticIntegral_isStronglyAdapted
      (A.approximant n).val.stochasticIntegral_isRightContinuous)
    (fun n => StronglyAdapted.isStronglyProgressive_of_rightContinuous
      (B.approximant n).val.stochasticIntegral_isStronglyAdapted
      (B.approximant n).val.stochasticIntegral_isRightContinuous)
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      A.regularGain_adapted A.regularGain_right)
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      B.regularGain_adapted B.regularGain_right) B.convergence
  refine ⟨{
    integrand_predictable := A.integrand_predictable.add B.integrand_predictable
    approximant := fun n => (hRows n).representative
    approximant_integrand := fun n => (hRows n).representative_integrand
    regularGain := A.regularGain + B.regularGain
    regularGain_adapted := A.regularGain_adapted.add B.regularGain_adapted
    regularGain_right := fun ω t => (A.regularGain_right ω t).add (B.regularGain_right ω t)
    regularGain_left := A.regularGain_left.add B.regularGain_left
    regularGain_zero := ?_
    gain_indistinguishable := A.gain_indistinguishable.add B.gain_indistinguishable
    convergence := hConv.congr_sequence (fun n => (hRows n).representative_gain.symm) }⟩
  filter_upwards [A.regularGain_zero, B.regularGain_zero] with ω hA hB
  change A.regularGain 0 ω + B.regularGain 0 ω = 0
  rw [hA, hB]
  exact zero_add (0 : Real)

end FTAPTheorem42.LocalCompletedM2A

namespace FTAPTheorem42.LocalCompletedM2A

/-! ## Terminal claims of the general predictable integral graph

A terminal claim includes its own almost-sure continuous-time limit witness.
Neither a finite-horizon limit nor a special decomposition is required of
the general gain.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {D : SpecialSemimartingaleDecomposition S F μ}

/-- Terminal gains of general predictable integrals at one admissibility
level, retaining the actual limiting claim. -/
def truncatedTerminalClaimsBy (G : LocallySIntegrableStrategy D) (a : Real) : Set (Ω → Real) :=
  {f | 0 < a ∧ ∃ H X : Process Ω, IsTruncatedIntegralGraph G H X ∧
    (∀ t, AELowerBoundedBy μ (-a) (X t)) ∧
    ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal => X t ω) atTop (𝓝 (f ω))}

/-- The general admissible terminal cone for the original source. -/
def truncatedTerminalClaims (G : LocallySIntegrableStrategy D) : Set (Ω → Real) :=
  {f | ∃ a : Real, f ∈ truncatedTerminalClaimsBy G a}

end FTAPTheorem42.LocalCompletedM2A
