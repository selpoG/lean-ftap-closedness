/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSquareIntegrableSpecialDecomposition
import FTAPTheorem42.Stochastic.Topology.Prelocal.Consumer

/-!
# Representation of a global special decomposition in the prelocal `H¹` carrier

The running-supremum prelocal carrier uses pointwise agreement on the strict
stochastic prefix, whereas a special-semimartingale decomposition is recorded
up to process indistinguishability.  This module keeps these two notions
separate.  It constructs a witness for an exact representative when only the
usual indistinguishable decomposition is available, and exposes a direct
pointwise variant when that stronger representative is supplied.

The analytic finiteness assumptions are explicit.  In particular, local
finite variation and a local martingale alone are not used to manufacture an
`H¹` witness without a stopping or integrability hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

/-! ## Deterministic stopping of the finite-variation component -/

/-! Stopping the locally finite-variation component at a deterministic horizon
produces the globally bounded-variation path required by the prelocal carrier.
The shared `deterministicallyStoppedProcess` retains it on every strict prefix
whose stopping time is at most that horizon. -/

/-! The measurability argument below is the same countable-grid argument used
by the consumer carrier.  It is kept here as a public bridge helper because
the original consumer intentionally keeps its corresponding implementation
private. -/

theorem measurable_strictPrefixVariation_of_regularProcess
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (A : Process Omega) (rho : Omega → NNReal) (T : NNReal)
    (hA : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hRho : IsStoppingTime F
      (fun omega => (rho omega : WithTop NNReal))) :
    Measurable (fun omega => eVariationOn
      (strictPrefixProcess A rho · omega) (Set.Icc 0 T)) := by
  have hP : StronglyAdapted F (strictPrefixProcess A rho) :=
    strictPrefixProcess_stronglyAdapted A rho hA hARight hALeft hRho
  have hPRight : ∀ omega t,
      ContinuousWithinAt (strictPrefixProcess A rho · omega) (Set.Ici t) t :=
    strictPrefixProcess_rightContinuous A rho hARight
  have hEq : (fun omega => eVariationOn
        (strictPrefixProcess A rho · omega) (Set.Icc 0 T)) =
      (fun omega => ⨆ r, FiniteVariationFactorialApproximation.eGridVariation
        (strictPrefixProcess A rho · omega) T r) := by
    funext omega
    exact FiniteVariationFactorialApproximation.eVariationOn_Icc_eq_iSup_eGridVariation
      (strictPrefixProcess A rho · omega) (hPRight omega) T
  rw [hEq]
  apply Measurable.iSup
  intro r
  unfold FiniteVariationFactorialApproximation.eGridVariation
  apply Finset.measurable_fun_sum
  intro k hk
  apply Measurable.edist
  · exact ((hP
      (FiniteVariationFactorialApproximation.point T r (k + 1))).mono
      (F.le (FiniteVariationFactorialApproximation.point T r (k + 1)))).measurable
  · exact ((hP
      (FiniteVariationFactorialApproximation.point T r k)).mono
      (F.le (FiniteVariationFactorialApproximation.point T r k))).measurable

/-! ## A small representation package -/

/-- A prelocal witness for an exact representative together with its
indistinguishability relation to the original target.  The witness itself
still requires pointwise strict-prefix agreement; no such agreement is
silently extracted from a process-level a.e. identity. -/
structure EmeryPrelocalH1SupExactRepresentation
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (X : Process Omega) (tau : Omega → NNReal) (T : NNReal) where
  exactTarget : Process Omega
  witness : EmeryPrelocalH1SupWitness
    (F := F) (mu := mu) exactTarget tau T
  exactTarget_indistinguishable : ProcessIndistinguishable mu exactTarget X

/-! ## The component constructor -/

/-- Build a running-supremum witness from component data.

The component `N` is kept as a local martingale; the carrier itself stops it
inside its envelope.  Thus this constructor does not assert that stopping an
arbitrary local martingale at a random time is a local martingale without the
corresponding theorem.  The finite-variation cost is the strict-prefix
process supplied by the carrier.
-/
noncomputable def EmeryPrelocalH1SupWitness.ofComponents
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} {X M A : Process Omega}
    {tau : Omega → NNReal} {T : NNReal}
    (hAgreement : ∀ t omega, t < tau omega →
      M t omega + A t omega = X t omega)
    (hMLocal : LocalMartingale M F mu)
    (hMAdapted : StronglyAdapted F M)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : ∀ omega, tau omega ≤ T)
    (hAAdapted : StronglyAdapted F A)
    (hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hALeft : ProcessHasLeftLimits A)
    (hAVar : ∀ omega, BoundedVariationOn (A · omega) Set.univ)
    (hEnvelopeMem : MemLp
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess M
          (fun omega => (tau omega : WithTop NNReal))) T)
      (1 : ENNReal) mu)
    (hVariationMeas : Measurable (fun omega => eVariationOn
      (strictPrefixProcess A tau · omega) (Set.Icc 0 T)))
    (hVariationFinite :
      prelocalH1SupFiniteVariationExpectedVariation
        (mu := mu) A tau T ≠ ∞) :
    EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T := by
  let τ : Omega → WithTop NNReal :=
    fun omega => (tau omega : WithTop NNReal)
  have hStoppedAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess M τ) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hMAdapted hTau hMRight
  have hEnvelopeStrong : StronglyMeasurable
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess M τ) T) := by
    exact (FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      hStoppedAdapted T).mono (F.le T)
  have hStoppedRight : ∀ omega t,
      ContinuousWithinAt
        (MeasureTheory.stoppedProcess M τ · omega) (Set.Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hMRight
  have hStoppedLeft : ProcessHasLeftLimits
      (MeasureTheory.stoppedProcess M τ) := hMLeft.stoppedProcess τ
  have hEnvelopePath : ∀ omega,
      ENNReal.ofReal
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (MeasureTheory.stoppedProcess M τ) T omega) =
        ⨆ t : Set.Iic T, ENNReal.ofReal
          |MeasureTheory.stoppedProcess M τ t.1 omega| := by
    intro omega
    exact FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
      hStoppedRight hStoppedLeft T
  exact {
    N := M
    A := A
    agrees_on_strict_prefix := hAgreement
    martingale_isLocalMartingale := hMLocal
    martingale_isStronglyAdapted := hMAdapted
    martingale_isRightContinuous := hMRight
    martingale_hasLeftLimits := hMLeft
    stoppingTime := hTau
    stoppingTime_le_horizon := hTauT
    finiteVariation_isStronglyAdapted := hAAdapted
    finiteVariation_isRightContinuous := hARight
    finiteVariation_hasLeftLimits := hALeft
    finiteVariation_isBoundedVariation := hAVar
    martingale_envelope_stronglyMeasurable := by
      simpa only [τ] using hEnvelopeStrong
    martingale_envelope_memLp_one := by
      simpa only [τ] using hEnvelopeMem
    martingale_envelope_eq_iSup := by
      simpa only [τ] using hEnvelopePath
    finiteVariation_measurable := hVariationMeas
    finiteVariation_integral_ne_top := hVariationFinite }

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
