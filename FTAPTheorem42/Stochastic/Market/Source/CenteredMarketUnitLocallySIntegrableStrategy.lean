/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization

/-!
# The centered unit-integrand market source

Stochastic integrals start at zero.  Thus the raw graph of the unit
predictable integrand against a market process `S` has gain `S - S 0`, not
the uncentered process `S`.  This module centers all three components of the
supplied special-semimartingale decomposition and packages that graph as a
`LocallySIntegrableStrategy`.

The construction does not assume that the chosen martingale representative
starts at zero.  The local-martingale centering proof uses the same localizing
sequence: on each localization event, the localized initial value is
integrable and adapted, hence its time-constant process is a true martingale.

As with the uncentered raw market graph, this is a data-level construction.
It does not assert membership in a stochastic-integral realization carrier.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped NNReal Topology

variable {Omega : Type*} [MeasurableSpace Omega]
  {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega}

namespace LocalMartingale

/-- A local martingale centered by its own time-zero value remains a local
martingale.  No global integrability assumption on the time-zero value is
needed. -/
theorem centered [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : LocalMartingale M F mu) :
    LocalMartingale (fun t omega => M t omega - M 0 omega) F mu := by
  unfold FTAPTheorem42.LocalMartingale at hM ⊢
  let tau : Nat -> Omega -> WithTop NNReal := hM.localSeq
  refine ⟨tau, hM.isLocalizingSequence_localSeq, ?_⟩
  intro n
  let B : Set Omega := {omega | (⊥ : WithTop NNReal) < tau n omega}
  let Z : Process Omega :=
    MeasureTheory.stoppedProcess (fun t => B.indicator (M t)) (tau n)
  have hZ : Martingale Z F mu := by
    simpa only [tau, B, Z] using hM.stoppedProcess_localSeq n
  have hZ0 : Martingale (fun _ => Z 0) F mu :=
    martingale_const_fun F mu (hZ.stronglyAdapted 0) (hZ.integrable 0)
  have hDiff : Martingale (Z - fun _ => Z 0) F mu := hZ.sub hZ0
  convert hDiff using 1
  funext t omega
  simp only [Pi.sub_apply, Z, B, MeasureTheory.stoppedProcess]
  by_cases homega : omega ∈ {omega | (⊥ : WithTop NNReal) < tau n omega}
  · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
      Set.indicator_of_mem homega]
    change ((0 : NNReal) : WithTop NNReal) < tau n omega at homega
    rw [min_eq_left homega.le]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega,
      Set.indicator_of_notMem homega]
    simp

end LocalMartingale

omit [MeasurableSpace Omega] in
/-- A process constant in time has left limits, without any measurability
assumption on its sample-dependent value. -/
theorem ProcessHasLeftLimits.timeConstant (c : Omega -> Real) :
    ProcessHasLeftLimits (fun _ omega => c omega) := by
  intro omega t
  apply tendsto_leftLim_of_tendsto
  exact ⟨c omega, tendsto_const_nhds⟩

namespace IsStronglyPredictable

/-- Repeating the time-zero value of a predictable process at every time
again gives a predictable process. -/
theorem timeConstant_initial {A : Process Omega}
    (hA : IsStronglyPredictable F A) :
    IsStronglyPredictable F (fun _ omega => A 0 omega) := by
  have hSnd : @Measurable (NNReal × Omega) Omega F.predictable (F 0)
      Prod.snd := by
    intro s hs
    rw [show Prod.snd ⁻¹' s = Set.univ ×ˢ s by
      ext p
      simp]
    exact ProcessNullSetRegularization.measurableSet_predictable_univ_prod hs
  exact (hA.stronglyAdapted 0).comp_measurable hSnd

end IsStronglyPredictable

namespace SpecialSemimartingaleDecomposition

/-- Subtracting the initial value does not change path variation. -/
theorem locallyBoundedVariationOn_sub_initial
    {A : NNReal -> Real} (hA : LocallyBoundedVariationOn A Set.univ) :
    LocallyBoundedVariationOn (fun t => A t - A 0) Set.univ := by
  intro a b ha hb
  unfold BoundedVariationOn at ⊢
  rw [show eVariationOn (fun t => A t - A 0) (Set.univ ∩ Set.Icc a b) =
      eVariationOn A (Set.univ ∩ Set.Icc a b) by
    unfold eVariationOn
    congr 1 with p
    apply Finset.sum_congr rfl
    intro i hi
    rw [edist_sub_right]]
  exact hA a b ha hb

/-- The centered raw graph of the unit predictable integrand against the
supplied market decomposition.

The gain is `S - S 0`; its martingale and finite-variation components are
centered separately.  The source decomposition only holds up to
indistinguishability, so the centered integral decomposition uses the same
common full-measure set at times `t` and `0`. -/
noncomputable def centeredUnitLocallySIntegrableStrategy
    [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : forall omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t)
    (hMAdapted : StronglyAdapted F D.martingalePart)
    (hMRight : forall omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t)
    (hARight : forall omega t,
      ContinuousWithinAt (D.finiteVariationPart · omega) (Set.Ici t) t) :
    LocallySIntegrableStrategy D where
  integrand := PredictableProcess.unit
  stochasticIntegral := fun t omega => S t omega - S 0 omega
  martingalePart := fun t omega =>
    D.martingalePart t omega - D.martingalePart 0 omega
  finiteVariationPart := fun t omega =>
    D.finiteVariationPart t omega - D.finiteVariationPart 0 omega
  integrand_isPredictable := PredictableProcess.isStronglyPredictable_unit
  stochasticIntegral_isStronglyAdapted :=
    hSAdapted.sub (fun t => (hSAdapted 0).mono (F.mono bot_le))
  stochasticIntegral_isRightContinuous := fun omega t =>
    (hSRight omega t).sub continuousWithinAt_const
  martingalePart_isLocalMartingale :=
    D.martingalePart_isLocalMartingale.centered
  martingalePart_isStronglyAdapted :=
    hMAdapted.sub (fun t => (hMAdapted 0).mono (F.mono bot_le))
  martingalePart_isRightContinuous := fun omega t =>
    (hMRight omega t).sub continuousWithinAt_const
  finiteVariationPart_isPredictable :=
    D.finiteVariationPart_isPredictable.sub
      (IsStronglyPredictable.timeConstant_initial
        D.finiteVariationPart_isPredictable)
  finiteVariationPart_isRightContinuous := fun omega t =>
    (hARight omega t).sub continuousWithinAt_const
  finiteVariationPart_isLocallyBoundedVariation := fun omega =>
    locallyBoundedVariationOn_sub_initial
      (D.finiteVariationPart_isLocallyBoundedVariation omega)
  integral_decomposition := by
    filter_upwards [D.decomposition] with omega homega
    intro t
    rw [homega t, homega 0]
    ring
  source_decomposition := D.decomposition

@[simp]
theorem centeredUnitLocallySIntegrableStrategy_integrand
    [SigmaFiniteFiltration mu F]
    (D : SpecialSemimartingaleDecomposition S F mu)
    (hSAdapted : StronglyAdapted F S)
    (hSRight : forall omega t,
      ContinuousWithinAt (S · omega) (Set.Ici t) t)
    (hMAdapted : StronglyAdapted F D.martingalePart)
    (hMRight : forall omega t,
      ContinuousWithinAt (D.martingalePart · omega) (Set.Ici t) t)
    (hARight : forall omega t,
      ContinuousWithinAt (D.finiteVariationPart · omega) (Set.Ici t) t) :
    (D.centeredUnitLocallySIntegrableStrategy hSAdapted hSRight hMAdapted
      hMRight hARight).integrand = PredictableProcess.unit :=
  rfl

end SpecialSemimartingaleDecomposition

end FTAPTheorem42

namespace FTAPTheorem42.SpecialSemimartingaleDecomposition

/-! ## A centered component source with an exact zero-initial gain

The zero initial value is required only almost surely. Component centering
then keeps the exact stored gain, rather than changing its representative.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {X : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ F]

/-- Center the two components while retaining the supplied gain exactly. -/
noncomputable def zeroInitialUnitSource
    (D : SpecialSemimartingaleDecomposition X F μ)
    (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hX0 : X 0 =ᵐ[μ] 0)
    (hMA : StronglyAdapted F D.martingalePart)
    (hMR : ∀ ω t, ContinuousWithinAt (D.martingalePart · ω) (Ici t) t)
    (hAR : ∀ ω t, ContinuousWithinAt (D.finiteVariationPart · ω) (Ici t) t) :
    LocallySIntegrableStrategy D :=
  { D.centeredUnitLocallySIntegrableStrategy hXA hXR hMA hMR hAR with
    stochasticIntegral := X
    stochasticIntegral_isStronglyAdapted := hXA
    stochasticIntegral_isRightContinuous := hXR
    integral_decomposition := by
      filter_upwards [D.decomposition, hX0] with ω hω h0
      intro t
      change X t ω = (D.martingalePart t ω - D.martingalePart 0 ω) +
        (D.finiteVariationPart t ω - D.finiteVariationPart 0 ω)
      have hInitial := hω 0
      rw [h0] at hInitial
      simp only [Pi.zero_apply] at hInitial
      linarith only [hInitial, hω t] }

end FTAPTheorem42.SpecialSemimartingaleDecomposition
