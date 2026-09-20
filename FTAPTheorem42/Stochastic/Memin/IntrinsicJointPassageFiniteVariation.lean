/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.IntrinsicJointPassageIntegralIdentification
import FTAPTheorem42.Stochastic.Memin.RangeVariationL1Control
import FTAPTheorem42.Stochastic.Integral.Localization.AEDominatedFiniteVariationBridge

/-!
# Finite-variation control at the intrinsic Mémín joint passages

The martingale identification selects its integrand from actual forward
convex combinations of the Mémín approximants.  This module connects that
new representative to the finite-variation range control.  Forward convexity
preserves the original pointwise Mémín limit, so the selected integrand is
equal almost everywhere to the full-sequence limit under every deterministic
range-variation control.

We also replace the normalized bridge of the intrinsic joint source prefix by
the range-normalized bridge shared by the whole approximating sequence.  The
joint prefix is a further stop of the deterministic source path, so its path
variation is dominated by the same range normalizer.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge
open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

omit [MeasurableSpace Omega] [SigmaFiniteFiltration mu F]
    [F.IsRightContinuous] in
/-- Isolate the proof-irrelevant path congruence needed when the stopping
calculus chooses a different representative of the same finite-variation
path. -/
private theorem variationDirection_eq_of_path_eq
    {A B : NNReal -> Real} (hA : BoundedVariationOn A Set.univ)
    (hB : BoundedVariationOn B Set.univ) (hAB : A = B) :
    FiniteVariationPath.variationDirection hA =
      FiniteVariationPath.variationDirection hB := by
  subst B
  rfl

omit [F.IsRightContinuous] in
/-- The integrand selected from the actual joint-passage convexifications
agrees with the full-sequence Mémín limit under every deterministic range
variation control. -/
theorem intrinsicJointPassageSelectedIntegrand_ae_eq_rangeVariation
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (T : NNReal) (hT : 0 < T) :
    intrinsicJointPassageSelectedIntegrand
      (D := D) (G := G) data w cutoff =ᵐ[
        meminRangeVariationControl G T hT
          (ActualSIntegrableStrategy.rawSequence data.approximant)
            data.variationSummable (data.martingaleEnvelopeSummable T)]
      Function.uncurry (meminLimitIntegrand
        (ActualSIntegrableStrategy.rawSequence data.approximant)) := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let nu := meminRangeVariationControl G T hT
    (ActualSIntegrableStrategy.rawSequence data.approximant)
      data.variationSummable (data.martingaleEnvelopeSummable T)
  let f : Nat -> NNReal × Omega -> Real := fun n =>
    Function.uncurry (data.approximant n).val.integrand
  have hBase : Integrable (f 0) nu := by
    apply memLp_one_iff_integrable.mp
    simpa only [nu, f, hGactual] using
      Cfv.meminBaseIntegrand_memLp_one_rangeVariation
        data.approximant T hT data.variationSummable
          (data.martingaleEnvelopeSummable T)
  have hSteps : (∑' k, ∫⁻ p, edist (f (k + 1) p) (f k p) ∂nu) ≠ ∞ := by
    change (∑' k, ∫⁻ p,
      edist ((data.approximant (k + 1)).val.integrand p.1 p.2)
        ((data.approximant k).val.integrand p.1 p.2) ∂nu) ≠ ∞
    simpa only [nu, hGactual] using
      Cfv.tsum_meminApproximantIntegrand_edist_rangeVariation_ne_top
        data.approximant T hT data.variationSummable
          (data.martingaleEnvelopeSummable T)
  have hLimit := MeminL1.integrable_l1_limit_of_summable_steps f
    (fun n => (data.approximant n).val.integrand_isPredictable
      |>.aestronglyMeasurable) hBase hSteps
  filter_upwards [hLimit.2.1] with p hp
  have hConvex := (TailConvexWeights.toForward w).tendsto_apply_real hp
  have hSubsequence := hConvex.comp hCutoff.tendsto_atTop
  change limUnder atTop (fun n =>
      intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p) = _
  have hSelectedTendsto : Tendsto (fun n =>
      intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p) atTop
      (nhds (limUnder atTop (fun n => f n p))) := by
    apply hSubsequence.congr'
    filter_upwards with n
    symm
    change (SIntegrableStrategy.tailConvexCombination
      (ActualSIntegrableStrategy.rawSequence data.approximant)
        (w (cutoff n))).integrand p.1 p.2 = _
    rw [SIntegrableStrategy.tailConvexCombination_integrand_apply]
    rfl
  change limUnder atTop (fun n =>
      intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff n) p) = limUnder atTop
        (fun n => f n p)
  exact hSelectedTendsto.limUnder_eq

omit [F.IsRightContinuous] in
/-- Consequently, the joint-passage selected integrand belongs to the same
deterministic range `L¹` space as the full-sequence limit. -/
theorem intrinsicJointPassageSelectedIntegrand_memLp_one_rangeVariation
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (T : NNReal) (hT : 0 < T) :
    MemLp (intrinsicJointPassageSelectedIntegrand
      (D := D) (G := G) data w cutoff) 1
      (meminRangeVariationControl G T hT
        (ActualSIntegrableStrategy.rawSequence data.approximant)
          data.variationSummable (data.martingaleEnvelopeSummable T)) := by
  have hFull : MemLp (Function.uncurry (meminLimitIntegrand
      (ActualSIntegrableStrategy.rawSequence data.approximant))) 1
      (meminRangeVariationControl G T hT
        (ActualSIntegrableStrategy.rawSequence data.approximant)
          data.variationSummable (data.martingaleEnvelopeSummable T)) := by
    simpa only [hGactual] using
      Cfv.meminLimitIntegrand_memLp_one_rangeVariation
        data.approximant T hT data.variationSummable
          (data.martingaleEnvelopeSummable T)
  exact (memLp_congr_ae
    (intrinsicJointPassageSelectedIntegrand_ae_eq_rangeVariation
       Gactual hGactual Cfv data w cutoff hCutoff T hT)).mpr hFull

/-- The raw joint source prefix is pathwise the finite stop of the
deterministically stopped raw source finite-variation component. -/
theorem intrinsicJointPassageSourcePrefix_finiteVariationPart_stopAt
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) :
    ProcessIndistinguishable mu
      (intrinsicJointPassageSourcePrefix base data n).finiteVariationPart
      (fun t omega => FiniteVariationStoppedPath.stopAt
        (fun u => (G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)).finiteVariationPart u omega)
        (intrinsicJointPassageFiniteLocalizer base data n omega) t) := by
  filter_upwards [intrinsicJointPassageSourcePrefix_finiteVariationPart
      base data n] with omega hPath
  intro t
  rw [hPath t]
  unfold MeasureTheory.stoppedProcess FiniteVariationStoppedPath.stopAt
  rw [<- coe_intrinsicJointPassageFiniteLocalizer base data n omega]
  rfl

/-- The canonical density of the raw joint prefix agrees with the intrinsic
direction of the literal finite stop of the deterministic source path. -/
theorem intrinsicJointPassageSourcePrefix_jumpDensity_ae_eq_stoppedDirection
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat)
    (E : SIntegrableFiniteVariationBridge
      (intrinsicJointPassageSourcePrefix base data n)) :
    ∀ᵐ omega ∂mu,
      (fun t => jumpCorrectedCanonicalVariationDensity E (t, omega)) =ᵐ[
        (FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            ((G.deterministicallyStopped (cadlagPassageHorizon n)
              (cadlagPassageHorizon_pos n)
              ).finiteVariationPart_isBoundedVariation omega)
            (intrinsicJointPassageFiniteLocalizer base data n omega)
          )).totalVariation]
        FiniteVariationPath.variationDirection
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            ((G.deterministicallyStopped (cadlagPassageHorizon n)
              (cadlagPassageHorizon_pos n)
              ).finiteVariationPart_isBoundedVariation omega)
            (intrinsicJointPassageFiniteLocalizer base data n omega)) := by
  filter_upwards [
      E.jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection,
      intrinsicJointPassageSourcePrefix_finiteVariationPart_stopAt
        base data n] with omega hDensity hPath
  let hPrefix := (intrinsicJointPassageSourcePrefix base data n
    ).finiteVariationPart_isBoundedVariation omega
  let hStopped := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    ((G.deterministicallyStopped (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      ).finiteVariationPart_isBoundedVariation omega)
    (intrinsicJointPassageFiniteLocalizer base data n omega)
  have hPathEq :
      (fun t => (intrinsicJointPassageSourcePrefix base data n
        ).finiteVariationPart t omega) =
        FiniteVariationStoppedPath.stopAt
          (fun u => (G.deterministicallyStopped (cadlagPassageHorizon n)
            (cadlagPassageHorizon_pos n)).finiteVariationPart u omega)
          (intrinsicJointPassageFiniteLocalizer base data n omega) :=
    funext hPath
  have hMeasure := FiniteVariationPath.signedMeasure_eq_of_eq
    hPrefix hStopped hPathEq
  have hDirection := variationDirection_eq_of_path_eq
    hPrefix hStopped hPathEq
  rw [<- hMeasure]
  simpa only [hDirection] using hDensity

/-- The joint prefix's whole-path variation is dominated almost surely by
the zeroth term of the common Mémín range normalizer. -/
theorem intrinsicJointPassageSourcePrefix_totalVariation_ae_le_rangeVariation
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((intrinsicJointPassageSourcePrefix base data n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.real
            Set.univ <=
        meminRangeVariationSequence G (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)
          (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega := by
  filter_upwards [
      intrinsicJointPassageSourcePrefix_finiteVariationPart_stopAt
        base data n] with omega hPath
  let T := cadlagPassageHorizon n
  let sourcePath := fun t =>
    (G.deterministicallyStopped T (cadlagPassageHorizon_pos n)
      ).finiteVariationPart t omega
  let hSource := (G.deterministicallyStopped T
    (cadlagPassageHorizon_pos n)).finiteVariationPart_isBoundedVariation omega
  let tau := intrinsicJointPassageFiniteLocalizer base data n omega
  let hStopped :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt hSource tau
  have hMeasure : FiniteVariationPath.signedMeasure
      ((intrinsicJointPassageSourcePrefix base data n
        ).finiteVariationPart_isBoundedVariation omega) =
      FiniteVariationPath.signedMeasure hStopped := by
    apply FiniteVariationPath.signedMeasure_eq_of_eq
    exact funext hPath
  rw [hMeasure]
  rw [FiniteVariationStoppedPath.totalVariation_stopAt_eq_restrict_Ioc
    sourcePath hSource
      ((G.deterministicallyStopped T
        (cadlagPassageHorizon_pos n)).finiteVariationPart_isRightContinuous
          omega) tau]
  rw [measureReal_restrict_apply_univ]
  calc
    (FiniteVariationPath.signedMeasure hSource).totalVariation.real
        (Set.Ioc 0 tau) <=
      meminStoppedSourceTotalVariation G T
        (cadlagPassageHorizon_pos n) omega := by
      exact measureReal_mono (Set.subset_univ _)
    _ <= meminJointVariationSequence G T (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega :=
      meminStoppedSourceTotalVariation_le_joint G T
        (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) omega
    _ <= meminJointLocalS1Sequence G T (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega :=
      meminJointVariationSequence_le_jointLocalS1 G T
        (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega
    _ <= meminRangeVariationSequence G T (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega :=
      meminJointLocalS1Sequence_le_rangeVariation G T
        (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) 0 omega

/-- Pathwise variation of the joint prefix is dominated by the deterministic
source variation before the joint stop. -/
theorem intrinsicJointPassageSourcePrefix_pathVariation_ae_le
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((intrinsicJointPassageSourcePrefix base data n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        ((G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  filter_upwards [
      intrinsicJointPassageSourcePrefix_finiteVariationPart_stopAt
        base data n] with omega hPath
  let T := cadlagPassageHorizon n
  let sourcePath := fun t =>
    (G.deterministicallyStopped T (cadlagPassageHorizon_pos n)
      ).finiteVariationPart t omega
  let hSource := (G.deterministicallyStopped T
    (cadlagPassageHorizon_pos n)).finiteVariationPart_isBoundedVariation omega
  let tau := intrinsicJointPassageFiniteLocalizer base data n omega
  let hStopped :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt hSource tau
  have hMeasure : FiniteVariationPath.signedMeasure
      ((intrinsicJointPassageSourcePrefix base data n
        ).finiteVariationPart_isBoundedVariation omega) =
      FiniteVariationPath.signedMeasure hStopped := by
    apply FiniteVariationPath.signedMeasure_eq_of_eq
    exact funext hPath
  rw [hMeasure]
  rw [FiniteVariationStoppedPath.totalVariation_stopAt_eq_restrict_Ioc
    sourcePath hSource
      ((G.deterministicallyStopped T
        (cadlagPassageHorizon_pos n)).finiteVariationPart_isRightContinuous
          omega) tau]
  exact Measure.restrict_le_self

/-- The range-normalized bridge on one intrinsic joint source prefix. -/
noncomputable def intrinsicJointPassageRangeVariationBridge
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) : SIntegrableFiniteVariationBridge
      (intrinsicJointPassageSourcePrefix base data n) :=
  ofAEDominatedSummableSequence
    (meminRangeVariationSequence G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_measurable G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_nonnegative G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_summable G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant)
      data.variationSummable
      (data.martingaleEnvelopeSummable (cadlagPassageHorizon n)))
    0 (intrinsicJointPassageSourcePrefix_totalVariation_ae_le_rangeVariation
      base data n)

/-- The exceptional-set repair leaves the common range reference measure
unchanged. -/
theorem intrinsicJointPassageRangeVariationBridge_referenceMeasure_eq
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (n : Nat) :
    (intrinsicJointPassageRangeVariationBridge base data n
      ).referenceMeasure =
      meminRangeVariationReferenceMeasure G (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant) := by
  exact ofAEDominatedSummableSequence_referenceMeasure_eq
    (meminRangeVariationSequence G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_measurable G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_nonnegative G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant))
    (meminRangeVariationSequence_summable G (cadlagPassageHorizon n)
      (cadlagPassageHorizon_pos n)
      (ActualSIntegrableStrategy.rawSequence data.approximant)
      data.variationSummable
      (data.martingaleEnvelopeSummable (cadlagPassageHorizon n)))
    0 (intrinsicJointPassageSourcePrefix_totalVariation_ae_le_rangeVariation
      base data n)

/-- The intrinsic joint-passage schedule with its normalized variation
bridges replaced by the common Mémín range bridges.  The source prefixes,
martingale kernels, and exhaustive localizer are unchanged. -/
noncomputable def intrinsicJointPassageRangeSchedule
    (base : LocalCompletedM2ASchedule G)
    (data : MeminSummableComponentLimitData (realizationModel G)) :
    LocalCompletedM2ASchedule G := by
  let target := intrinsicJointPassageSchedule base data
  exact {
    usualConditions := target.usualConditions
    localizer := target.localizer
    isLocalizingSequence := target.isLocalizingSequence
    horizon := target.horizon
    horizon_pos := target.horizon_pos
    localizer_le_horizon := target.localizer_le_horizon
    sourcePrefix := target.sourcePrefix
    sourcePrefix_stochasticIntegral := target.sourcePrefix_stochasticIntegral
    sourcePrefix_martingalePart := target.sourcePrefix_martingalePart
    sourcePrefix_finiteVariationPart :=
      target.sourcePrefix_finiteVariationPart
    martingale := target.martingale
    terminal_memLp := target.terminal_memLp
    variationBridge := intrinsicJointPassageRangeVariationBridge base data
    quadraticKernel := target.quadraticKernel }

/-- The martingale-selected integrand is variation-`L¹` on every intrinsic
joint source prefix over the common range normalizer. -/
theorem intrinsicJointPassageSelectedIntegrand_memLp_one
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat) :
    MemLp (intrinsicJointPassageSelectedIntegrand data w cutoff) 1
      (canonicalVariationMeasure
        (intrinsicJointPassageRangeVariationBridge base data n)) := by
  let localBridge := intrinsicJointPassageRangeVariationBridge base data n
  let deterministicBridge := meminRangeSourceFiniteVariationBridge G
    (cadlagPassageHorizon n) (cadlagPassageHorizon_pos n)
    (ActualSIntegrableStrategy.rawSequence data.approximant)
      data.variationSummable
      (data.martingaleEnvelopeSummable (cadlagPassageHorizon n))
  have hReference : localBridge.referenceMeasure =
      deterministicBridge.referenceMeasure :=
    (intrinsicJointPassageRangeVariationBridge_referenceMeasure_eq
      base data n).trans
        (meminRangeSourceFiniteVariationBridge_referenceMeasure_eq G
          (cadlagPassageHorizon n) (cadlagPassageHorizon_pos n)
          (ActualSIntegrableStrategy.rawSequence data.approximant)
          data.variationSummable
          (data.martingaleEnvelopeSummable
            (cadlagPassageHorizon n))).symm
  have hPath := intrinsicJointPassageSourcePrefix_pathVariation_ae_le
    base data n
  have hf := intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff
  have hMem : MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff) 1
      (meminRangeVariationControl G (cadlagPassageHorizon n)
        (cadlagPassageHorizon_pos n)
        (ActualSIntegrableStrategy.rawSequence data.approximant)
          data.variationSummable
          (data.martingaleEnvelopeSummable (cadlagPassageHorizon n))) :=
    intrinsicJointPassageSelectedIntegrand_memLp_one_rangeVariation
       Gactual hGactual Cfv data w cutoff hCutoff
        (cadlagPassageHorizon n) (cadlagPassageHorizon_pos n)
  change MemLp (intrinsicJointPassageSelectedIntegrand data w cutoff) 1
    (canonicalVariationMeasure localBridge)
  exact memLp_one_of_referenceMeasure_eq_of_pathVariation_le
    localBridge deterministicBridge hReference hPath
      (fun t omega => intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)) hf hMem

/-- The selected predictable limit is one exact finite-horizon
`M² + A¹` coefficient on each range-normalized joint prefix. -/
noncomputable def intrinsicJointPassageSelectedM2ACoefficient
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat)
    (hEnergy : MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n
        ).predictableEnergyMeasure) :
    FiniteHorizonM2ACoefficient
      ((intrinsicJointPassageRangeSchedule base data).variationBridge n)
      ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n) where
  coefficient := intrinsicJointPassageSelectedIntegrand data w cutoff
  coefficient_isStronglyMeasurable :=
    intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff
  coefficient_memLp_variation := by
    exact intrinsicJointPassageSelectedIntegrand_memLp_one
      base Gactual hGactual Cfv data w cutoff hCutoff n
  coefficient_memLp_energy := hEnergy

omit [F.IsRightContinuous] in
/-- On every positive integer horizon, replacing the full-sequence Mémín
limit by the integrand selected from actual joint-passage convexifications
preserves the finite-variation signed-measure identity. -/
theorem intrinsicJointPassageSelectedIntegrand_stopped_signedMeasure_eq
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((G.deterministicallyStopped (cadlagPassageHorizon n)
          (cadlagPassageHorizon_pos n)
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
            (fun t =>
              FiniteVariationPath.variationDirection
                  ((G.deterministicallyStopped (cadlagPassageHorizon n)
                    (cadlagPassageHorizon_pos n)
                    ).finiteVariationPart_isBoundedVariation omega) t *
                intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (data.finiteVariationLimit_boundedVariation omega)
              (cadlagPassageHorizon n)) := by
  have hMeasure := data.finiteVariation_stopped_signedMeasure_eq Cfv n
  have hLimit := Cfv.meminLimitIntegrand_stopped_path_l1 data.approximant
    data.variationSummable data.martingaleEnvelopeSummable n
  rw [hGactual] at hMeasure hLimit
  filter_upwards [hMeasure, hLimit] with omega hMeasureOmega hLimitOmega
  let hSource := (G.deterministicallyStopped (cadlagPassageHorizon n)
    (cadlagPassageHorizon_pos n)
      ).finiteVariationPart_isBoundedVariation omega
  let nu := (FiniteVariationPath.signedMeasure hSource).totalVariation
  have hIntegrandEq : (fun t =>
      FiniteVariationPath.variationDirection hSource t *
        intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega))
      =ᵐ[nu] fun t => FiniteVariationPath.variationDirection hSource t *
        meminLimitIntegrand
          (ActualSIntegrableStrategy.rawSequence data.approximant) t omega := by
    filter_upwards [hLimitOmega.2.1] with t ht
    have hConvex := (TailConvexWeights.toForward w).tendsto_apply_real ht
    have hSubsequence := hConvex.comp hCutoff.tendsto_atTop
    have hSelectedTendsto : Tendsto (fun k =>
        intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff k) (t, omega)) atTop
        (nhds (meminLimitIntegrand
          (ActualSIntegrableStrategy.rawSequence data.approximant)
            t omega)) := by
      apply hSubsequence.congr'
      filter_upwards with k
      symm
      change (SIntegrableStrategy.tailConvexCombination
        (ActualSIntegrableStrategy.rawSequence data.approximant)
          (w (cutoff k))).integrand t omega = _
      rw [SIntegrableStrategy.tailConvexCombination_integrand_apply]
      rfl
    have hSelected : intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega) =
      meminLimitIntegrand
          (ActualSIntegrableStrategy.rawSequence data.approximant) t omega := by
      exact hSelectedTendsto.limUnder_eq
    rw [hSelected]
  exact (WithDensityᵥEq.congr_ae hIntegrandEq).trans
    (by simpa only [nu, hSource, cadlagPassageHorizon] using hMeasureOmega)

/-- At one intrinsic joint passage, the selected coefficient orients the
stopped source variation to the corresponding stop of the existing
finite-variation component limit. -/
theorem intrinsicJointPassageSelectedIntegrand_pathDensity
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat)
    (E : SIntegrableFiniteVariationBridge
      (intrinsicJointPassageSourcePrefix base data n)) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((intrinsicJointPassageSourcePrefix base data n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
            (fun t => jumpCorrectedCanonicalVariationDensity E (t, omega) *
              intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (data.finiteVariationLimit_boundedVariation omega)
            (intrinsicJointPassageFiniteLocalizer base data n omega)) := by
  have hLimit := Cfv.meminLimitIntegrand_stopped_path_l1 data.approximant
    data.variationSummable data.martingaleEnvelopeSummable n
  rw [hGactual] at hLimit
  filter_upwards [
      intrinsicJointPassageSelectedIntegrand_stopped_signedMeasure_eq Gactual hGactual Cfv data
        w cutoff hCutoff n,
      hLimit,
      intrinsicJointPassageSourcePrefix_finiteVariationPart_stopAt
        base data n,
      intrinsicJointPassageSourcePrefix_jumpDensity_ae_eq_stoppedDirection
        base data n E]
      with omega hDensity hLimitOmega hSourcePathEq hBridgeDirection
  let T := cadlagPassageHorizon n
  let sourcePath := fun t =>
    (G.deterministicallyStopped T (cadlagPassageHorizon_pos n)
      ).finiteVariationPart t omega
  let hSourcePath :=
    (G.deterministicallyStopped T (cadlagPassageHorizon_pos n)
      ).finiteVariationPart_isBoundedVariation omega
  let limitPath := fun t => FiniteVariationStoppedPath.stopAt
    (data.finiteVariationLimit · omega) T t
  let hLimitPath := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (data.finiteVariationLimit_boundedVariation omega) T
  let tau := intrinsicJointPassageFiniteLocalizer base data n omega
  let selected := fun t => intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)
  let f := fun t => FiniteVariationPath.variationDirection hSourcePath t *
    selected t
  have hDensity' :
      (FiniteVariationPath.signedMeasure hSourcePath).totalVariation.withDensityᵥ f =
        FiniteVariationPath.signedMeasure hLimitPath := by
    simpa only [T, sourcePath, hSourcePath, limitPath, hLimitPath, selected,
      f] using hDensity
  have hSelectedEq : (fun t => meminLimitIntegrand
      (ActualSIntegrableStrategy.rawSequence data.approximant) t omega) =ᵐ[
      (FiniteVariationPath.signedMeasure hSourcePath).totalVariation]
      selected := by
    filter_upwards [hLimitOmega.2.1] with t ht
    have hConvex := (TailConvexWeights.toForward w).tendsto_apply_real ht
    have hSubsequence := hConvex.comp hCutoff.tendsto_atTop
    symm
    have hSelectedTendsto : Tendsto (fun k =>
        intrinsicJointPassageConvexifiedIntegrandSequence data w (cutoff k) (t, omega)) atTop
        (nhds (meminLimitIntegrand
          (ActualSIntegrableStrategy.rawSequence data.approximant)
            t omega)) := by
      apply hSubsequence.congr'
      filter_upwards with k
      symm
      change (SIntegrableStrategy.tailConvexCombination
        (ActualSIntegrableStrategy.rawSequence data.approximant)
          (w (cutoff k))).integrand t omega = _
      rw [SIntegrableStrategy.tailConvexCombination_integrand_apply]
      rfl
    exact hSelectedTendsto.limUnder_eq
  have hSelectedIntegrable : Integrable selected
      (FiniteVariationPath.signedMeasure hSourcePath).totalVariation :=
    hLimitOmega.1.congr hSelectedEq
  have hIntegrable : Integrable f
      (FiniteVariationPath.signedMeasure hSourcePath).totalVariation :=
    FiniteVariationPath.integrable_variationDirection_mul
      hSourcePath hSelectedIntegrable
  have hStoppedDensity := FiniteVariationStoppedPath.withDensityᵥ_stopAt_eq
    sourcePath limitPath hSourcePath hLimitPath
    ((G.deterministicallyStopped T
      (cadlagPassageHorizon_pos n)).finiteVariationPart_isRightContinuous omega)
    (fun t => FiniteVariationStoppedPath.rightContinuous_stopAt
      (data.finiteVariationLimit · omega)
      (data.finiteVariationLimit_rightContinuous omega) T t)
    tau hIntegrable hDensity'
  have hStoppedDirection :=
    FiniteVariationStoppedPath.variationDirection_stopAt_ae_eq
      sourcePath hSourcePath
      ((G.deterministicallyStopped T
        (cadlagPassageHorizon_pos n)).finiteVariationPart_isRightContinuous
          omega) tau
  have hTauLe : tau <= T := by
    exact RightContinuousStoppedMartingale.boundedTime_le
      (cadlagPassageHorizon n)
        (intrinsicJointPassageLocalizer base data n) omega
  have hNestedLimit : (fun t => FiniteVariationStoppedPath.stopAt
      limitPath tau t) = fun t => FiniteVariationStoppedPath.stopAt
        (data.finiteVariationLimit · omega) tau t := by
    funext t
    simp only [limitPath, FiniteVariationStoppedPath.stopAt]
    rw [min_eq_left ((min_le_right t tau).trans hTauLe)]
  have hNestedMeasure : FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt hLimitPath tau) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (data.finiteVariationLimit_boundedVariation omega) tau) :=
    FiniteVariationPath.signedMeasure_eq_of_eq _ _ hNestedLimit
  let hStoppedSource :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt hSourcePath tau
  have hSourceMeasure : FiniteVariationPath.signedMeasure
      ((intrinsicJointPassageSourcePrefix base data n
        ).finiteVariationPart_isBoundedVariation omega) =
      FiniteVariationPath.signedMeasure hStoppedSource := by
    apply FiniteVariationPath.signedMeasure_eq_of_eq
    exact funext hSourcePathEq
  rw [hSourceMeasure]
  have hIntegrandEq : (fun t =>
      jumpCorrectedCanonicalVariationDensity E (t, omega) * selected t) =ᵐ[
      (FiniteVariationPath.signedMeasure hStoppedSource).totalVariation] f := by
    filter_upwards [hBridgeDirection, hStoppedDirection]
      with t hBridge hStopped
    simp only [f]
    rw [hBridge, hStopped]
  exact (WithDensityᵥEq.congr_ae hIntegrandEq).trans
    (hStoppedDensity.trans hNestedMeasure)

/-- On any joint-prefix bridge carrying the selected coefficient in `L¹`,
the raw cumulative Stieltjes integral is the finite stop of the existing
finite-variation component limit. -/
theorem intrinsicJointPassageSelectedIntegrand_finiteVariationStopped_eq_raw
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat)
    (E : SIntegrableFiniteVariationBridge
      (intrinsicJointPassageSourcePrefix base data n))
    (hVariation : MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff) 1
      (canonicalVariationMeasure E)) :
    ProcessIndistinguishable mu
      (fun t omega => FiniteVariationStoppedPath.stopAt
        (data.finiteVariationLimit · omega)
        (intrinsicJointPassageFiniteLocalizer base data n omega) t)
      (finiteVariationIntegralProcess E (fun t omega =>
        intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega))) := by
  let selected : Process Omega := fun t omega =>
    intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)
  have hSelected : IsStronglyPredictable F selected :=
    intrinsicJointPassageSelectedIntegrand_isStronglyPredictable data w cutoff
  filter_upwards [
      integrable_section_ae_of_memLp_one_canonicalVariation
        E selected hSelected hVariation,
      intrinsicJointPassageSelectedIntegrand_pathDensity
        base Gactual hGactual Cfv data w cutoff hCutoff n E,
      data.finiteVariationLimit_zero]
      with omega hIntegrable hDensity hZero
  let tau := intrinsicJointPassageFiniteLocalizer base data n omega
  let stoppedLimit := fun t => FiniteVariationStoppedPath.stopAt
    (data.finiteVariationLimit · omega) tau t
  let hStoppedLimit := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (data.finiteVariationLimit_boundedVariation omega) tau
  have hOrientedIntegrable : Integrable
      (fun t => finiteVariationIntegralDensity E selected (t, omega))
      (FiniteVariationPath.signedMeasure
        ((intrinsicJointPassageSourcePrefix base data n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hSelected omega hIntegrable
  have hStoppedZero : stoppedLimit 0 = 0 := by
    change data.finiteVariationLimit (min 0 tau) omega = 0
    rw [min_eq_left (by positivity : (0 : NNReal) <= tau)]
    simpa only [Pi.zero_apply] using hZero
  have hInitial : FiniteVariationStoppedPath.stopAt
      (data.finiteVariationLimit · omega) tau ⊥ = 0 := by
    simpa only [stoppedLimit, NNReal.bot_eq_zero] using hStoppedZero
  intro t
  have hIdentity :=
    FiniteVariationPath.sub_initial_eq_setIntegral_of_withDensity_eq_signedMeasure
      hStoppedLimit
      (fun u => FiniteVariationStoppedPath.rightContinuous_stopAt
        (data.finiteVariationLimit · omega)
        (data.finiteVariationLimit_rightContinuous omega) tau u)
      (FiniteVariationPath.signedMeasure
        ((intrinsicJointPassageSourcePrefix base data n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation
      hOrientedIntegrable hDensity t
  rw [hInitial, sub_zero] at hIdentity
  simpa only [stoppedLimit, selected, finiteVariationIntegralProcess,
    pathVariationMeasureUpTo, NNReal.bot_eq_zero] using hIdentity

/-- The completed finite-variation component of the selected exact
coefficient is the finite joint-passage stop of the existing component
limit. -/
theorem intrinsicJointPassageSelectedM2ACoefficient_finiteVariationPart
    (base : LocalCompletedM2ASchedule G)
    (Gactual : ActualLocallySIntegrableStrategy (realizationModel G))
    (hGactual : Gactual.val = G)
    (Cfv : SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) Gactual)
    (data : MeminSummableComponentLimitData (realizationModel G))
    (w : forall n, TailConvexWeights n)
    (cutoff : Nat -> Nat) (hCutoff : StrictMono cutoff)
    (n : Nat)
    (hEnergy : MemLp
      (intrinsicJointPassageSelectedIntegrand data w cutoff)
      (2 : ENNReal)
      ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n
        ).predictableEnergyMeasure) :
    ProcessIndistinguishable mu
      (fun t omega => FiniteVariationStoppedPath.stopAt
        (data.finiteVariationLimit · omega)
        (intrinsicJointPassageFiniteLocalizer base data n omega) t)
      (finiteHorizonCompletedFiniteVariationPart
        (intrinsicJointPassageRangeSchedule base data).usualConditions
        ((intrinsicJointPassageRangeSchedule base data).horizon n)
        ((intrinsicJointPassageRangeSchedule base data).quadraticKernel n)
        ((intrinsicJointPassageRangeSchedule base data).variationBridge n)
        (intrinsicJointPassageSelectedM2ACoefficient base Gactual hGactual
          Cfv data w cutoff hCutoff n hEnergy)) := by
  let target := intrinsicJointPassageRangeSchedule base data
  let selected : Process Omega := fun t omega =>
    intrinsicJointPassageSelectedIntegrand data w cutoff (t, omega)
  let c := intrinsicJointPassageSelectedM2ACoefficient
    base Gactual hGactual Cfv data w cutoff hCutoff n hEnergy
  let X : Process Omega := fun t omega => FiniteVariationStoppedPath.stopAt
    (data.finiteVariationLimit · omega)
    (intrinsicJointPassageFiniteLocalizer base data n omega) t
  have hRaw : ProcessIndistinguishable mu X
      (finiteVariationIntegralProcess (target.variationBridge n) selected) := by
    exact intrinsicJointPassageSelectedIntegrand_finiteVariationStopped_eq_raw
      base Gactual hGactual Cfv data w cutoff hCutoff n
        (target.variationBridge n) c.coefficient_memLp_variation
  have hConstant : ∀ᵐ omega ∂mu, forall t,
      X t omega = X (min t (target.horizon n)) omega := by
    filter_upwards with omega
    intro t
    change data.finiteVariationLimit
        (min t (intrinsicJointPassageFiniteLocalizer base data n omega)) omega =
      data.finiteVariationLimit
        (min (min t (target.horizon n))
          (intrinsicJointPassageFiniteLocalizer base data n omega)) omega
    have hTau : intrinsicJointPassageFiniteLocalizer base data n omega <=
        target.horizon n := by
      exact RightContinuousStoppedMartingale.boundedTime_le
        (cadlagPassageHorizon n)
          (intrinsicJointPassageLocalizer base data n) omega
    rw [min_assoc, min_eq_right hTau]
  have hCompleted :=
    finiteHorizonCompletedFiniteVariationPart_indistinguishable
      target.usualConditions (target.variationBridge n)
        (target.quadraticKernel n) c
  filter_upwards [hRaw, hConstant, hCompleted] with omega hRawOmega
      hConstantOmega hCompletedOmega
  intro t
  calc
    X t omega = finiteVariationIntegralProcess
        (target.variationBridge n) selected t omega := hRawOmega t
    _ = finiteVariationIntegralProcess (target.variationBridge n) selected
        (min t (target.horizon n)) omega := by
      rw [<- hRawOmega t, <- hRawOmega (min t (target.horizon n))]
      exact hConstantOmega t
    _ = finiteVariationIntegralProcess
        (target.variationBridge n) c.integrand t omega := by
      change finiteVariationIntegralProcess (target.variationBridge n) selected
          (min t (target.horizon n)) omega =
        finiteVariationIntegralProcess (target.variationBridge n)
          (finiteHorizonCoefficient (target.horizon n) c.coefficient) t omega
      rw [finiteVariationIntegralProcess_finiteHorizonCoefficient]
      change finiteVariationIntegralProcess (target.variationBridge n) selected
          (min t (target.horizon n)) omega =
        finiteVariationIntegralProcess (target.variationBridge n)
          selected (min t (target.horizon n)) omega
      rfl
    _ = finiteHorizonCompletedFiniteVariationPart target.usualConditions
        (target.horizon n) (target.quadraticKernel n)
          (target.variationBridge n) c t omega :=
      (hCompletedOmega t).symm

end LocalCompletedM2A

end FTAPTheorem42
