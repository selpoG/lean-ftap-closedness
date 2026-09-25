/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.FiniteVariationCoordinateAgreement
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualConvexCombination
import FTAPTheorem42.Stochastic.Integral.Local.Construction.UnitSourceRealization
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationStieltjesCalculus
import FTAPTheorem42.Stochastic.FiniteVariation.VariationDirection

/-!
# Intrinsic finite-variation Stieltjes calculus

Every graph in the local-completed carrier has coefficient `L1` membership
and exact finite-variation semantics along one exhaustive schedule.  Given a
deterministic horizon, that schedule eventually lies beyond the horizon on
almost every path.  Stopping the local density identity there recovers the
global deterministic-horizon Stieltjes identity.

This module packages that local-to-global argument as the concrete
finite-variation calculus consumed by the Mémín range-realization theorem.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

omit [MeasurableSpace Omega] [F.IsRightContinuous]
    [SigmaFiniteFiltration mu F] in
/-- The intrinsic direction is unchanged when the underlying paths are
equal; proof arguments for bounded variation carry no extra semantics. -/
private theorem variationDirection_eq_of_path_eq
    {A B : NNReal -> Real} (hA : BoundedVariationOn A Set.univ)
    (hB : BoundedVariationOn B Set.univ) (hAB : A = B) :
    FiniteVariationPath.variationDirection hA =
      FiniteVariationPath.variationDirection hB := by
  subst B
  rfl

/-- On almost every path, an intrinsic actual coefficient is integrable
against every deterministic stop of the source finite-variation part. -/
theorem actual_finiteVariationPart_stopped_integrable
    (H : ActualSIntegrableStrategy (realizationModel G))
    (T : NNReal) (hT : 0 < T) :
    ∀ᵐ omega ∂mu, Integrable (fun t => H.val.integrand t omega)
      (FiniteVariationPath.signedMeasure
        ((G.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  have hAllIntegrable : ∀ᵐ omega ∂mu, forall n,
      Integrable (fun t => H.val.integrand t omega)
        (FiniteVariationPath.signedMeasure
          ((schedule.sourcePrefix n
            ).finiteVariationPart_isBoundedVariation omega)).totalVariation :=
    eventually_countable_forall.2 fun n => by
      obtain ⟨hVariation, _⟩ :=
        actualCoordinate_finiteVariationSemantics H n
      exact integrable_section_ae_of_memLp_one_canonicalVariation
        (schedule.variationBridge n) H.val.integrand
          H.val.integrand_isPredictable hVariation
  have hAllSource : ∀ᵐ omega ∂mu, forall n t,
      (schedule.sourcePrefix n).finiteVariationPart t omega =
        MeasureTheory.stoppedProcess
          (G.deterministicallyStopped (schedule.horizon n)
            (schedule.horizon_pos n)).finiteVariationPart
          (schedule.localizer n) t omega :=
    eventually_countable_forall.2 fun n =>
      schedule.sourcePrefix_finiteVariationPart n
  filter_upwards [schedule.isLocalizingSequence.tendsto_top,
      hAllIntegrable, hAllSource]
      with omega hTop hIntegrable hSource
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  obtain ⟨n, hn⟩ := (hTop T).exists
  have hTtau : (T : WithTop NNReal) <= schedule.localizer n omega := hn.le
  have hTauFinite : schedule.localizer n omega ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top)
      (schedule.localizer_le_horizon n omega)
  lift schedule.localizer n omega to NNReal using hTauFinite with tau hTau
  have hTTau : T <= tau := by
    exact WithTop.coe_le_coe.mp (hTau ▸ hTtau)
  have hTauHorizon : tau <= schedule.horizon n := by
    exact WithTop.coe_le_coe.mp
      (hTau ▸ schedule.localizer_le_horizon n omega)
  let prefixPath := fun t =>
    (schedule.sourcePrefix n).finiteVariationPart t omega
  let stoppedPrefix := FiniteVariationStoppedPath.stopAt prefixPath T
  let targetPath := fun t =>
    (G.deterministicallyStopped T hT).finiteVariationPart t omega
  have hPath : targetPath = stoppedPrefix := by
    funext t
    simp only [targetPath, stoppedPrefix,
      FiniteVariationStoppedPath.stopAt,
      LocallySIntegrableStrategy.deterministicallyStopped]
    change G.finiteVariationPart (min t T) omega =
      (schedule.sourcePrefix n).finiteVariationPart (min t T) omega
    rw [hSource n (min t T)]
    simp only [MeasureTheory.stoppedProcess]
    rw [<- hTau, <- WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    simp only [LocallySIntegrableStrategy.deterministicallyStopped]
    rw [min_eq_left ((min_le_right t T).trans hTTau),
      min_eq_left ((min_le_right t T).trans
        (hTTau.trans hTauHorizon))]
  let hPrefix := (schedule.sourcePrefix n
    ).finiteVariationPart_isBoundedVariation omega
  let hStoppedPrefix :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt hPrefix T
  have hMeasure : FiniteVariationPath.signedMeasure
      ((G.deterministicallyStopped T hT
        ).finiteVariationPart_isBoundedVariation omega) =
      FiniteVariationPath.signedMeasure hStoppedPrefix :=
    FiniteVariationPath.signedMeasure_eq_of_eq _ _ hPath
  rw [congrArg SignedMeasure.totalVariation hMeasure]
  exact FiniteVariationStoppedPath.integrable_totalVariation_stopAt
    prefixPath hPrefix
      ((schedule.sourcePrefix n).finiteVariationPart_isRightContinuous omega)
      T (hIntegrable n)

/-- The finite-variation output of every intrinsic actual graph has the
deterministic-horizon Stieltjes density prescribed by the unit source. -/
theorem actual_finiteVariationPart_stopped_signedMeasure
    (H : ActualSIntegrableStrategy (realizationModel G))
    (T : NNReal) (hT : 0 < T) :
    ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        ((G.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
            (fun t =>
              FiniteVariationPath.variationDirection
                  ((G.deterministicallyStopped T hT
                    ).finiteVariationPart_isBoundedVariation omega) t *
                H.val.integrand t omega) =
        FiniteVariationPath.signedMeasure
          (((H.val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation omega)) := by
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  have hAllDensity : ∀ᵐ omega ∂mu, forall n,
      let sigma := RightContinuousStoppedMartingale.boundedTime
        (schedule.horizon n) (schedule.localizer n) omega
      (FiniteVariationPath.signedMeasure
        ((schedule.sourcePrefix n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
          (fun u => finiteVariationIntegralDensity
            (schedule.variationBridge n)
              (witness.coefficient n).integrand (u, omega)) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (H.val.finiteVariationPart_isBoundedVariation omega) sigma) :=
    eventually_countable_forall.2 fun n =>
      actualCoordinate_finiteVariationPathDensity H n
  have hAllCoefficientIntegrable : ∀ᵐ omega ∂mu, forall n,
      Integrable (fun t => (witness.coefficient n).integrand t omega)
        (FiniteVariationPath.signedMeasure
          ((schedule.sourcePrefix n
            ).finiteVariationPart_isBoundedVariation omega)).totalVariation :=
    eventually_countable_forall.2 fun n =>
      integrable_section_ae_of_memLp_one_canonicalVariation
        (schedule.variationBridge n) (witness.coefficient n).integrand
          (witness.coefficient n).integrand_isStronglyPredictable
            (witness.coefficient n).integrand_memLp_variation
  have hAllSource : ∀ᵐ omega ∂mu, forall n t,
      (schedule.sourcePrefix n).finiteVariationPart t omega =
        MeasureTheory.stoppedProcess
          (G.deterministicallyStopped (schedule.horizon n)
            (schedule.horizon_pos n)).finiteVariationPart
          (schedule.localizer n) t omega :=
    eventually_countable_forall.2 fun n =>
      schedule.sourcePrefix_finiteVariationPart n
  have hAllBridgeDirection : ∀ᵐ omega ∂mu, forall n,
      (fun t => jumpCorrectedCanonicalVariationDensity
        (schedule.variationBridge n) (t, omega)) =ᵐ[
          (FiniteVariationPath.signedMeasure
            ((schedule.sourcePrefix n
              ).finiteVariationPart_isBoundedVariation omega)).totalVariation]
        FiniteVariationPath.variationDirection
          ((schedule.sourcePrefix n
            ).finiteVariationPart_isBoundedVariation omega) :=
    eventually_countable_forall.2 fun n =>
      (schedule.variationBridge n
        ).jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection
  filter_upwards [schedule.isLocalizingSequence.tendsto_top,
      hAllDensity, hAllCoefficientIntegrable, hAllSource,
      hAllBridgeDirection]
      with omega hTop hDensity hCoefficientIntegrable hSource
        hBridgeDirection
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  obtain ⟨n, hn⟩ := (hTop T).exists
  have hTtau : (T : WithTop NNReal) <= schedule.localizer n omega := hn.le
  have hTauFinite : schedule.localizer n omega ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top)
      (schedule.localizer_le_horizon n omega)
  lift schedule.localizer n omega to NNReal using hTauFinite with tau hTau
  have hTTau : T <= tau :=
    WithTop.coe_le_coe.mp (hTau ▸ hTtau)
  have hTauHorizon : tau <= schedule.horizon n :=
    WithTop.coe_le_coe.mp
      (hTau ▸ schedule.localizer_le_horizon n omega)
  let sigma := RightContinuousStoppedMartingale.boundedTime
    (schedule.horizon n) (schedule.localizer n) omega
  have hSigma : sigma = tau := by
    apply WithTop.coe_eq_coe.mp
    rw [RightContinuousStoppedMartingale.coe_boundedTime, <- hTau,
      min_eq_right (WithTop.coe_le_coe.mpr hTauHorizon)]
  have hTSigma : T <= sigma := hSigma ▸ hTTau
  let prefixPath := fun t =>
    (schedule.sourcePrefix n).finiteVariationPart t omega
  let hPrefix := (schedule.sourcePrefix n
    ).finiteVariationPart_isBoundedVariation omega
  let stoppedPrefix := FiniteVariationStoppedPath.stopAt prefixPath T
  let hStoppedPrefix :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt hPrefix T
  let targetSource := fun t =>
    (G.deterministicallyStopped T hT).finiteVariationPart t omega
  let hTargetSource := (G.deterministicallyStopped T hT
    ).finiteVariationPart_isBoundedVariation omega
  have hSourcePath : targetSource = stoppedPrefix := by
    funext t
    simp only [targetSource, stoppedPrefix,
      FiniteVariationStoppedPath.stopAt,
      LocallySIntegrableStrategy.deterministicallyStopped]
    change G.finiteVariationPart (min t T) omega =
      (schedule.sourcePrefix n).finiteVariationPart (min t T) omega
    rw [hSource n (min t T)]
    simp only [MeasureTheory.stoppedProcess]
    rw [<- hTau, <- WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    simp only [LocallySIntegrableStrategy.deterministicallyStopped]
    rw [min_eq_left ((min_le_right t T).trans hTTau),
      min_eq_left ((min_le_right t T).trans
        (hTTau.trans hTauHorizon))]
  let stoppedOutput := FiniteVariationStoppedPath.stopAt
    (fun t => H.val.finiteVariationPart t omega) sigma
  let hStoppedOutput := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (H.val.finiteVariationPart_isBoundedVariation omega) sigma
  let targetOutput := fun t =>
    (H.val.toLocally.deterministicallyStopped T hT
      ).finiteVariationPart t omega
  let hTargetOutput := (H.val.toLocally.deterministicallyStopped T hT
    ).finiteVariationPart_isBoundedVariation omega
  have hOutputPath : targetOutput =
      FiniteVariationStoppedPath.stopAt stoppedOutput T := by
    funext t
    simp only [targetOutput, stoppedOutput,
      FiniteVariationStoppedPath.stopAt,
      LocallySIntegrableStrategy.deterministicallyStopped]
    rw [min_eq_left ((min_le_right t T).trans hTSigma)]
    rfl
  let E := schedule.variationBridge n
  let c := witness.coefficient n
  let density := fun u => finiteVariationIntegralDensity E c.integrand
    (u, omega)
  have hDensityIntegrable : Integrable density
      (FiniteVariationPath.signedMeasure hPrefix).totalVariation :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E c.integrand_isStronglyPredictable omega
        (hCoefficientIntegrable n)
  have hStoppedDensity :
      (FiniteVariationPath.signedMeasure hStoppedPrefix).totalVariation.withDensityᵥ
          density =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            hStoppedOutput T) :=
    FiniteVariationStoppedPath.withDensityᵥ_stopAt_eq
      prefixPath stoppedOutput hPrefix hStoppedOutput
      ((schedule.sourcePrefix n).finiteVariationPart_isRightContinuous omega)
      (fun t => FiniteVariationStoppedPath.rightContinuous_stopAt
        (fun u => H.val.finiteVariationPart u omega)
          (H.val.finiteVariationPart_isRightContinuous omega) sigma t)
      T hDensityIntegrable (hDensity n)
  have hSourceMeasure : FiniteVariationPath.signedMeasure hTargetSource =
      FiniteVariationPath.signedMeasure hStoppedPrefix :=
    FiniteVariationPath.signedMeasure_eq_of_eq _ _ hSourcePath
  have hOutputMeasure : FiniteVariationPath.signedMeasure hTargetOutput =
      FiniteVariationPath.signedMeasure
        (FiniteVariationStoppedPath.boundedVariationOn_stopAt
          hStoppedOutput T) :=
    FiniteVariationPath.signedMeasure_eq_of_eq _ _ hOutputPath
  have hDirectionPath : FiniteVariationPath.variationDirection hTargetSource =
      FiniteVariationPath.variationDirection hStoppedPrefix :=
    variationDirection_eq_of_path_eq hTargetSource hStoppedPrefix hSourcePath
  let nuStopped :=
    (FiniteVariationPath.signedMeasure hStoppedPrefix).totalVariation
  have hNuStopped : nuStopped =
      (FiniteVariationPath.signedMeasure hPrefix).totalVariation.restrict
        (Ioc 0 T) :=
    FiniteVariationStoppedPath.totalVariation_stopAt_eq_restrict_Ioc
      prefixPath hPrefix
        ((schedule.sourcePrefix n).finiteVariationPart_isRightContinuous omega)
        T
  have hNuLe : nuStopped <=
      (FiniteVariationPath.signedMeasure hPrefix).totalVariation := by
    rw [hNuStopped]
    exact Measure.restrict_le_self
  have hStoppedDirection :
      FiniteVariationPath.variationDirection hStoppedPrefix =ᵐ[nuStopped]
        FiniteVariationPath.variationDirection hPrefix :=
    FiniteVariationStoppedPath.variationDirection_stopAt_ae_eq
      prefixPath hPrefix
        ((schedule.sourcePrefix n).finiteVariationPart_isRightContinuous omega)
        T
  have hSupport : ∀ᵐ u ∂nuStopped, u ∈ Ioc (0 : NNReal) T := by
    rw [hNuStopped]
    exact ae_restrict_mem measurableSet_Ioc
  have hIntegrandEq : (fun u =>
      FiniteVariationPath.variationDirection hTargetSource u *
        H.val.integrand u omega) =ᵐ[nuStopped] density := by
    filter_upwards [hStoppedDirection,
        ae_mono hNuLe (hBridgeDirection n), hSupport]
        with u hStopDirection hBridge hu
    have huHorizon : u <= schedule.horizon n :=
      hu.2.trans (hTTau.trans hTauHorizon)
    have hCoefficient : c.integrand u omega = H.val.integrand u omega := by
      unfold FiniteHorizonM2ACoefficient.integrand finiteHorizonCoefficient
      rw [PredictableProcess.restrict_apply_of_mem]
      · exact congrFun (witness.coefficient_eq n) (u, omega)
      · exact (mem_stochasticIntervalIocZero_iff
          (fun _ : Omega => schedule.horizon n) u omega).2
            ⟨hu.1, huHorizon⟩
    simp only [density, finiteVariationIntegralDensity]
    rw [hDirectionPath, hStopDirection, hBridge, hCoefficient]
  rw [congrArg SignedMeasure.totalVariation hSourceMeasure, hOutputMeasure]
  exact (WithDensityᵥEq.congr_ae hIntegrandEq).trans hStoppedDensity

/-- The intrinsic local-completed carrier carries its own finite-variation
Stieltjes calculus once the chosen source graph is the zero-based unit graph.
The difference field is obtained from pairwise schedule refinement, while the
two analytic fields are the local-to-global results above. -/
theorem finiteVariationStieltjesCalculus
    (base : LocalCompletedM2ASchedule G)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hZero : G.stochasticIntegral 0 =ᵐ[mu] 0) :
    SIntegrableFiniteVariationStieltjesCalculus D
      (realizationModel G) (actualUnitSource base hUnit hZero) where
  difference_isRealized := by
    intro H K
    simpa only [
      SIntegrablePredictableMultiplierLinearL2Calculus.lemma411Difference,
      SIntegrableStrategy.subOfRightContinuous,
      actualAddOfPairRefinement_val, actualNeg, ActualSIntegrableStrategy.congr] using
        (actualAddOfPairRefinement H (actualNeg G K)).property
  finiteVariationPart_stopped_integrable :=
    actual_finiteVariationPart_stopped_integrable
  finiteVariationPart_stopped_signedMeasure :=
    actual_finiteVariationPart_stopped_signedMeasure

end LocalCompletedM2A

end FTAPTheorem42
