/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.ContinuousFiniteVariationMartingale
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import FTAPTheorem42.Foundations.FactorialChronologicalGrid

/-!
# Rigidity of predictable finite-variation local martingales

The centered martingale coordinate of a realized stochastic-integral graph
must not depend on the raw special-semimartingale decomposition stored in its
record.  The required uniqueness reduces to the standard fact that a
predictable finite-variation local martingale is indistinguishable from its
initial value.

This module proves that fact from the already available predictable-jump
control, cumulative-variation stopping, and continuous finite-variation
martingale rigidity.  It then identifies the centered martingale components
of any two raw strategy records with indistinguishable gain processes.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory Topology

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A right-continuous local martingale remains a local martingale after
replacement by an indistinguishable strongly adapted right-continuous
version. -/
theorem LocalMartingale.congr_indistinguishable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
    {X Y : Process Omega}
    (hX : LocalMartingale X F mu)
    (hYAdapted : StronglyAdapted F Y)
    (hYRight : forall omega t,
      ContinuousWithinAt (Y · omega) (Set.Ici t) t)
    (hXY : ProcessIndistinguishable mu X Y) :
    LocalMartingale Y F mu := by
  unfold LocalMartingale at hX ⊢
  let tau : Nat -> Omega -> WithTop NNReal := hX.localSeq
  refine ⟨tau, hX.isLocalizingSequence_localSeq, ?_⟩
  intro n
  let B : Set Omega :=
    {omega | (⊥ : WithTop NNReal) < tau n omega}
  change Martingale
    (MeasureTheory.stoppedProcess (fun t => B.indicator (Y t)) (tau n))
      F mu
  have hTau : IsStoppingTime F (tau n) :=
    hX.isLocalizingSequence_localSeq.isStoppingTime n
  have hB : MeasurableSet[F 0] B := by
    have hEq : B = {omega | tau n omega <= (0 : NNReal)}ᶜ := by
      ext omega
      simp only [B, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      rw [show (⊥ : WithTop NNReal) = ((0 : NNReal) : WithTop NNReal) by rfl]
    rw [hEq]
    exact (hTau.measurableSet_le 0).compl
  have hStoppedAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess Y (tau n)) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hYAdapted hTau hYRight
  have hTargetAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess (fun t => B.indicator (Y t)) (tau n)) := by
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    intro t
    have hBt : MeasurableSet[F t] B :=
      (F.mono (show (0 : NNReal) ≤ t from bot_le)) B hB
    exact (hStoppedAdapted t).indicator hBt
  apply (hX.stoppedProcess_localSeq n).congr hTargetAdapted
  intro t
  filter_upwards [hXY] with omega homega
  simp only [B, tau, MeasureTheory.stoppedProcess]
  by_cases hmem : omega ∈
      {omega | (⊥ : WithTop NNReal) < hX.localSeq n omega}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    exact homega _
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

namespace PredictableFiniteVariationLocalMartingale

open ContinuousFiniteVariationMartingale

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- A predictable finite-variation local martingale can be inserted into a
zero-gain candidate decomposition.  This auxiliary strategy lets the
predictable-jump machinery act on the process without asserting that the
candidate is a realized stochastic integral. -/
noncomputable def zeroGainStrategy
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ) :
    SIntegrableStrategy D where
  integrand := 0 • A
  stochasticIntegral := 0
  martingalePart := fun t omega => -A t omega
  finiteVariationPart := A
  finiteVariationMeasure := 0
  integrand_isPredictable := by
    unfold IsStronglyPredictable at hAPredictable ⊢
    rw [show Function.uncurry (0 • A) =
        0 • Function.uncurry A by
      funext x
      rfl]
    exact hAPredictable.const_smul 0
  stochasticIntegral_isStronglyAdapted := fun _ => stronglyMeasurable_zero
  stochasticIntegral_isRightContinuous := fun _ _ =>
    continuousWithinAt_const
  martingalePart_isLocalMartingale := hALocal.neg
  martingalePart_isStronglyAdapted := hAPredictable.stronglyAdapted.neg
  martingalePart_isRightContinuous := fun omega t =>
    (hARight omega t).neg
  finiteVariationPart_isPredictable := hAPredictable
  finiteVariationPart_isRightContinuous := hARight
  finiteVariationPart_isBoundedVariation := hABoundedVariation
  integral_decomposition := by
    filter_upwards [] with omega
    intro t
    simp only [Pi.zero_apply]
    ring
  source_decomposition := D.decomposition

/-- Predictable-jump control applied to the zero-gain decomposition forces
all jumps of a predictable finite-variation local martingale to vanish on a
fixed positive horizon. -/
theorem processLeftJump_ae_eq_zero_upTo
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (D : SpecialSemimartingaleDecomposition S F mu)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ)
    {T : NNReal} (hT : 0 < T) :
    ∀ᵐ omega ∂mu, ∀ t, t ≤ T → processLeftJump A t omega = 0 := by
  let H : SIntegrableStrategy D :=
    zeroGainStrategy A hALocal hAPredictable hARight hABoundedVariation
  have hALeft : ProcessHasLeftLimits A := by
    simpa only [H, zeroGainStrategy] using H.finiteVariationPart_hasLeftLimits
  have hMartingaleLeft : ProcessHasLeftLimits H.martingalePart := by
    simpa only [H, zeroGainStrategy] using hALeft.neg
  let gainEnvelope : Omega → Real := 0
  obtain ⟨J, hJMem, _, hJumpBound, hJNorm⟩ :=
    SIntegrableProcessStoppingCalculus.lemma47MartingaleJumpEnvelope_of_strategy
      hUsual H hMartingaleLeft gainEnvelope MemLp.zero
      (Filter.Eventually.of_forall fun omega t => by
        simp [H, zeroGainStrategy, gainEnvelope]) hT
  have hJNormZero : eLpNorm J (2 : ENNReal) mu = 0 := by
    apply le_antisymm
    · simpa only [gainEnvelope, eLpNorm_zero, mul_zero] using hJNorm
    · exact bot_le
  have hJZero : J =ᵐ[mu] 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).1
      hJNormZero
  filter_upwards [hJZero, hJumpBound] with omega hJZeroOmega hJumpOmega
  intro t ht
  have hJZeroOmega' : J omega = 0 := by
    simpa only [Pi.zero_apply] using hJZeroOmega
  have hNegJump :
      processLeftJump H.martingalePart t omega =
        -processLeftJump A t omega := by
    change processLeftJump (fun s omega => -A s omega) t omega = _
    rw [show (fun s omega => -A s omega) =
        (fun s omega => (-1 : Real) * A s omega) by
      funext s omega
      ring]
    rw [processLeftJump_const_mul hALeft (-1) t omega]
    ring
  have hAbs : |processLeftJump A t omega| <= 0 := by
    simpa only [hNegJump, abs_neg, hJZeroOmega'] using hJumpOmega t ht
  exact abs_eq_zero.mp (le_antisymm hAbs (abs_nonneg _))

/-- All left jumps vanish outside one null set, simultaneously over the
whole nonnegative time axis. -/
theorem processLeftJump_ae_eq_zero
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (D : SpecialSemimartingaleDecomposition S F mu)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ) :
    ∀ᵐ omega ∂mu, ∀ t, processLeftJump A t omega = 0 := by
  have hInteger : ∀ n : Nat, ∀ᵐ omega ∂mu, ∀ t : NNReal,
      t ≤ ((n + 1 : Nat) : NNReal) → processLeftJump A t omega = 0 := by
    intro n
    apply processLeftJump_ae_eq_zero_upTo hUsual D A hALocal
      hAPredictable hARight hABoundedVariation
    exact_mod_cast Nat.succ_pos n
  filter_upwards [ae_all_iff.2 hInteger] with omega hOmega
  intro t
  have htCeil : t ≤ (Nat.ceil t : NNReal) := by
    exact_mod_cast Nat.le_ceil t
  exact hOmega (Nat.ceil t) t
    (htCeil.trans (by exact_mod_cast Nat.le_succ (Nat.ceil t)))

omit [MeasurableSpace Omega] in
/-- A right-continuous path with left limits and no left jumps is
continuous. -/
theorem continuous_of_rightContinuous_of_processLeftJump_eq_zero
    (f : NNReal → Real)
    (hRight : forall t, ContinuousWithinAt f (Set.Ici t) t)
    (hLeft : forall t,
      Tendsto f (nhdsWithin t (Set.Iio t)) (nhds (Function.leftLim f t)))
    (hJump : forall t, f t - Function.leftLim f t = 0) :
    Continuous f := by
  apply continuous_iff_continuousAt.2
  intro t
  apply continuousAt_iff_continuous_left'_right'.2
  constructor
  · have hLeftEq : Function.leftLim f t = f t := by
      linarith [hJump t]
    change Tendsto f (nhdsWithin t (Set.Iio t)) (nhds (f t))
    rw [← hLeftEq]
    exact hLeft t
  · exact (hRight t).mono Ioi_subset_Ici_self

/-- The jump theorem supplies pathwise continuity outside one common null
set. -/
theorem continuous_ae
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (D : SpecialSemimartingaleDecomposition S F mu)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ) :
    ∀ᵐ omega ∂mu, Continuous (A · omega) := by
  have hLeft : ProcessHasLeftLimits A := fun omega t =>
    (hABoundedVariation omega).tendsto_leftLim t
  filter_upwards [processLeftJump_ae_eq_zero hUsual D A hALocal
    hAPredictable hARight hABoundedVariation] with omega hJump
  apply continuous_of_rightContinuous_of_processLeftJump_eq_zero
    (A · omega) (hARight omega) (hLeft omega)
  intro t
  exact hJump t

/-- Cumulative-variation passages at the increasing levels `n + 1`. -/
noncomputable def variationLocalizer
    (H : SIntegrableStrategy D) : Nat → Omega → WithTop NNReal :=
  fun n =>
    SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter H
      (n + 1 : Nat)

omit [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F] in
/-- Since every stored finite-variation path has finite total variation,
its increasing cumulative-variation passages form a genuine localizing
sequence. -/
theorem variationLocalizer_isLocalizingSequence
    [F.IsRightContinuous]
    (H : SIntegrableStrategy D) :
    ProbabilityTheory.IsLocalizingSequence F (variationLocalizer H) mu := by
  refine
    { isStoppingTime := fun n =>
        SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter_isStoppingTime
          H H.finiteVariationPart_isRightContinuous (n + 1 : Nat)
      tendsto_top := Filter.Eventually.of_forall fun omega => ?_
      mono := Filter.Eventually.of_forall fun omega => ?_ }
  · rw [WithTop.tendsto_nhds_top_iff]
    intro t
    let variationTotal : Real :=
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ
    have hLevel : Tendsto (fun n : Nat => ((n + 1 : Nat) : Real))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    filter_upwards [hLevel.eventually_gt_atTop variationTotal] with n hn
    have hTop : variationLocalizer H n omega = ⊤ := by
      unfold variationLocalizer
        SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
        RightContinuousHittingTime.strictHittingAfter
      apply MeasureTheory.hittingAfter_eq_top_iff.mpr
      intro s _
      change ¬((n + 1 : Nat) : Real) <
        SIntegrableFiniteVariationBridge.cumulativeVariation H s omega
      apply not_lt_of_ge
      calc
        SIntegrableFiniteVariationBridge.cumulativeVariation H s omega ≤
            variationTotal := by
          let nu := (FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation omega)).totalVariation
          let : IsFiniteMeasure nu := by
            dsimp only [nu]
            unfold SignedMeasure.totalVariation
            infer_instance
          exact measureReal_mono (μ := nu) (Set.subset_univ _)
            (measure_ne_top nu Set.univ)
        _ ≤ ((n + 1 : Nat) : Real) := hn.le
    rw [hTop]
    exact WithTop.coe_lt_top t
  · intro n m hnm
    unfold variationLocalizer
    unfold SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
      RightContinuousHittingTime.strictHittingAfter
    apply MeasureTheory.hittingAfter_anti
    intro x hx
    change ((m + 1 : Nat) : Real) < x at hx
    change ((n + 1 : Nat) : Real) < x
    exact (by exact_mod_cast Nat.add_le_add_right hnm 1 :
      ((n + 1 : Nat) : Real) ≤ (m + 1 : Nat)).trans_lt hx

omit [MeasurableSpace Omega] in
/-- Localizer stopping preserves full path continuity when the original
path is continuous.  The bottom-time indicator merely selects between the
stopped path and the zero path. -/
theorem localizingStoppedProcess_continuous
    (X : Process Omega) (rho : Omega → WithTop NNReal)
    (omega : Omega) (hX : Continuous (X · omega)) :
    Continuous (localizingStoppedProcess X rho · omega) := by
  by_cases hPositive : (⊥ : WithTop NNReal) < rho omega
  · have hMem : omega ∈ {omega | (⊥ : WithTop NNReal) < rho omega} :=
      hPositive
    cases hRho : rho omega with
    | top =>
        have hEq : (localizingStoppedProcess X rho · omega) =
            (X · omega) := by
          funext t
          rw [localizingStoppedProcess,
            MeasureTheory.stoppedProcess_indicator_comm]
          rw [Set.indicator_of_mem hMem]
          exact MeasureTheory.stoppedProcess_eq_of_le (by rw [hRho]; exact le_top)
        rw [hEq]
        exact hX
    | coe s =>
        have hEq : (localizingStoppedProcess X rho · omega) =
            FiniteVariationStoppedPath.stopAt (X · omega) s := by
          funext t
          rw [localizingStoppedProcess,
            MeasureTheory.stoppedProcess_indicator_comm]
          rw [Set.indicator_of_mem hMem]
          by_cases hts : t ≤ s
          · rw [MeasureTheory.stoppedProcess_eq_of_le (by
                rw [hRho]
                exact WithTop.coe_le_coe.mpr hts)]
            simp only [FiniteVariationStoppedPath.stopAt, min_eq_left hts]
          · have hst : s ≤ t := le_of_not_ge hts
            rw [MeasureTheory.stoppedProcess_eq_of_ge (by
                rw [hRho]
                exact WithTop.coe_le_coe.mpr hst)]
            simp only [FiniteVariationStoppedPath.stopAt, min_eq_right hst,
              hRho, WithTop.untopA_eq_untop WithTop.coe_ne_top,
              WithTop.untop_coe]
        rw [hEq]
        exact hX.comp (continuous_id.min continuous_const)
  · have hNotMem : omega ∉ {omega | (⊥ : WithTop NNReal) < rho omega} :=
      hPositive
    have hEq : (localizingStoppedProcess X rho · omega) = 0 := by
      funext t
      rw [localizingStoppedProcess,
        MeasureTheory.stoppedProcess_indicator_comm]
      simp only [Set.indicator_of_notMem hNotMem, Pi.zero_apply]
    rw [hEq]
    exact continuous_const

omit [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F] in
/-- At a cumulative-variation localizer, a jump-free finite-variation path
has deterministic total variation at most the passage level.  The estimate
also covers the case where the passage time is infinite. -/
theorem eVariationOn_localizingStoppedProcess_variationLocalizer_le
    (H : SIntegrableStrategy D)
    (n : Nat)
    (rho : Omega → WithTop NNReal)
    (hRhoLe : forall omega, rho omega ≤ variationLocalizer H n omega)
    (omega : Omega)
    (hJump : forall t,
      processLeftJump H.finiteVariationPart t omega = 0)
    :
    eVariationOn
        (localizingStoppedProcess H.finiteVariationPart
          rho · omega) Set.univ ≤
      ENNReal.ofReal (n + 1 : Nat) := by
  let tau : Omega → WithTop NNReal := variationLocalizer H n
  let c : Real := (n + 1 : Nat)
  by_cases hPositive : (⊥ : WithTop NNReal) < rho omega
  · have hMem : omega ∈ {omega | (⊥ : WithTop NNReal) < rho omega} :=
      hPositive
    cases hRho : rho omega with
    | top =>
        have hTau : tau omega = ⊤ := by
          exact top_unique (hRho ▸ hRhoLe omega)
        have hPath :
            (localizingStoppedProcess H.finiteVariationPart rho · omega) =
              (H.finiteVariationPart · omega) := by
          funext t
          rw [localizingStoppedProcess,
            MeasureTheory.stoppedProcess_indicator_comm,
            Set.indicator_of_mem hMem]
          exact MeasureTheory.stoppedProcess_eq_of_le (by rw [hRho]; exact le_top)
        rw [hPath]
        let nu := (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation omega)).totalVariation
        let : IsFiniteMeasure nu := by
          dsimp only [nu]
          unfold SignedMeasure.totalVariation
          infer_instance
        have hPassageTop :
            SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
              H c omega = ⊤ := by
          simpa only [tau, variationLocalizer, c] using hTau
        have hAtMost (k : Nat) :
            SIntegrableFiniteVariationBridge.cumulativeVariation H k omega ≤ c := by
          change MeasureTheory.hittingAfter
            (SIntegrableFiniteVariationBridge.cumulativeVariation H)
              (Set.Ioi c) (0 : NNReal) omega = ⊤ at hPassageTop
          have hNoHit := (MeasureTheory.hittingAfter_eq_top_iff.mp
            hPassageTop) (k : NNReal) bot_le
          exact le_of_not_gt hNoHit
        have hTotalLe : nu.real Set.univ ≤ c := by
          apply le_of_tendsto
            (SIntegrableFiniteVariationBridge.tendsto_cumulativeVariation_natCast_atTop
              H H.finiteVariationPart_isRightContinuous omega)
          exact Filter.Eventually.of_forall hAtMost
        calc
          eVariationOn (H.finiteVariationPart · omega) Set.univ ≤
              (FiniteVariationPath.signedMeasure
                (H.finiteVariationPart_isBoundedVariation omega)).variation
                  Set.univ :=
            FiniteVariationPath.eVariationOn_univ_le_variation_univ
              (H.finiteVariationPart_isBoundedVariation omega)
              (H.finiteVariationPart_isRightContinuous omega)
          _ = nu Set.univ := by
            dsimp only [nu]
            rw [signedMeasure_totalVariation_eq_variation]
          _ = ENNReal.ofReal (nu.real Set.univ) := by
            rw [ofReal_measureReal]
          _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hTotalLe
          _ = ENNReal.ofReal (n + 1 : Nat) := rfl
    | coe s =>
        have hPath :
            (localizingStoppedProcess H.finiteVariationPart rho · omega) =
              FiniteVariationStoppedPath.stopAt
                (H.finiteVariationPart · omega) s := by
          funext t
          rw [localizingStoppedProcess,
            MeasureTheory.stoppedProcess_indicator_comm,
            Set.indicator_of_mem hMem]
          by_cases hts : t ≤ s
          · rw [MeasureTheory.stoppedProcess_eq_of_le (by
                rw [hRho]
                exact WithTop.coe_le_coe.mpr hts)]
            simp only [FiniteVariationStoppedPath.stopAt, min_eq_left hts]
          · have hst : s ≤ t := le_of_not_ge hts
            rw [MeasureTheory.stoppedProcess_eq_of_ge (by
                rw [hRho]
                exact WithTop.coe_le_coe.mpr hst)]
            simp only [FiniteVariationStoppedPath.stopAt, min_eq_right hst,
              hRho, WithTop.untopA_eq_untop WithTop.coe_ne_top,
              WithTop.untop_coe]
        rw [hPath]
        have hStopLe : (s : WithTop NNReal) ≤ tau omega := by
          exact hRho ▸ hRhoLe omega
        have hCumulativeLe :
            SIntegrableFiniteVariationBridge.cumulativeVariation H s omega ≤ c := by
          by_cases hAtPassage : (s : WithTop NNReal) = tau omega
          · have hPassageEq :
                SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
                  H c omega = (s : WithTop NNReal) := by
              simpa only [tau, variationLocalizer, c] using hAtPassage.symm
            have hPassageNeTop :
                SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
                  H c omega ≠ ⊤ := by
              rw [hPassageEq]
              exact WithTop.coe_ne_top
            have hUntop :
                (SIntegrableFiniteVariationBridge.cumulativeVariationHittingAfter
                  H c omega).untopA = s := by
              rw [hPassageEq,
                WithTop.untopA_eq_untop WithTop.coe_ne_top,
                WithTop.untop_coe]
            have hCumulative :=
              SIntegrableFiniteVariationBridge.cumulativeVariation_untopA_le_add_leftJump
                H H.finiteVariationPart_isRightContinuous c (by positivity)
                  omega hPassageNeTop
            rw [hUntop] at hCumulative
            have hJumpRaw :
                H.finiteVariationPart s omega -
                  Function.leftLim
                    (fun t => H.finiteVariationPart t omega) s = 0 :=
              hJump s
            simpa only [hJumpRaw, abs_zero, add_zero] using hCumulative
          · apply SIntegrableFiniteVariationBridge.cumulativeVariation_le_of_lt_hittingAfter
              H c omega s
            have hStrict : (s : WithTop NNReal) < tau omega :=
              lt_of_le_of_ne hStopLe hAtPassage
            simpa only [tau, variationLocalizer, c] using hStrict
        let stoppedBoundedVariation :=
          FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (H.finiteVariationPart_isBoundedVariation omega) s
        calc
          eVariationOn
              (FiniteVariationStoppedPath.stopAt
                (H.finiteVariationPart · omega) s) Set.univ ≤
              (FiniteVariationPath.signedMeasure
                stoppedBoundedVariation).variation Set.univ :=
            FiniteVariationPath.eVariationOn_univ_le_variation_univ
              stoppedBoundedVariation
              (FiniteVariationStoppedPath.rightContinuous_stopAt
                (H.finiteVariationPart · omega)
                (H.finiteVariationPart_isRightContinuous omega) s)
          _ = (FiniteVariationPath.signedMeasure
                stoppedBoundedVariation).totalVariation Set.univ := by
            rw [signedMeasure_totalVariation_eq_variation]
          _ = ENNReal.ofReal (variationOnFromTo
                (H.finiteVariationPart · omega) Set.univ 0 s) := by
            exact FiniteVariationStoppedPath.totalVariation_univ_stopAt
              (H.finiteVariationPart · omega)
              (H.finiteVariationPart_isBoundedVariation omega)
              (H.finiteVariationPart_isRightContinuous omega) s
          _ = ENNReal.ofReal
                (SIntegrableFiniteVariationBridge.cumulativeVariation
                  H s omega) := by
            congr 1
            unfold SIntegrableFiniteVariationBridge.cumulativeVariation
            exact FiniteVariationPath.variationOnFromTo_eq_totalVariation_Ioc
              (H.finiteVariationPart_isBoundedVariation omega)
              (H.finiteVariationPart_isRightContinuous omega) bot_le
          _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hCumulativeLe
          _ = ENNReal.ofReal (n + 1 : Nat) := rfl
  · have hNotMem : omega ∉ {omega | (⊥ : WithTop NNReal) < rho omega} :=
      hPositive
    have hPath :
        (localizingStoppedProcess H.finiteVariationPart rho · omega) = 0 := by
      funext t
      rw [localizingStoppedProcess,
        MeasureTheory.stoppedProcess_indicator_comm]
      simp only [Set.indicator_of_notMem hNotMem, Pi.zero_apply]
    rw [hPath]
    have hZero : eVariationOn (0 : NNReal → Real) Set.univ = 0 := by
      rw [eVariationOn.eq_zero_iff]
      intro x _ y _
      simp only [Pi.zero_apply, edist_self]
    rw [hZero]
    exact bot_le

/-- A predictable finite-variation local martingale is indistinguishable
from its initial value.  Predictable-jump control first makes the paths
continuous; the local-martingale and cumulative-variation localizers then
turn every coordinate into a true martingale with a deterministic variation
bound, to which continuous finite-variation rigidity applies. -/
theorem indistinguishable_initial
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (D : SpecialSemimartingaleDecomposition S F mu)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ) :
    ProcessIndistinguishable mu A (fun _ omega => A 0 omega) := by
  let H : SIntegrableStrategy D :=
    zeroGainStrategy A hALocal hAPredictable hARight hABoundedVariation
  let rho : Nat → Omega → WithTop NNReal :=
    min hALocal.localSeq (variationLocalizer H)
  have hVariationLocalizer := variationLocalizer_isLocalizingSequence H
  have hRhoLocalizing :
      ProbabilityTheory.IsLocalizingSequence F rho mu := by
    change ProbabilityTheory.IsLocalizingSequence F
      (min hALocal.localSeq (variationLocalizer H)) mu
    exact hALocal.isLocalizingSequence_localSeq.min hVariationLocalizer
  have hMartingale (n : Nat) :
      Martingale (localizingStoppedProcess A (rho n)) F mu := by
    change Martingale (localizingStoppedProcess A (fun omega =>
      min (hALocal.localSeq n omega) (variationLocalizer H n omega))) F mu
    have hStopped := martingale_indicator_stopped_min_of_rightContinuous
      (hVariationLocalizer.isStoppingTime n)
      (hALocal.stoppedProcess_localSeq n) hARight
    simpa only [localizingStoppedProcess] using hStopped
  have hJump : ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump H.finiteVariationPart t omega = 0 := by
    simpa only [H, zeroGainStrategy] using
      processLeftJump_ae_eq_zero hUsual D A hALocal hAPredictable
        hARight hABoundedVariation
  have hContinuous : ∀ᵐ omega ∂mu, Continuous (A · omega) :=
    continuous_ae hUsual D A hALocal hAPredictable hARight
      hABoundedVariation
  have hLocalizedContinuous (n : Nat) :
      ∀ᵐ omega ∂mu,
        Continuous (localizingStoppedProcess A (rho n) · omega) := by
    filter_upwards [hContinuous] with omega hContinuousOmega
    exact localizingStoppedProcess_continuous A (rho n) omega
      hContinuousOmega
  have hVariation (n : Nat) : ∀ᵐ omega ∂mu,
      eVariationOn (localizingStoppedProcess A (rho n) · omega) Set.univ ≤
        ENNReal.ofReal (n + 1 : Nat) := by
    filter_upwards [hJump] with omega hJumpOmega
    have hBound :=
      eVariationOn_localizingStoppedProcess_variationLocalizer_le
        H n (rho n) (fun omega => min_le_right _ _) omega hJumpOmega
    simpa only [H, zeroGainStrategy] using hBound
  have hLocalizedEq (n : Nat) : ProcessIndistinguishable mu
      (localizingStoppedProcess A (rho n))
      (fun _ omega => localizingStoppedProcess A (rho n) 0 omega) := by
    apply ProcessIndistinguishable.of_ae_eq_on_rightDense
      (localizingStoppedProcess A (rho n))
      (fun _ omega => localizingStoppedProcess A (rho n) 0 omega)
      NNRealRightDenseSkeleton.skeleton
      NNRealRightDenseSkeleton.skeleton_rightDense
    · exact Filter.Eventually.of_forall fun omega t =>
        localizingStoppedProcess_rightContinuous A (rho n) hARight omega t
    · exact Filter.Eventually.of_forall fun _ _ =>
        continuousWithinAt_const
    · intro k
      let V : Omega → Real := fun _ => (n + 1 : Nat)
      have hVMem : MemLp V (2 : ENNReal) mu := by
        simpa only [V] using
          (memLp_const (μ := mu) (p := (2 : ENNReal))
            (((n + 1 : Nat) : Real)))
      apply martingale_ae_eq_initial_of_ae_continuous_eVariationOn_le_memLp
          (hMartingale n) (hLocalizedContinuous n) V hVMem
          (Filter.Eventually.of_forall fun _ => by positivity)
      · simpa only [V] using hVariation n
  have hLocalizedEqAll : ∀ᵐ omega ∂mu, ∀ n t,
      localizingStoppedProcess A (rho n) t omega =
        localizingStoppedProcess A (rho n) 0 omega :=
    ae_all_iff.2 hLocalizedEq
  filter_upwards [hRhoLocalizing.tendsto_top, hLocalizedEqAll] with
    omega hRhoTop hEq
  intro t
  rw [WithTop.tendsto_nhds_top_iff] at hRhoTop
  obtain ⟨n, hn⟩ := (hRhoTop t).exists
  have hPositive : (⊥ : WithTop NNReal) < rho n omega :=
    bot_lt_of_lt hn
  have hMem : omega ∈ {omega | (⊥ : WithTop NNReal) < rho n omega} :=
    hPositive
  calc
    A t omega = localizingStoppedProcess A (rho n) t omega := by
      rw [localizingStoppedProcess,
        MeasureTheory.stoppedProcess_eq_of_le hn.le,
        Set.indicator_of_mem hMem]
    _ = localizingStoppedProcess A (rho n) 0 omega := hEq n t
    _ = A 0 omega := by
      rw [localizingStoppedProcess,
        MeasureTheory.stoppedProcess_eq_of_le
          (show ((0 : NNReal) : WithTop NNReal) ≤ rho n omega from
            bot_le), Set.indicator_of_mem hMem]

/-! ## Source-free rigidity corollaries -/

/-- A predictable finite-variation local martingale is constant without
choosing a special-semimartingale decomposition for an unrelated source.
The source parameter used by the internal jump-control argument is inhabited
by the trivial zero decomposition. -/
theorem indistinguishable_initial_of_predictableFiniteVariationLocalMartingale
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ) :
    ProcessIndistinguishable mu A (fun _ omega => A 0 omega) := by
  let D0 : SpecialSemimartingaleDecomposition
      (fun _ _ => (0 : Real)) F mu := {
    martingalePart := 0
    finiteVariationPart := 0
    martingalePart_isLocalMartingale :=
      ProbabilityTheory.Locally.of_prop (martingale_zero Real F mu)
    finiteVariationPart_isPredictable := stronglyMeasurable_zero
    finiteVariationPart_isLocallyBoundedVariation := by
      intro omega a b _ _
      exact monotoneOn_const.boundedVariationOn (C := (0 : Real))
        (by simp)
    decomposition := by
      filter_upwards [] with omega t
      simp }
  exact indistinguishable_initial hUsual D0 A hALocal hAPredictable
    hARight hABoundedVariation

/-- The zero-initial form of source-free predictable finite-variation
local-martingale rigidity. -/
theorem indistinguishable_zero_of_predictableFiniteVariationLocalMartingale
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (A : Process Omega)
    (hALocal : LocalMartingale A F mu)
    (hAPredictable : IsStronglyPredictable F A)
    (hARight : forall omega t,
      ContinuousWithinAt (A · omega) (Set.Ici t) t)
    (hABoundedVariation : forall omega,
      BoundedVariationOn (A · omega) Set.univ)
    (hAZero : A 0 = 0) :
    ProcessIndistinguishable mu A (fun _ _ => 0) := by
  have hInitial :=
    indistinguishable_initial_of_predictableFiniteVariationLocalMartingale
      hUsual A hALocal hAPredictable hARight hABoundedVariation
  filter_upwards [hInitial] with omega hω
  intro t
  have ht := hω t
  change A t omega = A 0 omega at ht
  simpa only [congrFun hAZero omega, Pi.zero_apply] using ht

end PredictableFiniteVariationLocalMartingale

namespace SIntegrableStrategy

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- The centered martingale component is intrinsic to the gain graph.  Thus
two candidate records with indistinguishable gains have indistinguishable
centered martingale coordinates, even if their raw special decompositions
use different representatives. -/
theorem centeredMartingalePart_indistinguishable_of_gain
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (H K : SIntegrableStrategy D)
    (hGain : ProcessIndistinguishable mu
      H.stochasticIntegral K.stochasticIntegral) :
    ProcessIndistinguishable mu
      H.centeredMartingalePart K.centeredMartingalePart := by
  let martingaleDifference : Process Omega := fun t omega =>
    H.martingalePart t omega - K.martingalePart t omega
  let finiteVariationDifference : Process Omega := fun t omega =>
    K.finiteVariationPart t omega - H.finiteVariationPart t omega
  have hMartingaleDifferenceLocal :
      LocalMartingale martingaleDifference F mu := by
    have hRaw := H.martingalePart_isLocalMartingale.add_of_rightContinuous
      K.martingalePart_isLocalMartingale.neg
      H.martingalePart_isRightContinuous
      (fun omega t => (K.martingalePart_isRightContinuous omega t).neg)
    simpa only [martingaleDifference, sub_eq_add_neg] using hRaw
  have hFiniteVariationDifferencePredictable :
      IsStronglyPredictable F finiteVariationDifference := by
    unfold IsStronglyPredictable
    rw [show Function.uncurry finiteVariationDifference =
        Function.uncurry K.finiteVariationPart -
          Function.uncurry H.finiteVariationPart by
      funext x
      rfl]
    exact K.finiteVariationPart_isPredictable.sub
      H.finiteVariationPart_isPredictable
  have hFiniteVariationDifferenceRight : forall omega t,
      ContinuousWithinAt (finiteVariationDifference · omega)
        (Set.Ici t) t := by
    intro omega t
    exact (K.finiteVariationPart_isRightContinuous omega t).sub
      (H.finiteVariationPart_isRightContinuous omega t)
  have hFiniteVariationDifferenceBoundedVariation : forall omega,
      BoundedVariationOn (finiteVariationDifference · omega) Set.univ := by
    intro omega
    change BoundedVariationOn (fun t =>
      K.finiteVariationPart t omega + -H.finiteVariationPart t omega) Set.univ
    exact boundedVariationOn_add
      (K.finiteVariationPart_isBoundedVariation omega)
      (boundedVariationOn_neg
        (H.finiteVariationPart_isBoundedVariation omega))
  have hDifference : ProcessIndistinguishable mu
      martingaleDifference finiteVariationDifference := by
    filter_upwards [H.integral_decomposition, K.integral_decomposition,
      hGain] with omega hH hK hGainOmega
    intro t
    dsimp only [martingaleDifference, finiteVariationDifference]
    have hHt := hH t
    have hKt := hK t
    have hGainT := hGainOmega t
    linarith
  have hFiniteVariationDifferenceLocal :
      LocalMartingale finiteVariationDifference F mu :=
    LocalMartingale.congr_indistinguishable
      hMartingaleDifferenceLocal
      hFiniteVariationDifferencePredictable.stronglyAdapted
      hFiniteVariationDifferenceRight hDifference
  have hConstant :=
    PredictableFiniteVariationLocalMartingale.indistinguishable_initial
      hUsual D finiteVariationDifference hFiniteVariationDifferenceLocal
      hFiniteVariationDifferencePredictable hFiniteVariationDifferenceRight
      hFiniteVariationDifferenceBoundedVariation
  filter_upwards [hConstant, hDifference] with
    omega hConstantOmega hDifferenceOmega
  intro t
  have hAt := hConstantOmega t
  have hDifferenceAt := hDifferenceOmega t
  have hDifferenceZero := hDifferenceOmega 0
  change H.martingalePart t omega - H.martingalePart 0 omega =
    K.martingalePart t omega - K.martingalePart 0 omega
  dsimp only [finiteVariationDifference] at hAt
  dsimp only [martingaleDifference, finiteVariationDifference] at hDifferenceAt
  dsimp only [martingaleDifference, finiteVariationDifference] at hDifferenceZero
  linarith

end SIntegrableStrategy

end FTAPTheorem42
