/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.CumulativeVariationAnnouncedJumpControl
import FTAPTheorem42.Foundations.ProcessEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma47.StoppedMartingale

/-!
# Martingale-jump envelopes for Lemma 4.7

The whole-gain envelope controls its jumps by twice that envelope.  The
predictable-graph Doob envelope controls the finite-variation jumps.  Their
sum therefore gives the `L²` martingale-jump envelope needed at the first
rescaling in Lemma 4.7.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [IsFiniteMeasure μ] in
/-- Combine the gain envelope with an already constructed simultaneous
finite-variation jump envelope. -/
theorem martingaleJumpEnvelope_memLp_and_bound_left_ae_of_finiteVariation
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hFiniteVariation :
      MemLp (countableLeftJumpEnvelope H.finiteVariationPart τ)
          (2 : ℝ≥0∞) μ ∧
        ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
          |processLeftJump H.finiteVariationPart t ω| ≤
            countableLeftJumpEnvelope H.finiteVariationPart τ ω) :
    MemLp (fun ω => 2 * gainEnvelope ω +
        countableLeftJumpEnvelope H.finiteVariationPart τ ω)
      (2 : ℝ≥0∞) μ ∧
      ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
        |processLeftJump H.martingalePart t ω| ≤
          2 * gainEnvelope ω +
            countableLeftJumpEnvelope H.finiteVariationPart τ ω := by
  constructor
  · exact (hGainEnvelope.const_mul 2).add hFiniteVariation.1
  · filter_upwards [H.abs_processLeftJump_stochasticIntegral_le
        hMartingaleLeft gainEnvelope hGainBound,
      H.processLeftJump_eq_components hMartingaleLeft,
      hFiniteVariation.2] with ω hGainJump hComponents hFiniteVariationJump
    intro t ht
    have hComponent : processLeftJump H.martingalePart t ω =
        processLeftJump H.stochasticIntegral t ω -
          processLeftJump H.finiteVariationPart t ω := by
      linarith [hComponents t]
    rw [hComponent]
    exact (abs_sub _ _).trans
      (add_le_add (hGainJump t) (hFiniteVariationJump t ht))

end SIntegrableStrategy

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Announced jump-crossing localization for Lemma 4.7

This is the vertical consumer from announced cumulative-variation jump
graphs to the first rescaled true martingale.  The main endpoint samples the
actual stochastic-integral decomposition at predictable completed
jump-crossing times.  Its final positive-horizon specialization constructs
the required ordinary announcements from graph predictability and the usual
conditions.
-/

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

open CumulativeVariationJumpEnumeration
open FactorialChronologicalGrid

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The actual decomposition and an announced jump-crossing family construct
one simultaneous martingale-jump envelope.  Its `L²` norm is at most six
times the norm of the supplied gain envelope. -/
theorem lemma47MartingaleJumpEnvelope_of_jumpCrossingAnnouncements
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    (T : ℝ≥0)
    (announcement : ∀ n, StoppingTimeAnnouncement ℱ
      (CumulativeVariationJumpEnumeration.jumpCrossingTime H T n)) :
    ∃ martingaleJump : Ω → ℝ,
      MemLp martingaleJump (2 : ℝ≥0∞) μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω) ∧
      (∀ᵐ ω ∂μ, ∀ t, t ≤ T →
        |processLeftJump H.martingalePart t ω| ≤ martingaleJump ω) ∧
      eLpNorm martingaleJump (2 : ℝ≥0∞) μ ≤
        6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
  let terminalEnvelope : Ω → ℝ :=
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      H.stochasticIntegral (T + 1)
  let J : Ω → ℝ := fun ω ↦ 2 * terminalEnvelope ω
  let martingaleJump : Ω → ℝ := fun ω ↦
    2 * gainEnvelope ω +
      countableLeftJumpEnvelope H.finiteVariationPart
        (CumulativeVariationJumpEnumeration.jumpCrossingTime H T) ω
  have hGainBoundUpTo : ∀ᵐ ω ∂μ, ∀ t, t ≤ T + 1 →
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω := by
    filter_upwards [hGainBound] with ω hω
    intro t _
    exact hω t
  have hTerminalEnvelope : MemLp terminalEnvelope (2 : ℝ≥0∞) μ := by
    exact FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_memLp_of_bound
      H.stochasticIntegral_isStronglyAdapted (T + 1) hGainEnvelope
      hGainBoundUpTo
  have hTerminalNorm :
      eLpNorm terminalEnvelope (2 : ℝ≥0∞) μ ≤
        eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
    apply eLpNorm_mono_ae hTerminalEnvelope.aestronglyMeasurable
    filter_upwards [hGainBound] with ω hω
    have hGainNonnegative : 0 ≤ gainEnvelope ω :=
      (abs_nonneg (H.stochasticIntegral 0 ω)).trans (hω 0)
    simp only [Real.norm_eq_abs]
    have hTerminalNonnegative : 0 ≤ terminalEnvelope ω :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg hTerminalNonnegative,
      abs_of_nonneg hGainNonnegative]
    exact FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_le_of_bound
      H.stochasticIntegral (T + 1) fun t _ ↦ hω t
  have hJ : MemLp J (2 : ℝ≥0∞) μ := by
    exact hTerminalEnvelope.const_mul 2
  have hJNorm : eLpNorm J (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
    calc
      eLpNorm J (2 : ℝ≥0∞) μ =
          2 * eLpNorm terminalEnvelope (2 : ℝ≥0∞) μ := by
        rw [show J = (2 : ℝ) • terminalEnvelope by
          funext ω
          simp only [J, Pi.smul_apply, smul_eq_mul]]
        rw [eLpNorm_const_smul,
          Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
        gcongr
  have hdecompAll := H.processLeftJump_eq_components hMartingaleLeft
  have hdecomp : ∀ n,
      (fun ω ↦ processLeftJump H.stochasticIntegral
        (CumulativeVariationJumpEnumeration.jumpCrossingTime H T n ω) ω) =ᵐ[μ]
        fun ω ↦ processLeftJump H.martingalePart
          (CumulativeVariationJumpEnumeration.jumpCrossingTime H T n ω) ω +
          processLeftJump H.finiteVariationPart
            (CumulativeVariationJumpEnumeration.jumpCrossingTime H T n ω) ω := by
    intro n
    filter_upwards [hdecompAll] with ω hω
    exact hω _
  have hTerminalEnvelopeBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T + 1 →
      |H.stochasticIntegral t ω| ≤ terminalEnvelope ω := by
    exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_ae
      H.stochasticIntegral_isRightContinuous (T + 1) hGainBoundUpTo
  have hJumpBoundAll :=
    H.abs_processLeftJump_stochasticIntegral_le_upTo
      hMartingaleLeft terminalEnvelope (T + 1) hTerminalEnvelopeBound
  have hJumpBound : ∀ n, (fun ω ↦
      |processLeftJump H.stochasticIntegral
        (CumulativeVariationJumpEnumeration.jumpCrossingTime H T n ω) ω|) ≤ᵐ[μ]
        J := by
    intro n
    filter_upwards [hJumpBoundAll] with ω hω
    exact hω _
      (CumulativeVariationJumpEnumeration.jumpCrossingTime_le H T n ω)
  have hFiniteVariation :=
    LocalMartingale.finiteVariationLeftJumpEnvelope_with_norm_of_jumpCrossingAnnouncements
      H H.finiteVariationPart_isRightContinuous
      H.martingalePart_isLocalMartingale J T
      H.martingalePart_isRightContinuous hMartingaleLeft announcement
      hJ hdecomp hJumpBound
  have hMartingaleJump :=
    H.martingaleJumpEnvelope_memLp_and_bound_left_ae_of_finiteVariation
      hMartingaleLeft gainEnvelope hGainEnvelope hGainBound T
      (CumulativeVariationJumpEnumeration.jumpCrossingTime H T)
      hFiniteVariation.1
  have hMartingaleJumpNonnegative : ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω := by
    filter_upwards [hGainBound] with ω hGainBoundω
    have hGainNonnegative : 0 ≤ gainEnvelope ω :=
      (abs_nonneg (H.stochasticIntegral 0 ω)).trans (hGainBoundω 0)
    exact add_nonneg (mul_nonneg (by norm_num) hGainNonnegative)
      (countableLeftJumpEnvelope_nonnegative
        H.finiteVariationPart
        (CumulativeVariationJumpEnumeration.jumpCrossingTime H T) ω)
  have hTwoGainNorm :
      eLpNorm (fun ω ↦ 2 * gainEnvelope ω) (2 : ℝ≥0∞) μ =
        2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
    rw [show (fun ω ↦ 2 * gainEnvelope ω) =
        (2 : ℝ) • gainEnvelope by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]]
    rw [eLpNorm_const_smul,
      Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hMartingaleJumpNorm :
      eLpNorm martingaleJump (2 : ℝ≥0∞) μ ≤
        6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
    calc
      eLpNorm martingaleJump (2 : ℝ≥0∞) μ ≤
          eLpNorm (fun ω ↦ 2 * gainEnvelope ω) (2 : ℝ≥0∞) μ +
            eLpNorm (countableLeftJumpEnvelope H.finiteVariationPart
              (CumulativeVariationJumpEnumeration.jumpCrossingTime H T))
              (2 : ℝ≥0∞) μ := by
        exact eLpNorm_add_le (by norm_num)
      _ = 2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ +
          eLpNorm (countableLeftJumpEnvelope H.finiteVariationPart
            (CumulativeVariationJumpEnumeration.jumpCrossingTime H T))
            (2 : ℝ≥0∞) μ := by
        rw [hTwoGainNorm]
      _ ≤ 2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ +
          2 * eLpNorm J (2 : ℝ≥0∞) μ :=
        add_le_add le_rfl hFiniteVariation.2
      _ ≤ 2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ +
          2 * (2 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ) :=
        add_le_add le_rfl (by gcongr)
      _ = 6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by ring
  exact ⟨martingaleJump, hMartingaleJump.1,
    hMartingaleJumpNonnegative, hMartingaleJump.2,
    hMartingaleJumpNorm⟩

/-- Under the usual conditions, the predictable jump-crossing announcements
are generated internally, so the quantitative martingale-jump envelope is an
actual-strategy output. -/
theorem lemma47MartingaleJumpEnvelope_of_strategy
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {T : ℝ≥0} (hT : 0 < T) :
    ∃ martingaleJump : Ω → ℝ,
      MemLp martingaleJump (2 : ℝ≥0∞) μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω) ∧
      (∀ᵐ ω ∂μ, ∀ t, t ≤ T →
        |processLeftJump H.martingalePart t ω| ≤ martingaleJump ω) ∧
      eLpNorm martingaleJump (2 : ℝ≥0∞) μ ≤
        6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
  apply lemma47MartingaleJumpEnvelope_of_jumpCrossingAnnouncements
    H hMartingaleLeft gainEnvelope hGainEnvelope hGainBound T
  intro n
  exact CumulativeVariationJumpEnumeration.jumpCrossingTime_announcement
    hUsual H H.finiteVariationPart_isRightContinuous hT n

/-- The actual first localization for a positive finite horizon.  The
announcements of the completed jump-crossing times are constructed from
their predictable graphs, rather than supplied as an external hypothesis. -/
theorem lemma47RescaleAndStopUpTo_martingale_of_strategy
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (scale martingaleLevel gainLevel : ℝ)
    (hMartingaleInitial :
      ∀ᵐ ω ∂μ, |H.martingalePart 0 ω| ≤ martingaleLevel)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    {T : ℝ≥0} (hT : 0 < T) :
    Martingale
      (C.lemma47RescaleAndStopUpTo H scale martingaleLevel
        gainLevel T).martingalePart ℱ μ := by
  obtain ⟨martingaleJump, hJumpMem, hJumpNonnegative,
      hJumpBound, _⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual H hMartingaleLeft
      gainEnvelope hGainEnvelope hGainBound hT
  exact C.lemma47RescaleAndStopUpTo_martingale_of_integrableJumpBound
    H hMartingaleLeft scale martingaleLevel gainLevel T martingaleJump
    (hJumpMem.integrable one_le_two) hJumpNonnegative
    hMartingaleInitial hJumpBound

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
