/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.Martingale.Basic.DominatedLocalMartingale

/-! # Jump envelopes and stopped tail martingales

A common passage threshold gives small L² jump envelopes for convex tails.
Closed stopping then gives a true martingale and a terminal L² bound. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Above one common passage threshold, every finite convex combination of
post-passage tails has an `L²` martingale-jump envelope of arbitrarily small
norm on every positive deterministic horizon.  The threshold is independent
of the weights, the size of the finite combination, and the horizon. -/
theorem exists_lemma49TailMartingaleJumpEnvelope_threshold
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : ℕ → SIntegrableStrategy D) (q : Ω → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) μ)
    (hMartingaleLeft : ∀ i,
      ProcessHasLeftLimits (H i).martingalePart)
    (hGainBound : ∀ i, ∀ᵐ ω ∂μ, ∀ t,
      |(H i).stochasticIntegral t ω| ≤ ‖q ω‖)
    (hMaximal : ∀ η : ℝ, 0 < η →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ i,
        μ {ω | ENNReal.ofReal R <
          ⨆ t : ℝ≥0,
            ENNReal.ofReal |(H i).martingalePart t ω|} ≤
              ENNReal.ofReal η)
    (η : ℝ) (hη : 0 < η) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧
      ∀ (weight : ℕ → ℝ) (n : ℕ) (c : ℝ), c₀ ≤ c →
        (∀ i ∈ Finset.range n, 0 ≤ weight i) →
        (∑ i ∈ Finset.range n, weight i = 1) →
        ∀ T : ℝ≥0, 0 < T →
          ∃ martingaleJump : Ω → ℝ,
            MemLp martingaleJump (2 : ℝ≥0∞) μ ∧
            (∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω) ∧
            (∀ᵐ ω ∂μ, ∀ t, t ≤ T →
              |processLeftJump
                (C.lemma48TailConvexStrategy H weight n c).martingalePart
                  t ω| ≤ martingaleJump ω) ∧
            eLpNorm martingaleJump (2 : ℝ≥0∞) μ ≤
              ENNReal.ofReal η := by
  obtain ⟨c₀, hc₀, hThreshold⟩ :=
    exists_lemma48PassageThreshold_with_probability_and_indicatorNorm
      H q hq 1 (η / 12) (by norm_num) (by positivity) hMaximal
  refine ⟨c₀, hc₀, ?_⟩
  intro weight n c hc hWeight hWeightSum T hT
  let L := C.lemma48TailConvexStrategy H weight n c
  let G := lemma48TailGainEnvelope H weight n c q
  have hGMem : MemLp G (2 : ℝ≥0∞) μ :=
    lemma48TailGainEnvelope_memLp H weight n c q hq
  have hGBound : ∀ᵐ ω ∂μ, ∀ t,
      |L.stochasticIntegral t ω| ≤ G ω :=
    C.lemma48TailConvexStrategy_gain_le_lemma48TailGainEnvelope
      H weight n c q hWeight hGainBound
  have hGNorm : eLpNorm G (2 : ℝ≥0∞) μ ≤
      2 * ENNReal.ofReal (η / 12) :=
    eLpNorm_lemma48TailGainEnvelope_le H weight n c q hq
      hWeight hWeightSum fun i hi => (hThreshold c hc).2 i
  obtain ⟨martingaleJump, hJumpMem, hJumpNonnegative,
      hJumpBound, hJumpNorm⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual L
      (C.lemma48TailConvexStrategy_martingalePart_hasLeftLimits
        H weight n c hMartingaleLeft)
      G hGMem hGBound hT
  refine ⟨martingaleJump, hJumpMem, hJumpNonnegative, hJumpBound,
    hJumpNorm.trans ?_⟩
  calc
    6 * eLpNorm G (2 : ℝ≥0∞) μ ≤
        6 * (2 * ENNReal.ofReal (η / 12)) := by gcongr
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      congr 1
      ring

/-- The tail-martingale passage, clamped at a deterministic horizon. -/
noncomputable def lemma49TailMartingalePassageUpTo
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (T : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => min (C.lemma48TailMartingalePassage H weight n c a ω)
    (T : WithTop ℝ≥0)

theorem lemma49TailMartingalePassageUpTo_isStoppingTime
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (T : ℝ≥0) :
    IsStoppingTime ℱ
      (C.lemma49TailMartingalePassageUpTo H weight n c a T) :=
  (C.lemma48TailMartingalePassage_isStoppingTime H weight n c a).min
    (isStoppingTime_const ℱ T)

/-- The actual convex tail strategy stopped at its martingale passage and
at the deterministic horizon. -/
noncomputable def lemma49StoppedTailConvexStrategy
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (T : ℝ≥0) : SIntegrableStrategy D :=
  C.stopAtTop (C.lemma49TailMartingalePassageUpTo H weight n c a T)
    (C.lemma49TailMartingalePassageUpTo_isStoppingTime
      H weight n c a T)
    (C.lemma48TailConvexStrategy H weight n c)

/-- The stopped actual martingale component is the stopped process of the
convex tail martingale. -/
theorem lemma49StoppedTailConvexStrategy_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (T : ℝ≥0) :
    ProcessIndistinguishable μ
      (C.lemma49StoppedTailConvexStrategy
        H weight n c a T).martingalePart
      (MeasureTheory.stoppedProcess
        (C.lemma48TailConvexStrategy H weight n c).martingalePart
        (C.lemma49TailMartingalePassageUpTo H weight n c a T)) :=
  C.martingalePart_stopAtTop
    (C.lemma49TailMartingalePassageUpTo H weight n c a T)
    (C.lemma49TailMartingalePassageUpTo_isStoppingTime
      H weight n c a T)
    (C.lemma48TailConvexStrategy H weight n c)

/-- A horizon-wise jump envelope controls the stopped tail martingale by the
passage level plus its possible final jump. -/
theorem lemma49StoppedTailConvexStrategy_martingalePart_bound
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (ha : 0 ≤ a) (T : ℝ≥0)
    (hMartingaleLeft : ∀ i,
      ProcessHasLeftLimits (H i).martingalePart)
    (martingaleJump : Ω → ℝ)
    (hJumpNonnegative : ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω)
    (hJumpBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump
        (C.lemma48TailConvexStrategy H weight n c).martingalePart t ω| ≤
          martingaleJump ω) :
    ∀ᵐ ω ∂μ, ∀ t,
      |(C.lemma49StoppedTailConvexStrategy
        H weight n c a T).martingalePart t ω| ≤
          a + martingaleJump ω := by
  let L := C.lemma48TailConvexStrategy H weight n c
  let σ := C.lemma49TailMartingalePassageUpTo H weight n c a T
  filter_upwards [C.lemma49StoppedTailConvexStrategy_martingalePart
      H weight n c a T,
    C.lemma48TailConvexStrategy_martingalePart_zero H weight n c,
    hJumpNonnegative, hJumpBound] with ω hStopped hZero hJumpNonnegativeω
      hJumpBoundω
  intro t
  rw [hStopped t]
  apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
    L.martingalePart
    (C.lemma48TailConvexStrategy_martingalePart_hasLeftLimits
      H weight n c hMartingaleLeft)
    a (martingaleJump ω) hJumpNonnegativeω ω
  · rw [hZero, Pi.zero_apply, abs_zero]
    exact ha
  · dsimp only [σ, lemma49TailMartingalePassageUpTo,
      lemma48TailMartingalePassage, lemma48FirstPassage]
    exact min_le_left _ _
  · dsimp only [σ, lemma49TailMartingalePassageUpTo]
    exact min_le_right _ _
  · exact hJumpBoundω

/-- The first-passage stopped tail is a true martingale.  Its terminal value
is square-integrable and has `L²` norm at most the passage level plus the
jump-envelope norm. -/
theorem lemma49StoppedTailConvexStrategy_martingale_l2
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c a : ℝ) (ha : 0 ≤ a) (T : ℝ≥0)
    (hMartingaleLeft : ∀ i,
      ProcessHasLeftLimits (H i).martingalePart)
    (martingaleJump : Ω → ℝ)
    (hJumpMem : MemLp martingaleJump (2 : ℝ≥0∞) μ)
    (hJumpNonnegative : ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω)
    (hJumpBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump
        (C.lemma48TailConvexStrategy H weight n c).martingalePart t ω| ≤
          martingaleJump ω) :
    let R := C.lemma49StoppedTailConvexStrategy H weight n c a T
    Martingale R.martingalePart ℱ μ ∧
      MemLp (R.martingalePart T) (2 : ℝ≥0∞) μ ∧
      eLpNorm (R.martingalePart T) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal a +
          eLpNorm martingaleJump (2 : ℝ≥0∞) μ := by
  let R := C.lemma49StoppedTailConvexStrategy H weight n c a T
  let Z : Ω → ℝ := fun ω => a + martingaleJump ω
  have hZMem : MemLp Z (2 : ℝ≥0∞) μ :=
    (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) a).add hJumpMem
  have hBound : ∀ᵐ ω ∂μ, ∀ t, |R.martingalePart t ω| ≤ Z ω :=
    C.lemma49StoppedTailConvexStrategy_martingalePart_bound
      H weight n c a ha T hMartingaleLeft martingaleJump
        hJumpNonnegative hJumpBound
  have hMartingale : Martingale R.martingalePart ℱ μ :=
    R.martingalePart_isMartingale_of_integrable_bound Z
      (hZMem.integrable one_le_two) hBound
  have hTerminal : MemLp (R.martingalePart T) (2 : ℝ≥0∞) μ := by
    apply hZMem.of_le
    · exact ((hMartingale.stronglyMeasurable T).mono
        (ℱ.le T)).aestronglyMeasurable
    · filter_upwards [hBound, hJumpNonnegative] with ω hBoundω hJumpω
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg ha hJumpω)]
      exact hBoundω T
  refine ⟨hMartingale, hTerminal, ?_⟩
  calc
    eLpNorm (R.martingalePart T) (2 : ℝ≥0∞) μ ≤
        eLpNorm Z (2 : ℝ≥0∞) μ := by
      apply eLpNorm_mono_ae hTerminal.aestronglyMeasurable
      filter_upwards [hBound, hJumpNonnegative] with ω hBoundω hJumpω
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg ha hJumpω)]
      exact hBoundω T
    _ ≤ eLpNorm (fun _ : Ω => a) (2 : ℝ≥0∞) μ +
        eLpNorm martingaleJump (2 : ℝ≥0∞) μ :=
      eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal a +
        eLpNorm martingaleJump (2 : ℝ≥0∞) μ := by
      congr 1
      rw [eLpNorm_const a (by norm_num) (NeZero.ne μ),
        Real.enorm_eq_ofReal ha]
      simp

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
