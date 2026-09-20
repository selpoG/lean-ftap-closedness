/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.DS.Lemma48.PostStoppingTail

/-!
# The stopped martingale prefixes of Lemma 4.10

For every original strategy and passage level, Lemma 4.10 separates its
martingale part into the prefix stopped at that strategy's own first passage
and the post-passage tail controlled by Lemma 4.9.  On a finite deterministic
horizon, the actual jump envelope from Corollary 2.4 makes this stopped prefix
a true `L²` martingale with a bound uniform in the strategy index.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableProcessStoppingCalculus
open SIntegrableProcessStoppingCalculus

open SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The first passage of an original martingale component, clamped at a
positive deterministic horizon. -/
noncomputable def lemma410PrefixPassageUpTo
    (H : SIntegrableStrategy D) (c : ℝ) (T : ℝ≥0) :
    Ω → WithTop ℝ≥0 :=
  fun ω => min (lemma48FirstPassage H c ω) (T : WithTop ℝ≥0)

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma410PrefixPassageUpTo_isStoppingTime
    (H : SIntegrableStrategy D) (c : ℝ) (T : ℝ≥0) :
    IsStoppingTime ℱ (lemma410PrefixPassageUpTo H c T) :=
  (lemma48FirstPassage_isStoppingTime H c).min
    (isStoppingTime_const ℱ T)

/-- The actual strategy stopped at its martingale passage and at the
deterministic horizon. -/
noncomputable def lemma410StoppedPrefixStrategy
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D) (c : ℝ) (T : ℝ≥0) :
    SIntegrableStrategy D :=
  C.stopAtTop (lemma410PrefixPassageUpTo H c T)
    (lemma410PrefixPassageUpTo_isStoppingTime H c T) H

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The martingale component of the actual stopped strategy is the original
martingale stopped at the individual passage time. -/
theorem lemma410StoppedPrefixStrategy_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D) (c : ℝ) (T : ℝ≥0) :
    ProcessIndistinguishable μ
      (C.lemma410StoppedPrefixStrategy H c T).martingalePart
      (MeasureTheory.stoppedProcess H.martingalePart
        (lemma410PrefixPassageUpTo H c T)) :=
  C.martingalePart_stopAtTop
    (lemma410PrefixPassageUpTo H c T)
    (lemma410PrefixPassageUpTo_isStoppingTime H c T) H

omit [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- A horizon-wise jump envelope controls the stopped martingale prefix by
the passage level plus the possible overshoot. -/
theorem lemma410StoppedPrefixStrategy_martingalePart_bound
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0)
    (martingaleJump : Ω → ℝ)
    (hJumpNonnegative : ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω)
    (hJumpBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump H.martingalePart t ω| ≤ martingaleJump ω) :
    ∀ᵐ ω ∂μ, ∀ t,
      |(C.lemma410StoppedPrefixStrategy H c T).martingalePart t ω| ≤
        c + martingaleJump ω := by
  let σ := lemma410PrefixPassageUpTo H c T
  filter_upwards [C.lemma410StoppedPrefixStrategy_martingalePart H c T,
    hMartingaleZero, hJumpNonnegative, hJumpBound] with
      ω hStopped hZero hJumpNonnegativeω hJumpBoundω
  intro t
  rw [hStopped t]
  apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
    H.martingalePart hMartingaleLeft c (martingaleJump ω)
      hJumpNonnegativeω ω
  · rw [hZero, Pi.zero_apply, abs_zero]
    exact hc
  · dsimp only [σ, lemma410PrefixPassageUpTo, lemma48FirstPassage]
    exact min_le_left _ _
  · dsimp only [σ, lemma410PrefixPassageUpTo]
    exact min_le_right _ _
  · exact hJumpBoundω

/-- The stopped prefix is a true martingale. Its terminal value is in `L²`,
with norm at most the passage level plus the jump-envelope norm. -/
theorem lemma410StoppedPrefixStrategy_martingale_l2
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0)
    (martingaleJump : Ω → ℝ)
    (hJumpMem : MemLp martingaleJump (2 : ℝ≥0∞) μ)
    (hJumpNonnegative : ∀ᵐ ω ∂μ, 0 ≤ martingaleJump ω)
    (hJumpBound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump H.martingalePart t ω| ≤ martingaleJump ω) :
    let R := C.lemma410StoppedPrefixStrategy H c T
    Martingale R.martingalePart ℱ μ ∧
      MemLp (R.martingalePart T) (2 : ℝ≥0∞) μ ∧
      eLpNorm (R.martingalePart T) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal c + eLpNorm martingaleJump (2 : ℝ≥0∞) μ := by
  let R := C.lemma410StoppedPrefixStrategy H c T
  let Z : Ω → ℝ := fun ω => c + martingaleJump ω
  have hZMem : MemLp Z (2 : ℝ≥0∞) μ :=
    (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) c).add hJumpMem
  have hBound : ∀ᵐ ω ∂μ, ∀ t, |R.martingalePart t ω| ≤ Z ω :=
    C.lemma410StoppedPrefixStrategy_martingalePart_bound
      H hMartingaleLeft hMartingaleZero c hc T martingaleJump
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
        abs_of_nonneg (add_nonneg hc hJumpω)]
      exact hBoundω T
  refine ⟨hMartingale, hTerminal, ?_⟩
  calc
    eLpNorm (R.martingalePart T) (2 : ℝ≥0∞) μ ≤
        eLpNorm Z (2 : ℝ≥0∞) μ := by
      apply eLpNorm_mono_ae hTerminal.aestronglyMeasurable
      filter_upwards [hBound, hJumpNonnegative] with ω hBoundω hJumpω
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg hc hJumpω)]
      exact hBoundω T
    _ ≤ eLpNorm (fun _ : Ω => c) (2 : ℝ≥0∞) μ +
        eLpNorm martingaleJump (2 : ℝ≥0∞) μ :=
      eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal c +
        eLpNorm martingaleJump (2 : ℝ≥0∞) μ := by
      congr 1
      rw [eLpNorm_const c (by norm_num) (NeZero.ne μ),
        Real.enorm_eq_ofReal hc]
      simp

/-- Corollary 2.4 supplies the jump envelope internally. Thus every positive
finite-horizon prefix has an `L²` bound depending only on its passage level
and the common gain envelope, not on the strategy index or horizon. -/
theorem lemma410StoppedPrefixStrategy_martingale_l2_of_strategy
    (C : SIntegrableProcessStoppingCalculus D)
    (hUsual : Filtration.UsualConditions μ ℱ)
    (H : SIntegrableStrategy D)
    (hMartingaleLeft : ProcessHasLeftLimits H.martingalePart)
    (hMartingaleZero : H.martingalePart 0 =ᵐ[μ] 0)
    (gainEnvelope : Ω → ℝ)
    (hGainEnvelope : MemLp gainEnvelope (2 : ℝ≥0∞) μ)
    (hGainBound : ∀ᵐ ω ∂μ, ∀ t,
      |H.stochasticIntegral t ω| ≤ gainEnvelope ω)
    (c : ℝ) (hc : 0 ≤ c) {T : ℝ≥0} (hT : 0 < T) :
    let R := C.lemma410StoppedPrefixStrategy H c T
    Martingale R.martingalePart ℱ μ ∧
      MemLp (R.martingalePart T) (2 : ℝ≥0∞) μ ∧
      eLpNorm (R.martingalePart T) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal c +
          6 * eLpNorm gainEnvelope (2 : ℝ≥0∞) μ := by
  obtain ⟨martingaleJump, hJumpMem, hJumpNonnegative,
      hJumpBound, hJumpNorm⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual H hMartingaleLeft
      gainEnvelope hGainEnvelope hGainBound hT
  have hStopped := C.lemma410StoppedPrefixStrategy_martingale_l2
    H hMartingaleLeft hMartingaleZero c hc T martingaleJump
      hJumpMem hJumpNonnegative hJumpBound
  exact ⟨hStopped.1, hStopped.2.1,
    hStopped.2.2.trans (add_le_add le_rfl hJumpNorm)⟩

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
