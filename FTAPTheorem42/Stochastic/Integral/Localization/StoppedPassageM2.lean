/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy

/-!
# Square-integrable martingales below a passage

An arbitrary stopping time below both an absolute martingale passage and a
positive deterministic horizon inherits the same `M²` estimate as the
canonical passage prefix.  Corollary 2.4 supplies the possible overshoot at
the stopping time, while the passage level controls the path before it.

This formulation is independent of how the smaller stopping time was
constructed.  In particular, it can be applied after intersecting several
source and output localizers.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableStoppingCalculus

open SIntegrableProcessStoppingCalculus

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

omit [F.IsRightContinuous] in
/-- A stop below a martingale passage and a deterministic horizon is a true
`M²` martingale.  Its terminal norm is bounded by the passage level plus the
norm of a supplied left-jump envelope. -/
theorem stoppedProcess_martingale_l2_of_memLpJumpBound_of_le_hitting
    (H : SIntegrableStrategy D)
    (hLeft : ProcessHasLeftLimits H.martingalePart)
    (hZero : H.martingalePart 0 =ᵐ[mu] 0)
    (c : Real) (hc : 0 <= c)
    (sigma : Omega -> WithTop NNReal) (hSigma : IsStoppingTime F sigma)
    {T : NNReal}
    (hSigmaHit : forall omega,
      sigma omega <= absoluteStrictHittingAfter H.martingalePart c omega)
    (hSigmaT : forall omega, sigma omega <= (T : WithTop NNReal))
    (jump : Omega -> Real)
    (hJumpMem : MemLp jump (2 : ENNReal) mu)
    (hJumpNonnegative : ∀ᵐ omega ∂mu, 0 <= jump omega)
    (hJumpBound : ∀ᵐ omega ∂mu, forall t, t <= T ->
      abs (processLeftJump H.martingalePart t omega) <= jump omega) :
    let R := MeasureTheory.stoppedProcess H.martingalePart sigma
    Martingale R F mu ∧
      MemLp (R T) (2 : ENNReal) mu ∧
      eLpNorm (R T) (2 : ENNReal) mu <=
        ENNReal.ofReal c + eLpNorm jump (2 : ENNReal) mu := by
  let R := MeasureTheory.stoppedProcess H.martingalePart sigma
  let Z : Omega -> Real := fun omega => c + jump omega
  have hInitial : ∀ᵐ omega ∂mu, abs (H.martingalePart 0 omega) <= c := by
    filter_upwards [hZero] with omega hZeroOmega
    rw [hZeroOmega, Pi.zero_apply, abs_zero]
    exact hc
  have hBound : ∀ᵐ omega ∂mu, forall t,
      abs (R t omega) <= Z omega := by
    filter_upwards [hJumpNonnegative, hInitial, hJumpBound] with omega
        hJumpOmega hInitialOmega hJumpBoundOmega
    intro t
    exact abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
      H.martingalePart hLeft c (jump omega) hJumpOmega omega hInitialOmega
        sigma (hSigmaHit omega) T (hSigmaT omega) hJumpBoundOmega t
  have hZMem : MemLp Z (2 : ENNReal) mu :=
    (memLp_const (μ := mu) (p := (2 : ENNReal)) c).add hJumpMem
  have hMartingale : Martingale R F mu :=
    (H.martingalePart_isLocalMartingale.stoppedProcess_of_rightContinuous
      H.martingalePart_isRightContinuous hSigma).martingale_of_integrable_bound
      (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        H.martingalePart_isStronglyAdapted hSigma H.martingalePart_isRightContinuous)
      Z (hZMem.integrable one_le_two) hBound
  have hTerminal : MemLp (R T) (2 : ENNReal) mu := by
    apply hZMem.of_le
    · exact ((hMartingale.stronglyMeasurable T).mono
        (F.le T)).aestronglyMeasurable
    · filter_upwards [hBound, hJumpNonnegative] with omega hBoundOmega
          hJumpOmega
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg hc hJumpOmega)]
      exact hBoundOmega T
  refine ⟨hMartingale, hTerminal, ?_⟩
  calc
    eLpNorm (R T) (2 : ENNReal) mu <=
        eLpNorm Z (2 : ENNReal) mu := by
      apply eLpNorm_mono_ae hTerminal.aestronglyMeasurable
      filter_upwards [hBound, hJumpNonnegative] with omega hBoundOmega
          hJumpOmega
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg hc hJumpOmega)]
      exact hBoundOmega T
    _ <= eLpNorm (fun _ : Omega => c) (2 : ENNReal) mu +
        eLpNorm jump (2 : ENNReal) mu :=
      eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal c + eLpNorm jump (2 : ENNReal) mu := by
      congr 1
      rw [eLpNorm_const c (by norm_num) (NeZero.ne mu),
        Real.enorm_eq_ofReal hc]
      simp

/-- Corollary 2.4 supplies the jump envelope internally.  Hence every stop
below the level-`c` passage and the positive horizon `T` satisfies the same
uniform `M²` estimate as the canonical own-passage prefix. -/
theorem stoppedProcess_martingale_l2_of_le_hitting_of_strategy
    (hUsual : Filtration.UsualConditions mu F)
    (H : SIntegrableStrategy D)
    (hLeft : ProcessHasLeftLimits H.martingalePart)
    (hZero : H.martingalePart 0 =ᵐ[mu] 0)
    (gainEnvelope : Omega -> Real)
    (hGainEnvelope : MemLp gainEnvelope (2 : ENNReal) mu)
    (hGainBound : ∀ᵐ omega ∂mu, forall t,
      abs (H.stochasticIntegral t omega) <= gainEnvelope omega)
    (c : Real) (hc : 0 <= c)
    (sigma : Omega -> WithTop NNReal) (hSigma : IsStoppingTime F sigma)
    {T : NNReal} (hT : 0 < T)
    (hSigmaHit : forall omega,
      sigma omega <= absoluteStrictHittingAfter H.martingalePart c omega)
    (hSigmaT : forall omega, sigma omega <= (T : WithTop NNReal)) :
    let R := MeasureTheory.stoppedProcess H.martingalePart sigma
    Martingale R F mu ∧
      MemLp (R T) (2 : ENNReal) mu ∧
      eLpNorm (R T) (2 : ENNReal) mu <=
        ENNReal.ofReal c +
          6 * eLpNorm gainEnvelope (2 : ENNReal) mu := by
  obtain ⟨jump, hJumpMem, hJumpNonnegative, hJumpBound, hJumpNorm⟩ :=
    lemma47MartingaleJumpEnvelope_of_strategy hUsual H hLeft
      gainEnvelope hGainEnvelope hGainBound hT
  have hStopped := stoppedProcess_martingale_l2_of_memLpJumpBound_of_le_hitting
    H hLeft hZero c hc sigma hSigma hSigmaHit hSigmaT jump hJumpMem
      hJumpNonnegative hJumpBound
  exact ⟨hStopped.1, hStopped.2.1,
    hStopped.2.2.trans (add_le_add le_rfl hJumpNorm)⟩

end SIntegrableStoppingCalculus

end FTAPTheorem42
