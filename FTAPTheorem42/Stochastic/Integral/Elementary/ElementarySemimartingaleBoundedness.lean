/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Semimartingale
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementaryPredictableIntegrand
import FTAPTheorem42.Foundations.EquivalentMeasureTransfer

/-!
# Semimartingales as elementary good integrators

For the fixed real-valued, nonnegative-real-time setting of Theorem 4.2, we
use the Bichteler--Dellacherie good-integrator formulation.  A sequence of
predictable elementary integrands which converges uniformly to zero must have
its elementary gains converge to zero in probability at every deterministic
time.  Measurability of those gains is recorded explicitly.

This definition only uses the pathwise elementary integral already available
in the repository.  It does not assume a stochastic integral for arbitrary
predictable processes.  The main theorem proves the measure-change fact needed
by the tilted-measure argument: the predicate is invariant under equivalent
finite measures.
-/

namespace FTAPTheorem42

open Filter MeasureTheory
open scoped NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace IsSemimartingale

/-- The elementary good-integrator definition of a semimartingale is
invariant under mutually absolutely continuous finite measures. -/
theorem iff_of_mutuallyAbsolutelyContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu nu : Measure Omega} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hMuNu : mu ≪ nu) (hNuMu : nu ≪ mu) :
    IsSemimartingale S F mu ↔ IsSemimartingale S F nu := by
  constructor
  · rintro ⟨hMeasMu, hGoodMu⟩
    refine ⟨fun H T => (hMeasMu H T).mono_ac hNuMu, ?_⟩
    intro H hUniform T
    exact
      (EquivalentMeasureTransfer.tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
        hMuNu hNuMu (fun n => hMeasMu (H n) T)).mp
          (hGoodMu H hUniform T)
  · rintro ⟨hMeasNu, hGoodNu⟩
    refine ⟨fun H T => (hMeasNu H T).mono_ac hMuNu, ?_⟩
    intro H hUniform T
    exact
      (EquivalentMeasureTransfer.tendstoInMeasure_iff_of_mutuallyAbsolutelyContinuous
        hMuNu hNuMu
          (fun n => (hMeasNu (H n) T).mono_ac hMuNu)).mpr
            (hGoodNu H hUniform T)

end IsSemimartingale

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Fixed-time boundedness of elementary semimartingale integrals

The good-integrator definition has its first uniform consequence here.  At a
fixed deterministic time, the gains of all predictable elementary
integrands bounded by one form a set bounded in probability.  Otherwise one
may choose gains escaping at linearly growing thresholds and scale the
corresponding integrands by the reciprocal threshold.  The scaled integrands
converge uniformly to zero, while their gains retain a fixed positive tail,
contradicting the semimartingale property.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Fixed-time elementary gains whose predictable integrands are bounded in
absolute value by one. -/
def UnitBoundedElementaryGainSet
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (T : NNReal) : Set (Omega → Real) :=
  {g | ∃ H : PredictableElementaryStrategy F,
    (∀ t omega, |H.integrand t omega| ≤ 1) ∧
      g = ElementaryStrategy.gain S H.toElementary T}

namespace IsSemimartingale

/-- A semimartingale's fixed-time elementary integrals are uniformly bounded
in probability when their integrands are uniformly bounded by one. -/
theorem claimSetBoundedInProbability_unitBoundedElementaryGainSet
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hS : IsSemimartingale S F mu) (T : NNReal) :
    ClaimSetBoundedInProbability mu
      (UnitBoundedElementaryGainSet S F T) := by
  by_contra hnot
  obtain ⟨epsilon, hepsilon, gain, hgainMem, hgainTail⟩ :=
    (ClaimSetUnboundedInProbabilityWitness.of_not_bounded hnot).exists_sequence_at
      (fun n => (n + 1 : Nat)) (fun n => by positivity)
  choose H hHBound hgain using fun n => hgainMem n
  let scale : Nat → Real := fun n => ((n + 1 : Nat) : Real)⁻¹
  have hscalePositive : ∀ n, 0 < scale n := fun n => by
    dsimp [scale]
    positivity
  let K : Nat → PredictableElementaryStrategy F := fun n =>
    (H n).posSMul (scale n) (hscalePositive n)
  have hKUniform : ElementaryIntegrandsTendstoUniformlyZero K := by
    intro delta hdelta
    have hscale : Tendsto scale atTop (nhds 0) := by
      simpa [scale, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    filter_upwards [((tendsto_order.1 hscale).2 delta hdelta)] with n hn
    intro t omega
    rw [show K n = (H n).posSMul (scale n) (hscalePositive n) by rfl,
      PredictableElementaryStrategy.integrand_posSMul]
    rw [abs_mul, abs_of_pos (hscalePositive n)]
    exact
      (mul_le_of_le_one_right (hscalePositive n).le
        (hHBound n t omega)).trans hn.le
  have hConverges := hS.2 K hKUniform T
  have hMeasureZero : Tendsto
      (fun n => mu {omega |
        (1 : Real) ≤
          ‖ElementaryStrategy.gain S (K n).toElementary T omega - 0‖})
      atTop (nhds 0) :=
    (tendstoInMeasure_iff_norm.mp hConverges) 1 zero_lt_one
  have hepsilonENN : 0 < ENNReal.ofReal epsilon :=
    ENNReal.ofReal_pos.mpr hepsilon
  have hEventuallySmall : ∀ᶠ n in atTop,
      mu {omega |
        (1 : Real) ≤
          ‖ElementaryStrategy.gain S (K n).toElementary T omega - 0‖} <
        ENNReal.ofReal epsilon :=
    ((tendsto_order.1 hMeasureZero).2 _ hepsilonENN)
  obtain ⟨n, hn⟩ := hEventuallySmall.exists
  have hsubset :
      {omega | ((n + 1 : Nat) : Real) < |gain n omega|} ⊆
        {omega | (1 : Real) ≤
          ‖ElementaryStrategy.gain S (K n).toElementary T omega - 0‖} := by
    intro omega homega
    change (1 : Real) ≤
      ‖ElementaryStrategy.gain S (K n).toElementary T omega - 0‖
    rw [show K n = (H n).posSMul (scale n) (hscalePositive n) by rfl,
      PredictableElementaryStrategy.toElementary_posSMul,
      ElementaryStrategy.gain_mulCoefficient]
    simp only [sub_zero, Real.norm_eq_abs]
    rw [← hgain n]
    rw [abs_mul, abs_of_pos (hscalePositive n)]
    dsimp [scale]
    have hpositive : (0 : Real) < (n + 1 : Nat) := by positivity
    rw [inv_mul_eq_div]
    exact one_le_div hpositive |>.2 homega.le
  have hlarge : ENNReal.ofReal epsilon <
      mu {omega | (1 : Real) ≤
        ‖ElementaryStrategy.gain S (K n).toElementary T omega - 0‖} :=
    (hgainTail n).trans_le (measure_mono hsubset)
  exact (lt_asymm hlarge hn).elim

end IsSemimartingale

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Subtraction of elementary good integrators -/

open Filter MeasureTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}

theorem IsSemimartingale.sub {X Y : Process Ω}
    (hX : IsSemimartingale X F μ) (hY : IsSemimartingale Y F μ) :
    IsSemimartingale (fun t w => X t w - Y t w) F μ := by
  have hEq (H : PredictableElementaryStrategy F) (T : NNReal) :
      ElementaryStrategy.gain (fun t w => X t w - Y t w) H.toElementary T =
        fun w => ElementaryStrategy.gain X H.toElementary T w -
          ElementaryStrategy.gain Y H.toElementary T w := by
    funext w
    have hs := ElementaryStrategy.gain_add_price (fun t w => X t w - Y t w) Y
      H.toElementary T w
    simp only [sub_add_cancel] at hs
    linarith
  refine ⟨?_, ?_⟩
  · intro H T
    rw [hEq]
    exact (hX.1 H T).sub (hY.1 H T)
  · intro H hH T
    simp only [hEq]
    have hs := tendstoInMeasure_add (hX.2 H hH T)
      (tendstoInMeasure_smul_const (-1) (hY.2 H hH T))
    simp only [Pi.zero_apply, mul_zero, add_zero, neg_one_mul] at hs
    exact hs.congr (fun n => Eventually.of_forall fun w => by simp [sub_eq_add_neg])
      (Eventually.of_forall fun w => rfl)

end FTAPTheorem42
