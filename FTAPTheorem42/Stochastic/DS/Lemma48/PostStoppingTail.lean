/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Passage
import FTAPTheorem42.Stochastic.DS.Lemma47.FirstPassage
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategy

/-!
# Post-stopping tail strategies for Lemma 4.8

Lemma 4.8 uses the part of a realized stochastic integral strictly after the
first passage of its martingale component.  This module constructs that tail
at the level of numerical component records. It also constructs finite
weighted sums of such tails and proves the corresponding gain and
component identities. Original-price realization is supplied separately in
`Lemma48FiniteRealizedTail`. No commutation between strategy-dependent stopping
and convexification is asserted.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Raw post-stopping processes -/

omit [MeasurableSpace Ω] in
@[simp]
theorem postStoppingTailProcess_eq_zero_of_le
    (X : Process Ω) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) (ht : (t : WithTop ℝ≥0) ≤ τ ω) :
    postStoppingTailProcess X τ t ω = 0 := by
  unfold postStoppingTailProcess
  rw [MeasureTheory.stoppedProcess_eq_of_le ht]
  ring

omit [MeasurableSpace Ω] in
theorem postStoppingTailProcess_eq_sub_of_lt
    (X : Process Ω) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) (ht : τ ω < (t : WithTop ℝ≥0)) :
    postStoppingTailProcess X τ t ω =
      X t ω - X (τ ω).untopA ω := by
  unfold postStoppingTailProcess
  rw [MeasureTheory.stoppedProcess_eq_of_ge ht.le]

/-! ## Numerical post-stopping records -/

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The component record carrying the part of `H` strictly after `τ`.
It is constructed algebraically as `H - H^τ`, so all three process
identities follow from the stopping calculus. -/
noncomputable def postStoppingTail
    (C : SIntegrableProcessStoppingCalculus D)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) : SIntegrableStrategy D :=
  H.add_of_rightContinuous (C.stopAtTop τ hτ H).neg

theorem postStoppingTail_stochasticIntegral
    (C : SIntegrableProcessStoppingCalculus D)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) :
    ProcessIndistinguishable μ
      (stochasticIntegral (C.postStoppingTail τ hτ H))
      (postStoppingTailProcess H.stochasticIntegral τ) := by
  filter_upwards [C.stochasticIntegral_stopAtTop τ hτ H] with ω hω
  intro t
  change H.stochasticIntegral t ω -
      stochasticIntegral (C.stopAtTop τ hτ H) t ω = _
  rw [hω t]
  rfl

theorem postStoppingTail_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (H : SIntegrableStrategy D) :
    ProcessIndistinguishable μ
      (C.postStoppingTail τ hτ H).martingalePart
      (postStoppingTailProcess H.martingalePart τ) := by
  filter_upwards [C.martingalePart_stopAtTop τ hτ H] with ω hω
  intro t
  change H.martingalePart t ω -
      (C.stopAtTop τ hτ H).martingalePart t ω = _
  rw [hω t]
  rfl

end SIntegrableProcessStoppingCalculus

/-! ## Finite weighted sums of realized strategies -/

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The weighted sum of the first `n` realized strategies.  The zero case is
implemented as `0 • H 0`, avoiding an unrelated zero-strategy provider. -/
noncomputable def weightedPrefixSum
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ) :
    ℕ → SIntegrableStrategy D
  | 0 => (H 0).smul 0
  | n + 1 => (weightedPrefixSum H weight n).add_of_rightContinuous
      ((H n).smul (weight n))

@[simp]
theorem weightedPrefixSum_integrand_apply
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (weightedPrefixSum H weight n).integrand t ω =
      ∑ i ∈ Finset.range n, weight i * (H i).integrand t ω := by
  induction n with
  | zero =>
      change 0 * (H 0).integrand t ω = 0
      ring
  | succ n ih =>
      rw [weightedPrefixSum]
      change (weightedPrefixSum H weight n).integrand t ω +
        weight n * (H n).integrand t ω = _
      rw [ih, Finset.sum_range_succ]

@[simp]
theorem weightedPrefixSum_stochasticIntegral_apply
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (weightedPrefixSum H weight n).stochasticIntegral t ω =
      ∑ i ∈ Finset.range n, weight i * (H i).stochasticIntegral t ω := by
  induction n with
  | zero =>
      change 0 * (H 0).stochasticIntegral t ω = 0
      ring
  | succ n ih =>
      rw [weightedPrefixSum]
      change (weightedPrefixSum H weight n).stochasticIntegral t ω +
        weight n * (H n).stochasticIntegral t ω = _
      rw [ih, Finset.sum_range_succ]

@[simp]
theorem weightedPrefixSum_martingalePart_apply
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (weightedPrefixSum H weight n).martingalePart t ω =
      ∑ i ∈ Finset.range n, weight i * (H i).martingalePart t ω := by
  induction n with
  | zero =>
      change 0 * (H 0).martingalePart t ω = 0
      ring
  | succ n ih =>
      rw [weightedPrefixSum]
      change (weightedPrefixSum H weight n).martingalePart t ω +
        weight n * (H n).martingalePart t ω = _
      rw [ih, Finset.sum_range_succ]

end SIntegrableStrategy

/-! ## The actual tail-convex family of Lemma 4.8 -/

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- First passage of the martingale maximal process used in Lemma 4.8. -/
noncomputable def lemma48FirstPassage
    (H : SIntegrableStrategy D) (c : ℝ) : Ω → WithTop ℝ≥0 :=
  absoluteStrictHittingAfter H.martingalePart c

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48FirstPassage_isStoppingTime
    (H : SIntegrableStrategy D) (c : ℝ) :
    IsStoppingTime ℱ (lemma48FirstPassage H c) :=
  absoluteStrictHittingAfter_isStoppingTime
    H.martingalePart_isStronglyAdapted
    H.martingalePart_isRightContinuous c

/-- The part of `H` strictly after its martingale first passage of `c`. -/
noncomputable def lemma48Tail
    (C : SIntegrableProcessStoppingCalculus D)
    (H : SIntegrableStrategy D) (c : ℝ) : SIntegrableStrategy D :=
  C.postStoppingTail (lemma48FirstPassage H c)
    (lemma48FirstPassage_isStoppingTime H c) H

/-- An actual finite weighted sum of first-passage tails. -/
noncomputable def lemma48TailConvexStrategy
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) : SIntegrableStrategy D :=
  SIntegrableStrategy.weightedPrefixSum (fun i => C.lemma48Tail (H i) c) weight n

/-- The total convex weight whose individual first-passage times have already
occurred strictly before `t`.  This is the active-weight process used to
preserve admissibility in the proof of Lemma 4.8. -/
noncomputable def lemma48ActiveMass
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) : Process Ω :=
  fun t ω => ∑ i ∈ Finset.range n, weight i *
    if lemma48FirstPassage (H i) c ω < (t : WithTop ℝ≥0) then 1 else 0

theorem lemma48TailConvexStrategy_stochasticIntegral
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    ProcessIndistinguishable μ
      (C.lemma48TailConvexStrategy H weight n c).stochasticIntegral
      (fun t ω => ∑ i ∈ Finset.range n, weight i *
        postStoppingTailProcess (H i).stochasticIntegral
          (lemma48FirstPassage (H i) c) t ω) := by
  have hTail : ∀ᵐ ω ∂μ, ∀ i t,
      (C.lemma48Tail (H i) c).stochasticIntegral t ω =
        postStoppingTailProcess (H i).stochasticIntegral
          (lemma48FirstPassage (H i) c) t ω := by
    rw [ae_all_iff]
    intro i
    exact C.postStoppingTail_stochasticIntegral
      (lemma48FirstPassage (H i) c)
      (lemma48FirstPassage_isStoppingTime (H i) c) (H i)
  filter_upwards [hTail] with ω hω
  intro t
  change (SIntegrableStrategy.weightedPrefixSum
    (fun i => C.lemma48Tail (H i) c) weight n).stochasticIntegral t ω = _
  rw [SIntegrableStrategy.weightedPrefixSum_stochasticIntegral_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hω i t]

theorem lemma48TailConvexStrategy_martingalePart
    (C : SIntegrableProcessStoppingCalculus D)
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    ProcessIndistinguishable μ
      (C.lemma48TailConvexStrategy H weight n c).martingalePart
      (fun t ω => ∑ i ∈ Finset.range n, weight i *
        postStoppingTailProcess (H i).martingalePart
          (lemma48FirstPassage (H i) c) t ω) := by
  have hTail : ∀ᵐ ω ∂μ, ∀ i t,
      (C.lemma48Tail (H i) c).martingalePart t ω =
        postStoppingTailProcess (H i).martingalePart
          (lemma48FirstPassage (H i) c) t ω := by
    rw [ae_all_iff]
    intro i
    exact C.postStoppingTail_martingalePart
      (lemma48FirstPassage (H i) c)
      (lemma48FirstPassage_isStoppingTime (H i) c) (H i)
  filter_upwards [hTail] with ω hω
  intro t
  change (SIntegrableStrategy.weightedPrefixSum
    (fun i => C.lemma48Tail (H i) c) weight n).martingalePart t ω = _
  rw [SIntegrableStrategy.weightedPrefixSum_martingalePart_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hω i t]

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
