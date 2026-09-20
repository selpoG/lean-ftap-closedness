/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Market.Transfer.EquivalentMeasure
import FTAPTheorem42.Stochastic.Decomposition.Source.Variation
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Martingale identities on fixed-horizon factorial grids

Right factorial approximation preserves the chronological order of target
times.  The finite-grid Doob martingale therefore satisfies the conditional
expectation identity between the approximating points of any two fixed times.
These identities are the discrete input for passing a common convex limit to
a continuous-time martingale component.
-/

namespace FTAPTheorem42

open MeasureTheory
open scoped NNReal ProbabilityTheory

namespace HorizonFactorialGrid

/-- Right factorial indices preserve the order of target times. -/
theorem approxIndex_mono
    (T s t : NNReal) (hs : s ≤ T) (ht : t ≤ T)
    (hst : s ≤ t) (r : Nat) :
    approxIndex T s hs r ≤ approxIndex T t ht r := by
  change Nat.ceil (s * (r.factorial : NNReal)) ≤
    Nat.ceil (t * (r.factorial : NNReal))
  exact Nat.ceil_mono
    (mul_le_mul_of_nonneg_right hst (by positivity))

end HorizonFactorialGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Finite variation of factorial-grid predictable paths

At one factorial-grid level, view the predictable Doob component as a path on
the fixed horizon by evaluating it at the first grid point to the right of the
target time.  The index map is monotone.  Its path variation is therefore no
larger than the discrete predictable variation accumulated over the whole
grid.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace HorizonFactorialGrid

/-- The right-factorial index is monotone on the fixed horizon. -/
theorem monotone_approxIndex_val (T : NNReal) (r : Nat) :
    Monotone (fun t : Set.Iic T => (approxIndex T t.1 t.2 r).1) := by
  intro s t hst
  exact_mod_cast approxIndex_mono T s.1 t.1 s.2 t.2 hst r

/-- Every right-factorial index lies before the terminal index of its grid. -/
theorem approxIndex_val_le_size (T : NNReal) (r : Nat) (t : Set.Iic T) :
    (approxIndex T t.1 t.2 r).1 ≤ size T r :=
  Nat.le_of_lt_succ (approxIndex T t.1 t.2 r).2

end HorizonFactorialGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Envelopes for convergent convexified factorial-grid components

An almost-everywhere convergent real sequence has an almost-everywhere finite
measurable norm envelope.  Tilting by that envelope makes it square
integrable under an equivalent probability measure.  Applied to the
convexified terminal Doob variations, the same envelope controls every
predictable component on the fixed horizon.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The countable pointwise norm envelope of a real-valued sequence. -/
noncomputable def sequenceNormEnvelope (u : Nat → Omega → Real) : Omega → Real :=
  fun omega => ⨆ n, ‖u n omega‖

/-- A countable envelope of measurable functions is measurable. -/
theorem measurable_sequenceNormEnvelope
    (u : Nat → Omega → Real) (hu : ∀ n, Measurable (u n)) :
    Measurable (sequenceNormEnvelope u) := by
  unfold sequenceNormEnvelope
  apply Measurable.iSup
  intro n
  exact (hu n).norm

omit [MeasurableSpace Omega] in
/-- Every term lies below the envelope whenever the pointwise norm sequence
is bounded above. -/
theorem norm_le_sequenceNormEnvelope_of_bddAbove
    (u : Nat → Omega → Real) {omega : Omega}
    (hbound : BddAbove (Set.range fun n => ‖u n omega‖)) (n : Nat) :
    ‖u n omega‖ ≤ sequenceNormEnvelope u omega := by
  unfold sequenceNormEnvelope
  exact le_ciSup hbound n

/-- Pointwise convergence gives the boundedness needed by the countable
envelope. -/
theorem ae_bddAbove_range_norm_of_tendstoAE
    {mu : Measure Omega} {u : Nat → Omega → Real} {v : Omega → Real}
    (hlim : TendstoAE mu u v) :
    ∀ᵐ omega ∂mu, BddAbove (Set.range fun n => ‖u n omega‖) := by
  filter_upwards [hlim] with omega homega
  exact homega.norm.bddAbove_range

/-- An a.e.-convergent measurable sequence admits a common square-integrable
envelope after an equivalent exponential change of measure. -/
theorem exists_tilted_sequenceNormEnvelope_of_tendstoAE
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (u : Nat → Omega → Real) (v : Omega → Real)
    (hu : ∀ n, Measurable (u n)) (hlim : TendstoAE mu u v) :
    ∃ (xi : Omega → Real) (Q : Measure Omega),
      Measurable xi ∧
      (∀ omega, 0 ≤ xi omega) ∧
      (∀ᵐ omega ∂mu, ∀ n, ‖u n omega‖ ≤ xi omega) ∧
      Q = CommonEnvelopeMeasure.tilted mu xi ∧
      IsProbabilityMeasure Q ∧
      Q ≪ mu ∧
      mu ≪ Q ∧
      MemLp xi 2 Q := by
  let raw : Omega → Real := sequenceNormEnvelope u
  let xi : Omega → Real := fun omega => max (raw omega) 0
  have hrawMeas : Measurable raw :=
    measurable_sequenceNormEnvelope u hu
  have hxiMeas : Measurable xi := hrawMeas.max measurable_const
  have hxiNonneg : ∀ omega, 0 ≤ xi omega := fun omega => le_max_right _ _
  have hdom : ∀ᵐ omega ∂mu, ∀ n, ‖u n omega‖ ≤ xi omega := by
    filter_upwards [ae_bddAbove_range_norm_of_tendstoAE hlim] with omega hbound
    intro n
    exact (norm_le_sequenceNormEnvelope_of_bddAbove u hbound n).trans
      (le_max_left _ _)
  let Q : Measure Omega := CommonEnvelopeMeasure.tilted mu xi
  have hQProbability : IsProbabilityMeasure Q := by
    exact CommonEnvelopeMeasure.tilted_isProbabilityMeasure
      hxiMeas hxiNonneg
  have hQmu : Q ≪ mu := CommonEnvelopeMeasure.tilted_absolutelyContinuous
  have hmuQ : mu ≪ Q :=
    CommonEnvelopeMeasure.absolutelyContinuous_tilted hxiMeas hxiNonneg
  have hxiL2 : MemLp xi 2 Q :=
    CommonEnvelopeMeasure.memLp_two_tilted hxiMeas hxiNonneg
  exact ⟨xi, Q, hxiMeas, hxiNonneg, hdom, rfl, hQProbability,
    hQmu, hmuQ, hxiL2⟩

end FTAPTheorem42
