/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.BoundedSource
import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness
import FTAPTheorem42.Foundations.UsualConditions

/-!
# Bounded semimartingale source data

This is the concrete source boundary needed before constructing a special
decomposition and a stochastic-integral calculus.  It contains only source
properties: usual conditions, adapted càdlàg regularity, a deterministic
uniform bound, and the elementary good-integrator semimartingale predicate.
It contains no decomposition, strategy realization, or closure conclusion.

All these source properties transfer to an equivalent probability measure.
The path properties are measure independent, the bound transfers by absolute
continuity, and semimartingale invariance is the elementary good-integrator
theorem.
-/

open MeasureTheory Set
open scoped NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedSemimartingaleSource

/-- A bounded semimartingale source remains one under an equivalent
probability measure. -/
def ofMutuallyAbsolutelyContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu Q : Measure Omega} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure Q]
    (M : BoundedSemimartingaleSource S F mu)
    (hMuQ : mu ≪ Q) (hQMu : Q ≪ mu) :
    BoundedSemimartingaleSource S F Q where
  usualConditions :=
    (Filtration.usualConditions_iff_of_mutuallyAbsolutelyContinuous
      hMuQ hQMu).mp M.usualConditions
  stronglyAdapted := M.stronglyAdapted
  rightContinuous := M.rightContinuous
  hasLeftLimits := M.hasLeftLimits
  bound := M.bound
  uniformBound := hQMu.ae_le M.uniformBound
  isSemimartingale :=
    (IsSemimartingale.iff_of_mutuallyAbsolutelyContinuous hMuQ hQMu).mp
      M.isSemimartingale

end BoundedSemimartingaleSource

end FTAPTheorem42
