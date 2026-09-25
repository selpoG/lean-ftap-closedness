/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Process.DenseRightLimitContinuity
import FTAPTheorem42.Stochastic.Process.FactorialGridRightApproximation

/-!
# Right continuity of the factorial-grid martingale regularization

The simultaneous right limits supplied by the upcrossing argument are not
merely pointwise limits. Since every preterminal time has strict right
approximants in the same factorial-grid union, the selected limit process is
right-continuous at every preterminal time outside one null set.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- Outside one null set, the selected factorial-grid right-limit process is
right-continuous at every time strictly before the horizon. -/
theorem Martingale.factorialGridRightLimit_isRightContinuous_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∀ t, t < T ->
      ContinuousWithinAt
        (fun s => factorialGridRightLimit M T s omega) (Ici t) t := by
  filter_upwards
    [Martingale.tendsto_factorialGridRightLimit_ae hM T hterminal]
      with omega hPath
  intro t ht
  apply continuousWithinAt_Ici_of_tendsto_denseRight ht
  · intro s hs
    exact hPath s hs
  · intro s hs
    let r : Nat -> NNReal := factorialGridRightApproxTime T s
    have hrWithin : Tendsto r atTop
        (nhdsWithin s (factorialGridTimes T ∩ Ioi s)) :=
      tendsto_nhdsWithin_iff.2 ⟨
        tendsto_factorialGridRightApproxTime T s hs.le,
        Filter.Eventually.of_forall fun n =>
          ⟨factorialGridRightApproxTime_mem T s n,
            lt_factorialGridRightApproxTime hs n⟩⟩
    exact (inferInstance : (Filter.map r atTop).NeBot).mono hrWithin

/-- Outside one null set, the selected right-limit process has a finite left
limit at every positive time up to the horizon. -/
theorem Martingale.factorialGridRightLimit_hasLeftLimits_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∀ t, 0 < t -> t ≤ T ->
      Tendsto
        (fun s => factorialGridRightLimit M T s omega)
        (nhdsWithin t (Iio t))
        (nhds (Function.leftLim
          (fun s => factorialGridRightLimit M T s omega) t)) := by
  filter_upwards
    [Martingale.tendsto_factorialGridRightLimit_ae hM T hterminal,
      Martingale.exists_tendsto_factorialGridTimes_nhdsLT_ae
        hM T hterminal]
      with omega hRight hLeft
  intro t ht htT
  obtain ⟨z, hz⟩ := hLeft t ht htT
  apply tendsto_leftLim_of_tendsto
  refine ⟨z, tendsto_nhdsLT_of_tendsto_denseLeftRight ht hz ?_ ?_⟩
  · intro s hst
    exact hRight s (hst.trans_le htT)
  · intro s hst
    have hsT : s < T := hst.trans_le htT
    let r : Nat -> NNReal := factorialGridRightApproxTime T s
    have hrWithin : Tendsto r atTop
        (nhdsWithin s (factorialGridTimes T ∩ Ioi s)) :=
      tendsto_nhdsWithin_iff.2 ⟨
        tendsto_factorialGridRightApproxTime T s hsT.le,
        Filter.Eventually.of_forall fun n =>
          ⟨factorialGridRightApproxTime_mem T s n,
            lt_factorialGridRightApproxTime hsT n⟩⟩
    exact (inferInstance : (Filter.map r atTop).NeBot).mono hrWithin

/-- The finite-horizon selected process has the two path properties needed
for a càdlàg regularization: right continuity before the terminal time and
left limits at every positive time up to it. -/
theorem Martingale.factorialGridRightLimit_isCadlagOn_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu,
      (∀ t, t < T -> ContinuousWithinAt
        (fun s => factorialGridRightLimit M T s omega) (Ici t) t) ∧
      (∀ t, 0 < t -> t ≤ T -> Tendsto
        (fun s => factorialGridRightLimit M T s omega)
        (nhdsWithin t (Iio t))
        (nhds (Function.leftLim
          (fun s => factorialGridRightLimit M T s omega) t))) := by
  filter_upwards
    [Martingale.factorialGridRightLimit_isRightContinuous_ae
      hM T hterminal,
      Martingale.factorialGridRightLimit_hasLeftLimits_ae
        hM T hterminal] with omega hRight hLeft
  exact ⟨hRight, hLeft⟩

end HorizonFactorialGrid

end FTAPTheorem42
