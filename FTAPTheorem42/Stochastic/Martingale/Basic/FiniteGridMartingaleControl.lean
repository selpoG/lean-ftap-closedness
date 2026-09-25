/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.DiscretePredictableIntegral
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleChronologicalGrid
import FTAPTheorem42.Stochastic.Memin.ControlLIntegral
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Predictable martingale controls on finite deterministic grids

For one deterministic interval `[s,t]`, put the measure with density
`‖M t - M s‖ₑ ^ 2` on the predictable graph at its left endpoint `s`.
Summing these measures over a finite chronological grid gives a genuine
measure on the continuous-time predictable sigma algebra.

For every bounded strongly predictable process `K`, its `L²` seminorm under
this measure is exactly the terminal `L²` seminorm of the finite-grid
predictable integral against a square-integrable martingale.  Thus the
control measure and its isometry are constructed from the martingale rather
than supplied as abstract fields.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The energy of one martingale increment, placed on the predictable graph
of the interval's left endpoint. -/
noncomputable def predictableIncrementEnergyControl
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (M : Process Ω) (s t : ℝ≥0) :
    MeminPredictableControlMeasure ℱ :=
  @Measure.map Ω (ℝ≥0 × Ω) _ ℱ.predictable
    (stoppingGraphMap (fun _ : Ω => s))
    (μ.withDensity fun ω => ‖M t ω - M s ω‖ₑ ^ 2)

/-- Integrating squared predictable coefficients against one increment
control gives the second moment of the corresponding weighted increment. -/
theorem lintegral_predictableIncrementEnergyControl
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (μ : Measure Ω) (M : Process Ω) (hM : StronglyAdapted ℱ M)
    (s t : ℝ≥0) (K : Process Ω) (hK : IsStronglyPredictable ℱ K) :
    (∫⁻ p, ‖Function.uncurry K p‖ₑ ^ 2
        ∂predictableIncrementEnergyControl ℱ μ M s t) =
      ∫⁻ ω, ‖K s ω * (M t ω - M s ω)‖ₑ ^ 2 ∂μ := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let graph : Ω → ℝ≥0 × Ω :=
    stoppingGraphMap (fun _ : Ω => s)
  have hGraph : @Measurable Ω (ℝ≥0 × Ω)
      (inferInstance : MeasurableSpace Ω) ℱ.predictable graph :=
    IsStoppingTime.measurable_stoppingGraphMap_predictable
      (isStoppingTime_const ℱ s)
  have hIntegrand : @Measurable (ℝ≥0 × Ω) ℝ≥0∞ ℱ.predictable _
      (fun p => ‖Function.uncurry K p‖ₑ ^ 2) :=
    hK.enorm.pow_const 2
  have hDensity : Measurable
      (fun ω => ‖M t ω - M s ω‖ₑ ^ 2) :=
    ((((hM t).mono (ℱ.le t)).sub
      ((hM s).mono (ℱ.le s))).enorm.pow_const 2)
  have hComp : Measurable
      (fun ω => ‖Function.uncurry K (graph ω)‖ₑ ^ 2) :=
    hIntegrand.comp hGraph
  rw [predictableIncrementEnergyControl,
    lintegral_map hIntegrand hGraph,
    lintegral_withDensity_eq_lintegral_mul μ hDensity hComp]
  apply lintegral_congr
  intro ω
  simp only [Pi.mul_apply, graph, stoppingGraphMap,
    Function.uncurry_apply_pair]
  rw [enorm_mul]
  ring

namespace ChronologicalGrid

variable {N : ℕ} (G : ChronologicalGrid ℝ≥0 N)

/-- The finite sum of left-graph increment-energy controls associated with
a chronological grid. -/
noncomputable def martingaleEnergyControl
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (M : Process Ω) :
    MeminPredictableControlMeasure ℱ :=
  ∑ k ∈ Finset.range N,
    predictableIncrementEnergyControl ℱ μ M
      (G.sampledTime k) (G.sampledTime (k + 1))

/-- The finite-grid control integral is the sum of the weighted increment
second moments. -/
theorem lintegral_martingaleEnergyControl
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (μ : Measure Ω) (M : Process Ω) (hM : StronglyAdapted ℱ M)
    (K : Process Ω) (hK : IsStronglyPredictable ℱ K) :
    (∫⁻ p, ‖Function.uncurry K p‖ₑ ^ 2
        ∂G.martingaleEnergyControl ℱ μ M) =
      ∑ k ∈ Finset.range N,
        ∫⁻ ω, ‖K (G.sampledTime k) ω *
          (M (G.sampledTime (k + 1)) ω -
            M (G.sampledTime k) ω)‖ₑ ^ 2 ∂μ := by
  rw [martingaleEnergyControl, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro k _
  exact lintegral_predictableIncrementEnergyControl
    μ M hM (G.sampledTime k) (G.sampledTime (k + 1)) K hK

/-- Sampling a strongly adapted coefficient process on the constantly
extended grid preserves adaptedness. -/
theorem stronglyAdapted_natSample
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {K : Process Ω} (hK : StronglyAdapted ℱ K) :
    StronglyAdapted (G.sampledFiltration ℱ) (G.natSample K) :=
  fun n => hK (G.sampledTime n)

/-- The predictable control energy equals the energy of the terminal
finite-grid stochastic integral. -/
theorem lintegral_martingaleEnergyControl_eq_terminal
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M K : Process Ω} {C : ℝ≥0 → ℝ}
    (hM : Martingale M ℱ μ)
    (hMLp : ∀ t, MemLp (M t) (2 : ℝ≥0∞) μ)
    (hK : IsStronglyPredictable ℱ K)
    (hKBound : ∀ t, ∀ᵐ ω ∂μ, |K t ω| ≤ C t) :
    (∫⁻ p, ‖Function.uncurry K p‖ₑ ^ 2
        ∂G.martingaleEnergyControl ℱ μ M) =
      ∫⁻ ω, ‖discretePredictableIntegral
        (G.natSample K) (G.natSample M) N ω‖ₑ ^ 2 ∂μ := by
  rw [G.lintegral_martingaleEnergyControl μ M hM.stronglyAdapted K hK]
  symm
  simpa only [natSample, sampledTime] using
    DiscretePredictableIntegral.lintegral_enorm_sq_eq_sum
      (ChronologicalGrid.Martingale.natSample (G := G) hM)
      (fun n => hMLp (G.sampledTime n))
      (G.stronglyAdapted_natSample hK.stronglyAdapted)
      (fun n => hKBound (G.sampledTime n)) N

end ChronologicalGrid

end FTAPTheorem42
