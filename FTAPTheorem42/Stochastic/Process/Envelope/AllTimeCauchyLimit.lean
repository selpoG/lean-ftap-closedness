/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Compactness.MaximalCauchyEnvelope
import FTAPTheorem42.Stochastic.Process.UniformLimits
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # A regular all-time uniform limit from all-time Cauchy control

The same fast extraction used by the envelope construction supplies an
adapted uniform limit. This does not assert stochastic-integral membership.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}

/-- Construct the limit, regularize it on one time-zero null set, and retain
uniform convergence over the entire time axis. -/
theorem exists_cadlag_uniform_limit_of_allTimeGap_cauchyInMeasure
    (X : Nat → Process Ω) (hUsual : Filtration.UsualConditions μ F)
    (hX : ∀ n, StronglyAdapted F (X n))
    (hXR : ∀ n ω t, ContinuousWithinAt (X n · ω) (Ici t) t)
    (hXL : ∀ n, ProcessHasLeftLimits (X n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖X n t ω - X m t ω‖} ≤ ENNReal.ofReal δ) :
    ∃ (f : Nat → Nat) (Y : Process Ω), StrictMono f ∧ StronglyAdapted F Y ∧
      (∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t) ∧ ProcessHasLeftLimits Y ∧
      ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => X (f n) t ω) (Y · ω) atTop := by
  obtain ⟨f, hf, hFast⟩ :=
    exists_strictMono_ae_fast_steps_of_allTimeGap_cauchyInMeasure X hcauchy
  let Z : Process Ω := fun t ω => limUnder atTop (fun n => X (f n) t ω)
  have hZ : StronglyAdapted F Z := by
    intro t
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun n => hX (f n) t)
  have hU : ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => X (f n) t ω) (Z · ω) atTop := by
    filter_upwards [hFast] with ω hω
    have hC : UniformCauchySeqOn (fun n t => X (f n) t ω) atTop univ := by
      apply uniformCauchySeqOn_of_eventually_dist_step_le_of_summable
        _ _ (fun k => ((1 : Real) / 2) ^ (k + 1))
      · simpa [pow_succ, mul_comm] using
          (summable_geometric_two.mul_left ((1 : Real) / 2))
      · intro k
        positivity
      · filter_upwards [hω] with k hk
        intro t _
        simpa only [dist_eq_norm, norm_sub_rev] using (hk t).le
    apply tendstoUniformlyOn_univ.mp
    exact hC.tendstoUniformlyOn_of_tendsto fun t ht =>
      (hC.cauchySeq ht).tendsto_limUnder
  have hReg : ∀ᵐ ω ∂μ, (∀ t, ContinuousWithinAt (Z · ω) (Ici t) t) ∧
      ∀ t, Tendsto (Z · ω) (𝓝[<] t) (𝓝 (Function.leftLim (Z · ω) t)) := by
    filter_upwards [hU] with ω hω
    exact ⟨rightContinuous_of_tendstoUniformly _ _ hω (fun n => hXR (f n) ω),
      leftLimits_of_tendstoUniformly _ _ hω (fun n => hXL (f n) ω)⟩
  obtain ⟨Y, hY, hYR, hYL, hYZ⟩ :=
    ProcessNullSetRegularization.exists_stronglyAdapted_rightContinuous_leftLimits_version
      hUsual hZ hReg
  refine ⟨f, Y, hf, hY, hYR, hYL, ?_⟩
  filter_upwards [hU, hYZ] with ω hω heq
  simpa only [show (Y · ω) = (Z · ω) from funext heq] using hω

end FTAPTheorem42
