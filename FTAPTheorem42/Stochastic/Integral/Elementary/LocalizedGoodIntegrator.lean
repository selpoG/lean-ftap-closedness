import FTAPTheorem42.Stochastic.Integral.Elementary.MartingaleGoodIntegrator
import Mathlib.Probability.Process.LocalProperty

/-! # Removing stopping from elementary good-integrator estimates -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsFiniteMeasure mu]

omit [MeasurableSpace Ω] in
theorem ElementaryStrategy.gain_stoppedProcess_eq_of_le
    (S : Process Ω) (H : ElementaryStrategy Ω NNReal)
    (τ : Ω → WithTop NNReal) (T : NNReal) (w : Ω) (h : (T : WithTop NNReal) ≤ τ w) :
    gain (stoppedProcess S τ) H T w = gain S H T w := by
  have heq (s : NNReal) (hs : s ≤ T) : stoppedProcess S τ s w = S s w :=
    stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr hs).trans h)
  simp only [gain, ElementaryInterval.gain, heq _ (min_le_left _ _)]

/-- No monotonicity of the stopping sequence is needed for this tail estimate. -/
theorem IsPreLocalizingSequence.tendsto_measure_le
    {τ : Nat → Ω → WithTop NNReal} (hτ : IsPreLocalizingSequence F τ mu) (T : NNReal) :
    Tendsto (fun r => mu {w | τ r w ≤ T}) atTop (𝓝 0) := by
  let f (r : Nat) : Ω → Real := {w | τ r w ≤ T}.indicator (fun _ => 1)
  have hf r : AEStronglyMeasurable (f r) mu :=
    (stronglyMeasurable_const.indicator
      (F.le T _ (hτ.isStoppingTime r T))).aestronglyMeasurable
  have hlim : ∀ᵐ w ∂mu, Tendsto (fun r => f r w) atTop (𝓝 0) := by
    filter_upwards [hτ.tendsto_top] with w hw
    apply tendsto_const_nhds.congr'
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hw T] with r hr
    change 0 = {w | τ r w ≤ T}.indicator (fun _ => (1 : Real)) w
    rw [Set.indicator_of_notMem (show w ∉ {w | τ r w ≤ T} from not_le.mpr hr)]
  have hc := (tendstoInMeasure_of_tendsto_ae hf hlim) 1 (by norm_num)
  have heq r : {w | (1 : ENNReal) ≤ edist (f r w) (0 : Real)} =
      {w | τ r w ≤ T} := by
    ext w
    change (1 : ENNReal) ≤ edist (f r w) 0 ↔ τ r w ≤ T
    by_cases h : τ r w ≤ T
    · have hv : f r w = 1 :=
        Set.indicator_of_mem (show w ∈ {w | τ r w ≤ T} from h) _
      rw [hv]
      simpa only [edist_dist, Real.dist_eq, sub_zero, abs_one, ENNReal.ofReal_one,
        le_refl, true_iff] using h
    · have hv : f r w = 0 :=
        Set.indicator_of_notMem (show w ∉ {w | τ r w ≤ T} from h) _
      rw [hv]
      simpa only [edist_self, nonpos_iff_eq_zero, one_ne_zero, false_iff] using h
  simpa only [heq] using hc

/-- A regular adapted process is a good integrator when an exhaustive family
of its closed stops consists of good integrators. -/
theorem isSemimartingale_of_stoppedProcess
    {S : Process Ω} (hAdapted : StronglyAdapted F S)
    (hRight : ∀ w t, ContinuousWithinAt (S · w) (Ici t) t)
    {τ : Nat → Ω → WithTop NNReal} (hτ : IsPreLocalizingSequence F τ mu)
    (hS : ∀ r, IsSemimartingale (stoppedProcess S (τ r)) F mu) :
    IsSemimartingale S F mu := by
  refine ⟨fun H T => ((H.stronglyAdapted_gain S
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous hAdapted hRight) T).mono
      (F.le T)).aestronglyMeasurable, ?_⟩
  intro H hH T ε hε
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  obtain ⟨r, hr⟩ := ((IsPreLocalizingSequence.tendsto_measure_le hτ T).eventually
    (gt_mem_nhds (ENNReal.half_pos hδ.ne'))).exists
  have hc := (hS r).2 H hH T ε hε
  filter_upwards [hc.eventually (gt_mem_nhds (ENNReal.half_pos hδ.ne'))] with n hn
  calc
    mu {w | ε ≤ edist (ElementaryStrategy.gain S (H n).toElementary T w) (0 : Real)} ≤
        mu ({w | τ r w ≤ T} ∪ {w | ε ≤ edist
          (ElementaryStrategy.gain (stoppedProcess S (τ r)) (H n).toElementary T w)
          (0 : Real)}) := by
      apply measure_mono
      intro w hw
      by_cases ht : τ r w ≤ T
      · exact Or.inl ht
      · exact Or.inr (by
          change ε ≤ edist (ElementaryStrategy.gain
            (stoppedProcess S (τ r)) (H n).toElementary T w) (0 : Real)
          rwa [ElementaryStrategy.gain_stoppedProcess_eq_of_le S _ _ T w
            (le_of_not_ge ht)])
    _ ≤ mu {w | τ r w ≤ T} + mu {w | ε ≤ edist
        (ElementaryStrategy.gain (stoppedProcess S (τ r)) (H n).toElementary T w)
        (0 : Real)} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hr.le hn.le
    _ = δ := ENNReal.add_halves δ

end FTAPTheorem42
