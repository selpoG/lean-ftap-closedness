import FTAPTheorem42.Stochastic.Integral.Elementary.ElementarySemimartingaleBoundedness

/-! # Closed stopping preserves the elementary good-integrator property -/

open Filter MeasureTheory
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

theorem PredictableElementaryStrategy.integrand_stopAt
    (H : PredictableElementaryStrategy F) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) (t : NNReal) (w : Ω) :
    (H.stopAt τ hτ).integrand t w = if t ≤ τ w then H.integrand t w else 0 := by
  classical
  have hBlock (B : PredictableElementaryInterval F) :
      (B.after τ hτ).neg.integrand t w =
        if t ≤ τ w then 0 else -B.integrand t w := by
    simp only [PredictableElementaryInterval.integrand,
      PredictableElementaryInterval.neg_interval, PredictableElementaryInterval.after_interval,
      ElementaryInterval.neg, ElementaryInterval.after, ElementaryInterval.mulCoefficient]
    split_ifs <;> simp_all <;> grind
  have hTail : ((H.after τ hτ).neg).integrand t w =
      if t ≤ τ w then 0 else -H.integrand t w := by
    induction H with
    | nil => simp [integrand, after, neg]
    | cons B H ih =>
      change (B.after τ hτ).neg.integrand t w +
        (PredictableElementaryStrategy.neg
          (PredictableElementaryStrategy.after H τ hτ)).integrand t w =
          if t ≤ τ w then 0 else
            -(B.integrand t w + PredictableElementaryStrategy.integrand H t w)
      rw [hBlock, ih]
      split_ifs <;> ring
  change (H ++ (H.after τ hτ).neg).integrand t w = _
  have hAdd : (H ++ (H.after τ hτ).neg).integrand =
      H.integrand + ((H.after τ hτ).neg).integrand := by
    simp [integrand]
  rw [hAdd]
  change H.integrand t w + ((H.after τ hτ).neg).integrand t w = _
  rw [hTail]
  split_ifs <;> ring

/-- Stop the integrand using the predictable post-stopping tail construction;
raw blockwise stopping alone would lose predictability. -/
theorem IsSemimartingale.stoppedProcess_coe {S : Process Ω}
    (hS : IsSemimartingale S F mu) (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    IsSemimartingale (stoppedProcess S (fun w => (τ w : WithTop NNReal))) F mu := by
  have hEq (H : PredictableElementaryStrategy F) (T : NNReal) :
      ElementaryStrategy.gain (stoppedProcess S (fun w => (τ w : WithTop NNReal)))
        H.toElementary T = ElementaryStrategy.gain S (H.stopAt τ hτ).toElementary T := by
    funext w
    rw [H.gain_stopAt]
    have hStop (s : NNReal) :
        stoppedProcess S (fun w => (τ w : WithTop NNReal)) s w = S (min s (τ w)) w := by
      change S (min (s : WithTop NNReal) (τ w : WithTop NNReal)).untopA w = _
      rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    simp only [ElementaryStrategy.gain, ElementaryInterval.gain, hStop,
      min_assoc, min_comm, min_left_comm]
  refine ⟨fun H T => hEq H T ▸ hS.1 (H.stopAt τ hτ) T, ?_⟩
  intro H hH T
  have hU : ElementaryIntegrandsTendstoUniformlyZero (fun n => (H n).stopAt τ hτ) := by
    intro ε hε
    filter_upwards [hH ε hε] with n hn
    intro t w
    rw [PredictableElementaryStrategy.integrand_stopAt]
    split_ifs
    · exact hn t w
    · simpa only [abs_zero] using hε.le
  simpa only [hEq] using hS.2 (fun n => (H n).stopAt τ hτ) hU T

end FTAPTheorem42
