import FTAPTheorem42.Stochastic.Decomposition.LargeJump.GlobalDecompositionOverlap
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.Residual

/-! # The adapted large-jump sum on all finite horizons -/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42.FiniteLargeJumpProcess

variable {Ω : Type*} {X : Process Ω} {c : Real}

noncomputable def globalProcess (X : Process Ω) (c : Real) : Process Ω :=
  fun t w => process X c t t w

theorem globalProcess_eq_on_horizon
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c)
    {t T : NNReal} (ht : t ≤ T) (w : Ω) :
    globalProcess X c t w = process X c T t w := by
  have h := congrFun (congrFun (process_min_horizon hRight hLeft hc ht) t) w
  simpa only [min_self, globalProcess] using h.symm

theorem globalProcess_zero
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) : globalProcess X c 0 = 0 :=
  process_zero hRight hLeft hc

theorem globalProcess_rightContinuous
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ w t, ContinuousWithinAt ((globalProcess X c) · w) (Ici t) t := by
  intro w t
  have heq : (fun s => globalProcess X c s w) =ᶠ[𝓝[≥] t]
      fun s => process X c (t + 1) s w := by
    filter_upwards [show ∀ᶠ s in 𝓝[≥] t, s < t + 1 from
      (eventually_lt_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds] with s hs
    exact globalProcess_eq_on_horizon hRight hLeft hc hs.le w
  exact (process_rightContinuous hRight hLeft hc w t).congr_of_eventuallyEq
    heq (globalProcess_eq_on_horizon hRight hLeft hc (le_add_of_nonneg_right zero_le_one) w)

theorem globalProcess_hasLeftLimits
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ProcessHasLeftLimits (globalProcess X c) := by
  intro w t
  have heq : (fun s => process X c t s w) =ᶠ[𝓝[<] t]
      fun s => globalProcess X c s w := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (globalProcess_eq_on_horizon hRight hLeft hc (show s < t from hs).le w).symm
  have hlim := (process_hasLeftLimits hRight hLeft hc w t).congr' heq
  rcases eq_or_neBot (𝓝[<] t) with hbot | hne
  · simp only [hbot, tendsto_bot]
  · rw [leftLim_eq_of_tendsto hlim]
    exact hlim

theorem globalProcess_locallyBoundedVariation
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    ∀ w, LocallyBoundedVariationOn ((globalProcess X c) · w) univ := by
  intro w a b ha hb
  have hv := process_locallyBoundedVariationOn (T := b) hRight hLeft hc w a b ha hb
  unfold BoundedVariationOn at hv ⊢
  rw [eVariationOn.eq_of_eqOn (f' := fun s => process X c b s w)
    (fun s hs => globalProcess_eq_on_horizon hRight hLeft hc hs.2.2 w)]
  exact hv

theorem globalProcess_stronglyAdapted [MeasurableSpace Ω]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} [F.IsRightContinuous]
    (hX : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) :
    StronglyAdapted F (globalProcess X c) :=
  fun t => stronglyAdapted_process hX hRight hLeft hc t t

noncomputable def globalSmallJumpResidual (X : Process Ω) (c : Real) : Process Ω :=
  fun t w => X t w - globalProcess X c t w

theorem globalSmallJumpResidual_jump_le
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X) (hc : 0 < c) (t : NNReal) (w : Ω) :
    |processLeftJump (globalSmallJumpResidual X c) t w| ≤ c := by
  by_cases ht : t = 0
  · subst t
    simpa only [processLeftJump,
      leftLim_eq_of_isBot (show IsBot (0 : NNReal) from isBot_bot), sub_self, abs_zero]
      using hc.le
  have htpos : 0 < t := bot_lt_iff_ne_bot.mpr ht
  let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have heq : (fun s => smallJumpResidual X c t s w) =ᶠ[𝓝[<] t]
      fun s => globalSmallJumpResidual X c s w := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    dsimp only [smallJumpResidual, globalSmallJumpResidual]
    rw [globalProcess_eq_on_horizon hRight hLeft hc (show s < t from hs).le w]
  have hlim := (smallJumpResidual_hasLeftLimits hRight hLeft hc w t).congr' heq
  have hj : processLeftJump (globalSmallJumpResidual X c) t w =
      processLeftJump (smallJumpResidual X c t) t w := by
    unfold processLeftJump
    rw [leftLim_eq_of_tendsto hlim]
    rfl
  rw [hj]
  exact abs_smallJumpResidual_processLeftJump_le hRight hLeft hc ⟨htpos, le_rfl⟩

end FTAPTheorem42.FiniteLargeJumpProcess
