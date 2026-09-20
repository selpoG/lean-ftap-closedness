/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ElementaryPredictable
import Mathlib.Probability.Process.Stopping

/-!
# Process regularity of predictable elementary gains

This module connects predictable elementary interval integrals to the process
properties consumed by the compactness argument.  A coefficient is only
measurable at its random starting time.  At a deterministic time `t` we first
restrict it to `{start ≤ t}`; this restriction is `ℱ t`-measurable, while the
gain is identically zero on the complementary event.

Right continuity is pathwise and follows from right continuity of the price
path.  Since a strategy contains only finitely many finite stopping times, its
running gain is eventually exactly equal to its terminal gain on every path.
-/

open Filter MeasureTheory Topology

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]

namespace PredictableElementaryInterval

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

/--
A random variable measurable at `τ`, restricted to the event `{τ ≤ t}`, is
measurable at deterministic time `t`.
-/
theorem measurable_ite_le_of_stoppingTime
    (τ : Ω → WithTop Time) (hτ : IsStoppingTime ℱ τ)
    (f : Ω → ℝ) (hf : Measurable[hτ.measurableSpace] f)
    (t : Time) :
    Measurable[ℱ t]
      (fun ω => if τ ω ≤ t then f ω else 0) := by
  intro u hu
  have hfpre :
      MeasurableSet[hτ.measurableSpace] (f ⁻¹' u) :=
    hf hu
  have hinter :
      MeasurableSet[ℱ t]
        (f ⁻¹' u ∩ {ω | τ ω ≤ t}) :=
    hfpre.2 t
  have hle : MeasurableSet[ℱ t] {ω | τ ω ≤ t} :=
    hτ t
  by_cases hzero : (0 : ℝ) ∈ u
  · have heq :
        (fun ω => if τ ω ≤ t then f ω else 0) ⁻¹' u =
          (f ⁻¹' u ∩ {ω | τ ω ≤ t}) ∪
            {ω | τ ω ≤ t}ᶜ := by
      ext ω
      by_cases hω : τ ω ≤ t <;> simp [hω, hzero]
    rw [heq]
    exact hinter.union hle.compl
  · have heq :
        (fun ω => if τ ω ≤ t then f ω else 0) ⁻¹' u =
          f ⁻¹' u ∩ {ω | τ ω ≤ t} := by
      ext ω
      by_cases hω : τ ω ≤ t <;> simp [hω, hzero]
    rw [heq]
    exact hinter

/-- The coefficient activated after the block's starting time. -/
noncomputable def activeCoefficient
    (B : PredictableElementaryInterval ℱ)
    (t : Time) (ω : Ω) : ℝ :=
  if (B.interval.startTime ω : WithTop Time) ≤ t then
    B.interval.coefficient ω
  else 0

theorem activeCoefficient_stronglyMeasurable
    (B : PredictableElementaryInterval ℱ) (t : Time) :
    StronglyMeasurable[ℱ t] (B.activeCoefficient t) :=
  (measurable_ite_le_of_stoppingTime
    (fun ω => (B.interval.startTime ω : WithTop Time))
    B.startStopping B.interval.coefficient
    B.coefficient_measurable t).stronglyMeasurable

theorem gain_eq_activeCoefficient_mul_stoppedProcess_sub
    [Nonempty Time]
    (S : Time → Ω → ℝ)
    (B : PredictableElementaryInterval ℱ)
    (t : Time) (ω : Ω) :
    B.interval.gain S t ω =
      B.activeCoefficient t ω *
        (MeasureTheory.stoppedProcess S
            (fun x => (B.interval.stopTime x : WithTop Time)) t ω -
          MeasureTheory.stoppedProcess S
            (fun x => (B.interval.startTime x : WithTop Time)) t ω) := by
  by_cases hstart : B.interval.startTime ω ≤ t
  · have hstop :
        MeasureTheory.stoppedProcess S
            (fun x => (B.interval.stopTime x : WithTop Time)) t ω =
          S (min t (B.interval.stopTime ω)) ω := by
      simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min]
      rw [WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    have hstart' :
        MeasureTheory.stoppedProcess S
            (fun x => (B.interval.startTime x : WithTop Time)) t ω =
          S (min t (B.interval.startTime ω)) ω := by
      simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min]
      rw [WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
    rw [hstop, hstart']
    simp [activeCoefficient, hstart, ElementaryInterval.gain]
  · have htstart : t ≤ B.interval.startTime ω :=
      le_of_not_ge hstart
    have htstop : t ≤ B.interval.stopTime ω :=
      htstart.trans (B.interval.start_le_stop ω)
    simp [activeCoefficient, hstart, ElementaryInterval.gain,
      MeasureTheory.stoppedProcess, min_eq_left htstart,
      min_eq_left htstop]

section Adapted

variable [Nonempty Time]
  [PseudoMetricSpace Time] [OrderTopology Time]
  [MeasurableSpace Time] [BorelSpace Time]
  [SecondCountableTopology Time]

theorem stronglyAdapted_gain
    (S : Time → Ω → ℝ) (hS : IsStronglyProgressive ℱ S)
    (B : PredictableElementaryInterval ℱ) :
    StronglyAdapted ℱ (B.interval.gain S) := by
  have hstop :=
    hS.stronglyAdapted_stoppedProcess B.stopStopping
  have hstart :=
    hS.stronglyAdapted_stoppedProcess B.startStopping
  intro t
  have hprod :=
    (B.activeCoefficient_stronglyMeasurable t).mul
      ((hstop t).sub (hstart t))
  convert hprod using 1
  funext ω
  exact B.gain_eq_activeCoefficient_mul_stoppedProcess_sub S t ω

end Adapted

section RightContinuous

variable [TopologicalSpace Time] [OrderTopology Time]

private theorem continuousWithinAt_min_const_comp
    (f : Time → ℝ)
    (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (b t : Time) :
    ContinuousWithinAt (fun s => f (min s b)) (Set.Ici t) t := by
  have hmin :
      ContinuousWithinAt (fun s : Time => min s b)
        (Set.Ici t) t :=
    (continuous_id.min
      (continuous_const :
        Continuous (fun _ : Time => b))).continuousAt.continuousWithinAt
  have hmaps :
      Set.MapsTo (fun s : Time => min s b)
        (Set.Ici t) (Set.Ici (min t b)) :=
    fun s hs => min_le_min_right b hs
  have hcomp :=
    (hf (min t b)).tendsto.comp
      (hmin.tendsto_nhdsWithin hmaps)
  change Tendsto (fun s => f (min s b))
    (𝓝[Set.Ici t] t) (𝓝 (f (min t b)))
  exact hcomp

theorem rightContinuous_gain
    (S : Time → Ω → ℝ)
    (hS : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (B : PredictableElementaryInterval ℱ)
    (ω : Ω) (t : Time) :
    ContinuousWithinAt (B.interval.gain S · ω) (Set.Ici t) t := by
  have hstop :=
    continuousWithinAt_min_const_comp
      (S · ω) (hS ω) (B.interval.stopTime ω) t
  have hstart :=
    continuousWithinAt_min_const_comp
      (S · ω) (hS ω) (B.interval.startTime ω) t
  have hcont :=
    (hstop.sub hstart).const_mul (B.interval.coefficient ω)
  convert hcont using 1
  funext s
  rfl

end RightContinuous

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

section Adapted

variable [Nonempty Time]
  [PseudoMetricSpace Time] [OrderTopology Time]
  [MeasurableSpace Time] [BorelSpace Time]
  [SecondCountableTopology Time]

theorem stronglyAdapted_gain
    (S : Time → Ω → ℝ) (hS : IsStronglyProgressive ℱ S)
    (H : PredictableElementaryStrategy ℱ) :
    StronglyAdapted ℱ
      (ElementaryStrategy.gain S (toElementary H)) := by
  induction H with
  | nil =>
      exact fun _ => stronglyMeasurable_const
  | cons B H ih =>
      intro t
      change
        StronglyMeasurable[ℱ t]
          (fun ω =>
            B.interval.gain S t ω +
              ElementaryStrategy.gain S (toElementary H) t ω)
      exact (B.stronglyAdapted_gain S hS t).add (ih t)

end Adapted

section RightContinuous

variable [TopologicalSpace Time] [OrderTopology Time]

theorem rightContinuous_gain
    (S : Time → Ω → ℝ)
    (hS : ∀ ω t, ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (H : PredictableElementaryStrategy ℱ)
    (ω : Ω) (t : Time) :
    ContinuousWithinAt
      (ElementaryStrategy.gain S (toElementary H) · ω)
      (Set.Ici t) t := by
  induction H with
  | nil =>
      change
        ContinuousWithinAt (fun _ : Time => (0 : ℝ))
          (Set.Ici t) t
      exact continuousWithinAt_const
  | cons B H ih =>
      change
        ContinuousWithinAt
          (fun s =>
            B.interval.gain S s ω +
              ElementaryStrategy.gain S (toElementary H) s ω)
          (Set.Ici t) t
      exact (B.rightContinuous_gain S hS ω t).add ih

end RightContinuous

end PredictableElementaryStrategy

end FTAPTheorem42
