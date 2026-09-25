/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Memin.SummableComponentLimitData
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableLocalMartingaleL2Control
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit
import FTAPTheorem42.Stochastic.Process.UniformProcessLimitUniqueness
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticProcessLimit
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableActualScalarCalculus
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge

/-!
# A joint passage localizer for the Mémín approximants

At one increasing passage level, take the infimum of the individual
martingale passages of every approximant, and then intersect it with the
source-martingale passage.  The resulting stopping time lies below all the
stops needed for the finite-horizon `M²` estimates.

The countable infimum still tends to infinity.  The essential point is a
compact-horizon bound uniform in the approximant index, obtained from the
already-proved pathwise uniform convergence of the Mémín martingale
components.  Merely knowing that every individual passage exceeds a fixed
time would not suffice, since their infimum could equal that time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace MeminSummableComponentLimitData

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {R : SIntegrableRealizationModel D}
  {G : ActualLocallySIntegrableStrategy R}

/-- The clamped own-martingale passage of one Mémín approximant at the
canonical level and horizon of coordinate `n`. -/
noncomputable def approximantPassageUpTo
    (data : MeminSummableComponentLimitData R) (n k : Nat) :
    Omega -> WithTop NNReal :=
  SIntegrableProcessStoppingCalculus.lemma410PrefixPassageUpTo
    (data.approximant k).val (cadlagPassageLevel n)
      (cadlagPassageHorizon n)

/-- The countable infimum of all approximant passages at one coordinate. -/
noncomputable def allApproximantsPassage
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    Omega -> WithTop NNReal :=
  fun omega => ⨅ k, data.approximantPassageUpTo n k omega

theorem approximantPassageUpTo_isStoppingTime
    (data : MeminSummableComponentLimitData R) (n k : Nat) :
    IsStoppingTime F (data.approximantPassageUpTo n k) :=
  SIntegrableProcessStoppingCalculus.lemma410PrefixPassageUpTo_isStoppingTime
    (data.approximant k).val (cadlagPassageLevel n)
      (cadlagPassageHorizon n)

theorem allApproximantsPassage_isStoppingTime
    (data : MeminSummableComponentLimitData R) (n : Nat) :
    IsStoppingTime F (data.allApproximantsPassage n) := by
  exact IsStoppingTime.iInf fun k =>
    data.approximantPassageUpTo_isStoppingTime n k

omit [F.IsRightContinuous] in
theorem approximantPassageUpTo_le_horizon
    (data : MeminSummableComponentLimitData R) (n k : Nat) (omega : Omega) :
    data.approximantPassageUpTo n k omega <=
      (cadlagPassageHorizon n : WithTop NNReal) :=
  min_le_right _ _

omit [F.IsRightContinuous] in
theorem approximantPassageUpTo_mono
    (data : MeminSummableComponentLimitData R) (k : Nat) :
    Monotone fun n => data.approximantPassageUpTo n k := by
  intro n m hnm omega
  apply min_le_min
  · unfold SIntegrableProcessStoppingCalculus.lemma48FirstPassage
      absoluteStrictHittingAfter
      RightContinuousHittingTime.strictHittingAfter
    apply MeasureTheory.hittingAfter_anti
    intro x hx
    exact (cadlagPassageLevel_monotone hnm).trans_lt hx
  · exact WithTop.coe_le_coe.mpr (cadlagPassageHorizon_monotone hnm)

omit [F.IsRightContinuous] in
theorem allApproximantsPassage_mono
    (data : MeminSummableComponentLimitData R) :
    Monotone data.allApproximantsPassage := by
  intro n m hnm omega
  apply iInf_mono
  intro k
  exact data.approximantPassageUpTo_mono k hnm omega

omit [F.IsRightContinuous] in
/-- Pathwise uniform convergence of the Mémín martingale components gives
a bound which is uniform in the approximant index on every compact time
interval. -/
theorem exists_approximantMartingale_abs_le_on_Icc
    (data : MeminSummableComponentLimitData R) (omega : Omega)
    (hUniform : TendstoUniformly
      (fun k t => (data.approximant k).val.martingalePart t omega)
      (fun t => data.martingaleLimit t omega) atTop)
    (T : NNReal) :
    exists B : Real, forall k t, t <= T ->
      abs ((data.approximant k).val.martingalePart t omega) <= B := by
  have hEach : forall k, exists B : Real, forall t, t <= T ->
      abs ((data.approximant k).val.martingalePart t omega) <= B := by
    intro k
    exact
      FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits
        ((data.approximant k).val.martingalePart · omega)
        ((data.approximant k).val.martingalePart_isRightContinuous omega)
        (data.approximant_martingaleLeft k omega) T
  choose bound hBound using hEach
  have hCloseEventually : ∀ᶠ k in atTop, forall t,
      dist ((data.approximant k).val.martingalePart t omega)
        (data.martingaleLimit t omega) < 1 :=
    ((Metric.tendstoUniformly_iff.mp hUniform) 1 zero_lt_one).mono
      fun _ hk t => by simpa only [dist_comm] using hk t
  obtain ⟨K, hClose⟩ := eventually_atTop.1 hCloseEventually
  let c : Nat -> Real := fun k => max (bound k) 0
  let B : Real := (∑ k ∈ Finset.range (K + 1), c k) + 2
  have hc_nonnegative : forall k, 0 <= c k := fun k => le_max_right _ _
  have hc_le_sum : forall {k}, k < K + 1 ->
      c k <= ∑ i ∈ Finset.range (K + 1), c i := by
    intro k hk
    exact Finset.single_le_sum (fun i _ => hc_nonnegative i)
      (Finset.mem_range.2 hk)
  refine ⟨B, ?_⟩
  intro k t ht
  by_cases hk : k < K
  · calc
      abs ((data.approximant k).val.martingalePart t omega) <=
          bound k := hBound k t ht
      _ <= c k := le_max_left _ _
      _ <= ∑ i ∈ Finset.range (K + 1), c i :=
        hc_le_sum (hk.trans_le (Nat.le_succ K))
      _ <= B := le_add_of_nonneg_right (by norm_num)
  · have hk_ge : K <= k := le_of_not_gt hk
    have hk_close := hClose k hk_ge t
    have hK_close := hClose K le_rfl t
    have hdiff :
        abs ((data.approximant k).val.martingalePart t omega -
          (data.approximant K).val.martingalePart t omega) < 2 := by
      calc
        abs ((data.approximant k).val.martingalePart t omega -
            (data.approximant K).val.martingalePart t omega) =
            dist ((data.approximant k).val.martingalePart t omega)
              ((data.approximant K).val.martingalePart t omega) := by
                rw [Real.dist_eq]
        _ <= dist ((data.approximant k).val.martingalePart t omega)
              (data.martingaleLimit t omega) +
            dist (data.martingaleLimit t omega)
              ((data.approximant K).val.martingalePart t omega) :=
          dist_triangle _ _ _
        _ < 1 + 1 := add_lt_add hk_close (by
          simpa only [dist_comm] using hK_close)
        _ = 2 := by norm_num
    calc
      abs ((data.approximant k).val.martingalePart t omega) <=
          abs ((data.approximant K).val.martingalePart t omega) +
            abs ((data.approximant k).val.martingalePart t omega -
              (data.approximant K).val.martingalePart t omega) := by
        calc
          abs ((data.approximant k).val.martingalePart t omega) =
              abs ((data.approximant K).val.martingalePart t omega +
                ((data.approximant k).val.martingalePart t omega -
                  (data.approximant K).val.martingalePart t omega)) := by
            congr 1
            ring
          _ <= _ := abs_add_le _ _
      _ <= c K + 2 := add_le_add
        ((hBound K t ht).trans (le_max_left _ _)) hdiff.le
      _ <= B := by
        simpa only [B, add_comm] using
          add_le_add_right (hc_le_sum (Nat.lt_succ_self K)) 2

omit [F.IsRightContinuous] in
/-- Once the canonical level dominates a common compact-horizon bound, every
approximant passage lies strictly beyond the tested time. -/
theorem eventually_lt_allApproximantsPassage
    (data : MeminSummableComponentLimitData R) (omega : Omega)
    (hUniform : TendstoUniformly
      (fun k t => (data.approximant k).val.martingalePart t omega)
      (fun t => data.martingaleLimit t omega) atTop)
    (t : NNReal) :
    ∀ᶠ n in atTop, (t : WithTop NNReal) <
      data.allApproximantsPassage n omega := by
  let U : NNReal := t + 1
  obtain ⟨B, hBound⟩ :=
    data.exists_approximantMartingale_abs_le_on_Icc omega hUniform U
  have hLevel : ∀ᶠ n in atTop, B < cadlagPassageLevel n :=
    cadlagPassageLevel_tendsto_atTop.eventually_gt_atTop B
  have hHorizon : ∀ᶠ n in atTop, U < cadlagPassageHorizon n :=
    cadlagPassageHorizon_tendsto_atTop.eventually_gt_atTop U
  filter_upwards [hLevel, hHorizon] with n hnLevel hnHorizon
  have hU_le_passage : forall k, (U : WithTop NNReal) <=
      data.approximantPassageUpTo n k omega := by
    intro k
    unfold approximantPassageUpTo
      SIntegrableProcessStoppingCalculus.lemma410PrefixPassageUpTo
    rw [le_min_iff]
    refine ⟨?_, WithTop.coe_le_coe.mpr hnHorizon.le⟩
    by_contra hnot
    have hHitLt :
        SIntegrableProcessStoppingCalculus.lemma48FirstPassage
          (data.approximant k).val (cadlagPassageLevel n) omega <
            (U : WithTop NNReal) := lt_of_not_ge hnot
    unfold SIntegrableProcessStoppingCalculus.lemma48FirstPassage
      absoluteStrictHittingAfter
      RightContinuousHittingTime.strictHittingAfter at hHitLt
    rw [MeasureTheory.hittingAfter_lt_iff] at hHitLt
    obtain ⟨u, hu, huLevel⟩ := hHitLt
    have huU : u <= U := hu.2.le
    exact (not_lt_of_ge (hBound k u huU)) (hnLevel.trans huLevel)
  rw [show data.allApproximantsPassage n omega =
      ⨅ k, data.approximantPassageUpTo n k omega by rfl]
  exact (show (t : WithTop NNReal) < (U : WithTop NNReal) by
    exact_mod_cast lt_add_one t).trans_le (le_iInf hU_le_passage)

end MeminSummableComponentLimitData

end FTAPTheorem42
