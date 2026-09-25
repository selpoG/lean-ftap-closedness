/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcess
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import FTAPTheorem42.Stochastic.Process.CadlagLargeJumpPath
import FTAPTheorem42.Stochastic.Process.FactorialCellJumpLimit

/-! # Jump summability and Stieltjes series for càdlàg finite-variation paths

Finite path variation bounds the absolute jump sum. Countable-support
integration then identifies Stieltjes integrals with their jump series.
-/

/-! ## Absolute summability on finite horizons -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42.FiniteVariationPath

/-- The absolute jump masses on a finite horizon are summable and bounded
by path variation. The index is time itself, so no enumeration is chosen. -/
theorem summable_abs_leftJump_Ioc
    {A : NNReal → Real} (hA : BoundedVariationOn A univ)
    (hRight : ∀ t, ContinuousWithinAt A (Ici t) t) (T : NNReal) :
    Summable (fun t : Ioc (0 : NNReal) T => |A t - Function.leftLim A t|) ∧
      (∑' t : Ioc (0 : NNReal) T, |A t - Function.leftLim A t|) ≤
        variationOnFromTo A univ 0 T := by
  classical
  let ν := (signedMeasure hA).totalVariation
  have hAtom : ∀ t, |A t - Function.leftLim A t| = ν.real {t} := by
    intro t
    rw [signedMeasure_totalVariation_real_singleton, signedMeasure_singleton hA hRight]
  have hBound : ∀ s : Finset (Ioc (0 : NNReal) T),
      ∑ t ∈ s, |A t - Function.leftLim A t| ≤ variationOnFromTo A univ 0 T := by
    intro s
    simp_rw [hAtom]
    have hSum : (∑ t ∈ s.image Subtype.val, ν.real {t}) = ∑ t ∈ s, ν.real {t.val} :=
      Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)
    rw [← hSum, sum_measureReal_singleton]
    rw [variationOnFromTo_eq_totalVariation_Ioc hA hRight (show (0 : NNReal) ≤ T from bot_le)]
    refine measureReal_mono ?_ (measure_ne_top ν _)
    intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact u.property
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hBound,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hBound⟩

end FTAPTheorem42.FiniteVariationPath

namespace FTAPTheorem42

/-- Deterministic stopping extends the jump-sum estimate to locally
finite-variation processes, with the original path variation as bound. -/
theorem summable_abs_processLeftJump_Ioc
    {Ω : Type*} (Q : Process Ω)
    (hBV : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ)
    (hRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t)
    (hLeft : ProcessHasLeftLimits Q) (T : NNReal) (omega : Ω) :
    Summable (fun t : Ioc (0 : NNReal) T => |processLeftJump Q t omega|) ∧
      (∑' t : Ioc (0 : NNReal) T, |processLeftJump Q t omega|) ≤
        variationOnFromTo (Q · omega) univ 0 T := by
  let rho : Ω → WithTop NNReal := fun _ => T
  let S := stoppedProcess Q rho
  have hPath : (S · omega) = FiniteVariationStoppedPath.stopAt (Q · omega) T := by
    funext t
    exact stoppedProcess_const_apply Q T t omega
  have hS := FiniteVariationPath.summable_abs_leftJump_Ioc
    (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (hBV omega) T)
    (FiniteVariationStoppedPath.rightContinuous_stopAt (Q · omega) (hRight omega) T) T
  rw [← hPath] at hS
  have hJump : ∀ t : Ioc (0 : NNReal) T,
      S t omega - Function.leftLim (S · omega) t = processLeftJump Q t omega := by
    intro t
    exact processLeftJump_stoppedProcess_eq_of_le Q hLeft rho t omega
      (WithTop.coe_le_coe.mpr t.property.2)
  simp_rw [hJump] at hS
  rw [hPath, FiniteVariationStoppedPath.variationOnFromTo_stopAt, min_self] at hS
  exact hS

end FTAPTheorem42

/-! ## Stieltjes integrals as jump series -/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped Topology

theorem signedIntegral_eq_tsum_of_countable_support
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (η : SignedMeasure α) (f : α → Real)
    (hCount : (Function.support f).Countable) (hInt : η.Integrable f) :
    (∫ᵛ t, f t ∂•η) = ∑' t, f t * η {t} := by
  classical
  let S := Function.support f
  have : Countable S := hCount.to_subtype
  have hUnion : (⋃ t : S, ({t.val} : Set α)) = S := by simp
  have hSum := VectorMeasure.integral_iUnion (μ := η)
    (B := ContinuousLinearMap.lsmul Real Real)
    (s := fun t : S => ({t.val} : Set α))
    (fun _ => measurableSet_singleton _)
    (fun i j hij => disjoint_singleton.mpr (fun h => hij (Subtype.ext h)))
    hInt.integrableOn
  rw [hUnion] at hSum
  have hIndicator : S.indicator f = f := indicator_support
  rw [← VectorMeasure.integral_indicator hCount.measurableSet, hIndicator] at hSum
  rw [hSum]
  simp only [VectorMeasure.integral_singleton, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply tsum_subtype_eq_of_support_subset (f := fun t => f t * η {t}) (s := S)
  intro t ht
  exact fun hf => ht (by simp [hf])

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Countable support of càdlàg jumps on a finite horizon -/

open Filter MeasureTheory Set Topology
open scoped NNReal

theorem countable_leftJump_support_Ioc
    (f : NNReal → Real)
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t))) (T : NNReal) :
    (Function.support ((Ioc (0 : NNReal) T).indicator
      (fun t => f t - Function.leftLim f t))).Countable := by
  classical
  apply (countable_iUnion (fun n : Nat =>
    (finite_largeJumpTimeSet hRight hLeft
      (by positivity : 0 < (1 : Real) / (n + 1)) T).countable)).mono
  intro t ht
  have ht' : t ∈ Ioc (0 : NNReal) T ∧ f t - Function.leftLim f t ≠ 0 := by
    simpa only [support_indicator, mem_inter_iff, Function.mem_support] using ht
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr ht'.2)
  exact mem_iUnion.mpr ⟨n, ht'.1, hn⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Stieltjes integrals of càdlàg jumps are jump series -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LeftContinuousPredictable

private theorem integrable_leftJump_indicator
    (f : NNReal → Real)
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (T : NNReal) (ν : Measure NNReal) [IsFiniteMeasure ν] :
    Integrable ((Ioc (0 : NNReal) T).indicator
      (fun t => f t - Function.leftLim f t)) ν := by
  classical
  let g := (Ioc (0 : NNReal) T).indicator (fun t => f t - Function.leftLim f t)
  let G := fun r => (Ioc (0 : NNReal) T).indicator (cellIncrement f T r)
  have hLimit : ∀ s, Tendsto (fun r => G r s) atTop (𝓝 (g s)) := by
    intro s
    by_cases hs : s ∈ Ioc (0 : NNReal) T
    · simpa only [G, g, indicator_of_mem hs] using tendsto_cellIncrement f hRight hLeft hs
    · simp only [G, g, indicator_of_notMem hs]
      exact tendsto_const_nhds
  have hMeas : AEStronglyMeasurable g ν := aestronglyMeasurable_of_tendsto_ae atTop
    (fun r => ((cellIncrement_measurable f T r).indicator measurableSet_Ioc).aestronglyMeasurable)
    (Eventually.of_forall hLimit)
  obtain ⟨C, hC⟩ :=
    FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits
      f hRight hLeft T
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 bot_le)
  refine (integrable_const (2 * C)).mono' hMeas (Eventually.of_forall (fun s => ?_))
  apply le_of_tendsto (hLimit s).norm
  apply Eventually.of_forall
  intro r
  by_cases hs : s ∈ Ioc (0 : NNReal) T
  · simp only [G, indicator_of_mem hs, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by
      linarith [hC (min (gridPoint r (leftIndex r s + 1)) T) (min_le_right _ _),
        hC (min (approx r s) T) (min_le_right _ _)])
  · simp only [G, indicator_of_notMem hs, norm_zero]
    positivity

/-- Time itself indexes the series; no enumeration or exceptional-time
representative is chosen. -/
theorem setIntegral_leftJump_eq_tsum
    (f : NNReal → Real)
    (hRight : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t, Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (T : NNReal) (η : SignedMeasure NNReal) :
    (∫ᵛ t in Ioc (0 : NNReal) T, f t - Function.leftLim f t ∂•η) =
      ∑' t : Ioc (0 : NNReal) T, (f t - Function.leftLim f t) * η {t.val} := by
  classical
  have hInt : η.Integrable ((Ioc (0 : NNReal) T).indicator
      (fun t => f t - Function.leftLim f t)) := by
    change Integrable _ η.variation
    rw [← signedMeasure_totalVariation_eq_variation]
    exact integrable_leftJump_indicator f hRight hLeft T η.totalVariation
  rw [← VectorMeasure.integral_indicator measurableSet_Ioc,
    signedIntegral_eq_tsum_of_countable_support η _
      (countable_leftJump_support_Ioc f hRight hLeft T) hInt,
    tsum_subtype (Ioc (0 : NNReal) T) (fun t => (f t - Function.leftLim f t) * η {t})]
  apply tsum_congr
  intro t
  by_cases ht : t ∈ Ioc (0 : NNReal) T <;> simp [ht]

/-- The atoms of the stopped finite-variation integrator are the original
process jumps throughout the closed horizon, including its terminal jump. -/
theorem setIntegral_processLeftJump_eq_tsum
    {Ω : Type*} [MeasurableSpace Ω] (X Q : Process Ω)
    (hRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (hQRight : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t)
    (hQLeft : ProcessHasLeftLimits Q)
    (hQ : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ) (T : NNReal) (omega : Ω) :
    (∫ᵛ t in Ioc (0 : NNReal) T, processLeftJump X t omega
      ∂•(FiniteVariationPath.signedMeasure
        (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
          (hQ omega) T))) =
      ∑' t : Ioc (0 : NNReal) T, processLeftJump X t omega * processLeftJump Q t omega := by
  let rho : Ω → WithTop NNReal := fun _ => T
  let S := stoppedProcess Q rho
  have hPath : (S · omega) = FiniteVariationStoppedPath.stopAt (Q · omega) T := by
    funext t
    exact stoppedProcess_const_apply Q T t omega
  have hBV :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn (hQ omega) T
  have hSR := FiniteVariationStoppedPath.rightContinuous_stopAt (Q · omega) (hQRight omega) T
  change (∫ᵛ t in Ioc (0 : NNReal) T, X t omega - Function.leftLim (X · omega) t
    ∂•(FiniteVariationPath.signedMeasure hBV)) = _
  rw [setIntegral_leftJump_eq_tsum (X · omega) (hRight omega) (hLeft omega)]
  apply tsum_congr
  intro t
  rw [FiniteVariationPath.signedMeasure_singleton hBV hSR]
  rw [← hPath]
  have hJump : S t omega - Function.leftLim (S · omega) t = processLeftJump Q t omega :=
    processLeftJump_stoppedProcess_eq_of_le Q hQLeft rho t omega
      (WithTop.coe_le_coe.mpr t.property.2)
  rw [hJump]
  rfl

end FTAPTheorem42
