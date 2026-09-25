/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedSkeletonLimit
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Martingale.Regularization.MartingaleFactorialGridUpcrossing

/-!
# Almost-sure boundedness on the factorial skeleton

Every point of the canonical fixed-horizon skeleton occurs on one of the
global factorial grids stopped at that horizon.  Doob's square-integrable
factorial-grid envelope therefore bounds the martingale simultaneously at
all canonical skeleton times, without assuming that the original version has
right-continuous paths.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open FTAPTheorem42.FactorialChronologicalGrid.Martingale

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

omit [MeasurableSpace Omega] in
/-- Every point of the canonical fixed-horizon skeleton occurs on a global
factorial grid stopped at the same horizon. -/
theorem stoppedLimitSkeleton_mem_stoppedGrid_range
    (T : NNReal) (n : Nat) :
    (stoppedLimitSkeleton T n).1 ∈ Set.range
      (FactorialChronologicalGrid.stoppedGrid T
        (max (Nat.unpair n).1 (Nat.ceil T))).time := by
  let r := (Nat.unpair n).1
  let q := max r (Nat.ceil T)
  have hrq : r <= q := le_max_left _ _
  have hTq : Nat.ceil T <= q := le_max_right _ _
  have hRange : (stoppedLimitSkeleton T n).1 ∈
      Set.range (grid T q).time :=
    range_grid_mono T hrq (stoppedLimitSkeleton_mem_grid_range T n)
  obtain ⟨k, hk⟩ := hRange
  have hkLe : k.1 <= size T q := Nat.le_of_lt_succ k.2
  have hSizeLe : size T q <= q * q.factorial := by
    unfold size
    exact Nat.mul_le_mul_right q.factorial hTq
  let l : Fin (q * q.factorial + 1) :=
    ⟨k.1, Nat.lt_succ_of_le (hkLe.trans hSizeLe)⟩
  refine ⟨l, ?_⟩
  change min ((k.1 : NNReal) / (q.factorial : NNReal)) T =
    (stoppedLimitSkeleton T n).1
  exact hk

omit [MeasurableSpace Omega] in
/-- Each canonical skeleton value is bounded by one level of the global
factorial running maximum. -/
theorem abs_stoppedLimitSkeleton_le_factorialRunningMax
    (M : Process Omega) (T : NNReal) (n : Nat) (omega : Omega) :
    |M (stoppedLimitSkeleton T n).1 omega| <=
      FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T
        (max (Nat.unpair n).1 (Nat.ceil T)) omega := by
  let q := max (Nat.unpair n).1 (Nat.ceil T)
  obtain ⟨l, hl⟩ := stoppedLimitSkeleton_mem_stoppedGrid_range T n
  have hValue :
      |M (stoppedLimitSkeleton T n).1 omega| =
        (FactorialChronologicalGrid.stoppedGrid T q).natSample
          (fun t omega => |M t omega|) l.1 omega := by
    simp only [ChronologicalGrid.natSample,
      ChronologicalGrid.sampledTime_fin_eq]
    rw [hl]
  rw [hValue]
  exact (Finset.le_sup' (fun j =>
    (FactorialChronologicalGrid.stoppedGrid T q).natSample
      (fun t omega => |M t omega|) j omega)
    (Finset.mem_range.2 l.2))

/-- Outside one null set, the martingale is bounded simultaneously at all
canonical skeleton times of a fixed horizon. -/
theorem Martingale.exists_abs_stoppedLimitSkeleton_le_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu, ∃ C : Real, ∀ n,
      |M (stoppedLimitSkeleton T n).1 omega| <= C := by
  let Z := FactorialChronologicalGrid.eFactorialRunningMaxSqEnvelope
    (fun t omega => |M t omega|) T
  filter_upwards
    [eFactorialRunningMaxSqEnvelope_abs_ae_lt_top hM T hterminal]
      with omega hZ
  refine ⟨Real.sqrt (Z omega).toReal, fun n => ?_⟩
  let q := max (Nat.unpair n).1 (Nat.ceil T)
  have hMax := abs_stoppedLimitSkeleton_le_factorialRunningMax
    M T n omega
  have hMaxNonneg : 0 <=
      FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T q omega := by
    unfold FactorialChronologicalGrid.factorialRunningMax
    exact finiteRunningMax_nonneg _ _ (fun _ _ => abs_nonneg _) omega
  have hSquare : ENNReal.ofReal
      (|M (stoppedLimitSkeleton T n).1 omega| ^ 2) <= Z omega := by
    refine (ENNReal.ofReal_le_ofReal <|
      (sq_le_sq₀ (abs_nonneg _) hMaxNonneg).2 hMax).trans ?_
    exact le_iSup (fun r => ENNReal.ofReal
      ((FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T r omega) ^ 2)) q
  apply Real.le_sqrt_of_sq_le
  have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hZ.ne).2
    hSquare
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hReal

/-- The two pathwise inputs for dense-skeleton regularization hold on one
common full-measure set: boundedness and finite rational upcrossings. -/
theorem Martingale.factorialSkeleton_regularizationInputs_ae
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu,
      (∃ C : Real, ∀ n,
        |M (stoppedLimitSkeleton T n).1 omega| <= C) ∧
      ∀ a b : Rat, a < b ->
        martingaleFactorialGridUpcrossings M T a b omega < ∞ := by
  filter_upwards
    [Martingale.exists_abs_stoppedLimitSkeleton_le_ae hM T hterminal,
      Martingale.martingaleFactorialGridUpcrossings_rat_ae_lt_top hM T]
      with omega hBounded hUpcrossings
  exact ⟨hBounded, hUpcrossings⟩

end HorizonFactorialGrid

end FTAPTheorem42
