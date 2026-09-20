/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticGridEnergy
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGate

/-! # Convergence of the original, unconvexified quadratic approximation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.BoundedMartingaleQuadraticApproximation

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {M : Process Ω} {T : NNReal}

theorem martingalePart_terminal_tendsto_Lp
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {C : NNReal} (hBound : ∀ t, t ≤ T → ∀ w, |M t w| ≤ C) :
    ∃ hPart : MemLp (D.martingalePart T) (2 : ENNReal) mu,
      Tendsto (fun n =>
        (martingalePart_terminal_memLp_two hM hRight T hMT
          (fun t ht => Eventually.of_forall (hBound t ht)) n).toLp (martingalePart M T n T))
        atTop (𝓝 (hPart.toLp (D.martingalePart T))) := by
  let H := fun n => gridStrategy hM.stronglyAdapted T n
  let B : Nat → NNReal := fun n => ((level T n) * (level T n).factorial : Nat) * C
  have hB : ∀ n w, (H n).coefficientAbsSum w ≤ B n :=
    fun n => gridStrategy_bound hM.stronglyAdapted T n hBound
  let g := fun n => ElementaryStrategy.gain M (H n).toElementary T
  have hg := fun n => (H n).gain_memLp_two M hM hRight T hMT (B n) (hB n)
  let G := fun n => (hg n).toLp (g n)
  have hG : CauchySeq G := gridStrategy_terminal_cauchy D hM hRight hLeft hMT hBound
  let P := fun n => martingalePart M T n T
  have hP : ∀ n, MemLp (P n) (2 : ENNReal) mu := fun n =>
    martingalePart_terminal_memLp_two hM hRight T hMT
      (fun t ht => Eventually.of_forall (hBound t ht)) n
  let Z := fun n => (hP n).toLp (P n)
  have hZEq (n : Nat) : Z n = (2 : Real) • G n := by
    have hEq : P n = (2 : Real) • g n := gridStrategy_gain hM.stronglyAdapted T n
    exact (MemLp.toLp_congr (hP n) ((hg n).const_smul (2 : Real))
      (Eventually.of_forall (congrFun hEq))).trans (MemLp.toLp_const_smul 2 (hg n))
  let Y : Lp Real (2 : ENNReal) mu := (2 : Real) • limUnder atTop G
  have hZ : Tendsto Z atTop (𝓝 Y) := by
    exact (hG.tendsto_limUnder.const_smul (2 : Real)).congr'
      (Eventually.of_forall (fun n => (hZEq n).symm))
  have hConv : Tendsto (fun k => (D.weights (D.cutoff k)).applyVector Z) atTop (𝓝 Y) :=
    (HorizonFactorialGrid.TailConvexWeights.tendsto_applyVector D.weights hZ).comp
      D.cutoff_strictMono.tendsto_atTop
  have hConvRaw := (tendstoInMeasure_of_tendsto_Lp hConv).congr_left (fun k =>
    (D.weights (D.cutoff k)).applyVector_coeFn_ae Z P (fun n => (hP n).coeFn_toLp))
  have hStored : TendstoInMeasure mu
      (fun k => (D.weights (D.cutoff k)).apply P) atTop (D.martingalePart T) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro k
      exact ((D.weights (D.cutoff k)).apply_stronglyMeasurable
        (fun n => ((martingalePart_isMartingale hM hRight T
          (fun t ht => Eventually.of_forall (hBound t ht)) n).stronglyAdapted T).mono
            (F.le T))).aestronglyMeasurable
    · filter_upwards [D.martingalePart_uniform] with w hw
      simpa only [BoundedMartingaleQuadraticConvexification.martingalePart_apply] using
        hw.tendsto_at T
  have hEq : (Y : Ω → Real) =ᵐ[mu] D.martingalePart T :=
    tendstoInMeasure_ae_unique hConvRaw hStored
  have hPart : MemLp (D.martingalePart T) (2 : ENNReal) mu := (Lp.memLp Y).ae_eq hEq
  have hPartEq : hPart.toLp (D.martingalePart T) = Y :=
    (MemLp.toLp_congr hPart (Lp.memLp Y) hEq.symm).trans (Lp.toLp_coeFn Y (Lp.memLp Y))
  exact ⟨hPart, by simpa only [hPartEq] using hZ⟩

theorem squaredIncrementPart_terminal_tendsto_eLpNorm_two
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {C : NNReal} (hBound : ∀ t, t ≤ T → ∀ w, |M t w| ≤ C) :
    Tendsto (fun n => eLpNorm
      (squaredIncrementPart M T n T - D.variation T) (2 : ENNReal) mu) atTop (𝓝 0) := by
  obtain ⟨hPart, hLimit⟩ := martingalePart_terminal_tendsto_Lp D hM hRight hLeft hMT hBound
  have hP := fun n => martingalePart_terminal_memLp_two hM hRight T hMT
    (fun t ht => Eventually.of_forall (hBound t ht)) n
  have hRaw := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => martingalePart M T n T) hP (D.martingalePart T) hPart).mp hLimit
  apply hRaw.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [← eLpNorm_neg]
  apply eLpNorm_congr_ae
  filter_upwards [D.variation_indistinguishable_raw] with w hw
  have h := martingalePart_add_squaredIncrementPart M T T n w
  have hV := hw T
  change D.variation T w = deterministicallyStoppedProcess M T T w ^ 2 -
    deterministicallyStoppedProcess M T 0 w ^ 2 - D.martingalePart T w at hV
  change -(martingalePart M T n T w - D.martingalePart T w) =
    squaredIncrementPart M T n T w - D.variation T w
  linarith

end FTAPTheorem42.BoundedMartingaleQuadraticApproximation
