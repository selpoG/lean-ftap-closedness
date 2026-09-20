/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Interface.MartingaleApproximation
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Foundations.ConvexProcesses
import FTAPTheorem42.Foundations.RightContinuousProgressive

/-! # DS Lemma 4.10: one convexification for all stopped coordinates

The proof chooses common forward weights in a countable Hilbert product.
Small convex tails then transfer the prefix Cauchy estimate to the original
components. No selection or Cauchy conclusion is part of the analytic input.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Common Hilbert weights and uniform convex-tail approximation yield
Émery Cauchy martingale components. The sequence cutoff precedes the test. -/
theorem exists_common_martingale_convexification
    (M : Nat → Process Ω) (P : Nat → Nat → Process Ω)
    (hMA : ∀ i, StronglyAdapted F (M i))
    (hMR : ∀ i ω t, ContinuousWithinAt (M i · ω) (Ici t) t)
    (hPM : ∀ i j, Martingale (P i j) F μ)
    (hPR : ∀ i j ω t, ContinuousWithinAt (P i j · ω) (Ici t) t)
    (hP0 : ∀ i j, P i j 0 =ᵐ[μ] 0)
    (hMem : ∀ i j, MemLp (P i j (j + 1 : NNReal)) 2 μ)
    (B : Nat → Real) (hB : ∀ j, 0 ≤ B j)
    (hBound : ∀ i j, eLpNorm (P i j (j + 1 : NNReal)) 2 μ ≤ ENNReal.ofReal (B j))
    (hApprox : ∀ T : NNReal, ∀ ε : Real, 0 < ε → ∃ j : Nat,
      T ≤ (j + 1 : NNReal) ∧
        ∀ (w : TailConvexWeights 0) (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F),
          (∫ ω, elementaryEmeryTestError (w.applyVector M)
            (w.applyVector (fun i => P i j)) J T ω ∂μ) ≤ ε) :
    ∃ w : ∀ n, TailConvexWeights n,
      ElementaryEmeryCauchy μ F (fun n => (w n).applyVector M) := by
  let Z := fun i j => (hMem i j).toLp (P i j (j + 1 : NNReal))
  have hZ i j : ‖Z i j‖ ≤ B j := by
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBound i j)).trans
      (by rw [ENNReal.toReal_ofReal (hB j)])
  obtain ⟨w, y, _, hConv⟩ :=
    DirectSumCoordinateControl.exists_common_tailConvexification_of_finite_coordinateBounds
      B Z hB hZ
  let X := fun n => (w n).applyVector M
  have hXR n := (w n).applyVector_rightContinuous M hMR
  have hXP n : IsStronglyProgressive F (X n) :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      ((w n).applyVector_stronglyAdapted M hMA) (hXR n)
  refine ⟨w, AnalyticInterface.emeryCauchy_of_uniform_approximations hXP ?_⟩
  intro T ε hε
  obtain ⟨j, hTj, hError⟩ := hApprox T ε hε
  let Y := fun n => (w n).applyVector (fun i => P i j)
  have hYM n : Martingale (Y n) F μ :=
    (w n).applyVector_martingale _ (fun i => hPM i j)
  have hYR n := (w n).applyVector_rightContinuous _ (fun i => hPR i j)
  have hYP n : IsStronglyProgressive F (Y n) :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous (hYM n).stronglyAdapted (hYR n)
  have hYZ n : ⇑((w n).applyVector (fun i => Z i j)) =ᵐ[μ] Y n (j + 1 : NNReal) := by
    filter_upwards [(w n).applyVector_coeFn_ae (fun i => Z i j)
      (fun i => P i j (j + 1 : NNReal)) (fun i => (hMem i j).coeFn_toLp)] with ω hω
    exact hω.trans ((w n).applyVector_process_apply _ _ ω).symm
  have hCauchy := AnalyticInterface.martingaleTestsCauchy_of_terminalL2 hYM hYR
    (fun n => (w n).applyVector_zero_ae _ (fun i => hP0 i j)) (j + 1 : NNReal)
    (fun n => (w n).applyVector (fun i => Z i j)) hYZ (hConv j).cauchySeq
  refine ⟨Y, hYP, fun n J => hError ((w n).mono (Nat.zero_le n)) J, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := hCauchy δ hδ
  exact ⟨N, fun n hn k hk J => hN n hn k hk T hTj J⟩

end FTAPTheorem42
