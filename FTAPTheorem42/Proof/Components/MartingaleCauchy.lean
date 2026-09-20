/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.EmeryAlgebra
import FTAPTheorem42.Interface.PrefixEnergy
import FTAPTheorem42.Proof.Components.TailTests
import FTAPTheorem42.Proof.Components.CommonConvexification

/-! # DS Lemma 4.10: one convexification of the original martingale components -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Choose common Hilbert weights and consume the main proof's uniform tail estimate. -/
theorem exists_original_martingale_convexification
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → OriginalSpecialGain source Q) (q : Ω → Real) (hq : MemLp q 2 Q)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (H i).original.gain t ω)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ q ω) :
    ∃ w : ∀ n, TailConvexWeights n,
      ElementaryEmeryCauchy Q F
        (fun n => (w n).applyVector (fun i => (H i).decomposition.N)) := by
  let M := fun i => (H i).decomposition.N
  let P := fun (i j : Nat) => absolutePassagePrefix (M i) (j + 1 : Real) (j + 1 : NNReal)
  let B := fun (j : Nat) => (ENNReal.ofReal (j + 1 : Real) + 6 * eLpNorm q 2 Q).toReal
  have hPrefix (i j : Nat) := originalGain_prefix_energy source hQμ hμQ hUsual (H i) q hq (hBound i)
    (j + 1 : Real) (by positivity) (j + 1 : NNReal) (by positivity)
  refine exists_common_martingale_convexification M P
    (fun i => (H i).decomposition.adaptedN)
    (fun i => (H i).decomposition.rightN)
    (fun i j => (hPrefix i j).1)
    (fun i j => (originalGain_prefix_regular source (H i) _ _).1)
    (fun i j => ?_) (fun i j => (hPrefix i j).2.1) B
    (fun _ => ENNReal.toReal_nonneg) (fun i j => ?_) ?_
  · exact (originalGain_prefix_regular source (H i) _ _).2
  · dsimp only [B]
    rw [ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by norm_num) hq.eLpNorm_ne_top⟩)]
    exact (hPrefix i j).2.2
  · intro T ε hε
    obtain ⟨c₀, hc₀, hTail⟩ := originalGain_tail_tests source hNFLVR hQμ hμQ hUsual H q hq hLower
      (fun i => by
        filter_upwards [hBound i] with ω hω
        exact fun t => (hω t).trans (le_abs_self _)) ε hε
    obtain ⟨j, hj⟩ := exists_nat_ge (max c₀ (T : Real))
    have hcj : c₀ ≤ (j + 1 : Real) :=
      (le_max_left _ _).trans (hj.trans (le_add_of_nonneg_right zero_le_one))
    have hTj : T ≤ (j + 1 : NNReal) := by
      exact_mod_cast (le_max_right c₀ (T : Real)).trans
        (hj.trans (le_add_of_nonneg_right zero_le_one))
    refine ⟨j, hTj, fun w J => ?_⟩
    by_cases hT : T = 0
    · simp only [hT, elementaryEmeryTestError_zero_horizon, integral_zero]
      exact hε.le
    · have hEstimate := hTail w (j + 1 : Real) hcj
        T (lt_of_le_of_ne bot_le (Ne.symm hT)) J
      have hPaths ω t (ht : t ≤ T) :
          (w.applyVector M - w.applyVector (fun i => P i j)) t ω =
            w.apply (fun i => absolutePassageTail (M i) (j + 1 : Real) t) ω := by
        simp only [Pi.sub_apply, TailConvexWeights.applyVector,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TailConvexWeights.apply]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_sub]
        exact congrArg (w.weight i * ·)
          (sub_absolutePassagePrefix_eq_tail (M i) _ _ t (ht.trans hTj) ω)
      have hErrors : elementaryEmeryTestError (w.applyVector M)
          (w.applyVector (fun i => P i j)) J T =
          elementaryEmeryTestError
            (fun t ω => w.apply (fun i => absolutePassageTail (M i) (j + 1 : Real) t) ω)
            0 J T := by
        rw [← elementaryEmeryTestError_sub_zero]
        funext ω
        exact elementaryEmeryTestError_congr_upto J T ω (hPaths ω) (fun _ _ => rfl)
      rw [hErrors]
      have hTailEq : w.applyVector (fun i => absolutePassageTail (H i).decomposition.N (j + 1 :
        Real)) =
          (fun t ω => w.apply (fun i => absolutePassageTail (M i) (j + 1 : Real) t) ω) := by
        funext t ω
        exact w.applyVector_process_apply _ t ω
      rwa [hTailEq] at hEstimate

end FTAPTheorem42.BoundedSourceIntegralMarket
