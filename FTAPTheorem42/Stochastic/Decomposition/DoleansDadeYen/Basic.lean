/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.HorizonResidual
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.CompensatorJumpBound

/-! # The all-time Doléans--Dade--Yen decomposition -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded-jump local martingale plus an adapted locally finite-variation
local martingale, for the same original source on the whole time axis. -/
structure DoleansDadeYenData
    (X : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (c : Real) where
  Q : Process Ω
  L : Process Ω
  Q_isLocalMartingale : LocalMartingale Q F mu
  L_isLocalMartingale : LocalMartingale L F mu
  Q_isStronglyAdapted : StronglyAdapted F Q
  L_isStronglyAdapted : StronglyAdapted F L
  Q_rightContinuous : ∀ omega t, ContinuousWithinAt (Q · omega) (Ici t) t
  L_rightContinuous : ∀ omega t, ContinuousWithinAt (L · omega) (Ici t) t
  Q_leftLimits : ProcessHasLeftLimits Q
  L_leftLimits : ProcessHasLeftLimits L
  Q_locallyBoundedVariation : ∀ omega, LocallyBoundedVariationOn (Q · omega) univ
  Q_zero : Q 0 = 0
  L_zero : L 0 = 0
  decomposition : X = fun t omega => L t omega + Q t omega
  L_jump_bound : ∀ᵐ omega ∂mu, ∀ t, |processLeftJump L t omega| ≤ 2 * c

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real}

/-- Construct the all-time decomposition, including its common-event jump
bound, from the original zero-initial càdlàg local martingale. -/
theorem exists_doleansDadeYenData
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hc : 0 < c) (hUsual : Filtration.UsualConditions mu F) :
    Nonempty (DoleansDadeYenData X F mu c) := by
  obtain ⟨P, Q, _, _, hPV, _, hPJ, hQA, hQM, hQR, hQL, hQZ, hQV, hSource⟩ :=
    exists_largeJumpHorizon_components hX hXAdapted hXRight hXLeft hXZero hc hUsual
  let L : Process Ω := fun t omega => X t omega - Q t omega
  have hLL : ProcessHasLeftLimits L := hXLeft.sub hQL
  have hPL : ProcessHasLeftLimits P :=
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      hPV
  let R : Nat → Process Ω := fun n =>
    FiniteLargeJumpProcess.smallJumpResidual X c (cadlagPassageHorizon n)
  have hRL : ∀ n, ProcessHasLeftLimits (R n) := fun _ =>
    FiniteLargeJumpProcess.smallJumpResidual_hasLeftLimits hXRight hXLeft hc
  have hStopJump : ∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ cadlagPassageHorizon n →
      processLeftJump L t omega = processLeftJump (R n) t omega + processLeftJump P t omega := by
    intro n
    let rho : Ω → WithTop NNReal := fun _ => cadlagPassageHorizon n
    have hStop : ProcessIndistinguishable mu (stoppedProcess L rho)
        (fun t omega => stoppedProcess (R n) rho t omega + stoppedProcess P rho t omega) := by
      filter_upwards [hSource] with omega hS
      intro t
      simp only [rho, stoppedProcess_const_apply]
      dsimp only [L, R, FiniteLargeJumpProcess.smallJumpResidual]
      rw [hS n t]
      ring
    filter_upwards [hStop.processLeftJump_eq_add ((hRL n).stoppedProcess rho)
      (hPL.stoppedProcess rho)] with omega hJ
    intro t ht
    have ht' : (t : WithTop NNReal) ≤ rho omega := WithTop.coe_le_coe.mpr ht
    simpa only [processLeftJump_stoppedProcess_eq_of_le L hLL rho t omega ht',
      processLeftJump_stoppedProcess_eq_of_le (R n) (hRL n) rho t omega ht',
      processLeftJump_stoppedProcess_eq_of_le P hPL rho t omega ht'] using hJ t
  have hJump : ∀ᵐ omega ∂mu, ∀ t, |processLeftJump L t omega| ≤ 2 * c := by
    filter_upwards [ae_all_iff.2 hStopJump, hPJ] with omega hS hP
    intro t
    by_cases ht : t = 0
    · subst t
      unfold processLeftJump
      rw [show Function.leftLim (fun s => L s omega) 0 = L 0 omega from
        leftLim_eq_of_isBot isBot_bot, sub_self, abs_zero]
      positivity
    · obtain ⟨n, hn⟩ := (cadlagPassageHorizon_tendsto_atTop.eventually_ge_atTop t).exists
      have hR : |processLeftJump (R n) t omega| ≤ c :=
        FiniteLargeJumpProcess.abs_smallJumpResidual_processLeftJump_le
          hXRight hXLeft hc ⟨(pos_iff_ne_zero).2 ht, hn⟩
      rw [hS n t hn]
      exact (abs_add_le _ _).trans (by linarith [hP t])
  refine ⟨{
    Q := Q, L := L
    Q_isLocalMartingale := hQM
    L_isLocalMartingale := by
      simpa only [L, sub_eq_add_neg] using hX.add_of_rightContinuous hQM.neg hXRight
        (fun omega t => (hQR omega t).neg)
    Q_isStronglyAdapted := hQA
    L_isStronglyAdapted := hXAdapted.sub hQA
    Q_rightContinuous := hQR
    L_rightContinuous := fun omega t => (hXRight omega t).sub (hQR omega t)
    Q_leftLimits := hQL, L_leftLimits := hLL
    Q_locallyBoundedVariation := hQV, Q_zero := hQZ
    L_zero := by
      funext omega
      change X 0 omega - Q 0 omega = 0
      simp only [hXZero, hQZ, Pi.zero_apply, sub_self]
    decomposition := by
      funext t omega
      exact (sub_add_cancel _ _).symm
    L_jump_bound := hJump }⟩

end HorizonFactorialGrid

end FTAPTheorem42
