/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.MartingaleTestEstimate
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessCauchy

/-! # Elementary-test continuity used in the common convexification proof

These are general continuity estimates. They neither select convex weights
nor assume NFLVR, maximality, or a Cauchy property of the selected components.
-/

namespace FTAPTheorem42.AnalyticInterface

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem emeryCauchy_of_uniform_approximations
    {X : Nat → Process Ω} (hX : ∀ n, IsStronglyProgressive F (X n))
    (hApprox : ∀ T : NNReal, ∀ ε : Real, 0 < ε →
      ∃ Y : Nat → Process Ω,
        (∀ n, IsStronglyProgressive F (Y n)) ∧
        (∀ n, ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
          (∫ ω, elementaryEmeryTestError (X n) (Y n) J T ω ∂μ) ≤ ε) ∧
        (∀ δ : Real, 0 < δ → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
          ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
            (∫ ω, elementaryEmeryTestError (Y n) (Y k) J T ω ∂μ) ≤ δ)) :
    ElementaryEmeryCauchy μ F X :=
  FTAPTheorem42.elementaryEmeryCauchy_of_uniform_approximations hX hApprox

variable [SigmaFiniteFiltration μ F]

theorem martingaleTestsCauchy_of_terminalL2
    {M : Nat → Process Ω} (hM : ∀ n, Martingale (M n) F μ)
    (hRight : ∀ n ω t, ContinuousWithinAt (M n · ω) (Ici t) t)
    (hZero : ∀ n, M n 0 =ᵐ[μ] 0) (U : NNReal)
    (Z : Nat → Lp Real 2 μ) (hZ : ∀ n, ⇑(Z n) =ᵐ[μ] M n U)
    (hCauchy : CauchySeq Z) :
    ∀ ε : Real, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
      ∀ T : NNReal, T ≤ U → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError (M n) (M k) J T ω ∂μ) ≤ ε :=
  FTAPTheorem42.martingale_testError_cauchy_of_terminal_L2 hM hRight hZero U Z hZ hCauchy

end FTAPTheorem42.AnalyticInterface
