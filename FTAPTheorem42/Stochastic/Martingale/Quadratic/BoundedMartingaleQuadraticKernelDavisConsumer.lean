/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleGridEnvelopeLimit
import FTAPTheorem42.Stochastic.Topology.Prelocal.DavisGeneric
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Foundations.CadlagEnvelope

/-!
# Davis estimates for quadratic kernels

Pass the convexified grid estimates to the terminal quadratic variation and
the continuous-time maximal envelope.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel

variable {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open SIntegrableFiniteVariationBridge
open SquareIntegrableMartingaleQuadraticApproximation

theorem factorialGridDavis_integral_runningMax_le_six_terminalRowRoot
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hM0 : M 0 = 0) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (r k : Nat) (hkr : r ≤ D.cutoff k) :
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
      6 * ∫ omega, terminalRowRoot D k omega ∂mu :=
  factorialGridDavis_integral_runningMax_le_six_convexRoot M T hM hM0
    (D.weights (D.cutoff k)) (terminalRowRoot_integrable D hM hMRight hMT k) r hkr

theorem factorialGridDavis_integral_runningMax_le_six_variationRoot
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hM0 : M 0 = 0) (hMT : MemLp (M T) (2 : ENNReal) mu) (r : Nat) :
    (∫ omega, FactorialChronologicalGrid.factorialRunningMax
      (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
      6 * ∫ omega,
        SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot
          D omega ∂mu := by
  have hTail : ∀ᶠ k in atTop, r ≤ D.cutoff k := by
    filter_upwards [eventually_ge_atTop r] with k hk
    exact hk.trans (D.cutoff_strictMono.le_apply)
  have hBound : ∀ᶠ k in atTop,
      (∫ omega, FactorialChronologicalGrid.factorialRunningMax
        (fun t omega => |M t omega|) T (level T r) omega ∂mu) ≤
        6 * ∫ omega, terminalRowRoot D k omega ∂mu := by
    filter_upwards [hTail] with k hk
    exact factorialGridDavis_integral_runningMax_le_six_terminalRowRoot
      D hM hMRight hM0 hMT r k hk
  exact le_of_tendsto_of_tendsto
    tendsto_const_nhds
    ((terminalRowRoot_integral_tendsto_variationRoot D hM hMRight hMT).const_mul 6)
    hBound

theorem finiteHorizonAbsoluteEnvelope_integral_le_six_variationRoot
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : forall omega t, Tendsto (M · omega) (𝓝[<] t)
      (𝓝 (Function.leftLim (M · omega) t)))
    (hM0 : M 0 = 0) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      M T omega ∂mu) ≤
      6 * ∫ omega,
        SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot
          D omega ∂mu := by
  exact (finiteHorizonAbsoluteEnvelope_integrable_of_grid_bound M T hM hMRight hMLeft
    (mul_nonneg (by norm_num) (integral_nonneg (fun _ => Real.sqrt_nonneg _)))
    (factorialGridDavis_integral_runningMax_le_six_variationRoot D hM hMRight hM0 hMT)).2

end BoundedMartingaleQuadraticKernel

end FTAPTheorem42
