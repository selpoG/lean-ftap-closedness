/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.MartingaleNormalization
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticProcessLimit

/-!
# A finite-horizon quadratic core for a normalized prelocal `H¹` witness

The running-supremum envelope of a prelocal `H¹` witness does not by itself
provide a terminal `L²` input.  This module therefore takes the honest extra
assumption that the terminal value of the stopped, zero-initial martingale is
in `L²`.  The existing square-integrable quadratic-kernel producer then gives
an actual regularized quadratic-variation data package.  Its terminal
square-root is the finite `p = 1` quadratic root coordinate recorded here.

No Davis/BDG comparison, localization, or passage from the running-supremum
cost to this quadratic coordinate is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

/-! ## The terminal quadratic root coordinate -/

/-- The terminal square-root of the regularized quadratic variation. -/
noncomputable def squareIntegrableMartingaleQuadraticRoot
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) : Ω → Real :=
  fun omega => Real.sqrt (Q.variation T omega)

/-- The corresponding `p = 1` quadratic root cost. -/
noncomputable def squareIntegrableMartingaleQuadraticRootCost
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal
    (squareIntegrableMartingaleQuadraticRoot Q omega) ∂mu

theorem squareIntegrableMartingaleQuadraticRoot_nonnegative
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    ∀ omega, 0 ≤ squareIntegrableMartingaleQuadraticRoot Q omega := by
  intro omega
  exact Real.sqrt_nonneg _

theorem squareIntegrableMartingaleQuadraticRoot_stronglyMeasurable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    StronglyMeasurable (squareIntegrableMartingaleQuadraticRoot Q) := by
  exact (Q.variation_measurable T).sqrt.stronglyMeasurable

private theorem quadraticVariation_terminal_nonnegative
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    ∀ omega, 0 ≤ Q.variation T omega := by
  intro omega
  have hZero : Q.variation 0 omega = 0 := by
    simpa using congrFun Q.variation_zero omega
  have hMono := Q.variation_monotone omega (show (0 : NNReal) ≤ T from bot_le)
  change Q.variation 0 omega ≤ Q.variation T omega at hMono
  rw [hZero] at hMono
  exact hMono

theorem squareIntegrableMartingaleQuadraticRoot_integrable
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    Integrable (squareIntegrableMartingaleQuadraticRoot Q) mu := by
  have hVariation : Integrable (Q.variation T) mu :=
    Q.variation_terminal_integrable
  have hMajorant : Integrable (fun omega => Q.variation T omega + 1) mu :=
    hVariation.add (integrable_const 1)
  apply Integrable.mono' hMajorant
    (squareIntegrableMartingaleQuadraticRoot_stronglyMeasurable Q).aestronglyMeasurable
  filter_upwards [] with omega
  change |Real.sqrt (Q.variation T omega)| ≤ Q.variation T omega + 1
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hQ : 0 ≤ Q.variation T omega :=
    quadraticVariation_terminal_nonnegative Q omega
  have hSq : (Real.sqrt (Q.variation T omega)) ^ 2 = Q.variation T omega :=
    Real.sq_sqrt hQ
  nlinarith [Real.sqrt_nonneg (Q.variation T omega)]

theorem squareIntegrableMartingaleQuadraticRootCost_eq_ofReal_integral
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    squareIntegrableMartingaleQuadraticRootCost Q =
      ENNReal.ofReal
        (∫ omega, squareIntegrableMartingaleQuadraticRoot Q omega ∂mu) := by
  unfold squareIntegrableMartingaleQuadraticRootCost
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (squareIntegrableMartingaleQuadraticRoot_integrable Q)
    (Eventually.of_forall (squareIntegrableMartingaleQuadraticRoot_nonnegative Q))

theorem squareIntegrableMartingaleQuadraticRootCost_ne_top
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {M : Process Ω} {T : NNReal}
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    squareIntegrableMartingaleQuadraticRootCost Q ≠ ∞ := by
  rw [squareIntegrableMartingaleQuadraticRootCost_eq_ofReal_integral Q]
  exact ENNReal.ofReal_ne_top

/-! ## A concrete certificate and its witness consumer -/

/-- A finite-horizon square-integrable martingale and its regularized
quadratic-variation data, together with the finite terminal root cost. -/
structure SquareIntegrableMartingaleQuadraticJ1Certificate
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (M : Process Ω) (T : NNReal) where
  source_martingale : Martingale M F mu
  source_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  source_terminal_memLp_two : MemLp (M T) (2 : ENNReal) mu
  quadraticData : BoundedMartingaleQuadraticKernel.Data F mu M T
  root_integrable : Integrable
    (squareIntegrableMartingaleQuadraticRoot quadraticData) mu
  root_cost_ne_top :
    squareIntegrableMartingaleQuadraticRootCost quadraticData ≠ ∞

/-- A true finite-horizon square-integrable martingale supplies the concrete
quadratic core certificate. -/
theorem exists_squareIntegrableMartingaleQuadraticJ1Certificate
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {M : Process Ω} {T : NNReal}
    (hUsual : Filtration.UsualConditions mu F)
    (hM : Martingale M F mu)
    (hRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hM2 : MemLp (M T) (2 : ENNReal) mu) :
    Nonempty (SquareIntegrableMartingaleQuadraticJ1Certificate
      F mu M T) := by
  obtain ⟨Q⟩ := SquareIntegrableMartingaleQuadraticKernel.exists_data
    hUsual hM hRight T hM2
  exact ⟨{
    source_martingale := hM
    source_rightContinuous := hRight
    source_terminal_memLp_two := hM2
    quadraticData := Q
    root_integrable := squareIntegrableMartingaleQuadraticRoot_integrable Q
    root_cost_ne_top := squareIntegrableMartingaleQuadraticRootCost_ne_top Q }⟩

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
