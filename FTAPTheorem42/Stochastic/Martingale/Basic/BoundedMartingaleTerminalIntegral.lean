/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticEnergy
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalElementaryLinearization

/-!
# Completing bounded-martingale terminal integrals

The quadratic Stieltjes measure of a bounded finite-horizon martingale gives
one grid-independent isometry on bounded predictable elementary strategies.
This module completes that concrete isometry.  Elementary predictable
strategies are chosen densely in the energy `L²` space, their actual terminal
gains form a Cauchy sequence in `L²(μ)`, and the resulting Hilbert-space limit
is independent of the approximating presentations.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy
namespace Data

open BoundedMartingaleQuadraticKernel
open PredictableIntervalAlgebra

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {M : Process Omega} {T : NNReal}

/-- Every bounded predictable elementary integrand belongs to the concrete
quadratic-energy `L²` space. -/
theorem elementaryIntegrand_memLp_two
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hCoefficient : forall omega, H.coefficientAbsSum omega <= C) :
    MemLp (Function.uncurry H.integrand) (2 : ENNReal)
      D.predictableEnergyMeasure := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure :=
    D.predictableEnergyMeasure_isFinite
  apply MemLp.of_bound
    H.integrand_isStronglyPredictable.aestronglyMeasurable (C : Real)
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]
    exact (H.abs_integrand_le_coefficientAbsSum p.1 p.2).trans
      (by exact_mod_cast hCoefficient p.2)

/-- The elementary strategy representing the difference of two elementary
integrands. -/
noncomputable def elementaryDifference
    (H K : PredictableElementaryStrategy F) :
    PredictableElementaryStrategy F :=
  H ++ K.neg

@[simp]
theorem elementaryDifference_integrand
    (H K : PredictableElementaryStrategy F) :
    (elementaryDifference H K).integrand = H.integrand - K.integrand := by
  rw [elementaryDifference,
    PredictableElementaryStrategy.append_integrand,
    PredictableElementaryStrategy.neg_integrand]
  rfl

theorem elementaryDifference_coefficientAbsSum_le
    (H K : PredictableElementaryStrategy F) (C E : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega <= C)
    (hK : forall omega, K.coefficientAbsSum omega <= E) :
    forall omega,
      (elementaryDifference H K).coefficientAbsSum omega <= C + E := by
  intro omega
  rw [elementaryDifference,
    PredictableElementaryStrategy.coefficientAbsSum_append,
    PredictableElementaryStrategy.coefficientAbsSum_neg]
  exact_mod_cast add_le_add (hH omega) (hK omega)

theorem elementaryDifference_gain
    (H K : PredictableElementaryStrategy F) (M : Process Omega)
    (t : NNReal) :
    ElementaryStrategy.gain M (elementaryDifference H K).toElementary t =
      ElementaryStrategy.gain M H.toElementary t -
        ElementaryStrategy.gain M K.toElementary t := by
  funext omega
  simp only [elementaryDifference,
    PredictableElementaryStrategy.toElementary_append,
    PredictableElementaryStrategy.toElementary_neg,
    ElementaryStrategy.gain_append, ElementaryStrategy.gain_neg,
    Pi.sub_apply]
  ring

/-- Difference form of the grid-independent elementary energy isometry. -/
theorem eLpNorm_predictableEnergyMeasure_sub_eq_gain_sub
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (H K : PredictableElementaryStrategy F) (C E : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega <= C)
    (hK : forall omega, K.coefficientAbsSum omega <= E) :
    eLpNorm (Function.uncurry H.integrand -
        Function.uncurry K.integrand) (2 : ENNReal)
        D.predictableEnergyMeasure =
      eLpNorm (ElementaryStrategy.gain M H.toElementary T -
        ElementaryStrategy.gain M K.toElementary T)
        (2 : ENNReal) mu := by
  have hIso := eLpNorm_predictableEnergyMeasure_eq_gain D
    hM hMRight hMT (elementaryDifference H K) (C + E)
      (elementaryDifference_coefficientAbsSum_le H K C E hH hK)
  rw [elementaryDifference_integrand] at hIso
  change eLpNorm (Function.uncurry H.integrand -
      Function.uncurry K.integrand) (2 : ENNReal)
      D.predictableEnergyMeasure = _ at hIso
  rw [elementaryDifference_gain] at hIso
  exact hIso

/-- Concrete data for one elementary approximation of an energy-`L²`
integrand. -/
structure ElementaryApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real) (epsilon : ENNReal) where
  strategy : PredictableElementaryStrategy F
  coefficientBound : NNReal
  coefficientAbsSum_le : forall omega,
    strategy.coefficientAbsSum omega <= coefficientBound
  error_lt : eLpNorm
    (f - Function.uncurry strategy.integrand) (2 : ENNReal)
      D.predictableEnergyMeasure < epsilon

/-- Every strongly predictable energy-`L²` integrand admits an actual
bounded predictable elementary approximation with prescribed positive
error. -/
theorem exists_elementaryApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
    Nonempty (ElementaryApproximation D f epsilon) := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  let : IsFiniteMeasure D.predictableEnergyMeasure :=
    D.predictableEnergyMeasure_isFinite
  obtain ⟨H, hFirst, _hSecond, C, hC⟩ :=
    exists_elementary_eLpNorm_sub_lt_two_with_coefficientBound
        D.predictableEnergyMeasure D.predictableEnergyMeasure
        D.predictableEnergyMeasure_timeZeroSlice
        D.predictableEnergyMeasure_timeZeroSlice
        (2 : ENNReal) (2 : ENNReal) (by norm_num) (by norm_num)
        f hfMeas hf hf hepsilon
  exact ⟨{
    strategy := H
    coefficientBound := C
    coefficientAbsSum_le := hC
    error_lt := hFirst }⟩

/-- The reciprocal error scale used for the terminal completion. -/
noncomputable def approximationTolerance (n : Nat) : ENNReal :=
  ENNReal.ofReal (1 / (n + 1 : Real))

theorem approximationTolerance_ne_zero (n : Nat) :
    approximationTolerance n ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

/-- The chosen actual elementary approximation at accuracy
`1 / (n + 1)`. -/
noncomputable def elementaryApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) : ElementaryApproximation D f (approximationTolerance n) :=
  Classical.choice
    (exists_elementaryApproximation D f hfMeas hf
      (approximationTolerance_ne_zero n))

/-- Raw predictable integrand of the chosen elementary approximation. -/
noncomputable def elementaryApproximationIntegrand
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) : NNReal × Omega -> Real :=
  Function.uncurry (elementaryApproximation D f hfMeas hf n).strategy.integrand

/-- The chosen elementary integrand belongs to the energy `L²` space. -/
theorem elementaryApproximationIntegrand_memLp
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    MemLp (elementaryApproximationIntegrand D f hfMeas hf n)
      (2 : ENNReal) D.predictableEnergyMeasure :=
  elementaryIntegrand_memLp_two D
    (elementaryApproximation D f hfMeas hf n).strategy
    (elementaryApproximation D f hfMeas hf n).coefficientBound
    (elementaryApproximation D f hfMeas hf n).coefficientAbsSum_le

/-- The chosen elementary `Lp` classes converge to the prescribed energy
`L²` class. -/
theorem elementaryApproximationIntegrand_tendsto
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Tendsto (fun n =>
      (elementaryApproximationIntegrand_memLp D f hfMeas hf n).toLp
        (elementaryApproximationIntegrand D f hfMeas hf n))
      atTop (nhds (hf.toLp f)) := by
  let : MeasurableSpace (NNReal × Omega) := F.predictable
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  have hError :=
    (elementaryApproximation D f hfMeas hf n).error_lt
  rw [eLpNorm_sub_comm] at hError
  calc
    (eLpNorm
        (elementaryApproximationIntegrand D f hfMeas hf n - f)
        (2 : ENNReal) D.predictableEnergyMeasure).toReal <=
        (approximationTolerance n).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hError.le
    _ = 1 / (n + 1 : Real) := by
      rw [approximationTolerance, ENNReal.toReal_ofReal]
      positivity

/-- The actual terminal gain of one chosen elementary approximation. -/
noncomputable def terminalApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) : Omega -> Real :=
  ElementaryStrategy.gain M
    (elementaryApproximation D f hfMeas hf n).strategy.toElementary T

/-- Every terminal approximation is square integrable. -/
theorem terminalApproximation_memLp
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    MemLp (terminalApproximation D f hfMeas hf n)
      (2 : ENNReal) mu :=
  (elementaryApproximation D f hfMeas hf n).strategy.gain_memLp_two
    M hM hMRight T hMT
    (elementaryApproximation D f hfMeas hf n).coefficientBound
    (elementaryApproximation D f hfMeas hf n).coefficientAbsSum_le

/-- Terminal distances between chosen elementary approximations are exactly
their energy-control distances. -/
theorem dist_terminalApproximation_toLp_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (g : NNReal × Omega -> Real)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hg : MemLp g (2 : ENNReal) D.predictableEnergyMeasure)
    (n m : Nat) :
    dist
        ((terminalApproximation_memLp D hM hMRight hMT
          f hfMeas hf n).toLp
            (terminalApproximation D f hfMeas hf n))
        ((terminalApproximation_memLp D hM hMRight hMT
          g hgMeas hg m).toLp
            (terminalApproximation D g hgMeas hg m)) =
      dist
        ((elementaryApproximationIntegrand_memLp
          D f hfMeas hf n).toLp
            (elementaryApproximationIntegrand D f hfMeas hf n))
        ((elementaryApproximationIntegrand_memLp
          D g hgMeas hg m).toLp
            (elementaryApproximationIntegrand D g hgMeas hg m)) := by
  let H := (elementaryApproximation D f hfMeas hf n).strategy
  let K := (elementaryApproximation D g hgMeas hg m).strategy
  have hIso := eLpNorm_predictableEnergyMeasure_sub_eq_gain_sub
    D hM hMRight hMT H K
      (elementaryApproximation D f hfMeas hf n).coefficientBound
      (elementaryApproximation D g hgMeas hg m).coefficientBound
      (elementaryApproximation D f hfMeas hf n).coefficientAbsSum_le
      (elementaryApproximation D g hgMeas hg m).coefficientAbsSum_le
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    Lp.dist_edist, Lp.edist_toLp_toLp]
  apply congrArg ENNReal.toReal
  symm
  simpa only [H, K, elementaryApproximationIntegrand,
    terminalApproximation] using hIso

/-- The chosen actual terminal gains form a Cauchy sequence in `L²(μ)`. -/
theorem terminalApproximation_cauchySeq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    CauchySeq (fun n =>
      (terminalApproximation_memLp D hM hMRight hMT
        f hfMeas hf n).toLp
          (terminalApproximation D f hfMeas hf n)) := by
  have hIntegrandCauchy : CauchySeq (fun n =>
      (elementaryApproximationIntegrand_memLp D f hfMeas hf n).toLp
        (elementaryApproximationIntegrand D f hfMeas hf n)) :=
    (elementaryApproximationIntegrand_tendsto D f hfMeas hf).cauchySeq
  rw [Metric.cauchySeq_iff] at hIntegrandCauchy ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hIntegrandCauchy epsilon hepsilon
  exact ⟨N, fun n hn m hm => by
    rw [dist_terminalApproximation_toLp_eq
      D hM hMRight hMT f hfMeas hf f hfMeas hf n m]
    exact hN n hn m hm⟩

/-- The completed finite-horizon terminal stochastic integral in the
concrete martingale-energy `L²` space. -/
noncomputable def finiteHorizonMartingaleTerminalIntegralLp
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Lp Real (2 : ENNReal) mu :=
  limUnder atTop (fun n =>
    (terminalApproximation_memLp D hM hMRight hMT
      f hfMeas hf n).toLp
        (terminalApproximation D f hfMeas hf n))

/-- Elementary terminal gains converge to the completed terminal
operator. -/
theorem terminalApproximation_tendsto
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    Tendsto (fun n =>
      (terminalApproximation_memLp D hM hMRight hMT
        f hfMeas hf n).toLp
          (terminalApproximation D f hfMeas hf n))
      atTop (nhds (finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f hfMeas hf)) :=
  (terminalApproximation_cauchySeq
    D hM hMRight hMT f hfMeas hf).tendsto_limUnder

/-- The completed terminal operator preserves distances in the predictable
energy `L²` space. -/
theorem dist_finiteHorizonMartingaleTerminalIntegralLp_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (g : NNReal × Omega -> Real)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hg : MemLp g (2 : ENNReal) D.predictableEnergyMeasure) :
    dist
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT f hfMeas hf)
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT g hgMeas hg) =
      dist (hf.toLp f) (hg.toLp g) := by
  let terminalF : Nat -> Lp Real (2 : ENNReal) mu := fun n =>
    (terminalApproximation_memLp D hM hMRight hMT
      f hfMeas hf n).toLp (terminalApproximation D f hfMeas hf n)
  let terminalG : Nat -> Lp Real (2 : ENNReal) mu := fun n =>
    (terminalApproximation_memLp D hM hMRight hMT
      g hgMeas hg n).toLp (terminalApproximation D g hgMeas hg n)
  let integrandF : Nat -> Lp Real (2 : ENNReal)
      D.predictableEnergyMeasure := fun n =>
    (elementaryApproximationIntegrand_memLp D f hfMeas hf n).toLp
      (elementaryApproximationIntegrand D f hfMeas hf n)
  let integrandG : Nat -> Lp Real (2 : ENNReal)
      D.predictableEnergyMeasure := fun n =>
    (elementaryApproximationIntegrand_memLp D g hgMeas hg n).toLp
      (elementaryApproximationIntegrand D g hgMeas hg n)
  have hTerminalF : Tendsto terminalF atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f hfMeas hf)) :=
    terminalApproximation_tendsto D hM hMRight hMT f hfMeas hf
  have hTerminalG : Tendsto terminalG atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT g hgMeas hg)) :=
    terminalApproximation_tendsto D hM hMRight hMT g hgMeas hg
  have hIntegrandF : Tendsto integrandF atTop (nhds (hf.toLp f)) :=
    elementaryApproximationIntegrand_tendsto D f hfMeas hf
  have hIntegrandG : Tendsto integrandG atTop (nhds (hg.toLp g)) :=
    elementaryApproximationIntegrand_tendsto D g hgMeas hg
  have hDistance : forall n,
      dist (terminalF n) (terminalG n) =
        dist (integrandF n) (integrandG n) := fun n =>
    dist_terminalApproximation_toLp_eq
      D hM hMRight hMT f hfMeas hf g hgMeas hg n n
  exact tendsto_nhds_unique (hTerminalF.dist hTerminalG)
    ((hIntegrandF.dist hIntegrandG).congr'
      (Filter.Eventually.of_forall fun n => (hDistance n).symm))

/-- ENNReal-valued difference isometry for the completed terminal
integral. -/
theorem edist_finiteHorizonMartingaleTerminalIntegralLp_eq_eLpNorm
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (g : NNReal × Omega -> Real)
    (hgMeas : StronglyMeasurable[F.predictable] g)
    (hg : MemLp g (2 : ENNReal) D.predictableEnergyMeasure) :
    edist
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT f hfMeas hf)
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT g hgMeas hg) =
      eLpNorm (f - g) (2 : ENNReal) D.predictableEnergyMeasure := by
  calc
    edist
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT f hfMeas hf)
        (finiteHorizonMartingaleTerminalIntegralLp
          D hM hMRight hMT g hgMeas hg) =
        ENNReal.ofReal (dist
          (finiteHorizonMartingaleTerminalIntegralLp
            D hM hMRight hMT f hfMeas hf)
          (finiteHorizonMartingaleTerminalIntegralLp
            D hM hMRight hMT g hgMeas hg)) :=
      Lp.edist_dist _ _
    _ = ENNReal.ofReal (dist (hf.toLp f) (hg.toLp g)) := by
      rw [dist_finiteHorizonMartingaleTerminalIntegralLp_eq
        D hM hMRight hMT f hfMeas hf g hgMeas hg]
    _ = edist (hf.toLp f) (hg.toLp g) := (Lp.edist_dist _ _).symm
    _ = eLpNorm (f - g) (2 : ENNReal) D.predictableEnergyMeasure :=
      Lp.edist_toLp_toLp f g hf hg

/-- Distance from a chosen terminal approximation to one bounded actual
elementary gain is its energy-control integrand distance. -/
theorem dist_terminalApproximation_to_elementary_eq
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega -> Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) (H : PredictableElementaryStrategy F) (C : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega <= C) :
    dist
        ((terminalApproximation_memLp D hM hMRight hMT
          f hfMeas hf n).toLp
            (terminalApproximation D f hfMeas hf n))
        ((H.gain_memLp_two M hM hMRight T hMT C hH).toLp
          (ElementaryStrategy.gain M H.toElementary T)) =
      dist
        ((elementaryApproximationIntegrand_memLp
          D f hfMeas hf n).toLp
            (elementaryApproximationIntegrand D f hfMeas hf n))
        ((elementaryIntegrand_memLp_two D H C hH).toLp
          (Function.uncurry H.integrand)) := by
  let K := (elementaryApproximation D f hfMeas hf n).strategy
  have hIso := eLpNorm_predictableEnergyMeasure_sub_eq_gain_sub
    D hM hMRight hMT K H
      (elementaryApproximation D f hfMeas hf n).coefficientBound C
      (elementaryApproximation D f hfMeas hf n).coefficientAbsSum_le hH
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    Lp.dist_edist, Lp.edist_toLp_toLp]
  apply congrArg ENNReal.toReal
  symm
  simpa only [K, elementaryApproximationIntegrand,
    terminalApproximation] using hIso

/-- On bounded predictable elementary integrands, the completed terminal
operator agrees with the original stochastic integral. -/
theorem finiteHorizonMartingaleTerminalIntegralLp_eq_elementary
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (H : PredictableElementaryStrategy F) (C : NNReal)
    (hH : forall omega, H.coefficientAbsSum omega <= C) :
    finiteHorizonMartingaleTerminalIntegralLp D hM hMRight hMT
        (Function.uncurry H.integrand)
        H.integrand_isStronglyPredictable
        (elementaryIntegrand_memLp_two D H C hH) =
      (H.gain_memLp_two M hM hMRight T hMT C hH).toLp
        (ElementaryStrategy.gain M H.toElementary T) := by
  let f : NNReal × Omega -> Real := Function.uncurry H.integrand
  let hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure :=
    elementaryIntegrand_memLp_two D H C hH
  let hGain : MemLp (ElementaryStrategy.gain M H.toElementary T)
      (2 : ENNReal) mu := H.gain_memLp_two M hM hMRight T hMT C hH
  have hCompleted : Tendsto (fun n =>
      (terminalApproximation_memLp D hM hMRight hMT
        f H.integrand_isStronglyPredictable hf n).toLp
          (terminalApproximation
            D f H.integrand_isStronglyPredictable hf n)) atTop
      (nhds (finiteHorizonMartingaleTerminalIntegralLp
        D hM hMRight hMT f H.integrand_isStronglyPredictable hf)) :=
    terminalApproximation_tendsto
      D hM hMRight hMT f H.integrand_isStronglyPredictable hf
  have hIntegrand : Tendsto (fun n =>
      (elementaryApproximationIntegrand_memLp
        D f H.integrand_isStronglyPredictable hf n).toLp
          (elementaryApproximationIntegrand
            D f H.integrand_isStronglyPredictable hf n))
      atTop (nhds (hf.toLp f)) :=
    elementaryApproximationIntegrand_tendsto
      D f H.integrand_isStronglyPredictable hf
  have hActual : Tendsto (fun n =>
      (terminalApproximation_memLp D hM hMRight hMT
        f H.integrand_isStronglyPredictable hf n).toLp
          (terminalApproximation
            D f H.integrand_isStronglyPredictable hf n)) atTop
      (nhds (hGain.toLp
        (ElementaryStrategy.gain M H.toElementary T))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hDistance := tendsto_iff_dist_tendsto_zero.mp hIntegrand
    exact hDistance.congr' (Filter.Eventually.of_forall fun n =>
      (dist_terminalApproximation_to_elementary_eq
        D hM hMRight hMT f H.integrand_isStronglyPredictable hf
          n H C hH).symm)
  exact tendsto_nhds_unique hCompleted hActual

end Data
end BoundedMartingaleQuadraticEnergy
end FTAPTheorem42
