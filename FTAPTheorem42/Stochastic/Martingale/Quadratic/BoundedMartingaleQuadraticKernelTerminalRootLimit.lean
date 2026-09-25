/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.QuadraticCore
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticConvexification
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticUniformIntegrability
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Terminal limits of the selected quadratic rows

The quadratic-kernel data package stores the actual tail weights and the
strictly increasing cutoff used by the process construction.  This file
connects those same rows, without choosing new weights, to the terminal
regularized variation and to its square root in `L¹`.

The result is still a deterministic-horizon statement.  It does not identify
the realized finite-grid square functions with a continuous quadratic
variation, and it does not supply a running-supremum estimate.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open SquareIntegrableMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticConvexification
open SquareIntegrableMartingaleQuadraticUniformIntegrability

variable {mu : Measure Omega} [IsProbabilityMeasure mu]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

theorem abs_sqrt_sub_sqrt_le {a b : Real} (ha : 0 <= a) (hb : 0 <= b) :
    |Real.sqrt a - Real.sqrt b| <= Real.sqrt |a - b| := by
  rcases le_total a b with hab | hba
  · have hsab : Real.sqrt a <= Real.sqrt b := Real.sqrt_le_sqrt hab
    have hnon : 0 <= Real.sqrt b - Real.sqrt a := sub_nonneg.mpr hsab
    rw [abs_of_nonpos (sub_nonpos.mpr hsab), neg_sub]
    apply (Real.le_sqrt hnon (abs_nonneg _)).2
    rw [sq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    nlinarith [mul_nonneg (Real.sqrt_nonneg a) hnon]
  · have hsba : Real.sqrt b <= Real.sqrt a := Real.sqrt_le_sqrt hba
    have hnon : 0 <= Real.sqrt a - Real.sqrt b := sub_nonneg.mpr hsba
    rw [abs_of_nonneg hnon]
    apply (Real.le_sqrt hnon (abs_nonneg _)).2
    rw [sq, abs_of_nonneg (sub_nonneg.mpr hba)]
    have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    nlinarith [mul_nonneg (Real.sqrt_nonneg b) hnon]

/-- The terminal row selected by the weights and cutoff stored in `D`. -/
noncomputable def terminalRow
    (D : Data F mu M T) (k : Nat) : Omega → Real :=
  BoundedMartingaleQuadraticConvexification.squaredIncrementPart
    M T (D.weights (D.cutoff k)) T

/-- The terminal square-root of a selected quadratic row. -/
noncomputable def terminalRowRoot
    (D : Data F mu M T) (k : Nat) : Omega → Real :=
  fun omega => Real.sqrt (terminalRow D k omega)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
/-- The stored rows are exactly a forward-convex reindexing of the original
factorial-grid terminal rows. -/
theorem terminalRow_eq_forwardApply
    (D : Data F mu M T) (k : Nat) :
    terminalRow D k =
      (TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights).apply
        (fun n => BoundedMartingaleQuadraticApproximation.squaredIncrementPart M T n T) k := by
  funext omega
  simp [terminalRow, BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply,
    TailConvexWeights.toForwardReindex_apply]

omit [SigmaFiniteFiltration mu F] in
theorem terminalRow_stronglyMeasurable
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (k : Nat) :
    StronglyMeasurable (terminalRow D k) := by
  rw [terminalRow_eq_forwardApply D k]
  let W : ForwardConvexWeights :=
    TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights
  change StronglyMeasurable (W.apply
    (fun n => squaredIncrementPart M T n T) k)
  exact W.apply_stronglyMeasurable
    (fun n => squaredIncrementPart_terminal_stronglyMeasurable hM hMRight T n) k

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem terminalRow_nonnegative
    (D : Data F mu M T) (k : Nat) :
    forall omega, 0 <= terminalRow D k omega := by
  intro omega
  exact squaredIncrementPart_nonneg M T T (D.weights (D.cutoff k)) omega

theorem terminalRow_integrable
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) (k : Nat) :
    Integrable (terminalRow D k) mu := by
  let Q : Nat -> Omega -> Real :=
    fun n => squaredIncrementPart M T n T
  let W : ForwardConvexWeights :=
    TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights
  have hQUI : UniformIntegrable Q 1 mu :=
    squaredIncrementPart_terminal_uniformIntegrable hM hMRight T hMT
  have hMem : MemLp (W.apply Q k) 1 mu :=
    (W.uniformIntegrable_apply (by norm_num) hQUI).memLp k
  have hEq : terminalRow D k = W.apply Q k := by
    simpa only [Q, W] using terminalRow_eq_forwardApply D k
  rw [hEq]
  exact memLp_one_iff_integrable.mp hMem

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem terminalRow_tendstoAE_variation
    (D : Data F mu M T) :
    ∀ᵐ omega ∂mu, Tendsto (fun k => terminalRow D k omega) atTop
      (nhds (D.variation T omega)) := by
  filter_upwards [D.variation_uniform] with omega homega
  simpa only [terminalRow] using homega.tendsto_at T

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem variation_terminal_nonnegative
    (D : Data F mu M T) :
    forall omega, 0 <= D.variation T omega := by
  intro omega
  have hZero : D.variation 0 omega = 0 := by
    simpa using congrFun D.variation_zero omega
  have hMono := D.variation_monotone omega (show (0 : NNReal) <= T from bot_le)
  change D.variation 0 omega <= D.variation T omega at hMono
  rw [hZero] at hMono
  exact hMono

theorem terminalRowRoot_integrable
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) (k : Nat) :
    Integrable (terminalRowRoot D k) mu := by
  have hRow : Integrable (terminalRow D k) mu :=
    terminalRow_integrable D hM hMRight hMT k
  have hMajorant : Integrable (fun omega => terminalRow D k omega + 1) mu :=
    hRow.add (integrable_const 1)
  have hMeas : Measurable (terminalRow D k) :=
    (terminalRow_stronglyMeasurable D hM hMRight k).measurable
  apply Integrable.mono' hMajorant hMeas.sqrt.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with omega
  change |Real.sqrt (terminalRow D k omega)| <= terminalRow D k omega + 1
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hRowNonneg : 0 <= terminalRow D k omega := terminalRow_nonnegative D k omega
  have hSq : (Real.sqrt (terminalRow D k omega)) ^ 2 = terminalRow D k omega :=
    Real.sq_sqrt hRowNonneg
  nlinarith [Real.sqrt_nonneg (terminalRow D k omega)]

theorem terminalRow_tendsto_L1_variation
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Tendsto (fun k => eLpNorm (terminalRow D k - D.variation T) 1 mu)
      atTop (nhds 0) := by
  let Q : Nat -> Omega -> Real :=
    fun n => squaredIncrementPart M T n T
  let W : ForwardConvexWeights :=
    TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights
  have hQUI : UniformIntegrable Q 1 mu :=
    squaredIncrementPart_terminal_uniformIntegrable hM hMRight T hMT
  have hWUI : UniformIntegrable (W.apply Q) 1 mu :=
    W.uniformIntegrable_apply (by norm_num) hQUI
  have hRowUI : UniformIntegrable (fun k => terminalRow D k) 1 mu :=
    hWUI.ae_eq (fun k => by
      filter_upwards [] with omega
      exact congrFun (terminalRow_eq_forwardApply D k) omega |>.symm)
  have hVariationMemLp : MemLp (D.variation T) 1 mu :=
    memLp_one_iff_integrable.mpr D.variation_terminal_integrable
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num) ENNReal.one_ne_top hRowUI.aestronglyMeasurable hVariationMemLp
      hRowUI.unifIntegrable (terminalRow_tendstoAE_variation D)

theorem terminalRowRoot_tendsto_L1_variationRoot
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Tendsto (fun k => eLpNorm
      (terminalRowRoot D k -
        SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot D)
      1 mu) atTop (nhds 0) := by
  let R : Nat -> Omega -> Real := fun k omega =>
    Real.sqrt |terminalRow D k omega - D.variation T omega|
  have hDiffL1 : Tendsto (fun k => eLpNorm
      (terminalRow D k - D.variation T) 1 mu) atTop (nhds 0) :=
    terminalRow_tendsto_L1_variation D hM hMRight hMT
  have hRMeas : forall k, AEStronglyMeasurable (R k) mu := by
    intro k
    have hRowMeas : Measurable (terminalRow D k) :=
      (terminalRow_stronglyMeasurable D hM hMRight k).measurable
    have hVarMeas : Measurable (D.variation T) := D.variation_measurable T
    have hDiffMeas : Measurable (fun omega =>
        terminalRow D k omega - D.variation T omega) := hRowMeas.sub hVarMeas
    exact (Measurable.abs hDiffMeas).sqrt.aestronglyMeasurable
  have hRpowEq : forall k, eLpNorm (R k) 2 mu =
      (eLpNorm (terminalRow D k - D.variation T) 1 mu) ^ (1 / 2 : Real) := by
    intro k
    have hNormRpow := eLpNorm_norm_rpow (μ := mu) (R k) (p := (1 : ENNReal))
      (q := (2 : Real)) (hRMeas k) (by norm_num)
    have hPoint : (fun omega => ‖R k omega‖ ^ (2 : Real)) =
        fun omega => |terminalRow D k omega - D.variation T omega| := by
      funext omega
      dsimp [R]
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two]
      exact Real.sq_sqrt (abs_nonneg _)
    have hAbsNorm : eLpNorm
        (fun omega => |terminalRow D k omega - D.variation T omega|) 1 mu =
        eLpNorm (terminalRow D k - D.variation T) 1 mu := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (eLpNorm_norm (μ := mu) (p := (1 : ENNReal))
          (terminalRow D k - D.variation T)
          ((terminalRow_stronglyMeasurable D hM hMRight k).aestronglyMeasurable.sub
            (D.variation_measurable T).aestronglyMeasurable))
    have hSquare : (eLpNorm (R k) 2 mu) ^ (2 : Real) =
        eLpNorm (terminalRow D k - D.variation T) 1 mu := by
      calc
        (eLpNorm (R k) 2 mu) ^ (2 : Real) =
            eLpNorm (R k) ((1 : ENNReal) * ENNReal.ofReal 2) mu ^ (2 : Real) := by
              norm_num
        _ = eLpNorm (fun omega => ‖R k omega‖ ^ (2 : Real)) 1 mu :=
          hNormRpow.symm
        _ = eLpNorm (fun omega => |terminalRow D k omega - D.variation T omega|) 1 mu :=
          congrArg (fun f => eLpNorm f 1 mu) hPoint
        _ = eLpNorm (terminalRow D k - D.variation T) 1 mu := hAbsNorm
    calc
      eLpNorm (R k) 2 mu =
          (eLpNorm (R k) 2 mu ^ (2 : Real)) ^ (1 / (2 : Real)) := by
            symm
            simpa only [one_div] using
              (ENNReal.rpow_rpow_inv (x := eLpNorm (R k) 2 mu)
                (y := (2 : Real)) (by norm_num))
      _ = (eLpNorm (terminalRow D k - D.variation T) 1 mu) ^ (1 / 2 : Real) := by
        rw [hSquare]
  have hRpowTendsto : Tendsto (fun k =>
      (eLpNorm (terminalRow D k - D.variation T) 1 mu) ^ (1 / 2 : Real))
      atTop (nhds 0) := by
    have hCont : Continuous (fun x : ENNReal => x ^ (1 / 2 : Real)) :=
      ENNReal.continuous_rpow_const
    have hContAt : Tendsto (fun x : ENNReal => x ^ (1 / 2 : Real))
        (nhds 0) (nhds 0) := by
      simpa using (hCont.continuousAt (x := (0 : ENNReal))).tendsto
    exact hContAt.comp hDiffL1
  have hRNormTendsto : Tendsto (fun k => eLpNorm (R k) 1 mu)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRpowTendsto
    · intro k
      exact bot_le
    · intro k
      change eLpNorm (R k) 1 mu ≤
        (eLpNorm (terminalRow D k - D.variation T) 1 mu) ^ (1 / 2 : Real)
      calc
        eLpNorm (R k) 1 mu ≤ eLpNorm (R k) 2 mu :=
          eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
        _ = _ := hRpowEq k
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRNormTendsto
  · intro k
    exact bot_le
  · intro k
    apply eLpNorm_mono_ae
      ((terminalRowRoot_integrable D hM hMRight hMT k).sub
        (SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot_integrable
          D)).aestronglyMeasurable
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |Real.sqrt (terminalRow D k omega) -
          Real.sqrt (D.variation T omega)| <=
          Real.sqrt |terminalRow D k omega - D.variation T omega| :=
        abs_sqrt_sub_sqrt_le (terminalRow_nonnegative D k omega)
          (variation_terminal_nonnegative D omega)
      _ = |R k omega| := by
        simpa only [R] using
          (abs_of_nonneg (Real.sqrt_nonneg
            |terminalRow D k omega - D.variation T omega|)).symm

theorem terminalRowRoot_integral_tendsto_variationRoot
    (D : Data F mu M T) (hM : Martingale M F mu)
    (hMRight : forall omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Tendsto (fun k => ∫ omega, terminalRowRoot D k omega ∂mu) atTop
      (nhds (∫ omega,
        SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot D omega ∂mu)) :=
  tendsto_integral_of_L1'
    (SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot D)
    (Eventually.of_forall fun k => terminalRowRoot_integrable D hM hMRight hMT k)
    (terminalRowRoot_tendsto_L1_variationRoot D hM hMRight hMT)

end BoundedMartingaleQuadraticKernel

end FTAPTheorem42
