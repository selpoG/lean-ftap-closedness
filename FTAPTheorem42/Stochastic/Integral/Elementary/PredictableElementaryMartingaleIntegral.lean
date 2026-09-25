/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepMartingaleApproximation
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit

/-!
# Martingale property of bounded predictable elementary gains

A bounded predictable elementary strategy is approximated by the concrete
chronological left-grid strategies constructed previously.  Their gains are
finite sums of deterministic-interval martingale transforms and hence true
martingales.  After stopping at a deterministic horizon, the same processes
converge pathwise at every time to the stopped actual elementary gain.

The finite-horizon martingale maximal envelope gives one uniform `L²`
dominator.  The uniform-integrability martingale-limit theorem therefore
upgrades the stopped actual gain itself to a true martingale.  This is the
first continuous-time realization theorem beyond a fixed finite grid; it is
proved from the concrete elementary gain rather than postulated by a
realization capability.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LeftContinuousPredictable

/-- A grid which covers `T` also gives the direct strict-right clipping
identity at every earlier evaluation time `U`. -/
theorem min_gridPoint_min_rightIndex_horizonCellCount_of_le
    (r : Nat) {U T t : NNReal} (hUT : U ≤ T) :
    min U (gridPoint r
      (min (rightIndex r t) (horizonCellCount r T))) =
      min U (strictRightApprox r t) := by
  calc
    min U (gridPoint r
        (min (rightIndex r t) (horizonCellCount r T))) =
        min U (min T (gridPoint r
          (min (rightIndex r t) (horizonCellCount r T)))) := by
      symm
      rw [← min_assoc, min_eq_left hUT]
    _ = min U (min T (strictRightApprox r t)) := by
      rw [min_gridPoint_min_rightIndex_horizonCellCount]
    _ = min U (strictRightApprox r t) := by
      rw [← min_assoc, min_eq_left hUT]

end LeftContinuousPredictable

namespace PredictableElementaryInterval

/-- A horizon-covering grid telescopes one elementary block at every earlier
evaluation time. -/
theorem horizonGrid_martingaleIntegralProcess_eq_of_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (r : Nat) {U T : NNReal} (hUT : U ≤ T) (omega : Omega) :
    (LeftContinuousPredictable.finiteGrid r
      (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
        B.integrand M U omega =
      B.interval.coefficient omega *
        (M (min U (LeftContinuousPredictable.strictRightApprox r
            (B.interval.stopTime omega))) omega -
          M (min U (LeftContinuousPredictable.strictRightApprox r
            (B.interval.startTime omega))) omega) := by
  rw [B.finiteGrid_martingaleIntegralProcess_eq M r
    (LeftContinuousPredictable.horizonCellCount r T) U omega,
    LeftContinuousPredictable.min_gridPoint_min_rightIndex_horizonCellCount_of_le
      r hUT,
    LeftContinuousPredictable.min_gridPoint_min_rightIndex_horizonCellCount_of_le
      r hUT]

/-- Right continuity identifies the horizon-grid transform of one block at
every time below the horizon. -/
theorem tendsto_horizonGrid_martingaleIntegralProcess_of_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (B : PredictableElementaryInterval F) (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {U T : NNReal} (hUT : U ≤ T) (omega : Omega) :
    Tendsto
      (fun r =>
        (LeftContinuousPredictable.finiteGrid r
          (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
            B.integrand M U omega)
      atTop (nhds (B.interval.gain M U omega)) := by
  have hTime (s : NNReal) : Tendsto
      (fun r => min U (LeftContinuousPredictable.strictRightApprox r s))
      atTop (nhds (min U s)) := by
    exact tendsto_const_nhds.min
      (LeftContinuousPredictable.tendsto_strictRightApprox s)
  have hSample (s : NNReal) : Tendsto
      (fun r => M (min U
        (LeftContinuousPredictable.strictRightApprox r s)) omega)
      atTop (nhds (M (min U s) omega)) := by
    apply (hMRight omega (min U s)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hTime s, Filter.Eventually.of_forall fun r =>
      min_le_min le_rfl
        ((LeftContinuousPredictable.lt_gridPoint_iff_rightIndex_le
          r (LeftContinuousPredictable.rightIndex r s) s).2 le_rfl).le⟩
  rw [show (fun r =>
      (LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
          B.integrand M U omega) =
      fun r => B.interval.coefficient omega *
        (M (min U (LeftContinuousPredictable.strictRightApprox r
            (B.interval.stopTime omega))) omega -
          M (min U (LeftContinuousPredictable.strictRightApprox r
            (B.interval.startTime omega))) omega) by
    funext r
    exact B.horizonGrid_martingaleIntegralProcess_eq_of_le
      M r hUT omega]
  exact tendsto_const_nhds.mul
    ((hSample (B.interval.stopTime omega)).sub
      (hSample (B.interval.startTime omega)))

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

/-- The horizon-grid transforms converge pathwise at every earlier
evaluation time to the actual elementary gain. -/
theorem tendsto_horizonGrid_martingaleIntegralProcess_of_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {U T : NNReal} (hUT : U ≤ T) (omega : Omega) :
    Tendsto
      (fun r =>
        (LeftContinuousPredictable.finiteGrid r
          (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
            H.integrand M U omega)
      atTop (nhds (ElementaryStrategy.gain M H.toElementary U omega)) := by
  induction H with
  | nil =>
      simp [PredictableElementaryStrategy.integrand,
        PredictableElementaryStrategy.toElementary,
        ElementaryStrategy.gain]
  | cons B H ih =>
      have hAdd (r : Nat) :
          (LeftContinuousPredictable.finiteGrid r
            (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
              (B.integrand +
                PredictableElementaryStrategy.integrand H) M =
            (LeftContinuousPredictable.finiteGrid r
              (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
                B.integrand M +
            (LeftContinuousPredictable.finiteGrid r
              (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
                (PredictableElementaryStrategy.integrand H) M :=
        ChronologicalGrid.martingaleIntegralProcess_add _ _ _ _
      change Tendsto
        (fun r =>
          (LeftContinuousPredictable.finiteGrid r
            (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
              (B.integrand +
                PredictableElementaryStrategy.integrand H) M U omega)
        atTop (nhds (B.interval.gain M U omega +
          ElementaryStrategy.gain M
            (PredictableElementaryStrategy.toElementary (ℱ := F) H)
            U omega))
      apply ((B.tendsto_horizonGrid_martingaleIntegralProcess_of_le
        M hMRight hUT omega).add ih).congr'
      exact Filter.Eventually.of_forall fun r =>
        (congrFun (congrFun (hAdd r) U) omega).symm

/-- A common source envelope up to `T` controls each horizon-grid transform
at every earlier evaluation time. -/
theorem norm_horizonGrid_martingaleIntegralProcess_le_of_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    {U T : NNReal} (hUT : U ≤ T) (omega : Omega) (E : Real)
    (hM : ∀ t, t ≤ T → ‖M t omega‖ ≤ E) (r : Nat) :
    ‖(LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)).martingaleIntegralProcess
          H.integrand M U omega‖ ≤
      2 * H.coefficientAbsSum omega * E := by
  induction H with
  | nil => simp [PredictableElementaryStrategy.integrand, coefficientAbsSum]
  | cons B H ih =>
      let G := LeftContinuousPredictable.finiteGrid r
        (LeftContinuousPredictable.horizonCellCount r T)
      have hAdd := ChronologicalGrid.martingaleIntegralProcess_add
        G B.integrand (PredictableElementaryStrategy.integrand H) M
      have hBlock :
          ‖G.martingaleIntegralProcess B.integrand M U omega‖ ≤
            2 * |B.interval.coefficient omega| * E := by
        rw [B.horizonGrid_martingaleIntegralProcess_eq_of_le
          M r hUT omega]
        calc
          ‖B.interval.coefficient omega *
              (M (min U (LeftContinuousPredictable.strictRightApprox r
                  (B.interval.stopTime omega))) omega -
                M (min U (LeftContinuousPredictable.strictRightApprox r
                  (B.interval.startTime omega))) omega)‖ =
              ‖B.interval.coefficient omega‖ *
                ‖M (min U (LeftContinuousPredictable.strictRightApprox r
                    (B.interval.stopTime omega))) omega -
                  M (min U (LeftContinuousPredictable.strictRightApprox r
                    (B.interval.startTime omega))) omega‖ := norm_mul _ _
          _ ≤ ‖B.interval.coefficient omega‖ * (E + E) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (norm_sub_le _ _).trans (add_le_add
              (hM _ ((min_le_left _ _).trans hUT))
              (hM _ ((min_le_left _ _).trans hUT)))
          _ = 2 * |B.interval.coefficient omega| * E := by
            rw [Real.norm_eq_abs]
            ring
      change ‖G.martingaleIntegralProcess
          (B.integrand + PredictableElementaryStrategy.integrand H)
          M U omega‖ ≤ _
      rw [congrFun (congrFun hAdd U) omega]
      calc
        ‖G.martingaleIntegralProcess B.integrand M U omega +
            G.martingaleIntegralProcess
              (PredictableElementaryStrategy.integrand H) M U omega‖ ≤
            ‖G.martingaleIntegralProcess B.integrand M U omega‖ +
              ‖G.martingaleIntegralProcess
                (PredictableElementaryStrategy.integrand H) M U omega‖ :=
          norm_add_le _ _
        _ ≤ 2 * |B.interval.coefficient omega| * E +
            2 * coefficientAbsSum H omega * E := add_le_add hBlock ih
        _ = 2 * coefficientAbsSum (B :: H) omega * E := by
          simp only [coefficientAbsSum, List.map_cons, List.sum_cons]
          ring

/-- A bounded predictable elementary gain, stopped at a deterministic
horizon where the source martingale is square-integrable, is a true
martingale. -/
theorem stoppedGain_isMartingale
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (H : PredictableElementaryStrategy F) (M : Process Omega)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (C : NNReal) (hCoefficient : ∀ omega,
      H.coefficientAbsSum omega ≤ C) :
    Martingale
      (MeasureTheory.stoppedProcess
        (ElementaryStrategy.gain M H.toElementary)
        (fun _ : Omega => (T : WithTop NNReal))) F mu := by
  let grid : (r : Nat) → ChronologicalGrid NNReal
      (LeftContinuousPredictable.horizonCellCount r T) := fun r =>
    LeftContinuousPredictable.finiteGrid r
      (LeftContinuousPredictable.horizonCellCount r T)
  let approximant : Nat → Process Omega := fun r =>
    MeasureTheory.stoppedProcess
      ((grid r).martingaleIntegralProcess H.integrand M)
      (fun _ : Omega => (T : WithTop NNReal))
  let target : Process Omega :=
    MeasureTheory.stoppedProcess
      (ElementaryStrategy.gain M H.toElementary)
      (fun _ : Omega => (T : WithTop NNReal))
  let envelope : Omega → Real :=
    FactorialChronologicalGrid.martingaleAbsoluteEnvelope M T
  let bound : Omega → Real := fun omega =>
    2 * (C : Real) * envelope omega
  have hProgressive : IsStronglyProgressive F M :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hM.stronglyAdapted hMRight
  have hGainAdapted : StronglyAdapted F
      (ElementaryStrategy.gain M H.toElementary) :=
    H.stronglyAdapted_gain M hProgressive
  have hGainRight : ∀ omega t, ContinuousWithinAt
      (ElementaryStrategy.gain M H.toElementary · omega) (Ici t) t :=
    H.rightContinuous_gain M hMRight
  have hTargetAdapted : StronglyAdapted F target := by
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hGainAdapted
      (isStoppingTime_const F T) hGainRight
  have hIntegrandBound : ∀ u, ∀ᵐ omega ∂mu,
      |H.integrand u omega| ≤ (C : Real) := by
    intro u
    exact Filter.Eventually.of_forall fun omega =>
      (H.abs_integrand_le_coefficientAbsSum u omega).trans (by
        exact_mod_cast hCoefficient omega)
  have hApproximantMartingale : ∀ r, Martingale (approximant r) F mu := by
    intro r
    have hGridMartingale : Martingale
        ((grid r).martingaleIntegralProcess H.integrand M) F mu := by
      exact (grid r).martingaleIntegralProcess_isMartingale
        hM hMRight H.integrand_isStronglyPredictable
        (fun _ => hIntegrandBound _)
    have hGridRight : ∀ omega u, ContinuousWithinAt
        ((grid r).martingaleIntegralProcess H.integrand M · omega)
          (Ici u) u :=
      (grid r).martingaleIntegralProcess_rightContinuous
        H.integrand M hMRight
    exact RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hGridMartingale (isStoppingTime_const F T) hGridRight
  have hLimit : ∀ u, ∀ᵐ omega ∂mu,
      Tendsto (fun r => approximant r u omega)
        atTop (nhds (target u omega)) := by
    intro u
    exact Filter.Eventually.of_forall fun omega => by
      simp only [approximant, target, stoppedProcess_const_apply]
      exact H.tendsto_horizonGrid_martingaleIntegralProcess_of_le
        M hMRight (min_le_right u T) omega
  have hEnvelopeMem : MemLp envelope (2 : ENNReal) mu :=
    FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
      hM T hMT
  have hBoundMem : MemLp bound (2 : ENNReal) mu := by
    exact hEnvelopeMem.const_mul (2 * (C : Real))
  have hEnvelopeDominates : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ‖M t omega‖ ≤ envelope omega :=
    FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      hM T hMT hMRight
  have hApproximantBound : ∀ r u, ∀ᵐ omega ∂mu,
      ‖approximant r u omega‖ ≤ ‖bound omega‖ := by
    intro r u
    filter_upwards [hEnvelopeDominates] with omega homega
    simp only [approximant, stoppedProcess_const_apply]
    have hRaw := H.norm_horizonGrid_martingaleIntegralProcess_le_of_le
      M (min_le_right u T) omega (envelope omega) homega r
    have hEnvelopeNonnegative : 0 ≤ envelope omega := Real.sqrt_nonneg _
    have hRealCoefficient : H.coefficientAbsSum omega ≤ (C : Real) := by
      exact_mod_cast hCoefficient omega
    have hBoundNonnegative : 0 ≤ 2 * (C : Real) * envelope omega :=
      mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg C))
        hEnvelopeNonnegative
    calc
      ‖(grid r).martingaleIntegralProcess H.integrand M (min u T) omega‖ ≤
          2 * H.coefficientAbsSum omega * envelope omega := hRaw
      _ ≤ 2 * (C : Real) * envelope omega := by
        nlinarith [H.coefficientAbsSum_nonneg omega]
      _ = ‖bound omega‖ := by
        rw [show bound omega = 2 * (C : Real) * envelope omega by rfl,
          Real.norm_eq_abs, abs_of_nonneg hBoundNonnegative]
  let B : NNReal := (eLpNorm bound (2 : ENNReal) mu).toNNReal
  have hBCoe : (B : ENNReal) = eLpNorm bound (2 : ENNReal) mu :=
    ENNReal.coe_toNNReal hBoundMem.eLpNorm_ne_top
  have hNormBound : ∀ r u,
      eLpNorm (approximant r u) (2 : ENNReal) mu ≤ B := by
    intro r u
    rw [hBCoe]
    exact eLpNorm_mono_ae
      ((hApproximantMartingale r).integrable u).aestronglyMeasurable
      (hApproximantBound r u)
  change Martingale target F mu
  exact Martingale.of_ae_tendsto_of_eLpNorm_two_le
    approximant target hApproximantMartingale hTargetAdapted
      hLimit B hNormBound

end PredictableElementaryStrategy

end FTAPTheorem42
