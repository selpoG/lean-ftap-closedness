/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernelTerminalRootLimit
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernelDavisConsumer

/-!
# Stopping consistency of finite-horizon quadratic variation

This module proves the process-level stopping consistency which is needed to
reuse the deterministic-horizon Davis estimate after a bounded stopping time.
The two deterministic grids need not be the same when their horizons differ,
so the proof compares the two raw square decompositions directly.  The
stopped variation supplied by the first data set is compared with the second
data set by the common stopped-source path, the jump-square identities, and
predictable finite-variation local-martingale rigidity.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticKernel.Data

open BoundedMartingaleQuadraticKernel
open PredictableFiniteVariationLocalMartingale

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M N : Process Omega} {T U : NNReal}

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
theorem stoppedSource_stoppedProcess_eq_at
    (M N : Process Omega) (T U : NNReal) (tau : Omega → NNReal)
    (hTauT : ∀ omega, tau omega ≤ T)
    (hTauU : ∀ omega, tau omega ≤ U)
    (omega : Omega)
    (hN : ∀ t, N t omega =
      MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal)) t omega) :
    ∀ t,
      deterministicallyStoppedProcess N U t omega =
        MeasureTheory.stoppedProcess
          (deterministicallyStoppedProcess M T)
          (fun omega => (tau omega : WithTop NNReal)) t omega := by
  intro t
  by_cases hle : (t : WithTop NNReal) ≤
      (tau omega : WithTop NNReal)
  · have htTau : t ≤ tau omega := WithTop.coe_le_coe.mp hle
    have htU : t ≤ U := htTau.trans (hTauU omega)
    have htT : t ≤ T := htTau.trans (hTauT omega)
    rw [deterministicallyStoppedProcess_apply,
      min_eq_left htU, hN t]
    have hMinA :
        (min (t : WithTop NNReal) (tau omega : WithTop NNReal)).untopA = t := by
      rw [min_eq_left hle,
        WithTop.untopA_eq_untop (WithTop.coe_ne_top :
          (t : WithTop NNReal) ≠ ⊤),
        WithTop.untop_coe t (by exact WithTop.coe_ne_top)]
    have hNStop :
        MeasureTheory.stoppedProcess M
            (fun omega => (tau omega : WithTop NNReal)) t omega =
          M t omega := by
      change M (min (t : WithTop NNReal)
        (tau omega : WithTop NNReal)).untopA omega = M t omega
      rw [hMinA]
    have hXStop :
        MeasureTheory.stoppedProcess
            (deterministicallyStoppedProcess M T)
            (fun omega => (tau omega : WithTop NNReal)) t omega =
          M t omega := by
      change deterministicallyStoppedProcess M T
        (min (t : WithTop NNReal)
          (tau omega : WithTop NNReal)).untopA omega = M t omega
      rw [hMinA, deterministicallyStoppedProcess_apply,
        min_eq_left htT]
    rw [hNStop, hXStop]
  · have hlt : (tau omega : WithTop NNReal) < (t : WithTop NNReal) :=
      lt_of_not_ge hle
    have htTau : tau omega ≤ t := WithTop.coe_le_coe.mp hlt.le
    have hTauU : tau omega ≤ U := hTauU omega
    have hTauMinU : (tau omega : WithTop NNReal) ≤
        (min t U : WithTop NNReal) := by
      exact WithTop.coe_le_coe.mpr (le_min htTau hTauU)
    have hNStop :
        MeasureTheory.stoppedProcess M
            (fun omega => (tau omega : WithTop NNReal)) (min t U) omega =
          M (tau omega) omega := by
      change M (min (min t U : WithTop NNReal)
        (tau omega : WithTop NNReal)).untopA omega = M (tau omega) omega
      have hMinA :
          (min (min t U : WithTop NNReal)
            (tau omega : WithTop NNReal)).untopA = tau omega := by
        rw [min_eq_right hTauMinU,
          WithTop.untopA_eq_untop (WithTop.coe_ne_top :
            (tau omega : WithTop NNReal) ≠ ⊤),
          WithTop.untop_coe (tau omega) (by exact WithTop.coe_ne_top)]
      rw [hMinA]
    have hXStop :
        MeasureTheory.stoppedProcess
            (deterministicallyStoppedProcess M T)
            (fun omega => (tau omega : WithTop NNReal)) t omega =
          M (tau omega) omega := by
      change deterministicallyStoppedProcess M T
        (min (t : WithTop NNReal)
          (tau omega : WithTop NNReal)).untopA omega = M (tau omega) omega
      have hMinA :
          (min (t : WithTop NNReal)
            (tau omega : WithTop NNReal)).untopA = tau omega := by
        rw [min_eq_right hlt.le,
          WithTop.untopA_eq_untop (WithTop.coe_ne_top :
            (tau omega : WithTop NNReal) ≠ ⊤),
          WithTop.untop_coe (tau omega) (by exact WithTop.coe_ne_top)]
      rw [hMinA, deterministicallyStoppedProcess_apply,
        min_eq_left (hTauT omega)]
    rw [deterministicallyStoppedProcess_apply,
      hN (min t U), hNStop, hXStop]

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
theorem stoppedProcess_rawVariation_eq
    (M : Process Omega) (T : NNReal) (Y : Process Omega)
    (tau : Omega → NNReal) :
    ∀ omega t,
      MeasureTheory.stoppedProcess
          (BoundedMartingaleQuadraticKernel.rawVariation M T Y)
          (fun omega => (tau omega : WithTop NNReal)) t omega =
        (MeasureTheory.stoppedProcess
            (deterministicallyStoppedProcess M T)
            (fun omega => (tau omega : WithTop NNReal)) t omega) ^ 2 -
          (MeasureTheory.stoppedProcess
            (deterministicallyStoppedProcess M T)
            (fun omega => (tau omega : WithTop NNReal)) 0 omega) ^ 2 -
          MeasureTheory.stoppedProcess Y
          (fun omega => (tau omega : WithTop NNReal)) t omega := by
  intro omega t
  let X : Process Omega :=
    deterministicallyStoppedProcess M T
  have hZero :
      MeasureTheory.stoppedProcess X
          (fun omega => (tau omega : WithTop NNReal)) 0 omega = X 0 omega := by
    change X (min (0 : WithTop NNReal)
      (tau omega : WithTop NNReal)).untopA omega = X 0 omega
    have hMin :
        min (0 : WithTop NNReal) (tau omega : WithTop NNReal) =
          (0 : WithTop NNReal) := min_eq_left (bot_le :
            (0 : WithTop NNReal) ≤ (tau omega : WithTop NNReal))
    rw [hMin, WithTop.untopA_eq_untop (by simp), WithTop.untop_zero]
  change X (min (t : WithTop NNReal)
      (tau omega : WithTop NNReal)).untopA omega ^ 2 - X 0 omega ^ 2 -
      Y (min (t : WithTop NNReal)
        (tau omega : WithTop NNReal)).untopA omega =
    X (min (t : WithTop NNReal)
        (tau omega : WithTop NNReal)).untopA omega ^ 2 -
      (MeasureTheory.stoppedProcess X
        (fun omega => (tau omega : WithTop NNReal)) 0 omega) ^ 2 -
      Y (min (t : WithTop NNReal)
        (tau omega : WithTop NNReal)).untopA omega
  rw [hZero]

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F] in
theorem stoppedProcess_coe_apply
    (X : Process Omega) (tau : Omega → NNReal) (t : NNReal) (omega : Omega) :
    MeasureTheory.stoppedProcess X
        (fun omega => (tau omega : WithTop NNReal)) t omega =
      X (min t (tau omega)) omega := by
  change X (min (t : WithTop NNReal)
      (tau omega : WithTop NNReal)).untopA omega = _
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop
    (WithTop.coe_ne_top : (↑(min t (tau omega)) : WithTop NNReal) ≠ ⊤),
    WithTop.untop_coe]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem variation_nonnegative_stop
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    ∀ omega t, 0 ≤ Q.variation t omega := by
  intro omega t
  have hZero : Q.variation 0 omega = 0 := by
    simpa using congrFun Q.variation_zero omega
  have hMono := Q.variation_monotone omega (show (0 : NNReal) ≤ t from bot_le)
  change Q.variation 0 omega ≤ Q.variation t omega at hMono
  rw [hZero] at hMono
  exact hMono

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem variation_boundedVariation_stop
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    ∀ omega, BoundedVariationOn (Q.variation · omega) Set.univ := by
  intro omega
  exact HorizonFactorialGrid.boundedVariationOn_of_monotone_nonnegative_constantAfter
    (variation_nonnegative_stop Q) Q.variation_monotone Q.variation_constantAfter omega

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem variation_hasLeftLimits_stop
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T) :
    ProcessHasLeftLimits Q.variation := by
  intro omega t
  exact (variation_boundedVariation_stop Q omega).tendsto_leftLim t

/-- A bounded stopping time transports the regularized quadratic variation
from one finite-horizon martingale to any indistinguishable stopped source.
The proof uses the two raw square decompositions and their common jump-square
identity; the predictable energy-measure restriction is not used as a
pathwise shortcut. -/
theorem variation_processIndistinguishable_of_bounded_stop
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (_hM : Martingale M F mu)
    (_hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (_hN : Martingale N F mu)
    (_hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    (tau : Omega → NNReal)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : ∀ omega, tau omega ≤ T)
    (hTauU : ∀ omega, tau omega ≤ U)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal)))) :
    ProcessIndistinguishable mu R.variation
      (MeasureTheory.stoppedProcess Q.variation
        (fun omega => (tau omega : WithTop NNReal))) := by
  let tauTop : Omega → WithTop NNReal :=
    fun omega => (tau omega : WithTop NNReal)
  let X : Process Omega :=
    deterministicallyStoppedProcess M T
  let P : Process Omega :=
    MeasureTheory.stoppedProcess Q.variation tauTop
  let Z : Process Omega :=
    MeasureTheory.stoppedProcess Q.martingalePart tauTop
  have hQLeft : ProcessHasLeftLimits Q.variation :=
    variation_hasLeftLimits_stop Q
  have hRLeft : ProcessHasLeftLimits R.variation :=
    variation_hasLeftLimits_stop R
  have hPLeft : ProcessHasLeftLimits P := by
    dsimp [P]
    exact hQLeft.stoppedProcess tauTop
  have hPAdapted : StronglyAdapted F P := by
    dsimp [P]
    exact RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      Q.variation_isStronglyAdapted hTau Q.variation_rightContinuous
  have hPRight : ∀ omega t,
      ContinuousWithinAt (P · omega) (Ici t) t := by
    dsimp [P]
    exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      Q.variation (τ := tauTop) Q.variation_rightContinuous
  have hPNonnegative : ∀ omega t, 0 ≤ P t omega := by
    intro omega t
    change 0 ≤ MeasureTheory.stoppedProcess Q.variation tauTop t omega
    rw [stoppedProcess_coe_apply Q.variation tau t omega]
    exact variation_nonnegative_stop Q omega (min t (tau omega))
  have hPMonotone : ∀ omega, Monotone (P · omega) := by
    intro omega s t hst
    change MeasureTheory.stoppedProcess Q.variation tauTop s omega ≤
      MeasureTheory.stoppedProcess Q.variation tauTop t omega
    rw [stoppedProcess_coe_apply Q.variation tau s omega,
      stoppedProcess_coe_apply Q.variation tau t omega]
    exact Q.variation_monotone omega (min_le_min_right _ hst)
  have hPBV : ∀ omega, BoundedVariationOn (P · omega) Set.univ := by
    intro omega
    apply (monotoneOn_univ.2 (hPMonotone omega)).boundedVariationOn
      (C := Q.variation (tau omega) omega)
    intro t _
    rw [abs_of_nonneg (hPNonnegative omega t)]
    change Q.variation (min t (tau omega)) omega ≤
      Q.variation (tau omega) omega
    exact Q.variation_monotone omega (min_le_right _ _)
  have hRawP : ProcessIndistinguishable mu P
      (BoundedMartingaleQuadraticKernel.rawVariation N U Z) := by
    have hQRaw := Q.variation_indistinguishable_raw.stoppedProcess tauTop
    filter_upwards [hQRaw, hNDef] with omega hQRawOmega hNPath
    intro t
    have hSourcePath : ∀ s,
        deterministicallyStoppedProcess N U s omega =
          MeasureTheory.stoppedProcess X tauTop s omega := by
      intro s
      exact stoppedSource_stoppedProcess_eq_at M N T U tau hTauT hTauU omega
        hNPath s
    change P t omega =
      BoundedMartingaleQuadraticKernel.rawVariation N U Z t omega
    calc
      P t omega = MeasureTheory.stoppedProcess
          (BoundedMartingaleQuadraticKernel.rawVariation M T
            Q.martingalePart) tauTop t omega := hQRawOmega t
      _ = (MeasureTheory.stoppedProcess X tauTop t omega) ^ 2 -
          (MeasureTheory.stoppedProcess X tauTop 0 omega) ^ 2 -
          MeasureTheory.stoppedProcess Q.martingalePart tauTop t omega := by
        simpa only [X] using
          stoppedProcess_rawVariation_eq M T Q.martingalePart tau omega t
      _ = (deterministicallyStoppedProcess N U t omega) ^ 2 -
          (deterministicallyStoppedProcess N U 0 omega) ^ 2 -
          Z t omega := by
        rw [hSourcePath t, hSourcePath 0]
      _ = BoundedMartingaleQuadraticKernel.rawVariation N U Z t omega := by
        rfl
  have hPJumpSource : ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump P t omega =
        processLeftJump
          (deterministicallyStoppedProcess N U)
          t omega ^ 2 := by
    filter_upwards [Q.processLeftJump_variation_eq_sq hMLeft, hNDef]
      with omega hQJump hNPath
    have hXLeft : ProcessHasLeftLimits X := by
      dsimp [X]
      exact hMLeft.stoppedProcess
        (fun _ : Omega => (T : WithTop NNReal))
    have hSourcePath : ∀ s,
        (deterministicallyStoppedProcess N U) s omega =
          MeasureTheory.stoppedProcess X tauTop s omega := by
      intro s
      exact stoppedSource_stoppedProcess_eq_at M N T U tau hTauT hTauU omega
        hNPath s
    have hSourceJump (t : NNReal) :
        processLeftJump
            (deterministicallyStoppedProcess N U)
            t omega = processLeftJump (MeasureTheory.stoppedProcess X tauTop)
            t omega := by
      have hSourcePath' :
          (fun s =>
            (deterministicallyStoppedProcess N U) s omega) =
          (fun s => MeasureTheory.stoppedProcess X tauTop s omega) := by
        funext s
        exact hSourcePath s
      unfold processLeftJump
      rw [hSourcePath t, hSourcePath']
    intro t
    have hQJumpAt : processLeftJump Q.variation t omega =
        processLeftJump X t omega ^ 2 := by
      simpa only [X] using hQJump t
    change processLeftJump (MeasureTheory.stoppedProcess Q.variation
      tauTop) t omega = _
    by_cases hle : (t : WithTop NNReal) ≤ tauTop omega
    · rw [processLeftJump_stoppedProcess_eq_of_le Q.variation hQLeft
          tauTop t omega hle,
        hQJumpAt, hSourceJump t,
        processLeftJump_stoppedProcess_eq_of_le X hXLeft tauTop t omega hle]
    · have hlt : tauTop omega < (t : WithTop NNReal) := lt_of_not_ge hle
      rw [processLeftJump_stoppedProcess_eq_zero_of_lt Q.variation
          tauTop t omega hlt,
        hSourceJump t,
        processLeftJump_stoppedProcess_eq_zero_of_lt X tauTop t omega hlt]
      norm_num
  let A : Process Omega := fun t omega =>
    P t omega - R.variation t omega
  let Aleft : Process Omega := fun t omega =>
    Function.leftLim (A · omega) t
  have hALeft : ProcessHasLeftLimits A := by
    exact hPLeft.sub hRLeft
  have hAAdapted : StronglyAdapted F A := by
    exact hPAdapted.sub R.variation_isStronglyAdapted
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    intro omega t
    exact (hPRight omega t).sub (R.variation_rightContinuous omega t)
  have hAJump : ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump A t omega = 0 := by
    filter_upwards [hPJumpSource,
      R.processLeftJump_variation_eq_sq hNLeft] with omega hPJump hRJump
    intro t
    change processLeftJump
      (fun s omega' => P s omega' - R.variation s omega') t omega = 0
    rw [processLeftJump_sub hPLeft hRLeft, hPJump t, hRJump t]
    ring
  have hAContinuous : ∀ᵐ omega ∂mu, Continuous (A · omega) := by
    filter_upwards [hAJump] with omega hJump
    apply continuous_of_rightContinuous_of_processLeftJump_eq_zero
      (A · omega) (hARight omega) (hALeft omega)
    intro t
    simpa only [processLeftJump] using hJump t
  have hABoundedVariation : ∀ omega,
      BoundedVariationOn (A · omega) Set.univ := by
    intro omega
    change BoundedVariationOn
      (fun t => P t omega - R.variation t omega) Set.univ
    exact boundedVariationOn_add (hPBV omega) (boundedVariationOn_neg
      (variation_boundedVariation_stop R omega))
  have hAleftPredictable : IsStronglyPredictable F Aleft := by
    exact ProcessHasLeftLimits.stronglyPredictable_leftLim hALeft hAAdapted
  have hAleftBoundedVariation : ∀ omega,
      BoundedVariationOn (Aleft · omega) Set.univ := by
    intro omega
    change BoundedVariationOn
      (Function.leftLim (A · omega)) Set.univ
    exact (hABoundedVariation omega).leftLim
  have hAleftRegular : ∀ᵐ omega ∂mu,
      (∀ t, ContinuousWithinAt (Aleft · omega) (Ici t) t) ∧
        BoundedVariationOn (Aleft · omega) Set.univ := by
    filter_upwards [hAContinuous] with omega hContinuous
    have hPath : (Aleft · omega) = (A · omega) := by
      funext t
      dsimp [Aleft]
      exact hContinuous.continuousWithinAt.leftLim_eq
    refine ⟨?_, hAleftBoundedVariation omega⟩
    rw [hPath]
    exact hARight omega
  obtain ⟨Aregular, hAregularPredictable, hAregularRight,
      hAregularBoundedVariation, hAregularLeft⟩ :=
    ProcessNullSetRegularization.exists_predictable_rightContinuous_boundedVariation_version
      hUsual hAleftPredictable hAleftRegular
  have hAleftA : ProcessIndistinguishable mu Aleft A := by
    filter_upwards [hAContinuous] with omega hContinuous
    intro t
    dsimp [Aleft]
    exact hContinuous.continuousWithinAt.leftLim_eq
  have hAregularA : ProcessIndistinguishable mu Aregular A :=
    hAregularLeft.trans hAleftA
  let B : Process Omega := fun t omega =>
    R.martingalePart t omega - Z t omega
  have hAB : ProcessIndistinguishable mu A B := by
    have hRaw := ProcessIndistinguishable.sub hRawP
      R.variation_indistinguishable_raw
    filter_upwards [hRaw] with omega hRawOmega
    intro t
    change P t omega - R.variation t omega =
      R.martingalePart t omega - Z t omega
    calc
      P t omega - R.variation t omega =
          BoundedMartingaleQuadraticKernel.rawVariation N U Z t omega -
          BoundedMartingaleQuadraticKernel.rawVariation N U
            R.martingalePart t omega := hRawOmega t
      _ = R.martingalePart t omega - Z t omega := by
        rw [BoundedMartingaleQuadraticKernel.rawVariation_apply,
          BoundedMartingaleQuadraticKernel.rawVariation_apply]
        ring
  have hZMartingale : Martingale Z F mu := by
    dsimp [Z]
    exact RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      Q.martingalePart_isMartingale hTau Q.martingalePart_rightContinuous
  have hBMartingale : Martingale B F mu := by
    change Martingale (R.martingalePart - Z) F mu
    exact R.martingalePart_isMartingale.sub hZMartingale
  have hAMartingale : Martingale A F mu := by
    apply hBMartingale.congr hAAdapted
    intro t
    exact (hAB.eventuallyEq_at t).symm
  have hAregularMartingale : Martingale Aregular F mu := by
    apply hAMartingale.congr hAregularPredictable.stronglyAdapted
    intro t
    exact (hAregularA.eventuallyEq_at t).symm
  have hAregularLocal : LocalMartingale Aregular F mu :=
    ProbabilityTheory.Locally.of_prop hAregularMartingale
  have hAregularInitial :=
    indistinguishable_initial_of_predictableFiniteVariationLocalMartingale
      hUsual Aregular hAregularLocal hAregularPredictable hAregularRight
      hAregularBoundedVariation
  have hPZero : P 0 = 0 := by
    funext omega
    change MeasureTheory.stoppedProcess Q.variation tauTop 0 omega = 0
    rw [stoppedProcess_coe_apply Q.variation tau 0 omega]
    have hmin : min (0 : NNReal) (tau omega) = 0 := min_eq_left bot_le
    rw [hmin]
    exact congrFun Q.variation_zero omega
  have hAZero : A 0 = 0 := by
    funext omega
    dsimp [A]
    rw [hPZero, congrFun R.variation_zero omega]
    ring
  have hAregularZero : Aregular 0 =ᵐ[mu] 0 := by
    filter_upwards [hAregularA.eventuallyEq_at 0] with omega hOmega
    have hAZeroOmega : A 0 omega = 0 := congrFun hAZero omega
    exact hOmega.trans hAZeroOmega
  have hAregularInitialZero : ProcessIndistinguishable mu
      (fun (_ : NNReal) omega => Aregular 0 omega)
      (fun (_ : NNReal) (_ : Omega) => 0) := by
    filter_upwards [hAregularZero] with omega hOmega
    intro t
    exact hOmega
  have hAregularZeroProcess : ProcessIndistinguishable mu Aregular
      (fun (_ : NNReal) (_ : Omega) => 0) :=
    hAregularInitial.trans hAregularInitialZero
  have hAZeroProcess : ProcessIndistinguishable mu A
      (fun (_ : NNReal) (_ : Omega) => 0) :=
    hAregularA.symm.trans hAregularZeroProcess
  filter_upwards [hAZeroProcess] with omega hOmega
  intro t
  have hDifference : P t omega - R.variation t omega = 0 := by
    simpa only [A] using hOmega t
  exact (sub_eq_zero.mp hDifference).symm

/-! ## Terminal-root consumers for a bounded stop -/

/-- The terminal root of a quadratic data witness for the stopped source agrees
with the stopped original quadratic coordinate almost everywhere. -/
theorem squareIntegrableMartingaleQuadraticRoot_ae_eq_stopped_of_bounded_stop
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hN : Martingale N F mu)
    (hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    (tau : Omega → NNReal)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : ∀ omega, tau omega ≤ T)
    (hTauU : ∀ omega, tau omega ≤ U)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal)))) :
    SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot R =ᵐ[mu]
      (fun omega => Real.sqrt (Q.variation (tau omega) omega)) := by
  have hVariation := variation_processIndistinguishable_of_bounded_stop
    hUsual hM hMRight hMLeft hN hNRight hNLeft Q R tau hTau hTauT hTauU hNDef
  filter_upwards [hVariation.eventuallyEq_at U] with omega hOmega
  change Real.sqrt (R.variation U omega) =
    Real.sqrt (Q.variation (tau omega) omega)
  rw [hOmega]
  rw [stoppedProcess_coe_apply Q.variation tau U omega,
    min_eq_right (hTauU omega)]

/-- The deterministic Davis envelope estimate for the stopped martingale can
be written directly in the stopped original quadratic coordinate. -/
theorem finiteHorizonAbsoluteEnvelope_integral_le_six_stoppedQuadraticRoot
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hN : Martingale N F mu)
    (hNRight : ∀ omega t,
      ContinuousWithinAt (N · omega) (Ici t) t)
    (hNLeft : ProcessHasLeftLimits N)
    (hN0 : N 0 = 0)
    (hNU : MemLp (N U) (2 : ENNReal) mu)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (R : BoundedMartingaleQuadraticKernel.Data F mu N U)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (tau : Omega → NNReal)
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)))
    (hTauT : ∀ omega, tau omega ≤ T)
    (hTauU : ∀ omega, tau omega ≤ U)
    (hNDef : ProcessIndistinguishable mu N
      (MeasureTheory.stoppedProcess M
        (fun omega => (tau omega : WithTop NNReal)))) :
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      N U omega ∂mu) ≤
      6 * ∫ omega, Real.sqrt (Q.variation (tau omega) omega) ∂mu := by
  have hDavis :=
    finiteHorizonAbsoluteEnvelope_integral_le_six_variationRoot
      R hN hNRight hNLeft hN0 hNU
  have hRoot := squareIntegrableMartingaleQuadraticRoot_ae_eq_stopped_of_bounded_stop
    hUsual hM hMRight hMLeft hN hNRight hNLeft Q R tau hTau hTauT hTauU hNDef
  calc
    (∫ omega, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        N U omega ∂mu) ≤
        6 * ∫ omega,
          SIntegrableFiniteVariationBridge.squareIntegrableMartingaleQuadraticRoot
            R omega ∂mu := hDavis
    _ = 6 * ∫ omega, Real.sqrt (Q.variation (tau omega) omega) ∂mu := by
      exact congrArg (fun x : Real => 6 * x) (integral_congr_ae hRoot)

end BoundedMartingaleQuadraticKernel.Data

end FTAPTheorem42
