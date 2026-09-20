/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticConvexification
import FTAPTheorem42.Stochastic.Martingale.Regularization.TerminalL1MartingaleProcessCompletion
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernel

/-!
# Process limits of quadratic approximations for finite-horizon M² martingales

Uniform integrability of the terminal squared-increment sums supplies one
mass-preserving forward convexification.  Its complementary martingale
terminals converge in `L¹`.  The weak-`L¹` martingale completion theorem then
selects a subsequence converging uniformly outside one null set.  The exact
square decomposition transfers this uniform convergence to the quadratic
parts, while the terminal limit retains the full centered energy.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SquareIntegrableMartingaleQuadraticProcessLimit

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification
open SquareIntegrableMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticConvexification

/-- A finite convex combination of general finite-horizon `M²` quadratic
martingale terms remains a true martingale. -/
theorem martingalePart_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {n : Nat} (w : TailConvexWeights n) :
    Martingale
      (BoundedMartingaleQuadraticConvexification.martingalePart M T w)
      F mu := by
  classical
  have hFinite : forall s : Finset Nat,
      Martingale
        (∑ i ∈ s, w.weight i •
          BoundedMartingaleQuadraticApproximation.martingalePart M T i)
        F mu := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact martingale_zero Real F mu
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (SquareIntegrableMartingaleQuadraticApproximation.martingalePart_isMartingale
          hM hMRight T hMT i).smul
            (w.weight i) |>.add ih
  exact hFinite w.support

omit [MeasurableSpace Omega] in
/-- The terminal values of the process-level convexification are exactly the
corresponding rows of the original forward-convex family. -/
theorem martingalePart_terminal_eq_forwardApply
    (M : Process Omega) (T : NNReal) (W : ForwardConvexWeights) (n : Nat) :
    BoundedMartingaleQuadraticConvexification.martingalePart
        M T (W.tailRow n) T =
      W.apply (fun i =>
        BoundedMartingaleQuadraticApproximation.martingalePart M T i T) n := by
  funext omega
  rw [BoundedMartingaleQuadraticConvexification.martingalePart_apply]
  rfl

omit [MeasurableSpace Omega] in
/-- The same row identity for the squared-increment processes. -/
theorem squaredIncrementPart_terminal_eq_forwardApply
    (M : Process Omega) (T : NNReal) (W : ForwardConvexWeights) (n : Nat) :
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        M T (W.tailRow n) T =
      W.apply (fun i =>
        BoundedMartingaleQuadraticApproximation.squaredIncrementPart M T i T) n := by
  funext omega
  rw [BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply]
  rfl

/-- A finite-horizon `M²` martingale has mass-preserving forward-convex
quadratic approximations whose martingale and quadratic parts converge
uniformly almost surely along one strict subsequence. -/
theorem exists_forwardConvex_quadraticLimit
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    ∃ (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat)
        (Y : Process Omega),
      StrictMono cutoff ∧
      Martingale Y F mu ∧
      (forall omega t,
        ContinuousWithinAt (Y · omega) (Ici t) t) ∧
      (forall t, T <= t -> Y t =ᵐ[mu] Y T) ∧
      (∀ᵐ omega ∂mu, TendstoUniformly
        (fun k t =>
          BoundedMartingaleQuadraticConvexification.martingalePart
            M T (w (cutoff k)) t omega)
        (fun t => Y t omega) atTop) ∧
      (∀ᵐ omega ∂mu, TendstoUniformly
        (fun k t =>
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart
            M T (w (cutoff k)) t omega)
        (fun t => deterministicallyStoppedProcess M T t omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega) atTop) ∧
      (∀ᵐ omega ∂mu, forall t,
        0 <= deterministicallyStoppedProcess M T t omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega) ∧
      (forall omega t, ContinuousWithinAt
        (fun u => deterministicallyStoppedProcess M T u omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y u omega) (Ici t) t) ∧
      (∫ omega, deterministicallyStoppedProcess M T T omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y T omega ∂mu) =
        ∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu ∧
      ∃ hYT : MemLp (Y T) 1 mu,
        hYT.toLp (Y T) =
          limUnder atTop (fun n =>
            ((memLp_one_iff_integrable.mpr
              ((SquareIntegrableMartingaleQuadraticProcessLimit.martingalePart_isMartingale
                hM hMRight T hMT
                (w n)).integrable T))).toLp
              (BoundedMartingaleQuadraticConvexification.martingalePart
                M T (w n) T)) := by
  obtain ⟨W, A, hQuadraticAE, hAMemLp, hANonnegative, _hQuadraticL1,
      hMass, hMartingaleL1⟩ :=
    exists_forwardConvex_terminal_tendstoAE_L1_integral_eq
      hM hMRight T hMT
  let w : forall n, TailConvexWeights n := fun n => W.tailRow n
  let X : Nat -> Process Omega := fun n =>
    BoundedMartingaleQuadraticConvexification.martingalePart M T (w n)
  let Q : Nat -> Process Omega := fun n =>
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart M T (w n)
  let N : Omega -> Real := fun omega =>
    M T omega ^ 2 - M 0 omega ^ 2 - A omega
  have hMZero : MemLp (M 0) (2 : ENNReal) mu :=
    (MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
      hM bot_le hMT).1
  have hNIntegrable : Integrable N mu := by
    dsimp only [N]
    exact (hMT.integrable_sq.sub hMZero.integrable_sq).sub
      (hAMemLp.integrable (by norm_num))
  have hNMemLp : MemLp N 1 mu :=
    memLp_one_iff_integrable.mpr hNIntegrable
  have hXMartingale : forall n, Martingale (X n) F mu := by
    intro n
    exact martingalePart_isMartingale hM hMRight T hMT (w n)
  have hTerminal : forall n, MemLp (X n T) 1 mu := fun n =>
    memLp_one_iff_integrable.mpr ((hXMartingale n).integrable T)
  have hTerminalEq : forall n,
      X n T = W.apply (fun i =>
        BoundedMartingaleQuadraticApproximation.martingalePart M T i T) n := by
    intro n
    dsimp only [X, w]
    exact martingalePart_terminal_eq_forwardApply M T W n
  have hTerminalTendsto : Tendsto
      (fun n => (hTerminal n).toLp (X n T)) atTop
      (nhds (hNMemLp.toLp N)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => X n T) hTerminal N hNMemLp).mpr
    have hNormEq : (fun n => eLpNorm (X n T - N) 1 mu) =
        fun n => eLpNorm
          (W.apply (fun i =>
            BoundedMartingaleQuadraticApproximation.martingalePart M T i T) n -
              fun omega => M T omega ^ 2 - M 0 omega ^ 2 - A omega)
          1 mu := by
      funext n
      rw [hTerminalEq n]
    rw [hNormEq]
    exact hMartingaleL1
  have hTerminalCauchy : CauchySeq
      (fun n => (hTerminal n).toLp (X n T)) :=
    hTerminalTendsto.cauchySeq
  obtain ⟨cutoff, hCutoff, Y, hYMartingale, hYRight, hYConstant,
      hMartingaleUniform, hYT, hYTLimit⟩ :=
    ChronologicalGrid.exists_rightContinuous_martingale_of_terminalL1_cauchy
      hUsual X T hXMartingale
      (fun n => BoundedMartingaleQuadraticConvexification.martingalePart_rightContinuous
        M hMRight T (w n))
      (fun n t ht => BoundedMartingaleQuadraticConvexification.martingalePart_constantAfter
        M T (w n) ht)
      hTerminal hTerminalCauchy
  have hSquaredUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun k t => Q (cutoff k) t omega)
      (fun t => deterministicallyStoppedProcess M T t omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega) atTop := by
    filter_upwards [hMartingaleUniform] with omega hUniform
    rw [Metric.tendstoUniformly_iff] at hUniform ⊢
    intro epsilon hepsilon
    filter_upwards [hUniform epsilon hepsilon] with k hk
    intro t
    have hDecomposition :=
      BoundedMartingaleQuadraticConvexification.martingalePart_add_squaredIncrementPart
        M T t (w (cutoff k)) omega
    have hQEq : Q (cutoff k) t omega =
        deterministicallyStoppedProcess M T t omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - X (cutoff k) t omega := by
      dsimp only [Q, X]
      linarith
    rw [hQEq]
    have hkt := hk t
    rw [Real.dist_eq] at hkt ⊢
    calc
      |deterministicallyStoppedProcess M T t omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega -
          (deterministicallyStoppedProcess M T t omega ^ 2 -
            deterministicallyStoppedProcess M T 0 omega ^ 2 - X (cutoff k) t omega)| =
          |X (cutoff k) t omega - Y t omega| := by
        congr 1
        ring
      _ = |Y t omega - X (cutoff k) t omega| := abs_sub_comm _ _
      _ < epsilon := hkt
  have hLimitNonnegative : ∀ᵐ omega ∂mu, forall t,
      0 <= deterministicallyStoppedProcess M T t omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega := by
    filter_upwards [hSquaredUniform] with omega hUniform
    intro t
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (hUniform.tendsto_at t) (Filter.Eventually.of_forall fun k =>
        BoundedMartingaleQuadraticConvexification.squaredIncrementPart_nonneg
          M T t (w (cutoff k)) omega)
  have hLimitRight : forall omega t, ContinuousWithinAt
      (fun u => deterministicallyStoppedProcess M T u omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y u omega) (Ici t) t := by
    intro omega t
    exact (((stoppedSource_rightContinuous M hMRight T omega t).pow 2).sub
      continuousWithinAt_const).sub (hYRight omega t)
  have hSelectedQuadraticAE : TendstoAE mu
      (fun k => W.apply (fun n =>
        BoundedMartingaleQuadraticApproximation.squaredIncrementPart M T n T)
          (cutoff k)) A :=
    hQuadraticAE.comp_strictMono hCutoff
  have hRawTerminalAE : TendstoAE mu
      (fun k => W.apply (fun n =>
        BoundedMartingaleQuadraticApproximation.squaredIncrementPart M T n T)
          (cutoff k))
      (fun omega => deterministicallyStoppedProcess M T T omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y T omega) := by
    filter_upwards [hSquaredUniform] with omega hUniform
    simpa only [Q, w, squaredIncrementPart_terminal_eq_forwardApply]
      using hUniform.tendsto_at T
  have hRawTerminalEq : (fun omega =>
      deterministicallyStoppedProcess M T T omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y T omega) =ᵐ[mu] A :=
    by
      filter_upwards [hRawTerminalAE, hSelectedQuadraticAE]
        with omega hRaw hSelected
      exact tendsto_nhds_unique hRaw hSelected
  have hRawMass :
      (∫ omega, deterministicallyStoppedProcess M T T omega ^ 2 -
          deterministicallyStoppedProcess M T 0 omega ^ 2 - Y T omega ∂mu) =
        ∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu := by
    rw [integral_congr_ae hRawTerminalEq]
    exact hMass
  refine ⟨w, cutoff, Y, hCutoff, hYMartingale, hYRight, hYConstant,
    ?_, ?_, hLimitNonnegative, hLimitRight, hRawMass, hYT, ?_⟩
  · simpa only [X] using hMartingaleUniform
  · simpa only [Q] using hSquaredUniform
  · exact hYTLimit

end SquareIntegrableMartingaleQuadraticProcessLimit

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Quadratic energy kernels for finite-horizon M² martingales

The mass-preserving `L¹` process limit of the factorial-grid square
decompositions satisfies the same nested-grid monotonicity argument as in the
bounded case.  After null-set regularization it therefore supplies the
existing quadratic-kernel `Data`, with no pathwise boundedness assumption on
the source martingale.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SquareIntegrableMartingaleQuadraticKernel

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticKernel
open SquareIntegrableMartingaleQuadraticProcessLimit

/-- Every finite-horizon true `M²` martingale produces the concrete
quadratic-variation data used by the predictable energy measure and completed
stochastic-integral construction. -/
theorem exists_data
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Nonempty (BoundedMartingaleQuadraticKernel.Data F mu M T) := by
  obtain ⟨w, cutoff, Y, hCutoff, hY, hYRight, _hYConstant,
      hMartingaleUniform, hSquaredUniform, _hNonnegative, hRawRight,
      _hMass, hYT, _hYTLimit⟩ :=
    exists_forwardConvex_quadraticLimit hUsual hM hMRight T hMT
  have hRawMonotone : ∀ᵐ omega ∂mu,
      Monotone (BoundedMartingaleQuadraticKernel.rawVariation M T Y · omega) :=
    BoundedMartingaleQuadraticVariation.quadraticLimit_monotone
      M T w cutoff hCutoff Y hSquaredUniform hRawRight
  exact BoundedMartingaleQuadraticKernel.exists_data_of_quadraticVariation
    hUsual hM hMRight T hMT w cutoff Y hCutoff hY hYRight
    hMartingaleUniform hSquaredUniform hRawRight hRawMonotone
    (hYT.integrable (by norm_num))

end SquareIntegrableMartingaleQuadraticKernel

end FTAPTheorem42
