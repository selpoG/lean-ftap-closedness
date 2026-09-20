/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralCadlag
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticEnergyUniqueness
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump

/-!
# Jumps of completed finite-horizon martingale integrals

The quadratic-energy atom at a time is the square of the stopped-source
jump.  Consequently, energy-almost-everywhere convergence of elementary
integrands becomes pointwise convergence at every nonzero source jump on
one common full-measure set.  Combining this fact with the pathwise uniform
process completion proves the usual stochastic-integral jump formula.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticEnergy.Data

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticKernel

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {M : Process Omega} {T : NNReal}

omit [SigmaFiniteFiltration mu F] in
/-- A stopped elementary process approximation is exactly the same
elementary gain evaluated against the stopped source. -/
theorem processApproximation_eq_gain_stoppedSource
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) :
    processApproximation D f hfMeas hf n =
      ElementaryStrategy.gain (deterministicallyStoppedProcess M T)
        (elementaryApproximation D f hfMeas hf n).strategy.toElementary := by
  funext t omega
  change ElementaryStrategy.gain M
      (elementaryApproximation D f hfMeas hf n).strategy.toElementary
        (min (t : WithTop NNReal) T).untopA omega = _
  rw [← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  exact (ElementaryStrategy.gain_stoppedProcess M
    (elementaryApproximation D f hfMeas hf n).strategy.toElementary
    (fun _ => T) t omega).symm

omit [SigmaFiniteFiltration mu F] in
/-- Every elementary process approximation has the expected jump against
the stopped source. -/
theorem processLeftJump_processApproximation
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hMLeft : ProcessHasLeftLimits M)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure)
    (n : Nat) (t : NNReal) (omega : Omega) :
    processLeftJump (processApproximation D f hfMeas hf n) t omega =
      elementaryApproximationIntegrand D f hfMeas hf n (t, omega) *
        processLeftJump (deterministicallyStoppedProcess M T) t omega := by
  rw [processApproximation_eq_gain_stoppedSource]
  exact PredictableElementaryStrategy.processLeftJump_gain
    (elementaryApproximation D f hfMeas hf n).strategy
    (deterministicallyStoppedProcess M T)
    (hMLeft.stoppedProcess fun _ : Omega => (T : WithTop NNReal))
    t omega

/-- The selected càdlàg completed integral has jump `f ΔM` at every
time on one common full-measure set. -/
theorem finiteHorizonMartingaleIntegralCadlagProcess_processLeftJump
    (hUsual : Filtration.UsualConditions mu F)
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (f : NNReal × Omega → Real)
    (hfMeas : StronglyMeasurable[F.predictable] f)
    (hf : MemLp f (2 : ENNReal) D.predictableEnergyMeasure) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump
          (finiteHorizonMartingaleIntegralCadlagProcess
            hUsual D hM hMRight hMLeft hMT f hfMeas hf) t omega =
        f (t, omega) * processLeftJump (deterministicallyStoppedProcess M T) t omega := by
  let g : Nat → NNReal × Omega → Real := fun n =>
    elementaryApproximationIntegrand D f hfMeas hf n
  obtain ⟨cutoff, hCutoff, hUniform⟩ :=
    exists_processApproximation_tendstoUniformly_cadlagProcess
      hUsual D hM hMRight hMLeft hMT f hfMeas hf
  have hLp : Tendsto (fun n =>
      (elementaryApproximationIntegrand_memLp
        D f hfMeas hf (cutoff n)).toLp (g (cutoff n)))
      atTop (nhds (hf.toLp f)) := by
    exact (elementaryApproximationIntegrand_tendsto
      D f hfMeas hf).comp hCutoff.tendsto_atTop
  obtain ⟨subseq, hSubseq, hCoeffLp⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  have hCoeffRaw : ∀ᵐ point ∂D.predictableEnergyMeasure,
      Tendsto (fun n => g (cutoff (subseq n)) point) atTop
        (nhds (f point)) := by
    have hApprox : ∀ᵐ point ∂D.predictableEnergyMeasure, ∀ n,
        ((elementaryApproximationIntegrand_memLp
          D f hfMeas hf (cutoff (subseq n))).toLp
            (g (cutoff (subseq n))) :
              NNReal × Omega → Real) point =
          g (cutoff (subseq n)) point :=
      ae_all_iff.2 fun n => MemLp.coeFn_toLp
        (elementaryApproximationIntegrand_memLp
          D f hfMeas hf (cutoff (subseq n)))
    filter_upwards [hCoeffLp, hApprox, MemLp.coeFn_toLp hf]
        with point hPoint hApproxPoint hTargetPoint
    have hPoint' := hPoint.congr'
      (Filter.Eventually.of_forall fun n => hApproxPoint n)
    rwa [hTargetPoint] at hPoint'
  let good : Set (NNReal × Omega) := {point |
    Tendsto (fun n => g (cutoff (subseq n)) point) atTop
      (nhds (f point))}
  have hGoodMeas : MeasurableSet[F.predictable] good := by
    let : MeasurableSpace (NNReal × Omega) := F.predictable
    exact MeasureTheory.measurableSet_tendsto_fun
      (fun n => (elementaryApproximation D f hfMeas hf
        (cutoff (subseq n))).strategy.integrand_isStronglyPredictable.measurable)
      hfMeas.measurable
  have hBadZero : D.predictableEnergyMeasure goodᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hCoeffRaw] with point hPoint
    exact hPoint
  let _ : IsSFiniteKernel D.stieltjesKernel :=
    IncreasingProcessStieltjesKernel.kernel_isSFinite D.variation
      D.variation_monotone D.variation_rightContinuous T
      D.variation_constantAfter D.variation_measurable
  have hBadFiber : ∀ᵐ omega ∂mu,
      D.stieltjesKernel omega
        ((fun t => (t, omega)) ⁻¹' goodᶜ) = 0 := by
    have hIntegral :
        ∫⁻ omega, D.stieltjesKernel omega
          ((fun t => (t, omega)) ⁻¹' goodᶜ) ∂mu = 0 := by
      rw [D.predictableEnergyMeasure_apply hGoodMeas.compl] at hBadZero
      simpa only [D.stieltjesKernel_apply] using hBadZero
    have hBadProd : MeasurableSet goodᶜ :=
      PredictableKernelMeasure.predictable_le_prod F goodᶜ hGoodMeas.compl
    exact (lintegral_eq_zero_iff
      (Kernel.measurable_kernel_prodMk_right hBadProd)).mp hIntegral
  have hAtom := D.stieltjesKernel_singleton_eq_jump_sq hMLeft
  filter_upwards [hUniform, hBadFiber, hAtom]
      with omega hUniformOmega hBadOmega hAtomOmega
  intro t
  let X := deterministicallyStoppedProcess M T
  let I := finiteHorizonMartingaleIntegralCadlagProcess
    hUsual D hM hMRight hMLeft hMT f hfMeas hf
  have hUniformSub : TendstoUniformly
      (fun n s => processApproximation D f hfMeas hf
        (cutoff (subseq n)) s omega)
      (fun s => I s omega) atTop :=
    fun u hu => hSubseq.tendsto_atTop.eventually (hUniformOmega u hu)
  have hApproxLeft : ∀ n s, Tendsto
      (fun u => processApproximation D f hfMeas hf
        (cutoff (subseq n)) u omega) (𝓝[<] s)
      (nhds (Function.leftLim (fun u =>
        processApproximation D f hfMeas hf
          (cutoff (subseq n)) u omega) s)) := by
    intro n s
    exact processApproximation_hasLeftLimits
      D hMLeft f hfMeas hf (cutoff (subseq n)) omega s
  have hLeft := tendsto_leftLim_of_tendstoUniformly
    (fun n s => processApproximation D f hfMeas hf
      (cutoff (subseq n)) s omega)
    (fun s => I s omega) hUniformSub hApproxLeft t
  have hJump : Tendsto (fun n => processLeftJump
      (processApproximation D f hfMeas hf (cutoff (subseq n))) t omega)
      atTop (nhds (processLeftJump I t omega)) := by
    simpa only [processLeftJump] using
      (hUniformSub.tendsto_at t).sub hLeft
  let sourceJump := processLeftJump X t omega
  have hProduct : Tendsto
      (fun n => g (cutoff (subseq n)) (t, omega) * sourceJump)
      atTop (nhds (f (t, omega) * sourceJump)) := by
    by_cases hSourceJump : sourceJump = 0
    · simp only [hSourceJump, mul_zero]
      exact tendsto_const_nhds
    · have hAtomPos : 0 < D.stieltjesKernel omega {t} := by
        rw [hAtomOmega t]
        exact ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hSourceJump)
      have htGood : (t, omega) ∈ good := by
        by_contra htBad
        have hSubset : ({t} : Set NNReal) ⊆
            (fun s => (s, omega)) ⁻¹' goodᶜ := by
          intro s hs
          rw [mem_singleton_iff.mp hs]
          exact htBad
        have hLe : D.stieltjesKernel omega {t} ≤
            D.stieltjesKernel omega
              ((fun s => (s, omega)) ⁻¹' goodᶜ) :=
          measure_mono hSubset
        rw [hBadOmega] at hLe
        exact (not_le_of_gt hAtomPos) hLe
      exact htGood.mul_const sourceJump
  have hApproxJump : Tendsto (fun n => processLeftJump
      (processApproximation D f hfMeas hf (cutoff (subseq n))) t omega)
      atTop (nhds (f (t, omega) * sourceJump)) := by
    apply hProduct.congr'
    exact Filter.Eventually.of_forall fun n =>
      (processLeftJump_processApproximation D hMLeft f hfMeas hf
        (cutoff (subseq n)) t omega).symm
  have hEq := tendsto_nhds_unique hJump hApproxJump
  simpa only [I, X, sourceJump] using hEq

end BoundedMartingaleQuadraticEnergy.Data

end FTAPTheorem42
