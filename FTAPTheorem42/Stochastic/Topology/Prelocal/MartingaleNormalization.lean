/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.BoundaryConsumer
import FTAPTheorem42.Stochastic.Market.Source.CenteredMarketUnitLocallySIntegrableStrategy
import FTAPTheorem42.Stochastic.Martingale.Basic.DominatedLocalMartingale

/-!
# Zero-initial normalization of the prelocal `H¹` martingale coordinate

The flattened prelocal carrier does not require its local-martingale coordinate
to start at zero.  This module moves the time-zero value from that coordinate
to the finite-variation coordinate.  The two coordinates still have the same
sum, and the finite-horizon envelope changes by at most a factor two.  The
normalized stopped local martingale is then upgraded to a true martingale by
the existing integrable-envelope theorem.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

/-! ## Pathwise identities for a time-constant shift -/

omit [MeasurableSpace Ω] in
private theorem strictPrefixProcess_add_timeConstant
    (A : Process Ω) (rho : Ω → NNReal) (c : Ω → Real)
    (hA : ProcessHasLeftLimits A) :
    strictPrefixProcess (fun t omega => A t omega + c omega) rho =
      (fun t omega => strictPrefixProcess A rho t omega + c omega) := by
  funext t omega
  have hLeft : ∀ s, Function.leftLim (fun u => A u omega + c omega) s =
      Function.leftLim (fun u => A u omega) s + c omega := by
    intro s
    rcases eq_or_neBot (𝓝[<] s) with hbot | hne
    · rw [leftLim_eq_of_eq_bot _ hbot, leftLim_eq_of_eq_bot _ hbot]
    · have hsum := (hA omega s).add
        (tendsto_const_nhds :
          Tendsto (fun _ : NNReal => c omega) (𝓝[<] s) (𝓝 (c omega)))
      rw [leftLim_eq_of_tendsto hsum]
  unfold strictPrefixProcess
  change
    (MeasureTheory.stoppedProcess (fun s omega => A s omega + c omega)
        (fun omega => (rho omega : WithTop NNReal)) t omega -
      postStopSampled (fun s omega => A s omega + c omega) rho t omega +
      postStopSampled
        (fun s omega => Function.leftLim (fun u => A u omega + c omega) s)
        rho t omega) =
      (MeasureTheory.stoppedProcess A
          (fun omega => (rho omega : WithTop NNReal)) t omega -
        postStopSampled A rho t omega +
        postStopSampled
          (fun s omega => Function.leftLim (A · omega) s) rho t omega) +
        c omega
  simp only [MeasureTheory.stoppedProcess, postStopSampled, hLeft]
  by_cases h : rho omega ≤ t
  · simp only [ite_eq_left h]
    ring
  · simp [h]

private theorem zeroInitial_strictPrefixVariation_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω}
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    prelocalH1SupFiniteVariationExpectedVariation
        (mu := mu)
        (fun t omega => w.A t omega + w.N 0 omega) tau T =
      prelocalH1SupFiniteVariationExpectedVariation
        (mu := mu) w.A tau T := by
  unfold prelocalH1SupFiniteVariationExpectedVariation
  rw [strictPrefixProcess_add_timeConstant w.A tau (fun omega => w.N 0 omega)
    w.finiteVariation_hasLeftLimits]
  apply lintegral_congr
  intro omega
  exact pathVariation_add_const (w.N 0 omega) _

/-! ## The normalized witness -/

/-- Move the martingale's time-zero value to the finite-variation coordinate.
The resulting witness has the same target and strict-prefix agreement, while
its martingale coordinate starts at zero pointwise. -/
noncomputable def EmeryPrelocalH1SupWitness.zeroInitial
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T := by
  let c : Ω → Real := fun omega => w.N 0 omega
  let N0 : Process Ω := fun t omega => w.N t omega - c omega
  let A0 : Process Ω := fun t omega => w.A t omega + c omega
  have hC : StronglyAdapted F (fun _t omega => c omega) := by
    intro t
    exact (w.martingale_isStronglyAdapted 0).mono (F.mono bot_le)
  have hN0Local : LocalMartingale N0 F mu := by
    simpa only [N0, c] using w.martingale_isLocalMartingale.centered
  have hN0Adapted : StronglyAdapted F N0 := by
    change StronglyAdapted F (w.N - fun _t omega => c omega)
    exact w.martingale_isStronglyAdapted.sub hC
  have hN0Right : ∀ omega t,
      ContinuousWithinAt (N0 · omega) (Set.Ici t) t := by
    intro omega t
    exact (w.martingale_isRightContinuous omega t).sub
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => c omega) (Set.Ici t) t)
  have hN0Left : ProcessHasLeftLimits N0 := by
    simpa only [N0] using
      w.martingale_hasLeftLimits.sub (ProcessHasLeftLimits.timeConstant c)
  have hA0Adapted : StronglyAdapted F A0 := by
    change StronglyAdapted F (w.A + fun _t omega => c omega)
    exact w.finiteVariation_isStronglyAdapted.add hC
  have hA0Right : ∀ omega t,
      ContinuousWithinAt (A0 · omega) (Set.Ici t) t := by
    intro omega t
    exact (w.finiteVariation_isRightContinuous omega t).add
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => c omega) (Set.Ici t) t)
  have hA0Left : ProcessHasLeftLimits A0 := by
    simpa only [A0] using
      w.finiteVariation_hasLeftLimits.add (ProcessHasLeftLimits.timeConstant c)
  have hStoppedAdapted : StronglyAdapted F
      (MeasureTheory.stoppedProcess N0
        (fun omega => (tau omega : WithTop NNReal))) :=
    RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
      hN0Adapted w.stoppingTime hN0Right
  have hEnvelopeStrong : StronglyMeasurable
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess N0
          (fun omega => (tau omega : WithTop NNReal))) T) :=
    (FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      hStoppedAdapted T).mono (F.le T)
  have hStoppedRight : ∀ omega t,
      ContinuousWithinAt
        (MeasureTheory.stoppedProcess N0
          (fun omega => (tau omega : WithTop NNReal)) · omega)
        (Set.Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous N0 hN0Right
  have hStoppedLeft : ProcessHasLeftLimits
      (MeasureTheory.stoppedProcess N0
        (fun omega => (tau omega : WithTop NNReal))) :=
    hN0Left.stoppedProcess (fun omega => (tau omega : WithTop NNReal))
  have hEnvelopeLe : ∀ omega,
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess N0
            (fun omega => (tau omega : WithTop NNReal))) T omega ≤
        2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
    intro omega
    apply FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_le_of_bound
      (MeasureTheory.stoppedProcess N0
        (fun omega => (tau omega : WithTop NNReal))) T
    intro t ht
    have hNBound :=
      FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
          w.N w.martingale_isRightContinuous)
        (w.martingale_hasLeftLimits.stoppedProcess
          (fun omega => (tau omega : WithTop NNReal))) (ω := omega) T t ht
    have hAtZero :=
      FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
          w.N w.martingale_isRightContinuous)
        (w.martingale_hasLeftLimits.stoppedProcess
          (fun omega => (tau omega : WithTop NNReal))) (ω := omega) T 0 bot_le
    have hStoppedAtZero :
        MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal)) 0 omega =
          w.N 0 omega := by
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      exact bot_le
    have hN0AtZero : |c omega| ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
      change |w.N 0 omega| ≤ _
      rw [← hStoppedAtZero]
      exact hAtZero
    have hN0Pointwise :
        |MeasureTheory.stoppedProcess N0
            (fun omega => (tau omega : WithTop NNReal)) t omega| ≤
          |MeasureTheory.stoppedProcess w.N
              (fun omega => (tau omega : WithTop NNReal)) t omega| + |c omega| := by
      change |w.N (min t (tau omega)) omega - c omega| ≤ _
      exact abs_sub _ _
    calc
      |MeasureTheory.stoppedProcess N0
          (fun omega => (tau omega : WithTop NNReal)) t omega| ≤
      |MeasureTheory.stoppedProcess w.N
              (fun omega => (tau omega : WithTop NNReal)) t omega| + |c omega| :=
        hN0Pointwise
      _ ≤ 2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
        have hadd :
            |MeasureTheory.stoppedProcess w.N
                (fun omega => (tau omega : WithTop NNReal)) t omega| + |c omega| ≤
              FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                (MeasureTheory.stoppedProcess w.N
                  (fun omega => (tau omega : WithTop NNReal))) T omega +
                FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                  (MeasureTheory.stoppedProcess w.N
                    (fun omega => (tau omega : WithTop NNReal))) T omega :=
          add_le_add hNBound hN0AtZero
        calc
          |MeasureTheory.stoppedProcess w.N
                (fun omega => (tau omega : WithTop NNReal)) t omega| + |c omega| ≤
              FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                (MeasureTheory.stoppedProcess w.N
                  (fun omega => (tau omega : WithTop NNReal))) T omega +
                FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                  (MeasureTheory.stoppedProcess w.N
                    (fun omega => (tau omega : WithTop NNReal))) T omega := hadd
          _ = 2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
              (MeasureTheory.stoppedProcess w.N
                (fun omega => (tau omega : WithTop NNReal))) T omega := by ring
  have hEnvelopeMem : MemLp
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess N0
          (fun omega => (tau omega : WithTop NNReal))) T)
      (1 : ENNReal) mu := by
    have hTwo : MemLp (fun omega =>
        (2 : Real) * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega)
        (1 : ENNReal) mu :=
      w.martingale_envelope_memLp_one.const_mul 2
    apply MemLp.of_le hTwo hEnvelopeStrong.aestronglyMeasurable
    filter_upwards [] with omega
    have hE0Nonneg : 0 ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess N0
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
      unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      exact Real.sqrt_nonneg _
    have hTwoENonneg : 0 ≤
        (2 : Real) * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N
            (fun omega => (tau omega : WithTop NNReal))) T omega := by
      apply mul_nonneg (by norm_num)
      unfold FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      exact Real.sqrt_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hE0Nonneg,
      abs_of_nonneg hTwoENonneg] using hEnvelopeLe omega
  have hEnvelopePath : ∀ omega,
      ENNReal.ofReal
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (MeasureTheory.stoppedProcess N0
              (fun omega => (tau omega : WithTop NNReal))) T omega) =
        ⨆ t : Set.Iic T, ENNReal.ofReal
          |MeasureTheory.stoppedProcess N0
            (fun omega => (tau omega : WithTop NNReal)) t.1 omega| := by
    intro omega
    exact FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
      hStoppedRight hStoppedLeft T
  have hCVar : ∀ omega, BoundedVariationOn
      (fun _ : NNReal => c omega) Set.univ := by
    intro omega
    change eVariationOn (fun _ : NNReal => c omega) Set.univ ≠ ∞
    rw [eVariationOn.constant_on (by simp)]
    simp
  exact {
    N := N0
    A := A0
    agrees_on_strict_prefix := by
      intro t omega ht
      have h := w.agrees_on_strict_prefix t omega ht
      dsimp [N0, A0, c]
      linarith
    martingale_isLocalMartingale := hN0Local
    martingale_isStronglyAdapted := hN0Adapted
    martingale_isRightContinuous := hN0Right
    martingale_hasLeftLimits := hN0Left
    stoppingTime := w.stoppingTime
    stoppingTime_le_horizon := w.stoppingTime_le_horizon
    finiteVariation_isStronglyAdapted := hA0Adapted
    finiteVariation_isRightContinuous := hA0Right
    finiteVariation_hasLeftLimits := hA0Left
    finiteVariation_isBoundedVariation := by
      intro omega
      exact boundedVariationOn_add
        (w.finiteVariation_isBoundedVariation omega) (hCVar omega)
    martingale_envelope_stronglyMeasurable := hEnvelopeStrong
    martingale_envelope_memLp_one := hEnvelopeMem
    martingale_envelope_eq_iSup := hEnvelopePath
    finiteVariation_measurable := by
      exact measurable_strictPrefixVariation_of_regularProcess A0 tau T
        hA0Adapted hA0Right hA0Left w.stoppingTime
    finiteVariation_integral_ne_top := by
      rw [zeroInitial_strictPrefixVariation_eq w]
      exact w.finiteVariation_integral_ne_top }

@[simp]
theorem EmeryPrelocalH1SupWitness.zeroInitial_martingalePart_zero
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
  (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (w.zeroInitial).N 0 = 0 := by
  funext omega
  rw [show (w.zeroInitial).N =
      (fun t omega => w.N t omega - w.N 0 omega) by
        simp [EmeryPrelocalH1SupWitness.zeroInitial]]
  simpa only [Pi.zero_apply] using sub_self (w.N 0 omega)

@[simp]
theorem EmeryPrelocalH1SupWitness.zeroInitial_N
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (w.zeroInitial).N = (fun t omega => w.N t omega - w.N 0 omega) := by
  simp [EmeryPrelocalH1SupWitness.zeroInitial]

@[simp]
theorem EmeryPrelocalH1SupWitness.zeroInitial_A
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    (w.zeroInitial).A = (fun t omega => w.A t omega + w.N 0 omega) := by
  simp [EmeryPrelocalH1SupWitness.zeroInitial]

/-! ## Cost and stopped-martingale consumers -/

theorem prelocalH1SupWitnessVariationCost_zeroInitial_eq
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    prelocalH1SupWitnessVariationCost (mu := mu) w.zeroInitial =
      prelocalH1SupWitnessVariationCost (mu := mu) w := by
  unfold prelocalH1SupWitnessVariationCost
  rw [w.zeroInitial_A]
  exact zeroInitial_strictPrefixVariation_eq w

theorem prelocalH1SupWitnessMartingaleCost_zeroInitial_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {X : Process Ω} {tau : Ω → NNReal}
    {T : NNReal} [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    prelocalH1SupWitnessMartingaleCost (mu := mu) w.zeroInitial ≤
      2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w := by
  let τ : Ω → WithTop NNReal := fun omega => (tau omega : WithTop NNReal)
  let E0 : Ω → Real :=
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (MeasureTheory.stoppedProcess w.zeroInitial.N τ) T
  let E : Ω → Real :=
    FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
      (MeasureTheory.stoppedProcess w.N τ) T
  have hBound : ∀ omega, E0 omega ≤ 2 * E omega := by
    intro omega
    change FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess w.zeroInitial.N τ) T omega ≤
      2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess w.N τ) T omega
    apply FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_le_of_bound
      (MeasureTheory.stoppedProcess w.zeroInitial.N τ) T
    intro t ht
    have hNBound :=
      FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
          w.N w.martingale_isRightContinuous)
        (w.martingale_hasLeftLimits.stoppedProcess τ) (ω := omega) T t ht
    have hAtZero :=
      FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
          w.N w.martingale_isRightContinuous)
        (w.martingale_hasLeftLimits.stoppedProcess τ) (ω := omega) T 0 bot_le
    have hStoppedAtZero :
        MeasureTheory.stoppedProcess w.N τ 0 omega = w.N 0 omega := by
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      exact bot_le
    have hCAbs : |w.N 0 omega| ≤
        FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N τ) T omega := by
      rw [← hStoppedAtZero]
      exact hAtZero
    have hSub :
        |MeasureTheory.stoppedProcess w.zeroInitial.N τ t omega| ≤
        |MeasureTheory.stoppedProcess w.N τ t omega| + |w.N 0 omega| := by
      rw [w.zeroInitial_N]
      change |w.N (min t (tau omega)) omega - w.N 0 omega| ≤ _
      exact abs_sub _ _
    calc
      |MeasureTheory.stoppedProcess w.zeroInitial.N τ t omega| ≤
          |MeasureTheory.stoppedProcess w.N τ t omega| + |w.N 0 omega| := hSub
      _ ≤ 2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
          (MeasureTheory.stoppedProcess w.N τ) T omega := by
        have hadd :
            |MeasureTheory.stoppedProcess w.N τ t omega| + |w.N 0 omega| ≤
              FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                (MeasureTheory.stoppedProcess w.N τ) T omega +
                FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                  (MeasureTheory.stoppedProcess w.N τ) T omega :=
          add_le_add hNBound hCAbs
        calc
          |MeasureTheory.stoppedProcess w.N τ t omega| + |w.N 0 omega| ≤
              FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                (MeasureTheory.stoppedProcess w.N τ) T omega +
                FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
                  (MeasureTheory.stoppedProcess w.N τ) T omega := hadd
          _ = 2 * FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
              (MeasureTheory.stoppedProcess w.N τ) T omega := by ring
  change eLpNorm E0 (1 : ENNReal) mu ≤ 2 * eLpNorm E (1 : ENNReal) mu
  calc
    eLpNorm E0 (1 : ENNReal) mu ≤
        eLpNorm (fun omega => (2 : Real) * E omega) (1 : ENNReal) mu := by
      apply eLpNorm_mono (f := E0)
        w.zeroInitial.martingale_envelope_stronglyMeasurable.aestronglyMeasurable
      intro omega
      have hE0Nonneg : 0 ≤ E0 omega := by
        unfold E0 FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        exact Real.sqrt_nonneg _
      have hENonneg : 0 ≤ E omega := by
        unfold E FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        exact Real.sqrt_nonneg _
      have hTwoENonneg : 0 ≤ (2 : Real) * E omega :=
        mul_nonneg (by norm_num) hENonneg
      simpa only [Real.norm_eq_abs, abs_of_nonneg hE0Nonneg,
        abs_of_nonneg hTwoENonneg] using hBound omega
    _ = 2 * eLpNorm E (1 : ENNReal) mu := by
      rw [show (fun omega => (2 : Real) * E omega) = (2 : Real) • E by
        funext omega
        rfl, eLpNorm_const_smul]
      norm_num [Real.enorm_eq_ofReal]

theorem prelocalH1SupWitnessCost_zeroInitial_le_two_mul
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}
    [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) :
    prelocalH1SupWitnessCost (mu := mu) w.zeroInitial ≤
      2 * prelocalH1SupWitnessCost (mu := mu) w := by
  rw [show prelocalH1SupWitnessCost (mu := mu) w.zeroInitial =
      prelocalH1SupWitnessMartingaleCost (mu := mu) w.zeroInitial +
        prelocalH1SupWitnessVariationCost (mu := mu) w.zeroInitial by rfl,
    prelocalH1SupWitnessVariationCost_zeroInitial_eq w]
  calc
    prelocalH1SupWitnessMartingaleCost (mu := mu) w.zeroInitial +
        prelocalH1SupWitnessVariationCost (mu := mu) w ≤
      2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w +
        prelocalH1SupWitnessVariationCost (mu := mu) w :=
      add_le_add_left (prelocalH1SupWitnessMartingaleCost_zeroInitial_le w)
        (prelocalH1SupWitnessVariationCost (mu := mu) w)
    _ ≤ 2 * (prelocalH1SupWitnessMartingaleCost (mu := mu) w +
        prelocalH1SupWitnessVariationCost (mu := mu) w) := by
      calc
        2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w +
              prelocalH1SupWitnessVariationCost (mu := mu) w ≤
            2 * prelocalH1SupWitnessMartingaleCost (mu := mu) w +
              (prelocalH1SupWitnessVariationCost (mu := mu) w +
                prelocalH1SupWitnessVariationCost (mu := mu) w) :=
          (by
            have hV :
              prelocalH1SupWitnessVariationCost (mu := mu) w ≤
                prelocalH1SupWitnessVariationCost (mu := mu) w +
                  prelocalH1SupWitnessVariationCost (mu := mu) w :=
              le_add_self
            exact add_le_add_right hV _)
        _ = 2 * (prelocalH1SupWitnessMartingaleCost (mu := mu) w +
            prelocalH1SupWitnessVariationCost (mu := mu) w) := by ring
    _ = 2 * prelocalH1SupWitnessCost (mu := mu) w := by rfl

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
