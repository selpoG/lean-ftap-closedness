import FTAPTheorem42.Stochastic.DS.Lemma49.StoppedTailMartingale
import FTAPTheorem42.Stochastic.DS.Lemma48.TailHorizon
import FTAPTheorem42.Stochastic.Topology.Emery.MartingaleTestEstimate
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessApproximation

/-! # Elementary-test estimates for the convex martingale tails

Stopped terminal energy controls every represented unit-bounded elementary
test. The passage probability controls the removal of the stop, independently
of the test's presentation or number of intervals.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators

namespace FTAPTheorem42

open SIntegrableProcessStoppingCalculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  [F.IsRightContinuous] {D : SpecialSemimartingaleDecomposition P F μ}

/-- A passage cutoff and its jump envelope give a test-independent maximal
expectation bound. The jump at the cutoff is included in the terminal energy. -/
theorem integral_lemma49_tail_test_le
    (H : Nat → SIntegrableStrategy D) (weight : Nat → Real) (n : Nat)
    (c a : Real) (ha : 0 ≤ a) (T : NNReal)
    (hML : ∀ i, ProcessHasLeftLimits (H i).martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 μ) (hξNonneg : ∀ᵐ ω ∂μ, 0 ≤ ξ ω)
    (hJump : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump (lemma48TailConvexStrategy (SIntegrableStrategy.processStoppingCalculus D)
        H weight n c).martingalePart t ω| ≤ ξ ω)
    (η : Real) (hη : 0 ≤ η) (hNorm : eLpNorm ξ 2 μ ≤ ENNReal.ofReal η)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
    let C := SIntegrableStrategy.processStoppingCalculus D
    (∫ ω, elementaryEmeryTestError (C.lemma48TailConvexStrategy H weight n c).martingalePart
      0 J T ω ∂μ) ≤ 2 * (a + η) +
        μ.real (C.lemma48TailMartingalePassageFiniteEvent H weight n c a) := by
  let C := SIntegrableStrategy.processStoppingCalculus D
  let L := C.lemma48TailConvexStrategy H weight n c
  let R := C.lemma49StoppedTailConvexStrategy H weight n c a T
  let τ := C.lemma48TailMartingalePassage H weight n c a
  have hτ : IsStoppingTime F τ := C.lemma48TailMartingalePassage_isStoppingTime H weight n c a
  have hR := C.lemma49StoppedTailConvexStrategy_martingale_l2
    H weight n c a ha T hML ξ hξ hξNonneg hJump
  have hRNorm : eLpNorm (R.martingalePart T) 2 μ ≤ ENNReal.ofReal (a + η) := by
    apply hR.2.2.trans
    rw [ENNReal.ofReal_add ha hη]
    exact add_le_add le_rfl hNorm
  have hRZero : R.martingalePart 0 =ᵐ[μ] 0 := by
    filter_upwards [C.lemma48TailConvexStrategy_martingalePart_zero H weight n c] with ω hω
    change stoppedProcess L.martingalePart
      (C.lemma49TailMartingalePassageUpTo H weight n c a T) 0 ω = 0
    rw [stoppedProcess_eq_of_le bot_le]
    exact hω
  have hEnergy := martingale_test_integral_le hR.1 R.martingalePart_isRightContinuous
    hRZero T hR.2.1 J
  have hNumeric : 2 * eLpNorm (R.martingalePart T) 2 μ ≤
      ENNReal.ofReal (2 * (a + η)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2), ENNReal.ofReal_ofNat]
    exact mul_le_mul le_rfl hRNorm bot_le bot_le
  have hZeroGain : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  have hRInt : (∫ ω, elementaryEmeryTestError R.martingalePart 0 J T ω ∂μ) ≤
      2 * (a + η) := by
    have hReal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hEnergy.trans hNumeric)
    simpa only [elementaryEmeryTestError, hZeroGain, Pi.zero_apply, sub_zero] using hReal
  have hRStop : R.martingalePart =
      stoppedProcess (stoppedProcess L.martingalePart τ) (fun _ => (T : WithTop NNReal)) := by
    rw [stoppedProcess_stoppedProcess']
    change stoppedProcess L.martingalePart (fun ω => min (τ ω) (T : WithTop NNReal)) = _
    congr 1
    funext ω
    exact min_comm _ _
  have hTestCap : elementaryEmeryTestError (stoppedProcess L.martingalePart τ) 0 J T =
      elementaryEmeryTestError R.martingalePart 0 J T := by
    funext ω
    have h := elementaryEmeryTestError_stopped_eq_of_le
      (stoppedProcess L.martingalePart τ) 0 (fun _ => (T : WithTop NNReal)) J T ω le_rfl
    change elementaryEmeryTestError
      (stoppedProcess (stoppedProcess L.martingalePart τ) (fun _ => (T : WithTop NNReal)))
      0 J T ω = _ at h
    rw [← hRStop] at h
    exact h.symm
  have hComparison := integral_elementaryEmeryTestError_le_stopped (μ := μ)
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      L.martingalePart_isStronglyAdapted L.martingalePart_isRightContinuous)
    (show IsStronglyProgressive F (0 : Process Ω) from fun _ => stronglyMeasurable_zero)
    τ hτ J T
  change (∫ ω, elementaryEmeryTestError L.martingalePart 0 J T ω ∂μ) ≤
    (∫ ω, elementaryEmeryTestError (stoppedProcess L.martingalePart τ) 0 J T ω ∂μ) +
      μ.real {ω | τ ω ≤ T} at hComparison
  rw [hTestCap] at hComparison
  apply hComparison.trans
  apply add_le_add hRInt
  apply measureReal_mono
  · intro ω hω
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hω
  · finiteness

end FTAPTheorem42
