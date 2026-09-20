import FTAPTheorem42.Stochastic.Topology.Emery.ProcessLocalization
import FTAPTheorem42.Stochastic.Topology.Emery.Semimartingale

/-! # Approximation by bounded predictable elementary coefficients

The error threshold is uniform over all unit tests. Localization errors
and intermediate process limits preserve this approximation property.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every finite horizon admits an elementary approximant, with a finite
deterministic coefficient-sum bound and a uniform error over unit tests.
Initial values are not detected and must be supplied separately. -/
def ElementaryEmeryApproximable (S X : Process Ω) : Prop :=
  ∀ T : NNReal, ∀ ε > (0 : Real),
    ∃ (J : PredictableElementaryStrategy F) (C : NNReal),
      (∀ ω, J.coefficientAbsSum ω ≤ C) ∧
      ∀ L : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        ∫ ω, elementaryEmeryTestError (ElementaryStrategy.gain S J.toElementary) X L T ω ∂μ ≤ ε

/-- A stopped test loses at most the probability of stopping before the
horizon. This error bound is independent of the test and its length. -/
theorem integral_elementaryEmeryTestError_le_stopped
    {X Y : Process Ω} (hX : IsStronglyProgressive F X) (hY : IsStronglyProgressive F Y)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) (T : NNReal) :
    (∫ ω, elementaryEmeryTestError X Y J T ω ∂μ) ≤
      (∫ ω, elementaryEmeryTestError (stoppedProcess X τ) (stoppedProcess Y τ) J T ω ∂μ) +
        μ.real {ω | τ ω ≤ T} := by
  let B := {ω | τ ω ≤ T}
  have hB : MeasurableSet B := F.le T _ (hτ T)
  have hbInt : Integrable (B.indicator (fun _ => (1 : Real))) μ :=
    (integrable_const _).indicator hB
  have hStopped := elementaryEmeryTestError_integrable (μ := μ)
    (hX.stoppedProcess hτ) (hY.stoppedProcess hτ) J T
  have hBound ω : elementaryEmeryTestError X Y J T ω ≤
      elementaryEmeryTestError (stoppedProcess X τ) (stoppedProcess Y τ) J T ω +
        B.indicator (fun _ => (1 : Real)) ω := by
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      exact (elementaryEmeryTestError_bounds _ _ _ _ _).2.trans
        (le_add_of_nonneg_left (elementaryEmeryTestError_bounds _ _ _ _ _).1)
    · rw [Set.indicator_of_notMem hω, add_zero, elementaryEmeryTestError_stopped_eq_of_le]
      exact (lt_of_not_ge hω).le
  have hi := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) hX hY J T)
    (hStopped.add hbInt) (Eventually.of_forall hBound)
  simpa only [Pi.add_apply, integral_add hStopped hbInt, integral_indicator hB,
    setIntegral_const, smul_eq_mul, mul_one] using hi

/-- Completed coordinate approximations become original, unstopped
approximations after their localization error is made small. -/
theorem elementaryEmeryApproximable_of_stopped
    {S X : Process Ω} (hS : IsStronglyProgressive F S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (hX : IsStronglyProgressive F X)
    {τ : Nat → Ω → WithTop NNReal} (hτ : IsPreLocalizingSequence F τ μ)
    (hLocal : ∀ k, ∃ (J : Nat → PredictableElementaryStrategy F) (C : Nat → NNReal),
      (∀ n ω, (J n).coefficientAbsSum ω ≤ C n) ∧
      ElementaryEmeryConverges μ F
        (fun n => stoppedProcess (ElementaryStrategy.gain S (J n).toElementary) (τ k))
        (stoppedProcess X (τ k))) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S X := by
  intro T ε hε
  have hBad : Tendsto (fun k => μ.real {ω | τ k ω ≤ T}) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (0 : ENNReal) ≠ ∞)).comp
        (FTAPTheorem42.IsPreLocalizingSequence.tendsto_measure_le hτ T)
  obtain ⟨k, hk⟩ := (hBad.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨J, C, hC, hConv⟩ := hLocal k
  obtain ⟨n, hn⟩ := (hConv T (ε / 2) (half_pos hε)).exists
  refine ⟨J n, C n, hC n, ?_⟩
  intro L
  have hJ := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    ((J n).stronglyAdapted_gain S hS) ((J n).rightContinuous_gain S hSRight)
  exact (integral_elementaryEmeryTestError_le_stopped hJ hX (τ k)
    (hτ.isStoppingTime k) L T).trans
    ((add_le_add (hn L) hk.le).trans_eq (add_halves ε))

/-- Uniform limits of elementary-approximable processes are again
approximable; the intermediate row is chosen before the test. -/
theorem ElementaryEmeryApproximable.of_converges
    {S Y : Process Ω} {X : Nat → Process Ω}
    (hS : IsStronglyProgressive F S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (hX : ∀ n, IsStronglyProgressive F (X n)) (hY : IsStronglyProgressive F Y)
    (hApprox : ∀ n, ElementaryEmeryApproximable (F := F) (μ := μ) S (X n))
    (hConv : ElementaryEmeryConverges μ F X Y) :
    ElementaryEmeryApproximable (F := F) (μ := μ) S Y := by
  intro T ε hε
  obtain ⟨n, hn⟩ := (hConv T (ε / 2) (half_pos hε)).exists
  obtain ⟨J, C, hC, hJ⟩ := hApprox n T (ε / 2) (half_pos hε)
  refine ⟨J, C, hC, ?_⟩
  intro L
  have hG := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (J.stronglyAdapted_gain S hS) (J.rightContinuous_gain S hSRight)
  have hBound ω : elementaryEmeryTestError (ElementaryStrategy.gain S J.toElementary) Y L T ω ≤
      elementaryEmeryTestError (X n) (ElementaryStrategy.gain S J.toElementary) L T ω +
        elementaryEmeryTestError (X n) Y L T ω :=
    FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope_sub_le_add
      (ElementaryStrategy.gain (ElementaryStrategy.gain S J.toElementary) L.strategy.toElementary)
      (ElementaryStrategy.gain Y L.strategy.toElementary)
      (ElementaryStrategy.gain (X n) L.strategy.toElementary) T ω
  have hi := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) hG hY L T)
    ((elementaryEmeryTestError_integrable (hX n) hG L T).add
      (elementaryEmeryTestError_integrable (hX n) hY L T)) (Eventually.of_forall hBound)
  simp only [Pi.add_apply] at hi
  rw [integral_add (elementaryEmeryTestError_integrable (hX n) hG L T)
    (elementaryEmeryTestError_integrable (hX n) hY L T),
    elementaryEmeryTestError_comm (X n)] at hi
  exact hi.trans ((add_le_add (hJ L) (hn L)).trans_eq (add_halves ε))

end FTAPTheorem42
