import FTAPTheorem42.Stochastic.Topology.Emery.ProcessApproximation
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessFastSubsequence

/-! # Realizing a regular process in the elementary completion

Finite-horizon uniform approximations choose one elementary sequence.
The process Cauchy condition and its zero-initial ucp limit supply the
existing realized-strategy carrier.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

open PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The horizon-by-horizon approximation property chooses a single
sequence with a uniform tail for every finite horizon. -/
theorem ElementaryEmeryApproximable.exists_convergent_sequence
    {S X : Process Ω} (hS : IsStronglyProgressive F S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (hX : IsStronglyProgressive F X)
    (hXRight : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (h : ElementaryEmeryApproximable (F := F) (μ := μ) S X) :
    ∃ (J : Nat → PredictableElementaryStrategy F) (C : Nat → NNReal),
      (∀ n ω, (J n).coefficientAbsSum ω ≤ C n) ∧
      ElementaryEmeryConverges μ F (fun n => elementaryGain S (J n)) X := by
  have hRows n := h ((n + 1 : Nat) : NNReal) (1 / ((n : Real) + 1)) (by positivity)
  choose J C hC hErr using hRows
  refine ⟨J, C, hC, ?_⟩
  intro T ε hε
  have hTend : Tendsto (fun n : Nat => ((n + 1 : Nat) : NNReal)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hSmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).eventually (gt_mem_nhds hε)
  filter_upwards [hTend.eventually (eventually_ge_atTop T), hSmall] with n hn hεn
  intro L
  have hJ := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    ((J n).stronglyAdapted_gain S hS) ((J n).rightContinuous_gain S hSRight)
  have hi := integral_mono_ae (elementaryEmeryTestError_integrable (μ := μ) hJ hX L T)
    (elementaryEmeryTestError_integrable hJ hX L ((n + 1 : Nat) : NNReal))
    (Eventually.of_forall fun ω => cappedFiniteHorizonAbsoluteEnvelope_mono_of_rightContinuous
      (fun t ω => ElementaryStrategy.gain (elementaryGain S (J n)) L.strategy.toElementary t ω -
        ElementaryStrategy.gain X L.strategy.toElementary t ω)
      (fun ω t => (L.strategy.rightContinuous_gain _
        ((J n).rightContinuous_gain S hSRight) ω t).sub
        (L.strategy.rightContinuous_gain X hXRight ω t)) hn ω)
  exact hi.trans ((hErr n L).trans hεn.le)

/-- Uniform Cauchy tests of the original elementary gains are the Cauchy
condition used by the original completion's supremum gauge. -/
theorem ElementaryEmeryCauchy.elementary_isCauchy
    {S : Process Ω} (hS : IsStronglyProgressive F S)
    (J : Nat → PredictableElementaryStrategy F)
    (h : ElementaryEmeryCauchy μ F (fun n => elementaryGain S (J n))) :
    PredictableElementaryEmery.IsCauchy μ S J := by
  intro T
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun p => ha.trans_le (gauge_nonnegative S hS (J p.1) (J p.2) T)
  · intro b hb
    obtain ⟨N, hN⟩ := h T (b / 2) (half_pos hb)
    filter_upwards [eventually_ge_atTop (N, N)] with p hp
    apply lt_of_le_of_lt _ (half_lt_self hb)
    apply csSup_le (Set.insert_nonempty 0 _)
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | ⟨L, rfl⟩
    · exact (half_pos hb).le
    · change testValue μ S L (J p.1) (J p.2) T ≤ b / 2
      rw [testValue_eq_integral]
      have hMul (K : PredictableElementaryStrategy F) : testedGain S L K =
          elementaryGain (elementaryGain S K) L.strategy :=
        (elementaryGain_source_mul S L.strategy K).symm
      have hEq : testedDifference S L (J p.1) (J p.2) =
          (fun t ω =>
            ElementaryStrategy.gain (elementaryGain S (J p.1)) L.strategy.toElementary t ω -
            ElementaryStrategy.gain (elementaryGain S (J p.2)) L.strategy.toElementary t ω) := by
        unfold testedDifference
        rw [hMul, hMul]
        rfl
      rw [hEq]
      exact hN p.1 hp.1 p.2 hp.2 L

/-- A regular zero-initial process with uniform elementary approximations
is an actual element of the existing realized completion, with exactly the
supplied gain and the chosen deterministic coefficient bounds. -/
theorem ElementaryEmeryApproximable.exists_realizedStrategy
    {S X : Process Ω} (hS : IsStronglyProgressive F S)
    (hSRight : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (hXA : StronglyAdapted F X)
    (hXR : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hX0 : X 0 =ᵐ[μ] 0)
    (h : ElementaryEmeryApproximable (F := F) (μ := μ) S X) :
    ∃ R : RealizedStrategy (ℱ := F) μ S, R.gain = X := by
  have hX := StronglyAdapted.isStronglyProgressive_of_rightContinuous hXA hXR
  obtain ⟨J, C, hC, hConv⟩ := h.exists_convergent_sequence hS hSRight hX hXR
  have hJ n := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    ((J n).stronglyAdapted_gain S hS) ((J n).rightContinuous_gain S hSRight)
  refine ⟨{
    representative := J
    representativeBound := C
    representative_coefficientAbsSum_le := hC
    gain := X
    gain_stronglyAdapted := hXA
    gain_rightContinuous := hXR
    gain_hasLeftLimits := hXL
    gain_convergence := ?_
    isCauchy := (hConv.cauchy hJ hX).elementary_isCauchy hS J }, rfl⟩
  intro r
  apply hConv.ucp hJ hX _ ((r + 1 : Nat) : NNReal)
  intro n
  filter_upwards [hX0] with ω hω
  rw [hω]
  change ElementaryStrategy.gain S (J n).toElementary 0 ω = 0
  simp [ElementaryStrategy.gain, ElementaryInterval.gain]

end FTAPTheorem42
