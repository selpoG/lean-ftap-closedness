import FTAPTheorem42.Core.WeakStar
import FTAPTheorem42.Core.FSpace
import FTAPTheorem42.Core.L1DualRepresentation
import FTAPTheorem42.Core.WeakStarBoundedSlice
import FTAPTheorem42.Core.KreinSmulian
import FTAPTheorem42.Core.KreinSmulianC0
import FTAPTheorem42.Core.KreinSmulianC0Separation
import FTAPTheorem42.Core.C0DualCoefficients
import FTAPTheorem42.Core.KreinSmulianPredualSeparator
import FTAPTheorem42.Core.KreinSmulianCriterion
import FTAPTheorem42.Core.WeakStarFatouClosed

/-!
# Pure probability estimates for Lemma 4.7

This module isolates the parts of the Delbaen--Schachermayer Lemma 4.7
argument that do not use semimartingales.  No independence assumptions occur
in the finite aggregation estimate below.
-/

open MeasureTheory
open scoped BigOperators ENNReal MeasureTheory

namespace FTAPTheorem42

variable {Ω ι : Type*} [MeasurableSpace Ω]

/--
A reverse Markov estimate for a bounded random variable.

If `f ≤ K`, its expectation is at least `K * b`, and `K > 0`, then the event
where `f` reaches half of that average scale has probability at least `b / 2`.
No lower bound on `f` is needed.
-/
theorem probReal_ge_half_of_integral_ge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : StronglyMeasurable f) (hfi : Integrable f μ)
    {K b : ℝ} (hK : 0 < K) (hb : 0 ≤ b)
    (hf_le : ∀ ω, f ω ≤ K)
    (hmean : K * b ≤ ∫ ω, f ω ∂μ) :
    b / 2 ≤ μ.real {ω | K * b / 2 ≤ f ω} := by
  let B : Set Ω := {ω | K * b / 2 ≤ f ω}
  have hB : MeasurableSet B :=
    stronglyMeasurable_const.measurableSet_le hf
  have hBIntegral :
      (∫ ω in B, f ω ∂μ) ≤ K * μ.real B := by
    calc
      (∫ ω in B, f ω ∂μ) ≤ ∫ _ in B, K ∂μ :=
        setIntegral_mono_on hfi.integrableOn (integrableOn_const) hB
          (fun ω _ => hf_le ω)
      _ = K * μ.real B := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        ring
  have hBComplIntegral :
      (∫ ω in Bᶜ, f ω ∂μ) ≤
        (K * b / 2) * μ.real Bᶜ := by
    calc
      (∫ ω in Bᶜ, f ω ∂μ) ≤ ∫ _ in Bᶜ, K * b / 2 ∂μ :=
        setIntegral_mono_on hfi.integrableOn (integrableOn_const) hB.compl
          (fun ω hω => le_of_not_ge hω)
      _ = (K * b / 2) * μ.real Bᶜ := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        ring
  have hscale : 0 ≤ K * b / 2 := by positivity
  have hcompl :
      (K * b / 2) * μ.real Bᶜ ≤ K * b / 2 := by
    exact mul_le_of_le_one_right hscale measureReal_le_one
  have hIntegralUpper :
      (∫ ω, f ω ∂μ) ≤ K * μ.real B + K * b / 2 := by
    rw [← integral_add_compl hB hfi]
    exact add_le_add hBIntegral (hBComplIntegral.trans hcompl)
  change b / 2 ≤ μ.real B
  nlinarith

/--
Finite aggregation of events without independence.

If every event in a nonempty finite family has probability at least `b`, then
with probability at least `b / 2`, at least the real-valued count
`#s * b / 2` of those events occur.
-/
theorem probReal_eventCount_ge_half
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    {b : ℝ} (hb : 0 ≤ b)
    (hMass : ∀ i ∈ s, b ≤ μ.real (A i)) :
    b / 2 ≤ μ.real {ω |
      (s.card : ℝ) * b / 2 ≤
        ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω} := by
  classical
  let count : Ω → ℝ :=
    fun ω => ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω
  have hcount_meas : StronglyMeasurable count := by
    dsimp [count]
    exact Finset.stronglyMeasurable_fun_sum s fun i hi =>
      (stronglyMeasurable_const :
        StronglyMeasurable (fun _ : Ω => (1 : ℝ))).indicator (hA i hi)
  have hcount_int : Integrable count μ := by
    exact integrable_finsetSum s fun i hi =>
      (integrable_const (1 : ℝ)).indicator (hA i hi)
  have hcount_le : ∀ ω, count ω ≤ (s.card : ℝ) := by
    intro ω
    calc
      count ω ≤ ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hω : ω ∈ A i
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      _ = (s.card : ℝ) := by simp
  have hcount_mean :
      (s.card : ℝ) * b ≤ ∫ ω, count ω ∂μ := by
    calc
      (s.card : ℝ) * b = ∑ _i ∈ s, b := by simp
      _ ≤ ∑ i ∈ s, μ.real (A i) :=
        Finset.sum_le_sum fun i hi => hMass i hi
      _ = ∫ ω, count ω ∂μ := by
        change (∑ i ∈ s, μ.real (A i)) =
          ∫ ω, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ
        symm
        calc
          (∫ ω, ∑ i ∈ s,
              (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
              ∑ i ∈ s, ∫ ω,
                (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ :=
            integral_finsetSum s fun i hi =>
              (integrable_const (1 : ℝ)).indicator (hA i hi)
          _ = ∑ i ∈ s, μ.real (A i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact integral_indicator_one (hA i hi)
  simpa [count] using probReal_ge_half_of_integral_ge
    hcount_meas hcount_int
    (K := (s.card : ℝ)) (b := b)
    (by exact_mod_cast hs.card_pos) hb hcount_le hcount_mean

/--
Finite aggregation of nonnegative random variables without independence.

If every `g i` exceeds `a` with probability at least `b`, then their finite
sum exceeds `#s * a * b / 2` with probability at least `b / 2`.
-/
theorem probReal_sum_ge_of_each_ge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (g : ι → Ω → ℝ)
    (hg_meas : ∀ i ∈ s, StronglyMeasurable (g i))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ g i ω)
    (hMass : ∀ i ∈ s, b ≤ μ.real {ω | a ≤ g i ω}) :
    b / 2 ≤ μ.real {ω |
      (s.card : ℝ) * a * b / 2 ≤ ∑ i ∈ s, g i ω} := by
  classical
  let A : ι → Set Ω := fun i => {ω | a ≤ g i ω}
  have hA : ∀ i ∈ s, MeasurableSet (A i) := by
    intro i hi
    exact stronglyMeasurable_const.measurableSet_le (hg_meas i hi)
  have hcount := probReal_eventCount_ge_half
    (μ := μ) s hs A hA hb hMass
  refine hcount.trans (measureReal_mono ?_)
  intro ω hω
  have hterm :
      ∀ i ∈ s,
        a * (A i).indicator (fun _ => (1 : ℝ)) ω ≤ g i ω := by
    intro i hi
    by_cases hiω : ω ∈ A i
    · simpa [Set.indicator_of_mem hiω, A] using hiω
    · simpa [Set.indicator_of_notMem hiω] using hg_nonneg i hi ω
  have hsum :
      a * (∑ i ∈ s,
        (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
          ∑ i ∈ s, g i ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hscaled :
      a * ((s.card : ℝ) * b / 2) ≤
        a * (∑ i ∈ s,
          (A i).indicator (fun _ => (1 : ℝ)) ω) :=
    mul_le_mul_of_nonneg_left hω ha
  calc
    (s.card : ℝ) * a * b / 2 =
        a * ((s.card : ℝ) * b / 2) := by ring
    _ ≤ a * (∑ i ∈ s,
        (A i).indicator (fun _ => (1 : ℝ)) ω) := hscaled
    _ ≤ ∑ i ∈ s, g i ω := hsum

/--
The `L²` estimate used to control a negative excursion set.

If the second moment of `X` is at most four, then the integral of `|X|` over
any measurable event is at most twice the square root of its probability.
-/
theorem setIntegral_abs_le_two_mul_sqrt_prob
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX2 : MemLp X 2 μ)
    (hsecond : (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ 4)
    {B : Set Ω} (hB : MeasurableSet B) :
    (∫ ω in B, |X ω| ∂μ) ≤ 2 * Real.sqrt (μ.real B) := by
  let oneB : Ω → ℝ := B.indicator fun _ => 1
  have honeB2 : MemLp oneB 2 μ := by
    exact memLp_indicator_const 2 hB 1 (Or.inr (by finiteness))
  have hX2' : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hX2
  have honeB2' : MemLp oneB (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using honeB2
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := X) (g := oneB)
    Real.HolderConjugate.two_two hX2' honeB2'
  have hleft :
      (∫ ω, ‖X ω‖ * ‖oneB ω‖ ∂μ) =
        ∫ ω in B, |X ω| ∂μ := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ B
      · simp [oneB, Set.indicator_of_mem hω, Real.norm_eq_abs]
      · simp [oneB, Set.indicator_of_notMem hω]
  have honeBSecond :
      (∫ ω, ‖oneB ω‖ ^ (2 : ℝ) ∂μ) = μ.real B := by
    calc
      (∫ ω, ‖oneB ω‖ ^ (2 : ℝ) ∂μ) =
          ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          by_cases hω : ω ∈ B
          · simp [oneB, Set.indicator_of_mem hω]
          · simp [oneB, Set.indicator_of_notMem hω]
      _ = μ.real B := integral_indicator_one hB
  have hfirst :
      Real.sqrt (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ 2 := by
    calc
      Real.sqrt (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt hsecond
      _ = 2 := by norm_num
  rw [hleft, honeBSecond, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at hholder
  exact hholder.trans
    (mul_le_mul_of_nonneg_right hfirst (Real.sqrt_nonneg _))

/--
A mean-zero `L²` variable with substantial positive-part expectation must have
a negative excursion of positive mass.

This is the analytic half of the negative-excursion estimate used in Lemma
4.7.  The complementary case, where the original large absolute-value event
already has a large negative half, is purely set-theoretic.
-/
theorem probReal_negExcursion_sq_lt_of_posPart_integral
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : StronglyMeasurable X)
    (hXi : Integrable X μ) (hX2 : MemLp X 2 μ)
    (hsecond : (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ 4)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    {α : ℝ} (hα : 0 < α)
    (hpos :
      3 * α < ∫ ω, ((X ω).toNNReal : ℝ) ∂μ) :
    α ^ 2 < μ.real {ω | X ω ≤ -α} := by
  let posX : Ω → ℝ := fun ω => ((X ω).toNNReal : ℝ)
  let negX : Ω → ℝ := fun ω => ((-X ω).toNNReal : ℝ)
  let B : Set Ω := {ω | X ω ≤ -α}
  have hB : MeasurableSet B :=
    hX.measurableSet_le stronglyMeasurable_const
  have hposInt : Integrable posX μ := hXi.real_toNNReal
  have hnegInt : Integrable negX μ := hXi.neg.real_toNNReal
  have hpos_eq_neg :
      (∫ ω, posX ω ∂μ) = ∫ ω, negX ω ∂μ := by
    have hparts := integral_eq_integral_pos_part_sub_integral_neg_part hXi
    change (∫ ω, ((X ω).toNNReal : ℝ) ∂μ) =
      ∫ ω, ((-X ω).toNNReal : ℝ) ∂μ
    linarith
  have hneg_le_abs :
      (∫ ω in B, negX ω ∂μ) ≤ ∫ ω in B, |X ω| ∂μ := by
    apply setIntegral_mono_on hnegInt.integrableOn
      hXi.norm.integrableOn hB
    intro ω hω
    change max (-X ω) 0 ≤ |X ω|
    exact max_le (neg_le_abs (X ω)) (abs_nonneg (X ω))
  have hneg_compl :
      (∫ ω in Bᶜ, negX ω ∂μ) ≤ α := by
    calc
      (∫ ω in Bᶜ, negX ω ∂μ) ≤ ∫ _ in Bᶜ, α ∂μ := by
        apply setIntegral_mono_on hnegInt.integrableOn
          (integrableOn_const) hB.compl
        intro ω hω
        change max (-X ω) 0 ≤ α
        apply max_le
        · have hnot : ¬X ω ≤ -α := by simpa [B] using hω
          linarith [lt_of_not_ge hnot]
        · exact hα.le
      _ = α * μ.real Bᶜ := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ α := mul_le_of_le_one_right hα.le measureReal_le_one
  have habsB :
      (∫ ω in B, |X ω| ∂μ) ≤
        2 * Real.sqrt (μ.real B) :=
    setIntegral_abs_le_two_mul_sqrt_prob hX2 hsecond hB
  have hneg_upper :
      (∫ ω, negX ω ∂μ) ≤
        2 * Real.sqrt (μ.real B) + α := by
    rw [← integral_add_compl hB hnegInt]
    exact add_le_add (hneg_le_abs.trans habsB) hneg_compl
  have hroot : α < Real.sqrt (μ.real B) := by
    have hpos' : 3 * α < ∫ ω, posX ω ∂μ := hpos
    rw [hpos_eq_neg] at hpos'
    nlinarith
  change α ^ 2 < μ.real B
  nlinarith [Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real B),
    Real.sqrt_nonneg (μ.real B)]

/--
Mean-zero negative-excursion estimate in the form used by Lemma 4.7.

Under a second-moment bound by four, if `|X| ≥ 1` has probability greater than
`6 * α`, then `X ≤ -α` has probability greater than `α²`.
-/
theorem probReal_negExcursion_sq_lt_of_abs_ge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : StronglyMeasurable X)
    (hXi : Integrable X μ) (hX2 : MemLp X 2 μ)
    (hsecond : (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂μ) ≤ 4)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1)
    (hmass : 6 * α < μ.real {ω | 1 ≤ |X ω|}) :
    α ^ 2 < μ.real {ω | X ω ≤ -α} := by
  let P : Set Ω := {ω | 1 ≤ X ω}
  let N : Set Ω := {ω | X ω ≤ -1}
  let B : Set Ω := {ω | X ω ≤ -α}
  have hP : MeasurableSet P :=
    stronglyMeasurable_const.measurableSet_le hX
  have hN : MeasurableSet N :=
    hX.measurableSet_le stronglyMeasurable_const
  have habs_subset : {ω | 1 ≤ |X ω|} ⊆ P ∪ N := by
    intro ω hω
    by_cases hx : 0 ≤ X ω
    · left
      simpa [P, abs_of_nonneg hx] using hω
    · right
      have hxneg : X ω < 0 := lt_of_not_ge hx
      simp [N, abs_of_neg hxneg] at hω ⊢
      linarith
  have hunion :
      6 * α < μ.real (P ∪ N) :=
    hmass.trans_le (measureReal_mono habs_subset)
  have hsplit :
      3 * α < μ.real P ∨ 3 * α < μ.real N := by
    by_cases hp : 3 * α < μ.real P
    · exact Or.inl hp
    · right
      by_contra hn
      have hle := measureReal_union_le (μ := μ) P N
      have hp' := le_of_not_gt hp
      have hn' := le_of_not_gt hn
      linarith
  rcases hsplit with hpositive | hnegative
  · let posX : Ω → ℝ := fun ω => ((X ω).toNNReal : ℝ)
    have hposInt : Integrable posX μ := hXi.real_toNNReal
    have hP_lower :
        μ.real P ≤ ∫ ω in P, posX ω ∂μ := by
      change μ.real P ≤ ∫ ω in P, ((X ω).toNNReal : ℝ) ∂μ
      calc
        μ.real P = 1 * μ.real P := by ring
        _ ≤ ∫ ω in P, ((X ω).toNNReal : ℝ) ∂μ :=
          setIntegral_ge_of_const_le_real hP (by finiteness)
            (fun ω hω => by
              change 1 ≤ max (X ω) 0
              exact hω.trans (le_max_left _ _))
            hposInt.integrableOn
    have hP_whole :
        (∫ ω in P, posX ω ∂μ) ≤ ∫ ω, posX ω ∂μ :=
      setIntegral_le_integral hposInt
        (Filter.Eventually.of_forall fun ω => by positivity)
    have hpos :
        3 * α < ∫ ω, ((X ω).toNNReal : ℝ) ∂μ := by
      change 3 * α < ∫ ω, posX ω ∂μ
      exact hpositive.trans_le (hP_lower.trans hP_whole)
    exact probReal_negExcursion_sq_lt_of_posPart_integral
      hX hXi hX2 hsecond hmean hα hpos
  · have hNB : N ⊆ B := by
      intro ω hω
      change X ω ≤ -α
      change X ω ≤ -1 at hω
      linarith
    have hBmass : 3 * α < μ.real B :=
      hnegative.trans_le (measureReal_mono hNB)
    have hsq_le : α ^ 2 ≤ α := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hα_one)]
    change α ^ 2 < μ.real B
    exact hsq_le.trans_lt ((show α < 3 * α by linarith).trans hBmass)

end FTAPTheorem42
