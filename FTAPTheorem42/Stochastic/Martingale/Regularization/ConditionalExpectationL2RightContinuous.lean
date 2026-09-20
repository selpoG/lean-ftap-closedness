/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationL2Decreasing

/-!
# L² right continuity of conditional-expectation martingales

The usual conditions make every ambient null set measurable at every time.
This identifies the Hilbert limit along the canonical right approximations
with conditional expectation at the limiting time.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [m0 : MeasurableSpace Omega]

/-- An a.e. strongly measurable real function is genuinely measurable with
respect to a sub-sigma algebra containing every ambient null set. -/
theorem measurable_of_aestronglyMeasurable_of_nullSets
    {mu : Measure Omega} {m : MeasurableSpace Omega} {f : Omega → Real}
    (hNull : ∀ s : Set Omega, mu s = 0 → MeasurableSet[m] s)
    (hf : AEStronglyMeasurable[m] f mu) : Measurable[m] f := by
  let g : Omega → Real := hf.mk f
  let bad : Set Omega := {omega | f omega ≠ g omega}
  have hbadZero : mu bad = 0 := by
    change mu {omega | ¬f omega = g omega} = 0
    exact ae_iff.mp hf.ae_eq_mk
  have hbadMeas : MeasurableSet[m] bad := hNull bad hbadZero
  intro s hs
  have hgMeas : Measurable[m] g := hf.stronglyMeasurable_mk.measurable
  have hbadPart : MeasurableSet[m] (f ⁻¹' s ∩ bad) := by
    apply hNull
    exact measure_mono_null inter_subset_right hbadZero
  have hgoodPart : MeasurableSet[m] (g ⁻¹' s \ bad) :=
    (hgMeas hs).diff hbadMeas
  rw [show f ⁻¹' s = (g ⁻¹' s \ bad) ∪ (f ⁻¹' s ∩ bad) by
    ext omega
    by_cases homega : omega ∈ bad
    · simp [homega]
    · have heq : f omega = g omega := by
        simpa only [bad, mem_ofPred_eq, not_not] using homega
      simp [homega, heq]]
  exact hgoodPart.union hbadPart

/-- The decreasing conditional expectations converge in `L²` to the
conditional expectation on the intersection, provided every sigma algebra
contains all ambient null sets. -/
theorem tendsto_condExpL2Value_iInf_of_antitone
    {mu : Measure Omega} (m : Nat → MeasurableSpace Omega)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    (hNull : ∀ (n : Nat) (s : Set Omega),
      mu s = 0 → MeasurableSet[m n] s)
    (f : Lp Real 2 mu) :
    Tendsto (fun n => condExpL2Value mu (m n) (hm0 n) f) atTop
      (𝓝 (condExpL2Value mu (⨅ n, m n)
        (iInf_le_of_le 0 (hm0 0)) f)) := by
  let x : Nat → Lp Real 2 mu := fun n =>
    condExpL2Value mu (m n) (hm0 n) f
  obtain ⟨xlim, hxlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_condExpL2Value_of_antitone m hm hm0 f)
  have hxMemN : ∀ n, xlim ∈ lpMeas Real Real (m n) 2 mu := by
    intro n
    change AEStronglyMeasurable[m n] (xlim : Omega → Real) mu
    apply (isClosed_aestronglyMeasurable (F := Real)
      (p := (2 : ENNReal)) (μ := mu) (hm0 n)).mem_of_tendsto hxlim
    filter_upwards [eventually_ge_atTop n] with k hk
    change AEStronglyMeasurable[m n]
      (condExpL2Value mu (m k) (hm0 k) f : Omega → Real) mu
    have hkMeas : AEStronglyMeasurable[m k]
        (condExpL2Value mu (m k) (hm0 k) f : Omega → Real) mu := by
      simpa only [condExpL2Value] using
        (aestronglyMeasurable_condExpL2 (m := m k) (m0 := m0) (μ := mu)
          (hm0 k) f)
    exact hkMeas.mono (hm hk)
  have hxMeasN : ∀ n, Measurable[m n] (xlim : Omega → Real) := by
    intro n
    exact measurable_of_aestronglyMeasurable_of_nullSets (hNull n)
      (mem_lpMeas_iff_aestronglyMeasurable.mp (hxMemN n))
  have hxMeasInf : Measurable[⨅ n, m n] (xlim : Omega → Real) := by
    intro s hs
    exact MeasurableSpace.measurableSet_iInf.mpr fun n => hxMeasN n hs
  have hxMemInf : xlim ∈ lpMeas Real Real (⨅ n, m n) 2 mu :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr
      hxMeasInf.stronglyMeasurable.aestronglyMeasurable
  let hmInf : (⨅ n, m n) ≤ m0 := iInf_le_of_le 0 (hm0 0)
  let _ : Fact ((⨅ n, m n) ≤ m0) := ⟨hmInf⟩
  have hProjection :
      (lpMeas Real Real (⨅ n, m n) 2 mu).starProjection f = xlim := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hxMemInf
    intro y hy
    have hyMeasInf : AEStronglyMeasurable[⨅ n, m n]
        (y : Omega → Real) mu :=
      mem_lpMeas_iff_aestronglyMeasurable.mp hy
    have hInner : ∀ n, inner Real (x n) y = inner Real f y := by
      intro n
      exact inner_condExpL2_eq_inner_fun (m := m n) (m0 := m0) (μ := mu)
        (hm0 n) f y (hyMeasInf.mono (iInf_le _ n))
    have hInnerLimit : Tendsto (fun n => inner Real (x n) y) atTop
        (𝓝 (inner Real xlim y)) := hxlim.inner tendsto_const_nhds
    have hEq : inner Real xlim y = inner Real f y :=
      tendsto_nhds_unique hInnerLimit
        (tendsto_const_nhds.congr'
          (Eventually.of_forall fun n => (hInner n).symm))
    rw [inner_sub_left, hEq, sub_self]
  have hTarget : condExpL2Value mu (⨅ n, m n) hmInf f = xlim := by
    simpa only [condExpL2Value, condExpL2, Submodule.starProjection_apply] using
      hProjection
  simpa only [x, hmInf, hTarget] using hxlim

/-- Under the usual conditions, conditional expectations of a terminal
`L²` variable converge in `L²` from the right to their value at `t`. -/
theorem tendsto_condExpL2Value_rightApprox_of_usualConditions
    {mu : Measure Omega}
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hUsual : Filtration.UsualConditions mu F)
    (f : Lp Real 2 mu) (t : NNReal) :
    Tendsto (fun n =>
      condExpL2Value mu (F (condExpRightApproxTime t n))
        (F.le (condExpRightApproxTime t n)) f) atTop
      (𝓝 (condExpL2Value mu (F t) (F.le t) f)) := by
  have hLimit := tendsto_condExpL2Value_iInf_of_antitone
    (fun n => F (condExpRightApproxTime t n))
    (fun _n _k hnk => F.mono (condExpRightApproxTime_antitone t hnk))
    (fun n => F.le (condExpRightApproxTime t n))
    (fun n s hs => hUsual.measurableSet_of_null bot_le hs) f
  simpa only [iInf_filtration_condExpRightApproxTime_eq
    F hUsual.rightContinuous t] using hLimit

/-- Under the usual conditions, the same `L²` right continuity holds along
any deterministic sequence approaching `t` from the right. -/
theorem tendsto_condExpL2Value_of_tendsto_nhdsGT
    {mu : Measure Omega}
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hUsual : Filtration.UsualConditions mu F)
    (f : Lp Real 2 mu) (t : NNReal) (s : Nat -> NNReal)
    (hts : ∀ n, t ≤ s n) (hs : Tendsto s atTop (nhds t)) :
    Tendsto (fun n =>
      condExpL2Value mu (F (s n)) (F.le (s n)) f) atTop
      (nhds (condExpL2Value mu (F t) (F.le t) f)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hCanonical := tendsto_condExpL2Value_rightApprox_of_usualConditions
    F hUsual f t
  have hCanonicalEventually := hCanonical.eventually
    (Metric.ball_mem_nhds _ hepsilon)
  obtain ⟨m, hm⟩ := hCanonicalEventually.exists
  have htApprox : t < condExpRightApproxTime t m := by
    unfold condExpRightApproxTime
    exact lt_add_of_pos_right t
      (PredictableIntervalAlgebra.rightApproxZero_pos m)
  have hsBefore : ∀ᶠ n in atTop, s n < condExpRightApproxTime t m :=
    hs.eventually (Iio_mem_nhds htApprox)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsBefore
  refine ⟨N, fun n hn => ?_⟩
  have hDistanceLe := norm_sub_condExpL2Value_mono_of_le
    (m0 := inferInstance)
    (F.le t) (F.le (s n)) (F.le (condExpRightApproxTime t m))
    (F.mono (hts n)) (F.mono (hN n hn).le) f
  rw [dist_eq_norm]
  exact hDistanceLe.trans_lt (by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hm)

end FTAPTheorem42
