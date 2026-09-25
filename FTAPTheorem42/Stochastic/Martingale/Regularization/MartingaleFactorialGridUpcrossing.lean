/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.Variation
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleChronologicalGrid
import FTAPTheorem42.Stochastic.Process.FiniteUpcrossingChain
import Mathlib.Probability.Martingale.Upcrossing

/-!
# Martingale upcrossings on fixed-horizon factorial grids

Sampling a continuous-time martingale on a fixed-horizon factorial grid gives
a discrete martingale.  Since every such grid ends exactly at the prescribed
horizon, Doob's upcrossing inequality has one right-hand side independent of
the mesh.  This is the probabilistic estimate used to construct simultaneous
one-sided limits on the nested dense skeleton.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- The index of an old grid point in the next factorial refinement. -/
def refinementIndex (r k : Nat) : Nat :=
  (r + 1) * k

theorem refinementIndex_strictMono (r : Nat) :
    StrictMono (refinementIndex r) := by
  intro k l hkl
  exact Nat.mul_lt_mul_of_pos_left hkl (Nat.succ_pos r)

@[simp]
theorem refinementIndex_size (T : NNReal) (r : Nat) :
    refinementIndex r (size T r) = size T (r + 1) := by
  unfold refinementIndex size
  rw [Nat.factorial_succ]
  ac_rfl

/-- Sampling the next factorial grid at an embedded old index recovers the
old sampled time. -/
theorem sampledTime_refinement (T : NNReal) (r k : Nat)
    (hk : k <= size T r) :
    (grid T (r + 1)).sampledTime (refinementIndex r k) =
      (grid T r).sampledTime k := by
  have hRefineLe : refinementIndex r k <= size T (r + 1) := by
    rw [<- refinementIndex_size T r]
    exact (refinementIndex_strictMono r).monotone hk
  unfold ChronologicalGrid.sampledTime ChronologicalGrid.natIndex
  simp only [min_eq_left hk, min_eq_left hRefineLe, grid_time]
  congr 1
  unfold refinementIndex
  simp only [Nat.cast_mul, Nat.factorial_succ]
  rw [mul_div_mul_left]
  positivity

omit [MeasurableSpace Omega] in
/-- A crossing chain ending at an arbitrary old-grid index is transported to
the corresponding index of the next factorial refinement. -/
theorem HasUpcrossingChain.factorialGrid_succ_before
    {a b : Real} {M : Process Omega} {omega : Omega}
    {k N : Nat} (T : NNReal) (r : Nat) (hN : N <= size T r)
    (hChain : HasUpcrossingChain a b ((grid T r).natSample M)
      omega k N) :
    HasUpcrossingChain a b ((grid T (r + 1)).natSample M)
      omega k (refinementIndex r N) := by
  exact hChain.map (refinementIndex r) (refinementIndex_strictMono r)
    (fun i hi => by
      change M ((grid T (r + 1)).sampledTime (refinementIndex r i)) omega =
        M ((grid T r).sampledTime i) omega
      rw [sampledTime_refinement T r i (hi.le.trans hN)])

omit [MeasurableSpace Omega] in
/-- An arbitrary-horizon chain and its terminal sampled time persist through
every later factorial refinement. -/
theorem HasUpcrossingChain.exists_factorialGrid_mono_before
    {a b : Real} {M : Process Omega} {omega : Omega}
    {k N r q : Nat} (T : NNReal) (hrq : r <= q) (hN : N <= size T r)
    (hChain : HasUpcrossingChain a b ((grid T r).natSample M)
      omega k N) :
    ∃ Nq, Nq ≤ size T q ∧
      (grid T q).sampledTime Nq = (grid T r).sampledTime N ∧
      HasUpcrossingChain a b ((grid T q).natSample M) omega k Nq := by
  induction q, hrq using Nat.le_induction with
  | base => exact ⟨N, hN, rfl, hChain⟩
  | succ q _ ih =>
      obtain ⟨Nq, hNq, hTime, hqChain⟩ := ih
      refine ⟨refinementIndex q Nq, ?_, ?_,
        HasUpcrossingChain.factorialGrid_succ_before T q hNq hqChain⟩
      · rw [<- refinementIndex_size T q]
        exact (refinementIndex_strictMono q).monotone hNq
      · rw [sampledTime_refinement T q Nq hNq, hTime]

omit [MeasurableSpace Omega] in
/-- Crossing times on an old factorial grid embed no earlier than the
corresponding crossing times on the refined grid. -/
private theorem crossingTime_refinement_le
    (M : Process Omega) (T : NNReal) (r : Nat)
    (a b : Real) (omega : Omega) (n : Nat) :
    (upperCrossingTime a b ((grid T r).natSample M) (size T r) n omega <
        size T r ->
      upperCrossingTime a b ((grid T (r + 1)).natSample M)
          (size T (r + 1)) n omega <=
        refinementIndex r
          (upperCrossingTime a b ((grid T r).natSample M)
            (size T r) n omega)) /\
    (lowerCrossingTime a b ((grid T r).natSample M) (size T r) n omega <
        size T r ->
      lowerCrossingTime a b ((grid T (r + 1)).natSample M)
          (size T (r + 1)) n omega <=
        refinementIndex r
          (lowerCrossingTime a b ((grid T r).natSample M)
            (size T r) n omega)) := by
  induction n with
  | zero =>
      constructor
      · intro _
        simp [refinementIndex]
      · intro hLower
        rw [lowerCrossingTime]
        have hCandidate :
            refinementIndex r
                (lowerCrossingTime a b ((grid T r).natSample M)
                  (size T r) 0 omega) <
              size T (r + 1) := by
          rw [<- refinementIndex_size T r]
          exact (refinementIndex_strictMono r) hLower
        apply (hittingBtwn_le_iff_of_lt _ hCandidate).2
        refine Exists.intro
          (refinementIndex r
            (lowerCrossingTime a b ((grid T r).natSample M)
              (size T r) 0 omega)) ?_
        constructor
        · constructor
          · simp [refinementIndex]
          · exact le_rfl
        · have hValue :
              (grid T r).natSample M
                  (lowerCrossingTime a b ((grid T r).natSample M)
                    (size T r) 0 omega) omega ∈ Set.Iic a := by
            rw [lowerCrossingTime] at hLower ⊢
            exact hittingBtwn_mem_set_of_hittingBtwn_lt hLower
          change M ((grid T (r + 1)).sampledTime
            (refinementIndex r
              (lowerCrossingTime a b ((grid T r).natSample M)
                (size T r) 0 omega))) omega <= a
          rw [sampledTime_refinement T r _ lowerCrossingTime_le]
          exact hValue
  | succ n ih =>
      have hUpperStep :
          upperCrossingTime a b ((grid T r).natSample M)
                (size T r) (n + 1) omega < size T r ->
            upperCrossingTime a b ((grid T (r + 1)).natSample M)
                (size T (r + 1)) (n + 1) omega <=
              refinementIndex r
                (upperCrossingTime a b ((grid T r).natSample M)
                  (size T r) (n + 1) omega) := by
        intro hUpper
        rw [upperCrossingTime_succ_eq]
        have hLowerCoarse :
            lowerCrossingTime a b ((grid T r).natSample M)
                (size T r) n omega < size T r :=
          lowerCrossingTime_le_upperCrossingTime_succ.trans_lt hUpper
        have hCandidate :
            refinementIndex r
                (upperCrossingTime a b ((grid T r).natSample M)
                  (size T r) (n + 1) omega) <
              size T (r + 1) := by
          rw [<- refinementIndex_size T r]
          exact (refinementIndex_strictMono r) hUpper
        apply (hittingBtwn_le_iff_of_lt _ hCandidate).2
        refine Exists.intro
          (refinementIndex r
            (upperCrossingTime a b ((grid T r).natSample M)
              (size T r) (n + 1) omega)) ?_
        constructor
        · constructor
          · exact (ih.2 hLowerCoarse).trans <|
              (refinementIndex_strictMono r).monotone
                lowerCrossingTime_le_upperCrossingTime_succ
          · exact le_rfl
        · have hValue :
              (grid T r).natSample M
                  (upperCrossingTime a b ((grid T r).natSample M)
                    (size T r) (n + 1) omega) omega ∈ Set.Ici b := by
            rw [upperCrossingTime_succ_eq] at hUpper ⊢
            exact hittingBtwn_mem_set_of_hittingBtwn_lt hUpper
          change b <= M ((grid T (r + 1)).sampledTime
            (refinementIndex r
              (upperCrossingTime a b ((grid T r).natSample M)
                (size T r) (n + 1) omega))) omega
          rw [sampledTime_refinement T r _ upperCrossingTime_le]
          exact hValue
      refine ⟨hUpperStep, ?_⟩
      intro hLower
      rw [lowerCrossingTime]
      have hUpperCoarse :
            upperCrossingTime a b ((grid T r).natSample M)
                (size T r) (n + 1) omega < size T r :=
          upperCrossingTime_le_lowerCrossingTime.trans_lt hLower
      have hCandidate :
            refinementIndex r
                (lowerCrossingTime a b ((grid T r).natSample M)
                  (size T r) (n + 1) omega) <
              size T (r + 1) := by
          rw [<- refinementIndex_size T r]
          exact (refinementIndex_strictMono r) hLower
      apply (hittingBtwn_le_iff_of_lt _ hCandidate).2
      refine Exists.intro
          (refinementIndex r
            (lowerCrossingTime a b ((grid T r).natSample M)
              (size T r) (n + 1) omega)) ?_
      constructor
      · constructor
        · exact (hUpperStep hUpperCoarse).trans <|
              (refinementIndex_strictMono r).monotone
                upperCrossingTime_le_lowerCrossingTime
        · exact le_rfl
      · have hValue :
            (grid T r).natSample M
                (lowerCrossingTime a b ((grid T r).natSample M)
                  (size T r) (n + 1) omega) omega ∈ Set.Iic a := by
          rw [lowerCrossingTime] at hLower ⊢
          exact hittingBtwn_mem_set_of_hittingBtwn_lt hLower
        change M ((grid T (r + 1)).sampledTime
          (refinementIndex r
            (lowerCrossingTime a b ((grid T r).natSample M)
              (size T r) (n + 1) omega))) omega <= a
        rw [sampledTime_refinement T r _ lowerCrossingTime_le]
        exact hValue

/-- Number of completed upcrossings before the terminal index of the
level-`r` fixed-horizon factorial grid. -/
noncomputable def martingaleUpcrossingsBefore
    (M : Process Omega) (T : NNReal) (r : Nat) (a b : Real) :
    Omega -> Nat :=
  upcrossingsBefore a b ((grid T r).natSample M) (size T r)

omit [MeasurableSpace Omega] in
/-- Refining a factorial grid can only increase the number of completed
upcrossings. -/
theorem martingaleUpcrossingsBefore_le_succ
    (M : Process Omega) (T : NNReal) (r : Nat)
    {a b : Real} (hab : a < b) (omega : Omega) :
    martingaleUpcrossingsBefore M T r a b omega <=
      martingaleUpcrossingsBefore M T (r + 1) a b omega := by
  by_cases hSize : size T r = 0
  · have hSizeSucc : size T (r + 1) = 0 := by
      rw [<- refinementIndex_size T r, hSize]
      rfl
    simp [martingaleUpcrossingsBefore, hSize, hSizeSucc]
  · have hSizePos : 0 < size T r := Nat.pos_of_ne_zero hSize
    have hCoarseCross :
        upperCrossingTime a b ((grid T r).natSample M) (size T r)
            (martingaleUpcrossingsBefore M T r a b omega) omega <
          size T r := by
      exact upperCrossingTime_lt_of_le_upcrossingsBefore hSizePos hab le_rfl
    have hFineCross :
        upperCrossingTime a b ((grid T (r + 1)).natSample M)
            (size T (r + 1))
            (martingaleUpcrossingsBefore M T r a b omega) omega <
          size T (r + 1) := by
      refine lt_of_le_of_lt
        ((crossingTime_refinement_le M T r a b omega _).1 hCoarseCross) ?_
      rw [<- refinementIndex_size T r]
      exact (refinementIndex_strictMono r) hCoarseCross
    unfold martingaleUpcrossingsBefore upcrossingsBefore
    exact le_csSup (upperCrossingTime_lt_bddAbove hab) hFineCross

omit [MeasurableSpace Omega] in
/-- The factorial-grid upcrossing counts form a monotone sequence in the
refinement level. -/
theorem martingaleUpcrossingsBefore_mono
    (M : Process Omega) (T : NNReal) {a b : Real} (hab : a < b)
    (omega : Omega) :
    Monotone (fun r => martingaleUpcrossingsBefore M T r a b omega) :=
  monotone_nat_of_le_succ fun r =>
    martingaleUpcrossingsBefore_le_succ M T r hab omega

/-- Total number of upcrossings seen on the nested factorial grids.  The
value is allowed to be infinite before the almost-sure estimate is applied. -/
noncomputable def martingaleFactorialGridUpcrossings
    (M : Process Omega) (T : NNReal) (a b : Real) : Omega -> ENNReal :=
  fun omega => ⨆ r,
    (martingaleUpcrossingsBefore M T r a b omega : ENNReal)

omit [MeasurableSpace Omega] in
/-- Finiteness of the total factorial-grid upcrossing count is equivalent to
a single natural bound for every grid level. -/
theorem martingaleFactorialGridUpcrossings_lt_top_iff
    (M : Process Omega) (T : NNReal) (a b : Real) (omega : Omega) :
    martingaleFactorialGridUpcrossings M T a b omega < (⊤ : ENNReal) <->
      exists K : Nat, forall r,
        martingaleUpcrossingsBefore M T r a b omega <= K := by
  unfold martingaleFactorialGridUpcrossings
  constructor
  · intro hFinite
    lift (iSup fun r =>
      (martingaleUpcrossingsBefore M T r a b omega : ENNReal)) to NNReal
        using hFinite.ne with c hc
    obtain ⟨K, hK⟩ := exists_nat_ge c
    refine ⟨K, fun r => ?_⟩
    have hSupLe :
        (iSup fun q =>
          (martingaleUpcrossingsBefore M T q a b omega : ENNReal)) <=
          (c : ENNReal) := hc.symm.le
    have hr : (martingaleUpcrossingsBefore M T r a b omega : ENNReal) <=
        (K : ENNReal) :=
      (le_iSup (fun q =>
        (martingaleUpcrossingsBefore M T q a b omega : ENNReal)) r).trans
          (hSupLe.trans (by exact_mod_cast hK))
    exact_mod_cast hr
  · rintro ⟨K, hK⟩
    exact lt_of_le_of_lt (iSup_le fun r => by
      have hr : (martingaleUpcrossingsBefore M T r a b omega : ENNReal) <=
          (K : ENNReal) := by exact_mod_cast hK r
      exact hr)
      ENNReal.coe_lt_top

/-- A factorial-grid upcrossing count is measurable. -/
theorem measurable_martingaleUpcrossingsBefore
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (hM : Martingale M F mu) (T : NNReal) (r : Nat)
    {a b : Real} (hab : a < b) :
    Measurable (martingaleUpcrossingsBefore M T r a b) := by
  have hSample : Martingale ((grid T r).natSample M)
      ((grid T r).sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := grid T r) hM
  exact hSample.stronglyAdapted.measurable_upcrossingsBefore hab

/-- A factorial-grid upcrossing count, viewed as a real random variable, is
integrable under every finite measure. -/
theorem integrable_martingaleUpcrossingsBefore
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal) (r : Nat)
    {a b : Real} (hab : a < b) :
    Integrable (fun omega =>
      (martingaleUpcrossingsBefore M T r a b omega : Real)) mu := by
  have hSample : Martingale ((grid T r).natSample M)
      ((grid T r).sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := grid T r) hM
  exact hSample.stronglyAdapted.integrable_upcrossingsBefore hab

/-- The total factorial-grid upcrossing count is measurable. -/
theorem measurable_martingaleFactorialGridUpcrossings
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega}
    (hM : Martingale M F mu) (T : NNReal)
    {a b : Real} (hab : a < b) :
    Measurable (martingaleFactorialGridUpcrossings M T a b) := by
  exact Measurable.iSup fun r =>
    measurable_from_top.comp
      (measurable_martingaleUpcrossingsBefore hM T r hab)

/-- Doob's upcrossing estimate on a factorial grid.  The terminal value is
`M T`, so the bound is uniform in the grid level `r`. -/
theorem Martingale.mul_integral_martingaleUpcrossingsBefore_le
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal) (r : Nat)
    (a b : Real) :
    (b - a) * (∫ omega,
      (martingaleUpcrossingsBefore M T r a b omega : Real) ∂mu) <=
      ∫ omega, (M T omega - a)⁺ ∂mu := by
  have hSample : Martingale ((grid T r).natSample M)
      ((grid T r).sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := grid T r) hM
  have hEstimate :=
    hSample.submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part
      a b (size T r)
  simpa only [martingaleUpcrossingsBefore, ChronologicalGrid.natSample,
    sampledTime_size] using hEstimate

/-- Doob's uniform estimate after taking the supremum over all factorial
grid levels. -/
theorem Martingale.mul_lintegral_martingaleFactorialGridUpcrossings_le
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    {a b : Real} (hab : a < b) :
    ENNReal.ofReal (b - a) *
        (∫⁻ omega, martingaleFactorialGridUpcrossings M T a b omega ∂mu) <=
      ∫⁻ omega, ENNReal.ofReal ((M T omega - a)⁺) ∂mu := by
  change ENNReal.ofReal (b - a) *
      (∫⁻ omega, ⨆ r,
        (martingaleUpcrossingsBefore M T r a b omega : ENNReal) ∂mu) <= _
  rw [lintegral_iSup]
  · rw [ENNReal.mul_iSup, iSup_le_iff]
    intro r
    rw [(by simp :
        (∫⁻ omega,
          (martingaleUpcrossingsBefore M T r a b omega : ENNReal) ∂mu) =
        ∫⁻ omega,
          ((martingaleUpcrossingsBefore M T r a b omega : Nat) : NNReal) ∂mu),
      lintegral_coe_eq_integral,
      <- ENNReal.ofReal_mul (sub_pos.2 hab).le]
    · exact ENNReal.ofReal_le_ofReal
        (Martingale.mul_integral_martingaleUpcrossingsBefore_le
          hM T r a b) |>.trans
          (ofReal_integral_eq_lintegral_ofReal
            ((hM.integrable T).sub (integrable_const a)).pos_part
            (Filter.Eventually.of_forall fun omega => posPart_nonneg _)).le
    · simpa only [NNReal.coe_natCast] using
        integrable_martingaleUpcrossingsBefore hM T r hab
  · intro r
    exact measurable_from_top.comp
      (measurable_martingaleUpcrossingsBefore hM T r hab)
  · intro r s hrs omega
    simpa only [ENNReal.coe_natCast, Nat.cast_le] using
      martingaleUpcrossingsBefore_mono M T hab omega hrs

/-- A martingale has only finitely many upcrossings on the union of the
nested factorial grids, almost surely. -/
theorem Martingale.martingaleFactorialGridUpcrossings_ae_lt_top
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal)
    {a b : Real} (hab : a < b) :
    ∀ᵐ omega ∂mu,
      martingaleFactorialGridUpcrossings M T a b omega < ∞ := by
  refine ae_lt_top
    (measurable_martingaleFactorialGridUpcrossings hM T hab) ?_
  have hBound :=
    Martingale.mul_lintegral_martingaleFactorialGridUpcrossings_le
      hM T hab
  have hCoefficient : ENNReal.ofReal (b - a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.2 hab))
  have hRightFinite :
      (∫⁻ omega, ENNReal.ofReal ((M T omega - a)⁺) ∂mu) ≠ ∞ :=
    ((hM.integrable T).sub (integrable_const a)).pos_part.lintegral_lt_top.ne
  rw [mul_comm,
    <- ENNReal.le_div_iff_mul_le (Or.inl hCoefficient)
      (Or.inl ENNReal.ofReal_ne_top)] at hBound
  exact (lt_of_le_of_lt hBound
    (ENNReal.div_lt_top hRightFinite hCoefficient)).ne

/-- The finite-upcrossing event can be chosen simultaneously for every
rational interval. -/
theorem Martingale.martingaleFactorialGridUpcrossings_rat_ae_lt_top
    {M : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (hM : Martingale M F mu) (T : NNReal) :
    ∀ᵐ omega ∂mu, ∀ a b : Rat, a < b ->
      martingaleFactorialGridUpcrossings M T a b omega < ∞ := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  by_cases hab : a < b
  · filter_upwards
      [Martingale.martingaleFactorialGridUpcrossings_ae_lt_top
        hM T (Rat.cast_lt.2 hab)] with omega hFinite
    exact fun _ => hFinite
  · exact Filter.Eventually.of_forall fun _ h => (hab h).elim

end HorizonFactorialGrid

end FTAPTheorem42
