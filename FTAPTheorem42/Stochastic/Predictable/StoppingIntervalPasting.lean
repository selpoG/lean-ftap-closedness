import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingInterval
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! # Pasting predictable coefficients along increasing stopping intervals

The finite prefixes agree up to every earlier stopping time. Their pointwise
limit is predictable and restricts exactly to each finite finitePrefix.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42.StoppingIntervalPasting

variable {Ω : Type*}

noncomputable def interval (τ : Nat → Ω → NNReal) (n : Nat) : Set (NNReal × Ω) :=
  stochasticIntervalIocZeroTop (fun ω => (τ n ω : WithTop NNReal))

noncomputable def finitePrefix (τ : Nat → Ω → NNReal) (K : Nat → Process Ω) : Nat → Process Ω
  | 0 => PredictableProcess.restrict (interval τ 0) (K 0)
  | n + 1 => finitePrefix τ K n +
      PredictableProcess.restrict (interval τ (n + 1) \ interval τ n) (K (n + 1))

noncomputable def paste (τ : Nat → Ω → NNReal) (K : Nat → Process Ω) : Process Ω :=
  fun t ω => limUnder atTop (fun n => finitePrefix τ K n t ω)

theorem interval_mono {τ : Nat → Ω → NNReal} (hτ : ∀ ω, Monotone (fun n => τ n ω))
    {n m : Nat} (hnm : n ≤ m) : interval τ n ⊆ interval τ m := by
  intro p hp
  obtain ⟨ht, hle⟩ := (mem_stochasticIntervalIocZeroTop_iff _ _ _).mp hp
  exact (mem_stochasticIntervalIocZeroTop_iff _ _ _).mpr
    ⟨ht, hle.trans (WithTop.coe_le_coe.mpr (hτ p.2 hnm))⟩

theorem prefix_eq_zero_of_notMem {τ : Nat → Ω → NNReal}
    (hτ : ∀ ω, Monotone (fun n => τ n ω)) (K : Nat → Process Ω)
    (n : Nat) {t : NNReal} {ω : Ω} (ht : (t, ω) ∉ interval τ n) :
    finitePrefix τ K n t ω = 0 := by
  induction n with
  | zero => exact PredictableProcess.restrict_apply_of_notMem ht
  | succ n ih =>
    have hn : (t, ω) ∉ interval τ n := fun h => ht (interval_mono hτ (Nat.le_succ n) h)
    have hd : (t, ω) ∉ interval τ (n + 1) \ interval τ n := fun h => ht h.1
    change finitePrefix τ K n t ω + PredictableProcess.restrict _ _ t ω = 0
    rw [ih hn, PredictableProcess.restrict_apply_of_notMem hd, add_zero]

theorem prefix_stable {τ : Nat → Ω → NNReal}
    (hτ : ∀ ω, Monotone (fun n => τ n ω)) (K : Nat → Process Ω)
    {n m : Nat} (hnm : n ≤ m) {t : NNReal} {ω : Ω} (ht : (t, ω) ∈ interval τ n) :
    finitePrefix τ K m t ω = finitePrefix τ K n t ω := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hd : (t, ω) ∉ interval τ (m + 1) \ interval τ m :=
      fun h => h.2 (interval_mono hτ hnm ht)
    change finitePrefix τ K m t ω + PredictableProcess.restrict _ _ t ω = _
    rw [PredictableProcess.restrict_apply_of_notMem hd, add_zero, ih]

theorem paste_restrict {τ : Nat → Ω → NNReal}
    (hτ : ∀ ω, Monotone (fun n => τ n ω)) (K : Nat → Process Ω) (n : Nat) :
    PredictableProcess.restrict (interval τ n) (paste τ K) = finitePrefix τ K n := by
  funext t ω
  by_cases ht : (t, ω) ∈ interval τ n
  · rw [PredictableProcess.restrict_apply_of_mem ht]
    have he : ∀ᶠ m in atTop, finitePrefix τ K m t ω = finitePrefix τ K n t ω :=
      (eventually_ge_atTop n).mono (fun _ hm => prefix_stable hτ K hm ht)
    exact (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))).limUnder_eq
  · rw [PredictableProcess.restrict_apply_of_notMem ht, prefix_eq_zero_of_notMem hτ K n ht]

theorem prefix_disjoint_next {τ : Nat → Ω → NNReal}
    (hτ : ∀ ω, Monotone (fun n => τ n ω)) (K : Nat → Process Ω) (n : Nat) :
    ∀ t ω, finitePrefix τ K n t ω = 0 ∨
      PredictableProcess.restrict (interval τ (n + 1) \ interval τ n) (K (n + 1)) t ω = 0 := by
  intro t ω
  by_cases ht : (t, ω) ∈ interval τ n
  · exact Or.inr (PredictableProcess.restrict_apply_of_notMem (fun h => h.2 ht))
  · exact Or.inl (prefix_eq_zero_of_notMem hτ K n ht)

variable [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}

theorem interval_predictable {τ : Nat → Ω → NNReal}
    (hτ : ∀ n, IsStoppingTime F (fun ω => (τ n ω : WithTop NNReal))) (n : Nat) :
    MeasurableSet[F.predictable] (interval τ n) :=
  IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop (hτ n)

theorem prefix_predictable {τ : Nat → Ω → NNReal}
    (hτ : ∀ n, IsStoppingTime F (fun ω => (τ n ω : WithTop NNReal)))
    {K : Nat → Process Ω} (hK : ∀ n, IsStronglyPredictable F (K n)) (n : Nat) :
    IsStronglyPredictable F (finitePrefix τ K n) := by
  induction n with
  | zero =>
    exact PredictableProcess.isStronglyPredictable_restrict (interval_predictable hτ 0) (hK 0)
  | succ n ih => exact ih.add (PredictableProcess.isStronglyPredictable_restrict
      ((interval_predictable hτ (n + 1)).diff (interval_predictable hτ n)) (hK (n + 1)))

theorem paste_predictable {τ : Nat → Ω → NNReal}
    (hτ : ∀ n, IsStoppingTime F (fun ω => (τ n ω : WithTop NNReal)))
    {K : Nat → Process Ω} (hK : ∀ n, IsStronglyPredictable F (K n)) :
    IsStronglyPredictable F (paste τ K) := by
  exact @MeasureTheory.StronglyMeasurable.limUnder
    Nat (NNReal × Ω) Real F.predictable _ _ atTop _
    (fun n p => finitePrefix τ K n p.1 p.2) _ _ (prefix_predictable hτ hK)

end FTAPTheorem42.StoppingIntervalPasting
