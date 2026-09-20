import FTAPTheorem42.Foundations.UsualConditions
import Mathlib.Probability.Process.LocalProperty

/-! # Everywhere increasing finite localizing sequences

Under the usual conditions a single exceptional null set can be replaced
by deterministic times. All original stopping times are preserved almost
surely, while monotonicity and exhaustiveness become pathwise properties.
-/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}

/-- A finite localizer admits an everywhere monotone exhaustive version,
with one common null set for the entire sequence. -/
theorem exists_everywhere_finiteLocalizer
    (hUsual : Filtration.UsualConditions μ F) (τ : Nat → Ω → NNReal)
    (hτ : IsLocalizingSequence F (fun n ω => (τ n ω : WithTop NNReal)) μ) :
    ∃ υ : Nat → Ω → NNReal,
      (∀ n, IsStoppingTime F (fun ω => (υ n ω : WithTop NNReal))) ∧
      (∀ ω, Monotone (fun n => υ n ω)) ∧
      (∀ ω, Tendsto (fun n => (υ n ω : WithTop NNReal)) atTop (𝓝 ⊤)) ∧
      ∀ᵐ ω ∂μ, ∀ n, υ n ω = τ n ω := by
  classical
  let good := {ω | Monotone (fun n => (τ n ω : WithTop NNReal)) ∧
    Tendsto (fun n => (τ n ω : WithTop NNReal)) atTop (𝓝 ⊤)}
  have hGood : ∀ᵐ ω ∂μ, ω ∈ good := hτ.mono.and hτ.tendsto_top
  have hNull : μ goodᶜ = 0 := by
    change μ {ω | ¬ω ∈ good} = 0
    exact ae_iff.mp hGood
  have hMeas : MeasurableSet[F 0] good := by
    have hm := (hUsual.containsNullSetsAtZero goodᶜ hNull).compl
    rwa [compl_compl] at hm
  let υ n ω := if ω ∈ good then τ n ω else ((n + 1 : Nat) : NNReal)
  refine ⟨υ, ?_, ?_, ?_, ?_⟩
  · intro n
    have hs := (hτ.isStoppingTime n).piecewise_of_le
      (isStoppingTime_const F ((n + 1 : Nat) : NNReal))
      (i := (0 : NNReal)) (fun _ => bot_le) (fun _ => bot_le) hMeas
    convert hs using 1
    funext ω
    by_cases hω : ω ∈ good <;> simp only [υ, hω, ite_true, ite_false,
      Set.piecewise]
  · intro ω n m hnm
    by_cases hω : ω ∈ good
    · simpa only [υ, ite_eq_left hω, WithTop.coe_le_coe] using hω.1 hnm
    · simp only [υ, ite_eq_right hω]
      exact_mod_cast Nat.add_le_add_right hnm 1
  · intro ω
    by_cases hω : ω ∈ good
    · simpa only [υ, ite_eq_left hω] using hω.2
    · simp only [υ, ite_eq_right hω]
      exact WithTop.tendsto_coe_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  · filter_upwards [hGood] with ω hω
    exact fun n => ite_eq_left hω

end FTAPTheorem42
