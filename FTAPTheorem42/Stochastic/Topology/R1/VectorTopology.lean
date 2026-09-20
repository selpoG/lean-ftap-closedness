/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.ScalarContinuity
import FTAPTheorem42.Stochastic.Topology.R1.Complete

/-! # The complete r1 topological vector space -/

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.R1Process

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [hUsual : Fact (Filtration.UsualConditions mu F)]

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] hUsual in
theorem val_injective : Function.Injective (val : R1Process F mu → Process Ω) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  cases h
  rfl

instance : Zero (R1Process F mu) where
  zero := ⟨0, (semimartingaleR1_ne_top_iff_decomposition hUsual.out).mp
    (by rw [semimartingaleR1_zero]; exact ENNReal.zero_ne_top)⟩

noncomputable instance : Add (R1Process F mu) where
  add X Y := ⟨X.val + Y.val, by
    obtain ⟨D⟩ := X.property
    obtain ⟨E⟩ := Y.property
    exact ⟨D.add E⟩⟩

instance : Neg (R1Process F mu) where
  neg X := ⟨-X.val, X.property.map J1Decomposition.neg⟩

noncomputable instance : Sub (R1Process F mu) where
  sub X Y := X + -Y

instance : SMul Nat (R1Process F mu) where
  smul n X := (n : Real) • X

instance : SMul Int (R1Process F mu) where
  smul n X := (n : Real) • X

@[simp] theorem zero_val : (0 : R1Process F mu).val = 0 := rfl
omit hUsual in
@[simp] theorem add_val (X Y : R1Process F mu) : (X + Y).val = X.val + Y.val := rfl
omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] hUsual in
@[simp] theorem neg_val (X : R1Process F mu) : (-X).val = -X.val := rfl
omit hUsual in
@[simp] theorem sub_val (X Y : R1Process F mu) : (X - Y).val = X.val - Y.val := by
  change X.val + -Y.val = X.val - Y.val
  exact (sub_eq_add_neg _ _).symm

noncomputable instance : AddCommGroup (R1Process F mu) :=
  val_injective.addCommGroup val rfl add_val neg_val sub_val
    (fun X n => by
      change (n : Real) • X.val = n • X.val
      funext t w
      simp [Pi.smul_apply, smul_eq_mul])
    (fun X n => by
      change (n : Real) • X.val = n • X.val
      funext t w
      simp [Pi.smul_apply, smul_eq_mul])

noncomputable instance : Module Real (R1Process F mu) :=
  Function.Injective.module Real
    ({ toFun := val, map_zero' := zero_val, map_add' := add_val } :
      R1Process F mu →+ Process Ω)
    val_injective smul_val

instance : ContinuousAdd (R1Process F mu) where
  continuous_add := by
    apply continuous_iff_seqContinuous.mpr
    intro u p hu
    have hX := (continuous_fst.tendsto p).comp hu
    have hY := (continuous_snd.tendsto p).comp hu
    rw [tendsto_iff_edist_tendsto_0] at hX hY ⊢
    have hUpper := hX.add hY
    simp only [zero_add] at hUpper
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun _ => bot_le)
    intro n
    change semimartingaleR1 (((u n).1.val + (u n).2.val) - (p.1.val + p.2.val)) F mu ≤ _
    rw [show (u n).1.val + (u n).2.val - (p.1.val + p.2.val) =
      ((u n).1.val - p.1.val) + ((u n).2.val - p.2.val) by abel]
    exact semimartingaleR1_add_le hUsual.out

instance : ContinuousNeg (R1Process F mu) where
  continuous_neg := by
    have h : Continuous (fun X : R1Process F mu => (-1 : Real) • X) :=
      continuous_const_smul (-1 : Real)
    simpa only [neg_one_smul] using h

instance : IsTopologicalAddGroup (R1Process F mu) where

end FTAPTheorem42.R1Process
