/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Rat
public import ElboimSly.Paper.Escape.Es55Stmt
public import ElboimSly.Paper.Escape.Plan5Meas
public import ElboimSly.Paper.Heavy.CyclicPath
public import Mathlib

/-!
# The frozen datum of Step 1 of ES22 Lemma 5.5

ES22 Lemma 5.5, Step 1.

From the entries `e₀` (walk `1`, ending at `v = W(ξ_B)`) and `e_B` (the backward walk `W_i^←`) of
the record at `S₃`:

* `d55T`: `t_* = t' - r_i - ξ_B` for the `a`-th jump `r_i = jt a` of `e_B`;
* `d55S`: the set of pairs `((e₀, e_B), y)` such that `e_B` exits `𝒬` at its `a`-th jump through
  `F_B` (with `w = jv a`), `y` satisfies the rational form of `E₅₆` for `(v, w, t_*)` and `y` does
  not jump at `t_*`.  It is measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

/-- `t_* = t' - r_i - ξ_B`, with `ξ_B = e₀.len`, `t' = cycFloor β (ξ_B + 4^j)` and `r_i` the time of
the `a`-th jump of the backward entry. -/
noncomputable def d55T (β : ℝ) (j : ℕ) (e₀ e_B : CycEntry ℕ (k + 2)) (a : ℕ) : ℝ :=
  cycFloor β (e₀.len.toReal + 4 ^ j) - (e_B.path.jt a).toReal - e₀.len.toReal

/-- `e_B` exits `𝒬` through `F_B` at its `a`-th jump. -/
def D55Exit (j : ℕ) (u : EscV k) (e_B : CycEntry ℕ (k + 2)) (a : ℕ) : Prop :=
  1 ≤ a ∧ e_B.path.jv a ∈ escFace j u ∧ ∀ b < a, e_B.path.jv b ∈ escQ j u

/-- The set `S` frozen at `S₃`. -/
def d55S (β : ℝ) (j : ℕ) (u : EscV k) :
    Set ((CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) × (ℝ≥0 → Fin (k + 2) → ℤ)) :=
  {x | ∃ a : ℕ, D55Exit j u x.1.2 a ∧
    EscRat β j u (entEnd x.1.1) (x.1.2.path.jv a) (d55T β j x.1.1 x.1.2 a) x.2 ∧
    noJumpRat x.2 (d55T β j x.1.1 x.1.2 a)}

theorem measurable_cycFloor (β : ℝ) : Measurable (cycFloor β) := by
  unfold cycFloor
  have h1 : Measurable fun x : ℝ => ⌊x / β⌋ := Int.measurable_floor.comp (measurable_id.div_const β)
  have h2 : Measurable fun x : ℝ => ((⌊x / β⌋ : ℤ) : ℝ) := measurable_from_top.comp h1
  have h3 : Measurable fun x : ℝ => x - β * ((⌊x / β⌋ : ℤ) : ℝ) :=
    measurable_id.sub (h2.const_mul β)
  have h4 : Measurable fun x : ℝ => ((⌊x - β * ((⌊x / β⌋ : ℤ) : ℝ)⌋ : ℤ) : ℝ) :=
    measurable_from_top.comp (Int.measurable_floor.comp h3)
  exact (h2.const_mul β).add h4

theorem es55_measurable_entry_jt (a : ℕ) : Measurable fun e : CycEntry ℕ (k + 2) => e.path.jt a :=
  (CPath.measurable_jt a).comp measurable_entPath

theorem es55_measurable_entry_jv (a : ℕ) : Measurable fun e : CycEntry ℕ (k + 2) => e.path.jv a :=
  (CPath.measurable_jv a).comp measurable_entPath

theorem measurable_d55T (β : ℝ) (j : ℕ) (a : ℕ) :
    Measurable fun p : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) => d55T β j p.1 p.2 a := by
  unfold d55T
  have h0 : Measurable fun p : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) => p.1.len.toReal :=
    ENNReal.measurable_toReal.comp (measurable_entry_len'.comp measurable_fst)
  have h1 : Measurable fun p : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) =>
      (p.2.path.jt a).toReal :=
    ENNReal.measurable_toReal.comp ((es55_measurable_entry_jt a).comp measurable_snd)
  exact (((measurable_cycFloor β).comp (h0.add measurable_const)).sub h1).sub h0

theorem measurableSet_d55S (β : ℝ) (j : ℕ) (u : EscV k) : MeasurableSet (d55S β j u) := by
  have e : d55S β j u = ⋃ a : ℕ, {x | D55Exit j u x.1.2 a} ∩
      ({x | EscRat β j u (entEnd x.1.1) (x.1.2.path.jv a) (d55T β j x.1.1 x.1.2 a) x.2} ∩
        {x | noJumpRat x.2 (d55T β j x.1.1 x.1.2 a)}) := by
    ext x; simp [d55S]
  rw [e]
  refine MeasurableSet.iUnion fun a => ?_
  have hjv : Measurable fun x : (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) ×
      (ℝ≥0 → Fin (k + 2) → ℤ) => x.1.2.path.jv a :=
    (es55_measurable_entry_jv a).comp (measurable_snd.comp measurable_fst)
  have hT : Measurable fun x : (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) ×
      (ℝ≥0 → Fin (k + 2) → ℤ) => d55T β j x.1.1 x.1.2 a :=
    (measurable_d55T β j a).comp measurable_fst
  refine ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · have e2 : {x : (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) × (ℝ≥0 → Fin (k + 2) → ℤ) |
        D55Exit j u x.1.2 a} = {x | 1 ≤ a} ∩ ({x | x.1.2.path.jv a ∈ escFace j u} ∩
          ⋂ b ∈ Finset.range a, {x | x.1.2.path.jv b ∈ escQ j u}) := by
      ext x; simp [D55Exit]
    rw [e2]
    refine (MeasurableSet.const _).inter (MeasurableSet.inter ?_ ?_)
    · exact (MeasurableSet.of_discrete (s := escFace j u)).preimage hjv
    · refine Finset.measurableSet_biInter _ fun b _ => ?_
      exact (MeasurableSet.of_discrete (s := escQ j u)).preimage
        ((es55_measurable_entry_jv b).comp (measurable_snd.comp measurable_fst))
  · have hv : Measurable fun x : (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) ×
        (ℝ≥0 → Fin (k + 2) → ℤ) => entEnd x.1.1 :=
      (measurable_entEnd (k := k)).comp (measurable_fst.comp measurable_fst)
    exact measurableSet_escRat (X := (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) ×
        (ℝ≥0 → Fin (k + 2) → ℤ)) β j u (fun x => entEnd x.1.1) (fun x => x.1.2.path.jv a)
      (fun x => d55T β j x.1.1 x.1.2 a) (fun x => x.2) hv hjv hT measurable_snd
  · exact measurableSet_noJumpRat (X := (CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2)) ×
        (ℝ≥0 → Fin (k + 2) → ℤ)) (fun x => d55T β j x.1.1 x.1.2 a) hT (fun x => x.2)
      measurable_snd

end ElboimSly.Paper.Escape
