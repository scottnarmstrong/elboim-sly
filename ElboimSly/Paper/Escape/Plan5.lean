/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Meas
public import Mathlib

/-!
# The connecting plan

The connecting plan (and the box escQ, the backward walks and zeta_i for the box `𝒬`).

`plan5 n β tn u β' i` is the plan `𝒫₅(B, β', i)` on `ℕ × S_β` (all walks in copy `0`, the
written proof's copy `1`), with `K = I + 2` walks:

* entry `0`: datum `(0, 0, 0, +1)`; it stops at the first event at which its position is in `B`
  (deadline `0` if it already is), at closing, or at length `t_n`;
* entries `1, …, I`: the walks `W_1, …, W_I`, with the rules (1)-(7) of the walks W_i and the stopping times tau_i
  (these read only the records of these walks);
* entry `I + 1`: the backward walk `W_i^←`, datum `(0, p_i, β', -1)`, stopped at the first exit
  from `𝒬` (an event) or at length `4^{j-1}`.

`planA` is the plan `𝒫_𝒜` of the walks W_i and the stopping times tau_i with the `I` walks `W_1, …, W_I` only (offset `0`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The box escQ, the backward walks and zeta_i: the box `𝒬 = u + [2^{j-1}, 7·2^{j-3}] × [2^{j-2}, 3·2^{j-2}]^{d-1}`. -/
def escQ (j : ℕ) (u : EscV k) : Set (EscV k) :=
  {x | (u 0 + 2 ^ j / 2 ≤ x 0 ∧ x 0 ≤ u 0 + 7 * (2 ^ j / 8)) ∧
    ∀ c, c ≠ 0 → (u c + 2 ^ j / 4 ≤ x c ∧ x c ≤ u c + 3 * (2 ^ j / 4))}

/-- The walk data of the plan: walk `m` (`1 ≤ m ≤ I`) starts at `p_m`, the walk `I + 1` is the
backward walk from `p_i`. -/
def plan5Start (D : EscRP k) (i β' : ℕ) (m : ℕ) : CycData ℕ (k + 2) :=
  if m = 0 then (0, 0, 0, true)
  else if m ≤ D.I then (0, D.P m, (β' : ℝ), true)
  else (0, D.P i, (β' : ℝ), false)

open Classical in
/-- The decision of the first walk (entry `0`): the position is in `B`, or closing. -/
noncomputable def plan5St0 (β : ℝ) (j : ℕ) (u : EscV k) {m : ℕ}
    (ρ : CycRecN ℕ (k + 2) (m + 1)) : Bool :=
  closeSt β (ρ (Fin.last m)).2 || decide (entEnd (ρ (Fin.last m)) ∈ escBlock j u)

open Classical in
/-- The deadline of the first walk: `0` if the position is in `B`, else the closing deadline or
the length `t_n`. -/
noncomputable def plan5Dl0 (β tn : ℝ) (j : ℕ) (u : EscV k) {m : ℕ}
    (ρ : CycRecN ℕ (k + 2) (m + 1)) : ℝ≥0∞ :=
  if entEnd (ρ (Fin.last m)) ∈ escBlock j u then 0
  else min (closeDl β (ρ (Fin.last m)).2) (ENNReal.ofReal tn - (ρ (Fin.last m)).len)

open Classical in
/-- The decision of the backward walk: the position has left `𝒬`. -/
noncomputable def plan5StB (j : ℕ) (u : EscV k) {m : ℕ} (ρ : CycRecN ℕ (k + 2) (m + 1)) : Bool :=
  decide (entEnd (ρ (Fin.last m)) ∉ escQ j u)

/-- The deadline of the backward walk: the length `4^{j-1}`. -/
noncomputable def plan5DlB (j : ℕ) {m : ℕ} (ρ : CycRecN ℕ (k + 2) (m + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal ((4 : ℝ) ^ (j - 1)) - (ρ (Fin.last m)).len

/-- The connecting plan `𝒫₅(B, β', i)` of the connecting plan. -/
noncomputable def plan5 (n : ℕ) (β tn : ℝ) [Fact (0 < β)] (u : EscV k) (β' i : ℕ)
    (hlog : 1 < Real.log β) : CycPlan ℕ (k + 2) β where
  K := ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
  start m _ := plan5Start (escRP n β u 1) i β' m
  dl m ρ :=
    if m = 0 then plan5Dl0 β tn (escJ n) u ρ
    else if m ≤ escIstar n (escJ n) then (escRP n β u 1).escDl m ρ
    else if m = escIstar n (escJ n) + 1 then plan5DlB (escJ n) ρ
    else ⊤
  st m ρ :=
    if m = 0 then plan5St0 β (escJ n) u ρ
    else if m ≤ escIstar n (escJ n) then (escRP n β u 1).escSt m ρ
    else if m = escIstar n (escJ n) + 1 then plan5StB (escJ n) u ρ
    else false
  measurable_start m := by
    unfold plan5Start
    split_ifs <;> exact measurable_const
  measurable_dl m := by
    have hlen : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => (ρ (Fin.last m)).len :=
      measurable_entry_len'.comp (measurable_pi_apply _)
    have hend : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => entEnd (ρ (Fin.last m)) :=
      measurable_entEnd.comp (measurable_pi_apply _)
    by_cases h0 : m = 0
    · simp only [h0, ite_true]
      classical
      unfold plan5Dl0
      refine Measurable.ite ?_ measurable_const ?_
      · exact hend (Set.to_countable _).measurableSet
      · exact Measurable.min ((measurable_closeDl β).comp
          (measurable_snd.comp (measurable_pi_apply _))) (measurable_const.sub hlen)
    · simp only [h0, ite_false]
      by_cases h1 : m ≤ escIstar n (escJ n)
      · simp only [h1, ite_true]
        exact measurable_escDl _ hlog m
      · simp only [h1, ite_false]
        by_cases h2 : m = escIstar n (escJ n) + 1
        · simp only [h2, ite_true]
          exact measurable_const.sub hlen
        · simp only [h2, ite_false]
          exact measurable_const
  measurable_st m := by
    classical
    by_cases h0 : m = 0
    · simp only [h0, ite_true]
      unfold plan5St0
      have hc : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => closeSt β (ρ (Fin.last m)).2 :=
        (measurable_closeSt β).comp (measurable_snd.comp (measurable_pi_apply _))
      have hd : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) =>
          decide (entEnd (ρ (Fin.last m)) ∈ escBlock (escJ n) u) := by
        refine measurable_to_bool ?_
        have : (fun ρ : CycRecN ℕ (k + 2) (m + 1) =>
            decide (entEnd (ρ (Fin.last m)) ∈ escBlock (escJ n) u)) ⁻¹' {true} =
            (fun ρ : CycRecN ℕ (k + 2) (m + 1) => entEnd (ρ (Fin.last m))) ⁻¹'
              escBlock (escJ n) u := by
          ext ρ; simp
        rw [this]
        exact (measurable_entEnd.comp (measurable_last (k := k) (m := m)))
          (Set.to_countable _).measurableSet
      exact (measurable_of_finite (fun p : Bool × Bool => p.1 || p.2)).comp (hc.prodMk hd)
    · simp only [h0, ite_false]
      by_cases h1 : m ≤ escIstar n (escJ n)
      · simp only [h1, ite_true]
        exact measurable_escSt _ hlog m
      · simp only [h1, ite_false]
        by_cases h2 : m = escIstar n (escJ n) + 1
        · simp only [h2, ite_true]
          unfold plan5StB
          refine measurable_to_bool ?_
          have : (fun ρ : CycRecN ℕ (k + 2) (m + 1) =>
              decide (entEnd (ρ (Fin.last m)) ∉ escQ (escJ n) u)) ⁻¹' {true} =
              (fun ρ : CycRecN ℕ (k + 2) (m + 1) => entEnd (ρ (Fin.last m))) ⁻¹'
                (escQ (escJ n) u)ᶜ := by
            ext ρ; simp
          rw [this]
          exact (measurable_entEnd.comp (measurable_last (k := k) (m := m))) (Set.to_countable _).measurableSet
        · simp only [h2, ite_false]
          exact measurable_const

/-- The plan `𝒫_𝒜(B, β')` of the walks W_i and the stopping times tau_i: the `I` walks `W_1, …, W_I` with the rules
(1)-(7); walk `ℓ` is entry `ℓ - 1`. -/
noncomputable def planA (n : ℕ) (β : ℝ) [Fact (0 < β)] (u : EscV k) (β' : ℕ)
    (hlog : 1 < Real.log β) : CycPlan ℕ (k + 2) β where
  K := ((escIstar n (escJ n) : ℕ) : ℕ∞)
  start m _ := (0, escPoint n (escJ n) u (m + 1), (β' : ℝ), true)
  dl m ρ := (escRP n β u 0).escDl (m + 1) ρ
  st m ρ := (escRP n β u 0).escSt (m + 1) ρ
  measurable_start _ := measurable_const
  measurable_dl m := measurable_escDl _ hlog (m + 1)
  measurable_st m := measurable_escSt _ hlog (m + 1)

end ElboimSly.Paper.Escape
