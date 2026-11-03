/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Heavy.Taufast
public import ElboimSly.Foundations.Cyclic.CycPlan
public import ElboimSly.Foundations.Cyclic.CycClosingPlan
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# The stopping rules (1)-(7) of the walks W_i and the stopping times tau_i, as decisions and deadlines of a plan

The walks W_i and the stopping times tau_i; The connecting plan.

A rule reads the record `ρ` whose last entry is the current walk (at an event, or at the start),
and returns the decision at an event (`escSt`) and the deadline computed at the last event
(`escDl`).  The data are bundled in `EscRP`; the walk `ℓ` (1-based) is entry `ℓ - 1 + o`
of the record, where `o` is the offset (`o = 0` for the plan `𝒫_𝒜`, `o = 1` for `𝒫₅`, whose
first entry is walk 1 of the plan, going to the block).

* (1), (4), (5), (6) are decisions at events (deadline `0` if they already hold).
* (2) and (7) are deadlines; (2) is also tested at events.
* (3) is tested at events.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

/-- The vertex set `ℤ^d`, `d = k + 2`. -/
abbrev EscV (k : ℕ) : Type := Fin (k + 2) → ℤ

/-- The data of the stopping rules (1)-(7). -/
structure EscRP (k : ℕ) where
  /-- The scale `n`. -/
  n : ℕ
  /-- The scale `j`. -/
  j : ℕ
  /-- The regeneration scale `β`. -/
  β : ℝ
  /-- The number `I` of points. -/
  I : ℕ
  /-- The points `p_ℓ`. -/
  P : ℕ → EscV k
  /-- The half block `B⁻`. -/
  Bm : Set (EscV k)
  /-- The offset of walk `1` in the record. -/
  o : ℕ

/-- The data of the walks W_i and the stopping times tau_i for the block `u`. -/
def escRP (n : ℕ) (β : ℝ) (u : EscV k) (o : ℕ) : EscRP k where
  n := n
  j := escJ n
  β := β
  I := escIstar n (escJ n)
  P := escPoint n (escJ n) u
  Bm := escBlockMinus (escJ n) u
  o := o

/-- The position at the end of a world-line. -/
noncomputable def entEnd (e : CycEntry ℕ (k + 2)) : EscV k := e.path.fn e.len.toNNReal

/-- Time of the current walk, `t = ς`. -/
noncomputable def escTm (e : CycEntry ℕ (k + 2)) : ℝ := e.len.toReal

/-- Condition (1): `W(t) = 0`. -/
def escC1 (e : CycEntry ℕ (k + 2)) : Prop := entEnd e = 0

/-- Condition (5), for the world-lines `e'` of the earlier walks:
`‖W(t) - W_{ℓ'}(s)‖ ≤ 1` for some `s ≤ τ_{ℓ'}`. -/
def escC5 (e : CycEntry ℕ (k + 2)) (e' : CycEntry ℕ (k + 2)) : Prop :=
  ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ e'.len ∧ ‖entEnd e - e'.path.fn s‖ ≤ 1

/-- The first time `t ≥ M` (real) with `‖w - p‖ ≤ 2 √t / ln t`, as an element of `[0, ∞]`. -/
noncomputable def escT2 (p w : EscV k) (M : ℝ) : ℝ≥0∞ :=
  sInf {t : ℝ≥0∞ | ∃ r : ℝ, t = ENNReal.ofReal r ∧ M ≤ r ∧ ‖w - p‖ ≤ 2 * Real.sqrt r / Real.log r}

namespace EscRP

variable (D : EscRP k)

/-- The record index of walk number `ℓ`. -/
def idx (ℓ : ℕ) : ℕ := ℓ - 1 + D.o

/-- Condition (2): `t ≥ ln β` and `‖W(t) - p_ℓ‖ ≤ 2 √t / ln t`. -/
def C2 (ℓ : ℕ) (e : CycEntry ℕ (k + 2)) : Prop :=
  Real.log D.β ≤ escTm e ∧ ‖entEnd e - D.P ℓ‖ ≤ 2 * Real.sqrt (escTm e) / Real.log (escTm e)

/-- Condition (3): `τ_fast(ln² max(t, ln β)) ≤ t`, for the path of the world-line (translated to
start at `0`). -/
def C3 (e : CycEntry ℕ (k + 2)) : Prop :=
  pathTfast (fun t : ℝ => e.path.fn t.toNNReal - e.path.fn 0)
    (Real.log (max (escTm e) (Real.log D.β)) ^ 2) ≤ ENNReal.ofReal (escTm e)

/-- Condition (4): `‖W(t) - p_{ℓ'}‖ ≤ n^17/6` for some `ℓ' ≤ I`, `ℓ' ≠ ℓ`. -/
def C4 (ℓ : ℕ) (e : CycEntry ℕ (k + 2)) : Prop :=
  ∃ ℓ', 1 ≤ ℓ' ∧ ℓ' ≤ D.I ∧ ℓ' ≠ ℓ ∧ ‖entEnd e - D.P ℓ'‖ ≤ (D.n : ℝ) ^ 17 / 6

/-- Condition (6): `d(W(t), B⁻) ≤ 2^j/8`. -/
def C6 (e : CycEntry ℕ (k + 2)) : Prop :=
  Metric.infDist (fun c => ((entEnd e c : ℤ) : ℝ)) ((fun x c => ((x c : ℤ) : ℝ)) '' D.Bm) ≤
    (2 : ℝ) ^ D.j / 8

/-- Condition (7): `t = 4^n`. -/
def C7 (e : CycEntry ℕ (k + 2)) : Prop := escTm e = 4 ^ D.n

/-- The earlier walks of the family: entries `idx 1, …, idx (ℓ - 1)` of the record. -/
def Cvisit {m : ℕ} (ℓ : ℕ) (ρ : CycRecN ℕ (k + 2) (m + 1)) : Prop :=
  ∃ ℓ' : ℕ, 1 ≤ ℓ' ∧ ℓ' < ℓ ∧ ∃ h : D.idx ℓ' < m + 1, escC5 (ρ (Fin.last m)) (ρ ⟨D.idx ℓ', h⟩)

/-- The conditions (1), (4), (5), (6): they concern the current position only. -/
def Cpos {m : ℕ} (ℓ : ℕ) (ρ : CycRecN ℕ (k + 2) (m + 1)) : Prop :=
  escC1 (ρ (Fin.last m)) ∨ D.C4 ℓ (ρ (Fin.last m)) ∨ D.Cvisit ℓ ρ ∨ D.C6 (ρ (Fin.last m))

/-- Some of (1)-(7) holds at the current time. -/
def Cany {m : ℕ} (ℓ : ℕ) (ρ : CycRecN ℕ (k + 2) (m + 1)) : Prop :=
  D.Cpos ℓ ρ ∨ D.C2 ℓ (ρ (Fin.last m)) ∨ D.C3 (ρ (Fin.last m)) ∨ D.C7 (ρ (Fin.last m))

open Classical in
/-- The decision of the rule for the walk number `ℓ` at an event. -/
noncomputable def escSt {m : ℕ} (ℓ : ℕ) (ρ : CycRecN ℕ (k + 2) (m + 1)) : Bool :=
  decide (D.Cany ℓ ρ)

open Classical in
/-- The deadline of the rule for the walk number `ℓ`. -/
noncomputable def escDl {m : ℕ} (ℓ : ℕ) (ρ : CycRecN ℕ (k + 2) (m + 1)) : ℝ≥0∞ :=
  if D.Cany ℓ ρ then 0 else
    min (escT2 (D.P ℓ) (entEnd (ρ (Fin.last m))) (max (escTm (ρ (Fin.last m))) (Real.log D.β)) -
        (ρ (Fin.last m)).len)
      (ENNReal.ofReal ((4 : ℝ) ^ D.n) - (ρ (Fin.last m)).len)

end EscRP

end ElboimSly.Paper.Escape
