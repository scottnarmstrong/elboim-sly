/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.SRW.SrwLaw
import Mathlib

/-!
# The driven construction: definitions

Driving walk; Walk driven by X; Coincidence-free driving paths.

Times are `ℝ≥0`, positions are `Fin d → ℤ`, and `β : ℝ≥0` is the (positive) cycle length.

* `IsDrivingPath x` is the driving path of walk driven by X.
* The driven walk `w^x` is defined jump by jump: `drivenTimes β x` enumerates the event set
  `E(x) = {s + kβ : s a jump time of x, k ≥ 0}` in increasing order (`⊤` once exhausted), and
  `drivenStage β x n` is the walk after the first `n` events, with the value at each new event
  given by `drivenRuleVal` (rules (D1)--(D3)).  `drivenWalk β x` is the limit of the stages.
* `drivenTreg β x` is the closing time `treg^x`.
* `CycCF β` is the coincidence-free set `cycCF` of coincidence-free driving paths.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The left value `f(s-) := lim_{u ↑ s} f(u)` (junk if the limit does not exist or `s = 0`). -/
noncomputable def leftVal (f : ℝ≥0 → Fin d → ℤ) (s : ℝ≥0) : Fin d → ℤ :=
  limUnder (𝓝[<] s) f

/-- A vector of `ℓ¹`-size `1`. -/
def IsUnitStep (v : Fin d → ℤ) : Prop := ∑ i, |v i| = 1

/-- A right-continuous path with finitely many jumps on bounded intervals. -/
structure IsRegPath (f : ℝ≥0 → Fin d → ℤ) : Prop where
  rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s
  fin : ∀ T : ℝ≥0, (CDisc f ∩ Iic T).Finite

/-- A driving path (walk driven by X): right-continuous, finitely many jumps on bounded intervals,
`x(0) = 0`, all jumps of `ℓ¹`-size `1`. -/
structure IsDrivingPath (x : ℝ≥0 → Fin d → ℤ) : Prop extends IsRegPath x where
  zero : x 0 = 0
  unit : ∀ s ∈ CDisc x, IsUnitStep (x s - leftVal x s)

section Rules

variable (β : ℝ≥0)

/-- `k ∈ H_t`: `k ≥ 1` and `t - kβ ≥ 0`. -/
def IsDelayIdx (t : ℝ≥0) (k : ℕ) : Prop := 1 ≤ k ∧ (k : ℝ≥0) * β ≤ t

/-- The hypothesis of rule (D1): `w` jumps at `t - kβ` and `w(t - kβ) = w(t-)`. -/
def ForcedAt (p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) (k : ℕ) : Prop :=
  IsDelayIdx β t k ∧ t - k * β ∈ CDisc p ∧ p (t - k * β) = leftVal p t

/-- The size-`1` condition of rule (D2): `w(t-) + Δx(t) ≠ w(t - kβ)` for all `k ∈ H_t`. -/
def TakenAt (x p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Prop :=
  ∀ k, IsDelayIdx β t k → leftVal p t + (x t - leftVal x t) ≠ p (t - k * β)

/-- (D1) (forced): if some `k ∈ H_t` has `w` jumping at `t - kβ` with `w(t - kβ) = w(t-)`, then
`w(t) = w((t - kβ)-)` for the least such `k`. -/
def DrivenD1 (p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Prop :=
  ∀ k, ForcedAt β p t k → (∀ k' < k, ¬ ForcedAt β p t k') → p t = leftVal p (t - k * β)

open Classical in
/-- (D2) (taken or suppressed). -/
def DrivenD2 (x p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Prop :=
  (∀ k, ¬ ForcedAt β p t k) → t ∈ CDisc x →
    p t = if TakenAt β x p t then leftVal p t + (x t - leftVal x t) else leftVal p t

/-- (D3): otherwise `w(t) = w(t-)`. -/
def DrivenD3 (x p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Prop :=
  (∀ k, ¬ ForcedAt β p t k) → t ∉ CDisc x → p t = leftVal p t

open Classical in
/-- The value prescribed by (D1)--(D3) at `t` from the past of `p` and the driver `x`. -/
noncomputable def drivenRuleVal (x p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Fin d → ℤ :=
  if ∃ k, ForcedAt β p t k then leftVal p (t - sInf {k | ForcedAt β p t k} * β)
  else if t ∈ CDisc x then
    (if TakenAt β x p t then leftVal p t + (x t - leftVal x t) else leftVal p t)
  else leftVal p t

/-- The event set `E(x) = {s + kβ : s a jump time of x, k ≥ 0}`. -/
def drivenEvents (x : ℝ≥0 → Fin d → ℤ) : Set ℝ≥0 :=
  {t | ∃ s ∈ CDisc x, ∃ k : ℕ, t = s + k * β}

/-- The first event strictly after `r`. -/
noncomputable def nextEvent (x : ℝ≥0 → Fin d → ℤ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {e | ∃ t ∈ drivenEvents β x, (t : ℝ≥0∞) = e ∧ r < e}

/-- The enumeration `0 = e_0 < e_1 < e_2 < ⋯` of `{0} ∪ E(x)` (`⊤` once exhausted). -/
noncomputable def drivenTimes (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => nextEvent β x (drivenTimes x n)

/-- The walk after the first `n` events. -/
noncomputable def drivenStage (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0 → Fin d → ℤ
  | 0 => fun _ => 0
  | n + 1 => fun s =>
    if (s : ℝ≥0∞) < drivenTimes β x (n + 1) then drivenStage x n s
    else drivenRuleVal β x (drivenStage x n) (drivenTimes β x (n + 1)).toNNReal

open Classical in
/-- Walk driven by X: the walk `w^x` driven by `x`, defined by the recursion (D1)--(D3) over the
events of `x`.  It is defined on all of `[0, ∞)`; the written proof stops it at `treg^x`. -/
noncomputable def drivenWalk (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Fin d → ℤ :=
  if h : ∃ n, (t : ℝ≥0∞) < drivenTimes β x (n + 1) then drivenStage β x (Nat.find h) t else 0

/-- The closing time `inf {kβ : k ≥ 1, p(kβ) = 0}` of a path `p` (`⊤` if there is none). -/
noncomputable def pathTreg (p : ℝ≥0 → Fin d → ℤ) : ℝ≥0∞ :=
  ⨅ k : {k : ℕ // 1 ≤ k ∧ p ((k : ℝ≥0) * β) = 0}, (((k.1 : ℝ≥0) * β : ℝ≥0) : ℝ≥0∞)

/-- Walk driven by X: the closing time `treg^x = inf {kβ : k ≥ 1, w^x(kβ) = 0}`. -/
noncomputable def drivenTreg (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0∞ :=
  pathTreg β (drivenWalk β x)

/-- The stopped value `w^x(t ∧ treg^x)`. -/
noncomputable def drivenStopped (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : Fin d → ℤ :=
  drivenWalk β x (min (t : ℝ≥0∞) (drivenTreg β x)).toNNReal

/-- Coincidence-free driving paths: the coincidence-free driving paths: (i) no two jump times of `x` differ by an
element of `β ℤ_{≥1}`, and (ii) `x` does not jump at any time in `β ℤ_{≥1}`. -/
def CycCF : Set (ℝ≥0 → Fin d → ℤ) :=
  {x | IsDrivingPath x ∧ (∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β) ∧
    ∀ k : ℕ, 1 ≤ k → (k : ℝ≥0) * β ∉ CDisc x}

end Rules

end ElboimSly.Cyclic

end
