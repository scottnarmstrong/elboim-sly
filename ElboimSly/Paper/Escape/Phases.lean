/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Escape.RelaxedClosed
public import ElboimSly.Foundations.Brownian.ESClaim56
public import Mathlib

/-!
# Phases, radii and events of Claim 5.6

Phases, radii and events of Claim 5.6.  Everything is pathwise: the path `y` plays the role of
`W_v = v + W`.  The radii `ρ_i`, endpoints `b_i` are those of `es56Rho`, `es56B`.

* `escPhaseM β t`: `m = ⌊log₄(t/√β)⌋`.
* `escPhaseA t m i`: `a_i`.  `escKappa m i`: `κ_i`.  `escR t m i`: `R_i = κ_i ρ_i`.
* `escZeta β y t m i`: `ζ_i`, the first relaxed time `≥ a_i` w.r.t. `y|[ζ_{i-1}, ·]`, or `b_i`.
* `EscB0`, `EscBi`, `EscBlast`: the events `ℬ₀`, `ℬ_i`, `ℬ_{2m+1}`; `EscG`: `G_i = ⋂_{i'≤i} ℬ_{i'}`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

/-- Cast of a lattice vector to `ℝ^d`. -/
def escCast (x : Fin (k + 2) → ℤ) : Fin (k + 2) → ℝ := fun c => (x c : ℝ)

/-- `m = ⌊log₄(t / √β)⌋` of phases, radii and events of Claim 5.6. -/
noncomputable def escPhaseM (β t : ℝ) : ℕ := ⌊Real.logb 4 (t / Real.sqrt β)⌋₊

/-- `a_i`: `4^{i-m} t / 2` for `i ≤ m`, `t - 4^{m-i} t / 2` for `i > m`. -/
noncomputable def escPhaseA (t : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then t / (2 * 4 ^ (m - i)) else t - t / (2 * 4 ^ (i - m))

/-- The curve `f` of phases, radii and events of Claim 5.6, for the block `u` at scale `j`. -/
noncomputable def escCurve (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) : ℝ → Fin (k + 2) → ℝ :=
  es56F t (escCast v) (escCast z) (escCentre j u)

/-- The factors `κ_i`: `1` for `i ≤ m-2`, `1/2` for `i = m-1`, `1/8` for `i ≥ m`. -/
noncomputable def escKappa (m i : ℕ) : ℝ :=
  if m ≤ i then 1 / 8 else if i + 1 = m then 1 / 2 else 1

/-- The walk radii `R_i = κ_i ρ_i`. -/
noncomputable def escR (t : ℝ) (m i : ℕ) : ℝ := escKappa m i * es56Rho t m i

/-- One step of the recursion for `ζ_i` given `ζ_{i-1} = prev`: the first `s ≥ a_i` relaxed with
respect to `y|[prev, s]`, or `b_i` if there is none before `b_i`. -/
noncomputable def escZetaStep (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (lo hi prev : ℝ) : ℝ :=
  open Classical in
  if ∃ s ∈ relaxedSet β y prev, lo ≤ s ∧ s < hi then sInf (relaxedSet β y prev ∩ Set.Ici lo) else hi

/-- The times `ζ_i` (`ζ_{-1} = 0`), for given lower and upper ends `lo i = a_i`, `hi i = b_i`. -/
noncomputable def escZetaAux (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (lo hi : ℕ → ℝ) : ℕ → ℝ
  | 0 => escZetaStep β y (lo 0) (hi 0) 0
  | i + 1 => escZetaStep β y (lo (i + 1)) (hi (i + 1)) (escZetaAux β y lo hi i)

/-- `ζ_i` of phases, radii and events of Claim 5.6. -/
noncomputable def escZeta (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (t : ℝ) (m i : ℕ) : ℝ :=
  escZetaAux β y (escPhaseA t m) (es56B t m) i

/-- `ζ_{i-1}` with the convention `ζ_{-1} = 0`. -/
noncomputable def escZetaPrev (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (t : ℝ) (m i : ℕ) : ℝ :=
  if i = 0 then 0 else escZeta β y t m (i - 1)

/-- `ℬ₀`. -/
def EscB0 (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) (y : ℝ → Fin (k + 2) → ℤ) : Prop :=
  let m := escPhaseM β t
  let ζ := escZeta β y t m 0
  ζ < es56B t m 0 ∧
  (∀ s, 0 ≤ s → s ≤ ζ → y s ∈ escBlockMinus j u ∧ ‖escCast (y s) - escCast v‖ ≤ β ^ (0.3 : ℝ)) ∧
  ‖escCast (y ζ) - escCurve j u v z t ζ‖ ≤ es56Rho t m 0

/-- `ℬ_i`, `1 ≤ i ≤ 2m`. -/
def EscBi (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (i : ℕ) :
    Prop :=
  let m := escPhaseM β t
  escZeta β y t m i < es56B t m i ∧
  (∀ s, escZeta β y t m (i - 1) ≤ s → s ≤ escZeta β y t m i →
    ‖escCast (y s) - escCurve j u v z t s‖ ≤ escR t m i) ∧
  ‖escCast (y (escZeta β y t m i)) - escCurve j u v z t (escZeta β y t m i)‖ ≤
    (24 / 100) * escR t m i

/-- `ℬ_{2m+1}`. -/
def EscBlast (β : ℝ) (j : ℕ) (u z : Fin (k + 2) → ℤ) (t : ℝ) (y : ℝ → Fin (k + 2) → ℤ) : Prop :=
  let m := escPhaseM β t
  (∀ s, escZeta β y t m (2 * m) ≤ s → s ≤ t →
    y s ∈ escBlockMinus j u ∧
      ‖escCast (y s) - escCast (y (escZeta β y t m (2 * m)))‖ ≤ β ^ (0.3 : ℝ)) ∧ y t = z

/-- `G_i = ⋂_{i' ≤ i} ℬ_{i'}` for `i ≤ 2m`. -/
def EscG (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) (y : ℝ → Fin (k + 2) → ℤ) (i : ℕ) :
    Prop :=
  EscB0 β j u v z t y ∧ ∀ i', 1 ≤ i' → i' ≤ i → EscBi β j u v z t y i'

end ElboimSly.Paper
