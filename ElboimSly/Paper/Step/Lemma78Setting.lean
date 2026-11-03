/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStoppingApp
public import ElboimSly.Paper.Step.ThitStopping
public import ElboimSly.Paper.Step.LocIco

/-!
# The stopping times of Lemma 7.8 (path level)

Setting of Lemma 7.8 (ES22 §7), the stopping-time part. For the second walk
`W₂` (a path `ℝ≥0 → Ω → ℤ^d`), the set `V = W₁([0,t'_n])` and the data `Step78Data`, we define
`ζ_i`, `ζ''_i`, `ζ'_i` as `WithTop ℝ≥0`-valued functions on the sample space:
`ζ_0 = ζ'_0 = 0`, `ζ_{i+1} = t'_n ∧ inf{r ≥ ζ'_i : r ∈ 𝒯₂, d(W₂(r), V) ≥ ρ_k}`,
`ζ''_{i+1} = thit^{(2)}(ζ_{i+1}) ∧ treg^{(2)} ∧ inf{r ≥ ζ_{i+1} : d(W₂ r, V) ≤ 1} ∧
inf{r ≥ ζ_{i+1} + 3.89^n : d(W₂ r, V) ≤ 1.9^n}` and `ζ'_{i+1} = t'_n ∧ ζ''_{i+1}`.

The distance conditions `d(x, V) ≥ ρ` and `d(x, V) ≤ r` are written as `∀ v ∈ V, ρ ≤ ‖x - v‖`
and `∃ v ∈ V, ‖x - v‖ ≤ r` (equivalent for finite `V`, which is the case in the source).
`𝒯₂` is the set of relaxed times with `α ≡ 0`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- Data of Lemma 7.8 at the level of paths: the second walk, the set `V`, and the parameters. -/
structure Step78Data (d : ℕ) (Ω : Type*) where
  /-- the cyclic period `β` -/
  β : ℝ
  /-- the time `t'_n` -/
  T : ℝ≥0
  /-- the level `n` -/
  n : ℕ
  /-- the far radius `ρ_k` -/
  ρ : ℝ
  /-- the displacement `u` (`W₂(mβ) = u` is a closing of `w₂`) -/
  u : Fin d → ℤ
  /-- the second walk -/
  w : ℝ≥0 → Ω → Fin d → ℤ
  /-- the set `V = W₁([0, t'_n])` -/
  V : Ω → Set (Fin d → ℤ)

variable {d : ℕ} {Ω : Type*}

/-- `inf {r ≥ R : r ∈ U}` (`⊤` if there is none). -/
noncomputable def step78FirstGe (U : Ω → Set ℝ) (R : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ (r : ℝ≥0) (_ : (r : ℝ) ∈ U ω ∧ R ω ≤ r), (r : WithTop ℝ≥0)

namespace Step78Data

variable (D : Step78Data d Ω)

/-- The path of `W₂` on `ℝ` for the sample point `ω`. -/
noncomputable def path (ω : Ω) : ℝ → Fin d → ℤ := stepExt fun s => D.w s ω

/-- The relaxed times `𝒯₂` (with `α ≡ 0`). -/
def relaxed (ω : Ω) : Set ℝ := stepRelaxedSetOf D.β D.w (fun _ _ => 0) ω

/-- `{r ∈ 𝒯₂ : d(W₂(r), V) ≥ ρ}`. -/
def farSet (ω : Ω) : Set ℝ :=
  {r | r ∈ D.relaxed ω ∧ ∀ v ∈ D.V ω, D.ρ ≤ ‖D.path ω r - v‖}

/-- `{r : d(W₂(r), V) ≤ 1}`. -/
def nearSet1 (ω : Ω) : Set ℝ := {r | ∃ v ∈ D.V ω, ‖D.path ω r - v‖ ≤ 1}

/-- `{r : d(W₂(r), V) ≤ 1.9^n}`. -/
def nearSet2 (ω : Ω) : Set ℝ := {r | ∃ v ∈ D.V ω, ‖D.path ω r - v‖ ≤ (19 / 10 : ℝ) ^ D.n}

/-- The gap `3.89^n`. -/
noncomputable def gap : ℝ≥0 := ((389 / 100 : ℝ) ^ D.n).toNNReal

/-- `treg^{(2)}`: the first `mβ`, `m ≥ 1`, with `W₂(mβ) = u`. -/
noncomputable def treg (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (m : ℕ) (_ : 1 ≤ m ∧ D.w ((m : ℝ) * D.β).toNNReal ω = D.u),
    (((m : ℝ) * D.β).toNNReal : WithTop ℝ≥0)

/-- `thit^{(2)}(R)` (with `α ≡ 0`), as a `WithTop ℝ≥0`-valued function. -/
noncomputable def thit (R : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  (stepThitStop D.β D.w (fun _ _ => 0) R ω : WithTop ℝ≥0)

/-- `ζ_{i+1}` as a function of `ζ'_i`. -/
noncomputable def nextZeta (R : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (D.T : WithTop ℝ≥0) (step78FirstGe D.farSet R ω)

/-- `ζ''` as a function of `ζ`. -/
noncomputable def zetaPP (Z : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (min (D.thit Z ω) (D.treg ω))
    (min (step78FirstGe D.nearSet1 Z ω) (step78FirstGe D.nearSet2 (fun ω => Z ω + (D.gap : WithTop ℝ≥0)) ω))

/-- `ζ'` as a function of `ζ`: `t'_n ∧ ζ''`, but not below `ζ` (on `{ζ < t'_n}` the maximum with
`ζ` changes nothing, and on `{ζ = t'_n}` it gives `t'_n`; the source's `t'_n ∧ ζ''` differs only
on `{treg^{(2)} < t'_n}`, which is disjoint from `Ω`). -/
noncomputable def zetaP' (Z : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  max (Z ω) (min (D.T : WithTop ℝ≥0) (D.zetaPP Z ω))

/-- The sequence `ζ'_i`, `ζ'_0 = 0`. -/
noncomputable def zp : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => 0
  | i + 1 => D.zetaP' (D.nextZeta (zp i))

/-- The sequence `ζ_i`, with `ζ_0 = 0` (not in the source). -/
noncomputable def zeta : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => 0
  | i + 1 => D.nextZeta (D.zp i)

end Step78Data

end ElboimSly.Paper.Step

end
