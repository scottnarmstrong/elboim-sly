/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Setting
public import ElboimSly.Paper.Avoid.Resample
public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Escape.Gamma
public import Mathlib

/-!
# First entrance times and the escape stopping time

First entrance times and the escape stopping time.  All objects are defined in the setting of standing assumptions and the setting of S4--S5
(`Paper/Avoid/Setting`), in the dimension `d = k + 2`:

* `escWalk ν`: the regenerated walk of an environment `ν`.
* `escXi W B'`: the first entrance time `ξ_{B'}` of a path into `B'`.
* `escY`: `Y_{B'} = 1_{{ξ ≤ t_n} ∩ ℰ(ξ)}` as a function of the environment `ν`.
* `escT`: `T_{B'} = ξ_{B'} ∧ t_n`, as a time `Ω → WithTop ℝ≥0`.
* `escPi`: `π_{B'} = Φ_{Y_{B'}}(ρ_{T_{B'}})`, the canonical version of
  `P(ℰ(ξ_{B'}) ∩ {ξ_{B'} ≤ t_n} | 𝓕_{T_{B'}})` (via the resampling formula).
* `escBlocks j`: the family `𝓑_j` of blocks with corner in `2^j ℤ^d`.
* `escTauEsc`: `τ_esc = inf{ξ_{B'} : B' ∈ 𝓑_j, ξ_{B'} ≤ t_n, π_{B'} ≤ n^{-γ}}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk `W` of an environment `ν` on `ℕ × S_β` (construction (i)). -/
noncomputable def escWalk (ν : Measure (CycS ℕ (k + 2) β)) : ℝ → Fin (k + 2) → ℤ :=
  ElboimSly.regenWalk fun i => ElboimSly.copyEnv ν i

/-- First entrance times and the escape stopping time: the first entrance time `ξ_{B'} = inf{t ≥ 0 : W(t) ∈ B'}`,
`inf ∅ = ∞`. -/
noncomputable def escXi (W : ℝ → Fin (k + 2) → ℤ) (B : Set (Fin (k + 2) → ℤ)) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : W t ∈ B), (t : ℝ≥0∞)

open Classical in
/-- First entrance times and the escape stopping time: `Y_{B'} = 1({ξ_{B'} ≤ t_n} ∩ ℰ(ξ_{B'}))`, a function of the
environment. -/
noncomputable def escY (n j : ℕ) (tn : ℝ) (B : Set (Fin (k + 2) → ℤ))
    (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0∞ :=
  if escXi (escWalk ν) B ≤ ENNReal.ofReal tn ∧
      EscEvent n j (escWalk ν) (escXi (escWalk ν) B).toReal then 1 else 0

/-- First entrance times and the escape stopping time: `T_{B'} = ξ_{B'} ∧ t_n`. -/
noncomputable def escT {Ω : Type*} (N : Ω → Measure (CycS ℕ (k + 2) β)) (tn : ℝ)
    (B : Set (Fin (k + 2) → ℤ)) (ω : Ω) : WithTop ℝ≥0 :=
  ((min (escXi (escWalk (N ω)) B) (ENNReal.ofReal tn)).toNNReal : ℝ≥0)

/-- First entrance times and the escape stopping time: `π_{B'} = Φ_{Y_{B'}}(ρ_{T_{B'}})`. -/
noncomputable def escPi {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (n j : ℕ) (tn : ℝ) (B : Set (Fin (k + 2) → ℤ))
    (ω : Ω) : ℝ≥0∞ :=
  resampleInt (regPlan (k + 2) β) Pr N (escT N tn B)
    (fun p => escY n j tn B p.2) ω

/-- Blocks with arbitrary corner, halves, admissibility; Lattice, norms, edges, boxes, blocks: the blocks `𝓑_j`, with corner in `2^j ℤ^d`. -/
def escBlocks (k j : ℕ) : Set (Set (Fin (k + 2) → ℤ)) :=
  {B | ∃ u : Fin (k + 2) → ℤ, (∀ c, (2 : ℤ) ^ j ∣ u c) ∧ B = escBlock j u}

open Classical in
/-- First entrance times and the escape stopping time: the escape stopping time
`τ_esc = inf{ξ_{B'} : B' ∈ 𝓑_j, ξ_{B'} ≤ t_n, π_{B'} ≤ n^{-γ}}`, with `inf ∅ = ∞`. -/
noncomputable def escTauEsc {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (n j : ℕ) (tn γ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (B : Set (Fin (k + 2) → ℤ)) (_ : B ∈ escBlocks k j)
    (_ : escXi (escWalk (N ω)) B ≤ ENNReal.ofReal tn ∧
      escPi Pr N n j tn B ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-γ))),
    escXi (escWalk (N ω)) B

end ElboimSly.Paper
