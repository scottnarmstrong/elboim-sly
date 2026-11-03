/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# The continuous-time simple random walk driven by a Poisson point process

Simple random walk.

The `2d` unit directions are `Dir d = Fin d × Bool` (coordinate and sign).  The intensity is
`clockIntensity (Dir d) = # ⊗ Leb|_{(0,∞)}` (`μ_d`).  Everything is stated for a single measure
`ν : Measure (Dir d × ℝ)` (a realisation of the point process): `goodSet d` is the good event `G`,
and `walk d ν t` is the canonical walk `X(t)`.  For a process `N`, `X ω t = walk d (N ω) t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- The `2d` unit directions `σ e_i`, encoded as (coordinate, sign). -/
abbrev Dir (d : ℕ) : Type := Fin d × Bool

/-- The unit vector of `Z^d` of a direction. -/
def Dir.vec {d : ℕ} (v : Dir d) : Fin d → ℤ := Pi.single v.1 (if v.2 then 1 else -1)

/-- The count `N_v(t) = ν({v} × (0,t])`. -/
def cnt {d : ℕ} (ν : Measure (Dir d × ℝ)) (v : Dir d) (t : ℝ) : ℝ≥0∞ :=
  ν ({v} ×ˢ Ioc 0 t)

/-- The total count `M(U) = ν(D × U)`. -/
def tot {d : ℕ} (ν : Measure (Dir d × ℝ)) (U : Set ℝ) : ℝ≥0∞ :=
  ν (univ ×ˢ U)

/-- The good event `G` of the written proof, as a set of measures on `Dir d × ℝ`. -/
def goodSet (d : ℕ) : Set (Measure (Dir d × ℝ)) :=
  (⋂ v : Dir d, ⋂ q : ℚ, ⋂ (_ : 0 < q), {ν | ∃ n : ℕ, cnt ν v q = n}) ∩
  ⋂ T : ℕ, ⋂ (_ : 1 ≤ T),
    ({ν | tot ν (Ioc 0 (T : ℝ)) < ∞} ∩
      ⋃ n : ℕ, ⋃ (_ : 1 ≤ n), ⋂ k : ℕ, ⋂ (_ : 1 ≤ k ∧ k ≤ n),
        {ν | tot ν (Ioc (((k : ℝ) - 1) * T / n) (k * T / n)) ≤ 1})

open Classical in
/-- The canonical simple random walk built from the realisation `ν`:
`X(t) = ∑_v v N_v(t)` on the good event and `0` off it. -/
noncomputable def walk (d : ℕ) (ν : Measure (Dir d × ℝ)) (t : ℝ) : Fin d → ℤ :=
  if ν ∈ goodSet d then ∑ v : Dir d, ((⌊(cnt ν v t).toReal⌋₊ : ℕ) : ℤ) • v.vec else 0

/-- The process `X ω t` built from a point process `N`. -/
noncomputable def srw {Ω : Type*} (d : ℕ) (N : Ω → Measure (Dir d × ℝ)) (ω : Ω) (t : ℝ) :
    Fin d → ℤ :=
  walk d (N ω) t

/-- The good event `G` as an event of `Ω`. -/
def goodEvent {Ω : Type*} (d : ℕ) (N : Ω → Measure (Dir d × ℝ)) : Set Ω :=
  N ⁻¹' goodSet d

end SRW
end ElboimSly
