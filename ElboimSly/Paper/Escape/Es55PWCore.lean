/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWGeom
public import ElboimSly.Paper.Escape.Plan5Entries
public import ElboimSly.Foundations.Cyclic.CycRingMeasure
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the deterministic core of the agreement

ES22 Lemma 5.5, Step 1, "Agreement on `E₅₆ ∩ E₀`".

For good environments `ν` (the true one) and `Ñ` (the fresh one, equal to `ν` off the explored
region `R`), and the fresh walk `P̃ = P^Ñ_{δ_c}` with `δ_c = (0, v, ξ, +1)`, which satisfies the
event `E₅₆` on `[0, t_*]`: the explored region of `P̃` before any `r < t_*` meets `R` in no atom of
`ν` or of `Ñ`.  The geometry of the record at `S₃` enters only through `PWReg`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

section core

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The event `E₅₆` on `[0, t_*]` for the walk `P̃` (real-time form). -/
structure PWPath (β : ℝ) (j : ℕ) (u : EscV k) (v w : EscV k) (tstar : ℝ)
    (Pt : CycPath (k + 2)) : Prop where
  mem : ∀ s : ℝ≥0, (s : ℝ) ≤ tstar → Pt.1.fn s ∈ escBlockMinus j u
  ne_v : ∀ s : ℝ≥0, β ≤ (s : ℝ) → (s : ℝ) ≤ tstar → Pt.1.fn s ≠ v
  ne_w : ∀ s : ℝ≥0, (s : ℝ) ≤ tstar - β → Pt.1.fn s ≠ w

/-- The geometry of the explored region `R` of the record at `S₃` as seen from `B⁻`:
every point has an endpoint outside `B⁻`, and the only atoms of `ν` in `R` on an edge through a
vertex of `B⁻` are the entrance atom `x_ent` and the exit atom `x_ex`. -/
structure PWReg (j : ℕ) (u : EscV k) (ν : Measure (CycS ℕ (k + 2) β)) (R : Set (CycS ℕ (k + 2) β))
    (v w : EscV k) (ξ : ℝ) (c : AddCircle β) : Prop where
  out : ∀ x ∈ R, ∃ q, Edge.Mem q x.2.1 ∧ q ∉ escBlockMinus j u
  atoms : ∀ x ∈ R, 1 ≤ ν {x} → ∀ z ∈ escBlockMinus j u, Edge.Mem z x.2.1 →
    (z = v ∧ x.2.2 = ((ξ : ℝ) : AddCircle β) ∧ ∃ a, a ∉ escBlock j u ∧ x.2.1.1 = s(a, v)) ∨
    (z = w ∧ x.2.2 = c)

theorem pw_left_mem {Pt : CycPath (k + 2)} {S : Set (EscV k)} {tstar : ℝ}
    (hS : ∀ s : ℝ≥0, (s : ℝ) ≤ tstar → Pt.1.fn s ∈ S) {r : ℝ≥0} (hr : 0 < r)
    (hrt : (r : ℝ) ≤ tstar) : Pt.1.left r ∈ S := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((Pt.1.eventually_left hr).and (self_mem_nhdsWithin (a := r)
    (s := Iio r))).exists
  rw [← hs]
  exact hS s (le_trans (by exact_mod_cast le_of_lt hsr) hrt)

theorem pw_left_eq_fn {Pt : CycPath (k + 2)} {r : ℝ≥0} (hr : 0 < r) :
    ∃ s : ℝ≥0, s < r ∧ Pt.1.fn s = Pt.1.left r := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((Pt.1.eventually_left hr).and (self_mem_nhdsWithin (a := r)
    (s := Iio r))).exists
  exact ⟨s, hsr, hs⟩

theorem pw_atom_zero_or_one {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν)
    (x : CycS ℕ (k + 2) β) : ν {x} = 0 ∨ ν {x} = 1 := by
  have hb := SepPartSeq.singleton_eq_zero_or_one (good_mem_bSimple (hν x.1)) x.2
  rw [cycSlice_singleton] at hb
  exact hb

theorem pw_circle_ge {a b : ℝ} (h : ((a : ℝ) : AddCircle β) = ((b : ℝ) : AddCircle β))
    (hab : b < a) : b + β ≤ a := by
  have hβ : 0 < β := Fact.out
  have hc : ((a - b : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp hc
  rw [zsmul_eq_mul] at hm
  have hpos : 0 < (m : ℝ) * β := by rw [hm]; linarith
  have hm0 : 0 < (m : ℝ) := by
    by_contra h0
    push Not at h0
    nlinarith
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  nlinarith

theorem pw_mem_region_cut {d : ℕ} (δ : CycData ℕ d) (p : CycPath d) (ℓ : ℝ≥0∞)
    (x : CycS ℕ d β) :
    x ∈ CycEntry.region β ((δ, p.cut ℓ) : CycEntry ℕ d) ↔
      ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ ℓ ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r ∧
        Edge.Mem (p.1.left r) x.2.1 := by
  constructor
  · rintro ⟨r, hr, hl, h1, h2, h3⟩
    have hl' : (r : ℝ≥0∞) ≤ ℓ := by
      have : CycEntry.len ((δ, p.cut ℓ) : CycEntry ℕ d) = ℓ := CPath.cut_len _ _
      rwa [this] at hl
    refine ⟨r, hr, hl', h1, h2, ?_⟩
    simp only [CycEntry.path, CycPath.cut] at h3
    rwa [CPath.left_cut _ _ hr hl'] at h3
  · rintro ⟨r, hr, hl, h1, h2, h3⟩
    have hl' : (r : ℝ≥0∞) ≤ CycEntry.len ((δ, p.cut ℓ) : CycEntry ℕ d) := by
      have : CycEntry.len ((δ, p.cut ℓ) : CycEntry ℕ d) = ℓ := CPath.cut_len _ _
      rwa [this]
    refine ⟨r, hr, hl', h1, h2, ?_⟩
    simp only [CycEntry.path, CycPath.cut]
    rwa [CPath.left_cut _ _ hr hl]

end core

end ElboimSly.Paper.Escape
