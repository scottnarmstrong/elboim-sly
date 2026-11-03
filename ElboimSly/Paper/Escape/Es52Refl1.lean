/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Escape.EscapeTime
public import ElboimSly.Foundations.Cyclic.CycMeancovSym
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: the reflection `h(x) = (-x₁, x₂, …)`

ES22 Proposition 5.2 proof, Step 2; lattice and time symmetries.

* `reflAut`: the lattice automorphism `h`, an involution fixing `0`;
* `reflU`: the corner `ũ = (-u₁ - 2^j + 1, u₂, …)` of `h(B)`;
* `h(B) = B̃`, `h(B⁺) = B̃⁻`, and `B̃` is admissible when `B` is and `u ≠ 0`;
* `envMap h (envMap h ν) = ν`, `CycGood (envMap h ν) ↔ CycGood ν`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The reflection `h(x) = (-x₁, x₂, …, x_d)` as a lattice automorphism. -/
def reflAut (k : ℕ) : LatticeAut (k + 2) := LatticeAut.reflect 0

theorem reflAut_apply (x : Fin (k + 2) → ℤ) (c : Fin (k + 2)) :
    (reflAut k).toEquiv x c = if c = 0 then -x c else x c := rfl

theorem reflAut_zero : (reflAut k).toEquiv 0 = 0 := by
  funext c; simp [reflAut_apply]

theorem reflAut_invol (x : Fin (k + 2) → ℤ) : (reflAut k).toEquiv ((reflAut k).toEquiv x) = x := by
  funext c; by_cases h : c = 0 <;> simp [reflAut_apply, h]

/-- The corner of the reflected block. -/
def reflU (j : ℕ) (u : Fin (k + 2) → ℤ) : Fin (k + 2) → ℤ :=
  fun c => if c = 0 then -u c - 2 ^ j + 1 else u c

theorem reflAut_mem_block {j : ℕ} {u x : Fin (k + 2) → ℤ} :
    (reflAut k).toEquiv x ∈ escBlock j (reflU j u) ↔ x ∈ escBlock j u := by
  unfold escBlock
  simp only [mem_ofPred_eq]
  refine forall_congr' fun c => ?_
  by_cases h : c = 0
  · subst h; simp only [reflAut_apply, reflU, ite_true]; constructor <;> rintro ⟨h1, h2⟩ <;>
      constructor <;> omega
  · simp [reflAut_apply, reflU, h]

theorem reflAut_mem_blockMinus {j : ℕ} (hj : 1 ≤ j) {u x : Fin (k + 2) → ℤ} :
    (reflAut k).toEquiv x ∈ escBlockMinus j (reflU j u) ↔ x ∈ escBlockPlus j u := by
  have h2 : (2 : ℤ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold escBlockMinus escBlockPlus escBlock
  simp only [mem_ofPred_eq, mem_sdiff]
  constructor
  · rintro ⟨⟨h1, h3⟩, h4⟩
    simp only [reflAut_apply, reflU, ite_true] at h1 h3
    have hb : ∀ c, u c ≤ x c ∧ x c < u c + 2 ^ j := by
      intro c
      by_cases hc : c = 0
      · subst hc; constructor <;> omega
      · have := h4 c hc
        simpa [reflAut_apply, reflU, hc] using this
    refine ⟨hb, ?_⟩
    rintro ⟨⟨m1, m2⟩, -⟩
    omega
  · rintro ⟨hb, hn⟩
    have h0 := hb 0
    have hge : u 0 + 2 ^ (j - 1) ≤ x 0 := by
      by_contra hlt
      exact hn ⟨⟨h0.1, by omega⟩, fun c _ => hb c⟩
    refine ⟨⟨?_, ?_⟩, fun c hc => ?_⟩
    · simp only [reflAut_apply, reflU, ite_true]; omega
    · simp only [reflAut_apply, reflU, ite_true]; omega
    · simpa [reflAut_apply, reflU, hc] using hb c

theorem reflAut_admissible {j : ℕ} {u : Fin (k + 2) → ℤ} (hadm : EscAdmissible j u)
    (hu : u ≠ 0) : EscAdmissible j (reflU j u) := by
  left
  intro h0
  have h1 : (0 : Fin (k + 2) → ℤ) ∈ escBlock j u := by
    have := (reflAut_mem_block (k := k) (j := j) (u := u) (x := 0)).1
    rw [reflAut_zero] at this
    exact this h0
  rcases hadm with h | h
  · exact h h1
  · exact hu h

theorem edgeEquiv_refl_invol (e : Edge (k + 2)) :
    edgeEquiv (reflAut k) (edgeEquiv (reflAut k) e) = e := by
  apply Subtype.ext
  show Sym2.map (reflAut k).toEquiv (Sym2.map (reflAut k).toEquiv e.1) = e.1
  rw [Sym2.map_map]
  have : ((reflAut k).toEquiv : (Fin (k + 2) → ℤ) → (Fin (k + 2) → ℤ)) ∘
      ((reflAut k).toEquiv : (Fin (k + 2) → ℤ) → (Fin (k + 2) → ℤ)) = id :=
    funext (reflAut_invol (k := k))
  rw [this]
  show Sym2.map (id : (Fin (k + 2) → ℤ) → _) e.1 = e.1
  exact congrFun Sym2.map_id e.1

omit [Fact (0 < β)] in
theorem envMap_envMap (ν : Measure (ℕ × RingSpace (k + 2) β)) :
    envMap (reflAut k) (envMap (reflAut k) ν) = ν := by
  unfold envMap
  rw [Measure.map_map (measurable_envMapFn _) (measurable_envMapFn _)]
  have : (Prod.map (id : ℕ → ℕ)
      (ringMapEquiv (edgeEquiv (reflAut k)) (MeasurableEquiv.refl (AddCircle β)))) ∘
      (Prod.map (id : ℕ → ℕ)
      (ringMapEquiv (edgeEquiv (reflAut k)) (MeasurableEquiv.refl (AddCircle β)))) = id := by
    funext ⟨a, e, θ⟩
    simp [Prod.map, ringMapEquiv_apply, edgeEquiv_refl_invol]
  rw [this, Measure.map_id]

omit [Fact (0 < β)] in
theorem cycGood_envMap_of {ν : Measure (ℕ × RingSpace (k + 2) β)} (hν : CycGood ν) :
    CycGood (envMap (reflAut k) ν) := fun ι => by
  rw [cycSlice_envMap]
  exact good_latticeMeasure _ (hν ι)

omit [Fact (0 < β)] in
theorem cycGood_envMap_iff {ν : Measure (ℕ × RingSpace (k + 2) β)} :
    CycGood (envMap (reflAut k) ν) ↔ CycGood ν := by
  refine ⟨fun h => ?_, cycGood_envMap_of⟩
  have := cycGood_envMap_of h
  rwa [envMap_envMap] at this

end ElboimSly.Paper.Escape
