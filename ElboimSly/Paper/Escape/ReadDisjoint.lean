/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5
public import ElboimSly.Foundations.Cyclic.CycSchemeEquiv
public import ElboimSly.Foundations.Cyclic.CycRegion
public import ElboimSly.Foundations.Cyclic.CycPathType
public import Mathlib

/-!
# The backward walk reads no point of the explored region: the geometric argument

ES22 Claim 5.7 ("It remains to see that `P̃` reads no point of `R_{S₂}` during
`(0, r_i(P̃)]`", parts (a) and (b)) and the box escQ, the backward walks and zeta_i.

* `region_overlap`: two world-lines whose regions meet have times `r₁, r₂ > 0` (within their
  lengths) with equal clocks and left limits at distance `≤ 1`.
* `clock_bwd_fwd`: for a backward walk at phase `β'` and a forward walk at phase `β'` the clocks
  agree only if `r₁ + r₂ ∈ βℤ`, hence `r₁ + r₂ ≥ β`.
* `escQ_nbhd_block`: every vertex within `ℓ^∞`-distance `1` of the box `𝒬` lies in the block `B`.
* `read_disjoint`: the geometric argument itself.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

section overlap

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- If a point lies in the regions of two world-lines, the world-lines have times `r₁, r₂ > 0` at
which the clocks agree and the left limits are within `1` (they lie on a common edge). -/
theorem region_overlap {e₁ e₂ : CycEntry ℕ (k + 2)} {x : CycS ℕ (k + 2) β}
    (h₁ : x ∈ e₁.region β) (h₂ : x ∈ e₂.region β) :
    ∃ r₁ r₂ : ℝ≥0, 0 < r₁ ∧ (r₁ : ℝ≥0∞) ≤ e₁.len ∧ 0 < r₂ ∧ (r₂ : ℝ≥0∞) ≤ e₂.len ∧
      e₁.data.clock β r₁ = e₂.data.clock β r₂ ∧ ‖e₁.path.left r₁ - e₂.path.left r₂‖ ≤ 1 := by
  obtain ⟨r₁, hr₁, hl₁, -, hc₁, hm₁⟩ := h₁
  obtain ⟨r₂, hr₂, hl₂, -, hc₂, hm₂⟩ := h₂
  exact ⟨r₁, r₂, hr₁, hl₁, hr₂, hl₂, hc₁.symm.trans hc₂, norm_le_one_of_mem_edge hm₁ hm₂⟩

/-- A backward walk and a forward walk at the same phase have equal clocks at times `r₁, r₂ > 0`
only if `β ≤ r₁ + r₂`. -/
theorem clock_bwd_fwd {β' : ℝ} {c c' : ℕ} {a b : Fin (k + 2) → ℤ} {r₁ r₂ : ℝ≥0}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : (CycData.clock β ((c, a, β', false) : CycData ℕ (k + 2)) r₁) =
      CycData.clock β ((c', b, β', true) : CycData ℕ (k + 2)) r₂) :
    β ≤ (r₁ : ℝ) + r₂ := by
  have hβ : 0 < β := Fact.out
  unfold CycData.clock CycData.sgn CycData.phase CycData.fwd at h
  simp only [Bool.false_eq_true, ite_false, ite_true] at h
  have hcirc : ((β' + -1 * (r₁ : ℝ) - (β' + 1 * (r₂ : ℝ)) : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp hcirc
  have hr : 0 < (r₁ : ℝ) + r₂ := by
    have := (NNReal.coe_pos.2 h₁); positivity
  have h3 : (m : ℝ) * β = -((r₁ : ℝ) + r₂) := by
    have h4 := hm
    rw [zsmul_eq_mul] at h4
    rw [h4]; ring
  have hm0 : m < 0 := by
    by_contra hm0
    push Not at hm0
    have : (0 : ℝ) ≤ (m : ℝ) * β := mul_nonneg (by exact_mod_cast hm0) hβ.le
    linarith
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  nlinarith

end overlap

section box

variable {k : ℕ}

/-- Every vertex within distance `1` of the box `𝒬` lies in the block `B`, once `16 ≤ 2^j`. -/
theorem escQ_nbhd_block {j : ℕ} (hj : 4 ≤ j) {u y z : EscV k} (hy : y ∈ escQ j u)
    (hz : ‖z - y‖ ≤ 1) : z ∈ escBlock j u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 4 := ⟨j - 4, by omega⟩
  have hp : (2 : ℤ) ^ (m + 4) = 16 * 2 ^ m := by ring
  have hm : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  intro c
  have hzc : |z c - y c| ≤ 1 := by
    have := norm_le_pi_norm (z - y) c
    simp only [Pi.sub_apply, Int.norm_eq_abs] at this
    have h2 : |((z c - y c : ℤ) : ℝ)| ≤ 1 := this.trans hz
    have h3 : ((|z c - y c| : ℤ) : ℝ) ≤ 1 := by rw [Int.cast_abs]; exact h2
    exact_mod_cast h3
  rw [abs_le] at hzc
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  rw [hp] at *
  generalize (2 : ℤ) ^ m = X at *
  by_cases hc : c = 0
  · subst hc
    constructor <;> omega
  · obtain ⟨hy4, hy5⟩ := hy3 c hc
    constructor <;> omega

end box

section read

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The values of the path of a world-line at times up to its length (the values after each of its
jumps up to the length). -/
def entVisited (e : CycEntry ℕ (k + 2)) : Set (EscV k) :=
  {y | ∃ a : ℕ, e.path.jt a ≤ e.len ∧ e.path.jv a = y}

/-- The set `A₇` of ES22 Claim 5.7: points at distance `≥ L` from `p` that are within `1` of a
vertex visited by one of the walks `1, …, I`. -/
def avoidSet (p : EscV k) (L : ℝ) (E : ℕ → CycEntry ℕ (k + 2)) (I : ℕ) : Set (EscV k) :=
  {y | L ≤ ‖y - p‖ ∧ ∃ m, 1 ≤ m ∧ m ≤ I ∧ ∃ v ∈ entVisited (E m), ‖y - v‖ ≤ 1}

theorem left_mem_entVisited (e : CycEntry ℕ (k + 2)) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ e.len) : e.path.left r ∈ entVisited e := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((e.path.eventually_left hr).and (self_mem_nhdsWithin (a := r)
    (s := Iio r))).exists
  have hsl : (s : ℝ≥0∞) ≤ e.len := (ENNReal.coe_le_coe.2 (le_of_lt hsr)).trans hl
  refine ⟨e.path.cnt s, ?_, ?_⟩
  · exact ((e.path.jt_le_iff _ s).2 le_rfl).trans hsl
  · rw [← hs, CPath.fn_eq_jv]

/-- **The geometric argument of ES22 Claim 5.7.** -/
theorem read_disjoint {j : ℕ} (hj : 4 ≤ j) {u : EscV k} {I i : ℕ} (hi : 1 ≤ i ∧ i ≤ I)
    (E : ℕ → CycEntry ℕ (k + 2)) (p : ℕ → EscV k) (β' : ℝ) (n : ℕ) (L7 t7 : ℝ)
    (hE0 : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) ≤ (E 0).len → (E 0).path.left r ∉ escBlock j u)
    (hEdata : ∀ m, 1 ≤ m → m ≤ I → (E m).data = (((0 : ℕ), p m, β', true) : CycData ℕ (k + 2)))
    (HV : ∀ R : ℝ, max (Real.log β) 10 ≤ R → ∀ r'' : ℝ≥0, 0 < r'' → (r'' : ℝ≥0∞) ≤ (E i).len →
      ‖(E i).path.left r'' - p i‖ ≤ R → (r'' : ℝ) ≤ 4 * R ^ 2 * Real.log R ^ 2)
    (HD : ∀ m, 1 ≤ m → m ≤ I → m ≠ i → ∀ r'' : ℝ≥0, 0 < r'' → (r'' : ℝ≥0∞) ≤ (E m).len →
      (n : ℝ) ^ 17 / 6 - 2 < ‖(E m).path.left r'' - p i‖)
    (q : CycPath (k + 2)) (r : ℝ≥0)
    (hQ : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r → q.1.left r' ∈ escQ j u)
    (hav : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r → q.1.left r' ∉ avoidSet (p i) L7 E I)
    (hfar : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r → t7 < r' → L7 + 1 ≤ ‖q.1.left r' - p i‖)
    (hL7 : max (Real.log β) 10 ≤ L7 + 1)
    (hβ : t7 + 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 < β) (hn : L7 + 1 < (n : ℝ) ^ 17 / 6 - 2) :
    Disjoint (CycEntry.region β ((((0 : ℕ), p i, β', false) : CycData ℕ (k + 2)),
        q.cut (r : ℝ≥0∞)))
      (⋃ m ∈ Finset.range (I + 1), (E m).region β) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_iUnion, Finset.mem_range] at hx'
  obtain ⟨m, hmI, hxm⟩ := hx'
  obtain ⟨r₁, r₂, hr₁, hl₁, hr₂, hl₂, hclock, hnorm⟩ := region_overlap hx hxm
  have hlen : (CycEntry.len ((((0 : ℕ), p i, β', false) : CycData ℕ (k + 2)), q.cut (r : ℝ≥0∞))) =
      (r : ℝ≥0∞) := by
    unfold CycEntry.len CycPath.cut
    simp only [CPath.cut_len]
  rw [hlen] at hl₁
  have hr₁r : r₁ ≤ r := by exact_mod_cast hl₁
  have hleft : (CycEntry.path ((((0 : ℕ), p i, β', false) : CycData ℕ (k + 2)),
      q.cut (r : ℝ≥0∞))).left r₁ = q.1.left r₁ := by
    unfold CycEntry.path CycPath.cut
    exact CPath.left_cut q.1 _ hr₁ hl₁
  rw [hleft] at hnorm
  have hy := hQ r₁ hr₁ hr₁r
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · have hz := hE0 r₂ hr₂ hl₂
    refine hz (escQ_nbhd_block hj hy ?_)
    rw [norm_sub_rev]; exact hnorm
  · have hmI' : m ≤ I := by omega
    have hdata := hEdata m hm1 hmI'
    have hclock' : CycData.clock β (((0 : ℕ), p i, β', false) : CycData ℕ (k + 2)) r₁ =
        CycData.clock β (((0 : ℕ), p m, β', true) : CycData ℕ (k + 2)) r₂ := by
      rw [← hdata]; exact hclock
    have hsum := clock_bwd_fwd hr₁ hr₂ hclock'
    have hv := left_mem_entVisited (E m) hr₂ hl₂
    set y := q.1.left r₁ with hydef
    set z := (E m).path.left r₂ with hzdef
    by_cases hfar' : L7 ≤ ‖y - p i‖
    · exact hav r₁ hr₁ hr₁r ⟨hfar', m, hm1, hmI', z, hv, hnorm⟩
    · push Not at hfar'
      have hr1t : (r₁ : ℝ) ≤ t7 := by
        by_contra hgt
        push Not at hgt
        have := hfar r₁ hr₁ hr₁r hgt
        linarith
      have hzp : ‖z - p i‖ < L7 + 1 := by
        have := norm_sub_le_norm_sub_add_norm_sub z y (p i)
        have h2 : ‖z - y‖ ≤ 1 := by rw [norm_sub_rev]; exact hnorm
        linarith
      by_cases hmi : m = i
      · subst hmi
        have := HV (L7 + 1) hL7 r₂ hr₂ hl₂ hzp.le
        linarith
      · have := HD m hm1 hmI' hmi r₂ hr₂ hl₂
        linarith

end read

end ElboimSly.Paper.Escape
