/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5
public import ElboimSly.Foundations.Cyclic.CycPathType
public import ElboimSly.Foundations.Cyclic.CPathLeft
public import Mathlib

/-!
# The exit from the box `𝒬`: geometry of ES22 Claim 5.7

ES22 Claim 5.7 ("`P̃` leaves `𝒬` before `4^{j-1}`, and its first exit lowers the first
coordinate to `u₁ + 2^{j-1} - 1`: the exit point is in `F_B`") and the box escQ, the backward walks and zeta_i (`r_i`).

* `escBigBox`: the box `u + [0, 7·2^{j-3}] × [2^{j-2}, 3·2^{j-2}]^{d-1}` of eq. (85);
* `escExit Q w`: the first exit time `r_i = inf {r > 0 : w r ∉ Q}`;
* `exit_geom`: a nearest-neighbour right-continuous path that starts in `𝒬`, stays in the big box
  up to time `S` and is outside `𝒬` at time `S`, exits `𝒬` at a time `r ≤ S` at a point of `F_B`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

/-- The box `u + [0, 7·2^{j-3}] × [2^{j-2}, 3·2^{j-2}]^{d-1}` of eq. (85) of ES22. -/
def escBigBox (j : ℕ) (u : EscV k) : Set (EscV k) :=
  {x | (u 0 ≤ x 0 ∧ x 0 ≤ u 0 + 7 * (2 ^ j / 8)) ∧
    ∀ c, c ≠ 0 → (u c + 2 ^ j / 4 ≤ x c ∧ x c ≤ u c + 3 * (2 ^ j / 4))}

/-- The first exit time `r = inf {r > 0 : w r ∉ Q}` of a path from a set `Q`. -/
noncomputable def escExit (Q : Set (EscV k)) (w : ℝ≥0 → EscV k) : ℝ≥0∞ :=
  ⨅ (r : ℝ≥0) (_ : 0 < r ∧ w r ∉ Q), (r : ℝ≥0∞)

theorem escQ_subset_bigBox (j : ℕ) (u : EscV k) : escQ j u ⊆ escBigBox j u := by
  intro x hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  refine ⟨⟨?_, h2⟩, h3⟩
  have : (0 : ℤ) ≤ 2 ^ j / 2 := by positivity
  omega

theorem mem_escQ_iff {j : ℕ} {u : EscV k} {x : EscV k} :
    x ∈ escQ j u ↔ x ∈ escBigBox j u ∧ u 0 + 2 ^ j / 2 ≤ x 0 := by
  constructor
  · intro hx
    exact ⟨escQ_subset_bigBox j u hx, hx.1.1⟩
  · rintro ⟨⟨⟨-, h2⟩, h3⟩, h4⟩
    exact ⟨⟨h4, h2⟩, h3⟩

/-- **Exit geometry.** -/
theorem exit_geom {j : ℕ} (hj : 4 ≤ j) {u : EscV k} (y : CycPath (k + 2)) {S : ℝ≥0}
    (hS : 0 < S) (hy0 : y.1.fn 0 ∈ escQ j u)
    (hbox : ∀ s : ℝ≥0, s ≤ S → y.1.fn s ∈ escBigBox j u) (hout : y.1.fn S ∉ escQ j u) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ S ∧ (∀ s : ℝ≥0, s < r → y.1.fn s ∈ escQ j u) ∧
      y.1.fn r ∈ escFace j u ∧ escExit (escQ j u) y.1.fn = r := by
  classical
  set G : Set ℝ≥0 := {r | 0 < r ∧ y.1.fn r ∉ escQ j u} with hG
  have hSG : S ∈ G := ⟨hS, hout⟩
  set r₀ := sInf G with hr₀
  have hbdd : BddBelow G := ⟨0, fun r _ => zero_le⟩
  have hr₀S : r₀ ≤ S := csInf_le hbdd hSG
  have hlt : ∀ s, s < r₀ → s ∉ G := fun s hs hsG => absurd (csInf_le hbdd hsG) (not_le.2 hs)
  -- `y r₀ ∉ Q`
  have hyr₀ : y.1.fn r₀ ∉ escQ j u := by
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (y.1.rc r₀)
    obtain ⟨g, hgG, hgu⟩ := exists_lt_of_csInf_lt ⟨S, hSG⟩ (lt_of_lt_of_le hu' le_rfl : r₀ < u')
    have hg0 : r₀ ≤ g := csInf_le hbdd hgG
    have := hsub ⟨hg0, hgu⟩
    simp only [mem_ofPred_eq] at this
    rw [← this]; exact hgG.2
  have hr₀pos : 0 < r₀ := by
    by_contra h
    have h0 : r₀ = 0 := le_antisymm (not_lt.1 h) zero_le
    rw [h0] at hyr₀
    exact hyr₀ hy0
  have hr₀G : r₀ ∈ G := ⟨hr₀pos, hyr₀⟩
  have hbefore : ∀ s : ℝ≥0, s < r₀ → y.1.fn s ∈ escQ j u := by
    intro s hs
    have hsG := hlt s hs
    by_cases hs0 : 0 < s
    · by_contra hn
      exact hsG ⟨hs0, hn⟩
    · have : s = 0 := le_antisymm (not_lt.1 hs0) zero_le
      rw [this]; exact hy0
  have hne : (𝓝[<] r₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr₀pos⟩
  obtain ⟨s₁, hs₁, hs₁lt⟩ := ((y.1.eventually_left hr₀pos).and
    (self_mem_nhdsWithin (a := r₀) (s := Iio r₀))).exists
  have hlQ : y.1.left r₀ ∈ escQ j u := by rw [← hs₁]; exact hbefore s₁ hs₁lt
  have hne2 : y.1.left r₀ ≠ y.1.fn r₀ := fun h => hyr₀ (h ▸ hlQ)
  have hdisc : r₀ ∈ CDisc y.1.fn := (y.1.mem_CDisc_iff hr₀pos).2 hne2
  have hsum := y.2 r₀ hdisc
  set a := y.1.fn r₀ with ha
  set l := y.1.left r₀ with hl
  have haB : a ∈ escBigBox j u := hbox r₀ hr₀S
  have ha0 : a 0 < u 0 + 2 ^ j / 2 := by
    by_contra h
    exact hyr₀ (mem_escQ_iff.2 ⟨haB, not_lt.1 h⟩)
  have hl0 : u 0 + 2 ^ j / 2 ≤ l 0 := (mem_escQ_iff.1 hlQ).2
  have hsplit : |a 0 - l 0| + ∑ c ∈ Finset.univ.erase 0, |a c - l c| = ∑ c, |a c - l c| :=
    Finset.add_sum_erase Finset.univ (fun c => |a c - l c|) (Finset.mem_univ 0)
  have hrest0 : 0 ≤ ∑ c ∈ Finset.univ.erase 0, |a c - l c| :=
    Finset.sum_nonneg fun c _ => abs_nonneg _
  have hf0 : 1 ≤ |a 0 - l 0| := by
    rw [abs_sub_comm, abs_of_nonneg (by omega)]; omega
  have hrest : ∑ c ∈ Finset.univ.erase 0, |a c - l c| = 0 := by
    omega
  have hf1 : |a 0 - l 0| = 1 := by
    omega
  have hac : ∀ c, c ≠ 0 → a c = l c := by
    intro c hc
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => abs_nonneg _)).1 hrest c
      (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩)
    have h2 : |a c - l c| = 0 := this
    rw [abs_eq_zero] at h2
    omega
  have ha0' : a 0 = l 0 - 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by omega)] at hf1; omega
  refine ⟨r₀, hr₀pos, hr₀S, hbefore, ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hpow : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
    have hpm : (2 : ℤ) ^ (m + 1 - 1) = 2 ^ m := by simp
    refine ⟨?_, fun c hc => ?_⟩
    · show a 0 = u 0 + 2 ^ (m + 1 - 1) - 1
      rw [hpm]
      rw [hpow] at ha0 hl0
      omega
    · have e : y.1.fn r₀ c = l c := hac c hc
      rw [e]
      exact (mem_escQ_iff.1 hlQ).1.2 c hc
  · apply le_antisymm
    · exact iInf₂_le r₀ hr₀G
    · refine le_iInf₂ fun r hr => ?_
      exact_mod_cast csInf_le hbdd hr

end ElboimSly.Paper.Escape
