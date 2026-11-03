/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWEntries
public import ElboimSly.Paper.Escape.Es55PWCore
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the explored region of the record at `S₃`, seen from `B⁻`

ES22 Lemma 5.5, Step 1, "Agreement on `E₅₆ ∩ E₀`".

`pw_reg_of_ent5` proves `PWReg` for the region `R ⊆ ⋃_{m ≤ I+1} R(E_m)` of the entries of `𝒫₅`:
every point of `R` has an endpoint outside `B⁻` (walk `1`: outside `B`; `W_m`: far from `B⁻`;
`W_i^←`: in `𝒬`), and the atoms of `ν` in `R` on an edge through a vertex of `B⁻` are the rings
`x_ent` (the last jump of walk `1`) and `x_ex` (the last jump of `W_i^←`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

section reg

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem ent5_eq_envPath (m : ℕ) :
    ent5 n tn u β' i hlog ν m =
      (dat (plan5 n β tn u β' i hlog) ν m,
        (envPath ν (dat (plan5 n β tn u β' i hlog) ν m)).cut
          ((plan5 n β tn u β' i hlog).stopLen m
            ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
            (pth5 n tn u β' i hlog ν m))) := ent5_eq n tn u β' i hlog ν m

/-- An atom of `ν` in the region of an entry is a known ring of the entry. -/
theorem pw_ringSet_ent5 (hν : CycGood ν) {m : ℕ} {x : CycS ℕ (k + 2) β}
    (hx : x ∈ (ent5 n tn u β' i hlog ν m).region β) (hat : 1 ≤ ν {x}) :
    x ∈ (ent5 n tn u β' i hlog ν m).ringSet β := by
  have h := entry_ringSet_eq hν (dat (plan5 n β tn u β' i hlog) ν m)
    ((plan5 n β tn u β' i hlog).stopLen m
      ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
      (pth5 n tn u β' i hlog ν m))
  rw [← ent5_eq_envPath] at h
  rw [h]
  refine ⟨hx, ?_⟩
  show ν {x} ≠ 0
  intro h0
  rw [h0] at hat
  simp at hat

variable {n tn u β' i hlog ν}

theorem pw_mem_edge_of_ring {a b z : EscV k} {e : Edge (k + 2)} (he : e.1 = s(a, b))
    (hz : z ∈ e.1) : z = a ∨ z = b := by
  rw [he] at hz
  exact Sym2.mem_iff.1 hz

/-- **The explored region of the record at `S₃`, seen from `B⁻`.** -/
theorem pw_reg_of_ent5 (hν : CycGood ν) (hj : 3 ≤ escJ n) (_hi : 1 ≤ i ∧ i ≤ escIstar n (escJ n))
    (hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u)
    {R : Set (CycS ℕ (k + 2) β)}
    (hR : R ⊆ ⋃ m ∈ Finset.range (escIstar n (escJ n) + 2), (ent5 n tn u β' i hlog ν m).region β) :
    PWReg (escJ n) u ν R (entEnd (ent5 n tn u β' i hlog ν 0))
      (entEnd (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)))
      (ent5 n tn u β' i hlog ν 0).len.toReal
      (((β' : ℝ) - (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len.toReal : ℝ) :
        AddCircle β) := by
  have hj1 : 1 ≤ escJ n := by omega
  have h8 : (1 : ℝ) ≤ (2 : ℝ) ^ escJ n / 8 := by
    have : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ escJ n := pow_le_pow_right₀ (by norm_num) hj
    linarith
  have hmem : ∀ x ∈ R, ∃ m, m < escIstar n (escJ n) + 2 ∧
      x ∈ (ent5 n tn u β' i hlog ν m).region β := by
    intro x hx
    have := hR hx
    simp only [mem_iUnion, Finset.mem_range] at this
    obtain ⟨m, hm, h⟩ := this
    exact ⟨m, hm, h⟩
  constructor
  · intro x hx
    obtain ⟨m, hm, hxm⟩ := hmem x hx
    obtain ⟨r, hr, hl, -, -, hmemr⟩ := hxm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ⟨_, hmemr, fun hq => ent5_walk1_left n tn u β' i hlog ν hr hl
        (blockMinus_subset_block hj1 hq)⟩
    · by_cases hmI : m ≤ escIstar n (escJ n)
      · refine ⟨_, hmemr, fun hq => ?_⟩
        have := ent5_mid_far n tn u β' i hlog ν hm0 hmI hr hl hq
        rw [sub_self, norm_zero] at this
        have : (0 : ℝ) < (2 : ℝ) ^ escJ n / 8 := by positivity
        linarith
      · have hmB : m = escIstar n (escJ n) + 1 := by omega
        subst hmB
        exact ⟨_, hmemr, fun hq => escQ_not_mem_blockMinus hj1
          (ent5_back_left_mem n tn u β' i hlog ν hν hpQ hr hl) hq⟩
  · intro x hx hat z hz hzm
    obtain ⟨m, hm, hxm⟩ := hmem x hx
    have hring := pw_ringSet_ent5 n tn u β' i hlog ν hν hxm hat.ge
    obtain ⟨r, hr, hl, hne, h1, h2, h3⟩ := hring
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · -- walk 1: the entrance ring
      have hza := ent5_walk1_left n tn u β' i hlog ν hr hl
      have hzb : z = (ent5 n tn u β' i hlog ν 0).path.fn r := by
        rcases pw_mem_edge_of_ring h3 (hzm : z ∈ x.2.1.1) with h | h
        · exact absurd (h ▸ blockMinus_subset_block hj1 hz) hza
        · exact h
      have hge : (ent5 n tn u β' i hlog ν 0).len ≤ r := by
        by_contra hlt
        push Not at hlt
        exact ent5_walk1_fn_lt n tn u β' i hlog ν hlt (hzb ▸ blockMinus_subset_block hj1 hz)
      have hlen : (ent5 n tn u β' i hlog ν 0).len = (r : ℝ≥0∞) := le_antisymm hge hl
      refine Or.inl ⟨?_, ?_, _, hza, ?_⟩
      · rw [hzb]; unfold entEnd; rw [hlen]; simp
      · rw [h2, ent5_data_zero, hlen]
        simp [CycData.clock, CycData.sgn, CycData.fwd, CycData.phase]
      · rw [h3]; unfold entEnd; rw [hlen]; simp
    · by_cases hmI : m ≤ escIstar n (escJ n)
      · exfalso
        have hfar := ent5_mid_far n tn u β' i hlog ν hm0 hmI hr hl hz
        have ha : (ent5 n tn u β' i hlog ν m).path.left r ∈ x.2.1.1 := by rw [h3]; simp
        have hb : (ent5 n tn u β' i hlog ν m).path.fn r ∈ x.2.1.1 := by rw [h3]; simp
        rcases pw_mem_edge_of_ring h3 (hzm : z ∈ x.2.1.1) with h | h
        · rw [← h, sub_self, norm_zero] at hfar
          have : (0 : ℝ) < (2 : ℝ) ^ escJ n / 8 := by positivity
          linarith
        · have := norm_le_one_of_mem_edge ha hb
          rw [← h] at this
          linarith
      · have hmB : m = escIstar n (escJ n) + 1 := by omega
        subst hmB
        have hza := ent5_back_left_mem n tn u β' i hlog ν hν hpQ hr hl
        have hzb : z = (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.fn r := by
          rcases pw_mem_edge_of_ring h3 (hzm : z ∈ x.2.1.1) with h | h
          · exact absurd hz (h ▸ escQ_not_mem_blockMinus hj1 hza)
          · exact h
        have hge : (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len ≤ r := by
          by_contra hlt
          push Not at hlt
          exact escQ_not_mem_blockMinus hj1
            (ent5_back_fn_mem n tn u β' i hlog ν hν hpQ hlt) (hzb ▸ hz)
        have hlen : (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len = (r : ℝ≥0∞) :=
          le_antisymm hge hl
        refine Or.inr ⟨?_, ?_⟩
        · rw [hzb]; unfold entEnd; rw [hlen]; simp
        · rw [h2, ent5_data_back, hlen]
          simp [CycData.clock, CycData.sgn, CycData.fwd, CycData.phase, sub_eq_add_neg]

end reg

end ElboimSly.Paper.Escape
