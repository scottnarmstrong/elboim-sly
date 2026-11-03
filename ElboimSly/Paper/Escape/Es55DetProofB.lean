/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55DetProofA
public import Mathlib

/-!
# `Es55DetAll`, part B: the entrance point `v` lies in `∂B ∩ B⁻`

ES22 Lemma 5.5, proof, first paragraph ("Then `v ∈ ∂B`: if `ξ_B > 0`, `W(ξ_B-) ∉ B` is a
neighbour of `v`; if `ξ_B = 0`, then `v = 0 = u` (admissibility) and `u - e₁ ∉ B`").
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

/-- A unit `ℓ¹`-step is a step along one coordinate. -/
theorem unit_step {d : ℕ} (a b : Fin d → ℤ) (h : ∑ i, |a i - b i| = 1) :
    ∃ c : Fin d, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ b = Function.update a c (a c + s) := by
  classical
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |a i - b i| := fun i _ => abs_nonneg _
  have hex : ∃ c, a c - b c ≠ 0 := by
    by_contra hno
    push Not at hno
    simp [hno] at h
  obtain ⟨c, hcne⟩ := hex
  have hge : 1 ≤ |a c - b c| := Int.one_le_abs hcne
  have hle : |a c - b c| ≤ 1 := by
    rw [← h]; exact Finset.single_le_sum h0 (Finset.mem_univ c)
  have hc : |a c - b c| = 1 := le_antisymm hle hge
  have hrest : ∀ j, j ≠ c → |a j - b j| = 0 := by
    have hs := Finset.add_sum_erase Finset.univ (fun i => |a i - b i|) (Finset.mem_univ c)
    rw [h, hc] at hs
    have hz : ∑ x ∈ Finset.univ.erase c, |a x - b x| = 0 := by omega
    intro j hj
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).1 hz j
      (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
  refine ⟨c, b c - a c, ?_, ?_⟩
  · rcases abs_cases (a c - b c) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hc; right; omega
    · rw [h1] at hc; left; omega
  · funext j
    by_cases hj : j = c
    · subst hj; simp
    · have := hrest j hj
      rw [abs_eq_zero, sub_eq_zero] at this
      simp [Function.update_of_ne hj, this]

theorem escBlockMinus_subset {d : ℕ} {j : ℕ} (u : Fin (d + 2) → ℤ) :
    escBlockMinus j u ⊆ escBlock j u := by
  intro x hx c
  by_cases hc : c = 0
  · subst hc
    refine ⟨hx.1.1, lt_of_lt_of_le hx.1.2 ?_⟩
    gcongr
    · norm_num
    · omega
  · exact hx.2 c hc

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ)
  (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β))

theorem ent5_zero_entEnd (hν : CycGood ν)
    (hle : escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn)
    (hlt : escXi (escWalk ν) (escBlock (escJ n) u) < ElboimSly.cycTreg (copyEnv ν 0))
    (hB : escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal ∈ escBlock (escJ n) u) :
    entEnd (ent5 n tn u β' i hlog ν 0) =
      escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal := by
  have hL := ent5_zero_len n tn u β' i hlog ν hν hle hlt hB
  set ξ := escXi (escWalk ν) (escBlock (escJ n) u)
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hx := ent5_fn n tn u β' i hlog ν 0 (s := ξ.toNNReal)
    (by rw [ENNReal.coe_toNNReal hξtop, hL])
  have hxt : ((ξ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ElboimSly.cycTreg (copyEnv ν 0) := by
    rw [ENNReal.coe_toNNReal hξtop]; exact hlt.le
  unfold entEnd
  rw [show (ent5 n tn u β' i hlog ν 0).len.toNNReal = ξ.toNNReal by rw [hL], hx,
    pth5_zero_eq_escWalk n tn u β' i hlog ν hν _ hxt]
  rfl

theorem ent5_zero_bdry (hadm : EscAdmissible (escJ n) u) (hν : CycGood ν)
    (hle : escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn)
    (hlt : escXi (escWalk ν) (escBlock (escJ n) u) < ElboimSly.cycTreg (copyEnv ν 0))
    (hBm : escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal ∈
      escBlockMinus (escJ n) u) :
    entEnd (ent5 n tn u β' i hlog ν 0) ∈ escBoundary (escJ n) u ∧
      entEnd (ent5 n tn u β' i hlog ν 0) ∈ escBlockMinus (escJ n) u := by
  have hB := escBlockMinus_subset u hBm
  have hL := ent5_zero_len n tn u β' i hlog ν hν hle hlt hB
  have hv := ent5_zero_entEnd n tn u β' i hlog ν hν hle hlt hB
  set ξ := escXi (escWalk ν) (escBlock (escJ n) u) with hξ
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set e0 := ent5 n tn u β' i hlog ν 0 with he0
  rw [hv]
  refine ⟨⟨hB, ?_⟩, hBm⟩
  by_cases hξ0 : ξ = 0
  · have hv0 : entEnd e0 = 0 := by
      have hx := ent5_fn n tn u β' i hlog ν 0 (s := 0) (by simp)
      have hg : Good (copyEnv ν 0) := by rw [copyEnv_eq_cycSlice]; exact hν 0
      unfold entEnd
      rw [show e0.len.toNNReal = 0 by rw [he0, hL, hξ0]; simp, hx,
        pth5_zero_fn n tn u β' i hlog ν hν]
      simpa using cycWalk_zero hg 0 0
    rw [hv] at hv0
    rw [hv0]
    rcases hadm with h | rfl
    · rw [hv0] at hB; exact absurd hB h
    · refine ⟨0, -1, Or.inr rfl, fun hin => ?_⟩
      have h1 : (0 : ℤ) ≤ -1 := by simpa using (hin 0).1
      omega
  · have hr : 0 < ξ.toNNReal := by
      rw [pos_iff_ne_zero]; intro h0
      exact hξ0 ((ENNReal.toNNReal_eq_zero_iff _).1 h0 |>.resolve_right hξtop)
    have hl : ((ξ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e0.len := by
      rw [ENNReal.coe_toNNReal hξtop, he0, hL]
    have hz := ent5_walk1_left n tn u β' i hlog ν hr hl
    have hfn : e0.path.fn ξ.toNNReal = escWalk ν ξ.toReal := by
      rw [← hv]; unfold entEnd
      rw [show e0.len.toNNReal = ξ.toNNReal by rw [he0, hL]]
    have hne : e0.path.left ξ.toNNReal ≠ e0.path.fn ξ.toNNReal := by
      intro heq
      rw [heq, hfn] at hz
      exact hz hB
    have hcd := (CPath.mem_CDisc_iff e0.path hr).2 hne
    have hunit := e0.2.2 _ hcd
    obtain ⟨c, s, hs, hc⟩ := unit_step _ _ hunit
    refine ⟨c, s, hs, ?_⟩
    have hc' : e0.path.left ξ.toNNReal =
        Function.update (escWalk ν ξ.toReal) c (escWalk ν ξ.toReal c + s) := by
      rw [← hfn]; exact hc
    rw [← hc']
    exact hz

end ElboimSly.Paper.Escape
