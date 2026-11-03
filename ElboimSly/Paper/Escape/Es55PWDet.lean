/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWReg
public import ElboimSly.Paper.Escape.Es55DetProofC
public import ElboimSly.Paper.Escape.Es55Freeze
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the exit time of the backward entry

ES22 Lemma 5.5, Step 1.  `ent5_back_len`: the length of the backward entry equals the time
`jt a` of its exit jump (`D55Exit`), and the exit index is unique.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem d55Exit_unique {j : ℕ} (hj : 1 ≤ j) {u : EscV k} {e : CycEntry ℕ (k + 2)} {a a' : ℕ}
    (h : D55Exit j u e a) (h' : D55Exit j u e a') : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd (h'.2.2 a hlt) (pw_escFace_not_mem_escQ hj h.2.1)
  · exact heq
  · exact absurd (h.2.2 a' hgt) (pw_escFace_not_mem_escQ hj h'.2.1)

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem ent5_back_len (hν : CycGood ν) (hj : 1 ≤ escJ n)
    (hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u) (hx : ν ∈ es55Exit β n u β' i) {a : ℕ}
    (hD : D55Exit (escJ n) u (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) a) :
    (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len =
      (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.jt a ∧
    (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.jt a ≤
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
  obtain ⟨a', hD', hjt⟩ := ent5_back_exit n tn u β' i hlog ν hν hj hx
  obtain rfl := d55Exit_unique hj hD hD'
  refine ⟨?_, hjt⟩
  set p := pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1) with hp
  have hpath0 : (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path = p.1.cut
      ((plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1)
        ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν)
          (escIstar n (escJ n) + 1)) p) := by
    rw [ent5_eq]; rfl
  rw [← ent5_len] at hpath0
  set L := (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len with hL
  have hpath := hpath0
  have hLa : p.1.jt a ≤ L := by
    by_contra hnot
    have : (p.1.cut L).jt a = ⊤ := by rw [CPath.jt_cut, ite_eq_right hnot]
    rw [hpath, this] at hjt
    exact absurd hjt (by simp)
  have hjtc : (p.1.cut L).jt a = p.1.jt a := by rw [CPath.jt_cut, ite_eq_left hLa]
  have hfin : p.1.jt a ≠ ⊤ := by
    have h2 : (p.1.cut L).jt a ≤ ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
      rw [← hpath]; exact hjt
    rw [hjtc] at h2
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have hnot : p.1.fn (p.1.jt a).toNNReal ∉ escQ (escJ n) u := by
    have : p.1.fn (p.1.jt a).toNNReal = p.1.jv a := rfl
    rw [this, ← CPath.jv_cut p.1 L a hLa, ← hpath]
    exact pw_escFace_not_mem_escQ hj hD.2.1
  have h0 : p.1.fn 0 ∈ escQ (escJ n) u := by
    rw [hp]; unfold pth5 pth
    rw [envPath_zero (hν _)]
    have : dat (plan5 n β tn u β' i hlog) ν (escIstar n (escJ n) + 1) =
        (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) :=
      ent5_data_back n tn u β' i hlog ν
    rw [this]; exact hpQ
  have h1 := stopLen_plan5_back_le n tn u β' i hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) (escIstar n (escJ n) + 1))
    p (p.1.jt a).toNNReal h0 hnot
  rw [← ent5_len, ← hL, ENNReal.coe_toNNReal hfin] at h1
  rw [hpath, hjtc]
  exact le_antisymm h1 hLa

end ElboimSly.Paper.Escape
