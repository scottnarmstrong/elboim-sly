/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPiece
public import ElboimSly.Foundations.Cyclic.CycRingPiece
public import Mathlib

/-!
# Chains of initial pieces and their limit

Measurability of record functionals (e). Let `(p_j)` be paths with `p_j` an initial piece of `p_{j+1}`.
Then each jump time `ς_a(p_j)` is nonincreasing in `j` and eventually constant, with limit `τ_a`.
If `∀ M, ∃ a, M < τ_a` (the limiting jump times tend to `∞`) the paths have a limit path `q`, a
path of length `⨆ len p_j`, of which every `p_j` is an initial piece, with `ς_a(q) = τ_a`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

theorem CPath.jv_cut (p : CPath V) (ℓ : ℝ≥0∞) (a : ℕ) (h : p.jt a ≤ ℓ) :
    (p.cut ℓ).jv a = p.jv a := by
  unfold CPath.jv
  rw [CPath.jt_cut, ite_eq_left h]
  rcases eq_or_ne (p.jt a) ⊤ with ht | ht
  · simp only [ht, ENNReal.toNNReal_top]
    exact CPath.fn_cut_of_le _ (by simp)
  · refine CPath.fn_cut_of_le _ ?_
    rw [ENNReal.coe_toNNReal ht]; exact h

/-- A chain of initial pieces. -/
def CPath.IsChain (p : ℕ → CPath V) : Prop := ∀ j, (p j).IsPiece (p (j + 1))

namespace CPath.IsChain

variable {p : ℕ → CPath V} (hp : CPath.IsChain p)
include hp

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem piece {j j' : ℕ} (h : j ≤ j') : (p j).IsPiece (p j') := by
  induction h with
  | refl => exact CPath.isPiece_refl _
  | step _ ih => exact ih.trans (hp _)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem len_mono : Monotone fun j => (p j).len := fun _ _ h => (hp.piece h).1

theorem jt_le {j j' : ℕ} (h : j ≤ j') (a : ℕ) : (p j').jt a ≤ (p j).jt a := by
  rw [(hp.piece h).2, CPath.jt_cut]
  split_ifs with hh
  · exact le_rfl
  · exact le_top

theorem jt_stab {j j' : ℕ} (h : j ≤ j') {a : ℕ} (ha : (p j).jt a < ⊤) :
    (p j').jt a = (p j).jt a := by
  have h1 := (hp.piece h).2
  have h2 : (p j).jt a = if (p j').jt a ≤ (p j).len then (p j').jt a else ⊤ := by
    conv_lhs => rw [h1]
    exact CPath.jt_cut _ _ _
  split_ifs at h2 with hh
  · exact h2.symm
  · exact absurd h2 (ne_of_lt ha)

/-- The limit `τ_a = ⨅_j ς_a(p_j)` of the jump times. -/
noncomputable def tau (p : ℕ → CPath V) (a : ℕ) : ℝ≥0∞ := ⨅ j, (p j).jt a

theorem tau_eventually (a : ℕ) : ∃ J, ∀ j, J ≤ j → (p j).jt a = tau p a := by
  by_cases h : ∃ J, (p J).jt a < ⊤
  · obtain ⟨J, hJ⟩ := h
    have hc : ∀ j, J ≤ j → (p j).jt a = (p J).jt a := fun j hj => hp.jt_stab hj hJ
    have hτ : tau p a = (p J).jt a := by
      refine le_antisymm (iInf_le _ J) (le_iInf fun j => ?_)
      rcases le_total J j with hh | hh
      · exact (hc j hh).ge
      · exact hp.jt_le hh a
    exact ⟨J, fun j hj => (hc j hj).trans hτ.symm⟩
  · push Not at h
    have : ∀ j, (p j).jt a = ⊤ := fun j => top_le_iff.mp (h j)
    refine ⟨0, fun j _ => ?_⟩
    simp [tau, this]

theorem jt_le_len {j j' : ℕ} (h : j ≤ j') {a : ℕ} (ha : (p j).jt a < ⊤) :
    (p j').jt a ≤ (p j).len := by
  have h1 := (hp.piece h).2
  have h2 : (p j).jt a = if (p j').jt a ≤ (p j).len then (p j').jt a else ⊤ := by
    conv_lhs => rw [h1]
    exact CPath.jt_cut _ _ _
  by_contra hh
  rw [ite_eq_right_of_eq_false _ _ (eq_false hh)] at h2
  exact absurd h2 (ne_of_lt ha)

omit hp [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem tau_mono : Monotone (tau p) := by
  refine monotone_nat_of_le_succ fun a => ?_
  refine le_iInf fun j => (iInf_le _ j).trans ?_
  rcases eq_or_ne ((p j).jt (a + 1)) ⊤ with h | h
  · rw [h]; exact le_top
  · exact (p j).jt_mono h.lt_top

omit hp [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem tau_le_jt (a j : ℕ) : tau p a ≤ (p j).jt a := iInf_le _ j

/-- Beyond the stabilization time of the jumps up to `T`, consecutive pieces agree on `[0, T]`. -/
theorem agree_step (hgood : ∀ M : ℝ≥0, ∃ a, (M : ℝ≥0∞) < tau p a) (T : ℝ≥0) :
    ∃ J, ∀ j, J ≤ j → ∀ r, r ≤ T → (p (j + 1)).fn r = (p j).fn r := by
  obtain ⟨A, hA⟩ := hgood T
  choose Ja hJa using hp.tau_eventually
  refine ⟨(Finset.range (A + 1)).sup Ja, fun j hj r hr => ?_⟩
  have hJ : ∀ a, a ≤ A → Ja a ≤ j := fun a ha =>
    (Finset.le_sup (f := Ja) (Finset.mem_range.mpr (by omega))).trans hj
  by_cases hrl : (r : ℝ≥0∞) ≤ (p j).len
  · rw [(hp j).2, CPath.fn_cut_of_le _ hrl]
  · push Not at hrl
    have hlfin : (p j).len ≠ ⊤ := ne_top_of_lt hrl
    set t : ℝ≥0 := (p j).len.toNNReal with ht
    have htl : (t : ℝ≥0∞) = (p j).len := ENNReal.coe_toNNReal hlfin
    have htr : t < r := by exact_mod_cast (htl ▸ hrl)
    have hnod : ∀ s ∈ Ioc t r, s ∉ CDisc (p (j + 1)).fn := by
      intro s hs hsd
      have hs0 : 0 < s := lt_of_le_of_lt bot_le hs.1
      obtain ⟨a, hsa, -, -⟩ := (p (j + 1)).exists_jump_idx hs0 ((CPath.mem_CDisc_iff _ hs0).mp hsd)
      have hsT : (s : ℝ≥0∞) ≤ T := by exact_mod_cast hs.2.trans hr
      have haA : a + 1 ≤ A := by
        by_contra hh
        push Not at hh
        have h1 := tau_mono (p := p) hh.le
        have h2 := tau_le_jt (p := p) (a + 1) (j + 1)
        rw [← hsa] at h2
        exact absurd (lt_of_lt_of_le hA (h1.trans h2)) (not_lt.mpr hsT)
      have hj1 : (p j).jt (a + 1) = tau p (a + 1) := hJa _ _ (hJ _ haA)
      have hj2 : (p (j + 1)).jt (a + 1) = tau p (a + 1) :=
        hJa _ _ ((hJ _ haA).trans (Nat.le_succ j))
      have hfin : (p j).jt (a + 1) < ⊤ := by rw [hj1, ← hj2, ← hsa]; exact ENNReal.coe_lt_top
      have h3 := hp.jt_le_len (Nat.le_succ j) hfin
      rw [← hsa, ← htl] at h3
      have h4 : s ≤ t := by exact_mod_cast h3
      exact absurd hs.1 (not_lt.mpr h4)
    have h1 : (p (j + 1)).fn r = (p (j + 1)).fn t :=
      eq_of_no_disc (p (j + 1)).rc htr.le hnod
    have h2 : (p j).fn r = (p j).fn t := by
      refine (p j).const _ _ ?_ ?_
      · exact hrl.le
      · exact htl.ge
    rw [h1, h2, (hp j).2, CPath.fn_cut_of_le _ htl.le]

end CPath.IsChain

end ElboimSly.Cyclic

end
