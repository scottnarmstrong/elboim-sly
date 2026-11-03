/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenBasic
public import ElboimSly.Foundations.Cyclic.CPathCount
public import Mathlib

/-!
# ES22 Lemma 2.2, Step 1: the deviation of a unit-step path is at most its number of jumps

ES22 Lemma 2.2, Step 1 ("each piece starts at `0`, and its jumps have `ℓ¹`-size `1`, so
`‖p(s)‖₁ ≤ J`").

`l1n_le_card_jumps`: for a regular path `f` with `f 0 = 0` and unit steps at every jump,
`‖f r‖₁ ≤ #(CDisc f ∩ (0, r])`.
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The `ℓ¹` norm of an integer vector, as a natural number. -/
def l1n (x : Fin d → ℤ) : ℕ := ∑ i, (x i).natAbs

theorem l1n_zero : l1n (0 : Fin d → ℤ) = 0 := by simp [l1n]

theorem l1n_add (a b : Fin d → ℤ) : l1n (a + b) ≤ l1n a + l1n b := by
  unfold l1n
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem l1n_eq_one {v : Fin d → ℤ} (h : IsUnitStep v) : l1n v = 1 := by
  unfold IsUnitStep at h
  unfold l1n
  have : ((∑ i, (v i).natAbs : ℕ) : ℤ) = 1 := by
    push_cast
    simpa [Int.natCast_natAbs] using h
  exact_mod_cast this

theorem l1n_le_card_jumps {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) (h0 : f 0 = 0)
    (hu : ∀ s ∈ CDisc f, IsUnitStep (f s - leftVal f s)) (n : ℕ) :
    ∀ r : ℝ≥0, (CDisc f ∩ Iic r).ncard = n → l1n (f r) ≤ n := by
  induction n with
  | zero =>
    intro r hr
    have hemp : CDisc f ∩ Iic r = ∅ := (Set.ncard_eq_zero (hf.fin r)).1 hr
    have := eq_of_no_disc hf.rc (zero_le : (0 : ℝ≥0) ≤ r) (fun s hs hd => by
      have : s ∈ CDisc f ∩ Iic r := ⟨hd, hs.2⟩
      rw [hemp] at this; exact this)
    rw [this, h0, l1n_zero]
  | succ n ih =>
    intro r hr
    have hfin := hf.fin r
    have hne : (CDisc f ∩ Iic r).Nonempty := by
      rw [← Set.ncard_pos hfin]; omega
    set u := hfin.toFinset.max' (by simpa using hne) with hu_def
    have humem : u ∈ CDisc f ∩ Iic r :=
      hfin.mem_toFinset.1 (hfin.toFinset.max'_mem (by simpa using hne))
    have hmax : ∀ s ∈ CDisc f ∩ Iic r, s ≤ u := fun s hs =>
      hfin.toFinset.le_max' s (by simpa using hs)
    -- `f r = f u`
    have hfr : f r = f u := eq_of_no_disc hf.rc humem.2 (fun s hs hd =>
      absurd (hmax s ⟨hd, hs.2⟩) (not_le.2 hs.1))
    have hu0 : 0 < u := humem.1.1
    -- the jumps strictly before `u`
    have hF : (CDisc f ∩ Iio u).Finite := (hf.fin u).subset fun s hs => ⟨hs.1, hs.2.le⟩
    obtain ⟨t, htu, ht⟩ : ∃ t, t < u ∧ ∀ s ∈ CDisc f, t < s → s < u → False := by
      by_cases hne' : (CDisc f ∩ Iio u).Nonempty
      · refine ⟨hF.toFinset.max' (by simpa using hne'), ?_, fun s hs h1 h2 => ?_⟩
        · have hmem := hF.toFinset.max'_mem (by simpa using hne')
          simp only [Finite.mem_toFinset] at hmem
          exact hmem.2
        · exact absurd (hF.toFinset.le_max' s (by simpa using ⟨hs, h2⟩)) (not_le.mpr h1)
      · exact ⟨0, hu0, fun s hs _ h2 => hne' ⟨s, hs, h2⟩⟩
    have hset : CDisc f ∩ Iic t = CDisc f ∩ Iio u := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans_lt htu⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hc
        exact ht s h1 (not_le.1 hc) h2
    have hcard : (CDisc f ∩ Iic t).ncard = n := by
      have hsplit : CDisc f ∩ Iic r = insert u (CDisc f ∩ Iio u) := by
        ext s
        simp only [mem_inter_iff, mem_Iic, mem_Iio, mem_insert_iff]
        constructor
        · rintro ⟨h1, h2⟩
          rcases (hmax s ⟨h1, h2⟩).lt_or_eq with h | h
          · exact Or.inr ⟨h1, h⟩
          · exact Or.inl h
        · rintro (rfl | ⟨h1, h2⟩)
          · exact humem
          · exact ⟨h1, h2.le.trans humem.2⟩
      rw [hsplit, Set.ncard_insert_of_notMem (fun h => lt_irrefl _ h.2) hF] at hr
      rw [hset]; omega
    have ihu := ih t hcard
    -- the left value at `u` is `f t`
    have hleft : leftVal f u = f t := by
      have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
      have hev := hf.eventually_leftVal hu0
      obtain ⟨v, hv1, hv2⟩ := (hev.and (Ioo_mem_nhdsLT htu)).exists
      have hc : f v = f t := const_of_no_disc hf.rc hv2.1.le (fun s hs hd =>
        ht s hd hs.1 (hs.2.trans_lt hv2.2)) v ⟨hv2.1.le, le_rfl⟩
      rw [← hv1, hc]
    have hstep := l1n_eq_one (hu u humem.1)
    have : f u = f t + (f u - leftVal f u) := by rw [hleft]; abel
    rw [hfr, this]
    calc l1n (f t + (f u - leftVal f u)) ≤ l1n (f t) + l1n (f u - leftVal f u) := l1n_add _ _
      _ ≤ n + 1 := by rw [hstep]; omega

end ElboimSly.Cyclic

end
