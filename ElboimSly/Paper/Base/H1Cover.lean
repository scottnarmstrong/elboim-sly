/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Count
public import ElboimSly.Paper.Base.H1Version
public import Mathlib

/-!
# (H1) at the base: no heavy blocks

ES22 Lemma 8.1, Step 2, estimate (8.4).

* `H1Good`: the deterministic hypotheses (far, fast, coupling, occupation).
* `h1_not_heavy`: under `H1Good`, no block of radius `r ≥ m₀` is heavy at any time `t ≤ T`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW

variable {d : ℕ}

/-- The integer times `i` with `√2 B(i)` in the box of radius `2m` around `x`. -/
def occSet (B : ℝ≥0 → Fin d → ℝ) (x : Fin d → ℤ) (m : ℕ) : Set ℕ :=
  {i | ‖Real.sqrt 2 • B (i : ℝ≥0) - latR x‖ ≤ 2 * (m : ℝ)}

/-- The deterministic hypotheses of Step 2 of ES22 Lemma 8.1 for a path `γ` and a Brownian path `B`. -/
structure H1Good (n : ℕ) (T : ℝ≥0) (R : ℝ) (M m0 : ℕ) (γ : PathSpace d)
    (B : ℝ≥0 → Fin d → ℝ) : Prop where
  far : ∀ s : ℝ≥0, s ≤ T → ‖γ s‖ < R
  fast : ∀ s s' : ℝ≥0, s ≤ s' → s' ≤ T → s' - s ≤ 1 → ‖γ s' - γ s‖ ≤ (n : ℝ) ^ 5
  cpl : ∀ s : ℝ≥0, s ≤ T → ‖latR (γ s) - Real.sqrt 2 • B s‖ < (n : ℝ) ^ 10
  occ : ∀ x : Fin d → ℤ, ‖x‖ < R → ∀ m : ℕ, m0 ≤ m → m ≤ M →
    (occSet B x m).Finite ∧ ((occSet B x m).ncard : ℝ) ≤ (m : ℝ) ^ (21 / 10 : ℝ)

theorem ncard_le_of_cover {ι α : Type*} [DecidableEq α] (S : Set α) (I : Finset ι)
    (L : ι → Finset α) {K : ℝ} (hS : S ⊆ ⋃ i ∈ I, (L i : Set α))
    (hK : ∀ i ∈ I, ((L i).card : ℝ) ≤ K) : (S.ncard : ℝ) ≤ I.card * K := by
  have hsub : S ⊆ ↑(I.biUnion L) := by simpa [Finset.coe_biUnion] using hS
  have h1 : S.ncard ≤ (I.biUnion L).card :=
    (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans_eq (Set.ncard_coe_finset _)
  have h2 : ((I.biUnion L).card : ℝ) ≤ ∑ i ∈ I, ((L i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc (S.ncard : ℝ) ≤ ((I.biUnion L).card : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2
    _ ≤ ∑ _i ∈ I, K := Finset.sum_le_sum hK
    _ = I.card * K := by simp

theorem visited_exists {γ : PathSpace d} {T : ℝ≥0} {t : ℝ} {u : Fin d → ℤ}
    (hu : u ∈ visitedSet (h1Walk T γ) 0 t) : ∃ s : ℝ≥0, s ≤ T ∧ γ s = u := by
  obtain ⟨r, -, rfl⟩ := hu
  exact ⟨min r.toNNReal T, min_le_right _ _, rfl⟩

/-- **ES22 Lemma 8.1, Step 2 (8.4).** No block of radius `r ≥ m₀` is heavy. -/
theorem h1_not_heavy {n : ℕ} (hn : 2 ≤ n) {T : ℝ≥0} {R : ℝ} {M m0 : ℕ} {γ : PathSpace d}
    {B : ℝ≥0 → Fin d → ℝ} (hg : H1Good n T R M m0 γ B) (hR : 0 ≤ R)
    (hM : (2 * R + 1) ^ d ≤ (M : ℝ) ^ (5 / 2 : ℝ))
    (hm2 : 2 * (n : ℝ) ^ 10 ≤ m0) (hm5 : (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) < m0)
    {t : ℝ} (_htT : t ≤ T) {r : ℝ} (hr : (m0 : ℝ) ≤ r) :
    ¬ IsHeavy (h1Walk T γ) 0 t (h1Walk T γ t) r := by
  rintro ⟨hr0, hheavy⟩
  have hrnn : 0 ≤ r := hr0.le
  set m := ⌊r⌋₊ with hmdef
  have hm : m0 ≤ m := Nat.le_floor hr
  have hmr : (m : ℝ) ≤ r := Nat.floor_le hrnn
  obtain ⟨sx, hsxT, hx⟩ : ∃ s : ℝ≥0, s ≤ T ∧ γ s = h1Walk T γ t :=
    ⟨min t.toNNReal T, min_le_right _ _, rfl⟩
  set x := h1Walk T γ t with hxdef
  have hxR : ‖x‖ < R := hx ▸ hg.far sx hsxT
  rw [ball_eq_floor _ hrnn] at hheavy
  set S := {v : Fin d → ℤ | ‖v - x‖ ≤ (m : ℝ)} ∩ visitedSet (h1Walk T γ) 0 t with hS
  have hpow : (m : ℝ) ^ (5 / 2 : ℝ) ≤ r ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hmr (by norm_num)
  suffices hlt : (S.ncard : ℝ) < (m : ℝ) ^ (5 / 2 : ℝ) by linarith
  rcases lt_or_ge M m with hMm | hMm
  · have hsub : S ⊆ ↑(ballBox d R) := fun v hv => by
      obtain ⟨s, hsT, rfl⟩ := visited_exists hv.2
      exact Finset.mem_coe.2 (mem_ballBox (hg.far s hsT))
    have h1 : S.ncard ≤ (ballBox d R).card :=
      (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans_eq (Set.ncard_coe_finset _)
    calc (S.ncard : ℝ) ≤ (ballBox d R).card := by exact_mod_cast h1
      _ ≤ (2 * R + 1) ^ d := card_ballBox d hR
      _ ≤ (M : ℝ) ^ (5 / 2 : ℝ) := hM
      _ < (m : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_lt_rpow (Nat.cast_nonneg _) (by exact_mod_cast hMm) (by norm_num)
  · obtain ⟨hfin, hcard⟩ := hg.occ x hxR m hm hMm
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hn10 : (3 : ℝ) ≤ (n : ℝ) ^ 10 :=
      calc (3 : ℝ) ≤ 2 ^ 10 := by norm_num
        _ ≤ (n : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hn2 10
    have hn5 : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 10 := pow_le_pow_right₀ hn1 (by norm_num)
    have hsub : S ⊆ ⋃ i ∈ hfin.toFinset, (↑(latNear (Real.sqrt 2 • B (i : ℝ≥0))
        (2 * (n : ℝ) ^ 10)) : Set (Fin d → ℤ)) := by
      intro v hv
      obtain ⟨s, hsT, rfl⟩ := visited_exists hv.2
      set i : ℕ := ⌊(s : ℝ)⌋₊ with hi
      have hi_le : (i : ℝ≥0) ≤ s := by
        rw [← NNReal.coe_le_coe]
        have := Nat.floor_le s.2
        simpa [hi] using this
      have hi_lt : (s : ℝ) < i + 1 := Nat.lt_floor_add_one _
      have hsub1 : s - (i : ℝ≥0) ≤ 1 := by
        rw [← NNReal.coe_le_coe, NNReal.coe_sub hi_le]
        simp only [NNReal.coe_natCast, NNReal.coe_one]
        linarith
      have f := hg.fast i s hi_le hsT hsub1
      have c := hg.cpl i (hi_le.trans hsT)
      have key : ‖latR (γ s) - Real.sqrt 2 • B (i : ℝ≥0)‖ < 2 * (n : ℝ) ^ 10 := by
        calc _ = ‖(latR (γ s) - latR (γ i)) + (latR (γ i) - Real.sqrt 2 • B (i : ℝ≥0))‖ := by
              congr 1; abel
          _ ≤ ‖latR (γ s) - latR (γ i)‖ + ‖latR (γ i) - Real.sqrt 2 • B (i : ℝ≥0)‖ :=
              norm_add_le _ _
          _ < _ := by rw [norm_latR_sub]; linarith
      refine Set.mem_biUnion (x := i) ?_ ?_
      · rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        show ‖Real.sqrt 2 • B (i : ℝ≥0) - latR x‖ ≤ 2 * (m : ℝ)
        have hv1 : ‖γ s - x‖ ≤ (m : ℝ) := hv.1
        have hm' : (m0 : ℝ) ≤ m := by exact_mod_cast hm
        calc ‖Real.sqrt 2 • B (i : ℝ≥0) - latR x‖
            ≤ ‖Real.sqrt 2 • B (i : ℝ≥0) - latR (γ s)‖ + ‖latR (γ s) - latR x‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * (n : ℝ) ^ 10 + m := by
              rw [norm_sub_rev, norm_latR_sub]; linarith
          _ ≤ 2 * (m : ℝ) := by linarith
      · exact Finset.mem_coe.2 (mem_latNear key)
    have hK : ∀ i ∈ hfin.toFinset, ((latNear (Real.sqrt 2 • B (i : ℝ≥0))
        (2 * (n : ℝ) ^ 10)).card : ℝ) ≤ (5 * (n : ℝ) ^ 10) ^ d := fun i _ =>
      (card_latNear _ (by positivity)).trans
        (pow_le_pow_left₀ (by positivity) (by linarith) d)
    have hcov := ncard_le_of_cover S hfin.toFinset
      (fun i => latNear (Real.sqrt 2 • B (i : ℝ≥0)) (2 * (n : ℝ) ^ 10)) hsub hK
    have hcardE : (hfin.toFinset.card : ℝ) = ((occSet B x m).ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
    set A : ℝ := 5 * (n : ℝ) ^ 10 with hA
    have hA0 : 0 < A := by positivity
    have hm0pos : (0 : ℝ) < m0 := lt_of_le_of_lt (by positivity) hm5
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hm0pos (by exact_mod_cast hm)
    have hAd : A ^ d < (m : ℝ) ^ (2 / 5 : ℝ) := by
      have h1 : (A ^ ((5 * d : ℝ) / 2)) ^ (2 / 5 : ℝ) < (m0 : ℝ) ^ (2 / 5 : ℝ) :=
        Real.rpow_lt_rpow (by positivity) hm5 (by norm_num)
      have h2 : (A ^ ((5 * d : ℝ) / 2)) ^ (2 / 5 : ℝ) = A ^ d := by
        rw [← Real.rpow_mul hA0.le]
        have : (5 * d : ℝ) / 2 * (2 / 5) = d := by ring
        rw [this, Real.rpow_natCast]
      have h3 : (m0 : ℝ) ^ (2 / 5 : ℝ) ≤ (m : ℝ) ^ (2 / 5 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)
      rw [h2] at h1
      exact h1.trans_le h3
    calc (S.ncard : ℝ) ≤ hfin.toFinset.card * A ^ d := hcov
      _ = ((occSet B x m).ncard : ℝ) * A ^ d := by rw [hcardE]
      _ ≤ (m : ℝ) ^ (21 / 10 : ℝ) * A ^ d := by gcongr
      _ < (m : ℝ) ^ (21 / 10 : ℝ) * (m : ℝ) ^ (2 / 5 : ℝ) :=
          mul_lt_mul_of_pos_left hAd (by positivity)
      _ = (m : ℝ) ^ (5 / 2 : ℝ) := by rw [← Real.rpow_add hmpos]; norm_num

end ElboimSly.Paper

end
