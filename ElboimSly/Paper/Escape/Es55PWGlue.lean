/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.PlanFreeze
public import ElboimSly.Paper.Escape.Es55Rat
public import ElboimSly.Foundations.Cyclic.CycRegenRc
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the glued continuation is right-continuous and agrees with its first piece

ES22 Lemma 5.5, Step 1 ("Agreement on `E₅₆ ∩ E₀`").

* `contGlue_rc`: the glue of right-continuous pieces is right-continuous;
* `walkMap_rc`: `walkMap ν` is right-continuous (for every `ν`);
* `contGlue_lt_treg`: if the glued path does not vanish at any `s ∈ [b, t]` then the first piece
  has not closed by time `t`, hence the glued path is the first piece on `[0, t]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic

variable {d : ℕ}

theorem contGlue_sigma_ge (b : ℝ≥0) (p : ℝ≥0 → Fin d → ℤ) (q : ℕ → ℝ≥0 → Fin d → ℤ) (n : ℕ) :
    (n : ℝ≥0∞) * b ≤ partialSums (fun k => pathTreg b (contPieces p q k)) n := by
  induction n with
  | zero => simp [partialSums]
  | succ n ih =>
    rw [partialSums_succ, Nat.cast_succ, add_mul, one_mul]
    exact add_le_add ih (le_pathTreg _ _)

theorem contGlue_exists_count {b : ℝ≥0} (hb : 0 < b) (p : ℝ≥0 → Fin d → ℤ)
    (q : ℕ → ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    ∃ n, partialSums (fun k => pathTreg b (contPieces p q k)) n ≤ t ∧
      (t : ℝ≥0∞) < partialSums (fun k => pathTreg b (contPieces p q k)) (n + 1) := by
  classical
  set σ := partialSums fun k => pathTreg b (contPieces p q k) with hσ
  have hex : ∃ n : ℕ, (t : ℝ≥0∞) < σ (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / b)
    refine ⟨n, lt_of_lt_of_le ?_ (contGlue_sigma_ge b p q (n + 1))⟩
    have : t < ((n + 1 : ℕ) : ℝ≥0) * b := by
      have h := (div_lt_iff₀ hb).1 hn
      calc t < n * b := h
        _ ≤ _ := by push_cast; nlinarith
    exact_mod_cast this
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simp [hσ, partialSums]
  · have := Nat.find_min hex (Nat.pred_lt h.ne')
    rw [Nat.pred_eq_sub_one, Nat.sub_add_cancel h] at this
    exact not_lt.1 this

theorem contGlue_rc {b : ℝ≥0} (hb : 0 < b) {p : ℝ≥0 → Fin d → ℤ} {q : ℕ → ℝ≥0 → Fin d → ℤ}
    (hp : ∀ s, ∀ᶠ u in 𝓝[≥] s, p u = p s) (hq : ∀ k s, ∀ᶠ u in 𝓝[≥] s, q k u = q k s)
    (t : ℝ≥0) : ∀ᶠ u in 𝓝[≥] t, contGlue b p q u = contGlue b p q t := by
  classical
  set σ := partialSums fun k => pathTreg b (contPieces p q k) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  obtain ⟨n, h1, h2⟩ := contGlue_exists_count hb p q t
  have hpc : ∀ k s, ∀ᶠ u in 𝓝[≥] s, contPieces p q k u = contPieces p q k s := by
    intro k
    cases k with
    | zero => exact hp
    | succ k => exact hq k
  set c := (σ n).toNNReal with hc
  have hlt : ∀ᶠ u : ℝ≥0 in 𝓝[≥] t, (u : ℝ≥0∞) < σ (n + 1) :=
    nhdsWithin_le_nhds (ENNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds h2) :
      ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : ℝ≥0∞) < σ (n + 1))
  have hrc : ∀ᶠ u in 𝓝[≥] t, contPieces p q n (u - c) = contPieces p q n (t - c) := by
    have ht : Tendsto (fun u : ℝ≥0 => u - c) (𝓝[≥] t) (𝓝[≥] (t - c)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u (hu : t ≤ u) => (tsub_le_tsub_right hu c : t - c ≤ u - c)⟩
    exact ht.eventually (hpc n (t - c))
  filter_upwards [hlt, hrc, self_mem_nhdsWithin] with u hu hr hge'
  have hσu : σ n ≤ u := le_trans h1 (by exact_mod_cast (show t ≤ u from hge'))
  have hc1 : gluedCount σ u = n := gluedCount_eq hm hσu hu
  have hc2 : gluedCount σ t = n := gluedCount_eq hm h1 h2
  unfold contGlue gluedWalk
  rw [← hσ, hc1, hc2]
  exact hr

theorem walkMap_rc {β : ℝ} [Fact (0 < β)] (ν : Measure (RingSpace d β)) (s : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] s, walkMap ν u = walkMap ν s := by
  classical
  have hg : Good (if Good ν then ν else 0) := by split_ifs with h; exacts [h, good_zero]
  obtain ⟨ε, hε, hc⟩ := cycWalk_const_near hg (r := (s : ℝ)) s.2
  have hlt : s < s + ε.toNNReal := by
    have : (0 : ℝ≥0) < ε.toNNReal := Real.toNNReal_pos.2 hε
    exact lt_add_of_pos_right _ this
  filter_upwards [Ico_mem_nhdsGE hlt] with u hu
  have hu1 : (s : ℝ) ≤ u := by exact_mod_cast hu.1
  have hu2 : (u : ℝ) < s + ε := by
    have := (NNReal.coe_lt_coe.2 hu.2)
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
  exact hc u hu1 hu2

/-- If the glued path has no zero in `[b, t]`, the first piece has not closed by time `t`, and the
glued path is the first piece on `[0, t]`. -/
theorem contGlue_lt_treg {b : ℝ≥0} (hb : 0 < b) (p : ℝ≥0 → Fin d → ℤ)
    (q : ℕ → ℝ≥0 → Fin d → ℤ) (hq : ∀ k, q k 0 = 0) {t : ℝ≥0}
    (h : ∀ s : ℝ≥0, b ≤ s → s ≤ t → contGlue b p q s ≠ 0) :
    (t : ℝ≥0∞) < pathTreg b p ∧ ∀ s : ℝ≥0, s ≤ t → contGlue b p q s = p s := by
  have hlt : (t : ℝ≥0∞) < pathTreg b p := by
    by_contra hle
    rw [not_lt] at hle
    have hfin : pathTreg b p < ⊤ := lt_of_le_of_lt hle ENNReal.coe_lt_top
    obtain ⟨j, hj1, hj, hz⟩ := pathTreg_exists hfin
    have hjb : (j : ℝ≥0) * b ≤ t := by rw [hj] at hle; exact_mod_cast hle
    have hag := contGlue_agree hb p q hq (r := (j : ℝ≥0) * b) (by rw [hj])
    exact h _ (le_mul_of_one_le_left zero_le (by exact_mod_cast hj1)) hjb (by rw [hag, hz])
  exact ⟨hlt, fun s hs => contGlue_agree hb p q hq (le_trans (by exact_mod_cast hs) hlt.le)⟩

end ElboimSly.Paper.Escape
