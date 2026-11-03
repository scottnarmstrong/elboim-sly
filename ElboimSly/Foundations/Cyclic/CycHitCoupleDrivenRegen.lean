/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDrivenCouple
public import Mathlib

/-!
# ES22 Lemma 2.1: Lemma 2.1 for the regenerated driven walk

ES22 Lemma 2.1 (ES22 §2, ES22 §2, ES22 §7).

Formalized here (pathwise parts):

* (a) `drivenPieces_mem_cycCF`: `x^{(i)} ∈ cycCF` whenever `σ_{i-1} < ∞`;
* (b) `cyc_hit_couple_driven_regen_b`: the pathwise coupling;
* (c) `cyc_hit_couple_driven_regen_c`: one driver, two histories.

Not formalized: (d) measurability and (e) the law form, which needs the constructions of the regenerated walk
(equality in law) and the strong Markov property of the SRW.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

/-- **ES22 Lemma 2.1 (b)**, the pathwise coupling. Let `x ∈ cycCF`, `V = W^x_reg`,
`t ≥ 0`. Then `t_hit(t) = ∞` if `t = α(t)`; `t_hit(t) ≤ σ_{𝔑_t + 1}` if `t > α(t)`; and
`V(t + s) - V(t) = W^{x_t}_reg(s)` for all `s ∈ [0, t_hit(t) - t]`. -/
theorem cyc_hit_couple_driven_regen_b (hb : 0 < b) (hx : x ∈ CycCF b) (t : ℝ≥0) :
    (t = drivenRegenAlpha b x t → drivenThit b x t = ⊤) ∧
    (drivenRegenAlpha b x t < t →
      drivenThit b x t ≤ drivenSigma b x (gluedCount (drivenSigma b x) t + 1)) ∧
    ∀ s : ℝ≥0, ((t + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t →
      drivenRegenFrom b x (t + s) - drivenRegenFrom b x t =
        drivenRegenFrom b (shiftPath x t) s := by
  obtain ⟨hσ1, hσ2⟩ := gluedCount_spec' hb x t
  set n := gluedCount (drivenSigma b x) t with hn
  have hnt : drivenSigma b x n < ⊤ := lt_of_le_of_lt hσ1 ENNReal.coe_lt_top
  set a := (drivenSigma b x n).toNNReal with ha
  have hna : drivenSigma b x n = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hnt.ne).symm
  have hat : a ≤ t := by rw [hna] at hσ1; exact_mod_cast hσ1
  have hta : a + (t - a) = t := add_tsub_cancel_of_le hat
  have hα : drivenRegenAlpha b x t = a := rfl
  have aux := regen_couple_aux hb hx hnt (t' := t - a) (by rw [hta]; exact hσ2)
    (by rw [hta]; exact hα)
  rw [hta] at aux
  obtain ⟨h1, h2, h3⟩ := aux
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, h3⟩
  · rw [hα] at h
    exact tsub_eq_zero_of_le h.le
  · rw [hα] at h
    exact tsub_pos_of_lt h

/-- The concatenation of `W|_{[0, s₁]}` and `W₂`: `W̃(s) = W(s)` for `s ≤ s₁`, `W(s₁) + W₂(s - s₁)`
after. -/
noncomputable def concatPath (W W₂ : ℝ≥0 → Fin d → ℤ) (s₁ : ℝ≥0) (s : ℝ≥0) : Fin d → ℤ :=
  if s ≤ s₁ then W s else W s₁ + W₂ (s - s₁)

theorem concatPath_of_le {W W₂ : ℝ≥0 → Fin d → ℤ} {s₁ u : ℝ≥0} (h0 : W₂ 0 = 0) (hu : s₁ ≤ u) :
    concatPath W W₂ s₁ u = W s₁ + W₂ (u - s₁) := by
  unfold concatPath
  split_ifs with h
  · have : u = s₁ := le_antisymm h hu
    subst this
    simp [h0]
  · rfl

theorem drivenRegenFrom_zero (hb : 0 < b) {y : ℝ≥0 → Fin d → ℤ} (hy : IsRegPath y) :
    drivenRegenFrom b y 0 = 0 := by
  rw [drivenRegenFrom_eq_walk_of_le hb hy (by simp), drivenWalk_zero hy hb]

/-- **ES22 Lemma 2.1 (c)**, one driver, two histories. -/
theorem cyc_hit_couple_driven_regen_c (hb : 0 < b) (hx : x ∈ CycCF b) {s₁ : ℝ≥0}
    (hx₁ : shiftPath x s₁ ∈ CycCF b) {t : ℝ≥0} (ht : s₁ ≤ t) :
    ∀ s : ℝ≥0, ((t + s : ℝ≥0) : ℝ≥0∞) ≤
        min (drivenThit b x t) (s₁ + drivenThit b (shiftPath x s₁) (t - s₁)) →
      drivenRegenFrom b x (t + s) - drivenRegenFrom b x t =
          concatPath (drivenRegenFrom b x) (drivenRegenFrom b (shiftPath x s₁)) s₁ (t + s) -
            concatPath (drivenRegenFrom b x) (drivenRegenFrom b (shiftPath x s₁)) s₁ t ∧
        concatPath (drivenRegenFrom b x) (drivenRegenFrom b (shiftPath x s₁)) s₁ (t + s) -
            concatPath (drivenRegenFrom b x) (drivenRegenFrom b (shiftPath x s₁)) s₁ t =
          drivenRegenFrom b (shiftPath x t) s := by
  intro s hs
  have hs1 := le_min_iff.1 hs
  have hb1 := (cyc_hit_couple_driven_regen_b hb hx t).2.2 s hs1.1
  have e : (t + s : ℝ≥0) = s₁ + ((t - s₁) + s) := by rw [← add_assoc, add_tsub_cancel_of_le ht]
  have hb2 := (cyc_hit_couple_driven_regen_b hb hx₁ (t - s₁)).2.2 s (by
    have h := hs1.2
    rw [e] at h
    push_cast at h
    exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).1 h)
  have hsh : shiftPath (shiftPath x s₁) (t - s₁) = shiftPath x t := by
    rw [shiftPath_add, add_tsub_cancel_of_le ht]
  rw [hsh] at hb2
  have h0 := drivenRegenFrom_zero hb hx₁.1.toIsRegPath
  have hts : s₁ ≤ t + s := ht.trans le_self_add
  rw [concatPath_of_le h0 hts, concatPath_of_le h0 ht]
  have e2 : t + s - s₁ = (t - s₁) + s := (tsub_add_eq_add_tsub ht).symm
  rw [e2]
  have hfin : drivenRegenFrom b x s₁ + drivenRegenFrom b (shiftPath x s₁) (t - s₁ + s) -
      (drivenRegenFrom b x s₁ + drivenRegenFrom b (shiftPath x s₁) (t - s₁)) =
      drivenRegenFrom b (shiftPath x t) s := by
    rw [← hb2]; abel
  exact ⟨hb1.trans hfin.symm, hfin⟩

end ElboimSly.Cyclic

end
