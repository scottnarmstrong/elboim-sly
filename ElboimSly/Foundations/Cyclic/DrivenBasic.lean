/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenDef
import Mathlib

/-!
# The driven construction: left values and the rules

Basic facts about `leftVal`, jump sets and the rules (D1)--(D3).
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {f g : ℝ≥0 → Fin d → ℤ}

theorem leftVal_eq_of_eventually {s : ℝ≥0} (hs : 0 < s) {c : Fin d → ℤ}
    (h : ∀ᶠ u in 𝓝[<] s, f u = c) : leftVal f s = c := by
  have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  exact (tendsto_nhds_of_eventually_eq h).limUnder_eq

theorem leftVal_congr {s : ℝ≥0} (h : ∀ u < s, f u = g u) : leftVal f s = leftVal g s := by
  unfold leftVal limUnder
  congr 1
  exact Filter.map_congr (Filter.eventually_of_mem self_mem_nhdsWithin h)

theorem mem_CDisc_congr {s : ℝ≥0} (h : ∀ u ≤ s, f u = g u) : s ∈ CDisc f ↔ s ∈ CDisc g := by
  unfold CDisc
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => not_congr (Filter.eventually_congr ?_)
  filter_upwards [self_mem_nhdsWithin (s := Set.Iio s)] with u hu
  rw [h u hu.le, h s le_rfl]

theorem IsRegPath.exists_left_const (hf : IsRegPath f) {s : ℝ≥0} (hs : 0 < s) :
    ∃ c, ∀ᶠ u in 𝓝[<] s, f u = c := by
  classical
  have hF : (CDisc f ∩ Iio s).Finite := (hf.fin s).subset (fun r hr => ⟨hr.1, hr.2.le⟩)
  obtain ⟨t, hts, ht⟩ : ∃ t, t < s ∧ ∀ r ∈ CDisc f, t < r → r < s → False := by
    by_cases hne : (CDisc f ∩ Iio s).Nonempty
    · refine ⟨hF.toFinset.max' (by simpa using hne), ?_, fun r hr h1 h2 => ?_⟩
      · have hmem := hF.toFinset.max'_mem (by simpa using hne)
        simp only [Finite.mem_toFinset] at hmem
        exact hmem.2
      · exact absurd (hF.toFinset.le_max' r (by simpa using ⟨hr, h2⟩)) (not_le.mpr h1)
    · refine ⟨0, hs, fun r hr _ h2 => hne ⟨r, hr, h2⟩⟩
  obtain ⟨m, hm1, hm2⟩ := exists_between hts
  refine ⟨f m, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hts] with u hu
  rcases le_total u m with hum | hmu
  · exact (const_of_no_disc hf.rc hum (fun r hr hd => ht r hd (hu.1.trans_le hr.1.le) (hr.2.trans_lt hm2))
      m ⟨hum, le_rfl⟩).symm
  · exact const_of_no_disc hf.rc hmu (fun r hr hd => ht r hd (hm1.trans_le hr.1.le)
      (hr.2.trans_lt hu.2)) u ⟨hmu, le_rfl⟩ |>.symm ▸ rfl

theorem IsRegPath.eventually_leftVal (hf : IsRegPath f) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᶠ u in 𝓝[<] s, f u = leftVal f s := by
  obtain ⟨c, hc⟩ := hf.exists_left_const hs
  rwa [leftVal_eq_of_eventually hs hc]

theorem IsRegPath.mem_CDisc_iff (hf : IsRegPath f) {s : ℝ≥0} :
    s ∈ CDisc f ↔ 0 < s ∧ leftVal f s ≠ f s := by
  constructor
  · intro h
    refine ⟨h.1, fun heq => h.2 ?_⟩
    have := hf.eventually_leftVal h.1
    rwa [heq] at this
  · rintro ⟨hs, hne⟩
    refine ⟨hs, fun h => hne ?_⟩
    exact leftVal_eq_of_eventually hs h

theorem IsRegPath.leftVal_eq_of_not_mem (hf : IsRegPath f) {s : ℝ≥0} (hs : 0 < s)
    (h : s ∉ CDisc f) : leftVal f s = f s := by
  by_contra hne
  exact h (hf.mem_CDisc_iff.2 ⟨hs, hne⟩)

theorem isUnitStep_neg {v : Fin d → ℤ} : IsUnitStep (-v) ↔ IsUnitStep v := by
  simp [IsUnitStep]

variable (β : ℝ≥0)

theorem drivenD123_iff (x p : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    (DrivenD1 β p t ∧ DrivenD2 β x p t ∧ DrivenD3 β x p t) ↔
      p t = drivenRuleVal β x p t := by
  classical
  by_cases hex : ∃ k, ForcedAt β p t k
  · rw [drivenRuleVal, ite_eq_left hex]
    have hD2 : DrivenD2 β x p t := fun h => absurd hex (by push Not; exact h)
    have hD3 : DrivenD3 β x p t := fun h => absurd hex (by push Not; exact h)
    simp only [hD2, hD3, and_true]
    have hmem : sInf {k | ForcedAt β p t k} ∈ {k | ForcedAt β p t k} := Nat.sInf_mem hex
    constructor
    · intro h1
      exact h1 _ hmem (fun k' hk' hF => Nat.notMem_of_lt_sInf hk' hF)
    · intro h k hk hmin
      have : k = sInf {k | ForcedAt β p t k} := by
        refine le_antisymm ?_ (Nat.sInf_le hk)
        by_contra hlt
        exact hmin _ (not_le.mp hlt) hmem
      rw [this]; exact h
  · have hD1 : DrivenD1 β p t := fun k hk => absurd ⟨k, hk⟩ hex
    have hno : ∀ k, ¬ ForcedAt β p t k := fun k hk => hex ⟨k, hk⟩
    rw [drivenRuleVal, ite_eq_right hex]
    by_cases hx : t ∈ CDisc x
    · rw [ite_eq_left hx]
      have hD3 : DrivenD3 β x p t := fun _ h => absurd hx h
      exact ⟨fun h => h.2.1 hno hx, fun h => ⟨hD1, fun _ _ => h, hD3⟩⟩
    · rw [ite_eq_right hx]
      have hD2 : DrivenD2 β x p t := fun _ h => absurd h hx
      exact ⟨fun h => h.2.2 hno hx, fun h => ⟨hD1, hD2, fun _ _ => h⟩⟩

theorem delayIdx_lt {t : ℝ≥0} (hβ : 0 < β) {k : ℕ} (hk : IsDelayIdx β t k) : t - k * β < t := by
  have hk1 : (0 : ℝ≥0) < k * β := mul_pos (by exact_mod_cast hk.1) hβ
  exact tsub_lt_self (hk1.trans_le hk.2) hk1

theorem drivenRuleVal_congr {x y p q : ℝ≥0 → Fin d → ℤ} {t : ℝ≥0} (hβ : 0 < β)
    (hx : ∀ s ≤ t, x s = y s) (hp : ∀ s < t, p s = q s) :
    drivenRuleVal β x p t = drivenRuleVal β y q t := by
  classical
  have hL : leftVal p t = leftVal q t := leftVal_congr hp
  have hLx : leftVal x t = leftVal y t := leftVal_congr fun u hu => hx u hu.le
  have hX : t ∈ CDisc x ↔ t ∈ CDisc y := mem_CDisc_congr hx
  have hpk : ∀ k, IsDelayIdx β t k → p (t - k * β) = q (t - k * β) :=
    fun k hk => hp _ (delayIdx_lt β hβ hk)
  have hF : ∀ k, ForcedAt β p t k ↔ ForcedAt β q t k := by
    intro k
    unfold ForcedAt
    constructor
    · rintro ⟨hk, h1, h2⟩
      refine ⟨hk, (mem_CDisc_congr (fun u hu => hp u (hu.trans_lt (delayIdx_lt β hβ hk)))).1 h1,
        ?_⟩
      rw [← hpk k hk, ← hL]; exact h2
    · rintro ⟨hk, h1, h2⟩
      refine ⟨hk, (mem_CDisc_congr (fun u hu => hp u (hu.trans_lt (delayIdx_lt β hβ hk)))).2 h1,
        ?_⟩
      rw [hpk k hk, hL]; exact h2
  have hset : {k | ForcedAt β p t k} = {k | ForcedAt β q t k} := Set.ext hF
  have hT : TakenAt β x p t ↔ TakenAt β y q t := by
    unfold TakenAt
    refine forall_congr' fun k => imp_congr_right fun hk => ?_
    rw [hL, hLx, hpk k hk, hx t le_rfl]
  by_cases hex : ∃ k, ForcedAt β p t k
  · have hex' : ∃ k, ForcedAt β q t k := by
      obtain ⟨k, hk⟩ := hex; exact ⟨k, (hF k).1 hk⟩
    rw [drivenRuleVal, ite_eq_left hex, drivenRuleVal, ite_eq_left hex', ← hset]
    exact leftVal_congr fun u hu => hp u (hu.trans_le tsub_le_self)
  · have hex' : ¬ ∃ k, ForcedAt β q t k := by
      rintro ⟨k, hk⟩; exact hex ⟨k, (hF k).2 hk⟩
    rw [drivenRuleVal, ite_eq_right hex, drivenRuleVal, ite_eq_right hex']
    simp only [hX, hT, hL, hLx, hx t le_rfl]

end ElboimSly.Cyclic

end
