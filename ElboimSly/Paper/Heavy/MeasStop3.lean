/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop2

/-!
# Stopping times `τ'(B)` and `τ'`

Measurability (a), (b).

* `iInf_attained_of_finite_sublevel`: an infimum with finite sublevel sets is attained when finite.
* `heavyTauPrimeBlock_sublevel_finite`: for `n ≥ 1`, only finitely many `(m, B)` have
  `τ'(B) ≤ T` (pathwise, for a cyclic path).
* `heavyTauPrime_attained`: `τ'(w) < ∞` implies `τ'(w) = τ'(B)` for some `(m, B)`.
* `AdaptedCyclic.isStoppingTime_heavyTauPrimeBlock`, `AdaptedCyclic.isStoppingTime_heavyTauPrime`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem iInf_attained_of_finite_sublevel {α : Type*} (g : α → ℝ≥0∞)
    (hfin : ∀ T : ℝ, 0 ≤ T → {p | g p ≤ ENNReal.ofReal T}.Finite) (h : ⨅ p, g p < ⊤) :
    ∃ p, g p = ⨅ p, g p := by
  have hex : ∃ T : ℝ, 0 ≤ T ∧ (⨅ p, g p) < ENNReal.ofReal T := by
    refine ⟨(⨅ p, g p).toReal + 1, by positivity, ?_⟩
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal h.ne]
    simpa using ENNReal.add_lt_add_left h.ne zero_lt_one
  obtain ⟨T, hT0, hT⟩ := hex
  obtain ⟨p0, hp0⟩ := iInf_lt_iff.1 hT
  set C := {p | g p ≤ ENNReal.ofReal T} with hC
  have hCne : (g '' C).Nonempty := ⟨g p0, p0, hp0.le, rfl⟩
  have hCfin : (g '' C).Finite := (hfin T hT0).image g
  obtain ⟨p1, hp1C, hp1⟩ := hCne.csInf_mem hCfin
  refine ⟨p1, le_antisymm ?_ (iInf_le g p1)⟩
  refine le_iInf fun p => ?_
  rw [hp1]
  by_cases hp : p ∈ C
  · exact sInf_le (show g p ∈ g '' C from ⟨p, hp, rfl⟩)
  · have : ENNReal.ofReal T < g p := not_le.1 hp
    exact (sInf_le (show g p0 ∈ g '' C from ⟨p0, hp0.le, rfl⟩)).trans (hp0.le.trans this.le)

theorem heavyTrials_pos {n : ℕ} (hn : 1 ≤ n) : 0 < heavyTrials d n := by
  unfold heavyTrials
  exact Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

theorem heavyD_pos {n : ℕ} (hn : 1 ≤ n) (m : ℕ) : 0 < heavyD n m := by
  unfold heavyD; positivity

variable {w : ℝ → Fin d → ℤ}

theorem heavyEntSeq_ge_D {j m : ℕ} {D : ℝ≥0∞} {ι : Fin d → ℤ} {K : ℕ} (hK : 0 < K) :
    D ≤ heavyEntSeq w j m D ι K := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  exact le_add_self.trans (heavyEntSeq_succ_ge i)

theorem heavyTauPrimeBlock_sublevel_finite (hw : IsCyclicPath w) {n : ℕ} (hn : 1 ≤ n)
    {T : ℝ} (hT : 0 ≤ T) :
    {p : ℕ × (Fin d → ℤ) | heavyTauPrimeBlock d n w p.1 p.2 ≤ ENNReal.ofReal T}.Finite := by
  have hV : (w '' Set.Icc 0 T).Finite := (hw.ncard_image_Icc_le le_rfl hT).1
  have hfin : (⋃ m ∈ Finset.range (⌈T⌉₊ + 1),
      (fun ι => (m, ι)) '' (heavyBlockIdx m '' (w '' Set.Icc 0 T))).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun m _ => (hV.image _).image _
  refine hfin.subset ?_
  rintro ⟨m, ι⟩ hp
  simp only [mem_ofPred_eq, heavyTauPrimeBlock, heavySi] at hp
  have hD : (heavyD n m : ℝ≥0∞) ≤ ENNReal.ofReal T :=
    (heavyEntSeq_ge_D (heavyTrials_pos (d := d) hn)).trans hp
  have hmT : (m : ℝ) ≤ T := by
    have h1 : ((heavyD n m : ℕ) : ℝ) ≤ T := by
      rw [← ENNReal.ofReal_natCast] at hD
      exact (ENNReal.ofReal_le_ofReal_iff hT).1 hD
    have h2 : (m : ℝ) < 4 ^ m := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
    have h3 : (4 : ℝ) ^ m ≤ (heavyD n m : ℕ) := by
      unfold heavyD
      have : (1 : ℝ) ≤ n ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
      push_cast
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]
    linarith
  have h0 : entranceTime w (heavyBlock m ι) ≤ ENNReal.ofReal T :=
    (heavyEntSeq_mono (Nat.zero_le (heavyTrials d n))).trans hp
  have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ heavyBlock m ι := by
    by_contra hno
    push Not at hno
    rw [entranceTime_eq_top_of_empty hno] at h0
    exact absurd h0 (by simp)
  obtain ⟨s, hs0, hsB⟩ := hne
  obtain ⟨s'', h0', -, hmem, heq⟩ := exists_entrance_real hw hs0 hsB
  rw [heq] at h0
  have hs''T : s'' ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 h0
  simp only [mem_iUnion, mem_image, Finset.mem_range]
  have hmc : m ≤ ⌈T⌉₊ := by exact_mod_cast hmT.trans (Nat.le_ceil T)
  refine ⟨m, Nat.lt_succ_of_le hmc, ι, ⟨w s'', ⟨s'', ⟨h0', hs''T⟩, rfl⟩,
    heavyBlock_eq_of_mem (mem_heavyBlock_idx m _) hmem⟩, rfl⟩

end ElboimSly.Paper
