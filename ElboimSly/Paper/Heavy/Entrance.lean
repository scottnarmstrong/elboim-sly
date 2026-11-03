/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Attained
public import ElboimSly.Paper.Heavy.Blocks
public import ElboimSly.Paper.Heavy.Thresholds

/-!
# Entrance times `s_i(B)`, the stopping time `τ'`, and entrances into sub-blocks

Entrance times s_i(B) and τ'(B); The stopping time τ' (ES22 §6, ES22 §6) and entrances into sub-blocks
(ES22 §6, ES22 §6).

For a path `w`, `j ≤ m` and the block `B = heavyBlock m ι`:
* `heavyEntrances w j m ι = {ξ_{B''} : B'' ∈ ℬ_j, B'' ⊆ B}` (`ℰ_B`);
* `heavyEntSeq w j m D ι i = s_i(B)` with spacing `D`: `s_0 = ξ_B`,
  `s_{i+1} = min {x ∈ ℰ_B : x ≥ s_i + D}` (`sInf` in `[0, ∞]`, `inf ∅ = ∞`);
* `heavySi w n m ι i`: the same with `j = j_n` and `D = D_m = n² 4^m`;
* `heavyTauPrimeBlock d n w m ι = τ'(B) = s_{K_n}(B)` and `heavyTauPrime d t₀ n w = τ'(w)`.

Deviation D6: the minimum is over `x ≥ s_{i-1} + D_m`, as in the written proof.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

/-- The sub-block indices: `B'' = heavyBlock j ι' ⊆ heavyBlock m ι`. -/
def heavySubIdx (d j m : ℕ) (ι : Fin d → ℤ) : Set (Fin d → ℤ) :=
  {ι' | heavyBlock j ι' ⊆ heavyBlock m ι}

/-- `ℰ_B = {ξ_{B''} : B'' ∈ ℬ_j, B'' ⊆ B}`. -/
noncomputable def heavyEntrances (w : ℝ → Fin d → ℤ) (j m : ℕ) (ι : Fin d → ℤ) : Set ℝ≥0∞ :=
  (fun ι' => entranceTime w (heavyBlock j ι')) '' heavySubIdx d j m ι

/-- Entrance times s_i(B) and τ'(B). The entrance times `s_i(B)` with spacing `D`. -/
noncomputable def heavyEntSeq (w : ℝ → Fin d → ℤ) (j m : ℕ) (D : ℝ≥0∞) (ι : Fin d → ℤ) :
    ℕ → ℝ≥0∞
  | 0 => entranceTime w (heavyBlock m ι)
  | i + 1 => sInf {x ∈ heavyEntrances w j m ι | heavyEntSeq w j m D ι i + D ≤ x}

/-- Entrance times s_i(B) and τ'(B). `s_i(B)` with `j = j_n` and spacing `D_m = n² 4^m`. -/
noncomputable def heavySi (w : ℝ → Fin d → ℤ) (n m : ℕ) (ι : Fin d → ℤ) (i : ℕ) : ℝ≥0∞ :=
  heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι i

/-- Entrance times s_i(B) and τ'(B). `τ'(B) = s_{K_n}(B)`. -/
noncomputable def heavyTauPrimeBlock (d n : ℕ) (w : ℝ → Fin d → ℤ) (m : ℕ) (ι : Fin d → ℤ) :
    ℝ≥0∞ :=
  heavySi w n m ι (heavyTrials d n)

/-- The stopping time τ'. `τ'(w) = inf {τ'(B) : m ≥ m₀, B ∈ ℬ_m}`. -/
noncomputable def heavyTauPrime (d : ℕ) (t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  ⨅ (m : ℕ) (_ : heavyM0 d t₀ n ≤ m) (ι : Fin d → ℤ), heavyTauPrimeBlock d n w m ι

section seq

variable {w : ℝ → Fin d → ℤ} {j m : ℕ} {D : ℝ≥0∞} {ι : Fin d → ℤ}

theorem heavyEntSeq_succ_ge (i : ℕ) :
    heavyEntSeq w j m D ι i + D ≤ heavyEntSeq w j m D ι (i + 1) := by
  show _ ≤ sInf _
  exact le_sInf fun x hx => hx.2

theorem heavyEntSeq_mono : Monotone (heavyEntSeq w j m D ι) :=
  monotone_nat_of_le_succ fun i => le_self_add.trans (heavyEntSeq_succ_ge i)

theorem entranceTime_mono {A B : Set (Fin d → ℤ)} (h : A ⊆ B) (w : ℝ → Fin d → ℤ) :
    entranceTime w B ≤ entranceTime w A :=
  iInf₂_mono' fun t ht => ⟨t, ⟨ht.1, h ht.2⟩, le_rfl⟩

/-- Entrances into sub-blocks, first part. -/
theorem heavyEntSeq_entrance {K : ℕ} {ι' : Fin d → ℤ} {ξ : ℝ≥0∞}
    (hsub : ι' ∈ heavySubIdx d j m ι) (hξ : ξ = entranceTime w (heavyBlock j ι'))
    {t : ℝ≥0∞} (hξt : ξ ≤ t) (ht : t < heavyEntSeq w j m D ι K) :
    ∃ i < K, heavyEntSeq w j m D ι i ≤ ξ ∧ ξ < heavyEntSeq w j m D ι i + D := by
  set s := heavyEntSeq w j m D ι with hs
  have h0 : s 0 ≤ ξ := by
    show entranceTime w (heavyBlock m ι) ≤ ξ
    rw [hξ]; exact entranceTime_mono hsub w
  have hK : ¬ s K ≤ ξ := fun h => absurd (lt_of_le_of_lt (hξt.trans' h) ht) (lt_irrefl _)
  classical
  set P : ℕ → Prop := fun ℓ => s ℓ ≤ ξ with hP
  set i := Nat.findGreatest P K with hi
  have hPi : P i := Nat.findGreatest_spec (P := P) (Nat.zero_le K) h0
  have hiK : i ≤ K := Nat.findGreatest_le K
  have hiK' : i < K := lt_of_le_of_ne hiK fun h => hK (h ▸ hPi)
  refine ⟨i, hiK', hPi, ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : ξ ∈ {x ∈ heavyEntrances w j m ι | s i + D ≤ x} :=
    ⟨⟨ι', hsub, hξ.symm⟩, hcon⟩
  have : s (i + 1) ≤ ξ := sInf_le hmem
  have h2 : i + 1 ≤ Nat.findGreatest P K := Nat.le_findGreatest hiK' this
  omega

end seq


section attained

variable {w : ℝ → Fin d → ℤ}

/-- The first entrance time into `B` is attained by a real time. -/
theorem exists_entrance_real (hw : IsCyclicPath w) {B : Set (Fin d → ℤ)} {s : ℝ} (hs : 0 ≤ s)
    (hws : w s ∈ B) :
    ∃ s'' : ℝ, 0 ≤ s'' ∧ s'' ≤ s ∧ w s'' ∈ B ∧ entranceTime w B = ENNReal.ofReal s'' := by
  set S : Set ℝ := {t | 0 ≤ t ∧ w t ∈ B} with hS
  have hne : S.Nonempty := ⟨s, hs, hws⟩
  have hb : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have h0 : 0 ≤ sInf S := le_csInf hne fun t ht => ht.1
  have hmem : sInf S ∈ S := by
    by_contra hn
    have hnB : w (sInf S) ∉ B := fun h => hn ⟨h0, h⟩
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc _ h0)
    obtain ⟨t, ht, ht2⟩ := exists_lt_of_csInf_lt hne
      (show sInf S < sInf S + (u - sInf S) by linarith [mem_Ioi.1 hu])
    have : w t = w (sInf S) := hsub ⟨csInf_le hb ht, by linarith⟩
    exact hnB (this ▸ ht.2)
  refine ⟨sInf S, h0, csInf_le hb ⟨hs, hws⟩, hmem.2, ?_⟩
  unfold entranceTime
  apply le_antisymm
  · exact iInf₂_le (f := fun t (_ : t ∈ {t : ℝ | 0 ≤ t ∧ w t ∈ B}) => ENNReal.ofReal t) _ hmem
  · exact le_iInf₂ fun t ht => ENNReal.ofReal_le_ofReal (csInf_le hb ht)

theorem entranceTime_le_of_mem {B : Set (Fin d → ℤ)} {s : ℝ} (hs : 0 ≤ s) (hws : w s ∈ B) :
    entranceTime w B ≤ ENNReal.ofReal s :=
  iInf₂_le (f := fun t (_ : t ∈ {t : ℝ | 0 ≤ t ∧ w t ∈ B}) => ENNReal.ofReal t) s ⟨hs, hws⟩

variable {j m : ℕ} {D : ℝ≥0∞} {ι : Fin d → ℤ}

/-- Entrances into sub-blocks, consequence. Every visit to `B` at a time `s ≤ t < s_K(B)` is
preceded by an entrance `s''` into a sub-block, of the form `[s_i, s_i + D)`, in the same block of `ℬ_j`. -/
theorem heavy_entrance_conseq (hw : IsCyclicPath w) (hjm : j ≤ m) {K : ℕ} {t s : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < heavyEntSeq w j m D ι K)
    (hsB : w s ∈ heavyBlock m ι) :
    ∃ s'' : ℝ, 0 ≤ s'' ∧ s'' ≤ s ∧
      (∃ i < K, heavyEntSeq w j m D ι i ≤ ENNReal.ofReal s'' ∧
        ENNReal.ofReal s'' < heavyEntSeq w j m D ι i + D) ∧
      w s'' ∈ heavyBlock j (heavyBlockIdx j (w s)) := by
  set ι' := heavyBlockIdx j (w s) with hι'
  have hsubset : heavyBlock j ι' ⊆ heavyBlock m ι :=
    heavyBlock_refine hjm (mem_heavyBlock_idx j (w s)) hsB
  have hsub : ι' ∈ heavySubIdx d j m ι := hsubset
  obtain ⟨s'', h0, hle, hmem, heq⟩ := exists_entrance_real hw hs0 (mem_heavyBlock_idx j (w s))
  have hξt : entranceTime w (heavyBlock j ι') ≤ ENNReal.ofReal t :=
    (entranceTime_le_of_mem hs0 (mem_heavyBlock_idx j (w s))).trans
      (ENNReal.ofReal_le_ofReal hst)
  obtain ⟨i, hiK, hi1, hi2⟩ := heavyEntSeq_entrance (w := w) (D := D) hsub rfl hξt ht
  refine ⟨s'', h0, hle, ⟨i, hiK, heq ▸ hi1, heq ▸ hi2⟩, ?_⟩
  exact hmem

end attained

end ElboimSly.Paper
