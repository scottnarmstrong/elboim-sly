/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenBasic
import Mathlib

/-!
# Closing for the driven walk

Closing for the driven walk (a)--(e).

The lemma is proved for an arbitrary path `w` that is a solution of the rules (D1)--(D3) for the
driver `x` up to its closing time `τ = pathTreg β w` (`DrivenSol β x w`), assuming condition (i)
of `cycCF` for `x` (`hi`).  Existence of the driven walk is proved elsewhere.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- `w` solves (D1)--(D3) for the driver `x` at every `t ∈ (0, τ]`, `τ = pathTreg β w`. -/
structure DrivenSol (β : ℝ≥0) (x w : ℝ≥0 → Fin d → ℤ) : Prop where
  beta_pos : 0 < β
  reg : IsRegPath w
  zero : w 0 = 0
  rules : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ pathTreg β w →
    DrivenD1 β w t ∧ DrivenD2 β x w t ∧ DrivenD3 β x w t

/-- Arithmetic: `t - k₁β = (t - k₂β) + (k₂ - k₁)β`. -/
theorem sub_shift {t : ℝ≥0} {β : ℝ≥0} {k1 k2 : ℕ} (h12 : k1 ≤ k2) (h : (k2 : ℝ≥0) * β ≤ t) :
    t - k1 * β = (t - k2 * β) + ((k2 - k1 : ℕ) : ℝ≥0) * β := by
  have e : (k2 : ℝ≥0) * β = k1 * β + ((k2 - k1 : ℕ) : ℝ≥0) * β := by
    rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' h12]
  refine tsub_eq_of_eq_add ?_
  calc t = (t - k2 * β) + k2 * β := (tsub_add_cancel_of_le h).symm
    _ = (t - k2 * β) + (k1 * β + ((k2 - k1 : ℕ) : ℝ≥0) * β) := by rw [← e]
    _ = _ := by ring

theorem sub_add_of_delay {t β : ℝ≥0} {k : ℕ} (h : (k : ℝ≥0) * β ≤ t) : t - k * β + k * β = t :=
  tsub_add_cancel_of_le h

theorem class_nat {β : ℝ≥0} (hβ : 0 < β) {s s' t0 : ℝ≥0} {j j' : ℤ} (hlt : s < s')
    (hs : (s : ℝ) = t0 + j * β) (hs' : (s' : ℝ) = t0 + j' * β) :
    ∃ k : ℕ, 1 ≤ k ∧ s' = s + k * β := by
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ
  have hltr : (s : ℝ) < s' := by exact_mod_cast hlt
  have hpos : 0 < ((j' - j : ℤ) : ℝ) := by
    have : (0 : ℝ) < (j' - j : ℝ) * β := by
      have : (s' : ℝ) - s = (j' - j : ℝ) * β := by rw [hs, hs']; ring
      linarith
    have h2 : (0 : ℝ) < (j' - j : ℝ) := pos_of_mul_pos_left this hβr.le
    exact_mod_cast h2
  have hpos' : 0 < j' - j := by exact_mod_cast hpos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j' - j := ⟨_, Int.toNat_of_nonneg hpos'.le⟩
  refine ⟨k, by omega, ?_⟩
  apply NNReal.coe_injective
  have hkr : ((k : ℕ) : ℝ) = (j' : ℝ) - j := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at this
    linarith
  push_cast
  rw [hkr, hs, hs']
  ring

namespace DrivenSol

variable {β : ℝ≥0} {x w : ℝ≥0 → Fin d → ℤ} (S : DrivenSol β x w)

include S

theorem pos_of_forced {t : ℝ≥0} {k : ℕ} (hk : ForcedAt β w t k) : 0 < t := by
  have h1 : (0 : ℝ≥0) < k * β := mul_pos (by exact_mod_cast hk.1.1) S.beta_pos
  exact h1.trans_le hk.1.2

theorem forced_least {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathTreg β w) {k : ℕ}
    (hk : ForcedAt β w t k) : ∃ k0, ForcedAt β w t k0 ∧ w t = leftVal w (t - k0 * β) := by
  classical
  have hex : ∃ k, ForcedAt β w t k := ⟨k, hk⟩
  have hr := (S.rules t (S.pos_of_forced hk) ht).1
  exact ⟨Nat.find hex, Nat.find_spec hex,
    hr _ (Nat.find_spec hex) fun k' hk' => Nat.find_min hex hk'⟩

theorem forced_jump {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathTreg β w) {k : ℕ}
    (hk : ForcedAt β w t k) : t ∈ CDisc w := by
  obtain ⟨k0, hk0, hw⟩ := S.forced_least ht hk
  refine S.reg.mem_CDisc_iff.2 ⟨S.pos_of_forced hk, fun heq => ?_⟩
  have hj := (S.reg.mem_CDisc_iff.1 hk0.2.1).2
  apply hj
  rw [← hw, ← heq]
  exact hk0.2.2.symm

theorem jump_cases {t : ℝ≥0} (hj : t ∈ CDisc w) (ht : (t : ℝ≥0∞) ≤ pathTreg β w) :
    (∃ k, ForcedAt β w t k ∧ w t = leftVal w (t - k * β)) ∨
      (t ∈ CDisc x ∧ ∀ k, ¬ ForcedAt β w t k) := by
  by_cases hex : ∃ k, ForcedAt β w t k
  · obtain ⟨k, hk⟩ := hex
    exact Or.inl (S.forced_least ht hk)
  · right
    push Not at hex
    refine ⟨?_, hex⟩
    by_contra hx
    have h3 := (S.rules t hj.1 ht).2.2 hex hx
    exact (S.reg.mem_CDisc_iff.1 hj).2 h3.symm

/-- The jumps of a class `t0 + βℕ` are rooted at a jump of `x` and cross the same edge. -/
theorem root (_hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β) :
    ∀ t ∈ CDisc w, (t : ℝ≥0∞) ≤ pathTreg β w →
      ∃ (t0 : ℝ≥0) (j : ℕ), t0 ∈ CDisc x ∧ t = t0 + j * β ∧
        ({leftVal w t, w t} : Set (Fin d → ℤ)) = {leftVal w t0, w t0} := by
  have key : ∀ t ∈ CDisc w, (t : ℝ≥0∞) ≤ pathTreg β w →
      (∀ t' ∈ CDisc w, t' < t → ∃ (t0 : ℝ≥0) (j : ℕ), t0 ∈ CDisc x ∧ t' = t0 + j * β ∧
        ({leftVal w t', w t'} : Set (Fin d → ℤ)) = {leftVal w t0, w t0}) →
      ∃ (t0 : ℝ≥0) (j : ℕ), t0 ∈ CDisc x ∧ t = t0 + j * β ∧
        ({leftVal w t, w t} : Set (Fin d → ℤ)) = {leftVal w t0, w t0} := by
    intro t hj ht IH
    rcases S.jump_cases hj ht with ⟨k, hk, hwt⟩ | ⟨hx, _⟩
    · have hlt := delayIdx_lt β S.beta_pos hk.1
      obtain ⟨t0, j, h0, he, hedge⟩ :=
        IH (t - k * β) hk.2.1 hlt
      refine ⟨t0, j + k, h0, ?_, ?_⟩
      · calc t = (t - k * β) + k * β := (sub_add_of_delay hk.1.2).symm
          _ = t0 + j * β + k * β := by rw [he]
          _ = t0 + ((j + k : ℕ) : ℝ≥0) * β := by push_cast; ring
      · calc ({leftVal w t, w t} : Set (Fin d → ℤ))
            = {leftVal w (t - k * β), w (t - k * β)} := by
              rw [hwt, hk.2.2]; exact Set.pair_comm _ _
          _ = _ := hedge
    · exact ⟨t, 0, hx, by simp, rfl⟩
  intro t hj ht
  classical
  by_contra hP
  set C := {t' | t' ∈ CDisc w ∧ t' ≤ t ∧ (t' : ℝ≥0∞) ≤ pathTreg β w ∧
    ¬ ∃ (t0 : ℝ≥0) (j : ℕ), t0 ∈ CDisc x ∧ t' = t0 + j * β ∧
        ({leftVal w t', w t'} : Set (Fin d → ℤ)) = {leftVal w t0, w t0}} with hC
  have hfin : C.Finite := (S.reg.fin t).subset fun t ht => ⟨ht.1, ht.2.1⟩
  have hne : C.Nonempty := ⟨t, hj, le_rfl, ht, hP⟩
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image C id hfin hne
  refine ha.2.2.2 (key a ha.1 ha.2.2.1 fun t' ht' hlt => ?_)
  by_contra hPt
  have : t' ∈ C := ⟨ht', hlt.le.trans ha.2.1,
    (by exact_mod_cast hlt.le : (t' : ℝ≥0∞) ≤ a).trans ha.2.2.1, hPt⟩
  exact absurd (hmin t' this) (not_le.2 hlt)

omit S in
theorem root_eq (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t0 t0' : ℝ≥0} (h0 : t0 ∈ CDisc x) (h0' : t0' ∈ CDisc x) {a b : ℕ}
    (h : t0 + a * β = t0' + b * β) : t0 = t0' := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : t0 + a * β = (t0' + ((c + 1 : ℕ) : ℝ≥0) * β) + a * β := by
      rw [h]; push_cast; ring
    have h2 := add_right_cancel this
    exact absurd h2 (hi t0' h0' t0 h0 (c + 1) (by omega))
  · subst hab; exact add_right_cancel h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : t0' + b * β = (t0 + ((c + 1 : ℕ) : ℝ≥0) * β) + b * β := by
      rw [← h]; push_cast; ring
    have h2 := add_right_cancel this
    exact absurd h2 (hi t0 h0 t0' h0' (c + 1) (by omega))

/-- (a): jumps in one class cross one edge. -/
theorem edge_eq (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} {k : ℕ} (ht : t ∈ CDisc w) (ht' : t + k * β ∈ CDisc w)
    (hτ : ((t + k * β : ℝ≥0) : ℝ≥0∞) ≤ pathTreg β w) :
    ({leftVal w (t + k * β), w (t + k * β)} : Set (Fin d → ℤ)) = {leftVal w t, w t} := by
  have hτ0 : (t : ℝ≥0∞) ≤ pathTreg β w :=
    (by exact_mod_cast (le_self_add : t ≤ t + k * β) : (t : ℝ≥0∞) ≤ _).trans hτ
  obtain ⟨t0, j, h0, he, hed⟩ := S.root hi t ht hτ0
  obtain ⟨t0', j', h0', he', hed'⟩ := S.root hi _ ht' hτ
  have : t0 + ((j + k : ℕ) : ℝ≥0) * β = t0' + j' * β := by
    rw [← he']
    calc t0 + ((j + k : ℕ) : ℝ≥0) * β = (t0 + j * β) + k * β := by push_cast; ring
      _ = _ := by rw [← he]
  have := root_eq hi h0 h0' this
  subst this
  rw [hed, hed']

/-- (a), first part: classification of a jump of `w`. -/
theorem closing_a_cases (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (hj : t ∈ CDisc w) (ht : (t : ℝ≥0∞) ≤ pathTreg β w) :
    (t ∈ CDisc x ∧ ∀ k, IsDelayIdx β t k → t - k * β ∉ CDisc w) ∨
      (∃ k, IsDelayIdx β t k ∧ t - k * β ∈ CDisc w ∧ w t = leftVal w (t - k * β) ∧
        leftVal w t = w (t - k * β)) := by
  rcases S.jump_cases hj ht with ⟨k, hk, hwt⟩ | ⟨hx, hno⟩
  · exact Or.inr ⟨k, hk.1, hk.2.1, hwt, hk.2.2.symm⟩
  · left
    refine ⟨hx, fun k hk hjk => ?_⟩
    have hle : (((t - k * β : ℝ≥0)) : ℝ≥0∞) ≤ pathTreg β w :=
      (by exact_mod_cast (tsub_le_self : t - k * β ≤ t) : (_ : ℝ≥0∞) ≤ t).trans ht
    obtain ⟨t0, j, h0, he, _⟩ := S.root hi _ hjk hle
    have : t = t0 + ((j + k : ℕ) : ℝ≥0) * β := by
      calc t = (t - k * β) + k * β := (sub_add_of_delay hk.2).symm
        _ = _ := by rw [he]; push_cast; ring
    exact hi t0 h0 t hx (j + k) (by have := hk.1; omega) this

/-- (a): a jump with no earlier jump in its class is a (D2) jump of `x`. -/
theorem closing_a_earliest
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (hj : t ∈ CDisc w) (ht : (t : ℝ≥0∞) ≤ pathTreg β w)
    (hno : ∀ k, IsDelayIdx β t k → t - k * β ∉ CDisc w) : t ∈ CDisc x := by
  rcases S.closing_a_cases hi hj ht with ⟨hx, _⟩ | ⟨k, hk, hjk, _⟩
  · exact hx
  · exact absurd hjk (hno k hk)

/-- (a): (D1) never applies at a jump time of `x`. -/
theorem closing_a_no_forced
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (hx : t ∈ CDisc x) (ht : (t : ℝ≥0∞) ≤ pathTreg β w) (k : ℕ) :
    ¬ ForcedAt β w t k := by
  intro hk
  have hle : (((t - k * β : ℝ≥0)) : ℝ≥0∞) ≤ pathTreg β w :=
    (by exact_mod_cast (tsub_le_self : t - k * β ≤ t) : (_ : ℝ≥0∞) ≤ t).trans ht
  obtain ⟨t0, j, h0, he, _⟩ := S.root hi _ hk.2.1 hle
  have : t = t0 + ((j + k : ℕ) : ℝ≥0) * β := by
    calc t = (t - k * β) + k * β := (sub_add_of_delay hk.1.2).symm
      _ = _ := by rw [he]; push_cast; ring
  exact hi t0 h0 t hx (j + k) (by have := hk.1.1; omega) this

/-- Auxiliary: equal left values at two times of one class give a bad time. -/
theorem bad_of_leftVal {s s' : ℝ≥0} {j : ℕ} (hs' : 0 < s') (_hj : 1 ≤ j)
    (hs : s = s' + j * β) (hτ : (s : ℝ≥0∞) ≤ pathTreg β w)
    (hL : leftVal w s = leftVal w s') :
    ∃ r : ℝ≥0, r < s ∧ (r : ℝ≥0∞) < pathTreg β w ∧ (j : ℝ≥0) * β ≤ r ∧
      w r = w (r - j * β) := by
  have hs0 : 0 < s := hs'.trans_le (hs ▸ le_self_add)
  obtain ⟨a, has, ha⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs0).1
    (S.reg.eventually_leftVal hs0)
  obtain ⟨a', has', ha'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs').1
    (S.reg.eventually_leftVal hs')
  set e0 : ℝ≥0 := min (min (s - a) (s' - a')) s' with he0
  have he0pos : 0 < e0 := lt_min (lt_min (tsub_pos_of_lt has) (tsub_pos_of_lt has')) hs'
  set ε : ℝ≥0 := e0 / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεlt : ε < e0 := by
    rw [hε]; exact half_lt_self he0pos
  have hε1 : ε < s - a := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε < s' - a' := hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ε < s' := hεlt.trans_le (min_le_right _ _)
  have hrs : s - ε < s := tsub_lt_self hs0 hεpos
  have hr1 : s - ε ∈ Ioo a s := ⟨lt_tsub_iff_right.2 (by
      have := lt_tsub_iff_left.1 hε1
      exact this), hrs⟩
  have hrj : s - ε - j * β = s' - ε := by
    rw [tsub_right_comm, hs, add_tsub_cancel_right]
  have hr2 : s' - ε ∈ Ioo a' s' :=
    ⟨lt_tsub_iff_right.2 (by
      have := lt_tsub_iff_left.1 hε2
      exact this), tsub_lt_self hs' hεpos⟩
  refine ⟨s - ε, hrs, lt_of_lt_of_le (by exact_mod_cast hrs) hτ, ?_, ?_⟩
  · rw [hs]
    have : (j : ℝ≥0) * β + ε ≤ s' + j * β := by
      exact (add_comm _ _).le.trans (add_le_add hε3.le le_rfl)
    exact le_tsub_of_add_le_right this
  · rw [hrj]
    have e1 := ha hr1
    have e2 := ha' hr2
    simp only [mem_ofPred_eq] at e1 e2
    rw [e1, e2, hL]

/-- (b), first part: no bad times. -/
theorem no_bad (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    (r : ℝ≥0) (k : ℕ) :
    ¬ ((r : ℝ≥0∞) < pathTreg β w ∧ 1 ≤ k ∧ (k : ℝ≥0) * β ≤ r ∧ w r = w (r - k * β)) := by
  classical
  intro hcon
  let Bk : ℕ → Set ℝ≥0 := fun k =>
    {r | (r : ℝ≥0∞) < pathTreg β w ∧ 1 ≤ k ∧ (k : ℝ≥0) * β ≤ r ∧ w r = w (r - k * β)}
  set B : Set ℝ≥0 := ⋃ k, Bk k with hB
  have hBne : B.Nonempty := ⟨r, Set.mem_iUnion.2 ⟨k, hcon⟩⟩
  set r0 := sInf B with hr0
  have hlb : ∀ r ∈ B, r0 ≤ r := fun r hr => csInf_le (OrderBot.bddBelow B) hr
  set K := ⌈(r0 + 1) / β⌉₊ with hK
  have hfreq : ∃ k : ℕ, ∃ᶠ r in 𝓝[≥] r0, r ∈ Bk k := by
    by_contra hno
    simp only [not_exists, Filter.not_frequently] at hno
    have hall : ∀ᶠ r in 𝓝[≥] r0, ∀ k ∈ Finset.range (K + 1), r ∉ Bk k :=
      (Filter.eventually_all_finset _).2 fun k _ => hno k
    have hlt : ∀ᶠ r in 𝓝[≥] r0, r < r0 + 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_of_pos_right r0 one_pos))
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hall.and hlt)
    have : u' ≤ r0 := by
      refine le_csInf hBne fun r hr => ?_
      by_contra hlt'
      push Not at hlt'
      obtain ⟨k0, hk0⟩ := Set.mem_iUnion.1 hr
      have hr0r := hlb r hr
      have hmem := hsub ⟨hr0r, hlt'⟩
      refine hmem.1 k0 ?_ hk0
      rw [Finset.mem_range, Nat.lt_succ_iff]
      have h1 : (k0 : ℝ≥0) * β ≤ r0 + 1 := hk0.2.2.1.trans hmem.2.le
      have h2 : (k0 : ℝ≥0) ≤ (r0 + 1) / β := by rwa [le_div_iff₀ S.beta_pos]
      exact_mod_cast h2.trans (Nat.le_ceil _)
    exact absurd hu' (not_lt.2 this)
  obtain ⟨k, hk⟩ := hfreq
  have hmemk : ∀ᶠ r in 𝓝[≥] r0, r ∈ Ici r0 := eventually_mem_nhdsWithin
  have hkr : (k : ℝ≥0) * β ≤ r0 := by
    by_contra h
    push Not at h
    have hev : ∀ᶠ r in 𝓝[≥] r0, r < k * β :=
      nhdsWithin_le_nhds (Iio_mem_nhds h)
    obtain ⟨r, hr, hrl⟩ := (hk.and_eventually hev).exists
    exact absurd hr.2.2.1 (not_le.2 hrl)
  have hcont : Tendsto (fun r : ℝ≥0 => r - k * β) (𝓝[≥] r0) (𝓝[≥] (r0 - k * β)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.sub continuous_const).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [hmemk] with r hr
      exact (tsub_le_tsub_right (show r0 ≤ r from hr) _ : r0 - k * β ≤ r - k * β)
  have hrc1 : ∀ᶠ r in 𝓝[≥] r0, w r = w r0 := S.reg.rc r0
  have hrc2 : ∀ᶠ r in 𝓝[≥] r0, w (r - k * β) = w (r0 - k * β) := hcont.eventually (S.reg.rc _)
  obtain ⟨r1, hr1, h1, h2, h3⟩ :=
    (hk.and_eventually (hrc1.and (hrc2.and hmemk))).exists
  have hr1' : r0 ≤ r1 := h3
  have hk1 : 1 ≤ k := hr1.2.1
  have hr0τ : (r0 : ℝ≥0∞) < pathTreg β w :=
    lt_of_le_of_lt (by exact_mod_cast hr1') hr1.1
  have hw0 : w r0 = w (r0 - k * β) := by rw [← h1, ← h2, hr1.2.2.2]
  have hr0B : r0 ∈ Bk k := ⟨hr0τ, hk1, hkr, hw0⟩
  have hbadlow : ∀ r : ℝ≥0, r < r0 → (r : ℝ≥0∞) < pathTreg β w → ∀ j : ℕ, 1 ≤ j →
      (j : ℝ≥0) * β ≤ r → w r = w (r - j * β) → False := fun r hr hτ j hj hjr hw =>
    absurd (hlb r (Set.mem_iUnion.2 ⟨j, hτ, hj, hjr, hw⟩)) (not_le.2 hr)
  have hbad_of : ∀ {s s' : ℝ≥0} {j : ℕ}, 0 < s' → 1 ≤ j → s = s' + j * β → s ≤ r0 →
      leftVal w s = leftVal w s' → False := by
    intro s s' j hs' hj hs hsr hL
    have hsτ : (s : ℝ≥0∞) ≤ pathTreg β w := (by exact_mod_cast hsr : (s : ℝ≥0∞) ≤ r0).trans hr0τ.le
    obtain ⟨r, hr, hrτ, hjr, hw⟩ := S.bad_of_leftVal hs' hj hs hsτ hL
    exact hbadlow r (hr.trans_le hsr) hrτ j hj hjr hw
  set u := r0 - k * β with hu
  have hr0pos : 0 < r0 := by
    have : (0 : ℝ≥0) < k * β := mul_pos (by exact_mod_cast hk1) S.beta_pos
    exact this.trans_le hkr
  have hr0u : r0 = u + k * β := (sub_add_of_delay hkr).symm
  rcases eq_or_ne u 0 with hu0 | hu0
  · have hr0eq : r0 = k * β := by rw [hr0u, hu0, zero_add]
    have hw' : w ((k : ℝ≥0) * β) = 0 := by
      rw [← hr0eq, hw0, hu0, S.zero]
    have hle : pathTreg β w ≤ (((k : ℝ≥0) * β : ℝ≥0) : ℝ≥0∞) :=
      iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ w ((k : ℝ≥0) * β) = 0} =>
        ((((k.1 : ℝ≥0) * β : ℝ≥0)) : ℝ≥0∞)) ⟨k, hk1, hw'⟩
    rw [← hr0eq] at hle
    exact absurd hr0τ (not_lt.2 hle)
  · have hupos : 0 < u := pos_iff_ne_zero.2 hu0
    have huτ : (u : ℝ≥0∞) ≤ pathTreg β w :=
      (by exact_mod_cast (tsub_le_self : u ≤ r0) : (u : ℝ≥0∞) ≤ r0).trans hr0τ.le
    by_cases hr0j : r0 ∈ CDisc w <;> by_cases huj : u ∈ CDisc w
    · -- both jump
      have hedge := S.edge_eq hi (t := u) (k := k) huj (by rw [← hr0u]; exact hr0j)
        (by rw [← hr0u]; exact hr0τ.le)
      rw [← hr0u] at hedge
      have hne_u := (S.reg.mem_CDisc_iff.1 huj).2
      have hne_r := (S.reg.mem_CDisc_iff.1 hr0j).2
      have hmem : leftVal w u ∈ ({leftVal w r0, w r0} : Set (Fin d → ℤ)) := by
        rw [hedge]; exact Or.inl rfl
      rcases hmem with h | h
      · exact hbad_of hupos hk1 hr0u le_rfl h.symm
      · exact hne_u (by rw [h, hw0])
    · -- r0 jumps, u does not
      rcases S.jump_cases hr0j hr0τ.le with ⟨k', hk', hwk'⟩ | ⟨hx0, hno⟩
      · have hne : k' ≠ k := by
          rintro rfl
          exact huj hk'.2.1
        have hp'pos : 0 < r0 - k' * β := (S.reg.mem_CDisc_iff.1 hk'.2.1).1
        have hlvp' : leftVal w (r0 - k' * β) = w r0 := hwk'.symm
        have hlvu : leftVal w u = w u := S.reg.leftVal_eq_of_not_mem hupos huj
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hsh := sub_shift (t := r0) (β := β) hlt.le hkr
          exact hbad_of (s := r0 - k' * β) (s' := u) (j := k - k') hupos (by omega) hsh
            ((tsub_le_self)) (by rw [hlvp', hlvu, hw0])
        · have hsh := sub_shift (t := r0) (β := β) hgt.le hk'.1.2
          exact hbad_of (s := u) (s' := r0 - k' * β) (j := k' - k) hp'pos (by omega) hsh
            (tsub_le_self) (by rw [hlvp', hlvu, hw0])
      · have h2 := (S.rules r0 hr0pos hr0τ.le).2.1 hno hx0
        have hne_r := (S.reg.mem_CDisc_iff.1 hr0j).2
        by_cases hT : TakenAt β x w r0
        · rw [ite_eq_left hT] at h2
          exact hT k ⟨hk1, hkr⟩ (by rw [← h2, hw0])
        · rw [ite_eq_right hT] at h2
          exact hne_r h2.symm
    · -- u jumps, r0 does not
      have hforced : ForcedAt β w r0 k := ⟨⟨hk1, hkr⟩, huj, by
        rw [← hw0, S.reg.leftVal_eq_of_not_mem hr0pos hr0j]⟩
      exact hr0j (S.forced_jump hr0τ.le hforced)
    · -- neither jumps
      exact hbad_of hupos hk1 hr0u le_rfl
        (by rw [S.reg.leftVal_eq_of_not_mem hr0pos hr0j,
          S.reg.leftVal_eq_of_not_mem hupos huj, hw0])

/-- (b), first claim. -/
theorem closing_b_ne (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {s s' : ℝ≥0} {k : ℕ} (hk : 1 ≤ k) (hs : s = s' + k * β)
    (hτ : (s : ℝ≥0∞) < pathTreg β w) : w s ≠ w s' := by
  intro h
  refine S.no_bad hi s k ⟨hτ, hk, ?_, ?_⟩
  · rw [hs]; exact le_add_self
  · have : s - k * β = s' := by rw [hs, add_tsub_cancel_right]
    rw [this]; exact h

/-- (b), second claim. -/
theorem closing_b_left_ne
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {s s' : ℝ≥0} {k : ℕ} (hs' : 0 < s') (hk : 1 ≤ k) (hs : s = s' + k * β)
    (hτ : (s : ℝ≥0∞) ≤ pathTreg β w) : leftVal w s ≠ leftVal w s' := by
  intro h
  obtain ⟨r, _, hrτ, hjr, hw⟩ := S.bad_of_leftVal hs' hk hs hτ h
  exact S.no_bad hi r k ⟨hrτ, hk, hjr, hw⟩

/-- (c): at most one index satisfies the condition of (D1). -/
theorem closing_c (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathTreg β w) {k1 k2 : ℕ}
    (h1 : ForcedAt β w t k1) (h2 : ForcedAt β w t k2) : k1 = k2 := by
  have key : ∀ {k1 k2 : ℕ}, ForcedAt β w t k1 → ForcedAt β w t k2 → k1 < k2 → False := by
    intro k1 k2 h1 h2 hlt
    have hsh := sub_shift (t := t) (β := β) hlt.le h2.1.2
    have hlt1 := delayIdx_lt β S.beta_pos h1.1
    refine S.closing_b_ne hi (s := t - k1 * β) (s' := t - k2 * β) (k := k2 - k1) (by omega)
      hsh (lt_of_lt_of_le (by exact_mod_cast hlt1) ht) ?_
    rw [h1.2.2, h2.2.2]
  rcases lt_trichotomy k1 k2 with h | h | h
  · exact (key h1 h2 h).elim
  · exact h
  · exact (key h2 h1 h).elim

/-- (d): two jumps of one class start from different endpoints. -/
theorem closing_d_endpoints
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {s s' : ℝ≥0} {k : ℕ} (hs : s ∈ CDisc w) (hk : 1 ≤ k) (hs' : s' = s + k * β)
    (hτ : (s' : ℝ≥0∞) ≤ pathTreg β w) : leftVal w s' ≠ leftVal w s :=
  S.closing_b_left_ne hi hs.1 hk hs' hτ

/-- (d): each class contains at most two jumps of `w` in `(0, t]`, `t ≤ τ`. -/
theorem closing_d_card (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathTreg β w) (t0 : ℝ≥0) :
    {s : ℝ≥0 | s ∈ CDisc w ∧ s ≤ t ∧ ∃ j : ℤ, (s : ℝ) = t0 + j * β}.ncard ≤ 2 := by
  classical
  set T := {s : ℝ≥0 | s ∈ CDisc w ∧ s ≤ t ∧ ∃ j : ℤ, (s : ℝ) = t0 + j * β} with hT
  rcases T.eq_empty_or_nonempty with h | ⟨s0, hs0⟩
  · rw [h]; simp
  have hτ : ∀ s ∈ T, (s : ℝ≥0∞) ≤ pathTreg β w := fun s hs =>
    (by exact_mod_cast hs.2.1 : (s : ℝ≥0∞) ≤ t).trans ht
  have hedge : ∀ s ∈ T, ({leftVal w s, w s} : Set (Fin d → ℤ)) = {leftVal w s0, w s0} := by
    intro s hs
    obtain ⟨j, hj⟩ := hs.2.2
    obtain ⟨j0, hj0⟩ := hs0.2.2
    rcases lt_trichotomy s s0 with h | h | h
    · obtain ⟨k, _, hk⟩ := class_nat S.beta_pos h hj hj0
      have := S.edge_eq hi (t := s) (k := k) (by exact (hs.1)) (hk ▸ hs0.1) (hk ▸ hτ s0 hs0)
      rw [← hk] at this
      exact this.symm
    · rw [h]
    · obtain ⟨k, _, hk⟩ := class_nat S.beta_pos h hj0 hj
      have := S.edge_eq hi (t := s0) (k := k) hs0.1 (hk ▸ hs.1) (hk ▸ hτ s hs)
      rw [← hk] at this
      exact this
  have hfin : ({leftVal w s0, w s0} : Set (Fin d → ℤ)).Finite := Set.toFinite _
  refine (Set.ncard_le_ncard_of_injOn (leftVal w) (fun s hs => ?_) ?_ hfin).trans ?_
  · rw [← hedge s hs]; exact Or.inl rfl
  · intro s1 h1 s2 h2 heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨j1, hj1⟩ := h1.2.2
      obtain ⟨j2, hj2⟩ := h2.2.2
      obtain ⟨k, hk1, hk⟩ := class_nat S.beta_pos h hj1 hj2
      exact S.closing_d_endpoints hi h1.1 hk1 hk (hk ▸ hτ s2 h2) heq.symm
    · obtain ⟨j1, hj1⟩ := h1.2.2
      obtain ⟨j2, hj2⟩ := h2.2.2
      obtain ⟨k, hk1, hk⟩ := class_nat S.beta_pos h hj2 hj1
      exact S.closing_d_endpoints hi h2.1 hk1 hk (hk ▸ hτ s1 h1) heq
  · exact (Set.ncard_insert_le _ _).trans (by simp)

/-- (e): neither the precedence of (D1) over (D2) nor the least-index convention is used. -/
theorem closing_e (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathTreg β w) :
    (t ∈ CDisc x → ∀ k, ¬ ForcedAt β w t k) ∧
      ∀ k1 k2, ForcedAt β w t k1 → ForcedAt β w t k2 → k1 = k2 :=
  ⟨fun hx k => S.closing_a_no_forced hi hx ht k, fun _ _ h1 h2 => S.closing_c hi ht h1 h2⟩

end DrivenSol

end ElboimSly.Cyclic

end
