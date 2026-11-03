/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Heavy.Occupation
public import ElboimSly.Paper.Heavy.BadFinite
public import ElboimSly.Paper.Heavy.BlockProbCount
public import ElboimSly.Paper.Heavy.CountVisited
public import ElboimSly.Paper.Heavy.NoFast
public import Mathlib

/-!
# The time spent in the exceptional set

Short gaps, first paragraph ("Time spent in the exceptional set"),
ES22 §7. On `{τ'_bad > T}`, `|E_T| ≤ (9^d + 1) 2^{kd} · 2n` if `t_n^{5δ} > β` and
`E_t = ∅` otherwise, and by occupation before closing the time `W₂` spends in `E_t` is at most
`β |E_T|`. (The cardinality of `N(B, 2^{k+1})` is bounded through the box of side `9 · 2^k`.)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ} {β t₀ q T : ℝ} {n : ℕ} {u : Fin d → ℤ} {W₁ W₂ : ℝ → Fin d → ℤ}

theorem Step78CrossBad.mono {ι : Fin d → ℤ} {t t' : ℝ}
    (h : Step78CrossBad d β t₀ n q T W₁ W₂ ι t) (htt : t ≤ t') :
    Step78CrossBad d β t₀ n q T W₁ W₂ ι t' := by
  unfold Step78CrossBad at h ⊢
  dsimp only at h ⊢
  obtain ⟨a, ha, b, hb, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨a, ha, b, hb, h1, h2.trans htt, h3, h4, h5, h6, h7, h8⟩

theorem step78BadBlocks_mono {t t' : ℝ} (htt : t ≤ t') :
    step78BadBlocks d β t₀ n q T W₁ W₂ t ⊆ step78BadBlocks d β t₀ n q T W₁ W₂ t' :=
  fun _ h => h.imp id fun h' => h'.mono htt

theorem step78BadBlocks_finite (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ) :
    (step78BadBlocks d β t₀ n q T W₁ W₂ t).Finite := by
  set k := heavyLevel d n
  have hX : (cycIntTimes β ∩ Icc 0 T).Finite := cycIntTimes_inter_Icc_finite hβ T
  have hnear : ∀ x : ℝ, {ι : Fin d → ℤ | W₁ x ∈ latNbhd (heavyBlock k ι) (2 ^ (k + 2))}.Finite := by
    intro x
    have := blocks_near_finite (W₁ x) k (2 ^ (k + 2))
    refine this.subset fun ι hι => ?_
    simpa [latNbhd] using hι
  refine ((badSet_finite (w := W₁) (t₀ := t₀) (n := n) hβ htk T).union
    (hX.biUnion fun x _ => hnear x)).subset ?_
  rintro ι (h | h)
  · exact Or.inl h
  · right
    unfold Step78CrossBad at h
    dsimp only at h
    obtain ⟨a, ha, b, hb, h1, -, h3, -⟩ := h
    exact mem_iUnion₂.2 ⟨a, ⟨ha, ha.1, by linarith⟩, h3⟩

theorem nbhd_card_le (k : ℕ) (ι : Fin d → ℤ) :
    (latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 1))).Finite ∧
      (latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 1))).ncard ≤ 9 ^ d * (2 ^ k) ^ d := by
  obtain ⟨Uf, hU, hc⟩ := exists_finset_nbhd (d := d) k ι
  have hsub : latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 1)) ⊆ (Uf : Set (Fin d → ℤ)) := by
    intro x hx
    rw [Finset.mem_coe, ← hU]
    have hx' : latDist x (heavyBlock k ι) ≤ (2 : ℝ) ^ (k + 1) := hx
    exact show latDist x (heavyBlock k ι) ≤ (2 : ℝ) ^ (k + 2) from
      hx'.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨Uf.finite_toSet.subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub Uf.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  calc Uf.card ≤ (9 * 2 ^ k) ^ d := hc
    _ = _ := by rw [mul_pow]

/-- `|E_t| ≤ (9^d + 1) 2^{kd} (|ℬ'_t| + b_t(w₂))`. -/
theorem step78Exc_card_le (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ) :
    (step78Exc d β t₀ n q T u W₁ W₂ t).Finite ∧
      (step78Exc d β t₀ n q T u W₁ W₂ t).ncard ≤ (9 ^ d + 1) * (2 ^ heavyLevel d n) ^ d *
        ((step78BadBlocks d β t₀ n q T W₁ W₂ t).ncard +
          badCount d β t₀ n (fun s => W₂ s - u) t) := by
  set k := heavyLevel d n
  set S1 := step78BadBlocks d β t₀ n q T W₁ W₂ t with hS1
  set S2 := {ι : Fin d → ℤ | BadByTime d β t₀ n (fun s => W₂ s - u) ι t} with hS2
  have h1 : S1.Finite := step78BadBlocks_finite hβ htk t
  have h2 : S2.Finite := badSet_finite hβ htk t
  have hA : (⋃ ι ∈ S1, latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 1))).Finite :=
    h1.biUnion fun ι _ => (nbhd_card_le k ι).1
  have hB : (badUnion d β t₀ n (fun s => W₂ s - u) t).Finite :=
    h2.biUnion fun ι _ => (ncard_heavyBlock_le k ι).1
  have hA' : (⋃ ι ∈ S1, latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 1))).ncard ≤
      9 ^ d * (2 ^ k) ^ d * S1.ncard := by
    refine (h1.ncard_biUnion_le _).trans ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ h1]
    calc _ ≤ ∑ _ι ∈ h1.toFinset, 9 ^ d * (2 ^ k) ^ d :=
          Finset.sum_le_sum fun ι _ => (nbhd_card_le k ι).2
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card S1 h1, mul_comm]
  have hB' : (badUnion d β t₀ n (fun s => W₂ s - u) t).ncard ≤ (2 ^ k) ^ d * S2.ncard := by
    unfold badUnion
    refine (h2.ncard_biUnion_le _).trans ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ h2]
    calc _ ≤ ∑ _ι ∈ h2.toFinset, (2 ^ k) ^ d :=
          Finset.sum_le_sum fun ι _ => (ncard_heavyBlock_le k ι).2
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card S2 h2, mul_comm]
  unfold step78Exc
  refine ⟨hA.union (hB.image _), ?_⟩
  refine (Set.ncard_union_le _ _).trans ?_
  have hi : ((fun x => u + x) '' badUnion d β t₀ n (fun s => W₂ s - u) t).ncard ≤
      (badUnion d β t₀ n (fun s => W₂ s - u) t).ncard := Set.ncard_image_le hB
  unfold badCount
  have e1 : 0 ≤ (2 ^ k) ^ d * S2.ncard := Nat.zero_le _
  nlinarith [Nat.zero_le (S1.ncard), Nat.zero_le ((2 ^ k) ^ d),
    Nat.zero_le (9 ^ d * (2 ^ k) ^ d * S1.ncard), hA', hB', hi,
    Nat.zero_le ((2 ^ k) ^ d * S1.ncard), Nat.zero_le ((2 ^ k) ^ d * S2.ncard),
    Nat.zero_le (9 ^ d * (2 ^ k) ^ d * S2.ncard)]

theorem step78Exc_mono (_hβ : 0 < β) (_htk : 0 ≤ heavyTkPrime d t₀ n) {t t' : ℝ} (htt : t ≤ t') :
    step78Exc d β t₀ n q T u W₁ W₂ t ⊆ step78Exc d β t₀ n q T u W₁ W₂ t' := by
  unfold step78Exc badUnion
  refine union_subset_union ?_ (image_mono ?_)
  · exact iUnion₂_mono' fun ι hι => ⟨ι, step78BadBlocks_mono htt hι, subset_rfl⟩
  · exact iUnion₂_mono' fun ι hι => ⟨ι, BadByTime.mono hι htt, subset_rfl⟩

/-- No `t ≤ T` has too many bad blocks when `τ'_bad > T`. -/
theorem step78_count_le (hτ : ENNReal.ofReal T < step78TauBad d β t₀ n q T u W₁ W₂) {t : ℝ}
    (ht : t ≤ T) :
    (β < indScale t₀ n ^ (5 * indDelta d) →
      step78BadCount d β t₀ n q T u W₁ W₂ t ≤ 2 * n) ∧
    (¬ β < indScale t₀ n ^ (5 * indDelta d) → step78BadCount d β t₀ n q T u W₁ W₂ t = 0) := by
  unfold step78TauBad at hτ
  constructor
  · intro hc
    rw [ite_eq_left hc] at hτ
    by_contra hcon
    push Not at hcon
    have := (iInf₂_le t ⟨ht, hcon⟩ : (⨅ (t : ℝ) (_ : t ≤ T ∧
      2 * n < step78BadCount d β t₀ n q T u W₁ W₂ t), ENNReal.ofReal t) ≤ ENNReal.ofReal t)
    exact absurd (lt_of_lt_of_le hτ (this.trans (ENNReal.ofReal_le_ofReal ht))) (lt_irrefl _)
  · intro hc
    rw [ite_eq_right hc] at hτ
    by_contra hcon
    have h1 : 1 ≤ step78BadCount d β t₀ n q T u W₁ W₂ t := Nat.one_le_iff_ne_zero.2 hcon
    have := (iInf₂_le t ⟨ht, h1⟩ : (⨅ (t : ℝ) (_ : t ≤ T ∧
      1 ≤ step78BadCount d β t₀ n q T u W₁ W₂ t), ENNReal.ofReal t) ≤ ENNReal.ofReal t)
    exact absurd (lt_of_lt_of_le hτ (this.trans (ENNReal.ofReal_le_ofReal ht))) (lt_irrefl _)

/-- The occupation of a finite set `A` by `w₂` in `[0, T]`. -/
theorem step78_occ_of_finite (hβ : 0 < β) {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (hnr : HasNoReturn β w) {T : ℝ} (hT : ENNReal.ofReal T ≤ cycClosingTime β w)
    {A : Set (Fin d → ℤ)} (hA : A.Finite) :
    volume {t : ℝ | t ∈ Icc 0 T ∧ w t ∈ A} ≤ (A.ncard : ℝ≥0∞) * ENNReal.ofReal β := by
  have hsub : {t : ℝ | t ∈ Icc 0 T ∧ w t ∈ A} ⊆ {s : ℝ | s ∈ Ico 0 T ∧ w s ∈ A} ∪ {T} := by
    rintro t ⟨⟨h0, h1⟩, hA'⟩
    rcases h1.lt_or_eq with h | h
    · exact Or.inl ⟨⟨h0, h⟩, hA'⟩
    · exact Or.inr h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, add_zero]
  exact volume_mem_finite_le hβ hw hnr hT hA

/-- Short gaps, "Time spent in the exceptional set": on `{τ'_bad > T}` and
`T ≤ T(w₂)`, with `w₂ = W₂ - u`. -/
theorem step78_occ (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)
    (hw : IsCyclicPath fun s => W₂ s - u) (hnr : HasNoReturn β fun s => W₂ s - u)
    (hcl : ENNReal.ofReal T ≤ cycClosingTime β fun s => W₂ s - u)
    (hτ : ENNReal.ofReal T < step78TauBad d β t₀ n q T u W₁ W₂) (_hT0 : 0 ≤ T) :
    (β < indScale t₀ n ^ (5 * indDelta d) →
      volume {t : ℝ | t ∈ Icc 0 T ∧ W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t} ≤
        ENNReal.ofReal (((9 ^ d + 1) * (2 ^ heavyLevel d n) ^ d * (2 * n) : ℕ) * β)) ∧
    (¬ β < indScale t₀ n ^ (5 * indDelta d) →
      volume {t : ℝ | t ∈ Icc 0 T ∧ W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t} = 0) := by
  obtain ⟨hfin, hcard⟩ := step78Exc_card_le (β := β) (t₀ := t₀) (n := n) (q := q) (T := T)
    (u := u) (W₁ := W₁) (W₂ := W₂) hβ htk T
  have hcnt : (step78BadBlocks d β t₀ n q T W₁ W₂ T).ncard +
      badCount d β t₀ n (fun s => W₂ s - u) T = step78BadCount d β t₀ n q T u W₁ W₂ T := rfl
  have hocc : volume {t : ℝ | t ∈ Icc 0 T ∧ W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t} ≤
      ((step78Exc d β t₀ n q T u W₁ W₂ T).ncard : ℝ≥0∞) * ENNReal.ofReal β := by
    have hA : ((fun x => x - u) '' step78Exc d β t₀ n q T u W₁ W₂ T).Finite := hfin.image _
    have hsub : {t : ℝ | t ∈ Icc 0 T ∧ W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t} ⊆
        {t : ℝ | t ∈ Icc 0 T ∧ (fun s => W₂ s - u) t ∈
          (fun x => x - u) '' step78Exc d β t₀ n q T u W₁ W₂ T} := by
      rintro t ⟨ht, hE⟩
      exact ⟨ht, _, step78Exc_mono hβ htk ht.2 hE, rfl⟩
    have hinj : Function.Injective fun x : Fin d → ℤ => x - u := fun x y h => by simpa using h
    refine (measure_mono hsub).trans ((step78_occ_of_finite hβ hw hnr hcl hA).trans ?_)
    rw [Set.ncard_image_of_injective _ hinj]
  constructor
  · intro hc
    have h2 := (step78_count_le hτ le_rfl).1 hc
    have hle : (step78Exc d β t₀ n q T u W₁ W₂ T).ncard ≤
        (9 ^ d + 1) * (2 ^ heavyLevel d n) ^ d * (2 * n) :=
      hcard.trans (Nat.mul_le_mul_left _ (hcnt ▸ h2))
    refine hocc.trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hβ.le)
    exact_mod_cast hle
  · intro hc
    have h2 := (step78_count_le hτ le_rfl).2 hc
    have h0 : (step78Exc d β t₀ n q T u W₁ W₂ T).ncard = 0 := by
      have := hcard; rw [hcnt, h2] at this; simpa using this
    refine le_antisymm (hocc.trans ?_) (zero_le)
    rw [h0]; simp

end ElboimSly.Paper.Step

end
