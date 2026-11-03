/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Seven

/-!
# Lemma 6.6

ES22 Lemma 6.6 (§6; deviation F60).

If `t_n^{5δ} > β`, then `P(#{B ∈ ℬ* : B bad} > n) ≤ exp(-δ²n³/(2·33^d))`.

The proof extracts, from `n + 1` bad blocks, at least `a = ⌈(n+1)/33^d⌉` bad blocks whose indices are
pairwise at `ℓ^∞`-distance `≥ 17` (`greedy_separated`), uses independence of the events
`{B bad}` for such families, and a union bound over the at most `5^{ad(n+1)}` families.

`es6_six_of_blockprob` takes two inputs as distinctly named hypotheses: `hblk`
(probability that a block is bad (b)) and `hindep` (goodness is local; independence at distance (d), independence at distance).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- Greedy extraction of a separated subfamily: indices at pairwise `ℓ^∞`-distance `≥ 17`, at least
a `33^{-d}` fraction of the family. -/
theorem greedy_separated (S : Finset (Fin d → ℤ)) :
    ∃ A ⊆ S, S.card ≤ 33 ^ d * A.card ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ c, (17 : ℤ) ≤ |x c - y c| := by
  classical
  induction' hS : S.card using Nat.strong_induction_on with m ih generalizing S
  by_cases hemp : S = ∅
  · exact ⟨∅, by simp, by simp [hemp] at hS ⊢; omega, by simp⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hemp
  set R : Finset (Fin d → ℤ) := S.filter fun y => ∀ c, |x c - y c| ≤ 16 with hR
  have hxR : x ∈ R := by simp [hR, hx]
  have hRcard : R.card ≤ 33 ^ d := by
    have hsub : R ⊆ Fintype.piFinset fun c => Finset.Icc (x c - 16) (x c + 16) := by
      intro y hy
      simp only [hR, Finset.mem_filter] at hy
      simp only [Fintype.mem_piFinset, Finset.mem_Icc]
      intro c
      have := abs_le.1 (hy.2 c)
      constructor <;> linarith [this.1, this.2]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc]
    have : ∀ c : Fin d, (x c + 16 + 1 - (x c - 16)).toNat = 33 := fun c => by omega
    simp [this]
  set S' := S \ R with hS'
  have hlt : S'.card < m := by
    rw [← hS]
    exact Finset.card_lt_card (Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.2
      ⟨x, hx, fun h => (Finset.mem_sdiff.1 h).2 hxR⟩)
  obtain ⟨A', hA'S, hA'card, hA'sep⟩ := ih S'.card hlt S' rfl
  have hxA' : x ∉ A' := fun h => by
    have := hA'S h
    simp [hS', hxR] at this
  refine ⟨insert x A', ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx
    · exact (Finset.mem_sdiff.1 (hA'S hy)).1
  · rw [Finset.card_insert_of_notMem hxA']
    have : S.card ≤ S'.card + R.card := by
      calc S.card ≤ (S' ∪ R).card := Finset.card_le_card (fun y hy => by
            by_cases h : y ∈ R <;> simp [hS', h, hy])
        _ ≤ _ := Finset.card_union_le _ _
    rw [← hS]
    calc S.card ≤ 33 ^ d * A'.card + 33 ^ d := by omega
      _ = 33 ^ d * (A'.card + 1) := by ring
  · intro u hu v hv huv
    have hfar : ∀ y ∈ A', ∃ c, (17 : ℤ) ≤ |x c - y c| := by
      intro y hy
      have hy' := Finset.mem_sdiff.1 (hA'S hy)
      have : ¬ ∀ c, |x c - y c| ≤ 16 := fun h => hy'.2 (by simp [hR, hy'.1, h])
      push Not at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by omega⟩
    rcases Finset.mem_insert.1 hu with e1 | h1 <;> rcases Finset.mem_insert.1 hv with e2 | h2
    · exact absurd (e1.trans e2.symm) huv
    · rw [e1]; exact hfar v h2
    · rw [e2]
      obtain ⟨c, hc⟩ := hfar u h1
      exact ⟨c, by rw [abs_sub_comm]; exact hc⟩
    · exact hA'sep u h1 v h2 huv

/-- ES22 Lemma 6.6, conditional on `hblk` (probability that a block is bad (b)) and `hindep`
(goodness is local; independence at distance (d)). -/
theorem es6_six_of_blockprob {Pe : Measure Ω} {t₀ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hT7 : d * ((n : ℝ) + 1) * Real.log 5 ≤ indDelta d ^ 2 * (n : ℝ) ^ 2 / 2)
    {env : Ω → Measure (RingSpace d β)}
    (hblk : ∀ ι ∈ heavyBstar d n,
      Pe {ω | HeavyBlockBad d β t₀ n (env ω) ι} ≤
        ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 2))))
    (hindep : ∀ A : Finset (Fin d → ℤ),
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ c, (17 : ℤ) ≤ |x c - y c|) →
        Pe (⋂ ι ∈ A, {ω | HeavyBlockBad d β t₀ n (env ω) ι}) =
          ∏ ι ∈ A, Pe {ω | HeavyBlockBad d β t₀ n (env ω) ι}) :
    Pe {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d)))) := by
  classical
  have hfin : (heavyBstar d n).Finite := (Finset.finite_toSet _).subset (heavyBstar_subset d n)
  set Bf := hfin.toFinset with hBf
  set a : ℕ := ⌈((n : ℝ) + 1) / 33 ^ d⌉₊ with ha
  set bad : (Fin d → ℤ) → Set Ω := fun ι => {ω | HeavyBlockBad d β t₀ n (env ω) ι} with hbad
  set F : Finset (Finset (Fin d → ℤ)) := (Bf.powersetCard a).filter fun A =>
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ c, (17 : ℤ) ≤ |x c - y c| with hF
  set p : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 2))) with hp
  have hsub : {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} ⊆
      ⋃ A ∈ F, ⋂ ι ∈ A, bad ι := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    set Sset : Set (Fin d → ℤ) := {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι} with hSs
    have hSfin : Sset.Finite := hfin.subset (fun ι hι => hι.1)
    obtain ⟨A, hAS, hAcard, hAsep⟩ := greedy_separated hSfin.toFinset
    have hScard : n < hSfin.toFinset.card := by rwa [← Set.ncard_eq_toFinset_card _ hSfin]
    have haA : a ≤ A.card := by
      rw [ha, Nat.ceil_le, div_le_iff₀ (by positivity)]
      have : n + 1 ≤ 33 ^ d * A.card := by omega
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((33 ^ d * A.card : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    obtain ⟨A₀, hA₀, hA₀card⟩ := Finset.exists_subset_card_eq haA
    simp only [mem_iUnion, mem_iInter, exists_prop]
    refine ⟨A₀, ?_, fun ι hι => ?_⟩
    · simp only [hF, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨fun ι hι => ?_, hA₀card⟩, fun x hx y hy hxy => hAsep x (hA₀ hx) y (hA₀ hy) hxy⟩
      have := hSfin.mem_toFinset.1 (hAS (hA₀ hι))
      exact hfin.mem_toFinset.2 this.1
    · have := hSfin.mem_toFinset.1 (hAS (hA₀ hι))
      exact this.2
  have hFcard : F.card ≤ (5 ^ (d * (n + 1))) ^ a := by
    calc F.card ≤ (Bf.powersetCard a).card := Finset.card_filter_le _ _
      _ = Bf.card.choose a := Finset.card_powersetCard _ _
      _ ≤ Bf.card ^ a := Nat.choose_le_pow _ _
      _ ≤ _ := by
          apply Nat.pow_le_pow_left
          rw [hBf, ← Set.ncard_eq_toFinset_card _ hfin]
          exact ncard_heavyBstar_le d n hn
  have hterm : ∀ A ∈ F, Pe (⋂ ι ∈ A, bad ι) ≤ p ^ a := by
    intro A hA
    simp only [hF, Finset.mem_filter, Finset.mem_powersetCard] at hA
    rw [hindep A hA.2]
    calc ∏ ι ∈ A, Pe (bad ι) ≤ ∏ _ι ∈ A, p :=
          Finset.prod_le_prod fun ι hι => hblk ι (hfin.mem_toFinset.1 (hA.1.1 hι))
      _ = p ^ a := by rw [Finset.prod_const, hA.1.2]
  have hmain : Pe {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} ≤
      (F.card : ℝ≥0∞) * p ^ a := by
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ A ∈ F, Pe (⋂ ι ∈ A, bad ι) ≤ ∑ _A ∈ F, p ^ a := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hmain.trans ?_
  set y : ℝ := indDelta d ^ 2 * (n : ℝ) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h5 : ((5 ^ (d * (n + 1)) : ℕ) : ℝ) ≤ Real.exp (y / 2) := by
    have : ((5 ^ (d * (n + 1)) : ℕ) : ℝ) = Real.exp (d * ((n : ℝ) + 1) * Real.log 5) := by
      have h := Real.exp_nat_mul (Real.log 5) (d * (n + 1))
      rw [Real.exp_log (by norm_num)] at h
      push_cast at h ⊢
      rw [h]
    rw [this]
    exact Real.exp_le_exp.2 hT7
  have hFreal : (F.card : ℝ) ≤ Real.exp (y / 2) ^ a :=
    (by exact_mod_cast hFcard : (F.card : ℝ) ≤ ((5 ^ (d * (n + 1)) : ℕ) : ℝ) ^ a).trans
      (pow_le_pow_left₀ (by positivity) h5 a)
  have hpow : p ^ a = ENNReal.ofReal (Real.exp (-y) ^ a) := by
    rw [hp, ENNReal.ofReal_pow (Real.exp_pos _).le]
  rw [hpow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have ha0 : ((n : ℝ) + 1) / 33 ^ d ≤ a := Nat.le_ceil _
  calc (F.card : ℝ) * Real.exp (-y) ^ a ≤ Real.exp (y / 2) ^ a * Real.exp (-y) ^ a := by gcongr
    _ = Real.exp (-(y / 2 * a)) := by
        rw [← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have h33 : (0 : ℝ) < 33 ^ d := by positivity
        have : indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d) ≤ y / 2 * a := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : ((n : ℝ) + 1) ≤ a * 33 ^ d := by
            rwa [div_le_iff₀ h33] at ha0
          have : (n : ℝ) ≤ a * 33 ^ d := by linarith
          have hd2 : 0 ≤ indDelta d ^ 2 := by positivity
          calc indDelta d ^ 2 * (n : ℝ) ^ 3 = y * n := by rw [hy]; ring
            _ ≤ y * (a * 33 ^ d) := by gcongr
            _ = _ := by ring
        linarith

end ElboimSly.Paper.Heavy
