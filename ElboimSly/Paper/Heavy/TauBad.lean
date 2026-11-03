/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadTransfer
public import ElboimSly.Paper.Heavy.Six
public import ElboimSly.Paper.Heavy.Cor610Aux
public import ElboimSly.Paper.Heavy.FastDisplacementE
public import ElboimSly.Paper.Heavy.PiecesClosing
public import ElboimSly.Paper.Heavy.PiecesPath
public import ElboimSly.Paper.Heavy.Eight1

/-!
# Equation (tau.bad)

Eq. (tau.bad) (ES22 §6; deviation D6).

For a good environment `ν` with first piece `w = W^ν`:

* `bad_blocks_subset_Bstar`: before `τ_fast`, every block bad by time `T' ≤ t_n` lies in `ℬ*` and is
  bad for `ν` (discovered bad blocks are bad, pathwise consequences of tfast and heavyJ (e)).
* `taubad_det`: on `{τ_fast > t_n} ∩ {τ_bad ≤ t_n ∧ t_reg}`, more than `n` blocks of `ℬ*` are bad
  (if `t_n^{5δ} > β`), respectively at least one (otherwise).
* `es6_taubad_of`: the probability bound, from `P(τ_fast ≤ t_n)` and the bounds of ES22 Lemma 6.6 and
  ES22 Lemma 6.7, which enter as distinctly named hypotheses.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem heavyLevel_le_self (hd : 1 ≤ d) (n : ℕ) : heavyLevel d n ≤ n := by
  have h := heavyLevel_le hd n
  have hδ := heavy_indDelta_pos hd
  have h2 : indDelta d ≤ 1 / 4 := by
    unfold indDelta
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : (heavyLevel d n : ℝ) ≤ n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact_mod_cast this

/-- Eq. (tau.bad), first step: blocks bad by time `T' ≤ t_n < τ_fast` are in `ℬ*`
and bad for `ν`. -/
theorem bad_blocks_subset_Bstar (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n)
    (hν : Good ν) {T' : ℝ} (hT'0 : 0 ≤ T') (hT'n : T' ≤ indScale t₀ n)
    (hfast : ENNReal.ofReal T' < pathTfastCube (fun s : ℝ => cycWalk ν 0 0 s) n) :
    {ι | BadByTime d β t₀ n (fun s : ℝ => cycWalk ν 0 0 s) ι T'} ⊆
      {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι} := by
  intro ι hι
  have hcyc := isCyclicPath_cycWalk hν
  refine ⟨?_, hν, not_heavyBlockGood_of_badByTime hν hι⟩
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; have : 0 < t₀ := by linarith
    positivity
  -- a witness
  have hwit : ∃ x : ℝ, 0 ≤ x ∧ x ≤ T' ∧
      latDist (cycWalk ν 0 0 x) (heavyBlock (heavyLevel d n) ι) ≤ (2 : ℝ) ^ (heavyLevel d n + 2) := by
    unfold BadByTime at hι
    dsimp only at hι
    rcases hι with ⟨x, hx, h1, h2, -⟩ | ⟨x, hx, h1, h2, -⟩ | ⟨x₁, hx₁, x₂, hx₂, h1, -, h3, -⟩
    · have := htk
      exact ⟨x, hx.1, by linarith, h1⟩
    · exact ⟨x, hx.1, h1, h2⟩
    · have := htk
      exact ⟨x₁, hx₁.1, by linarith, h1⟩
  obtain ⟨x, hx0, hxT, hxB⟩ := hwit
  have hn : 0 < n := by have := hT.t4; omega
  have h4n : T' ≤ 4 ^ (n + 1) := hT'n.trans (indScale_le_four_pow ht4 n)
  have hnorm : ‖cycWalk ν 0 0 x‖ < 5 ^ n := norm_lt_five_pow_of_lt_pathTfastCube
    (w := fun s : ℝ => cycWalk ν 0 0 s) hcyc hT.t3 hn hx0 (hxT.trans h4n)
    (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hxT) hfast)
  -- distance of the block from the origin
  have hk : heavyLevel d n ≤ n := heavyLevel_le_self (by omega) n
  have h2k : (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 5 ^ n := by
    have h1 : (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 4 ^ (n + 1) := by
      calc (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 2 ^ (n + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ 4 ^ (n + 1) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := hT.t3
    have : (4 : ℝ) ^ (n + 1) ≤ (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) (n + 1)]
    linarith
  have hexists : ∃ a ∈ heavyBlock (heavyLevel d n) ι, ‖cycWalk ν 0 0 x - a‖ ≤ (2 : ℝ) ^ (heavyLevel d n + 2) := by
    have hne := heavyBlock_nonempty (d := d) (heavyLevel d n) ι
    have := exists_le_of_latDist_le (R := 2 ^ (heavyLevel d n + 2)) hne (by exact_mod_cast hxB)
    obtain ⟨a, haB, ha⟩ := this
    exact ⟨a, haB, by exact_mod_cast ha⟩
  obtain ⟨a, haB, ha⟩ := hexists
  show latDist (0 : Fin d → ℤ) (heavyBlock (heavyLevel d n) ι) ≤ ((2 * 5 ^ n : ℕ) : ℝ)
  refine (latDist_le_norm_of_mem haB 0).trans ?_
  have : ‖(0 : Fin d → ℤ) - a‖ ≤ ‖cycWalk ν 0 0 x‖ + ‖cycWalk ν 0 0 x - a‖ := by
    calc ‖(0 : Fin d → ℤ) - a‖ = ‖-(a)‖ := by simp
      _ = ‖-(cycWalk ν 0 0 x) + (cycWalk ν 0 0 x - a)‖ := by congr 1; abel
      _ ≤ ‖-(cycWalk ν 0 0 x)‖ + ‖cycWalk ν 0 0 x - a‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  push_cast
  linarith

/-- Eq. (tau.bad), pathwise: on `{τ_fast > t_n} ∩ {τ_bad ≤ t_n ∧ t_reg}`, the badness
counts of `ℬ*` exceed the thresholds. -/
theorem taubad_det (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β)
    (hT : HeavyT d n₀ E n) (hν : Good ν)
    (hfast : min (ENNReal.ofReal (indScale t₀ n)) (cycTreg ν) <
      pathTfastCube (fun s : ℝ => cycWalk ν 0 0 s) n)
    (hbad : heavyTauBad d β t₀ n (fun s : ℝ => cycWalk ν 0 0 s) ≤
      min (ENNReal.ofReal (indScale t₀ n)) (cycTreg ν)) :
    (β < indScale t₀ n ^ (5 * indDelta d) →
      n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι}.ncard) ∧
    (¬ β < indScale t₀ n ^ (5 * indDelta d) →
      ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n ν ι) := by
  have hcyc := isCyclicPath_cycWalk hν
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; have : 0 < t₀ := by linarith
    positivity
  have htn0 : 0 ≤ indScale t₀ n := by unfold indScale; have : 0 < t₀ := by linarith
                                      positivity
  set m : ℝ≥0∞ := min (ENNReal.ofReal (indScale t₀ n)) (cycTreg ν) with hm
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  set T' : ℝ := m.toReal with hT'
  have hT'0 : 0 ≤ T' := ENNReal.toReal_nonneg
  have hmT : ENNReal.ofReal T' = m := ENNReal.ofReal_toReal hmtop
  have hT'n : T' ≤ indScale t₀ n := by
    have : ENNReal.ofReal T' ≤ ENNReal.ofReal (indScale t₀ n) := by
      rw [hmT]; exact min_le_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff htn0).1 this
  have hfast' : ENNReal.ofReal T' < pathTfastCube (fun s : ℝ => cycWalk ν 0 0 s) n := by
    rw [hmT]; exact hfast
  have hsub := bad_blocks_subset_Bstar hd ht1 ht4 hT hν hT'0 hT'n hfast'
  have hfin : {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι}.Finite :=
    ((Finset.finite_toSet _).subset (heavyBstar_subset d n)).subset fun ι hι => hι.1
  have hcount : ∀ ℓ : ℕ, heavyBadTime d β t₀ n (fun s : ℝ => cycWalk ν 0 0 s) ℓ ≤ m →
      ℓ ≤ {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι}.ncard := by
    intro ℓ hℓ
    rw [← hmT, heavyBadTime_le_iff hcyc hβ htk ℓ hT'0] at hℓ
    exact hℓ.trans (Set.ncard_le_ncard hsub hfin)
  unfold heavyTauBad at hbad
  constructor
  · intro hc
    rw [ite_eq_left hc] at hbad
    have := hcount (n + 1) hbad
    omega
  · intro hc
    rw [ite_eq_right hc] at hbad
    have := hcount 1 hbad
    obtain ⟨ι, hι⟩ := Set.nonempty_of_ncard_ne_zero
      (s := {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι}) (by omega)
    exact ⟨ι, hι.1, hι.2⟩

/-- Eq. (tau.bad), conditional on `P(τ_fast ≤ t_n) ≤ ϖ` (`hfast`, from
Eq. (taufast)) and on the bounds `h6`, `h7` of ES22 Lemma 6.6 and ES22 Lemma 6.7. -/
theorem es6_taubad_of {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {env : Ω → Measure (RingSpace d β)} (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hgood : ∀ᵐ ω ∂Pe, Good (env ω))
    {ϖ q₆ q₇ : ℝ}
    (hfast : Pe {ω | pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
      min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ ENNReal.ofReal ϖ)
    (h6 : β < indScale t₀ n ^ (5 * indDelta d) →
      Pe {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} ≤
        ENNReal.ofReal q₆)
    (h7 : ¬ β < indScale t₀ n ^ (5 * indDelta d) →
      Pe {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (env ω) ι} ≤ ENNReal.ofReal q₇) :
    Pe {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤
      ENNReal.ofReal ϖ + ENNReal.ofReal (max q₆ q₇) := by
  by_cases hc : β < indScale t₀ n ^ (5 * indDelta d)
  · have hsub : {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ᵐ[Pe]
        {ω | pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ∪
        {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} := by
      filter_upwards [hgood] with ω hω hmem
      by_cases hf : pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))
      · exact Or.inl hf
      · exact Or.inr ((taubad_det hd ht1 ht4 hβ hT hω (not_le.1 hf) hmem).1 hc)
    refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add hfast ((h6 hc).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  · have hsub : {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ᵐ[Pe]
        {ω | pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ∪
        {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (env ω) ι} := by
      filter_upwards [hgood] with ω hω hmem
      by_cases hf : pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))
      · exact Or.inl hf
      · exact Or.inr ((taubad_det hd ht1 ht4 hβ hT hω (not_le.1 hf) hmem).2 hc)
    refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add hfast ((h7 hc).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))

end ElboimSly.Paper.Heavy
