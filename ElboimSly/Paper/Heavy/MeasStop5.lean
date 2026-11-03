/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop4
public import ElboimSly.Paper.Heavy.MeasFast

/-!
# The closing time and the stopping time `τ_V`

Measurability (c) (`T_reg`) and (e) (`τ_V`).

* `cycClosingTime_le_iff`: `T(w) ≤ t` iff `w (ℓβ) = 0` for some integer `1 ≤ ℓ` with `ℓβ ≤ t`.
* `AdaptedCyclic.isStoppingTime_cycClosingTime`.
* `heavyTauV`, `AdaptedCyclic.isStoppingTime_heavyTauV`: `τ_V = inf {ξ_{B'} : 0 < ξ_{B'} < ∞,
  V_{B'} ≤ c}` is a stopping time when each `V_{B'}` is `ℱ_{ξ_{B'}}`-measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

theorem cycClosingTime_le_iff {β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) :
    cycClosingTime β w ≤ ENNReal.ofReal T ↔
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ (ℓ : ℝ) * β ≤ T ∧ w (ℓ * β) = 0 := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have hlow : ENNReal.ofReal ((⌊T / β⌋₊ + 1 : ℕ) * β) ≤ cycClosingTime β w := by
      refine le_iInf₂ fun ℓ hℓ => ENNReal.ofReal_le_ofReal ?_
      refine mul_le_mul_of_nonneg_right ?_ hβ.le
      have hlt : T < ℓ * β := by
        by_contra hc
        exact hno ℓ hℓ.1 (not_lt.1 hc) hℓ.2
      have : T / β < ℓ := by rw [div_lt_iff₀ hβ]; exact hlt
      have h2 : ⌊T / β⌋₊ < ℓ := (Nat.floor_lt (by positivity)).2 this
      exact_mod_cast h2
    have h3 : T < ((⌊T / β⌋₊ + 1 : ℕ) : ℝ) * β := by
      have := Nat.lt_floor_add_one (T / β)
      push_cast
      rw [← div_lt_iff₀ hβ]
      exact this
    have := hlow.trans h
    rw [ENNReal.ofReal_le_ofReal_iff hT] at this
    linarith
  · rintro ⟨ℓ, hℓ, hℓT, hw0⟩
    exact (iInf₂_le (f := fun ℓ (_ : ℓ ∈ {ℓ : ℕ | 1 ≤ ℓ ∧ w (ℓ * β) = 0}) =>
      ENNReal.ofReal (ℓ * β)) ℓ ⟨hℓ, hw0⟩).trans (ENNReal.ofReal_le_ofReal hℓT)

variable {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {W : Ω → ℝ → Fin d → ℤ}

/-- Measurability (c): `T(W)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_cycClosingTime (h : AdaptedCyclic f W) {β : ℝ}
    (hβ : 0 < β) : IsStoppingTime f (fun ω => cycClosingTime β (W ω)) := by
  intro i
  have hset : {ω | cycClosingTime β (W ω) ≤ (i : WithTop ℝ≥0)} =
      ⋃ ℓ : ℕ, ⋃ _ : 1 ≤ ℓ ∧ (ℓ : ℝ) * β ≤ i, {ω | W ω (ℓ * β) = 0} := by
    ext ω
    have := cycClosingTime_le_iff (w := W ω) hβ (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    exact this.trans (by simp only [and_assoc])
  have key : MeasurableSet[f i] (⋃ ℓ : ℕ, ⋃ _ : 1 ≤ ℓ ∧ (ℓ : ℝ) * β ≤ i,
      {ω | W ω (ℓ * β) = 0}) := by
    refine MeasurableSet.iUnion fun ℓ => MeasurableSet.iUnion fun hℓ => ?_
    exact h.measurableSet_mem (by have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.1
                                  positivity) hℓ.2 {0}
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

/-- The blocks of `ℬ_j` whose entrance time is at most `T` form a finite set. -/
theorem entrance_sublevel_finite (hw : IsCyclicPath w) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    {ι : Fin d → ℤ | entranceTime w (heavyBlock j ι) ≤ ENNReal.ofReal T}.Finite := by
  have hV : (w '' Set.Icc 0 T).Finite := (hw.ncard_image_Icc_le le_rfl hT).1
  refine (hV.image (heavyBlockIdx j)).subset ?_
  intro ι hι
  have h0 : entranceTime w (heavyBlock j ι) ≤ ENNReal.ofReal T := hι
  have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ heavyBlock j ι := by
    by_contra hno
    push Not at hno
    rw [entranceTime_eq_top_of_empty hno] at h0
    exact absurd h0 (by simp)
  obtain ⟨s, hs0, hsB⟩ := hne
  obtain ⟨s'', h0', -, hmem, heq⟩ := exists_entrance_real hw hs0 hsB
  rw [heq] at h0
  have hs''T : s'' ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 h0
  exact ⟨w s'', ⟨s'', ⟨h0', hs''T⟩, rfl⟩, heavyBlock_eq_of_mem (mem_heavyBlock_idx j _) hmem⟩

/-- Measurability (e). `τ_V = inf {ξ_{B'} : B' ∈ ℬ_j, 0 < ξ_{B'} < ∞,
V_{B'} ≤ c}` (`inf ∅ = ∞`). -/
noncomputable def heavyTauV (w : ℝ → Fin d → ℤ) (j : ℕ) (V : (Fin d → ℤ) → ℝ) (c : ℝ) : ℝ≥0∞ :=
  ⨅ ι ∈ {ι : Fin d → ℤ | 0 < entranceTime w (heavyBlock j ι) ∧
      entranceTime w (heavyBlock j ι) < ⊤ ∧ V ι ≤ c}, entranceTime w (heavyBlock j ι)

/-- The infimum defining `τ_V` is attained when finite, and `τ_V ≤ T` iff some admissible
`B'` has `ξ_{B'} ≤ T`. -/
theorem heavyTauV_le_iff (hw : IsCyclicPath w) (j : ℕ) (V : (Fin d → ℤ) → ℝ) (c : ℝ) {T : ℝ}
    (_hT : 0 ≤ T) :
    heavyTauV w j V c ≤ ENNReal.ofReal T ↔
      ∃ ι : Fin d → ℤ, 0 < entranceTime w (heavyBlock j ι) ∧
        entranceTime w (heavyBlock j ι) ≤ ENNReal.ofReal T ∧ V ι ≤ c := by
  constructor
  · intro h
    have heq : heavyTauV w j V c = ⨅ p : {ι : Fin d → ℤ | 0 < entranceTime w (heavyBlock j ι) ∧
        entranceTime w (heavyBlock j ι) < ⊤ ∧ V ι ≤ c}, entranceTime w (heavyBlock j p.1) :=
      iInf_subtype'
    have hfin : ⨅ p : {ι : Fin d → ℤ | 0 < entranceTime w (heavyBlock j ι) ∧
        entranceTime w (heavyBlock j ι) < ⊤ ∧ V ι ≤ c},
        entranceTime w (heavyBlock j p.1) < ⊤ := by
      rw [← heq]; exact h.trans_lt ENNReal.ofReal_lt_top
    obtain ⟨p, hp⟩ := iInf_attained_of_finite_sublevel
      (fun p : {ι : Fin d → ℤ | 0 < entranceTime w (heavyBlock j ι) ∧
        entranceTime w (heavyBlock j ι) < ⊤ ∧ V ι ≤ c} => entranceTime w (heavyBlock j p.1))
      (fun T' hT' => (entrance_sublevel_finite hw j hT').preimage Subtype.val_injective.injOn)
      hfin
    refine ⟨p.1, p.2.1, ?_, p.2.2.2⟩
    rw [hp]
    rw [← heq]; exact h
  · rintro ⟨ι, h0, hι, hV⟩
    refine (iInf₂_le (f := fun ι (_ : ι ∈ {ι : Fin d → ℤ | 0 < entranceTime w (heavyBlock j ι) ∧
        entranceTime w (heavyBlock j ι) < ⊤ ∧ V ι ≤ c}) => entranceTime w (heavyBlock j ι)) ι
      ⟨h0, hι.trans_lt ENNReal.ofReal_lt_top, hV⟩).trans hι

/-- Measurability (e): `τ_V` is a stopping time when `V_{B'}` is
`ℱ_{ξ_{B'}}`-measurable. -/
theorem AdaptedCyclic.isStoppingTime_heavyTauV (h : AdaptedCyclic f W) (j : ℕ)
    (V : (Fin d → ℤ) → Ω → ℝ) (c : ℝ)
    (hV : ∀ ι, Measurable[(h.isStoppingTime_entrance (heavyBlock j ι)).measurableSpace] (V ι)) :
    IsStoppingTime f (fun ω => heavyTauV (W ω) j (fun ι => V ι ω) c) := by
  intro i
  have hset : {ω | heavyTauV (W ω) j (fun ι => V ι ω) c ≤ (i : WithTop ℝ≥0)} =
      ⋃ ι : Fin d → ℤ, (({ω | V ι ω ≤ c} ∩ {ω | entranceTime (W ω) (heavyBlock j ι) ≤ i}) ∩
        {ω | entranceTime (W ω) (heavyBlock j ι) ≤ (0 : ℝ≥0)}ᶜ) := by
    ext ω
    have := heavyTauV_le_iff (h.path ω) j (fun ι => V ι ω) c (T := (i : ℝ))
      (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff, not_le]
    refine this.trans (exists_congr fun ι => ?_)
    simp only [ENNReal.coe_zero, pos_iff_ne_zero, ne_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h3, h2⟩, by simpa [nonpos_iff_eq_zero] using h1⟩
    · rintro ⟨⟨h3, h2⟩, h1⟩; exact ⟨by simpa [nonpos_iff_eq_zero] using h1, h2, h3⟩
  have key : MeasurableSet[f i] (⋃ ι : Fin d → ℤ,
      (({ω | V ι ω ≤ c} ∩ {ω | entranceTime (W ω) (heavyBlock j ι) ≤ i}) ∩
        {ω | entranceTime (W ω) (heavyBlock j ι) ≤ (0 : ℝ≥0)}ᶜ)) := by
    refine MeasurableSet.iUnion fun ι => ?_
    have hξ := h.isStoppingTime_entrance (heavyBlock j ι)
    refine MeasurableSet.inter ?_ ((f.mono (zero_le : (0 : ℝ≥0) ≤ i) _ (hξ 0)).compl)
    have hmeas : MeasurableSet[hξ.measurableSpace] {ω | V ι ω ≤ c} :=
      hV ι measurableSet_Iic
    exact ((hξ.measurableSet _).1 hmeas).2 i
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

end ElboimSly.Paper
