/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvAt
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvRegLim
public import ElboimSly.Foundations.Cyclic.CycDrivenEvents
public import Mathlib

/-!
# The driving scheme (c): the region and the rings of a driven record

The driving scheme (c), (i). "At the times `r'' ∈ (r, r + s*]`, the sets `Z_{<r''}`,
`Q_{<r''}` of world-lines of a plan; joint exploration filtration (b) differ from `cycReg(ρ)`, `cycRing(ρ)` only at the cyclic times
`c_δ((r, r''))`, which do not contain `c_δ(r'')` because `h ≤ β`."

* `isEntry_snoc_iff`, `region_gAt`, `ringSet_gAt`: for a record with `GAt P rl k r ρ`, the region
  and the rings are those of the first `k` world-lines together with those of the initial piece
  of walk `k`;
* `mem_Z_iff_region`, `mem_Q_iff_ringSet`: at the cyclic time `c_δ(r'')` with `r < r'' ≤ r + β`
  the driven sets `R ∪ Z_own(r'')` and `Q ∪ Q_own(r'')` agree with `ρ.region` and `ρ.ringSet`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem snoc_castSucc' {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) (i : Fin k) :
    CycRec.snoc g e (Fin.castSucc i) = g i := by
  simp [CycRec.snoc]

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem snoc_last' {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) :
    CycRec.snoc g e (Fin.last k) = e := by
  simp [CycRec.snoc]

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem isEntry_snoc_iff {k : ℕ} (g : CycRecN I d k) (e e' : CycEntry I d) :
    CycRec.IsEntry (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) e' ↔
      CycRec.IsEntry (Sum.inl ⟨k, g⟩ : CycRec I d) e' ∨ e' = e := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [CycRec.nth] at hn
    split_ifs at hn with h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hlt | heq
    · left
      refine ⟨n, ?_⟩
      simp only [CycRec.nth, hlt, dite_true]
      have : (⟨n, h⟩ : Fin (k + 1)) = Fin.castSucc ⟨n, hlt⟩ := rfl
      rw [this, snoc_castSucc'] at hn
      exact hn
    · right
      have : (⟨n, h⟩ : Fin (k + 1)) = Fin.last k := Fin.ext heq
      rw [this, snoc_last'] at hn
      exact (Option.some.inj hn).symm
  · rintro (⟨n, hn⟩ | rfl)
    · simp only [CycRec.nth] at hn
      split_ifs at hn with h
      refine ⟨n, ?_⟩
      simp only [CycRec.nth, Nat.lt_succ_of_lt h, dite_true]
      have : (⟨n, Nat.lt_succ_of_lt h⟩ : Fin (k + 1)) = Fin.castSucc ⟨n, h⟩ := rfl
      rw [this, snoc_castSucc']
      exact hn
    · refine ⟨k, ?_⟩
      simp only [CycRec.nth, Nat.lt_succ_self k, dite_true]
      have : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [this, snoc_last']

omit [Fact (0 < β)] in
omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem region_snoc {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) :
    CycRec.region β (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) =
      CycRec.region β (Sum.inl ⟨k, g⟩ : CycRec I d) ∪ e.region β := by
  ext x
  constructor
  · rintro ⟨e', he', hx⟩
    rcases (isEntry_snoc_iff g e e').1 he' with h | rfl
    · exact Or.inl ⟨e', h, hx⟩
    · exact Or.inr hx
  · rintro (⟨e', he', hx⟩ | hx)
    · exact ⟨e', (isEntry_snoc_iff g e e').2 (Or.inl he'), hx⟩
    · exact ⟨e, (isEntry_snoc_iff g e e).2 (Or.inr rfl), hx⟩

omit [Fact (0 < β)] in
omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem ringSet_snoc {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) :
    CycRec.ringSet β (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) =
      CycRec.ringSet β (Sum.inl ⟨k, g⟩ : CycRec I d) ∪ e.ringSet β := by
  ext x
  constructor
  · rintro ⟨e', he', hx⟩
    rcases (isEntry_snoc_iff g e e').1 he' with h | rfl
    · exact Or.inl ⟨e', h, hx⟩
    · exact Or.inr hx
  · rintro (⟨e', he', hx⟩ | hx)
    · exact ⟨e', (isEntry_snoc_iff g e e').2 (Or.inl he'), hx⟩
    · exact ⟨e, (isEntry_snoc_iff g e e).2 (Or.inr rfl), hx⟩

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem mem_ringSet_cut_iff (δ : CycData I d) (p : CycPath d) (ℓ : ℝ≥0∞)
    (x : I × RingSpace d β) :
    x ∈ CycEntry.ringSet β ((δ, p.cut ℓ) : CycEntry I d) ↔
      ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ ℓ ∧ p.1.left r ≠ p.1.fn r ∧ x.1 = δ.copy ∧
        x.2.2 = δ.clock β r ∧ x.2.1.1 = s(p.1.left r, p.1.fn r) := by
  have hlen : CycEntry.len ((δ, p.cut ℓ) : CycEntry I d) = ℓ := CPath.cut_len _ _
  have hfn : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ℓ → (p.cut ℓ).1.fn r = p.1.fn r := fun r hr => by
    show (p.1.cut ℓ).fn r = _
    rw [CPath.cut_fn, min_eq_left hr]; simp
  constructor
  · rintro ⟨r, hr0, hrl, hne, h1, h2, h3⟩
    rw [hlen] at hrl
    have hl : (p.cut ℓ).1.left r = p.1.left r := CPath.left_cut _ _ hr0 hrl
    have hf := hfn r hrl
    have hne' : p.1.left r ≠ p.1.fn r := by rw [← hl, ← hf]; exact hne
    have h3' : x.2.1.1 = s(p.1.left r, p.1.fn r) := by rw [← hl, ← hf]; exact h3
    exact ⟨r, hr0, hrl, hne', h1, h2, h3'⟩
  · rintro ⟨r, hr0, hrl, hne, h1, h2, h3⟩
    have hl : (p.cut ℓ).1.left r = p.1.left r := CPath.left_cut _ _ hr0 hrl
    have hf := hfn r hrl
    refine ⟨r, hr0, by rw [hlen]; exact hrl, ?_, h1, h2, ?_⟩
    · show (p.cut ℓ).1.left r ≠ (p.cut ℓ).1.fn r
      rw [hl, hf]; exact hne
    · show x.2.1.1 = s((p.cut ℓ).1.left r, (p.cut ℓ).1.fn r)
      rw [hl, hf]; exact h3

variable {J : Type*} {jx : ∀ k : ℕ, CycRecN I d k → J} {X : J → CycPath d}
  {P : CycPlan I d β} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}

omit [Countable I] [MeasurableSingletonClass I] in
theorem region_gAt (h : GAt P (drule P jx X) k r ρ) :
    ρ.region β = CycRec.region β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩ : CycRec I d) ∪
      CycEntry.region β (gdat P (drule P jx X) k, (gpth P (drule P jx X) k).cut (r : ℝ≥0∞)) := by
  rw [h.rec_eq]; exact region_snoc _ _

omit [Countable I] [MeasurableSingletonClass I] in
theorem ringSet_gAt (h : GAt P (drule P jx X) k r ρ) :
    ρ.ringSet β = CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩ : CycRec I d) ∪
      CycEntry.ringSet β (gdat P (drule P jx X) k,
        (gpth P (drule P jx X) k).cut (r : ℝ≥0∞)) := by
  rw [h.rec_eq]; exact ringSet_snoc _ _

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
/-- Cyclic times: if `r < r' < r''` and `r'' ≤ r + β` the clock values differ. -/
theorem clock_ne_of_close (δ : CycData I d) {r r' r'' : ℝ≥0} (h1 : r < r') (h2 : r' < r'')
    (h3 : (r'' : ℝ) ≤ r + β) : δ.clock β r' ≠ δ.clock β r'' := by
  intro hc
  obtain ⟨n, hn1, hn2⟩ := clock_eq_shift δ h2 hc
  have hβ : 0 < β := Fact.out
  have h1' : (r : ℝ) < r' := by exact_mod_cast h1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  nlinarith

omit [Countable I] [MeasurableSingletonClass I] in
/-- At the cyclic time `c_δ(r'')`, `r < r'' ≤ r + β`, the driven region `R ∪ Z_own(r'')` is the
region of the record. -/
theorem mem_Z_iff_region (h : GAt P (drule P jx X) k r ρ) {r'' : ℝ≥0} (h1 : r < r'')
    (h2 : (r'' : ℝ) ≤ r + β) {y : I × RingSpace d β}
    (hy2 : y.2.2 = (gdat P (drule P jx X) k).clock β r'') :
    y ∈ CycRec.region β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩ : CycRec I d) ∪
        drvZown β (gdat P (drule P jx X) k) (gpth P (drule P jx X) k).1 r'' ↔
      y ∈ ρ.region β := by
  rw [region_gAt h, Set.mem_union, Set.mem_union, CycSchemeEnv.mem_region_cut_iff]
  constructor
  · rintro (hR | ⟨r', hr0, hr1, hc1, hc2, hc3⟩)
    · exact Or.inl hR
    · right
      by_cases hle : r' ≤ r
      · exact ⟨r', hr0, by exact_mod_cast hle, hc1, hc2, hc3⟩
      · exfalso
        have : r < r' := not_le.1 hle
        exact clock_ne_of_close _ this hr1 h2 (hc2.symm.trans hy2)
  · rintro (hR | ⟨r', hr0, hr1, hc1, hc2, hc3⟩)
    · exact Or.inl hR
    · right
      have hr1' : r' ≤ r := by exact_mod_cast hr1
      exact ⟨r', hr0, lt_of_le_of_lt hr1' h1, hc1, hc2, hc3⟩

omit [Countable I] [MeasurableSingletonClass I] in
theorem mem_Q_iff_ringSet (h : GAt P (drule P jx X) k r ρ) {r'' : ℝ≥0} (h1 : r < r'')
    (h2 : (r'' : ℝ) ≤ r + β) {y : I × RingSpace d β}
    (hy2 : y.2.2 = (gdat P (drule P jx X) k).clock β r'') :
    y ∈ CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩ : CycRec I d) ∪
        drvQown β (gdat P (drule P jx X) k) (gpth P (drule P jx X) k).1 r'' ↔
      y ∈ ρ.ringSet β := by
  rw [ringSet_gAt h, Set.mem_union, Set.mem_union, mem_ringSet_cut_iff]
  constructor
  · rintro (hR | ⟨r', hr0, hr1, hne, hc1, hc2, hc3⟩)
    · exact Or.inl hR
    · right
      by_cases hle : r' ≤ r
      · exact ⟨r', hr0, by exact_mod_cast hle, hne, hc1, hc2, hc3⟩
      · exfalso
        have : r < r' := not_le.1 hle
        exact clock_ne_of_close _ this hr1 h2 (hc2.symm.trans hy2)
  · rintro (hR | ⟨r', hr0, hr1, hne, hc1, hc2, hc3⟩)
    · exact Or.inl hR
    · right
      have hr1' : r' ≤ r := by exact_mod_cast hr1
      exact ⟨r', hr0, lt_of_le_of_lt hr1' h1, hne, hc1, hc2, hc3⟩

end CycSchemeGen
end ElboimSly.Cyclic

end
