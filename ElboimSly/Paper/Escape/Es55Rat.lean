/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Incl
public import Mathlib

/-!
# Rational form of events of right-continuous step paths

ES22 Lemma 5.5, Step 1 (freezing at `S₃` needs a measurable set of paths).

For a right-continuous path `y : ℝ≥0 → ℤ^d` the statements "`P (y t)`" and "`P (y s)` for all
`s ∈ [a, b]`" are expressed by evaluating `y` at rational times only (`ratVal`, `ratIcc`).  Then
`EscRat` is the rational form of the event `E₅₆` of ES22 Claim 5.6 for the path `v + y`, and is a
measurable set of `(v, z, t, y)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace ElboimSly.Paper.Escape

variable {d : ℕ}

/-- Right-continuity of a path `ℝ≥0 → ℤ^d` (locally constant on the right). -/
def RC (y : ℝ≥0 → Fin d → ℤ) : Prop := ∀ s : ℝ≥0, ∀ᶠ u in 𝓝[≥] s, y u = y s

/-- `P (y t)`, read at rational times just to the right of `t`. -/
def ratVal (y : ℝ≥0 → Fin d → ℤ) (t : ℝ) (P : (Fin d → ℤ) → Prop) : Prop :=
  ∃ q0 : ℚ, t < q0 ∧ ∀ q : ℚ, t < q → (q : ℝ) < q0 → P (y (q : ℝ).toNNReal)

/-- `P (y s)` for all `s ∈ [a, b]`, read at rational times. -/
def ratIcc (y : ℝ≥0 → Fin d → ℤ) (a b : ℝ) (P : (Fin d → ℤ) → Prop) : Prop :=
  (∀ q : ℚ, a ≤ q → (q : ℝ) < b → P (y (q : ℝ).toNNReal)) ∧ (a ≤ b → ratVal y b P)

theorem es55_exists_Ico_const {y : ℝ≥0 → Fin d → ℤ} (hy : RC y) (s : ℝ≥0) :
    ∃ u1 : ℝ≥0, s < u1 ∧ ∀ u, s ≤ u → u < u1 → y u = y s := by
  obtain ⟨u1, hu1, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hy s)
  exact ⟨u1, hu1, fun u h1 h2 => hsub ⟨h1, h2⟩⟩

/-- A rational strictly between two reals. -/
theorem ratVal_iff {y : ℝ≥0 → Fin d → ℤ} (hy : RC y) {t : ℝ} (ht : 0 ≤ t)
    (P : (Fin d → ℤ) → Prop) : ratVal y t P ↔ P (y t.toNNReal) := by
  obtain ⟨u1, hu1, hc⟩ := es55_exists_Ico_const hy t.toNNReal
  have hu1R : t < (u1 : ℝ) := by
    have := (NNReal.coe_lt_coe.2 hu1); rwa [Real.coe_toNNReal _ ht] at this
  constructor
  · rintro ⟨q0, hq0, hq⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hq0 hu1R)
    have hq0' : (0 : ℝ) ≤ q := by linarith [lt_of_le_of_lt ht hq1]
    have h := hq q hq1 (lt_of_lt_of_le hq2 (min_le_left _ _))
    have hqu : (q : ℝ).toNNReal < u1 := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0']
      exact lt_of_lt_of_le hq2 (min_le_right _ _)
    have hts : t.toNNReal ≤ (q : ℝ).toNNReal := Real.toNNReal_le_toNNReal hq1.le
    rwa [hc _ hts hqu] at h
  · intro h
    obtain ⟨q0, hq1, hq2⟩ := exists_rat_btwn hu1R
    refine ⟨q0, hq1, fun q hq hqq => ?_⟩
    have hq0' : (0 : ℝ) ≤ q := by linarith [lt_of_le_of_lt ht hq]
    have hqu : (q : ℝ).toNNReal < u1 := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0']
      exact lt_trans hqq hq2
    have hts : t.toNNReal ≤ (q : ℝ).toNNReal := Real.toNNReal_le_toNNReal hq.le
    rwa [hc _ hts hqu]

theorem ratIcc_iff {y : ℝ≥0 → Fin d → ℤ} (hy : RC y) {a b : ℝ} (ha : 0 ≤ a)
    (P : (Fin d → ℤ) → Prop) :
    ratIcc y a b P ↔ ∀ s : ℝ, a ≤ s → s ≤ b → P (y s.toNNReal) := by
  constructor
  · rintro ⟨h1, h2⟩ s hs1 hs2
    rcases hs2.eq_or_lt with rfl | hlt
    · exact (ratVal_iff hy (by linarith) P).1 (h2 hs1)
    · obtain ⟨u1, hu1, hc⟩ := es55_exists_Ico_const hy s.toNNReal
      have hs0 : 0 ≤ s := le_trans ha hs1
      have hu1R : s < (u1 : ℝ) := by
        have := (NNReal.coe_lt_coe.2 hu1); rwa [Real.coe_toNNReal _ hs0] at this
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlt hu1R)
      have hq0' : (0 : ℝ) ≤ q := by linarith
      have h := h1 q (by linarith) (lt_of_lt_of_le hq2 (min_le_left _ _))
      have hqu : (q : ℝ).toNNReal < u1 := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0']
        exact lt_of_lt_of_le hq2 (min_le_right _ _)
      have hts : s.toNNReal ≤ (q : ℝ).toNNReal := Real.toNNReal_le_toNNReal (by linarith)
      rwa [hc _ hts hqu] at h
  · intro h
    refine ⟨fun q hq1 hq2 => h q hq1 hq2.le, fun hab => ?_⟩
    exact (ratVal_iff hy (by linarith) P).2 (h b hab le_rfl)

/-- The rational form of `E₅₆` for the path `v + y`. -/
def EscRat (β : ℝ) (j : ℕ) {k : ℕ} (u v z : Fin (k + 2) → ℤ) (t : ℝ)
    (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ratVal y t (fun x => v + x = z) ∧ ratIcc y 0 t (fun x => v + x ∈ escBlockMinus j u) ∧
    ratIcc y β t (fun x => v + x ≠ v) ∧ ratIcc y 0 (t - β) (fun x => v + x ≠ z)

theorem esc56_iff_rat {β : ℝ} (hβ : 0 ≤ β) {j k : ℕ} {u v z : Fin (k + 2) → ℤ} {t : ℝ}
    (ht : 0 ≤ t) {y : ℝ≥0 → Fin (k + 2) → ℤ} (hy : RC y) :
    Esc56Event β j u v z t (fun r => v + y r.toNNReal) ↔ EscRat β j u v z t y := by
  unfold Esc56Event EscRat
  rw [ratVal_iff hy ht, ratIcc_iff hy le_rfl, ratIcc_iff hy hβ, ratIcc_iff hy le_rfl]

/-- No jump at `t`, read at rational times. -/
def noJumpRat (y : ℝ≥0 → Fin d → ℤ) (t : ℝ) : Prop :=
  ∃ q0 : ℚ, 0 ≤ (q0 : ℝ) ∧ (q0 : ℝ) < t ∧ ∃ q1 : ℚ, t < q1 ∧ ∀ q q' : ℚ, (q0 : ℝ) < q →
    (q : ℝ) < t → t < q' → (q' : ℝ) < q1 → y (q : ℝ).toNNReal = y (q' : ℝ).toNNReal

theorem noJumpRat_iff {y : ℝ≥0 → Fin d → ℤ} (hy : RC y) {t : ℝ} (ht : 0 < t) :
    noJumpRat y t ↔
      ∃ l : ℝ, 0 ≤ l ∧ l < t ∧ ∀ s : ℝ, l < s → s < t → y s.toNNReal = y t.toNNReal := by
  obtain ⟨u1, hu1, hc⟩ := es55_exists_Ico_const hy t.toNNReal
  have hu1R : t < (u1 : ℝ) := by
    have := (NNReal.coe_lt_coe.2 hu1); rwa [Real.coe_toNNReal _ ht.le] at this
  constructor
  · rintro ⟨q0, hq00, hq0, q1, hq1t, h⟩
    refine ⟨q0, hq00, hq0, fun s hs1 hs2 => ?_⟩
    have hs0 : 0 ≤ s := by linarith
    obtain ⟨us, hus, hcs⟩ := es55_exists_Ico_const hy s.toNNReal
    have husR : s < (us : ℝ) := by
      have := (NNReal.coe_lt_coe.2 hus); rwa [Real.coe_toNNReal _ hs0] at this
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn (lt_min hs2 husR)
    obtain ⟨q', hqa', hqb'⟩ := exists_rat_btwn (lt_min hq1t hu1R)
    have hqt : (q : ℝ) < t := lt_of_lt_of_le hqb (min_le_left _ _)
    have hqus : (q : ℝ) < us := lt_of_lt_of_le hqb (min_le_right _ _)
    have hq0' : 0 ≤ (q : ℝ) := by linarith
    have hq'0 : 0 ≤ (q' : ℝ) := by linarith
    have e1 : y (q : ℝ).toNNReal = y s.toNNReal := by
      refine hcs _ (Real.toNNReal_le_toNNReal hqa.le) ?_
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0']; exact hqus
    have e2 : y (q' : ℝ).toNNReal = y t.toNNReal := by
      refine hc _ (Real.toNNReal_le_toNNReal hqa'.le) ?_
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq'0]
      exact lt_of_lt_of_le hqb' (min_le_right _ _)
    have e3 := h q q' (by linarith) hqt hqa' (lt_of_lt_of_le hqb' (min_le_left _ _))
    rw [← e1, e3, e2]
  · rintro ⟨l, hl0, hlt, h⟩
    obtain ⟨q0, hq0a, hq0b⟩ := exists_rat_btwn hlt
    obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn hu1R
    refine ⟨q0, by linarith, hq0b, q1, hq1a, fun q q' h1 h2 h3 h4 => ?_⟩
    have hqpos : 0 ≤ (q : ℝ) := by linarith
    have e1 : y (q : ℝ).toNNReal = y t.toNNReal := h q (by linarith) h2
    have hq'0 : 0 ≤ (q' : ℝ) := by linarith
    have hqu : (q' : ℝ).toNNReal < u1 := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq'0]; linarith
    have hts : t.toNNReal ≤ (q' : ℝ).toNNReal := Real.toNNReal_le_toNNReal h3.le
    rw [e1, hc _ hts hqu]

section meas

variable {X : Type*} [MeasurableSpace X] {C : Type*} [MeasurableSpace C] [Countable C]
  [MeasurableSingletonClass C]

theorem es55_measurableSet_atom (c : X → C) (hc : Measurable c) (y : X → ℝ≥0 → Fin d → ℤ)
    (hy : Measurable y) (r : ℝ≥0) (P : C → (Fin d → ℤ) → Prop) :
    MeasurableSet {x | P (c x) (y x r)} := by
  have h : Measurable fun x => (c x, y x r) :=
    hc.prodMk ((measurable_pi_apply r).comp hy)
  exact (MeasurableSet.of_discrete (s := {p : C × (Fin d → ℤ) | P p.1 p.2})).preimage h

theorem measurableSet_ratVal (t : X → ℝ) (ht : Measurable t) (c : X → C) (hc : Measurable c)
    (y : X → ℝ≥0 → Fin d → ℤ) (hy : Measurable y) (P : C → (Fin d → ℤ) → Prop) :
    MeasurableSet {x | ratVal (y x) (t x) (P (c x))} := by
  have e : {x | ratVal (y x) (t x) (P (c x))} = ⋃ q0 : ℚ, ({x | t x < q0} ∩
      ⋂ q : ℚ, ({x | ¬ (t x < q ∧ (q : ℝ) < q0)} ∪ {x | P (c x) (y x (q : ℝ).toNNReal)})) := by
    ext x
    simp only [ratVal, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter, mem_union]
    constructor
    · rintro ⟨q0, h1, h2⟩
      exact ⟨q0, h1, fun q => by by_cases h : t x < q ∧ (q : ℝ) < q0 <;> simp_all⟩
    · rintro ⟨q0, h1, h2⟩
      exact ⟨q0, h1, fun q hq hq' => by
        rcases h2 q with h | h
        · exact absurd ⟨hq, hq'⟩ h
        · exact h⟩
  rw [e]
  refine MeasurableSet.iUnion fun q0 => (measurableSet_lt ht measurable_const).inter ?_
  refine MeasurableSet.iInter fun q => MeasurableSet.union ?_ (es55_measurableSet_atom c hc y hy _ P)
  exact ((measurableSet_lt ht measurable_const).inter (MeasurableSet.const _)).compl

theorem measurableSet_ratIcc (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b) (c : X → C)
    (hc : Measurable c) (y : X → ℝ≥0 → Fin d → ℤ) (hy : Measurable y)
    (P : C → (Fin d → ℤ) → Prop) :
    MeasurableSet {x | ratIcc (y x) (a x) (b x) (P (c x))} := by
  have e : {x | ratIcc (y x) (a x) (b x) (P (c x))} =
      (⋂ q : ℚ, ({x | ¬ (a x ≤ q ∧ (q : ℝ) < b x)} ∪ {x | P (c x) (y x (q : ℝ).toNNReal)})) ∩
      ({x | ¬ (a x ≤ b x)} ∪ {x | ratVal (y x) (b x) (P (c x))}) := by
    ext x
    simp only [ratIcc, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun q => by by_cases h : a x ≤ q ∧ (q : ℝ) < b x <;> simp_all,
        by by_cases h : a x ≤ b x <;> simp_all⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun q hq hq' => ?_, fun h => ?_⟩
      · rcases h1 q with h | h
        · exact absurd ⟨hq, hq'⟩ h
        · exact h
      · rcases h2 with h' | h'
        · exact absurd h h'
        · exact h'
  rw [e]
  refine (MeasurableSet.iInter fun q => MeasurableSet.union ?_
    (es55_measurableSet_atom c hc y hy _ P)).inter (MeasurableSet.union ?_
    (measurableSet_ratVal b hb c hc y hy P))
  · exact ((measurableSet_le ha measurable_const).inter
      (measurableSet_lt measurable_const hb)).compl
  · exact (measurableSet_le ha hb).compl

theorem measurableSet_noJumpRat (t : X → ℝ) (ht : Measurable t) (y : X → ℝ≥0 → Fin d → ℤ)
    (hy : Measurable y) : MeasurableSet {x | noJumpRat (y x) (t x)} := by
  have e : {x | noJumpRat (y x) (t x)} = ⋃ q0 : ℚ, ⋃ q1 : ℚ, ({x | 0 ≤ (q0 : ℝ)} ∩
      {x | (q0 : ℝ) < t x} ∩ {x | t x < q1} ∩ ⋂ q : ℚ, ⋂ q' : ℚ,
        ({x | ¬ ((q0 : ℝ) < q ∧ (q : ℝ) < t x ∧ t x < q' ∧ (q' : ℝ) < q1)} ∪
          {x | y x (q : ℝ).toNNReal = y x (q' : ℝ).toNNReal})) := by
    ext x
    simp only [noJumpRat, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter, mem_union]
    constructor
    · rintro ⟨q0, h0, h1, q1, h2, h3⟩
      exact ⟨q0, q1, ⟨⟨h0, h1⟩, h2⟩, fun q q' => by
        by_cases h : (q0 : ℝ) < q ∧ (q : ℝ) < t x ∧ t x < q' ∧ (q' : ℝ) < q1
        · exact Or.inr (h3 q q' h.1 h.2.1 h.2.2.1 h.2.2.2)
        · exact Or.inl h⟩
    · rintro ⟨q0, q1, ⟨⟨h0, h1⟩, h2⟩, h3⟩
      exact ⟨q0, h0, h1, q1, h2, fun q q' a b c d => by
        rcases h3 q q' with h | h
        · exact absurd ⟨a, b, c, d⟩ h
        · exact h⟩
  rw [e]
  refine MeasurableSet.iUnion fun q0 => MeasurableSet.iUnion fun q1 => ?_
  refine ((MeasurableSet.const _ |>.inter (measurableSet_lt measurable_const ht)).inter
    (measurableSet_lt ht measurable_const)).inter ?_
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => MeasurableSet.union ?_ ?_
  · exact ((MeasurableSet.const _).inter ((measurableSet_lt measurable_const ht).inter
      ((measurableSet_lt ht measurable_const).inter (MeasurableSet.const _)))).compl
  · have h1 : Measurable fun x => y x (q : ℝ).toNNReal := (measurable_pi_apply _).comp hy
    have h2 : Measurable fun x => y x (q' : ℝ).toNNReal := (measurable_pi_apply _).comp hy
    exact measurableSet_eq_fun h1 h2

theorem measurableSet_escRat {k : ℕ} (β : ℝ) (j : ℕ) (u : Fin (k + 2) → ℤ)
    (v z : X → Fin (k + 2) → ℤ) (t : X → ℝ) (y : X → ℝ≥0 → Fin (k + 2) → ℤ) (hv : Measurable v)
    (hz : Measurable z) (ht : Measurable t) (hy : Measurable y) :
    MeasurableSet {x | EscRat β j u (v x) (z x) (t x) (y x)} := by
  have hc : Measurable fun x => (v x, z x) := hv.prodMk hz
  unfold EscRat
  refine (measurableSet_ratVal t ht _ hc y hy
    (fun c w => c.1 + w = c.2)).inter ((measurableSet_ratIcc (fun _ => 0) t measurable_const ht _
    hc y hy (fun c w => c.1 + w ∈ escBlockMinus j u)).inter
    ((measurableSet_ratIcc (fun _ => β) t measurable_const ht _ hc y hy
    (fun c w => c.1 + w ≠ c.1)).inter (measurableSet_ratIcc (fun _ => 0) (fun x => t x - β)
    measurable_const (ht.sub_const β) _ hc y hy (fun c w => c.1 + w ≠ c.2))))

end meas

end ElboimSly.Paper.Escape
