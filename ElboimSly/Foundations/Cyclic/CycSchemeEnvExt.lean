/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.Cyclic.CycRecLimit
public import Mathlib

/-!
# The environment scheme (b): the records of the scheme extend each other

The environment scheme (b), measurability of record functionals (e). `shape P ν k r` is the record of the first
`k` full environment world-lines and the initial piece of walk `k` at time `r`. For a state with
`EnvAt` and a good outcome, the record of `upd` extends the old one (`extends_upd`): this is the
hypothesis `hext` of `recLim`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)}

/-- The record of the first `k` full environment world-lines and the initial piece of walk `k` at
time `r`. -/
noncomputable def shape (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (k : ℕ) (r : ℝ≥0) :
    CycRec I d :=
  Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k) (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞))⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_shape_lt (k : ℕ) (r : ℝ≥0) {i : ℕ} (hi : i < k) :
    (shape P ν k r).nth i = some (P.E (rule P ν) i) := by
  simp only [shape, CycRec.nth, dite_eq_left (Nat.lt_succ_of_lt hi)]
  congr 1
  have : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this]
  simp only [CycRec.snoc, Fin.snoc_castSucc]
  exact P.ideal_apply (rule P ν) k ⟨i, hi⟩

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem nth_shape_self (k : ℕ) (r : ℝ≥0) :
    (shape P ν k r).nth k = some (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) := by
  simp only [shape, CycRec.nth, dite_eq_left (Nat.lt_succ_self k)]
  congr 1
  have : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this]
  simp [CycRec.snoc]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem nth_shape_gt (k : ℕ) (r : ℝ≥0) {i : ℕ} (hi : k < i) : (shape P ν k r).nth i = none := by
  simp only [shape, CycRec.nth, dite_eq_right (show ¬ i < k + 1 by omega)]

theorem isPiece_cut (p : CPath (Fin d → ℤ)) {r r' : ℝ≥0∞} (h : r ≤ r') :
    (p.cut r).IsPiece (p.cut r') := by
  refine ⟨by simpa using h, ?_⟩
  rw [CPath.cut_len, CPath.cut_cut p h]

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem extends_shape_same (k : ℕ) {r r' : ℝ≥0} (h : r ≤ r') :
    (shape P ν k r).Extends (shape P ν k r') := by
  intro i e he
  rcases lt_trichotomy i k with hi | heq | hi
  · rw [nth_shape_lt k r hi] at he
    refine ⟨e, by rw [nth_shape_lt k r' hi]; exact he, rfl, ?_⟩
    exact CPath.isPiece_refl _
  · rw [heq, nth_shape_self] at he
    cases he
    exact ⟨(dat P ν k, (pth P ν k).cut (r' : ℝ≥0∞)), by rw [heq]; exact nth_shape_self k r', rfl,
      isPiece_cut (pth P ν k).1 (by exact_mod_cast h : (r : ℝ≥0∞) ≤ r')⟩
  · rw [nth_shape_gt k r hi] at he
    exact absurd he (by simp)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem extends_shape_next (k : ℕ) {r : ℝ≥0} (h : (r : ℝ≥0∞) ≤ sInf (cand P ν k)) :
    (shape P ν k r).Extends (shape P ν (k + 1) 0) := by
  intro i e he
  rcases lt_trichotomy i k with hi | heq | hi
  · rw [nth_shape_lt k r hi] at he
    refine ⟨e, by rw [nth_shape_lt (k + 1) 0 (Nat.lt_succ_of_lt hi)]; exact he, rfl, ?_⟩
    exact CPath.isPiece_refl _
  · rw [heq, nth_shape_self] at he
    cases he
    refine ⟨P.E (rule P ν) k, by rw [heq]; exact nth_shape_lt (k := k + 1) 0 (Nat.lt_succ_self k), rfl, ?_⟩
    rw [E_eq]
    exact isPiece_cut _ h
  · rw [nth_shape_gt k r hi] at he
    exact absurd he (by simp)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem EnvAt.eq_shape {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    ρ = shape P ν k r := h.rec_eq

theorem extends_upd {sc : ℝ≥0∞} (hν : CycGood ν) {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}
    (h : EnvAt P ν k r ρ) {o : Outcome (CycS I d β)} (hg : StepGood P sc ν ρ o) :
    ρ.Extends (CycScheme.upd P sc (ρ, false) o).1 := by
  by_cases hs : CycScheme.stops P sc (ρ, false) o
  · by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
    · obtain ⟨-, h2⟩ := upd_stop_next hν h hg hs hK
      have := extends_shape_next (P := P) (ν := ν) k h.le_sInf
      rw [← h.eq_shape, ← h2.eq_shape] at this
      exact this
    · rw [upd_stop_end hν h hg hs hK]
      have e : (Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ : CycRec I d) =
          shape P ν k (r + CycScheme.sStar P sc (ρ, false) o) := by
        show (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k)⟩ : CycRec I d) = _
        rw [E_eq_of_stops hν h hg hs]
        rfl
      show ρ.Extends (Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ : CycRec I d)
      rw [e]
      have := extends_shape_same (P := P) (ν := ν) k
        (le_self_add : r ≤ r + CycScheme.sStar P sc (ρ, false) o)
      rw [← h.eq_shape] at this
      exact this
  · obtain ⟨h1, -⟩ := upd_notStop hν h hg hs
    have := extends_shape_same (P := P) (ν := ν) k
      (le_self_add : r ≤ r + CycScheme.sStar P sc (ρ, false) o)
    rw [← h.eq_shape, ← h1.eq_shape] at this
    exact this

end CycSchemeEnv
end ElboimSly.Cyclic

end
