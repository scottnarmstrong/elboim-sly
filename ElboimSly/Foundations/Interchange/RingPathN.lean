/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.SymmGood
import Mathlib

/-!
# Ring paths indexed by `ℕ`

Ring paths; Symmetries preserve good configurations (transport rules).

`IsRingPath` is stated with `Fin`-indexed data, which is awkward for truncating and splicing. Here
`NRingPath μ J n v t` is the same notion for `ℕ`-indexed `v` and `t` (only `v 0, …, v n` and
`t 0, …, t (n-1)` matter). We prove the equivalence and the operations needed for (G3): truncation,
suffix, time reversal, time translation and the action of lattice automorphisms.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A ring path of length `n` with `ℕ`-indexed vertices and times. -/
def NRingPath (μ : Measure (RingSpace d β)) (J : Set ℝ) (n : ℕ) (v : ℕ → Fin d → ℤ)
    (t : ℕ → ℝ) : Prop :=
  (∀ i j, i < j → j < n → t i < t j) ∧ (∀ i, i < n → t i ∈ J) ∧
    ∀ i, i < n → ∃ e : Edge d, e.1 = s(v i, v (i + 1)) ∧ Rings μ e (t i)

/-- No ring path of length `n` in `J` starts at `y`. -/
def NoPathFrom (μ : Measure (RingSpace d β)) (J : Set ℝ) (y : Fin d → ℤ) (n : ℕ) : Prop :=
  ¬ ∃ v t, v 0 = y ∧ NRingPath μ J n v t

/-- No ring path of length `n` in `J` ends at `y`. -/
def NoPathTo (μ : Measure (RingSpace d β)) (J : Set ℝ) (y : Fin d → ℤ) (n : ℕ) : Prop :=
  ¬ ∃ v t, v n = y ∧ NRingPath μ J n v t

omit [Fact (0 < β)] in
theorem isRingPath_of_nRingPath {μ : Measure (RingSpace d β)} {J : Set ℝ} {n : ℕ}
    {v t} (h : NRingPath μ J n v t) :
    IsRingPath μ J n (fun i : Fin (n + 1) => v i) (fun i : Fin n => t i) := by
  refine ⟨fun i j hij => h.1 i j hij j.2, fun i => h.2.1 i i.2, fun i => ?_⟩
  obtain ⟨e, he, hr⟩ := h.2.2 i i.2
  exact ⟨e, by simpa using he, hr⟩

omit [Fact (0 < β)] in
theorem exists_nRingPath_of_isRingPath {μ : Measure (RingSpace d β)} {J : Set ℝ} {n : ℕ}
    {v : Fin (n + 1) → Fin d → ℤ} {t : Fin n → ℝ} (h : IsRingPath μ J n v t) :
    ∃ (v' : ℕ → Fin d → ℤ) (t' : ℕ → ℝ), v' 0 = v 0 ∧ v' n = v (Fin.last n) ∧
      NRingPath μ J n v' t' := by
  classical
  refine ⟨fun i => if hi : i < n + 1 then v ⟨i, hi⟩ else v 0,
    fun i => if hi : i < n then t ⟨i, hi⟩ else 0, by simp, by simp [Fin.last], ?_, ?_, ?_⟩
  · intro i j hij hj
    simp only [hj, dite_eq_left, hij.trans hj]
    exact h.1 (show (⟨i, hij.trans hj⟩ : Fin n) < ⟨j, hj⟩ from hij)
  · intro i hi
    simpa [hi] using h.2.1 ⟨i, hi⟩
  · intro i hi
    obtain ⟨e, he, hr⟩ := h.2.2 ⟨i, hi⟩
    refine ⟨e, ?_, by simpa [hi] using hr⟩
    simpa [hi, show i + 1 < n + 1 by omega, show i < n + 1 by omega] using he

omit [Fact (0 < β)] in
theorem noPathFrom_iff {μ : Measure (RingSpace d β)} {J : Set ℝ} {y : Fin d → ℤ} {n : ℕ} :
    NoPathFrom μ J y n ↔
      ¬ ∃ (v : Fin (n + 1) → Fin d → ℤ) (t : Fin n → ℝ), v 0 = y ∧ IsRingPath μ J n v t := by
  constructor
  · rintro h ⟨v, t, hv, hp⟩
    obtain ⟨v', t', h0, -, hp'⟩ := exists_nRingPath_of_isRingPath hp
    exact h ⟨v', t', h0.trans hv, hp'⟩
  · rintro h ⟨v, t, hv, hp⟩
    exact h ⟨_, _, by simpa using hv, isRingPath_of_nRingPath hp⟩

omit [Fact (0 < β)] in
theorem noPathTo_iff {μ : Measure (RingSpace d β)} {J : Set ℝ} {y : Fin d → ℤ} {n : ℕ} :
    NoPathTo μ J y n ↔
      ¬ ∃ (v : Fin (n + 1) → Fin d → ℤ) (t : Fin n → ℝ), v (Fin.last n) = y ∧
        IsRingPath μ J n v t := by
  constructor
  · rintro h ⟨v, t, hv, hp⟩
    obtain ⟨v', t', -, h0, hp'⟩ := exists_nRingPath_of_isRingPath hp
    exact h ⟨v', t', h0.trans hv, hp'⟩
  · rintro h ⟨v, t, hv, hp⟩
    exact h ⟨_, _, by simpa using hv, isRingPath_of_nRingPath hp⟩

section ops

variable {μ : Measure (RingSpace d β)} {J J' : Set ℝ} {n m : ℕ} {v : ℕ → Fin d → ℤ}
  {t : ℕ → ℝ}

omit [Fact (0 < β)] in
theorem NRingPath.truncate (h : NRingPath μ J n v t) (hm : m ≤ n) : NRingPath μ J m v t :=
  ⟨fun i j hij hj => h.1 i j hij (hj.trans_le hm), fun i hi => h.2.1 i (hi.trans_le hm),
    fun i hi => h.2.2 i (hi.trans_le hm)⟩

omit [Fact (0 < β)] in
theorem NRingPath.mono (h : NRingPath μ J n v t) (hJ : ∀ i, i < n → t i ∈ J → t i ∈ J') :
    NRingPath μ J' n v t :=
  ⟨h.1, fun i hi => hJ i hi (h.2.1 i hi), h.2.2⟩

omit [Fact (0 < β)] in
/-- The suffix of a ring path. -/
theorem NRingPath.suffix (h : NRingPath μ J n v t) (m : ℕ) :
    NRingPath μ J (n - m) (fun i => v (i + m)) (fun i => t (i + m)) := by
  refine ⟨fun i j hij hj => h.1 _ _ (by omega) (by omega), fun i hi => h.2.1 _ (by omega),
    fun i hi => ?_⟩
  obtain ⟨e, he, hr⟩ := h.2.2 (i + m) (by omega)
  exact ⟨e, by
    show _ = s(v (i + m), v (i + 1 + m))
    rw [he, Nat.add_right_comm i 1 m], hr⟩

omit [Fact (0 < β)] in
/-- Time translation. -/
theorem NRingPath.rotate (r : ℝ) (h : NRingPath (rotateMeasure r μ) J n v t) :
    NRingPath μ {u | u + r ∈ J} n v (fun i => t i - r) := by
  refine ⟨fun i j hij hj => by simpa using h.1 i j hij hj, fun i hi => ?_, fun i hi => ?_⟩
  · simpa using h.2.1 i hi
  · obtain ⟨e, he, hr⟩ := h.2.2 i hi
    exact ⟨e, he, (rings_rotateMeasure r μ e _).mp hr⟩

omit [Fact (0 < β)] in
/-- Lattice automorphisms transport ring paths. -/
theorem NRingPath.lattice (g : LatticeAut d) (h : NRingPath (latticeMeasure g μ) J n v t) :
    NRingPath μ J n (fun i => g.toEquiv.symm (v i)) t := by
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨e, he, hr⟩ := h.2.2 i hi
  refine ⟨(edgeEquiv g).symm e, ?_, ?_⟩
  · show Sym2.map g.toEquiv.symm e.1 = _
    rw [he]; rfl
  · have : Rings (latticeMeasure g μ) (edgeEquiv g ((edgeEquiv g).symm e)) (t i) := by
      simpa using hr
    exact (rings_latticeMeasure g μ _ _).mp this

omit [Fact (0 < β)] in
/-- Time reversal turns a path for the reflected configuration into a path for `μ`. -/
theorem NRingPath.reflect (h : NRingPath (reflectMeasure β μ) J n v t) :
    NRingPath μ {u | -u ∈ J} n (fun i => v (n - i)) (fun i => -t (n - 1 - i)) := by
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := h.1 (n - 1 - j) (n - 1 - i) (by omega) (by omega)
    simpa using this
  · simpa using h.2.1 (n - 1 - i) (by omega)
  · obtain ⟨e, he, hr⟩ := h.2.2 (n - 1 - i) (by omega)
    have hr' := (rings_reflectMeasure μ e _).mp hr
    refine ⟨e, ?_, by simpa using hr'⟩
    rw [he, Sym2.eq_swap]
    have h1 : n - 1 - i + 1 = n - i := by omega
    have h2 : n - (i + 1) = n - 1 - i := by omega
    show _ = s(v (n - i), v (n - (i + 1)))
    rw [h1, h2]

omit [Fact (0 < β)] in
/-- Time reversal turns a path for `μ` into a path for the reflected configuration. -/
theorem NRingPath.reflect' (h : NRingPath μ J n v t) :
    NRingPath (reflectMeasure β μ) {u | -u ∈ J} n (fun i => v (n - i))
      (fun i => -t (n - 1 - i)) := by
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := h.1 (n - 1 - j) (n - 1 - i) (by omega) (by omega)
    simpa using this
  · simpa using h.2.1 (n - 1 - i) (by omega)
  · obtain ⟨e, he, hr⟩ := h.2.2 (n - 1 - i) (by omega)
    refine ⟨e, ?_, (rings_reflectMeasure μ e _).mpr (by simpa using hr)⟩
    rw [he, Sym2.eq_swap]
    have h1 : n - 1 - i + 1 = n - i := by omega
    have h2 : n - (i + 1) = n - 1 - i := by omega
    show _ = s(v (n - i), v (n - (i + 1)))
    rw [h1, h2]

end ops

end ElboimSly.Interchange
