/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.RingPathN
import Mathlib

/-!
# Splitting ring paths in time

Symmetries preserve good configurations (the argument for rotations).

If, for every window `I_j` and every vertex `y`, ring paths in `I_j` starting at `y` have bounded
length, then the same is true for every interval `[p, p + β/2]`. The proof splits the interval
into two halves, each inside some window; the vertex reached after the first half lies in a finite
ball. The statement for paths ending at `y` follows by time reversal.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Ring paths starting at `y` in `J` have bounded length. -/
def StartFree (μ : Measure (RingSpace d β)) (J : Set ℝ) (y : Fin d → ℤ) : Prop :=
  ∃ n, NoPathFrom μ J y n

/-- Ring paths ending at `y` in `J` have bounded length. -/
def EndFree (μ : Measure (RingSpace d β)) (J : Set ℝ) (y : Fin d → ℤ) : Prop :=
  ∃ n, NoPathTo μ J y n

section basic

variable {μ : Measure (RingSpace d β)} {J J' : Set ℝ} {y : Fin d → ℤ} {n n' : ℕ}

omit [Fact (0 < β)] in
theorem NoPathFrom.of_le (h : NoPathFrom μ J y n) (hn : n ≤ n') : NoPathFrom μ J y n' :=
  fun ⟨v, t, hv, hp⟩ => h ⟨v, t, hv, hp.truncate hn⟩

end basic

/-- The `ℓ¹` distance on `ℤᵈ`. -/
def l1 (a b : Fin d → ℤ) : ℤ := ∑ i, |a i - b i|

theorem l1_triangle (a b c : Fin d → ℤ) : l1 a c ≤ l1 a b + l1 b c := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

theorem l1_comm (a b : Fin d → ℤ) : l1 a b = l1 b a := by
  unfold l1
  exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _

theorem l1_edge {e : Edge d} {u w : Fin d → ℤ} (h : e.1 = s(u, w)) : l1 u w = 1 := by
  obtain ⟨a, b, hab, hadj⟩ := e.2
  rw [h] at hab
  rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · rw [l1_comm]; exact hadj

omit [Fact (0 < β)] in
theorem NRingPath.l1_le {μ : Measure (RingSpace d β)} {J : Set ℝ} {n : ℕ}
    {v : ℕ → Fin d → ℤ} {t : ℕ → ℝ} (h : NRingPath μ J n v t) :
    ∀ k, k ≤ n → l1 (v k) (v 0) ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [l1]
  | succ k ih =>
    intro hk
    obtain ⟨e, he, -⟩ := h.2.2 k (by omega)
    have h1 := l1_edge he
    have h2 := ih (by omega)
    have h3 := l1_triangle (v (k + 1)) (v k) (v 0)
    have h4 := l1_comm (v (k + 1)) (v k)
    push_cast
    linarith

theorem finite_l1_ball (y : Fin d → ℤ) (N : ℕ) : {w : Fin d → ℤ | l1 w y ≤ N}.Finite := by
  have hW : {w : Fin d → ℤ | ∀ i, w i ∈ Set.Icc (y i - N) (y i + N)}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc (y i - N) (y i + N)) |>.subset (fun w hw i => hw i)
  refine hW.subset fun w hw i => ?_
  have h1 : |w i - y i| ≤ l1 w y :=
    Finset.single_le_sum (f := fun i => |w i - y i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have := abs_le.mp (h1.trans hw)
  constructor <;> linarith [this.1, this.2]

/-- A short interval lies in some window. -/
theorem exists_window_quarter (p : ℝ) :
    ∃ j : ℤ, Set.Icc p (p + β / 4) ⊆ ringWindow β j := by
  have hβ : 0 < β := Fact.out
  refine ⟨⌊4 * p / β⌋, fun u hu => ?_⟩
  have h1 : ((⌊4 * p / β⌋ : ℤ) : ℝ) ≤ 4 * p / β := Int.floor_le _
  have h2 : 4 * p / β < ((⌊4 * p / β⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hβ] at h1
  rw [div_lt_iff₀ hβ] at h2
  unfold ringWindow
  constructor <;> nlinarith [hu.1, hu.2]

/-- If paths from every vertex in every window have bounded length, the same holds in every
interval of length `β / 2`. -/
theorem startFree_Icc {μ : Measure (RingSpace d β)}
    (H : ∀ (j : ℤ) (y : Fin d → ℤ), StartFree μ (ringWindow β j) y) (p : ℝ) (y : Fin d → ℤ) :
    StartFree μ (Set.Icc p (p + β / 2)) y := by
  classical
  have hβ : 0 < β := Fact.out
  obtain ⟨j1, hj1⟩ := exists_window_quarter (β := β) p
  obtain ⟨j2, hj2⟩ := exists_window_quarter (β := β) (p + β / 4)
  obtain ⟨N1, h1⟩ := H j1 y
  choose N2 h2 using H j2
  obtain ⟨M, hM⟩ := ((finite_l1_ball y N1).image (fun w => N2 w)).bddAbove
  refine ⟨N1 + M + 1, ?_⟩
  rintro ⟨v, t, hv0, hp⟩
  set N := N1 + M + 1 with hN
  set q := p + β / 4 with hq
  have hex : ∃ i, N ≤ i ∨ q < t i := ⟨N, Or.inl le_rfl⟩
  set m := Nat.find hex with hm
  have hmN : m ≤ N := Nat.find_min' hex (Or.inl le_rfl)
  have hbelow : ∀ i, i < m → t i ≤ q := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this.2
  have habove : m < N → ∀ i, m ≤ i → i < N → q < t i := fun hmN' i hmi hiN => by
    have hspec := Nat.find_spec hex
    rcases hspec with h | h
    · omega
    · rcases eq_or_lt_of_le hmi with rfl | hlt
      · exact h
      · exact h.trans (hp.1 m i hlt hiN)
  have hprefix : NRingPath μ (ringWindow β j1) m v t := by
    refine (hp.truncate hmN).mono fun i hi hti => hj1 ⟨?_, ?_⟩
    · exact hti.1
    · exact hbelow i hi
  have hmN1 : m < N1 := by
    by_contra hge
    exact h1 ⟨v, t, hv0, hprefix.truncate (not_lt.mp hge)⟩
  have hmN' : m < N := by omega
  have hdist : l1 (v m) y ≤ N1 := by
    have := (hp.truncate hmN).l1_le m le_rfl
    rw [hv0] at this
    exact this.trans (by exact_mod_cast hmN1.le)
  have hsuf := hp.suffix m
  have hsuf' : NRingPath μ (ringWindow β j2) (N - m) (fun i => v (i + m)) (fun i => t (i + m)) := by
    refine hsuf.mono fun i hi hti => hj2 ⟨?_, ?_⟩
    · exact (habove hmN' (i + m) (by omega) (by omega)).le
    · have := hti.2
      rw [hq]; linarith
  have hle : N2 (v m) ≤ M := hM ⟨v m, hdist, rfl⟩
  exact h2 (v m) ⟨fun i => v (i + m), fun i => t (i + m), by simp, hsuf'.truncate (by omega)⟩

omit [Fact (0 < β)] in
/-- The window `I_j` reflected through `0` is `I_{-j-2}`. -/
theorem neg_ringWindow (j : ℤ) : {u : ℝ | -u ∈ ringWindow β j} = ringWindow β (-j - 2) := by
  ext u
  unfold ringWindow
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [Fact (0 < β)] in
/-- Reflection exchanges paths starting at `y` and paths ending at `y`. -/
theorem noPathFrom_reflect {μ : Measure (RingSpace d β)} {J : Set ℝ} {y : Fin d → ℤ} {n : ℕ}
    (h : NoPathTo μ {u | -u ∈ J} y n) : NoPathFrom (reflectMeasure β μ) J y n := by
  rintro ⟨v, t, hv, hp⟩
  exact h ⟨fun i => v (n - i), fun i => -t (n - 1 - i), by simpa using hv, hp.reflect⟩

omit [Fact (0 < β)] in
theorem noPathTo_reflect {μ : Measure (RingSpace d β)} {J : Set ℝ} {y : Fin d → ℤ} {n : ℕ}
    (h : NoPathFrom μ {u | -u ∈ J} y n) : NoPathTo (reflectMeasure β μ) J y n := by
  rintro ⟨v, t, hv, hp⟩
  exact h ⟨fun i => v (n - i), fun i => -t (n - 1 - i), by simpa using hv, hp.reflect⟩

/-- The analogue of `startFree_Icc` for paths ending at `y`. -/
theorem endFree_Icc {μ : Measure (RingSpace d β)}
    (H : ∀ (j : ℤ) (y : Fin d → ℤ), EndFree μ (ringWindow β j) y) (p : ℝ) (y : Fin d → ℤ) :
    EndFree μ (Set.Icc p (p + β / 2)) y := by
  have H' : ∀ (j : ℤ) (y : Fin d → ℤ), StartFree (reflectMeasure β μ) (ringWindow β j) y :=
    fun j y => by
      obtain ⟨n, hn⟩ := H (-j - 2) y
      exact ⟨n, noPathFrom_reflect (by rw [neg_ringWindow]; exact hn)⟩
  obtain ⟨n, hn⟩ := startFree_Icc H' (-p - β / 2) y
  refine ⟨n, ?_⟩
  rintro ⟨v, t, hv, hp⟩
  refine hn ⟨_, _, by simpa using hv, hp.reflect'.mono fun i _ hi => ?_⟩
  obtain ⟨h1, h2⟩ := hi
  constructor <;> linarith

end ElboimSly.Interchange
