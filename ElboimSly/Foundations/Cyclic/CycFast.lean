/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFastWin
public import Mathlib

/-!
# ES22 Claim 2.3

ES22 Claim 2.3. For `d ≥ 1`, `β ≥ 1`, `L ≥ 1`, `t ≥ 1` and the regenerated walk of a
Poisson environment on `ℕ × S_β`,
`P(t_fast(L) ≤ t) ≤ 8 e² t² e^{-L/(40d)}` (`cyc_fast_explicit`); hence the claim with
`C = 8 e²` and `c = 1/(40 d)` (`cyc_fast`).

Proof (as in the written proof, with the covering repaired as in F01): Step 0 (`tfast_pair`), Step 3
(`tfast_mem_window`: a pair at distance `≤ 1` lies in a unit window of one of the first
`⌊t/β⌋ + 1` pieces, in `⌊t/β⌋ + 1` windows of length `β`, each covered by `≤ min(⌊β⌋, ⌊t⌋) + 1`
windows of length `2`), Step 2 (`window_prob`), and a union bound. Unlike the printed argument, the
case `t < β` is not treated separately: the number of unit windows is `≤ ⌊t⌋ + 1 ≤ 2t` there.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange ElboimSly.SRW

/-- The counting bound `n² I ≤ 8 t²`. -/
theorem count_bound {b t : ℝ≥0} (hb1 : 1 ≤ b) (ht1 : 1 ≤ t) :
    ((⌊t / b⌋₊ + 1 : ℕ) * (⌊t / b⌋₊ + 1 : ℕ) * (min ⌊b⌋₊ ⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ 8 * (t : ℝ) ^ 2 := by
  have hB : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hT : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hb0 : (0 : ℝ≥0) < b := lt_of_lt_of_le one_pos hb1
  have hfl : (⌊t / b⌋₊ : ℝ) ≤ (t : ℝ) / b := by
    have := Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ t / b)
    exact_mod_cast this
  have hI : ((min ⌊b⌋₊ ⌊t⌋₊ : ℕ) : ℝ) ≤ min (b : ℝ) t := by
    rw [Nat.cast_min]
    exact min_le_min (by exact_mod_cast Nat.floor_le zero_le) (by exact_mod_cast Nat.floor_le zero_le)
  simp only [Nat.cast_add, Nat.cast_one]
  rcases lt_or_ge t b with hlt | hge
  · have h0 : ⌊t / b⌋₊ = 0 := Nat.floor_eq_zero.2 ((div_lt_one hb0).2 hlt)
    rw [h0]
    have : (min (b : ℝ) t) ≤ t := min_le_right _ _
    have h2 : ((min ⌊b⌋₊ ⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * t := by linarith
    simp only [Nat.cast_zero, zero_add]
    nlinarith
  · have hTB : (1 : ℝ) ≤ (t : ℝ) / b := by
      rw [le_div_iff₀ (by exact_mod_cast hb0)]; simpa using (by exact_mod_cast hge : (b : ℝ) ≤ t)
    have hn : (⌊t / b⌋₊ : ℝ) + 1 ≤ 2 * ((t : ℝ) / b) := by linarith
    have hIb : ((min ⌊b⌋₊ ⌊t⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * b := by
      have := min_le_left (b : ℝ) t
      linarith
    have hBpos : (0 : ℝ) < b := by linarith
    have hn0 : (0 : ℝ) ≤ (⌊t / b⌋₊ : ℝ) + 1 := by positivity
    have hI0 : (0 : ℝ) ≤ ((min ⌊b⌋₊ ⌊t⌋₊ : ℕ) : ℝ) + 1 := by positivity
    calc ((⌊t / b⌋₊ : ℝ) + 1) * ((⌊t / b⌋₊ : ℝ) + 1) * (((min ⌊b⌋₊ ⌊t⌋₊ : ℕ) : ℝ) + 1)
        ≤ (2 * ((t : ℝ) / b)) * (2 * ((t : ℝ) / b)) * (2 * b) := by
          gcongr
      _ = 8 * (t : ℝ) ^ 2 / b := by field_simp; ring
      _ ≤ 8 * (t : ℝ) ^ 2 := by
          rw [div_le_iff₀ hBpos]; nlinarith [sq_nonneg (t : ℝ)]

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

/-- **ES22 Claim 2.3** (ES22 Claim 2.3), explicit form: for `d ≥ 1`, `β ≥ 1`, `L, t ≥ 1`,
`P(t_fast(L) ≤ t) ≤ 8 e² t² e^{-L/(40 d)}`. -/
theorem cyc_fast_explicit (hd : 1 ≤ d) (hβ : 1 ≤ β)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {L t : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t) :
    Pe.real {ω | ElboimSly.cycTfast (fun k => cycSlice k (N ω)) L ≤ ENNReal.ofReal t} ≤
      8 * Real.exp 2 * t ^ 2 * Real.exp (-(L / (40 * d))) := by
  have := hN.isProbabilityMeasure
  have hβpos : 0 < β := Fact.out
  set b : ℝ≥0 := β.toNNReal with hb
  have hb1 : 1 ≤ b := by rw [hb, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hβ
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht0 : 0 ≤ t := by linarith
  have ht'1 : 1 ≤ t' := by rw [ht', ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal ht
  have ht'c : (t' : ℝ) = t := Real.coe_toNNReal t ht0
  set n : ℕ := ⌊t' / b⌋₊ + 1 with hn
  set I : ℕ := min ⌊b⌋₊ ⌊t'⌋₊ + 1 with hI
  set S : Finset (ℕ × ℕ × ℕ) := Finset.range n ×ˢ Finset.range n ×ˢ Finset.range I with hS
  set A : ℕ × ℕ × ℕ → Set Ω := fun p =>
    {ω | shiftTraj ((p.2.1 : ℝ≥0) * b + p.2.2) (cycSlice p.1 (N ω)) ∈
      farSet (d := d) (L / 4) 2} with hA
  have hsub : {ω | ElboimSly.cycTfast (fun k => cycSlice k (N ω)) L ≤ ENNReal.ofReal t} ≤ᵐ[Pe]
      ⋃ p ∈ S, A p := by
    filter_upwards [ae_cycGood hN] with ω hω h
    obtain ⟨j, m, i, hj, hm, hi, hmem⟩ := tfast_mem_window hω hβ hL ht h
    refine mem_iUnion₂.2 ⟨(j, m, i), ?_, hmem⟩
    simp only [hS, Finset.mem_product, Finset.mem_range]
    exact ⟨hj, hm, hi⟩
  have hp : ∀ p ∈ S, Pe.real (A p) ≤ Real.exp 2 * Real.exp (-(L / (40 * d))) := fun p _ =>
    window_prob hN hd hL p.1 _
  have hcard : (S.card : ℝ) ≤ 8 * t ^ 2 := by
    have := count_bound hb1 ht'1
    rw [ht'c] at this
    simpa [hS, hn, hI, Finset.card_product, mul_assoc] using this
  calc Pe.real _ ≤ Pe.real (⋃ p ∈ S, A p) := measureReal_mono_ae' hsub
    _ ≤ ∑ p ∈ S, Pe.real (A p) := measureReal_biUnion_finset_le S A
    _ ≤ ∑ _p ∈ S, Real.exp 2 * Real.exp (-(L / (40 * d))) := Finset.sum_le_sum hp
    _ = S.card * (Real.exp 2 * Real.exp (-(L / (40 * d)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 * t ^ 2 * (Real.exp 2 * Real.exp (-(L / (40 * d)))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 8 * Real.exp 2 * t ^ 2 * Real.exp (-(L / (40 * d))) := by ring

universe u

/-- **ES22 Claim 2.3** (ES22 Claim 2.3): there are `C, c > 0` depending only on `d` such that for
all `β ≥ 1`, `L ≥ 1` and `t ≥ 1`, `P(t_fast(L) ≤ t) ≤ C t² e^{-c L}`. -/
theorem cyc_fast (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) [Fact (0 < β)], 1 ≤ β →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (Pe : Measure Ω)
        (N : Ω → Measure (ℕ × RingSpace d β)),
        IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe →
        ∀ {L t : ℝ}, 1 ≤ L → 1 ≤ t →
          Pe.real {ω | ElboimSly.cycTfast (fun k => cycSlice k (N ω)) L ≤ ENNReal.ofReal t} ≤
            C * t ^ 2 * Real.exp (-(c * L)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨8 * Real.exp 2, 1 / (40 * d), by positivity, by positivity, ?_⟩
  intro β _ hβ Ω _ Pe N hN L t hL ht
  have := cyc_fast_explicit hd hβ hN hL ht
  have e : L / (40 * d) = 1 / (40 * d) * L := by ring
  rwa [e] at this

end ElboimSly.Cyclic

end
