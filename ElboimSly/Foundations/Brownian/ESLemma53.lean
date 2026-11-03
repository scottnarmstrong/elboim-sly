/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.EscapeLineProb
public import ElboimSly.Foundations.Brownian.ESClaim57
import Mathlib

/-!
# ES22 Lemma 5.3: the event `𝓘`

ES22 Lemma 5.3: the event ℐ.

The dimension is `m + 1` with `m ≥ 4` (so `d ≥ 5`). Here `N` is the parameter `n` of ES22, `L = 2^j`
with `N^20 ≤ L`, `a = ⌊N^17/3⌋`, and `i0`, `i1` are the first and second coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {m : ℕ}

/-- The point `p_ℓ = u + 2^{j-2}(3, 2, …, 2) + ℓ a e₂`. -/
noncomputable def es53P (i0 i1 : Fin (m + 1)) (u : Fin (m + 1) → ℝ) (L a : ℝ) (ℓ : ℕ) :
    Fin (m + 1) → ℝ :=
  c57P i0 i1 u L ((ℓ : ℝ) * a)

/-- A continuous function of the path is `≥ c` at every time iff its (dense) infimum is. -/
lemma le_pathInf_univ_iff {d : ℕ} {G : (Fin d → ℝ) → ℝ} (hG : Continuous G) {w : PathSpace d}
    (hw : Continuous w) (c : ℝ) :
    (c : EReal) ≤ pathInf Set.univ G w ↔ ∀ s : ℝ≥0, c ≤ G (w s) := by
  have hf : Continuous fun t : ℝ≥0 => G (w t) := hG.comp hw
  have e : pathInf Set.univ G w = ⨅ t ∈ (Set.univ : Set ℝ≥0), ((G (w t) : ℝ) : EReal) :=
    (iInf_eq_denseSub Set.ordConnected_univ hf).symm
  rw [e]
  simp only [Set.mem_univ, iInf_pos, le_iInf_iff, EReal.coe_le_coe_iff]

/-- ES22 Lemma 5.3: the event ℐ. The path set `𝔍` of the event `𝓘`. -/
def es53Set (i0 i1 : Fin (m + 1)) (u : Fin (m + 1) → ℝ) (σ L a : ℝ) (N i : ℕ) :
    Set (PathSpace (m + 1)) :=
  {w | ((L / 5 : ℝ) : EReal) ≤ pathInf Set.univ
      (fun z => Metric.infDist (es53P i0 i1 u L a i + σ • z) (c57Bminus i0 u L)) w ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
      (((N : ℝ) ^ 17 / 5 : ℝ) : EReal) ≤ pathInf Set.univ
        (fun z => ‖es53P i0 i1 u L a i + σ • z - es53P i0 i1 u L a ℓ‖) w}

lemma measurableSet_es53Set (i0 i1 : Fin (m + 1)) (u : Fin (m + 1) → ℝ) (σ L a : ℝ) (N i : ℕ) :
    MeasurableSet (es53Set i0 i1 u σ L a N i) := by
  have hc1 : Continuous fun z : Fin (m + 1) → ℝ =>
      Metric.infDist (es53P i0 i1 u L a i + σ • z) (c57Bminus i0 u L) :=
    (Metric.continuous_infDist_pt _).comp (by fun_prop)
  have h1 : MeasurableSet {w : PathSpace (m + 1) | ((L / 5 : ℝ) : EReal) ≤ pathInf Set.univ
      (fun z => Metric.infDist (es53P i0 i1 u L a i + σ • z) (c57Bminus i0 u L)) w} :=
    measurableSet_le measurable_const (measurable_pathInf _ hc1)
  have h2 : MeasurableSet {w : PathSpace (m + 1) | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
      (((N : ℝ) ^ 17 / 5 : ℝ) : EReal) ≤ pathInf Set.univ
        (fun z => ‖es53P i0 i1 u L a i + σ • z - es53P i0 i1 u L a ℓ‖) w} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun ℓ => ?_
    by_cases hℓ : 1 ≤ ℓ ∧ ℓ ≤ N ^ 3 ∧ ℓ ≠ i
    · have : {w : PathSpace (m + 1) | 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
          (((N : ℝ) ^ 17 / 5 : ℝ) : EReal) ≤ pathInf Set.univ
            (fun z => ‖es53P i0 i1 u L a i + σ • z - es53P i0 i1 u L a ℓ‖) w} =
          {w | (((N : ℝ) ^ 17 / 5 : ℝ) : EReal) ≤ pathInf Set.univ
            (fun z => ‖es53P i0 i1 u L a i + σ • z - es53P i0 i1 u L a ℓ‖) w} := by
        ext w; simp [hℓ.1, hℓ.2.1, hℓ.2.2]
      rw [this]
      exact measurableSet_le measurable_const (measurable_pathInf _ (by fun_prop))
    · have : {w : PathSpace (m + 1) | 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
          (((N : ℝ) ^ 17 / 5 : ℝ) : EReal) ≤ pathInf Set.univ
            (fun z => ‖es53P i0 i1 u L a i + σ • z - es53P i0 i1 u L a ℓ‖) w} = Set.univ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro h1 h2 h3
        exact absurd ⟨h1, h2, h3⟩ hℓ
      rw [this]; exact MeasurableSet.univ
  exact h1.inter h2

lemma es53P_sub {i0 i1 : Fin (m + 1)} (hne : i0 ≠ i1) (u : Fin (m + 1) → ℝ) (L a : ℝ) (i ℓ : ℕ)
    (k : Fin (m + 1)) :
    es53P i0 i1 u L a i k - es53P i0 i1 u L a ℓ k = if k = i1 then ((i : ℝ) - ℓ) * a else 0 := by
  unfold es53P c57P
  by_cases h0 : k = i0
  · subst h0; simp [hne]
  · by_cases h1 : k = i1
    · subst h1; simp [h0]; ring
    · simp [h0, h1]

lemma Bminus_nonempty (i0 : Fin (m + 1)) (u : Fin (m + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    (c57Bminus i0 u L).Nonempty := by
  refine ⟨u, fun k => ?_⟩
  split_ifs
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨le_rfl, by linarith⟩

/-- The set `Q` of the proof of ES22 Lemma 5.3: the event ℐ lies in the region of escaping a box and a line of points. -/
lemma es53_Q_subset {i0 i1 : Fin (m + 1)} (_hne : i0 ≠ i1) (u : Fin (m + 1) → ℝ) {L a : ℝ}
    (hL : 0 < L) {i : ℕ} (hia : (i : ℝ) * a ≤ L / 3) (ha0 : 0 ≤ a) :
    {y | Metric.infDist (es53P i0 i1 u L a i + y) (c57Bminus i0 u L) < L / 5} ⊆
      {y | y i0 ≤ -(L / 20)} ∩ Metric.closedBall 0 (2 * L) := by
  intro y hy
  obtain ⟨v, hv, hdist⟩ := (Metric.infDist_lt_iff (Bminus_nonempty i0 u hL)).1 hy
  rw [dist_eq_norm] at hdist
  have hi : (0 : ℝ) ≤ (i : ℝ) * a := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := (abs_lt.1 ((coord_le_norm _ _ i0).trans_lt hdist))
    have h2 := (hv i0)
    simp only [ite_true] at h2
    simp only [es53P, c57P, ite_true, Pi.add_apply] at h1
    simp only [Set.mem_ofPred_eq]
    linarith [h2.1, h2.2, h1.1, h1.2]
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hvp : ‖v - es53P i0 i1 u L a i‖ ≤ 5 * L / 6 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      rw [Real.norm_eq_abs, abs_le]
      have h2 := hv k
      have hcoord : es53P i0 i1 u L a i k = u k +
          (if k = i0 then 3 * L / 4 else if k = i1 then L / 2 + (i : ℝ) * a else L / 2) := rfl
      rw [Pi.sub_apply, hcoord]
      split_ifs at h2 ⊢ <;> constructor <;> linarith [h2.1, h2.2]
    calc ‖y‖ = ‖(es53P i0 i1 u L a i + y - v) + (v - es53P i0 i1 u L a i)‖ := by congr 1; abel
      _ ≤ L / 5 + 5 * L / 6 := (norm_add_le _ _).trans (add_le_add hdist.le hvp)
      _ ≤ 2 * L := by linarith

/-- ES22 Lemma 5.3: the event ℐ, on the event `E = {B ∈ 𝔏}`. -/
theorem es53_on_event {i0 i1 : Fin (m + 1)} (hne : i0 ≠ i1) (hm : 3 ≤ m) (u : Fin (m + 1) → ℝ)
    {σ L : ℝ} (hσ0 : 0 < σ) {N i : ℕ} (hN : 2 ≤ N) (_hi1 : 1 ≤ i) (hi2 : i ≤ N ^ 3)
    (hL : (N : ℝ) ^ 20 ≤ L) (hCl : Cline (m + 1) ≤ 3 * (N : ℝ) ^ 3)
    {w : PathSpace (m + 1)} (hw : Continuous w)
    (hmem : w ∈ lineSet i0 i1 σ ((N ^ 17 / 3 : ℕ) : ℝ) L) (s : ℝ≥0) :
    L / 5 ≤ Metric.infDist (es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • w s)
        (c57Bminus i0 u L) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
        (N : ℝ) ^ 17 / 5 ≤ ‖es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • w s -
          es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) ℓ‖ := by
  set a : ℝ := ((N ^ 17 / 3 : ℕ) : ℝ) with ha
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h17 : 3 ≤ N ^ 17 := by
    calc 3 ≤ 2 ^ 17 := by norm_num
      _ ≤ N ^ 17 := Nat.pow_le_pow_left hN 17
  have ha1 : 1 ≤ N ^ 17 / 3 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have ha0 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast ha1
  have haup : a ≤ (N : ℝ) ^ 17 / 3 := by
    have := Nat.cast_div_le (α := ℝ) (m := N ^ 17) (n := 3)
    simpa using this
  have halo : ((N : ℝ) ^ 17 - 2) / 3 ≤ a := by
    have h1 : N ^ 17 ≤ 3 * (N ^ 17 / 3) + 2 := by omega
    have h2 : (N : ℝ) ^ 17 ≤ 3 * a + 2 := by rw [ha]; exact_mod_cast h1
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hiN : (i : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast hi2
  have hia : (i : ℝ) * a ≤ L / 3 := by
    calc (i : ℝ) * a ≤ (N : ℝ) ^ 3 * ((N : ℝ) ^ 17 / 3) :=
          mul_le_mul hiN haup (by linarith) (by positivity)
      _ = (N : ℝ) ^ 20 / 3 := by ring
      _ ≤ L / 3 := by linarith
  have hA : Cline (m + 1) * a ≤ L := by
    calc Cline (m + 1) * a ≤ (3 * (N : ℝ) ^ 3) * ((N : ℝ) ^ 17 / 3) :=
          mul_le_mul hCl haup (by linarith) (by positivity)
      _ = (N : ℝ) ^ 20 := by ring
      _ ≤ L := hL
  have hQ := es53_Q_subset hne u hLpos hia (by linarith : (0 : ℝ) ≤ a)
  have hav := lineSet_avoids hm hne hσ0 (by linarith : 0 < a) hA hw hmem hQ s
  refine ⟨?_, fun ℓ hℓ1 hℓ2 hℓi => ?_⟩
  · by_contra hlt
    exact hav.1 (show σ • w s ∈ {y | Metric.infDist (es53P i0 i1 u L a i + y)
      (c57Bminus i0 u L) < L / 5} from not_le.1 hlt)
  · have hN17 : (20 : ℝ) ≤ (N : ℝ) ^ 17 := by
      calc (20 : ℝ) ≤ 2 ^ 17 := by norm_num
        _ ≤ (N : ℝ) ^ 17 := pow_le_pow_left₀ (by norm_num) hN2 17
    have hna : (N : ℝ) ^ 17 / 5 ≤ 2 * a / 3 := by linarith
    have hDk : ∀ k, (es53P i0 i1 u L a i + σ • w s - es53P i0 i1 u L a ℓ) k =
        (if k = i1 then ((i : ℝ) - ℓ) * a else 0) + σ * w s k := by
      intro k
      have := es53P_sub hne u L a i ℓ k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hcoord : ∀ k, |(es53P i0 i1 u L a i + σ • w s - es53P i0 i1 u L a ℓ) k| ≤
        ‖es53P i0 i1 u L a i + σ • w s - es53P i0 i1 u L a ℓ‖ := fun k => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm
        (es53P i0 i1 u L a i + σ • w s - es53P i0 i1 u L a ℓ) k
    rcases hav.2 with ⟨k, hk1, hk2⟩ | hk
    · refine hna.trans (hk2.trans ((le_of_eq ?_).trans (hcoord k)))
      rw [hDk k]; simp [hk1]
    · have hil : (1 : ℝ) ≤ |(i : ℝ) - ℓ| := by
        have : (i : ℤ) ≠ ℓ := fun h => hℓi (by exact_mod_cast h.symm)
        have h2 : (1 : ℤ) ≤ |(i : ℤ) - ℓ| := Int.one_le_abs (sub_ne_zero.2 this)
        exact_mod_cast h2
      have h1 := hcoord i1
      rw [hDk i1] at h1; simp only [ite_true] at h1
      have h2 : a ≤ |((i : ℝ) - ℓ) * a| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ a)]; nlinarith
      have h3 := abs_sub_abs_le_abs_sub (((i : ℝ) - ℓ) * a) (-(σ * w s i1))
      rw [abs_neg, sub_neg_eq_add] at h3
      linarith

/-- ES22 Lemma 5.3: the event ℐ. `n_{53}(d) = max {2, ⌈(C_line/3)^{1/3}⌉}`. -/
noncomputable def n53 (d : ℕ) : ℕ := max 2 ⌈(Cline d / 3) ^ ((1 : ℝ) / 3)⌉₊

lemma Cline_le_of_n53 {d N : ℕ} (hN : n53 d ≤ N) : Cline d ≤ 3 * (N : ℝ) ^ 3 := by
  have h1 : ⌈(Cline d / 3) ^ ((1 : ℝ) / 3)⌉₊ ≤ N := (le_max_right _ _).trans hN
  have h2 : (Cline d / 3) ^ ((1 : ℝ) / 3) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hC : 0 ≤ Cline d / 3 := by have := (Cline_ge d).1; positivity
  have h3 : ((Cline d / 3) ^ ((1 : ℝ) / 3)) ^ 3 ≤ (N : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h2 3
  rw [← Real.rpow_natCast, ← Real.rpow_mul hC] at h3
  norm_num at h3
  linarith

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → (Fin (m + 1) → ℝ)}

/-- ES22 Lemma 5.3: the event ℐ (ES22 Lemma 5.3). -/
theorem es53_main [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion (m + 1) B P)
    (hm : 3 ≤ m) {i0 i1 : Fin (m + 1)} (hne : i0 ≠ i1) (u : Fin (m + 1) → ℝ) {σ L : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {N i : ℕ} (hN : n53 (m + 1) ≤ N) (hi1 : 1 ≤ i) (hi2 : i ≤ N ^ 3)
    (hL : (N : ℝ) ^ 20 ≤ L) :
    ENNReal.ofReal (cline (m + 1)) ≤
        P {ω | pathMap B ω ∈ lineSet i0 i1 σ ((N ^ 17 / 3 : ℕ) : ℝ) L} ∧
      {ω | pathMap B ω ∈ lineSet i0 i1 σ ((N ^ 17 / 3 : ℕ) : ℝ) L} ⊆
        {ω | pathMap B ω ∈ es53Set i0 i1 u σ L ((N ^ 17 / 3 : ℕ) : ℝ) N i} ∧
      {ω | pathMap B ω ∈ es53Set i0 i1 u σ L ((N ^ 17 / 3 : ℕ) : ℝ) N i} =
        {ω | ∀ s : ℝ≥0, L / 5 ≤ Metric.infDist
            (es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • B s ω) (c57Bminus i0 u L) ∧
          ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
            (N : ℝ) ^ 17 / 5 ≤ ‖es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • B s ω -
              es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) ℓ‖} ∧
      MeasurableSet {ω | pathMap B ω ∈ es53Set i0 i1 u σ L ((N ^ 17 / 3 : ℕ) : ℝ) N i} := by
  have hσ0 : 0 < σ := by linarith
  have hCl := Cline_le_of_n53 hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have h17 : 3 ≤ N ^ 17 := by
    calc 3 ≤ 2 ^ 17 := by norm_num
      _ ≤ N ^ 17 := Nat.pow_le_pow_left hN2 17
  have ha1 : 1 ≤ N ^ 17 / 3 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have ha0 : (1 : ℝ) ≤ ((N ^ 17 / 3 : ℕ) : ℝ) := by exact_mod_cast ha1
  have haup : ((N ^ 17 / 3 : ℕ) : ℝ) ≤ (N : ℝ) ^ 17 / 3 := by
    have := Nat.cast_div_le (α := ℝ) (m := N ^ 17) (n := 3)
    simpa using this
  have hA : Cline (m + 1) * ((N ^ 17 / 3 : ℕ) : ℝ) ≤ L := by
    calc Cline (m + 1) * ((N ^ 17 / 3 : ℕ) : ℝ) ≤ (3 * (N : ℝ) ^ 3) * ((N : ℝ) ^ 17 / 3) :=
          mul_le_mul hCl haup (by linarith) (by positivity)
      _ = (N : ℝ) ^ 20 := by ring
      _ ≤ L := hL
  have hcont : ∀ ω, Continuous (pathMap B ω) := fun ω => continuous_path hB ω
  have hiff : ∀ w : PathSpace (m + 1), Continuous w →
      (w ∈ es53Set i0 i1 u σ L ((N ^ 17 / 3 : ℕ) : ℝ) N i ↔
        ∀ s : ℝ≥0, L / 5 ≤ Metric.infDist
            (es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • w s) (c57Bminus i0 u L) ∧
          ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N ^ 3 → ℓ ≠ i →
            (N : ℝ) ^ 17 / 5 ≤ ‖es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • w s -
              es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) ℓ‖) := by
    intro w hw
    have hc1 : Continuous fun z : Fin (m + 1) → ℝ =>
        Metric.infDist (es53P i0 i1 u L ((N ^ 17 / 3 : ℕ) : ℝ) i + σ • z) (c57Bminus i0 u L) :=
      (Metric.continuous_infDist_pt _).comp (by fun_prop)
    unfold es53Set
    simp only [Set.mem_ofPred_eq]
    rw [le_pathInf_univ_iff hc1 hw]
    constructor
    · rintro ⟨h1, h2⟩ s
      refine ⟨h1 s, fun ℓ hℓ1 hℓ2 hℓi => ?_⟩
      exact (le_pathInf_univ_iff (by fun_prop) hw _).1 (h2 ℓ hℓ1 hℓ2 hℓi) s
    · intro H
      refine ⟨fun s => (H s).1, fun ℓ hℓ1 hℓ2 hℓi => ?_⟩
      exact (le_pathInf_univ_iff (by fun_prop) hw _).2 fun s => (H s).2 ℓ hℓ1 hℓ2 hℓi
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lineSet_prob hB hm hne hσ1 hσ2 (by linarith) hA
  · intro ω hω
    have := es53_on_event hne hm u hσ0 hN2 hi1 hi2 hL hCl (hcont ω) hω
    exact (hiff _ (hcont ω)).2 fun s => this s
  · ext ω
    exact hiff _ (hcont ω)
  · exact hB.measurable_pathMap (measurableSet_es53Set _ _ _ _ _ _ _ _)

end B

end ElboimSly.Brownian
