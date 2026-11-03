/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Stopping
public import Mathlib

/-!
# Auxiliary facts for vertices visited by an explored walk

* `sqrt_div_log_ge`: `R ≤ 2√s / ln s` for `s ≥ 4 R² ln² R`, `R ≥ 10`.
* `not_cond_of_lt`: before `τ_i` none of the conditions (1)–(7) holds.
* `box_card_le`: the number of lattice points in a sup-norm ball.
-/

@[expose] public section

namespace ElboimSly.Paper

lemma log_le_half_self {R : ℝ} (hR : 10 ≤ R) : 2 * Real.log R ≤ R := by
  have h := Real.log_le_sub_one_of_pos (show 0 < R / 4 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have h4 : Real.log 4 ≤ 3 / 2 := by
    have := Real.log_two_lt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  linarith

/-- `x ↦ x / ln x` is nondecreasing on `[e, ∞)`; here `e ≤ 3 ≤ x₀`. -/
lemma div_log_mono {x₀ x : ℝ} (h0 : 3 ≤ x₀) (hx : x₀ ≤ x) :
    x₀ / Real.log x₀ ≤ x / Real.log x := by
  have hx0 : 0 < x₀ := by linarith
  have hxp : 0 < x := by linarith
  have hl0 : 1 ≤ Real.log x₀ := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hlx : Real.log x₀ ≤ Real.log x := Real.log_le_log hx0 hx
  have hlx0 : 0 < Real.log x := by linarith
  have hl00 : 0 < Real.log x₀ := by linarith
  have hb := Real.log_le_sub_one_of_pos (show 0 < x / x₀ by positivity)
  rw [Real.log_div hxp.ne' hx0.ne'] at hb
  rw [div_le_div_iff₀ hl00 hlx0]
  have h1 : x₀ * Real.log x ≤ x₀ * Real.log x₀ + (x - x₀) := by
    have : x₀ * (Real.log x - Real.log x₀) ≤ x₀ * (x / x₀ - 1) :=
      mul_le_mul_of_nonneg_left hb hx0.le
    have e : x₀ * (x / x₀ - 1) = x - x₀ := by field_simp
    nlinarith
  nlinarith

lemma sqrt_div_log_ge {R s : ℝ} (hR : 10 ≤ R) (hs : 4 * R ^ 2 * Real.log R ^ 2 ≤ s) :
    R ≤ 2 * Real.sqrt s / Real.log s := by
  have hlR : 2 ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hx0 : 2 * R * Real.log R ≤ Real.sqrt s := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hx3 : 3 ≤ 2 * R * Real.log R := by nlinarith
  have hxp : 0 < Real.sqrt s := by linarith
  have hsp : 0 < s := by nlinarith
  have hls : Real.log s = 2 * Real.log (Real.sqrt s) := by
    rw [Real.log_sqrt hsp.le]; ring
  have hmono := div_log_mono hx3 hx0
  have hlx0 : 0 < Real.log (2 * R * Real.log R) := Real.log_pos (by linarith)
  have hlogx0 : Real.log (2 * R * Real.log R) ≤ 2 * Real.log R := by
    have e : Real.log (2 * R * Real.log R) = Real.log R + Real.log (2 * Real.log R) := by
      rw [show 2 * R * Real.log R = R * (2 * Real.log R) by ring,
        Real.log_mul (by linarith) (by linarith)]
    have : Real.log (2 * Real.log R) ≤ Real.log R :=
      Real.log_le_log (by linarith) (log_le_half_self hR)
    linarith
  have h1 : R ≤ 2 * R * Real.log R / Real.log (2 * R * Real.log R) := by
    rw [le_div_iff₀ hlx0]
    nlinarith
  have hxl : 0 < Real.log (Real.sqrt s) := Real.log_pos (by linarith)
  rw [hls, show 2 * Real.sqrt s / (2 * Real.log (Real.sqrt s)) =
    Real.sqrt s / Real.log (Real.sqrt s) by field_simp]
  exact h1.trans hmono

lemma not_cond_of_lt {k : ℕ} {n j : ℕ} {β : ℝ} {I : ℕ} {P : ℕ → Fin (k + 2) → ℤ}
    {W : ℕ → ℝ → Fin (k + 2) → ℤ} {Bm : Set (Fin (k + 2) → ℤ)} {i : ℕ} {t : ℝ} (ht0 : 0 < t)
    (ht : t < escTauSeq n j β I P W Bm i) :
    ¬ EscStopCond n j β I P W Bm
      (fun ℓ => if _h : ℓ < i then escTauSeq n j β I P W Bm ℓ else 0) i t := by
  intro hc
  have : escTauSeq n j β I P W Bm i ≤ t := by
    rw [escTauSeq]
    exact csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨ht0, hc⟩
  linarith

/-- The integer box of radius `m` around `y`. -/
def ballFin {d : ℕ} (y : Fin d → ℤ) (m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun c => Finset.Icc (y c - m) (y c + m)

lemma card_ballFin {d : ℕ} (y : Fin d → ℤ) (m : ℕ) : (ballFin y m).card = (2 * m + 1) ^ d := by
  classical
  unfold ballFin
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have : ∀ c : Fin d, (y c + m + 1 - (y c - m)).toNat = 2 * m + 1 := by
    intro c; omega
  simp [this]

lemma mem_ballFin {d : ℕ} {x y : Fin d → ℤ} {L : ℝ} (_hL : 0 ≤ L) (hx : ‖x - y‖ ≤ L) :
    x ∈ ballFin y ⌊L⌋₊ := by
  classical
  unfold ballFin
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro c
  have h1 : |((x c - y c : ℤ) : ℝ)| ≤ L := by
    have := norm_le_pi_norm (x - y) c
    have h5 : ‖(x - y) c‖ ≤ L := this.trans hx
    rwa [Pi.sub_apply, Int.norm_eq_abs] at h5
  have h2 : |x c - y c| ≤ ⌊L⌋₊ := by
    have h3 : ((|x c - y c| : ℤ) : ℝ) ≤ L := by simpa [Int.cast_abs] using h1
    have h4 : (|x c - y c|).toNat ≤ ⌊L⌋₊ := by
      apply Nat.le_floor
      have : ((|x c - y c|).toNat : ℝ) = ((|x c - y c| : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _)]
      rw [this]; exact h3
    have := Int.self_le_toNat (|x c - y c|)
    omega
  rw [abs_le] at h2
  constructor <;> linarith [h2.1, h2.2]

end ElboimSly.Paper
