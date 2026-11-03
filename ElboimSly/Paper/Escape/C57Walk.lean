/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Geom
public import ElboimSly.Paper.Escape.Es53BM
public import ElboimSly.Foundations.Brownian.ESClaim57
public import Mathlib

/-!
# The event `E₅₇` from the Brownian coupling

ES22 Claim 5.7 ("Events", `E₅₇`), ES22 Claim 5.7, eq. (85): staying in a box and visiting B^- and the induction hypothesis at arbitrary times (d), deviation
D11.

If the law of the walk up to time `T = 4^j` admits a `(σ, ε)`-coupling with failure probability `η`
(hypothesis (H4)), `ε < 2^j/64`, then, with probability `≥ c₅₇ - η`, the walk started at `p_i`
stays in the box `escBigBox` of eq. (85) up to time `4^{j-1}` and is outside `𝒬` at time `4^{j-1}`
(at the test times `qSet`, which is equivalent for right-continuous paths).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Bridge ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem escBigBox_of_cast {j : ℕ} (hj : 3 ≤ j) {z u : EscV k}
    (h : escCast z ∈ c57BigBox (0 : Fin (k + 2)) (escCast u) ((2 : ℝ) ^ j)) : z ∈ escBigBox j u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
  have hp : (2 : ℝ) ^ (m + 3) = 8 * 2 ^ m := by ring
  have hpz : (2 : ℤ) ^ (m + 3) = 8 * 2 ^ m := by ring
  have hm : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  refine ⟨?_, fun c hc => ?_⟩
  · have := h 0
    simp only [ite_true, escCast, hp] at this
    obtain ⟨h1, h2⟩ := this
    have h1' : u 0 ≤ z 0 := by exact_mod_cast h1
    have h2' : (z 0 : ℝ) ≤ u 0 + 7 * 2 ^ m := by linarith
    have h2'' : z 0 ≤ u 0 + 7 * 2 ^ m := by exact_mod_cast h2'
    rw [hpz]
    constructor <;> omega
  · have := h c
    simp only [ite_eq_right hc, escCast, hp] at this
    obtain ⟨h1, h2⟩ := this
    have h1' : (u c : ℝ) + 2 * 2 ^ m ≤ z c := by linarith
    have h2' : (z c : ℝ) ≤ u c + 6 * 2 ^ m := by linarith
    have h1'' : u c + 2 * 2 ^ m ≤ z c := by exact_mod_cast h1'
    have h2'' : z c ≤ u c + 6 * 2 ^ m := by exact_mod_cast h2'
    rw [hpz]
    constructor <;> omega

theorem not_escQ_of_cast {j : ℕ} (hj : 1 ≤ j) {z u : EscV k}
    (h : escCast z ∈ c57Bminus (0 : Fin (k + 2)) (escCast u) ((2 : ℝ) ^ j)) : z ∉ escQ j u := by
  intro hQ
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hp : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hpz : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h0 := h 0
  simp only [ite_true, escCast, hp] at h0
  have h2 : (z 0 : ℝ) < u 0 + 2 ^ m := by linarith [h0.2]
  have h2' : z 0 < u 0 + 2 ^ m := by exact_mod_cast h2
  have h1 : u 0 + 2 ^ (m + 1) / 2 ≤ z 0 := hQ.1.1
  rw [hpz] at h1
  omega

/-- The event `E₅₇` for a walk on `[0, Tn]`, at the test times. -/
def G57W (n j : ℕ) (u : EscV k) (i : ℕ) (S Tn : ℝ≥0) :
    Set (Set.Icc (0 : ℝ≥0) Tn → EscV k) :=
  {w | (∀ q ∈ qSet 0 S, ∀ hq : q ≤ Tn, escPoint n j u i + w ⟨q, ⟨bot_le, hq⟩⟩ ∈ escBigBox j u) ∧
    ∀ hS : S ≤ Tn, escPoint n j u i + w ⟨S, ⟨bot_le, hS⟩⟩ ∉ escQ j u}

theorem measurableSet_G57W (n j : ℕ) (u : EscV k) (i : ℕ) (S Tn : ℝ≥0) :
    MeasurableSet (G57W n j u i S Tn) := by
  have e : G57W n j u i S Tn =
      (⋂ q ∈ qSet 0 S, ⋂ hq : q ≤ Tn, {w : Set.Icc (0 : ℝ≥0) Tn → EscV k |
        escPoint n j u i + w ⟨q, ⟨bot_le, hq⟩⟩ ∈ escBigBox j u}) ∩
      ⋂ hS : S ≤ Tn, {w : Set.Icc (0 : ℝ≥0) Tn → EscV k |
        escPoint n j u i + w ⟨S, ⟨bot_le, hS⟩⟩ ∉ escQ j u} := by
    ext w; simp [G57W]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.biInter (qSet_countable 0 S) fun q _ =>
    MeasurableSet.iInter fun hq => ?_) (MeasurableSet.iInter fun hS => ?_)
  · exact (MeasurableSet.of_discrete (s := {v : EscV k | escPoint n j u i + v ∈ escBigBox j u})).preimage
      (measurable_pi_apply _)
  · exact (MeasurableSet.of_discrete (s := {v : EscV k | escPoint n j u i + v ∉ escQ j u})).preimage
      (measurable_pi_apply _)

/-- The clipped point of `[0, Tn]`. -/
def ptC (Tn s : ℝ≥0) : Set.Icc (0 : ℝ≥0) Tn := ⟨min s Tn, bot_le, min_le_right _ _⟩

theorem ptC_of_le {Tn s : ℝ≥0} (h : s ≤ Tn) : ptC Tn s = ⟨s, bot_le, h⟩ := by
  apply Subtype.ext
  exact min_eq_left h

/-- **`E₅₇` for the walk** (ES22 Claim 5.7; ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-, the induction hypothesis at arbitrary times (d), D11). -/
theorem lawW_57_ge {n : ℕ} (u : EscV k) {i : ℕ} (hi1 : 1 ≤ i)
    (hiI : i ≤ escIstar n (escJ n)) (_hn : 2 ≤ n) (_hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n)
    (hj : 3 ≤ escJ n) (hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n)
    {Tn S : ℝ≥0} (hTn : (Tn : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2)
    (hS : (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4) {σ ε η : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hε0 : 0 < ε) (hε : ε < (2 : ℝ) ^ escJ n / 64)
    {lawW : Measure (Set.Icc (0 : ℝ≥0) Tn → EscV k)}
    (h : AdmitsBMCoupling (k + 2) Tn lawW σ ε η) :
    ENNReal.ofReal (c57 (k + 2)) - ENNReal.ofReal η ≤ lawW (G57W n (escJ n) u i S Tn) := by
  obtain ⟨Q, hQ, hlaw, hB, -, hbd⟩ := exists_standardBrownianMotion_of_admitsBMCoupling h
  have := hQ
  set B := zeroMod (Prod.snd : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) → _) with hBdef
  have hne : (0 : Fin (k + 2)) ≠ 1 := by simp
  set j := escJ n with hjdef
  set L : ℝ := (2 : ℝ) ^ j with hL
  set ηi : ℝ := (i : ℝ) * (escLambda n : ℝ) with hηi
  have hL0 : 0 < L := by positivity
  have hη0 : 0 ≤ ηi := by positivity
  have hη : ηi ≤ 3 * L / 16 := by
    have h1 : (16 : ℝ) * (escIstar n j * escLambda n) ≤ 3 * 2 ^ j := by exact_mod_cast hIlam
    have h2 : (i : ℝ) ≤ escIstar n j := by exact_mod_cast hiI
    have h3 : (i : ℝ) * escLambda n ≤ escIstar n j * escLambda n :=
      mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    rw [hηi]; rw [hL]; linarith
  have hprob := c57_prob hB hne hσ1 hσ2 hL0 hη0 hη
  set E : Set (WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ)) :=
    {ω | pathMap B ω ∈ c57Set (0 : Fin (k + 2)) 1 σ L ηi} with hE
  set H : Set (WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ)) :=
    {p | ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) Tn,
      ENNReal.ofReal ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖} with hH
  have hmapset : lawW (G57W n j u i S Tn) =
      Q ((fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹'
        (G57W n j u i S Tn)) := by
    rw [← hlaw]
    exact Measure.map_apply (f := fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1)
      (measurable_subtype_coe.comp measurable_fst) (measurableSet_G57W _ _ _ _ _ _)
  have hcast : escCast (escPoint n j u i) = c57P (0 : Fin (k + 2)) 1 (escCast u) L ηi := by
    have := escCast_escPoint (k := k) n j (by omega) u i
    rw [this]; rfl
  have hsubset : E ∩ Hᶜ ⊆ (fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹'
      (G57W n j u i S Tn) := by
    rintro p ⟨hpE, hpH⟩
    have hpH' : ∀ t : Set.Icc (0 : ℝ≥0) Tn,
        ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖ < ε := by
      intro t
      simp only [hH, mem_compl_iff, mem_ofPred_eq, not_le] at hpH
      have := lt_of_le_of_lt (le_iSup (fun t : Set.Icc (0 : ℝ≥0) Tn =>
        ENNReal.ofReal ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖) t) hpH
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 this
    set y : ℝ≥0 → Fin (k + 2) → ℝ := fun s => escCast (escPoint n j u i + p.1.1 (ptC Tn s)) with hy
    have hyclose : ∀ s : ℝ≥0, (s : ℝ) ≤ L ^ 2 →
        ‖y s - (c57P (0 : Fin (k + 2)) 1 (escCast u) L ηi + σ • pathMap B p s)‖ < L / 64 := by
      intro s hs
      have hsT : s ≤ Tn := by
        rw [← NNReal.coe_le_coe, hTn]; exact hs
      have e1 : y s - (c57P (0 : Fin (k + 2)) 1 (escCast u) L ηi + σ • pathMap B p s) =
          escCast (p.1.1 (ptC Tn s)) - σ • B s p := by
        rw [← hcast]
        simp only [hy, pathMap, ptC_of_le hsT]
        funext c; simp [escCast]
      rw [e1, ptC_of_le hsT]
      have := hpH' ⟨s, bot_le, hsT⟩
      have this' : ‖escCast (p.1.1 ⟨s, bot_le, hsT⟩) - σ • B s p‖ < ε := this
      exact lt_trans this' (by linarith)
    have hw : Continuous (pathMap B p) := (hB.continuous_zero p).1
    obtain ⟨hbox, hB⟩ := c57_consequence hne hL0 hη0 hη hw hpE (escCast u) hyclose
    refine ⟨fun q hq hqT => ?_, fun hST => ?_⟩
    · have hqL : (q : ℝ) ≤ L ^ 2 := by
        have : q ≤ Tn := hqT
        rw [← hTn]; exact_mod_cast this
      have := hbox q hqL
      simp only [hy, ptC_of_le hqT] at this
      exact escBigBox_of_cast hj this
    · have hST' : (L ^ 2 / 4).toNNReal = S := by
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (by positivity), hS]
      have := hB
      rw [hST'] at this
      simp only [hy, ptC_of_le hST] at this
      exact not_escQ_of_cast (by omega) this
  have hQH : Q H ≤ ENNReal.ofReal η := hbd
  have h1 : Q E ≤ Q (E ∩ Hᶜ) + Q H := by
    calc Q E ≤ Q ((E ∩ Hᶜ) ∪ H) := measure_mono (fun p hp => by
          by_cases hh : p ∈ H
          · exact Or.inr hh
          · exact Or.inl ⟨hp, hh⟩)
      _ ≤ _ := measure_union_le _ _
  rw [hmapset]
  calc ENNReal.ofReal (c57 (k + 2)) - ENNReal.ofReal η ≤ Q E - Q H :=
        tsub_le_tsub hprob hQH
    _ ≤ Q (E ∩ Hᶜ) := tsub_le_iff_right.2 h1
    _ ≤ _ := measure_mono hsubset

end ElboimSly.Paper.Escape
