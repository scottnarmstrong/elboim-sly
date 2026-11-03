/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Events
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.Brownian.ESLemma53
public import ElboimSly.Foundations.Brownian.EscapeLine
public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import Mathlib

/-!
# The event `𝒢` from the Brownian coupling

ES22 Lemma 5.3, the paragraph "`𝒢` (`ℋ ∩ ℐ`, D11)".  If the law of the walk up to time `T'`
admits a `(σ, ε)`-coupling with failure probability `η` (hypothesis (H4) of the induction hypothesis at arbitrary times (d)), then the
walk satisfies `𝒢` with probability `≥ c_line - η` (`lawW_G_ge`), where `ε ≤ n^{17}/30` and
`ε ≤ 3·2^j/40`.  The Brownian ingredient is `es53_main` (ES22 Lemma 5.3: the event ℐ).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Bridge ElboimSly.Paper

variable {k : ℕ}

/-- The bad event of `𝒢` at a vertex `v` (a position of `W'_i`). -/
def EsGBad (n j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) (v : Fin (k + 2) → ℤ) : Prop :=
  (Metric.infDist (fun c => ((v c : ℤ) : ℝ))
      ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ≤ (2 : ℝ) ^ j / 8) ∨
    (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ I ∧ ℓ ≠ i ∧ ‖v - escPoint n j u ℓ‖ ≤ (n : ℝ) ^ 17 / 6)

theorem escCast_escPoint (n j : ℕ) (hj : 2 ≤ j) (u : Fin (k + 2) → ℤ) (ℓ : ℕ) :
    escCast (escPoint n j u ℓ) =
      es53P (0 : Fin (k + 2)) 1 (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) ((escLambda n : ℕ) : ℝ) ℓ := by
  funext c
  unfold es53P c57P escCast
  by_cases hc0 : c = 0
  · subst hc0
    simp only [ite_true]
    rw [escPoint_zero_coord hj]; ring
  · by_cases hc1 : c = 1
    · subst hc1
      simp only [ite_eq_right hc0, ite_true]
      rw [escPoint_one_coord hj]; ring
    · simp only [ite_eq_right hc0, ite_eq_right hc1]
      rw [escPoint_other_coord hj ℓ hc0 hc1]; ring

theorem lattice_subset_box (j : ℕ) (hj : 1 ≤ j) (u : Fin (k + 2) → ℤ) :
    ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ⊆
      c57Bminus (0 : Fin (k + 2)) (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) := by
  rintro _ ⟨y, hy, rfl⟩
  intro c
  have hh := cast_two_pow_pred hj
  by_cases hc : c = 0
  · subst hc
    simp only [ite_true]
    refine ⟨by exact_mod_cast hy.1.1, ?_⟩
    have : (y 0 : ℝ) < u 0 + ((2 : ℤ) ^ (j - 1) : ℤ) := by exact_mod_cast hy.1.2
    rw [hh] at this; exact this
  · simp only [ite_eq_right hc]
    have := hy.2 c hc
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- Pointwise: a lattice path close to a Brownian path in `𝔏` has no bad point. -/
theorem not_gBad_of_close (n j I : ℕ) (hj : 2 ≤ j) (u : Fin (k + 2) → ℤ) {i : ℕ}
    {ε : ℝ} (hε1 : ε ≤ (n : ℝ) ^ 17 / 30) (hε2 : ε ≤ 3 * (2 : ℝ) ^ j / 40)
    (hI : I ≤ n ^ 3) (z : Fin (k + 2) → ℝ) (v : Fin (k + 2) → ℤ)
    (hz1 : (2 : ℝ) ^ j / 5 ≤ Metric.infDist
      (es53P (0 : Fin (k + 2)) 1 (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) ((escLambda n : ℕ) : ℝ) i + z)
      (c57Bminus (0 : Fin (k + 2)) (fun c => (u c : ℝ)) ((2 : ℝ) ^ j)))
    (hz2 : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n ^ 3 → ℓ ≠ i → (n : ℝ) ^ 17 / 5 ≤
      ‖es53P (0 : Fin (k + 2)) 1 (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) ((escLambda n : ℕ) : ℝ) i + z -
        es53P (0 : Fin (k + 2)) 1 (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) ((escLambda n : ℕ) : ℝ) ℓ‖)
    (hclose : ‖escCast v - z‖ < ε) : ¬ EsGBad n j I u i (escPoint n j u i + v) := by
  have hcast : escCast (escPoint n j u i + v) = escCast (escPoint n j u i) + escCast v := by
    funext c; simp [escCast]
  rw [escCast_escPoint n j hj] at hcast
  set P : ℕ → Fin (k + 2) → ℝ := fun ℓ =>
    es53P (0 : Fin (k + 2)) 1 (fun c => (u c : ℝ)) ((2 : ℝ) ^ j) ((escLambda n : ℕ) : ℝ) ℓ with hP
  have hx : escCast (escPoint n j u i + v) = P i + escCast v := hcast
  have hne : ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u).Nonempty :=
    (escBlockMinus_nonempty (u := u) (by omega)).image _
  have hdist : dist (P i + z) (escCast (escPoint n j u i + v)) < ε := by
    rw [hx, dist_eq_norm]
    have : P i + z - (P i + escCast v) = z - escCast v := by abel
    rw [this, norm_sub_rev]; exact hclose
  rintro (h | ⟨ℓ, hℓ1, hℓI, hℓne, hℓ⟩)
  · have hsub := lattice_subset_box (u := u) j (by omega)
    have h1 := Metric.infDist_le_infDist_of_subset hsub hne (x := escCast (escPoint n j u i + v))
    have h2 := Metric.infDist_le_infDist_add_dist (x := P i + z)
      (y := escCast (escPoint n j u i + v))
      (s := c57Bminus (0 : Fin (k + 2)) (fun c => (u c : ℝ)) ((2 : ℝ) ^ j))
    have h' : Metric.infDist (escCast (escPoint n j u i + v))
        ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ≤ (2 : ℝ) ^ j / 8 := h
    linarith
  · have hℓn : ℓ ≤ n ^ 3 := hℓI.trans hI
    have h3 : (n : ℝ) ^ 17 / 5 ≤ ‖P i + z - P ℓ‖ := hz2 ℓ hℓ1 hℓn hℓne
    have htri := norm_sub_le_norm_sub_add_norm_sub (P i + z) (escCast (escPoint n j u i + v)) (P ℓ)
    have hPℓ : P ℓ = escCast (escPoint n j u ℓ) := (escCast_escPoint n j hj u ℓ).symm
    rw [hPℓ] at h3
    rw [hPℓ, norm_escCast_sub] at htri
    rw [dist_eq_norm] at hdist
    have := hℓ
    linarith

/-- The event `𝒢` for a walk path on `[0, T]`, at the test times. -/
def GsetW (n j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) (Tn : ℝ≥0) :
    Set (Set.Icc (0 : ℝ≥0) Tn → Fin (k + 2) → ℤ) :=
  {w | ¬ ∃ q ∈ qSet 0 Tn, ∃ hq : q ≤ Tn,
    EsGBad n j I u i (escPoint n j u i + w ⟨q, ⟨bot_le, hq⟩⟩)}

theorem measurableSet_GsetW (n j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) (Tn : ℝ≥0) :
    MeasurableSet (GsetW n j I u i Tn) := by
  have hc : GsetW n j I u i Tn = {w : Set.Icc (0 : ℝ≥0) Tn → Fin (k + 2) → ℤ | ∃ q ∈ qSet 0 Tn,
      ∃ hq : q ≤ Tn, EsGBad n j I u i (escPoint n j u i + w ⟨q, ⟨bot_le, hq⟩⟩)}ᶜ := by
    ext w; simp [GsetW]
  rw [hc]
  refine MeasurableSet.compl ?_
  have : {w : Set.Icc (0 : ℝ≥0) Tn → Fin (k + 2) → ℤ | ∃ q ∈ qSet 0 Tn, ∃ hq : q ≤ Tn,
      EsGBad n j I u i (escPoint n j u i + w ⟨q, ⟨bot_le, hq⟩⟩)} =
      ⋃ q ∈ qSet 0 Tn, ⋃ hq : q ≤ Tn, {w | EsGBad n j I u i (escPoint n j u i +
        w ⟨q, ⟨bot_le, hq⟩⟩)} := by
    ext w; simp
  rw [this]
  refine MeasurableSet.biUnion (qSet_countable 0 Tn) fun q _ => MeasurableSet.iUnion fun hq => ?_
  exact (MeasurableSet.of_discrete (s := {v : Fin (k + 2) → ℤ |
    EsGBad n j I u i (escPoint n j u i + v)})).preimage (measurable_pi_apply _)

theorem lawW_G_ge (hk : 3 ≤ k) {n : ℕ} (hn53 : n53 (k + 2) ≤ n) (u : Fin (k + 2) → ℤ) {i : ℕ}
    (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) (hIn : escIstar n (escJ n) ≤ n ^ 3)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n) (hj2 : 2 ≤ escJ n) {Tn : ℝ≥0}
    {σ ε η : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hε0 : 0 < ε) (hε1 : ε ≤ (n : ℝ) ^ 17 / 30)
    (hε2 : ε ≤ 3 * (2 : ℝ) ^ escJ n / 40)
    {lawW : Measure (Set.Icc (0 : ℝ≥0) Tn → Fin (k + 2) → ℤ)}
    (h : AdmitsBMCoupling (k + 2) Tn lawW σ ε η) :
    ENNReal.ofReal (cline (k + 2)) - ENNReal.ofReal η ≤
      lawW (GsetW n (escJ n) (escIstar n (escJ n)) u i Tn) := by
  obtain ⟨Q, hQ, hlaw, hB, -, hbd⟩ := exists_standardBrownianMotion_of_admitsBMCoupling h
  have := hQ
  set B := zeroMod (Prod.snd : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) → _) with hBdef
  have hne : (0 : Fin (k + 2)) ≠ 1 := by simp
  obtain ⟨hprob, hsub, heq, -⟩ := es53_main (m := k + 1) hB (by omega) hne
    (fun c => (u c : ℝ)) hσ1 hσ2 (N := n) (i := i) hn53 hi1 (hiI.trans hIn) hj1
  set E : Set (WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ)) :=
    {ω | pathMap B ω ∈ lineSet (0 : Fin (k + 2)) 1 σ ((n ^ 17 / 3 : ℕ) : ℝ) ((2 : ℝ) ^ escJ n)}
    with hE
  set H : Set (WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ)) :=
    {p | ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) Tn,
      ENNReal.ofReal ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖} with hH
  have hmapset : lawW (GsetW n (escJ n) (escIstar n (escJ n)) u i Tn) =
      Q ((fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹'
        (GsetW n (escJ n) (escIstar n (escJ n)) u i Tn)) := by
    rw [← hlaw]
    exact Measure.map_apply (f := fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1)
      (measurable_subtype_coe.comp measurable_fst) (measurableSet_GsetW _ _ _ _ _ _)
  have hsubset : E ∩ Hᶜ ⊆ (fun p : WalkPath (k + 2) Tn × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹'
      (GsetW n (escJ n) (escIstar n (escJ n)) u i Tn) := by
    rintro p ⟨hpE, hpH⟩ ⟨q, hq, hqT, hbad⟩
    have hpE' := hsub hpE
    rw [heq] at hpE'
    simp only [mem_ofPred_eq] at hpE'
    have hpH' : ∀ t : Set.Icc (0 : ℝ≥0) Tn,
        ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖ < ε := by
      intro t
      simp only [hH, mem_compl_iff, mem_ofPred_eq, not_le] at hpH
      have := lt_of_le_of_lt (le_iSup (fun t : Set.Icc (0 : ℝ≥0) Tn =>
        ENNReal.ofReal ‖(fun c => ((p.1.1 t c : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖) t) hpH
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 this
    have := hpE' q
    refine not_gBad_of_close n (escJ n) (escIstar n (escJ n)) hj2 u hε1 hε2 hIn
      (σ • B q p) (p.1.1 ⟨q, ⟨bot_le, hqT⟩⟩) this.1 this.2 (hpH' ⟨q, ⟨bot_le, hqT⟩⟩) hbad
  have hQE : ENNReal.ofReal (cline (k + 2)) ≤ Q E := hprob
  have hQH : Q H ≤ ENNReal.ofReal η := hbd
  have h1 : Q E ≤ Q (E ∩ Hᶜ) + Q H := by
    calc Q E ≤ Q ((E ∩ Hᶜ) ∪ H) := measure_mono (fun p hp => by
          by_cases hh : p ∈ H
          · exact Or.inr hh
          · exact Or.inl ⟨hp, hh⟩)
      _ ≤ _ := measure_union_le _ _
  rw [hmapset]
  calc ENNReal.ofReal (cline (k + 2)) - ENNReal.ofReal η ≤ Q E - Q H :=
        tsub_le_tsub hQE hQH
    _ ≤ Q (E ∩ Hᶜ) := tsub_le_iff_right.2 h1
    _ ≤ _ := measure_mono hsubset

end ElboimSly.Paper.Escape
