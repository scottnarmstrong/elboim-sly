/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.BernoulliStopping

/-!
# Counting long gaps

Counting long gaps. For `[0,∞]`-valued `s_0 ≤ r_0 ≤ s_1 ≤ … ≤ r_{K-1} ≤ s_K`, the
number of `i` with `r_i ≥ s_i + L` is at most `⌊t/L⌋` on `{s_K ≤ t}`.
-/

public section

namespace ElboimSly

open MeasureTheory ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The success event `{r_i ≥ s_i + L}` of the `i`-th gap. -/
@[expose] def concGapEvent (s r : ℕ → Ω → ℝ≥0∞) (L : ℝ) (i : ℕ) : Set Ω :=
  {ω | s i ω + ENNReal.ofReal L ≤ r i ω}

/-- Counting long gaps, the pointwise counting bound `S · L ≤ t`. -/
lemma concGapEvent_count_mul_le {K : ℕ} {s r : ℕ → Ω → ℝ≥0∞}
    (hsr : ∀ i < K, ∀ ω, s i ω ≤ r i ω) (hrs : ∀ i < K, ∀ ω, r i ω ≤ s (i + 1) ω)
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {ω : Ω} (hω : s K ω ≤ ENNReal.ofReal t) :
    (concCount (concGapEvent s r L) K ω : ℝ) * L ≤ t := by
  have hmono : ∀ i j, i ≤ j → j ≤ K → s i ω ≤ s j ω := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      exact (ih (by omega)).trans ((hsr j (by omega) ω).trans (hrs j (by omega) ω))
  have hfin : ∀ j ≤ K, s j ω ≠ ⊤ := fun j hj =>
    ne_top_of_le_ne_top ofReal_ne_top ((hmono j K hj le_rfl).trans hω)
  have key : ∀ j ≤ K, (concCount (concGapEvent s r L) j ω : ℝ) * L ≤
      (s j ω).toReal - (s 0 ω).toReal := by
    intro j
    induction j with
    | zero => intro _; simp [concCount_zero]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hstep : (s j ω).toReal ≤ (s (j + 1) ω).toReal :=
        ENNReal.toReal_mono (hfin (j + 1) hj) (hmono j (j + 1) (by omega) hj)
      rw [concCount_succ]
      by_cases hA : ω ∈ concGapEvent s r L j
      · have h1 : s j ω + ENNReal.ofReal L ≤ s (j + 1) ω :=
          hA.trans (hrs j (by omega) ω)
        have h2 := ENNReal.toReal_mono (hfin (j + 1) hj) h1
        rw [ENNReal.toReal_add (hfin j (by omega)) ofReal_ne_top, ENNReal.toReal_ofReal hL.le]
          at h2
        rw [Set.indicator_of_mem hA]
        push_cast
        linarith
      · rw [Set.indicator_of_notMem hA]
        push_cast
        linarith
  have h := key K le_rfl
  have h0 : 0 ≤ (s 0 ω).toReal := ENNReal.toReal_nonneg
  have hK : (s K ω).toReal ≤ t := ENNReal.toReal_le_of_le_ofReal ht hω
  linarith

/-- **Counting long gaps.** Counting long gaps: on `{s_K ≤ t}` the number of long
gaps is at most `⌊t/L⌋`, so the probability that `s_K ≤ t` while all trials are active is at most
`P(Bin(K,p) ≤ ⌊t/L⌋)`. -/
theorem concGapCount_le [IsProbabilityMeasure μ] {K : ℕ} {s r : ℕ → Ω → ℝ≥0∞}
    (hsr : ∀ i < K, ∀ ω, s i ω ≤ r i ω) (hrs : ∀ i < K, ∀ ω, r i ω ≤ s (i + 1) ω)
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {G : ℕ → Set Ω} {𝒢 : ℕ → MeasurableSpace Ω}
    (h𝒢le : ∀ i ≤ K, 𝒢 i ≤ m0) (h𝒢mono : ∀ i < K, 𝒢 i ≤ 𝒢 (i + 1))
    (hG : ∀ i < K, MeasurableSet[𝒢 i] (G i))
    (hA : ∀ i < K, MeasurableSet[𝒢 (i + 1)] (concGapEvent s r L i))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : ∀ i < K, ∀ F, MeasurableSet[𝒢 i] F →
      p * μ.real (G i ∩ F) ≤ μ.real (concGapEvent s r L i ∩ G i ∩ F)) :
    μ.real ({ω | s K ω ≤ ENNReal.ofReal t} ∩ concGamma G K) ≤ concBinomLE K p ⌊t / L⌋ := by
  refine le_trans (measureReal_mono ?_) (concBernoulli_lower h𝒢le h𝒢mono hG hA hp0 hp1 hB ⌊t / L⌋)
  intro ω ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  have h := concGapEvent_count_mul_le hsr hrs hL ht h1
  show ((concCount (concGapEvent s r L) K ω : ℕ) : ℤ) ≤ ⌊t / L⌋
  rw [Int.le_floor, le_div_iff₀ hL]
  exact_mod_cast h


/-- Counting long gaps, last assertion: for stopping times `s_i ≤ r_i ≤ s_{i+1}` of a
filtration indexed by `ℝ≥0`, the gap event `A_i` lies in `ℱ_{s_{i+1}}`, so `𝒢_i = ℱ_{s_i}` is
admissible in `concGapCount_le`. -/
theorem measurableSet_concGapEvent_stopping {ℱ : Filtration NNReal m0} {K : ℕ}
    {s r : ℕ → Ω → ℝ≥0∞} (hs : ∀ i, IsStoppingTime ℱ (s i)) (hr : ∀ i, IsStoppingTime ℱ (r i))
    (hsr : ∀ i < K, ∀ ω, s i ω ≤ r i ω) (hrs : ∀ i < K, ∀ ω, r i ω ≤ s (i + 1) ω)
    {L : ℝ} {i : ℕ} (hi : i < K) :
    MeasurableSet[(hs (i + 1)).measurableSpace] (concGapEvent s r L i) :=
  measurableSet_add_const_le_stopping (hs i) (hr i) (hs (i + 1)) (hsr i hi) (hrs i hi) L.toNNReal

end ElboimSly
