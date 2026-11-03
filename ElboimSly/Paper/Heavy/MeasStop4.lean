/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop3

/-!
# The stopping time `τ'`

Measurability (a), (b).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ} {t₀ : ℝ} {n : ℕ}

theorem heavyTauPrime_eq_iInf :
    heavyTauPrime d t₀ n w = ⨅ p : {p : ℕ × (Fin d → ℤ) // heavyM0 d t₀ n ≤ p.1},
      heavyTauPrimeBlock d n w p.1.1 p.1.2 := by
  refine le_antisymm (le_iInf fun p => ?_) (le_iInf fun m => le_iInf fun hm => le_iInf fun ι => ?_)
  · exact iInf_le_of_le p.1.1 (iInf_le_of_le p.2 (iInf_le _ p.1.2))
  · exact iInf_le (fun p : {p : ℕ × (Fin d → ℤ) // heavyM0 d t₀ n ≤ p.1} =>
      heavyTauPrimeBlock d n w p.1.1 p.1.2) ⟨(m, ι), hm⟩

/-- Measurability (b): the infimum defining `τ'` is attained when finite. -/
theorem heavyTauPrime_attained (hw : IsCyclicPath w) (hn : 1 ≤ n)
    (h : heavyTauPrime d t₀ n w < ⊤) :
    ∃ m, heavyM0 d t₀ n ≤ m ∧ ∃ ι, heavyTauPrimeBlock d n w m ι = heavyTauPrime d t₀ n w := by
  rw [heavyTauPrime_eq_iInf] at h ⊢
  obtain ⟨p, hp⟩ := iInf_attained_of_finite_sublevel
    (fun p : {p : ℕ × (Fin d → ℤ) // heavyM0 d t₀ n ≤ p.1} =>
      heavyTauPrimeBlock d n w p.1.1 p.1.2)
    (fun T hT => (heavyTauPrimeBlock_sublevel_finite hw hn hT).preimage
      Subtype.val_injective.injOn) h
  exact ⟨p.1.1, p.2, p.1.2, hp⟩

theorem heavyTauPrime_le_iff (hw : IsCyclicPath w) (hn : 1 ≤ n) {T : ℝ} :
    heavyTauPrime d t₀ n w ≤ ENNReal.ofReal T ↔
      ∃ m, heavyM0 d t₀ n ≤ m ∧ ∃ ι, heavyTauPrimeBlock d n w m ι ≤ ENNReal.ofReal T := by
  constructor
  · intro h
    obtain ⟨m, hm, ι, e⟩ := heavyTauPrime_attained hw hn (h.trans_lt ENNReal.ofReal_lt_top)
    exact ⟨m, hm, ι, e ▸ h⟩
  · rintro ⟨m, hm, ι, h⟩
    exact (iInf_le_of_le m (iInf_le_of_le hm (iInf_le _ ι))).trans h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℝ≥0 mΩ} {W : Ω → ℝ → Fin d → ℤ}

theorem AdaptedCyclic.isStoppingTime_heavySi (h : AdaptedCyclic f W) (m : ℕ) (ι : Fin d → ℤ)
    (i : ℕ) : IsStoppingTime f (fun ω => heavySi (W ω) n m ι i) := by
  have := h.isStoppingTime_entSeq (f := f) (j := heavyScaleJ n) (mm := m) (ι := ι)
    (heavyD n m : ℝ≥0) i
  simpa [heavySi] using this

/-- Measurability (a): `τ'(B)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_heavyTauPrimeBlock (h : AdaptedCyclic f W) (m : ℕ)
    (ι : Fin d → ℤ) : IsStoppingTime f (fun ω => heavyTauPrimeBlock d n (W ω) m ι) :=
  h.isStoppingTime_heavySi m ι _

/-- Measurability (b): `τ'` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_heavyTauPrime (h : AdaptedCyclic f W) (hn : 1 ≤ n) :
    IsStoppingTime f (fun ω => heavyTauPrime d t₀ n (W ω)) := by
  intro i
  have hset : {ω | heavyTauPrime d t₀ n (W ω) ≤ (i : WithTop ℝ≥0)} =
      ⋃ m : ℕ, ⋃ _ : heavyM0 d t₀ n ≤ m, ⋃ ι : Fin d → ℤ,
        {ω | heavyTauPrimeBlock d n (W ω) m ι ≤ (i : ℝ≥0∞)} := by
    ext ω
    have := heavyTauPrime_le_iff (t₀ := t₀) (h.path ω) hn (T := (i : ℝ))
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_iUnion]
    exact this.trans (by simp only [exists_prop])
  have key : MeasurableSet[f i] (⋃ m : ℕ, ⋃ _ : heavyM0 d t₀ n ≤ m, ⋃ ι : Fin d → ℤ,
        {ω | heavyTauPrimeBlock d n (W ω) m ι ≤ (i : ℝ≥0∞)}) :=
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun ι =>
      h.isStoppingTime_heavyTauPrimeBlock m ι i
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

end ElboimSly.Paper
