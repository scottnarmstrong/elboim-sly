/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasEnd
public import ElboimSly.Paper.Heavy.BadMeasMain

/-!
# The functionals before closing

The functionals before closing.

If `w = w'` on `[0, T]` (two cyclic paths) then for each of
`ξ_A`, `τ_fast`, `τ_jump`, `s_i(B)`, `τ'(B)`, `τ'`, `τ_bad` the event `{F ≤ T}` is the same for `w`
and `w'`; for the entrance-type functionals the values coincide on `{F ≤ T}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w w' : ℝ → Fin d → ℤ}

theorem entranceTime_le_of_agree (hw : IsCyclicPath w) {A : Set (Fin d → ℤ)} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, w s = w' s) (hle : entranceTime w A ≤ ENNReal.ofReal T) :
    entranceTime w' A ≤ entranceTime w A := by
  have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ A := by
    by_contra hno
    push Not at hno
    rw [entranceTime_eq_top_of_empty hno] at hle
    exact absurd hle (by simp)
  obtain ⟨s, hs0, hsA⟩ := hne
  obtain ⟨s'', h0, -, hmem, heq⟩ := exists_entrance_real hw hs0 hsA
  rw [heq] at hle ⊢
  have hsT : s'' ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hle
  exact entranceTime_le_of_mem h0 (by rwa [← h s'' ⟨h0, hsT⟩])

theorem entranceTime_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') {A : Set (Fin d → ℤ)}
    {T : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Icc 0 T, w s = w' s)
    (hle : entranceTime w A ≤ ENNReal.ofReal T) : entranceTime w A = entranceTime w' A := by
  have h1 := entranceTime_le_of_agree hw hT h hle
  have h2 := entranceTime_le_of_agree hw' hT (fun s hs => (h s hs).symm) (h1.trans hle)
  exact le_antisymm h2 h1

theorem heavyEntSeq_le_of_agree (j m : ℕ) (D : ℝ≥0∞) (ι : Fin d → ℤ) {T : ℝ} (hT : 0 ≤ T)
    {v v' : ℝ → Fin d → ℤ} (hv : IsCyclicPath v) (hv' : IsCyclicPath v')
    (hvv' : ∀ s ∈ Icc 0 T, v s = v' s) (i : ℕ)
    (ih : heavyEntSeq v j m D ι i ≤ ENNReal.ofReal T →
      heavyEntSeq v j m D ι i = heavyEntSeq v' j m D ι i)
    (hle : heavyEntSeq v j m D ι (i + 1) ≤ ENNReal.ofReal T) :
    heavyEntSeq v' j m D ι (i + 1) ≤ heavyEntSeq v j m D ι (i + 1) := by
  have hS : {x ∈ heavyEntrances v j m ι | heavyEntSeq v j m D ι i + D ≤ x}.Finite :=
    (heavyEntrances_finite v j m ι).subset fun x hx => hx.1
  have hne : {x ∈ heavyEntrances v j m ι | heavyEntSeq v j m D ι i + D ≤ x}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    have : heavyEntSeq v j m D ι (i + 1) = ⊤ := by
      show sInf _ = _
      rw [hemp]; exact sInf_empty
    rw [this] at hle
    exact absurd hle (by simp)
  obtain ⟨⟨ι', hι', hx⟩, hxD⟩ := hne.csInf_mem hS
  have hm : heavyEntSeq v j m D ι (i + 1) = entranceTime v (heavyBlock j ι') := hx.symm
  have hξT : entranceTime v (heavyBlock j ι') ≤ ENNReal.ofReal T := le_of_eq_of_le hm.symm hle
  have hsi : heavyEntSeq v j m D ι i ≤ ENNReal.ofReal T :=
    le_self_add.trans (hxD.trans ((le_of_eq hx.symm).trans hξT))
  have e1 := ih hsi
  have e2 := entranceTime_agree hv hv' hT hvv' hξT
  have hmem : entranceTime v' (heavyBlock j ι') ∈
      {x ∈ heavyEntrances v' j m ι | heavyEntSeq v' j m D ι i + D ≤ x} := by
    refine ⟨⟨ι', hι', rfl⟩, ?_⟩
    rw [← e1, ← e2]
    exact le_of_le_of_eq hxD hx.symm
  exact (sInf_le hmem).trans (le_of_eq (e2.symm.trans hm.symm))

theorem heavyEntSeq_agree (j m : ℕ) (D : ℝ≥0∞) (ι : Fin d → ℤ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ (i : ℕ) (v v' : ℝ → Fin d → ℤ), IsCyclicPath v → IsCyclicPath v' →
      (∀ s ∈ Icc 0 T, v s = v' s) → heavyEntSeq v j m D ι i ≤ ENNReal.ofReal T →
        heavyEntSeq v j m D ι i = heavyEntSeq v' j m D ι i := by
  intro i
  induction i with
  | zero => intro v v' hv hv' hvv' h0; exact entranceTime_agree hv hv' hT hvv' h0
  | succ i ih =>
    intro v v' hv hv' hvv' hle
    have a := heavyEntSeq_le_of_agree j m D ι hT hv hv' hvv' i (ih v v' hv hv' hvv') hle
    have b := heavyEntSeq_le_of_agree j m D ι hT hv' hv (fun s hs => (hvv' s hs).symm) i
      (ih v' v hv' hv fun s hs => (hvv' s hs).symm) (a.trans hle)
    exact le_antisymm b a

theorem cycJumpSet_congr {T : ℝ} (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    ∀ r ∈ Ioc 0 T, r ∈ cycJumpSet w ↔ r ∈ cycJumpSet w' := by
  intro r hr
  unfold cycJumpSet
  simp only [mem_ofPred_eq]
  refine and_congr_right fun _ => not_congr (Filter.eventually_congr ?_)
  filter_upwards [Ioo_mem_nhdsLT hr.1] with u hu
  rw [h u ⟨hu.1.le, hu.2.le.trans hr.2⟩, h r ⟨hr.1.le, hr.2⟩]

/-- The functionals before closing for `τ_fast`. -/
theorem pathTfast_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') {L : ℝ}
    (hL : 0 < L) {T : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    pathTfast w L ≤ ENNReal.ofReal T ↔ pathTfast w' L ≤ ENNReal.ofReal T := by
  rw [← not_lt, ← not_lt, ofReal_lt_pathTfast_congr hw hw' hL hT h]

/-- The functionals before closing for `τ_jump`. -/
theorem pathTjump_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') {L : ℝ}
    (hL : 0 < L) {T : ℝ} (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    pathTjump w L ≤ ENNReal.ofReal T ↔ pathTjump w' L ≤ ENNReal.ofReal T := by
  rw [← not_lt, ← not_lt, ofReal_lt_pathTjump_congr hw hw' hL (cycJumpSet_congr h)]

/-- The functionals before closing for the closing time `T(w)`. -/
theorem cycClosingTime_le_iff_of_agree {β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    cycClosingTime β w ≤ ENNReal.ofReal T ↔ cycClosingTime β w' ≤ ENNReal.ofReal T := by
  rw [cycClosingTime_le_iff hβ hT, cycClosingTime_le_iff hβ hT]
  refine exists_congr fun ℓ => and_congr Iff.rfl (and_congr_right fun hℓT => ?_)
  have h0 : 0 ≤ (ℓ : ℝ) * β := by positivity
  rw [h (ℓ * β) ⟨h0, hℓT⟩]

/-- The functionals before closing for `s_i(B)`: the event `{s_i(B) ≤ T}`. -/
theorem heavyEntSeq_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') (j m : ℕ)
    (D : ℝ≥0∞) (ι : Fin d → ℤ) (i : ℕ) {T : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyEntSeq w j m D ι i ≤ ENNReal.ofReal T ↔ heavyEntSeq w' j m D ι i ≤ ENNReal.ofReal T := by
  constructor
  · intro hle
    exact (heavyEntSeq_agree j m D ι hT i w w' hw hw' h hle) ▸ hle
  · intro hle
    exact (heavyEntSeq_agree j m D ι hT i w' w hw' hw (fun s hs => (h s hs).symm) hle) ▸ hle

/-- The functionals before closing for `τ'(B)`. -/
theorem heavyTauPrimeBlock_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') (n m : ℕ)
    (ι : Fin d → ℤ) {T : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyTauPrimeBlock d n w m ι ≤ ENNReal.ofReal T ↔
      heavyTauPrimeBlock d n w' m ι ≤ ENNReal.ofReal T :=
  heavyEntSeq_le_iff_of_agree hw hw' _ _ _ _ _ hT h

/-- The functionals before closing for `τ'`. -/
theorem heavyTauPrime_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') {t₀ : ℝ}
    {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyTauPrime d t₀ n w ≤ ENNReal.ofReal T ↔ heavyTauPrime d t₀ n w' ≤ ENNReal.ofReal T := by
  rw [heavyTauPrime_le_iff hw hn, heavyTauPrime_le_iff hw' hn]
  refine exists_congr fun m => and_congr Iff.rfl (exists_congr fun ι => ?_)
  exact heavyTauPrimeBlock_le_iff_of_agree hw hw' n m ι hT h

/-- The functionals before closing for `τ_bad`. -/
theorem heavyTauBad_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') {β t₀ : ℝ}
    {n : ℕ} (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyTauBad d β t₀ n w ≤ ENNReal.ofReal T ↔ heavyTauBad d β t₀ n w' ≤ ENNReal.ofReal T := by
  have key : ∀ ℓ, heavyBadTime d β t₀ n w ℓ ≤ ENNReal.ofReal T ↔
      heavyBadTime d β t₀ n w' ℓ ≤ ENNReal.ofReal T := by
    intro ℓ
    rw [heavyBadTime_le_iff hw hβ htk ℓ hT, heavyBadTime_le_iff hw' hβ htk ℓ hT,
      badCount_congr hβ htk (t := T) h]
  unfold heavyTauBad
  split_ifs
  · exact key _
  · exact key _

end ElboimSly.Paper
