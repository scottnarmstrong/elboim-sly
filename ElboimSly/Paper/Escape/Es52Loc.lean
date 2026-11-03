/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Stop0
public import Mathlib

/-!
# Prop 5.2, Step 2: localization of the first walk of `𝒫₅`

t' and escK(β'); The connecting plan; ES22 Proposition 5.2.

On `𝒦(β')` the first walk of `𝒫₅(B, β', i)` stops at `ξ_B` and the first piece of the regenerated
walk is cut at `ξ_B`; hence the truncation of `𝒫_reg` at `T_B = ξ_B ∧ t_n` and the truncation of
`𝒫₅` at `S₁ = Λ₁` have the same ring measure and the same explored region.

* `escK_iff_ent5`: `𝒦(β')` is the event that the first entry of `𝒫₅` satisfies `EscKEnt`.
* `escS1_eq`: `S₁` is the length of the first entry.
* `loc_rm`, `loc_region`: the localization.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The `𝒦`-predicate on the first entry of a record. -/
def EscKEnt (β tn : ℝ) (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) (e : CycEntry ℕ (k + 2)) : Prop :=
  entEnd e ∈ escBlockMinus (escJ n) u ∧ e.len ≤ ENNReal.ofReal tn ∧
    cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ escJ n)) = (β' : ℝ)

/-- `T_B = ξ_B ∧ t_n` as a nonnegative real (junk-free since `t_n < ⊤`). -/
noncomputable def escT0 (β tn : ℝ) [Fact (0 < β)] (n : ℕ) (u : Fin (k + 2) → ℤ)
    (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0 :=
  (min (escXi (escWalk ν) (escBlock (escJ n) u)) (ENNReal.ofReal tn)).toNNReal

/-- `S₁ = Λ₁` of `𝒫₅`, as a nonnegative real. -/
noncomputable def escS1 (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (β' i : ℕ)
    (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0 :=
  (((plan5 n β tn u β' i hlog).envFinal ν).cum 1).toNNReal

/-! ### Generic lemmas -/

theorem pathXi_eq_of_agree {f g : ℝ≥0 → Fin (k + 2) → ℤ} {B : Set (Fin (k + 2) → ℤ)}
    {c : ℝ≥0∞} (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ c → f s = g s) (hlt : pathXi f B < c) :
    pathXi f B = pathXi g B := by
  obtain ⟨s0, hs0f, hs0lt⟩ : ∃ s : ℝ≥0, f s ∈ B ∧ (s : ℝ≥0∞) < c := by
    unfold pathXi at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨t, ht, htc⟩ := hlt
    exact ⟨t, ht, htc⟩
  apply le_antisymm
  · refine le_pathXi fun s hs => ?_
    by_cases hsc : (s : ℝ≥0∞) ≤ c
    · exact pathXi_le (by rw [h s hsc]; exact hs)
    · exact (pathXi_le hs0f).trans (hs0lt.le.trans (not_le.1 hsc).le)
  · refine le_pathXi fun s hs => ?_
    by_cases hsc : (s : ℝ≥0∞) ≤ c
    · exact pathXi_le (by rw [← h s hsc]; exact hs)
    · exact (pathXi_le (by rw [← h s0 hs0lt.le]; exact hs0f)).trans
        (hs0lt.le.trans (not_le.1 hsc).le)

/-- Entries with the same data, the same length and the same path up to the length have the
same region. -/
theorem entry_region_congr {e e' : CycEntry ℕ (k + 2)} (hd : e.data = e'.data)
    (hl : e.len = e'.len)
    (hf : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ e.len → e.path.fn s = e'.path.fn s) (β : ℝ) :
    e.region β = e'.region β ∧ e.ringSet β = e'.ringSet β := by
  have hleft : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) ≤ e.len → e.path.left r = e'.path.left r := by
    intro r hr hrl
    refine e.path.left_eq_of_eventually hr ?_
    have hne : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
    filter_upwards [e'.path.eventually_left hr, self_mem_nhdsWithin (a := r) (s := Iio r)]
      with s hs hsr
    rw [hf s ((ENNReal.coe_le_coe.2 (le_of_lt hsr)).trans hrl), hs]
  constructor
  · ext x
    constructor
    · rintro ⟨r, hr, hrl, h1, h2, h3⟩
      refine ⟨r, hr, hl ▸ hrl, ?_, ?_, ?_⟩
      · rw [← hd]; exact h1
      · rw [← hd]; exact h2
      · rw [← hleft r hr hrl]; exact h3
    · rintro ⟨r, hr, hrl, h1, h2, h3⟩
      have hrl' : (r : ℝ≥0∞) ≤ e.len := hl ▸ hrl
      refine ⟨r, hr, hrl', ?_, ?_, ?_⟩
      · rw [hd]; exact h1
      · rw [hd]; exact h2
      · rw [hleft r hr hrl']; exact h3
  · ext x
    constructor
    · rintro ⟨r, hr, hrl, hne, h1, h2, h3⟩
      have hfr := hf r hrl
      refine ⟨r, hr, hl ▸ hrl, ?_, ?_, ?_, ?_⟩
      · rw [← hleft r hr hrl, ← hfr]; exact hne
      · rw [← hd]; exact h1
      · rw [← hd]; exact h2
      · rw [← hleft r hr hrl, ← hfr]; exact h3
    · rintro ⟨r, hr, hrl, hne, h1, h2, h3⟩
      have hrl' : (r : ℝ≥0∞) ≤ e.len := hl ▸ hrl
      have hfr := hf r hrl'
      refine ⟨r, hr, hrl', ?_, ?_, ?_, ?_⟩
      · rw [hleft r hr hrl', hfr]; exact hne
      · rw [hd]; exact h1
      · rw [hd]; exact h2
      · rw [hleft r hr hrl', hfr]; exact h3

/-- An entry of length `0` has empty region and ring set. -/
theorem entry_len_zero {e : CycEntry ℕ (k + 2)} (h : e.len = 0) (β : ℝ) :
    e.region β = ∅ ∧ e.ringSet β = ∅ := by
  constructor
  · ext x
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨r, hr, hrl, -⟩
    rw [h] at hrl
    exact absurd (ENNReal.coe_le_coe.1 (by simpa using hrl)) (not_le.2 hr)
  · ext x
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨r, hr, hrl, -⟩
    rw [h] at hrl
    exact absurd (ENNReal.coe_le_coe.1 (by simpa using hrl)) (not_le.2 hr)

/-- Region and ring set of a record whose entries after the first all have length `0`. -/
theorem rec_region_of_nth {ρ : CycRec ℕ (k + 2)} {e0 : CycEntry ℕ (k + 2)}
    (h0 : ρ.nth 0 = some e0) (hk : ∀ j : ℕ, 1 ≤ j → ∀ e, ρ.nth j = some e → e.len = 0) (β : ℝ) :
    ρ.region β = e0.region β ∧ ρ.ringSet β = e0.ringSet β := by
  constructor
  · ext x
    constructor
    · rintro ⟨e, ⟨j, hj⟩, hx⟩
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rw [h0] at hj; cases hj; exact hx
      · have := (entry_len_zero (hk j hjp e hj) β).1
        rw [this] at hx; exact absurd hx (by simp)
    · intro hx; exact ⟨e0, ⟨0, h0⟩, hx⟩
  · ext x
    constructor
    · rintro ⟨e, ⟨j, hj⟩, hx⟩
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rw [h0] at hj; cases hj; exact hx
      · have := (entry_len_zero (hk j hjp e hj) β).2
        rw [this] at hx; exact absurd hx (by simp)
    · intro hx; exact ⟨e0, ⟨0, h0⟩, hx⟩

/-! ### The first entry of `𝒫₅` -/

/-- The first piece of the regenerated walk, as a function of nonnegative times. -/
noncomputable def piece0 (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0 → Fin (k + 2) → ℤ :=
  fun s => cycWalk (cycSlice 0 ν) 0 0 (s : ℝ)

section entry0

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem dat5_zero_loc :
    dat (plan5 n β tn u β' i hlog) ν 0 = regionData (I := ℕ) (k + 2) 0 := by
  simp [dat, plan5, plan5Start, regionData]

theorem pth5_zero (hν : CycGood ν) :
    (pth5 n tn u β' i hlog ν 0).1.len = ⊤ ∧ (pth5 n tn u β' i hlog ν 0).1.fn = piece0 ν := by
  have h := envPath_len (δ := regionData (I := ℕ) (k + 2) 0) (ν := ν) (hν 0)
  have e : pth5 n tn u β' i hlog ν 0 = envPath ν (regionData (I := ℕ) (k + 2) 0) := by
    unfold pth5 pth; rw [dat5_zero_loc]
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  funext s
  exact envFn_regionData ν 0 s

theorem ent5_len0 (hν : CycGood ν) :
    (ent5 n tn u β' i hlog ν 0).len =
      min (min (pathXi (piece0 ν) (escBlock (escJ n) u)) (cycTreg (cycSlice 0 ν)))
        (ENNReal.ofReal tn) := by
  rw [ent5_len, plan5_stopLen0_eq n tn u β' i hlog _ _ (pth5_zero n tn u β' i hlog ν hν).1,
    (pth5_zero n tn u β' i hlog ν hν).2]
  unfold piece0
  rw [pathTreg_cycWalk]

theorem ent5_fn0 (hν : CycGood ν) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν 0).len) :
    (ent5 n tn u β' i hlog ν 0).path.fn s = piece0 ν s := by
  rw [ent5_fn n tn u β' i hlog ν 0 hs, (pth5_zero n tn u β' i hlog ν hν).2]

theorem ent5_data0' : (ent5 n tn u β' i hlog ν 0).data = regionData (I := ℕ) (k + 2) 0 :=
  ent5_data_zero n tn u β' i hlog ν

theorem ent5_entEnd0 (hν : CycGood ν) (_hL : (ent5 n tn u β' i hlog ν 0).len ≠ ⊤) :
    entEnd (ent5 n tn u β' i hlog ν 0) =
      cycWalk (cycSlice 0 ν) 0 0 (ent5 n tn u β' i hlog ν 0).len.toReal := by
  unfold entEnd
  rw [ent5_fn0 n tn u β' i hlog ν hν ENNReal.coe_toNNReal_le_self]
  unfold piece0
  rw [ENNReal.coe_toNNReal_eq_toReal]

end entry0

theorem escWalk_piece0 {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ cycTreg (cycSlice 0 ν)) : escWalk ν (s : ℝ) = piece0 ν s := by
  exact escWalk_eq_first hν s.2 (by rw [ENNReal.ofReal_coe_nnreal, copyEnv_eq_cycSlice]; exact hs)

theorem escWalk_piece0_real {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {x : ℝ}
    (hx : 0 ≤ x) (hs : ENNReal.ofReal x ≤ cycTreg (cycSlice 0 ν)) :
    escWalk ν x = cycWalk (cycSlice 0 ν) 0 0 x :=
  escWalk_eq_first hν hx (by rw [copyEnv_eq_cycSlice]; exact hs)

theorem escXi_eq_xi0 {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) (n : ℕ) (u : EscV k)
    (h : pathXi (piece0 ν) (escBlock (escJ n) u) < cycTreg (cycSlice 0 ν) ∨
      escXi (escWalk ν) (escBlock (escJ n) u) < cycTreg (cycSlice 0 ν)) :
    escXi (escWalk ν) (escBlock (escJ n) u) = pathXi (piece0 ν) (escBlock (escJ n) u) := by
  rw [escXi_eq_pathXi]
  rcases h with h | h
  · exact (pathXi_eq_of_agree (f := piece0 ν) (g := fun t : ℝ≥0 => escWalk ν (t : ℝ))
      (fun s hs => (escWalk_piece0 hν hs).symm) h).symm
  · rw [escXi_eq_pathXi] at h
    exact pathXi_eq_of_agree (f := fun t : ℝ≥0 => escWalk ν (t : ℝ)) (g := piece0 ν)
      (fun s hs => escWalk_piece0 hν hs) h

section charK

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)

/-- **`𝒦(β')` is the event that the first entry of `𝒫₅` satisfies `EscKEnt`.** -/
theorem escK_iff_ent5 (_hadm : EscAdmissible (escJ n) u) (_htn : 0 < tn)
    {ν : Measure (CycS ℕ (k + 2) β)} :
    ν ∈ escKSet β tn n β' u ↔
      CycGood ν ∧ EscKEnt β tn n u β' (ent5 n tn u β' i hlog ν 0) := by
  have hβ : 0 < β := Fact.out
  constructor
  · rintro ⟨hν, hxle, hxlt, hWξ, hph⟩
    rw [copyEnv_eq_cycSlice] at hxlt
    have hx := escXi_eq_xi0 hν n u (Or.inr hxlt)
    have hL : (ent5 n tn u β' i hlog ν 0).len = escXi (escWalk ν) (escBlock (escJ n) u) := by
      rw [ent5_len0 n tn u β' i hlog ν hν, ← hx, min_eq_left hxlt.le, min_eq_left hxle]
    have hxtop : escXi (escWalk ν) (escBlock (escJ n) u) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxle
    refine ⟨hν, ?_, hL ▸ hxle, ?_⟩
    · rw [ent5_entEnd0 n tn u β' i hlog ν hν (hL ▸ hxtop), hL,
        ← escWalk_piece0_real hν ENNReal.toReal_nonneg
          (by rw [ENNReal.ofReal_toReal hxtop]; exact hxlt.le)]
      exact hWξ
    · rw [hL]; exact hph
  · rintro ⟨hν, hB, hle, hph⟩
    have hLtop : (ent5 n tn u β' i hlog ν 0).len ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    set L := (ent5 n tn u β' i hlog ν 0).len with hLdef
    have hlen := ent5_len0 n tn u β' i hlog ν hν
    rw [← hLdef] at hlen
    have hend := ent5_entEnd0 n tn u β' i hlog ν hν hLtop
    rw [← hLdef] at hend
    rw [hend] at hB
    have hBB := escBlockMinus_subset_block hB
    have hx0L : pathXi (piece0 ν) (escBlock (escJ n) u) ≤ L := by
      have := pathXi_le (f := piece0 ν) (B := escBlock (escJ n) u) (s := L.toNNReal)
        (by unfold piece0; rw [ENNReal.coe_toNNReal_eq_toReal]; exact hBB)
      rwa [ENNReal.coe_toNNReal hLtop] at this
    have hLx : L ≤ pathXi (piece0 ν) (escBlock (escJ n) u) := by
      rw [hlen]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hLeq : L = pathXi (piece0 ν) (escBlock (escJ n) u) := le_antisymm hLx hx0L
    have hLt : L ≤ cycTreg (cycSlice 0 ν) := by
      rw [hlen]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hlt : pathXi (piece0 ν) (escBlock (escJ n) u) < cycTreg (cycSlice 0 ν) := by
      refine lt_of_le_of_ne (hLeq ▸ hLt) ?_
      intro heq
      have hfin : cycTreg (cycSlice 0 ν) < ⊤ := heq ▸ hLeq ▸ lt_top_iff_ne_top.2 hLtop
      obtain ⟨m, -, hm0, hme⟩ := exists_cycTreg_eq hfin
      have hLreal : L.toReal = (m : ℝ) * β := by
        rw [hLeq, heq, hme, ENNReal.toReal_ofReal (by positivity)]
      have h0B : (0 : Fin (k + 2) → ℤ) ∈ escBlock (escJ n) u := by
        rw [hLreal, hm0] at hBB; exact hBB
      have h00 : pathXi (piece0 ν) (escBlock (escJ n) u) ≤ 0 := by
        have := pathXi_le (f := piece0 ν) (B := escBlock (escJ n) u) (s := 0)
          (by unfold piece0; simp only [NNReal.coe_zero]; rw [cycWalk_zero (hν 0)]; exact h0B)
        simpa using this
      have hge := regPlan_tau_ge (cycSlice 0 ν)
      rw [← heq] at hge
      have : (β.toNNReal : ℝ≥0∞) ≤ 0 := hge.trans h00
      exact absurd (ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hβ)) (not_lt.2 this)
    have hx := escXi_eq_xi0 hν n u (Or.inl hlt)
    refine ⟨hν, ?_, ?_, ?_, ?_⟩
    · rw [hx, ← hLeq]; exact hle
    · rw [copyEnv_eq_cycSlice, hx]; exact hlt
    · have hxtop : escXi (escWalk ν) (escBlock (escJ n) u) ≠ ⊤ := by
        rw [hx, ← hLeq]; exact hLtop
      rw [escWalk_piece0_real hν ENNReal.toReal_nonneg
        (by rw [ENNReal.ofReal_toReal hxtop, hx]; exact hlt.le), hx, ← hLeq]
      exact hB
    · rw [hx, ← hLeq]; exact hph

end charK

/-! ### Truncations -/

section trunc

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem envFinal_nth0 (P : CycPlan ℕ (k + 2) β) (hK : (0 : ℕ∞) < P.K) :
    (P.envFinal ν).nth 0 = some (P.E (rule P ν) 0) := by
  classical
  have h := CycPlan.cycFinal_nth_gen P (rule P ν) 0
  have hc : P.Cont (rule P ν) 0 := ⟨by exact_mod_cast hK, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [ite_eq_left hc] at h
  exact h

/-- `S₁ = Λ₁` is the length of the first entry. -/
theorem escS1_eq (_hν : CycGood ν) :
    ((plan5 n β tn u β' i hlog).envFinal ν).cum 1 = (ent5 n tn u β' i hlog ν 0).len := by
  have h0 := envFinal_nth0 ν (plan5 n β tn u β' i hlog) (by
    show (0 : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
    exact_mod_cast Nat.succ_pos _)
  unfold CycRec.cum
  rw [Finset.sum_range_one]
  unfold CycRec.lenAt
  rw [h0]
  rfl

theorem escS1_lt_top (hν : CycGood ν) :
    (ent5 n tn u β' i hlog ν 0).len < ⊤ := by
  have := plan5_planFin n β tn u β' i hlog ν hν 0 (by
    show (0 : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
    exact_mod_cast Nat.succ_pos _)
  exact this

/-- Truncating `𝒫_reg` before the closing time of the first piece leaves the first piece cut. -/
theorem reg_trunc {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < cycTreg (cycSlice 0 ν)) :
    ∃ e0 : CycEntry ℕ (k + 2),
      (CycRec.trunc s ((regPlan (k + 2) β).envFinal ν)).nth 0 = some e0 ∧
      e0.data = regionData (I := ℕ) (k + 2) 0 ∧ e0.len = s ∧
      (∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ s → e0.path.fn r = piece0 ν r) ∧
      ∀ j : ℕ, 1 ≤ j → (CycRec.trunc s ((regPlan (k + 2) β).envFinal ν)).nth j = none := by
  classical
  set P := regPlan (k + 2) β with hP
  have hK : (0 : ℕ∞) < P.K := by
    show (0 : ℕ∞) < (⊤ : ℕ∞)
    exact ENat.natCast_lt_top 0
  have hE := regPlan_E_env hν 0
  have hEn : P.E (rule P ν) 0 = P.E (fun k ρ => envPath ν (P.start k ρ)) 0 := rfl
  have hlam1 : lam P ν 1 = cycTreg (cycSlice 0 ν) := by
    rw [lam_succ]; simp only [lam, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [hEn]; exact hE.1
  have hlam0 : lam P ν 0 = 0 := by simp [lam]
  refine ⟨(P.E (rule P ν) 0).cut s, ?_, rfl, ?_, ?_, ?_⟩
  · rw [trunc_envFinal_nth P.junk s 0, ite_eq_left]
    · unfold tgt
      rw [hlam0, zero_add, ite_eq_right, tsub_zero]
      rw [hEn, hE.1]; exact not_le.2 hs
    · refine ⟨⟨hK, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, ?_⟩
      rw [hlam0]; exact zero_le
  · exact CPath.cut_len _ _
  · intro r hr
    show ((P.E (rule P ν) 0).2.1.cut s).fn r = _
    rw [CPath.cut_fn_of_le _ _ hr]
    have := hE.2 r (hr.trans hs.le)
    rw [hEn]
    exact this
  · intro j hj
    rw [trunc_envFinal_nth P.junk s j, ite_eq_right]
    rintro ⟨-, hl⟩
    have h1 : lam P ν 1 ≤ lam P ν j := lam_mono hj
    rw [hlam1] at h1
    exact absurd (hs.trans_le (h1.trans hl)) (lt_irrefl _)

/-- Truncating `𝒫₅` at `Λ₁` leaves the first entry and entries of length `0`. -/
theorem plan5_trunc {ν : Measure (CycS ℕ (k + 2) β)} (_hν : CycGood ν) {S : ℝ≥0}
    (hS : (S : ℝ≥0∞) = (ent5 n tn u β' i hlog ν 0).len) :
    (CycRec.trunc S ((plan5 n β tn u β' i hlog).envFinal ν)).nth 0 =
        some (ent5 n tn u β' i hlog ν 0) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ e, (CycRec.trunc S ((plan5 n β tn u β' i hlog).envFinal ν)).nth j =
        some e → e.len = 0 := by
  classical
  set P := plan5 n β tn u β' i hlog with hP
  have hK : (0 : ℕ∞) < P.K := by
    show (0 : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
    exact_mod_cast Nat.succ_pos _
  have hPF : PlanFin P := plan5_planFin n β tn u β' i hlog
  have hlam1 : lam P ν 1 = (S : ℝ≥0∞) := by
    rw [lam_succ]; simp only [lam, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [hS]; rfl
  have hlam0 : lam P ν 0 = 0 := by simp [lam]
  refine ⟨?_, ?_⟩
  · rw [trunc_envFinal_nth P.junk S 0, ite_eq_left]
    · unfold tgt
      rw [hlam0, zero_add, ite_eq_left]
      · rfl
      · show (P.E (rule P ν) 0).len ≤ S
        rw [hS]; rfl
    · refine ⟨⟨hK, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, ?_⟩
      rw [hlam0]; exact zero_le
  · intro j hj e he
    rw [trunc_envFinal_nth P.junk S j] at he
    by_cases hc : P.Cont (rule P ν) j ∧ lam P ν j ≤ (S : ℝ≥0∞)
    · rw [ite_eq_left hc] at he
      cases he
      have h1 : (S : ℝ≥0∞) ≤ lam P ν j := hlam1 ▸ lam_mono hj
      have hne : lam P ν j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc.2
      unfold tgt
      split_ifs with hh
      · have : lam P ν j + (P.E (rule P ν) j).len ≤ lam P ν j + 0 := by
          rw [add_zero]; exact hh.trans h1
        exact le_antisymm ((ENNReal.add_le_add_iff_left hne).1 this) zero_le
      · show ((P.E (rule P ν) j).2.1.cut _).len = 0
        rw [CPath.cut_len]
        exact tsub_eq_zero_of_le h1
    · rw [ite_eq_right hc] at he
      exact absurd he (by simp)

end trunc

/-! ### Localization on `𝒦(β')` -/

section loc

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)

theorem K_facts {ν : Measure (CycS ℕ (k + 2) β)} (hK : ν ∈ escKSet β tn n β' u) :
    CycGood ν ∧ escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn ∧
      escXi (escWalk ν) (escBlock (escJ n) u) < cycTreg (cycSlice 0 ν) ∧
      (ent5 n tn u β' i hlog ν 0).len = escXi (escWalk ν) (escBlock (escJ n) u) := by
  obtain ⟨hν, hxle, hxlt, -⟩ := hK
  rw [copyEnv_eq_cycSlice] at hxlt
  have hx := escXi_eq_xi0 hν n u (Or.inr hxlt)
  refine ⟨hν, hxle, hxlt, ?_⟩
  rw [ent5_len0 n tn u β' i hlog ν hν, ← hx, min_eq_left hxlt.le, min_eq_left hxle]

theorem loc_both (_hadm : EscAdmissible (escJ n) u) (_htn : 0 < tn)
    {ν : Measure (CycS ℕ (k + 2) β)} (hK : ν ∈ escKSet β tn n β' u) :
    (CycRec.trunc (escT0 β tn n u ν) ((regPlan (k + 2) β).envFinal ν)).region β =
        (CycRec.trunc (escS1 n tn u β' i hlog ν) ((plan5 n β tn u β' i hlog).envFinal ν)).region
          β ∧
      (CycRec.trunc (escT0 β tn n u ν) ((regPlan (k + 2) β).envFinal ν)).ringSet β =
        (CycRec.trunc (escS1 n tn u β' i hlog ν) ((plan5 n β tn u β' i hlog).envFinal ν)).ringSet
          β := by
  obtain ⟨hν, hxle, hxlt, hL⟩ := K_facts n tn u β' i hlog hK
  set xi := escXi (escWalk ν) (escBlock (escJ n) u) with hxi
  have hxtop : xi ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxle
  have hT : ((escT0 β tn n u ν : ℝ≥0) : ℝ≥0∞) = xi := by
    unfold escT0
    rw [← hxi, min_eq_left hxle, ENNReal.coe_toNNReal hxtop]
  have hS : ((escS1 n tn u β' i hlog ν : ℝ≥0) : ℝ≥0∞) = (ent5 n tn u β' i hlog ν 0).len := by
    unfold escS1
    rw [escS1_eq n tn u β' i hlog ν hν, ENNReal.coe_toNNReal (escS1_lt_top n tn u β' i hlog ν hν).ne]
  obtain ⟨e0, h0, hd, hl, hf, hrest⟩ := reg_trunc (s := escT0 β tn n u ν) hν (by rw [hT]; exact hxlt)
  obtain ⟨h0', hrest'⟩ := plan5_trunc n tn u β' i hlog hν hS
  have hR := rec_region_of_nth h0 (fun j hj e he => by rw [hrest j hj] at he; cases he) β
  have hP := rec_region_of_nth h0' hrest' β
  have hcong := entry_region_congr (e := e0) (e' := ent5 n tn u β' i hlog ν 0)
    (by rw [hd, ent5_data0']) (by rw [hl, hT, hL]) (fun s hs => by
      have hs' : (s : ℝ≥0∞) ≤ (escT0 β tn n u ν : ℝ≥0) := by rw [hl] at hs; exact hs
      rw [hf s hs', ent5_fn0 n tn u β' i hlog ν hν (by rw [hL, ← hT]; exact hs')]) β
  exact ⟨hR.1.trans (hcong.1.trans hP.1.symm), hR.2.trans (hcong.2.trans hP.2.symm)⟩

/-- **Localization of the ring measure.** -/
theorem loc_rm (hadm : EscAdmissible (escJ n) u) (htn : 0 < tn)
    {ν : Measure (CycS ℕ (k + 2) β)} (hK : ν ∈ escKSet β tn n β' u) :
    (CycRec.trunc (escT0 β tn n u ν) ((regPlan (k + 2) β).envFinal ν)).rm β =
      (CycRec.trunc (escS1 n tn u β' i hlog ν) ((plan5 n β tn u β' i hlog).envFinal ν)).rm β := by
  unfold CycRec.rm
  rw [(loc_both n tn u β' i hlog hadm htn hK).2]

/-- **Localization of the explored region.** -/
theorem loc_region (hadm : EscAdmissible (escJ n) u) (htn : 0 < tn)
    {ν : Measure (CycS ℕ (k + 2) β)} (hK : ν ∈ escKSet β tn n β' u) :
    (CycRec.trunc (escT0 β tn n u ν) ((regPlan (k + 2) β).envFinal ν)).region β =
      (CycRec.trunc (escS1 n tn u β' i hlog ν) ((plan5 n β tn u β' i hlog).envFinal ν)).region
        β :=
  (loc_both n tn u β' i hlog hadm htn hK).1

end loc

end ElboimSly.Paper.Escape
