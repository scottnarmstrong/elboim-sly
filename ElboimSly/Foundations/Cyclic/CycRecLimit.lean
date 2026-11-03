/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycChainLimit2
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import Mathlib

/-!
# Measurability of record functionals (e): limits of growing records (definitions and chains)

Measurability of record functionals (e). A record `ρ'` *extends* `ρ` if every entry of `ρ` is an initial
piece of the entry of `ρ'` with the same index (same datum, and `p = p'(· ∧ ℓ)`, `ℓ ≤ ℓ'`). This is
weaker than the written proof's hypothesis (it does not ask the non-last entries to be equal), so the
statements below are slightly more general.

For a sequence `ρ_j(ϑ)` of records, each extending the previous, we define the limiting number of
entries, the stage `firstStage` at which entry `k` first occurs, and the chain of paths of entry `k`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

/-- `ρ'` extends `ρ`: every entry of `ρ` is an initial piece of the entry of `ρ'` with the same
index. -/
def CycRec.Extends (ρ ρ' : CycRec I d) : Prop :=
  ∀ k e, ρ.nth k = some e → ∃ e', ρ'.nth k = some e' ∧ e.data = e'.data ∧
    e.path.IsPiece e'.path

omit [MeasurableSpace I] in
theorem CycRec.Extends.refl (ρ : CycRec I d) : ρ.Extends ρ := fun _ e h =>
  ⟨e, h, rfl, CPath.isPiece_refl _⟩

omit [MeasurableSpace I] in
theorem CycRec.Extends.trans {ρ ρ' ρ'' : CycRec I d} (h : ρ.Extends ρ') (h' : ρ'.Extends ρ'') :
    ρ.Extends ρ'' := fun k e he => by
  obtain ⟨e', he', hd, hp⟩ := h k e he
  obtain ⟨e'', he'', hd', hp'⟩ := h' k e' he'
  exact ⟨e'', he'', hd.trans hd', hp.trans hp'⟩

section Seq

variable {Θ : Type*} (ρ : ℕ → Θ → CycRec I d)

/-- The limiting number of entries. -/
noncomputable def numLim (ϑ : Θ) : ℕ∞ := ⨆ j, (ρ j ϑ).num

/-- The first stage at which entry `k` occurs (`0` if it never does). -/
noncomputable def firstStage (k : ℕ) (ϑ : Θ) : ℕ :=
  open scoped Classical in
  if h : ∃ j, (k : ℕ∞) < (ρ j ϑ).num then Nat.find h else 0

variable (junk : CycEntry I d)

/-- The entry `k` at stage `j`, with the stages before it first occurs replaced by that stage. -/
noncomputable def stageEntry (k j : ℕ) (ϑ : Θ) : CycEntry I d :=
  (ρ (max j (firstStage ρ k ϑ)) ϑ).coord junk k

/-- The chain of paths of entry `k`. -/
noncomputable def stagePath (k : ℕ) (ϑ : Θ) (j : ℕ) : CPath (Fin d → ℤ) :=
  (stageEntry ρ junk k j ϑ).path

variable {ρ}

omit [MeasurableSpace I] in
theorem lt_numLim_iff {k : ℕ} {ϑ : Θ} :
    (k : ℕ∞) < numLim ρ ϑ ↔ ∃ j, (k : ℕ∞) < (ρ j ϑ).num := by
  unfold numLim
  rw [lt_iSup_iff]

omit [MeasurableSpace I] in
theorem nth_of_lt_num {ρ' : CycRec I d} {k : ℕ} (h : (k : ℕ∞) < ρ'.num) :
    ∃ e, ρ'.nth k = some e := by
  rcases ρ' with ⟨n, f⟩ | f
  · have : k < n := by simpa [CycRec.num] using h
    exact ⟨f ⟨k, this⟩, by simp [CycRec.nth, this]⟩
  · exact ⟨f k, by simp [CycRec.nth]⟩

omit [MeasurableSpace I] in
theorem lt_num_of_nth {ρ' : CycRec I d} {k : ℕ} {e : CycEntry I d} (h : ρ'.nth k = some e) :
    (k : ℕ∞) < ρ'.num := by
  rcases ρ' with ⟨n, f⟩ | f
  · have : k < n := by
      by_contra hh
      simp [CycRec.nth, hh] at h
    simpa [CycRec.num] using this
  · simp [CycRec.num]

end Seq

section Chain

variable {Θ : Type*} {ρ : ℕ → Θ → CycRec I d} (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ))
  (junk : CycEntry I d)
include hext

omit [MeasurableSpace I] in
theorem extends_of_le (ϑ : Θ) {j j' : ℕ} (h : j ≤ j') : (ρ j ϑ).Extends (ρ j' ϑ) := by
  induction h with
  | refl => exact CycRec.Extends.refl _
  | step _ ih => exact ih.trans (hext _ _)

omit [MeasurableSpace I] in
theorem lt_num_of_le (ϑ : Θ) {j j' : ℕ} (h : j ≤ j') {k : ℕ}
    (hk : (k : ℕ∞) < (ρ j ϑ).num) : (k : ℕ∞) < (ρ j' ϑ).num := by
  obtain ⟨e, he⟩ := nth_of_lt_num hk
  obtain ⟨e', he', -⟩ := extends_of_le hext ϑ h k e he
  exact lt_num_of_nth he'

omit hext [MeasurableSpace I] in
theorem firstStage_spec (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) :
    (k : ℕ∞) < (ρ (firstStage ρ k ϑ) ϑ).num := by
  classical
  have hex : ∃ j, (k : ℕ∞) < (ρ j ϑ).num := lt_numLim_iff.mp hk
  unfold firstStage
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

omit [MeasurableSpace I] in
theorem lt_num_stage (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) (j : ℕ) :
    (k : ℕ∞) < (ρ (max j (firstStage ρ k ϑ)) ϑ).num :=
  lt_num_of_le hext ϑ (le_max_right _ _) (firstStage_spec ϑ hk)

omit [MeasurableSpace I] in
theorem stageEntry_nth (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) (j : ℕ) :
    (ρ (max j (firstStage ρ k ϑ)) ϑ).nth k = some (stageEntry ρ junk k j ϑ) := by
  obtain ⟨e, he⟩ := nth_of_lt_num (lt_num_stage hext ϑ hk j)
  simp [stageEntry, CycRec.coord, he]

omit [MeasurableSpace I] in
theorem stageEntry_succ (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) (j : ℕ) :
    (stageEntry ρ junk k j ϑ).data = (stageEntry ρ junk k (j + 1) ϑ).data ∧
      (stageEntry ρ junk k j ϑ).path.IsPiece (stageEntry ρ junk k (j + 1) ϑ).path := by
  have h1 := stageEntry_nth hext junk ϑ hk j
  have h2 := stageEntry_nth hext junk ϑ hk (j + 1)
  have hle : max j (firstStage ρ k ϑ) ≤ max (j + 1) (firstStage ρ k ϑ) :=
    max_le_max (Nat.le_succ j) le_rfl
  obtain ⟨e', he', hd, hp⟩ := extends_of_le hext ϑ hle k _ h1
  rw [h2] at he'
  cases he'
  exact ⟨hd, hp⟩

omit [MeasurableSpace I] in
theorem stagePath_isChain (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) :
    CPath.IsChain (stagePath ρ junk k ϑ) := fun j => (stageEntry_succ hext junk ϑ hk j).2

omit [MeasurableSpace I] in
theorem stageEntry_data (ϑ : Θ) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) (j : ℕ) :
    (stageEntry ρ junk k j ϑ).data = (stageEntry ρ junk k 0 ϑ).data := by
  induction j with
  | zero => rfl
  | succ n ih => exact (stageEntry_succ hext junk ϑ hk n).1.symm.trans ih

end Chain

section Limit

variable {Θ : Type*} {ρ : ℕ → Θ → CycRec I d} (junk : CycEntry I d)

/-- The limiting jump times of entry `k` tend to `∞`. -/
def LimGood (ρ : ℕ → Θ → CycRec I d) (junk : CycEntry I d) (k : ℕ) (ϑ : Θ) : Prop :=
  ∀ M : ℕ, ∃ a, (M : ℝ≥0∞) < CPath.IsChain.tau (stagePath ρ junk k ϑ) a

omit [MeasurableSpace I] in
theorem LimGood.nnreal {k : ℕ} {ϑ : Θ} (h : LimGood ρ junk k ϑ) :
    ∀ M : ℝ≥0, ∃ a, (M : ℝ≥0∞) < CPath.IsChain.tau (stagePath ρ junk k ϑ) a := fun M => by
  obtain ⟨a, ha⟩ := h ⌈M⌉₊
  refine ⟨a, lt_of_le_of_lt ?_ ha⟩
  exact_mod_cast Nat.le_ceil M

/-- The set `Θ_0` of measurability of record functionals (e): every entry that occurs has limiting jump times
tending to `∞`. -/
def thetaZero (ρ : ℕ → Θ → CycRec I d) (junk : CycEntry I d) : Set Θ :=
  {ϑ | ∀ k : ℕ, (k : ℕ∞) < numLim ρ ϑ → LimGood ρ junk k ϑ}

variable (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ))

/-- The limit entry `k`: the datum, and the limit path of the chain of its paths. -/
noncomputable def limEntry (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (k : ℕ) (ϑ : Θ) :
    CycEntry I d :=
  open scoped Classical in
  if h : (k : ℕ∞) < numLim ρ ϑ ∧ LimGood ρ junk k ϑ then
    ((stageEntry ρ junk k 0 ϑ).data,
      ⟨(stagePath_isChain hext junk ϑ h.1).limPath (LimGood.nnreal junk h.2),
        unitJumps_limPath (stagePath_isChain hext junk ϑ h.1) (LimGood.nnreal junk h.2)
          (fun j => (stageEntry ρ junk k j ϑ).2.2)⟩)
  else junk

/-- The limit record `Φ(ϑ)` of measurability of record functionals (e) on `Θ_0`, and the empty record elsewhere. -/
noncomputable def recLim (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (ϑ : Θ) : CycRec I d :=
  open scoped Classical in
  if ϑ ∈ thetaZero ρ junk then
    (if numLim ρ ϑ = ⊤ then Sum.inr (fun k => limEntry junk hext k ϑ)
      else Sum.inl ⟨(numLim ρ ϑ).toNat, fun i => limEntry junk hext i ϑ⟩)
  else CycRec.empty

end Limit

end ElboimSly.Cyclic

end
