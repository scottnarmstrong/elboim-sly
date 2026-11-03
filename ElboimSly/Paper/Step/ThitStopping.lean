/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ThitKey
public import Mathlib

/-!
# `thit(R)` is a stopping time

Structure of relaxed times; stopping times (d), the part for `thit(R)`: if `R` is a stopping time of
the filtration `(𝒢_t)`, `w` is an adapted right-continuous lattice path and `α` is adapted with
the event times of `(w, α)` locally finite, then `thit(R)` (`:= ∞` on `{R = ∞}`) is a
`(𝒢_t)`-stopping time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- `thit(R)` for the sample path `ω`, `:= ∞` on `{R = ∞}`. -/
noncomputable def stepThitStop (β : ℝ) (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (R : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if R ω = ⊤ then ⊤ else
    stepThit β (stepExt fun s => w s ω) (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ))
      (stopReal R ω : ℝ)

/-- The event that the pair `(j, u)` is a witness for `thit(R) ≤ t` (see `stepThit_le_iff`). -/
def stepThitEvent (β : ℝ) (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (R : Ω → WithTop ℝ≥0) (j : ℕ) (u : ℝ≥0) : Set Ω :=
  {ω | R ω ≠ ⊤ ∧ ((α (stopReal R ω) ω : ℝ≥0) : ℝ) + j * β ≤ u ∧ R ω ≤ u ∧
    (u : ℝ) < stopReal R ω + j * β ∧
    ‖w u ω - w (((u : ℝ) - j * β).toNNReal) ω‖ ≤ 1}

theorem measurableSet_stepThitEvent {β : ℝ} (hβ : 0 < β) (f : Filtration ℝ≥0 m)
    (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (hw : ∀ t, Measurable[f t] (w t)) (hα : ∀ t, Measurable[f t] (α t))
    (hfin : ∀ ω, StepEventsFinite (stepExt fun s => w s ω)
      (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ)))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) (j : ℕ) (u : ℝ≥0) :
    MeasurableSet[f u] (stepThitEvent β w α R j u) := by
  classical
  have hjβ : 0 ≤ (j : ℝ) * β := by positivity
  set c : ℝ≥0 := ((u : ℝ) - j * β).toNNReal with hc
  have hcu : c ≤ u := by
    rw [hc, Real.toNNReal_le_iff_le_coe]
    linarith
  let Ua : Ω → Set ℝ := fun ω => {s | ((α s.toNNReal ω : ℝ≥0) : ℝ) + j * β ≤ u}
  have hUa : ∀ t : ℝ≥0, MeasurableSet[f t] {ω | (t : ℝ) ∈ Ua ω} := by
    intro t
    let : MeasurableSpace Ω := f t
    have h1 : Measurable fun ω => ((α t ω : ℝ≥0) : ℝ) + j * β :=
      (hα t).coe_nnreal_real.add_const _
    have h2 : MeasurableSet {ω | ((α t ω : ℝ≥0) : ℝ) + j * β ≤ u} :=
      measurableSet_le h1 measurable_const
    simpa [Ua] using h2
  have hlocUa : ∀ ω, IsLocIco (Ua ω) := fun ω => by
    have := isLocIco_alpha_le (hfin ω) ((u : ℝ) - j * β)
    convert this using 1
    ext s
    simp only [Ua, mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  have hA := measurableSet_stopped_mem f hUa hlocUa hR u
  have hB : MeasurableSet[f u] ({ω | (u : ℝ) < stopReal R ω + j * β} ∩ {ω | R ω ≤ u}) := by
    by_cases hneg : (u : ℝ) - j * β < 0
    · have : {ω | (u : ℝ) < stopReal R ω + j * β} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        have := (stopReal R ω).2
        linarith
      rw [this, univ_inter]
      exact hR u
    · push Not at hneg
      have hc' : (c : ℝ) = (u : ℝ) - j * β := by rw [hc, Real.coe_toNNReal _ hneg]
      have : {ω | (u : ℝ) < stopReal R ω + j * β} ∩ {ω | R ω ≤ u} =
          {ω | R ω ≤ u} \ {ω | R ω ≤ c} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h2, fun h3 => ?_⟩
          obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1
            (lt_of_le_of_lt h2 (WithTop.coe_lt_top u)).ne
          have h3 : R ω ≤ c := h3
          rw [← ha] at h3
          have h4 : a ≤ c := WithTop.coe_le_coe.1 h3
          have h5 : stopReal R ω = a := by simp only [stopReal, ← ha, WithTop.untopD_coe]
          rw [h5] at h1
          have : (a : ℝ) ≤ c := h4
          linarith
        · rintro ⟨h2, h3⟩
          refine ⟨?_, h2⟩
          obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1
            (lt_of_le_of_lt h2 (WithTop.coe_lt_top u)).ne
          have h5 : stopReal R ω = a := by simp only [stopReal, ← ha, WithTop.untopD_coe]
          rw [h5]
          have h6 : ¬ a ≤ c := fun h => h3 (by rw [← ha]; exact WithTop.coe_le_coe.2 h)
          have h7 : c < a := not_le.1 h6
          have h8 : (c : ℝ) < a := h7
          linarith
      rw [this]
      exact (hR u).diff (f.mono hcu _ (hR c))
  have hD : MeasurableSet[f u] {ω | ‖w u ω - w c ω‖ ≤ 1} := by
    have h1 : Measurable[f u] (w u) := hw u
    have h2 : Measurable[f u] (w c) := (hw c).mono (f.mono hcu) le_rfl
    let : MeasurableSpace Ω := f u
    have hs : MeasurableSet {p : (Fin d → ℤ) × (Fin d → ℤ) | ‖p.1 - p.2‖ ≤ 1} :=
      (Set.to_countable _).measurableSet
    exact (h1.prodMk h2) hs
  have heq : stepThitEvent β w α R j u =
      (({ω | R ω ≠ ⊤ ∧ (stopReal R ω : ℝ) ∈ Ua ω} ∩ {ω | R ω ≤ u}) ∩
        ({ω | (u : ℝ) < stopReal R ω + j * β} ∩ {ω | R ω ≤ u})) ∩
        {ω | ‖w u ω - w c ω‖ ≤ 1} := by
    ext ω
    simp only [stepThitEvent, Ua, mem_ofPred_eq, mem_inter_iff, Real.toNNReal_coe]
    tauto
  rw [heq]
  exact (hA.inter hB).inter hD

/-- Pointwise unpacking of `stepThitEvent` on `{R < ∞}`. -/
theorem mem_stepThitEvent_iff {β : ℝ} (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    {R : Ω → WithTop ℝ≥0} (j : ℕ) (u : ℝ≥0) (ω : Ω) (hR : R ω ≠ ⊤) :
    ω ∈ stepThitEvent β w α R j u ↔
      ((u : ℝ) ∈ stepVj β (stepExt fun s => w s ω) j ∧
        max ((fun r : ℝ => ((α r.toNNReal ω : ℝ≥0) : ℝ)) (stopReal R ω : ℝ) + j * β)
          (stopReal R ω : ℝ) ≤ u ∧ (u : ℝ) < (stopReal R ω : ℝ) + j * β) := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hR
  have h5 : stopReal R ω = a := by simp only [stopReal, ← ha, WithTop.untopD_coe]
  have hle : R ω ≤ u ↔ (a : ℝ) ≤ u := by
    rw [← ha]; exact WithTop.coe_le_coe.trans NNReal.coe_le_coe.symm
  simp only [stepThitEvent, stepVj, stepExt, mem_ofPred_eq, Real.toNNReal_coe, max_le_iff, hle,
    h5]
  tauto

/-- **`thit(R)` is a stopping time** (structure of relaxed times; stopping times (d)). -/
theorem isStoppingTime_stepThit {β : ℝ} (hβ : 1 < β) (f : Filtration ℝ≥0 m)
    (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (hw : ∀ t, Measurable[f t] (w t)) (hα : ∀ t, Measurable[f t] (α t))
    (hfin : ∀ ω, StepEventsFinite (stepExt fun s => w s ω)
      (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ)))
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) :
    IsStoppingTime f (fun ω => (stepThitStop β w α R ω : WithTop ℝ≥0)) := by
  classical
  have hβ0 : 0 < β := by linarith
  have hV : ∀ ω (j : ℕ), IsLocIco (stepVj β (stepExt fun s => w s ω) j) := fun ω j =>
    isLocIco_stepVj hβ0
      (fun a b hab hb => by
        simp only [stepExt, Real.toNNReal_of_nonpos hb, Real.toNNReal_of_nonpos (hab.trans hb)])
      (fun M => by
        obtain ⟨E, h0, hpos, htop, hc⟩ := (hfin ω).const_form M
        exact ⟨E, h0, hpos, htop, fun a b ha hab hno => (hc a b ha hab hno).1⟩) j
  intro t
  have key : {ω | (stepThitStop β w α R ω : WithTop ℝ≥0) ≤ t} =
      ⋃ j : ℕ, ⋃ (_ : 1 ≤ j), (stepThitEvent β w α R j t ∪
        ⋃ (q : ℚ) (_ : 0 ≤ q ∧ (q : ℝ) < t), stepThitEvent β w α R j ((q : ℝ).toNNReal)) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_union, exists_prop]
    by_cases hRt : R ω = ⊤
    · have h1 : (stepThitStop β w α R ω : WithTop ℝ≥0) = ⊤ := by simp [stepThitStop, hRt]
      rw [h1]
      constructor
      · intro h; exact absurd h (WithTop.not_top_le_coe _)
      · rintro ⟨j, -, h | ⟨q, -, h⟩⟩
        · exact absurd hRt h.1
        · exact absurd hRt h.1
    · have h1 : (stepThitStop β w α R ω : WithTop ℝ≥0) =
          stepThit β (stepExt fun s => w s ω) (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ))
            (stopReal R ω : ℝ) := by simp [stepThitStop, hRt]
      rw [h1]
      have h2 := stepThit_le_iff_rat (A := fun r : ℝ => ((α r.toNNReal ω : ℝ≥0) : ℝ)) hβ0
        (hV ω) (stopReal R ω).2 t
      rw [ENNReal.ofReal_coe_nnreal] at h2
      refine h2.trans ?_
      refine exists_congr fun j => and_congr_right fun _ => ?_
      rw [mem_stepThitEvent_iff w α j t ω hRt]
      refine or_congr Iff.rfl (exists_congr fun q => ?_)
      constructor
      · rintro ⟨hq0, hqt, hqV, hql, hqu⟩
        have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
        refine ⟨⟨hq0, hqt⟩, ?_⟩
        rw [mem_stepThitEvent_iff w α j _ ω hRt, Real.coe_toNNReal _ hq0']
        exact ⟨hqV, hql, hqu⟩
      · rintro ⟨⟨hq0, hqt⟩, h⟩
        have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
        rw [mem_stepThitEvent_iff w α j _ ω hRt, Real.coe_toNNReal _ hq0'] at h
        exact ⟨hq0, hqt, h.1, h.2.1, h.2.2⟩
  show MeasurableSet[f t] {ω | (stepThitStop β w α R ω : WithTop ℝ≥0) ≤ t}
  rw [key]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
  refine (measurableSet_stepThitEvent hβ0 f w α hw hα hfin hR j t).union ?_
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq.1
  have hle : (q : ℝ).toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq.2.le
  exact f.mono hle _ (measurableSet_stepThitEvent hβ0 f w α hw hα hfin hR j _)

end ElboimSly.Paper
