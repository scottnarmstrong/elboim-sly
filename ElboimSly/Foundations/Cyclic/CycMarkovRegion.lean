/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovFilt
public import ElboimSly.Foundations.Cyclic.CycRegion
public import Mathlib

/-!
# The explored region and the ring measure in the language of the walk

Markov property of the environment at walk stopping times, proof ("`R^{𝒫_W}_s = ℛ_{(0,s]}(W)` because `c_{δ₀}(r) = [r]`", "the ring
measure in (a) is `cycRM(cycRec^{𝒫_W}(T))`").

* `cycJumpRings β f a b`: the points `({f(r-), f(r)}, [r])` of the jumps of `f` at times
  `r ∈ (a, b]`;
* `markovRegion N T ω = ℛ_{(0,T]}(W)` (`∅` on `{T = ∞}`), `markovRings N T ω` likewise for the jumps;
* `region_markovEntry`, `ringSet_markovEntry`: the region and known rings of `cycRec^{𝒫_W}(t)`
  are `{} × ℛ_{(0,t]}(W)` and `{} × (jump points)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The points `({f(r-), f(r)}, [r])` of the jumps of `f` at times `r ∈ (a, b]`: the support of the
ring measure of Markov property of the environment at walk stopping times (a). -/
def cycJumpRings (β : ℝ) (f : ℝ → Fin d → ℤ) (a b : ℝ) : Set (RingSpace d β) :=
  {x | ∃ t : ℝ, a < t ∧ t ≤ b ∧ x.2 = (t : AddCircle β) ∧
    ∃ z, IsLeftLimitAbove a f t z ∧ z ≠ f t ∧ x.1.1 = s(z, f t)}

section ll

variable {ν : Measure (RingSpace d β)}

theorem isLeftLimitAbove_congr_pos {f g : ℝ → Fin d → ℤ} (h : ∀ u, 0 < u → f u = g u) {t : ℝ}
    {z : Fin d → ℤ} (hz : IsLeftLimitAbove 0 f t z) : IsLeftLimitAbove 0 g t z :=
  hz.mono fun u hu hu0 => (h u hu0).symm.trans (hu hu0)

/-- For `r > 0`, `W(r-) = z` in the sense of `IsLeftLimitAbove` iff the half-line path has left
limit `z`. -/
theorem isLeftLimitAbove_walk_iff (_hν : Good ν) (p : CPath (Fin d → ℤ))
    (hp : ∀ r : ℝ≥0, p.fn r = ElboimSly.cycWalk ν 0 0 (r : ℝ)) {r : ℝ≥0} (hr : 0 < r)
    (z : Fin d → ℤ) :
    IsLeftLimitAbove 0 (fun s => ElboimSly.cycWalk ν 0 0 s) (r : ℝ) z ↔ p.left r = z := by
  have hcongr : ∀ u : ℝ, 0 < u → ElboimSly.cycWalk ν 0 0 u = fwdReal 0 p.fn u := by
    intro u hu
    simp only [fwdReal, sub_zero, hp, Real.coe_toNNReal _ hu.le]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h0 : IsLeftLimitAbove 0 (fun s => ElboimSly.cycWalk ν 0 0 s) (r : ℝ) (p.left r) := by
    refine isLeftLimitAbove_congr_pos (fun u hu => (hcongr u hu).symm) ?_
    refine fwdReal_isLeftLimitAbove hr' ?_
    have : (((r : ℝ) - 0).toNNReal) = r := by simp
    rw [this]
    exact p.eventually_left hr
  constructor
  · intro hz
    exact (IsLeftLimitAbove.unique hr' h0 hz)
  · rintro rfl; exact h0

end ll

/-- The region `ℛ_{(0,T]}(W)` of the walk `W` of `N` (`∅` on `{T = ∞}`). -/
noncomputable def markovRegion {Ω : Type*} (N : Ω → Measure (RingSpace d β))
    (T : Ω → WithTop ℝ≥0) (ω : Ω) : Set (RingSpace d β) :=
  (T ω).recTopCoe ∅ (fun t => cycRegion β (fun s => markovW N ω s) 0 (t : ℝ))

/-- The jump points of `W` on `(0, T]` (`∅` on `{T = ∞}`). -/
noncomputable def markovRings {Ω : Type*} (N : Ω → Measure (RingSpace d β))
    (T : Ω → WithTop ℝ≥0) (ω : Ω) : Set (RingSpace d β) :=
  (T ω).recTopCoe ∅ (fun t => cycJumpRings β (fun s => markovW N ω s) 0 (t : ℝ))

section entry

variable {ν : Measure (RingSpace d β)}

theorem markovEntry_left (ν : Measure (Unit × RingSpace d β)) {t r : ℝ≥0} (hr : 0 < r)
    (hrt : r ≤ t) : (markovEntry ν t).path.left r = (envPath ν (markovData d)).1.left r :=
  CPath.left_cut (envPath ν (markovData d)).1 (t : ℝ≥0∞) hr (by exact_mod_cast hrt)

theorem markovData_clock (r : ℝ≥0) : (markovData d).clock β r = ((r : ℝ) : AddCircle β) := by
  simp [markovData, CycData.clock, CycData.phase, CycData.sgn, CycData.fwd]

theorem region_markovEntry (hν : Good ν) (t : ℝ≥0) :
    (markovEntry (liftU ν) t).region β =
      {()} ×ˢ cycRegion β (fun s => ElboimSly.cycWalk ν 0 0 s) 0 (t : ℝ) := by
  have hp := envPath_fn_liftU hν
  have hLL := fun {r : ℝ≥0} (hr : 0 < r) (z : Fin d → ℤ) =>
    isLeftLimitAbove_walk_iff hν (envPath (liftU ν) (markovData d)).1 hp hr z
  ext x
  obtain ⟨⟨⟩, e, θ⟩ := x
  simp only [CycEntry.region, mem_prod, mem_singleton_iff, mem_ofPred_eq, cycRegion]
  constructor
  · rintro ⟨r, hr0, hrt, -, hθ, hmem⟩
    have hrt' : r ≤ t := by
      have : (r : ℝ≥0∞) ≤ t := by rwa [markovEntry_len] at hrt
      exact_mod_cast this
    refine ⟨trivial, r, by exact_mod_cast hr0, by exact_mod_cast hrt',
      ?_, (envPath (liftU ν) (markovData d)).1.left r, ?_, ?_⟩
    · rw [hθ]; exact markovData_clock r
    · exact (hLL hr0 _).2 rfl
    · rwa [markovEntry_left _ hr0 hrt'] at hmem
  · rintro ⟨-, τ, hτ0, hτt, hθ, z, hz, hmem⟩
    have hτ0' : 0 < τ.toNNReal := Real.toNNReal_pos.2 hτ0
    have hτe : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal _ hτ0.le
    rw [← hτe] at hz
    have hzl := (hLL hτ0' z).1 hz
    have hrt' : τ.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, hτe]; exact hτt
    refine ⟨τ.toNNReal, hτ0', ?_, trivial, ?_, ?_⟩
    · rw [markovEntry_len]; exact_mod_cast hrt'
    · rw [hθ]
      have := (markovData_clock (d := d) (β := β) τ.toNNReal).symm
      rw [hτe] at this
      exact this
    · rw [markovEntry_left _ hτ0' hrt', hzl]; exact hmem

theorem markovEntry_fn_of_le (ν : Measure (Unit × RingSpace d β)) {t r : ℝ≥0} (hrt : r ≤ t) :
    (markovEntry ν t).path.fn r = (envPath ν (markovData d)).1.fn r := by
  rw [markovEntry_fn, min_eq_left hrt]

theorem ringSet_markovEntry (hν : Good ν) (t : ℝ≥0) :
    (markovEntry (liftU ν) t).ringSet β =
      {()} ×ˢ cycJumpRings β (fun s => ElboimSly.cycWalk ν 0 0 s) 0 (t : ℝ) := by
  have hp := envPath_fn_liftU hν
  have hLL := fun {r : ℝ≥0} (hr : 0 < r) (z : Fin d → ℤ) =>
    isLeftLimitAbove_walk_iff hν (envPath (liftU ν) (markovData d)).1 hp hr z
  ext x
  obtain ⟨⟨⟩, e, θ⟩ := x
  simp only [CycEntry.ringSet, mem_prod, mem_singleton_iff, mem_ofPred_eq, cycJumpRings]
  constructor
  · rintro ⟨r, hr0, hrt, hne, -, hθ, he⟩
    have hrt' : r ≤ t := by
      have : (r : ℝ≥0∞) ≤ t := by rwa [markovEntry_len] at hrt
      exact_mod_cast this
    rw [markovEntry_left _ hr0 hrt', markovEntry_fn_of_le _ hrt', hp] at hne he
    refine ⟨trivial, r, by exact_mod_cast hr0, by exact_mod_cast hrt', ?_,
      (envPath (liftU ν) (markovData d)).1.left r, (hLL hr0 _).2 rfl, hne, he⟩
    rw [hθ]; exact markovData_clock r
  · rintro ⟨-, τ, hτ0, hτt, hθ, z, hz, hne, he⟩
    have hτ0' : 0 < τ.toNNReal := Real.toNNReal_pos.2 hτ0
    have hτe : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal _ hτ0.le
    have hrt' : τ.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, hτe]; exact hτt
    rw [← hτe] at hz hne he
    have hzl := (hLL hτ0' z).1 hz
    refine ⟨τ.toNNReal, hτ0', ?_, ?_, trivial, ?_, ?_⟩
    · rw [markovEntry_len]; exact_mod_cast hrt'
    · rw [markovEntry_left _ hτ0' hrt', markovEntry_fn_of_le _ hrt', hp, hzl]; exact hne
    · rw [hθ]
      have := (markovData_clock (d := d) (β := β) τ.toNNReal).symm
      rw [hτe] at this
      exact this
    · rw [markovEntry_left _ hτ0' hrt', markovEntry_fn_of_le _ hrt', hp, hzl]; exact he

end entry

section record

theorem region_inl_one (g : CycRecN Unit d 1) :
    CycRec.region β (Sum.inl ⟨1, g⟩ : CycRec Unit d) = (g 0).region β := by
  ext x
  simp only [CycRec.region, CycRec.IsEntry, CycRec.nth, mem_ofPred_eq]
  constructor
  · rintro ⟨e, ⟨k, hk⟩, hx⟩
    by_cases h : k < 1
    · simp only [h, dite_true, Option.some.injEq] at hk
      have : (⟨k, h⟩ : Fin 1) = 0 := Subsingleton.elim _ _
      rw [this] at hk; subst hk; exact hx
    · simp [h] at hk
  · intro hx
    exact ⟨g 0, ⟨0, by simp⟩, hx⟩

theorem ringSet_inl_one (g : CycRecN Unit d 1) :
    CycRec.ringSet β (Sum.inl ⟨1, g⟩ : CycRec Unit d) = (g 0).ringSet β := by
  ext x
  simp only [CycRec.ringSet, CycRec.IsEntry, CycRec.nth, mem_ofPred_eq]
  constructor
  · rintro ⟨e, ⟨k, hk⟩, hx⟩
    by_cases h : k < 1
    · simp only [h, dite_true, Option.some.injEq] at hk
      have : (⟨k, h⟩ : Fin 1) = 0 := Subsingleton.elim _ _
      rw [this] at hk; subst hk; exact hx
    · simp [h] at hk
  · intro hx
    exact ⟨g 0, ⟨0, by simp⟩, hx⟩

end record

end ElboimSly.Cyclic

end
