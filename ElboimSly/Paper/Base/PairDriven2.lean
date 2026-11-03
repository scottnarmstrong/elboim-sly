/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairDriven
public import Mathlib

/-!
# The driven path of the second walk in cyclic walks within one lap

Cyclic walks within one lap (b), (c), "Walk 2".

* `drivenPath_two`: if the first walk has the same phase, the driven path of the second walk is
  the two-particle path `𝔉_{a,b}(X₁, X₂)` on `[0, L]`.
* `drivenPath_two_far`: if the windows are disjoint modulo `β`, it is `b + X₂` on `[0, L]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base Function

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem mem_region_one (ρ : CycRecN Unit d 1) (e : Edge d) (θ : AddCircle β) :
    (((), (e, θ)) : Unit × RingSpace d β) ∈ CycRec.region β (Sum.inl ⟨1, ρ⟩) ↔
      ∃ r' : ℝ≥0, 0 < r' ∧ (r' : ℝ≥0∞) ≤ (ρ 0).len ∧ θ = (ρ 0).data.clock β r' ∧
        Edge.Mem ((ρ 0).path.left r') e := by
  constructor
  · rintro ⟨e', ⟨k, hk⟩, r', h0, h1, -, h3, h4⟩
    have hk0 : k < 1 := by
      by_contra hh
      simp [CycRec.nth, hh] at hk
    obtain rfl : k = 0 := by omega
    simp only [CycRec.nth, dite_eq_left hk0, Option.some.injEq] at hk
    subst hk
    exact ⟨r', h0, h1, h3, h4⟩
  · rintro ⟨r', h0, h1, h3, h4⟩
    exact ⟨ρ 0, ⟨0, by simp [CycRec.nth]⟩, r', h0, h1, rfl, h3, h4⟩

omit [Fact (0 < β)] in
theorem mem_ringSet_one (ρ : CycRecN Unit d 1) (e : Edge d) (θ : AddCircle β) :
    (((), (e, θ)) : Unit × RingSpace d β) ∈ CycRec.ringSet β (Sum.inl ⟨1, ρ⟩) ↔
      ∃ r' : ℝ≥0, 0 < r' ∧ (r' : ℝ≥0∞) ≤ (ρ 0).len ∧ (ρ 0).path.left r' ≠ (ρ 0).path.fn r' ∧
        θ = (ρ 0).data.clock β r' ∧ e.1 = s((ρ 0).path.left r', (ρ 0).path.fn r') := by
  constructor
  · rintro ⟨e', ⟨k, hk⟩, r', h0, h1, h2, -, h4, h5⟩
    have hk0 : k < 1 := by
      by_contra hh
      simp [CycRec.nth, hh] at hk
    obtain rfl : k = 0 := by omega
    simp only [CycRec.nth, dite_eq_left hk0, Option.some.injEq] at hk
    subst hk
    exact ⟨r', h0, h1, h2, h4, h5⟩
  · rintro ⟨r', h0, h1, h2, h4, h5⟩
    exact ⟨ρ 0, ⟨0, by simp [CycRec.nth]⟩, r', h0, h1, h2, rfl, h4, h5⟩

omit [Fact (0 < β)] in
/-- The set of clocks carrying a known ring of a one-entry record is finite. -/
theorem finite_clocks_ringSet_one (ρ : CycRecN Unit d 1) (hlen : (ρ 0).len < ⊤) :
    {θ : AddCircle β | ∃ e : Edge d,
      (((), (e, θ)) : Unit × RingSpace d β) ∈ CycRec.ringSet β (Sum.inl ⟨1, ρ⟩)}.Finite := by
  set c := (ρ 0).path with hc
  set T := (ρ 0).len.toNNReal with hT
  refine ((c.fin T).image fun r' => (ρ 0).data.clock β r').subset ?_
  rintro θ ⟨e, he⟩
  obtain ⟨r', h0, h1, h2, h4, -⟩ := (mem_ringSet_one ρ e θ).1 he
  refine ⟨r', ⟨(c.mem_CDisc_iff h0).2 h2, ?_⟩, h4.symm⟩
  have : (r' : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by rw [hT, ENNReal.coe_toNNReal hlen.ne]; exact h1
  exact_mod_cast this

/-- The first walk of the record: data `(a, r₀, +1)`, length `L`, and path `a + X₁` on `[0, L]`. -/
structure FirstWalk (ρ : CycRecN Unit d 1) (a : Fin d → ℤ) (r0 : ℝ) (X1 : CPath (Fin d → ℤ))
    (L : ℝ≥0) : Prop where
  data : (ρ 0).data = ((), a, r0, true)
  len : (ρ 0).len = L
  fn : ∀ t ≤ L, (ρ 0).path.fn t = a + X1.fn t

variable {a b : Fin d → ℤ} {r0 : ℝ} {X1 X2 : CPath (Fin d → ℤ)} {L : ℝ≥0} {ρ : CycRecN Unit d 1}

theorem FirstWalk.left (h : FirstWalk ρ a r0 X1 L) {r : ℝ≥0} (hr : 0 < r) (hrL : r ≤ L) :
    (ρ 0).path.left r = a + leftLim X1.fn r := by
  rw [CPath.left_congr (ρ 0).path (translateCPath a X1) hr
    (fun t ht => h.fn t (ht.le.trans hrL)), translateCPath_left a X1 hr,
    cpath_left_eq_leftLim X1 hr]

theorem FirstWalk.region_iff (h : FirstWalk ρ a r0 X1 L) (hL : (L : ℝ) < β) {r : ℝ≥0}
    (hr : 0 < r) (hrL : r ≤ L) (e : Edge d) (b : Fin d → ℤ) :
    (((), (e, CycData.clock β (((), b, r0, true) : CycData Unit d) r)) : Unit × RingSpace d β) ∈
        CycRec.region β (Sum.inl ⟨1, ρ⟩) ↔ Edge.Mem ((ρ 0).path.left r) e := by
  rw [mem_region_one, h.data]
  constructor
  · rintro ⟨r', -, h1, h2, h3⟩
    have hr'L : r' ≤ L := by
      rw [h.len] at h1; exact_mod_cast h1
    have := (clock_eq_iff_of_lt (I := Unit) (δ := ((), b, r0, true)) (δ' := ((), a, r0, true))
      rfl rfl rfl hL hrL hr'L).1 h2
    subst this
    exact h3
  · intro hm
    refine ⟨r, hr, by rw [h.len]; exact_mod_cast hrL, rfl, hm⟩

theorem FirstWalk.ringSet_iff (h : FirstWalk ρ a r0 X1 L) (hL : (L : ℝ) < β) {r : ℝ≥0}
    (hr : 0 < r) (hrL : r ≤ L) (e : Edge d) (b : Fin d → ℤ) :
    (((), (e, CycData.clock β (((), b, r0, true) : CycData Unit d) r)) : Unit × RingSpace d β) ∈
        CycRec.ringSet β (Sum.inl ⟨1, ρ⟩) ↔
      ((ρ 0).path.left r ≠ (ρ 0).path.fn r ∧ e.1 = s((ρ 0).path.left r, (ρ 0).path.fn r)) := by
  rw [mem_ringSet_one, h.data]
  constructor
  · rintro ⟨r', -, h1, h2, h3, h4⟩
    have hr'L : r' ≤ L := by
      rw [h.len] at h1; exact_mod_cast h1
    have := (clock_eq_iff_of_lt (I := Unit) (δ := ((), b, r0, true)) (δ' := ((), a, r0, true))
      rfl rfl rfl hL hrL hr'L).1 h3
    subst this
    exact ⟨h2, h4⟩
  · rintro ⟨h2, h4⟩
    exact ⟨r, hr, by rw [h.len]; exact_mod_cast hrL, h2, rfl, h4⟩

theorem FirstWalk.region_iff_far (h : FirstWalk ρ a r0 X1 L) {r2 : ℝ}
    (h1 : r0 + L < r2) (h2 : r2 + L < r0 + β) {r : ℝ≥0} (hrL : r ≤ L) (e : Edge d)
    (b : Fin d → ℤ) :
    (((), (e, CycData.clock β (((), b, r2, true) : CycData Unit d) r)) : Unit × RingSpace d β) ∉
        CycRec.region β (Sum.inl ⟨1, ρ⟩) := by
  rw [mem_region_one, h.data]
  rintro ⟨r', -, h3, h4, -⟩
  have hr'L : r' ≤ L := by
    rw [h.len] at h3; exact_mod_cast h3
  exact clock_ne_of_disjoint (I := Unit) (δ := ((), a, r0, true)) (δ' := ((), b, r2, true))
    rfl rfl h1 h2 hr'L hrL h4.symm

theorem FirstWalk.ringSet_iff_far (h : FirstWalk ρ a r0 X1 L) {r2 : ℝ}
    (h1 : r0 + L < r2) (h2 : r2 + L < r0 + β) {r : ℝ≥0} (hrL : r ≤ L) (e : Edge d)
    (b : Fin d → ℤ) :
    (((), (e, CycData.clock β (((), b, r2, true) : CycData Unit d) r)) : Unit × RingSpace d β) ∉
        CycRec.ringSet β (Sum.inl ⟨1, ρ⟩) := by
  rw [mem_ringSet_one, h.data]
  rintro ⟨r', -, h3, -, h4, -⟩
  have hr'L : r' ≤ L := by
    rw [h.len] at h3; exact_mod_cast h3
  exact clock_ne_of_disjoint (I := Unit) (δ := ((), a, r0, true)) (δ' := ((), b, r2, true))
    rfl rfl h1 h2 hr'L hrL h4.symm

/-- **cyclic walks within one lap (b), walk 2**: the driven path of the second walk, started at the same
phase, is the two-particle path on `[0, L]`. -/
theorem drivenPath_two (_hXu1 : X1.UnitJumps) (hXu2 : X2.UnitJumps) (_hX1 : X1.fn 0 = 0)
    (_hX2 : X2.fn 0 = 0) (hL : (L : ℝ) < β) (h : FirstWalk ρ a r0 X1 L) :
    ∀ t ≤ L, (drivenPath β (CycRec.region β (Sum.inl ⟨1, ρ⟩))
      (CycRec.ringSet β (Sum.inl ⟨1, ρ⟩)) ((), b, r0, true) X2 0).1.fn t =
        twoParticle a b X1.fn X2.fn t := by
  classical
  set δ : CycData Unit d := ((), b, r0, true) with hδ
  have hs1 : IsStepPath X1.fn := ⟨X1.rc, X1.fin⟩
  have hs2 : IsStepPath X2.fn := ⟨X2.rc, X2.fin⟩
  have hy := isTwoParticle_twoParticle a b hs1 hs2
  have hys : IsStepPath (twoParticle a b X1.fn X2.fn) := hy.step
  have hlen : (ρ 0).len < ⊤ := by rw [h.len]; exact ENNReal.coe_lt_top
  have hQf := finite_clocks_ringSet_one (β := β) ρ hlen
  refine drivenPath_eq_of_rules hXu2 hQf (stepCPath _ hys) (by simp [stepCPath, hy.zero, δ,
    CycData.start]) fun r hr hrL => ?_
  have hf : δ.fwd = true := rfl
  have hq := hy.rule r hr
  have hql := stepCPath_left hys hr
  have hleft := h.left hr hrL
  have hfn : (ρ 0).path.fn r = a + X1.fn r := h.fn r hrL
  have hX2l := cpath_left_eq_leftLim X2 hr
  have hX1l := cpath_left_eq_leftLim X1 hr
  unfold DrvRule
  simp only [zero_add]
  rw [hql, hX2l]
  show RuleFn δ (δ.clock β r) (leftLim (twoParticle a b X1.fn X2.fn) r)
    (twoParticle a b X1.fn X2.fn r) _ _ _ _
  set w := leftLim (twoParticle a b X1.fn X2.fn) r with hw
  set v := twoParticle a b X1.fn X2.fn r with hv
  have hZ : ∀ e : Edge d, (δ.copy, (e, δ.clock β r)) ∈
      (CycRec.region β (Sum.inl ⟨1, ρ⟩) ∪ drvZown β δ (stepCPath _ hys) r) ↔
        (a + leftLim X1.fn r) ∈ e.1 := by
    intro e
    rw [mem_union]
    have h1 := (notMem_own hf hL hrL (stepCPath _ hys) e).1
    have h2 := h.region_iff hL hr hrL e b
    rw [hleft] at h2
    exact ⟨fun hh => hh.elim (fun x => h2.1 x) (fun x => absurd x h1), fun x => Or.inl (h2.2 x)⟩
  have hQ : ∀ e : Edge d, (δ.copy, (e, δ.clock β r)) ∈
      (CycRec.ringSet β (Sum.inl ⟨1, ρ⟩) ∪ drvQown β δ (stepCPath _ hys) r) ↔
        ((a + leftLim X1.fn r) ≠ (a + X1.fn r) ∧
          e.1 = s(a + leftLim X1.fn r, a + X1.fn r)) := by
    intro e
    rw [mem_union]
    have h1 := (notMem_own hf hL hrL (stepCPath _ hys) e).2
    have h2 := h.ringSet_iff hL hr hrL e b
    rw [hleft, hfn] at h2
    exact ⟨fun hh => hh.elim (fun x => h2.1 x) (fun x => absurd x h1), fun x => Or.inl (h2.2 x)⟩
  have hc1 : (r ∈ CDisc X1.fn ∧ (w = a + leftLim X1.fn r ∨ w = a + X1.fn r)) ↔
      (a + leftLim X1.fn r ≠ a + X1.fn r ∧ (w = a + leftLim X1.fn r ∨ w = a + X1.fn r)) := by
    rw [hs1.mem_CDisc_iff hr]; simp
  have hc2 : (r ∈ CDisc X2.fn ∧ a + leftLim X1.fn r ≠ w ∧
      a + leftLim X1.fn r ≠ w + (X2.fn r - leftLim X2.fn r)) ↔
      (leftLim X2.fn r ≠ X2.fn r ∧ a + leftLim X1.fn r ≠ w ∧
        a + leftLim X1.fn r ≠ w + (X2.fn r - leftLim X2.fn r)) := by
    rw [hs2.mem_CDisc_iff hr]
  refine ruleFn_pair (l := a + leftLim X1.fn r) (n := a + X1.fn r)
    (dv := X2.fn r - leftLim X2.fn r) hQ hZ ?_ ?_ ?_ ?_ ?_
  · intro hne
    have hd : r ∈ CDisc (ρ 0).path.fn := ((ρ 0).path.mem_CDisc_iff hr).2 (by
      rw [hleft, hfn]; exact hne)
    have := (ρ 0).2.2 r hd
    change ∑ i, |(ρ 0).path.fn r i - (ρ 0).path.left r i| = 1 at this
    rw [hleft, hfn] at this
    simpa [abs_sub_comm] using this
  · intro hj
    have hd : r ∈ CDisc X2.fn := (hs2.mem_CDisc_iff hr).2 hj
    have := hXu2 r hd
    rw [hX2l] at this
    simpa using this
  · intro hcond
    rw [hq]
    unfold twoStep
    rw [ite_eq_left (hc1.2 hcond)]
  · intro hn hjc
    rw [hq]
    unfold twoStep
    rw [ite_eq_right (fun hh => hn (hc1.1 hh)), ite_eq_left (hc2.2 hjc)]
  · intro hn hjc
    rw [hq]
    unfold twoStep
    rw [ite_eq_right (fun hh => hn (hc1.1 hh)), ite_eq_right (fun hh => hjc (hc2.1 hh))]

/-- **cyclic walks within one lap (c), walk 2**: if the windows of the two walks are disjoint modulo `β`,
the driven path of the second walk is `b + X₂` on `[0, L]`. -/
theorem drivenPath_two_far (hXu2 : X2.UnitJumps) (hX2 : X2.fn 0 = 0) (hL : (L : ℝ) < β)
    (h : FirstWalk ρ a r0 X1 L) {r2 : ℝ} (h1 : r0 + L < r2) (h2 : r2 + L < r0 + β) :
    ∀ t ≤ L, (drivenPath β (CycRec.region β (Sum.inl ⟨1, ρ⟩))
      (CycRec.ringSet β (Sum.inl ⟨1, ρ⟩)) ((), b, r2, true) X2 0).1.fn t = b + X2.fn t := by
  have hlen : (ρ 0).len < ⊤ := by rw [h.len]; exact ENNReal.coe_lt_top
  have hQf := finite_clocks_ringSet_one (β := β) ρ hlen
  refine drivenPath_eq_of_rules hXu2 hQf (translateCPath b X2) (by simp [translateCPath,
    stepCPath, hX2, CycData.start]) fun r hr hrL => ?_
  exact drvRule_translate hL _ _ hr hrL (fun e => h.region_iff_far h1 h2 hrL e b)
    (fun e => h.ringSet_iff_far h1 h2 hrL e b)

end ElboimSly.Paper

end
