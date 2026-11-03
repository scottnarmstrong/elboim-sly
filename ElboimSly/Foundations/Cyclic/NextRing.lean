/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.PreGood
public import ElboimSly.Foundations.Cyclic.Arc
public import ElboimSly.Foundations.Interchange.TrajProps
import Mathlib

/-!
# Next ring time of a set of edges

Measurability, Step 1 (the next ring time `R(ν, z, a)`).

For a finite set `E` of edges, `nxt ν E t` is the first time after `t` at which an edge of `E`
rings. On `Nice` it is attained when `E` ever rings, and the map `(ν, t) ↦ nxtJ ν E t`
(with the dummy value `t + 1` when `E` never rings, as in `exists_step_fwd`) is measurable.
The rational-witness trick replaces the dyadic limits of the written proof:
a ring in `(t, c]` exists iff for some rational `q > t` the arc `(q, c]` carries an atom.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Some edge of `E` rings at the real time `u`. -/
def RingsIn (ν : Measure (RingSpace d β)) (E : Set (Edge d)) (u : ℝ) : Prop :=
  ∃ e ∈ E, Rings ν e u

/-- Some edge of `E` ever rings. -/
def HasRing (ν : Measure (RingSpace d β)) (E : Set (Edge d)) : Prop := ∃ u, RingsIn ν E u

/-- The first ring time of `E` after `t`. -/
noncomputable def nxt (ν : Measure (RingSpace d β)) (E : Set (Edge d)) (t : ℝ) : ℝ :=
  sInf {u | t < u ∧ RingsIn ν E u}

open scoped Classical in
/-- `nxt`, with the dummy value `t + 1` when `E` never rings. -/
noncomputable def nxtJ (ν : Measure (RingSpace d β)) (E : Set (Edge d)) (t : ℝ) : ℝ :=
  if HasRing ν E then nxt ν E t else t + 1

theorem finite_times_Icc {F : Set (AddCircle β)} (hF : F.Finite) (p q : ℝ) :
    {t : ℝ | t ∈ Icc p q ∧ (t : AddCircle β) ∈ F}.Finite := by
  have hβ : 0 < β := Fact.out
  choose c hc using fun θ : AddCircle β => QuotientAddGroup.mk_surjective θ
  refine (hF.biUnion (fun θ _ => (Set.finite_Icc ⌈(p - c θ) / β⌉ ⌊(q - c θ) / β⌋).image
    (fun n : ℤ => c θ + n * β))).subset ?_
  rintro t ⟨⟨hp, hq⟩, hr⟩
  refine Set.mem_biUnion (x := (t : AddCircle β)) hr ?_
  have h1 : ((t - c (t : AddCircle β) : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub]
    have := hc (t : AddCircle β)
    rw [show (((c (t : AddCircle β) : ℝ)) : AddCircle β) = t from this, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp h1
  rw [zsmul_eq_mul] at hn
  refine ⟨n, ⟨?_, ?_⟩, by simp only []; linarith⟩
  · rw [Int.ceil_le, div_le_iff₀ hβ]; linarith
  · rw [Int.le_floor, le_div_iff₀ hβ]; linarith

theorem ringsIn_finite_Icc (hν : Nice ν) {E : Set (Edge d)} (hE : E.Finite) (p q : ℝ) :
    {t : ℝ | t ∈ Icc p q ∧ RingsIn ν E t}.Finite := by
  have hF : (⋃ e ∈ E, ringSet ν e).Finite := hE.biUnion fun e _ => hν.2 e
  refine (finite_times_Icc hF p q).subset ?_
  rintro t ⟨ht, e, he, hr⟩
  exact ⟨ht, Set.mem_biUnion he hr⟩

omit [Fact (0 < β)] in
theorem RingsIn.add_zsmul {E : Set (Edge d)} {u : ℝ} (h : RingsIn ν E u) (k : ℤ) :
    RingsIn ν E (u + k * β) := by
  obtain ⟨e, he, hr⟩ := h
  exact ⟨e, he, (Interchange.rings_add_zsmul e u k).mpr hr⟩

/-- If `E` ever rings, its first ring time after `t` exists and is `nxt`. -/
theorem isLeast_nxt (hν : Nice ν) {E : Set (Edge d)} (hE : E.Finite) (t : ℝ)
    (h : HasRing ν E) : IsLeast {u | t < u ∧ RingsIn ν E u} (nxt ν E t) := by
  have hβ : 0 < β := Fact.out
  obtain ⟨u0, hu0⟩ := h
  obtain ⟨k, hk⟩ := exists_nat_gt ((t - u0) / β)
  have hw : RingsIn ν E (u0 + (k : ℝ) * β) := by simpa using hu0.add_zsmul (k : ℤ)
  have hwt : t < u0 + (k : ℝ) * β := by
    rw [div_lt_iff₀ hβ] at hk; linarith
  set w := u0 + (k : ℝ) * β
  have hfin : {u | t < u ∧ u ≤ w ∧ RingsIn ν E u}.Finite :=
    (ringsIn_finite_Icc hν hE t w).subset (fun u ⟨h1, h2, h3⟩ => ⟨⟨h1.le, h2⟩, h3⟩)
  have hne : {u | t < u ∧ u ≤ w ∧ RingsIn ν E u}.Nonempty := ⟨w, hwt, le_rfl, hw⟩
  have hmem := hne.csInf_mem hfin
  have heq : nxt ν E t = sInf {u | t < u ∧ u ≤ w ∧ RingsIn ν E u} := by
    apply le_antisymm
    · exact csInf_le ⟨t, fun u hu => hu.1.le⟩ ⟨hmem.1, hmem.2.2⟩
    · refine le_csInf ⟨w, hwt, hw⟩ fun u ⟨hu1, hu2⟩ => ?_
      by_cases huw : u ≤ w
      · exact csInf_le hfin.bddBelow ⟨hu1, huw, hu2⟩
      · exact le_trans hmem.2.1 (not_le.mp huw).le
  rw [heq]
  exact ⟨⟨hmem.1, hmem.2.2⟩, fun u ⟨hu1, hu2⟩ => by
    by_cases huw : u ≤ w
    · exact csInf_le hfin.bddBelow ⟨hu1, huw, hu2⟩
    · exact le_trans hmem.2.1 (not_le.mp huw).le⟩

theorem nxt_le_iff (hν : Nice ν) {E : Set (Edge d)} (hE : E.Finite) (t c : ℝ)
    (h : HasRing ν E) : nxt ν E t ≤ c ↔ ∃ u, t < u ∧ u ≤ c ∧ RingsIn ν E u := by
  have hl := isLeast_nxt hν hE t h
  constructor
  · intro hc
    exact ⟨nxt ν E t, hl.1.1, hc, hl.1.2⟩
  · rintro ⟨u, hu1, hu2, hu3⟩
    exact (hl.2 ⟨hu1, hu3⟩).trans hu2

omit [Fact (0 < β)] in
theorem nxtJ_of_hasRing {E : Set (Edge d)} (t : ℝ) (h : HasRing ν E) : nxtJ ν E t = nxt ν E t := by
  simp [nxtJ, h]

omit [Fact (0 < β)] in
theorem nxtJ_of_not_hasRing {E : Set (Edge d)} (t : ℝ) (h : ¬ HasRing ν E) :
    nxtJ ν E t = t + 1 := by
  simp [nxtJ, h]

/-! ### Measurability -/

omit [Fact (0 < β)] in
/-- On `Nice`, an atom in `{e} × A` is a ring of `e` in `A`. -/
theorem exists_ring_iff (hν : Nice ν) (e : Edge d) {A : Set (AddCircle β)}
    (hA : MeasurableSet A) : (∃ θ ∈ A, θ ∈ ringSet ν e) ↔ 1 ≤ ν ({e} ×ˢ A) := by
  constructor
  · rintro ⟨θ, hθA, hθ⟩
    exact hθ.trans (measure_mono (fun p hp => by
      rw [Set.mem_singleton_iff.mp hp]; exact ⟨rfl, hθA⟩))
  · intro h
    obtain ⟨x, hx, h1⟩ := hν.1 _ ((measurableSet_singleton e).prod hA)
      (fun h0 => by rw [h0] at h; simp at h)
    obtain ⟨x1, x2⟩ := x
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_singleton_iff] at hx1
    subst hx1
    exact ⟨x2, hx2, h1⟩

theorem ringIn_arc_iff (hν : Nice ν) (e : Edge d) (q c : ℝ) :
    (∃ u, q < u ∧ u ≤ c ∧ Rings ν e u) ↔ 1 ≤ ν ({e} ×ˢ arc β q c) := by
  rw [← exists_ring_iff hν e (measurableSet_arc q c)]
  constructor
  · rintro ⟨u, h1, h2, h3⟩
    exact ⟨u, mem_arc_iff.mpr ⟨u, h1, h2, rfl⟩, h3⟩
  · rintro ⟨θ, hθ, hr⟩
    obtain ⟨u, h1, h2, rfl⟩ := mem_arc_iff.mp hθ
    exact ⟨u, h1, h2, hr⟩

/-- The event "some edge of `E` has an atom in `(q, c]`". -/
def ringInSet (E : Set (Edge d)) (q c : ℝ) : Set (Measure (RingSpace d β)) :=
  ⋃ e ∈ E, {ν | 1 ≤ ν ({e} ×ˢ arc β q c)}

theorem measurableSet_ringInSet (E : Set (Edge d)) (q c : ℝ) :
    MeasurableSet (ringInSet (β := β) E q c) :=
  MeasurableSet.biUnion (Set.to_countable E) fun e _ =>
    Measure.measurable_coe ((measurableSet_singleton e).prod (measurableSet_arc q c))
      measurableSet_Ici

theorem mem_ringInSet_iff (hν : Nice ν) (E : Set (Edge d)) (q c : ℝ) :
    ν ∈ ringInSet E q c ↔ ∃ u, q < u ∧ u ≤ c ∧ RingsIn ν E u := by
  simp only [ringInSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, RingsIn]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨u, h1, h2, h3⟩ := (ringIn_arc_iff hν e q c).mpr h
    exact ⟨u, h1, h2, e, he, h3⟩
  · rintro ⟨u, h1, h2, e, he, h3⟩
    exact ⟨e, he, (ringIn_arc_iff hν e q c).mp ⟨u, h1, h2, h3⟩⟩

/-- The event "`E` has a ring in `(t, c]`" as a subset of `Measure S × ℝ`. -/
def hasRingAfter (E : Set (Edge d)) (c : ℝ) : Set (Measure (RingSpace d β) × ℝ) :=
  ⋃ q : ℚ, {p | p.2 < q ∧ p.1 ∈ ringInSet E q c}

theorem measurableSet_hasRingAfter (E : Set (Edge d)) (c : ℝ) :
    MeasurableSet (hasRingAfter (β := β) E c) :=
  MeasurableSet.iUnion fun q =>
    (measurableSet_lt measurable_snd measurable_const).inter
      (measurable_fst (measurableSet_ringInSet E q c))

theorem mem_hasRingAfter_iff (hν : Nice ν) (E : Set (Edge d)) (t c : ℝ) :
    (ν, t) ∈ hasRingAfter E c ↔ ∃ u, t < u ∧ u ≤ c ∧ RingsIn ν E u := by
  simp only [hasRingAfter, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨u, h1, h2, h3⟩ := (mem_ringInSet_iff hν E q c).mp h
    exact ⟨u, hq.trans h1, h2, h3⟩
  · rintro ⟨u, h1, h2, h3⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    exact ⟨q, hq1, (mem_ringInSet_iff hν E q c).mpr ⟨u, hq2, h2, h3⟩⟩

/-- The event "`E` ever rings". -/
def hasRingSet (E : Set (Edge d)) : Set (Measure (RingSpace d β)) :=
  ⋃ e ∈ E, {ν | 1 ≤ ν ({e} ×ˢ Set.univ)}

omit [Fact (0 < β)] in
theorem measurableSet_hasRingSet (E : Set (Edge d)) : MeasurableSet (hasRingSet (β := β) E) :=
  MeasurableSet.biUnion (Set.to_countable E) fun e _ =>
    Measure.measurable_coe ((measurableSet_singleton e).prod MeasurableSet.univ) measurableSet_Ici

omit [Fact (0 < β)] in
theorem mem_hasRingSet_iff (hν : Nice ν) (E : Set (Edge d)) :
    ν ∈ hasRingSet E ↔ HasRing ν E := by
  simp only [hasRingSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, HasRing, RingsIn]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨θ, -, hθ⟩ := (exists_ring_iff hν e MeasurableSet.univ).mpr h
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact ⟨u, e, he, hθ⟩
  · rintro ⟨u, e, he, hr⟩
    exact ⟨e, he, (exists_ring_iff hν e MeasurableSet.univ).mp ⟨_, Set.mem_univ _, hr⟩⟩

/-- Measurability of the dummy-extended next ring time on `PreGood`. -/
theorem measurable_nxtJ {E : Set (Edge d)} (hE : E.Finite) :
    Measurable (fun p : NiceSet d β × ℝ => nxtJ p.1.1 E p.2) := by
  refine measurable_of_Iic fun c => ?_
  let U : Set (Measure (RingSpace d β) × ℝ) :=
    ((hasRingSet E ×ˢ Set.univ) ∩ hasRingAfter E c) ∪
      ((hasRingSet E)ᶜ ×ˢ Set.univ ∩ {p | p.2 + 1 ≤ c})
  have hU : MeasurableSet U :=
    (((measurableSet_hasRingSet E).prod MeasurableSet.univ).inter
      (measurableSet_hasRingAfter E c)).union
      ((((measurableSet_hasRingSet E).compl).prod MeasurableSet.univ).inter
        (measurableSet_le (measurable_snd.add measurable_const) measurable_const))
  have : (fun p : NiceSet d β × ℝ => nxtJ p.1.1 E p.2) ⁻¹' Iic c =
      (fun p : NiceSet d β × ℝ => ((p.1.1, p.2) : Measure (RingSpace d β) × ℝ)) ⁻¹' U := by
    ext ⟨⟨ν, hν⟩, t⟩
    simp only [Set.mem_preimage, Set.mem_Iic, U, Set.mem_union, Set.mem_inter_iff,
      Set.mem_prod, Set.mem_univ, and_true, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [mem_hasRingSet_iff hν]
    by_cases hH : HasRing ν E
    · rw [nxtJ_of_hasRing t hH, nxt_le_iff hν hE t c hH, mem_hasRingAfter_iff hν]
      simp [hH]
    · rw [nxtJ_of_not_hasRing t hH]
      simp [hH]
  rw [this]
  exact (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd) hU

end ElboimSly.Cyclic

end
