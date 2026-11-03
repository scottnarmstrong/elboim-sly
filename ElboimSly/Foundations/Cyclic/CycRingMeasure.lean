/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Cyclic.PreGood
public import ElboimSly.Foundations.PPP.Simple
public import Mathlib

/-!
# The ring measure of a record

Basic properties of world-lines (b): for good `ν` and every record `ρ` whose entries are initial pieces
of environment paths, `ν|_{R(ρ)} = RM(ρ)`.

A good `ν` on `I × S_β` is the counting measure on its atoms (`cycGood_eq_count`): this is
Simple counting measures form a measurable set (b, c) on each copy. The ring set of a world-line is its region intersected with
the atoms (`entry_ringSet_eq`), by the swap rule.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)]

/-- The atoms of a measure on `I × S_β`. -/
def cycAtoms (ν : Measure (I × RingSpace d β)) : Set (I × RingSpace d β) := {x | ν {x} ≠ 0}

omit [Fact (0 < β)] in
theorem cycAtoms_inter_range (ι : I) (ν : Measure (I × RingSpace d β)) :
    cycAtoms ν ∩ range (Prod.mk ι) = Prod.mk ι '' SepPartSeq.atoms (cycSlice ι ν) := by
  ext x
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, by simpa [cycAtoms, SepPartSeq.atoms, cycSlice_singleton] using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by simpa [cycAtoms, SepPartSeq.atoms, cycSlice_singleton] using hy, y, rfl⟩

theorem measurableSet_cycAtoms [Countable I] {ν : Measure (I × RingSpace d β)}
    (hν : CycGood ν) : MeasurableSet (cycAtoms ν) := by
  have : cycAtoms ν = ⋃ ι : I, Prod.mk ι '' SepPartSeq.atoms (cycSlice ι ν) := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro hx
      exact ⟨x.1, by rw [← cycAtoms_inter_range]; exact ⟨hx, x.2, rfl⟩⟩
    · rintro ⟨ι, hx⟩
      rw [← cycAtoms_inter_range] at hx
      exact hx.1
  rw [this]
  exact MeasurableSet.iUnion fun ι =>
    (measurableEmbedding_prodMk_left ι).measurableSet_image.mpr
      (SepPartSeq.measurableSet_atoms (good_mem_bSimple (hν ι)))

/-- A good measure on `I × S_β` is the counting measure on its atoms. -/
theorem cycGood_eq_count [Countable I] {ν : Measure (I × RingSpace d β)} (hν : CycGood ν) :
    ν = Measure.count.restrict (cycAtoms ν) := by
  have hat := measurableSet_cycAtoms hν
  ext A hA
  have hcov : ∀ B : Set (I × RingSpace d β), B = ⋃ ι : I, B ∩ range (Prod.mk ι) := by
    intro B; ext x; simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨x.1, h, x.2, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : ∀ B : Set (I × RingSpace d β), Pairwise
      (Function.onFun Disjoint fun ι : I => B ∩ range (Prod.mk ι)) := by
    intro B ι ι' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    obtain ⟨y, rfl⟩ := hx.2
    obtain ⟨y', hy'⟩ := hx'.2
    exact (congrArg Prod.fst hy').symm
  have hrange : ∀ ι : I, MeasurableSet (range (Prod.mk ι) : Set (I × RingSpace d β)) :=
    fun ι => (measurableEmbedding_prodMk_left ι).measurableSet_range
  rw [Measure.restrict_apply hA]
  conv_lhs => rw [hcov A]
  conv_rhs => rw [hcov (A ∩ cycAtoms ν)]
  rw [measure_iUnion (hdisj A) fun ι => hA.inter (hrange ι),
    measure_iUnion (hdisj _) fun ι => (hA.inter hat).inter (hrange ι)]
  refine tsum_congr fun ι => ?_
  have h1 : A ∩ range (Prod.mk ι) = Prod.mk ι '' (Prod.mk ι ⁻¹' A) := by
    rw [Set.image_preimage_eq_inter_range]
  have h2 : (A ∩ cycAtoms ν) ∩ range (Prod.mk ι) =
      Prod.mk ι '' (Prod.mk ι ⁻¹' A ∩ SepPartSeq.atoms (cycSlice ι ν)) := by
    rw [Set.image_inter (measurableEmbedding_prodMk_left ι).injective, ← h1, ← cycAtoms_inter_range]
    ext x; simp only [mem_inter_iff]; tauto
  have hsl := SepPartSeq.eq_count_restrict_of_mem_bSimple (good_mem_bSimple (hν ι))
  have hAι : MeasurableSet (Prod.mk ι ⁻¹' A) := measurable_prodMk_left hA
  have hatι := SepPartSeq.measurableSet_atoms (good_mem_bSimple (hν ι))
  rw [Measure.count_apply ((hA.inter hat).inter (hrange ι)), h2,
    Set.InjOn.encard_image ((measurableEmbedding_prodMk_left ι).injective.injOn),
    ← Measure.count_apply (hAι.inter hatι), ← Measure.restrict_apply hAι, ← hsl, h1]
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left ι).comap_apply]

theorem CPath.cut_fn_of_le {V : Type*} (p : CPath V) (ℓ : ℝ≥0∞) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) ≤ ℓ) : (p.cut ℓ).fn r = p.fn r := by
  rw [CPath.cut_fn, min_eq_left h]; simp

/-- The ring set of an initial piece of an environment path is its region intersected with the
atoms of `ν`. -/
theorem entry_ringSet_eq [Countable I] {ν : Measure (I × RingSpace d β)} (hν : CycGood ν)
    (δ : CycData I d) (ℓ : ℝ≥0∞) :
    CycEntry.ringSet β ((δ, (envPath ν δ).cut ℓ) : CycEntry I d) =
      CycEntry.region β ((δ, (envPath ν δ).cut ℓ) : CycEntry I d) ∩ cycAtoms ν := by
  have hg := hν δ.copy
  ext x
  constructor
  · rintro ⟨r, hr0, hrl, hne, h1, h2, h3⟩
    have hrl' : (r : ℝ≥0∞) ≤ ℓ := by
      have : CycEntry.len ((δ, (envPath ν δ).cut ℓ) : CycEntry I d) = ℓ := CPath.cut_len _ _
      rwa [this] at hrl
    have h1 : x.1 = δ.copy := h1
    have h2 : x.2.2 = δ.clock β r := h2
    simp only [CycEntry.path, CycPath.cut] at hne h3
    rw [CPath.left_cut _ _ hr0 hrl', CPath.cut_fn_of_le _ _ hrl'] at hne h3
    have hsw := envPath_swap hg hr0
    have hex : ∃ e : Edge d, Edge.Mem ((envPath ν δ).1.left r) e ∧
        1 ≤ ν {(δ.copy, (e, δ.clock β r))} := by
      by_contra hno
      exact hne (hsw.2 hno).symm
    obtain ⟨e, he, hat⟩ := hex
    have heq := hsw.1 e he hat
    have hxe : x.2.1 = e := Subtype.ext (h3.trans heq.symm)
    have hx : x = (δ.copy, (e, δ.clock β r)) := Prod.ext h1 (Prod.ext hxe h2)
    refine ⟨⟨r, hr0, hrl, h1, h2, ?_⟩, ?_⟩
    · simp only [CycEntry.path, CycPath.cut]
      rw [CPath.left_cut _ _ hr0 hrl']
      show (envPath ν δ).1.left r ∈ x.2.1.1
      rw [h3]; exact Sym2.mem_mk_left _ _
    · show ν {x} ≠ 0
      rw [hx]
      exact fun h0 => absurd hat (by rw [h0]; simp)
  · rintro ⟨⟨r, hr0, hrl, h1, h2, h3⟩, hat⟩
    have hrl' : (r : ℝ≥0∞) ≤ ℓ := by
      have : CycEntry.len ((δ, (envPath ν δ).cut ℓ) : CycEntry I d) = ℓ := CPath.cut_len _ _
      rwa [this] at hrl
    have h1 : x.1 = δ.copy := h1
    have h2 : x.2.2 = δ.clock β r := h2
    simp only [CycEntry.path, CycPath.cut] at h3
    rw [CPath.left_cut _ _ hr0 hrl'] at h3
    have hx : x = (δ.copy, (x.2.1, δ.clock β r)) := by ext <;> simp [h1, h2]
    have hone : 1 ≤ ν {x} := by
      have hb := SepPartSeq.singleton_eq_zero_or_one (good_mem_bSimple (hν x.1)) x.2
      rw [cycSlice_singleton] at hb
      have : ν {(x.1, x.2)} = ν {x} := rfl
      rcases hb with hb | hb
      · exact absurd (by rw [← this]; exact hb) hat
      · rw [this] at hb; exact hb.ge
    rw [hx] at hone
    have hsw := envPath_swap hg hr0
    have heq := hsw.1 x.2.1 h3 hone
    have hadj := latticeAdj_of_edge x.2.1 heq
    have hne : (envPath ν δ).1.left r ≠ (envPath ν δ).1.fn r := by
      intro hh
      rw [← hh] at hadj
      simp at hadj
    refine ⟨r, hr0, hrl, ?_, h1, h2, ?_⟩
    · simp only [CycEntry.path, CycPath.cut]
      rw [CPath.left_cut _ _ hr0 hrl', CPath.cut_fn_of_le _ _ hrl']
      exact hne
    · simp only [CycEntry.path, CycPath.cut]
      rw [CPath.left_cut _ _ hr0 hrl', CPath.cut_fn_of_le _ _ hrl']
      exact heq

/-- Basic properties of world-lines (b). For good `ν` and a record whose entries are initial pieces of
environment paths, `ν|_{R(ρ)} = RM(ρ)`. -/
theorem restrict_region_eq_rm [Countable I] {ν : Measure (I × RingSpace d β)} (hν : CycGood ν)
    {ρ : CycRec I d}
    (hρ : ∀ e, ρ.IsEntry e → ∃ ℓ : ℝ≥0∞, e = (e.1, (envPath ν e.1).cut ℓ)) :
    ν.restrict (ρ.region β) = ρ.rm β := by
  have hat := measurableSet_cycAtoms hν
  have hring : ρ.ringSet β = ρ.region β ∩ cycAtoms ν := by
    ext x
    constructor
    · rintro ⟨e, he, hx⟩
      obtain ⟨ℓ, hℓ⟩ := hρ e he
      rw [hℓ, entry_ringSet_eq hν] at hx
      exact ⟨⟨e, he, by rw [hℓ]; exact hx.1⟩, hx.2⟩
    · rintro ⟨⟨e, he, hx⟩, hxa⟩
      obtain ⟨ℓ, hℓ⟩ := hρ e he
      refine ⟨e, he, ?_⟩
      rw [hℓ, entry_ringSet_eq hν]
      rw [hℓ] at hx
      exact ⟨hx, hxa⟩
  unfold CycRec.rm
  rw [hring, ← Measure.restrict_restrict' hat, ← cycGood_eq_count hν]

end ElboimSly.Cyclic

end
