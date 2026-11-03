/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.TrajApi
public import ElboimSly.Foundations.Interchange.TrajProps
import Mathlib

/-!
# Explored regions, locality and disjointness

Explored region; Locality; Separation gives disjoint regions.

Paths are the real-time functions `f : ℝ → ℤᵈ` of `Interchange.IsPathOn`; the left limit
`γ(t-)` is `IsLeftLimitAbove a f t z` (looking at times above `a` only).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped NNReal ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν ν' : Measure (RingSpace d β)}

variable (β) in
/-- The explored region `R_{(a,b]}(f) = {(e, [t]) : t ∈ (a, b], e ∋ f(t-)}`.
Explored region. -/
def cycRegion (f : ℝ → Fin d → ℤ) (a b : ℝ) : Set (RingSpace d β) :=
  {p | ∃ t : ℝ, a < t ∧ t ≤ b ∧ p.2 = (t : AddCircle β) ∧
    ∃ z, IsLeftLimitAbove a f t z ∧ p.1.Mem z}

theorem isLeftLimitAbove_congr {a b : ℝ} {f g : ℝ → Fin d → ℤ} (h : ∀ t ∈ Icc a b, f t = g t)
    {t : ℝ} (_ha : a < t) (hb : t ≤ b) {z : Fin d → ℤ} (hz : IsLeftLimitAbove a f t z) :
    IsLeftLimitAbove a g t z := by
  filter_upwards [hz, self_mem_nhdsWithin (a := t) (s := Iio t)] with u hu hu' hau
  rw [← h u ⟨hau.le, (le_of_lt (lt_of_lt_of_le hu' hb))⟩]
  exact hu hau

omit [Fact (0 < β)] in
theorem cycRegion_congr {a b : ℝ} {f g : ℝ → Fin d → ℤ} (h : ∀ t ∈ Icc a b, f t = g t) :
    cycRegion β f a b = cycRegion β g a b := by
  ext p
  constructor
  · rintro ⟨t, h1, h2, h3, z, hz, hm⟩
    exact ⟨t, h1, h2, h3, z, isLeftLimitAbove_congr h h1 h2 hz, hm⟩
  · rintro ⟨t, h1, h2, h3, z, hz, hm⟩
    exact ⟨t, h1, h2, h3, z, isLeftLimitAbove_congr (fun t ht => (h t ht).symm) h1 h2 hz, hm⟩

omit [Fact (0 < β)] in
theorem rings_iff_of_restrict_eq {R : Set (RingSpace d β)}
    (h : ν.restrict R = ν'.restrict R) {e : Edge d} {t : ℝ}
    (hp : ((e, (t : AddCircle β)) : RingSpace d β) ∈ R) : Rings ν e t ↔ Rings ν' e t := by
  have key : ν {((e, (t : AddCircle β)) : RingSpace d β)} =
      ν' {((e, (t : AddCircle β)) : RingSpace d β)} := by
    have := congrArg (fun m : Measure (RingSpace d β) => m {((e, (t : AddCircle β)) :
      RingSpace d β)}) h
    simp only [Measure.restrict_apply (measurableSet_singleton _),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hp)] at this
    exact this
  unfold Rings ringSet
  simp only [Set.mem_ofPred_eq, key]

/-- Locality. If `ν` and `ν'` are good and agree on the explored region
of `γ^ν_{x,a}` over `(a, b]`, then `γ^{ν'}_{x,a} = γ^ν_{x,a}` on `[a, b]`, and the explored
regions coincide. -/
theorem cyc_locality (hν : Good ν) (hν' : Good ν') (x : Fin d → ℤ) {a b : ℝ} (hab : a ≤ b)
    (h : ν.restrict (cycRegion β (fwdTraj hν x a) a b) =
      ν'.restrict (cycRegion β (fwdTraj hν x a) a b)) :
    (∀ t ∈ Icc a b, fwdTraj hν' x a t = fwdTraj hν x a t) ∧
      cycRegion β (fwdTraj hν' x a) a b = cycRegion β (fwdTraj hν x a) a b := by
  have hf := fwdTraj_isPathOn hν x a b
  have hf' : IsPathOn ν' a b (fwdTraj hν x a) := by
    refine ⟨hf.1, hf.2.1, hf.2.2.1, fun t ht z hz => ?_⟩
    have hsw := hf.2.2.2 t ht z hz
    have hreg : ∀ e : Edge d, e.Mem z →
        ((e, (t : AddCircle β)) : RingSpace d β) ∈ cycRegion β (fwdTraj hν x a) a b :=
      fun e he => ⟨t, ht.1, ht.2, rfl, z, hz, he⟩
    refine ⟨fun e he hr => hsw.1 e he ((rings_iff_of_restrict_eq h (hreg e he)).mpr hr),
      fun hn => hsw.2 fun ⟨e, he, hr⟩ => hn ⟨e, he, (rings_iff_of_restrict_eq h (hreg e he)).mp hr⟩⟩
  have heq := fwdTraj_eq_of_isPathOn hν' (x := x) hab hf' (fwdTraj_self hν x a)
  refine ⟨fun t ht => (heq t ht).symm, ?_⟩
  exact cycRegion_congr (fun t ht => (heq t ht).symm)

theorem norm_le_one_of_mem_edge {e : Edge d} {z z' : Fin d → ℤ} (hz : e.Mem z) (hz' : e.Mem z') :
    ‖z - z'‖ ≤ 1 := by
  obtain ⟨u, v, huv, hadj⟩ := e.2
  have hz2 : z ∈ e.1 := hz
  have hz2' : z' ∈ e.1 := hz'
  rw [huv, Sym2.mem_iff] at hz2 hz2'
  have hb : ‖u - v‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have : |u i - v i| ≤ 1 := by
      rw [← hadj]
      exact Finset.single_le_sum (f := fun i => |u i - v i|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    simpa [Int.norm_eq_abs] using (by exact_mod_cast this : ((|u i - v i| : ℤ) : ℝ) ≤ 1)
  have hvu : ‖v - u‖ ≤ 1 := by rwa [norm_sub_rev]
  rcases hz2 with rfl | rfl <;> rcases hz2' with rfl | rfl
  · simp
  · exact hb
  · exact hvu
  · simp

omit [Fact (0 < β)] in
/-- Separation gives disjoint regions. Separated left limits at times differing by a multiple of
`β` give disjoint explored regions. -/
theorem cyc_disjoint (f : ℝ → Fin d → ℤ) {a b c d' : ℝ}
    (h : ∀ s ∈ Ioc c d', ∀ s' ∈ Ioc a b, ∀ z z' : Fin d → ℤ, IsLeftLimitAbove c f s z →
      IsLeftLimitAbove a f s' z' → (∃ k : ℤ, s - s' = k * β) → 2 ≤ ‖z - z'‖) :
    Disjoint (cycRegion β f c d') (cycRegion β f a b) := by
  refine Set.disjoint_left.mpr fun p hp hp' => ?_
  obtain ⟨s, hs1, hs2, hs3, z, hz, hm⟩ := hp
  obtain ⟨s', hs1', hs2', hs3', z', hz', hm'⟩ := hp'
  have hcirc : ((s - s' : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub, ← hs3, ← hs3', sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp hcirc
  have h2 := h s ⟨hs1, hs2⟩ s' ⟨hs1', hs2'⟩ z z' hz hz' ⟨k, by rw [← hk]; simp⟩
  have h1 := norm_le_one_of_mem_edge hm hm'
  linarith

end ElboimSly.Cyclic

end
