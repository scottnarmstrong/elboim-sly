/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodLocalMeas
public import ElboimSly.Paper.Heavy.LocalFunction
public import ElboimSly.Paper.Heavy.Claim69Aux
public import ElboimSly.Foundations.Interchange.GoodAs

/-!
# Goodness of blocks: independence at distance

Goodness is local; independence at distance (c) and (d) (ES22 §6).

* `disjoint_heavyBlockRegion`: if the indices of two blocks of `ℬ_k` are at `ℓ^∞`-distance at least
  `17`, then `A_B ∩ A_{B'} = ∅`.
* `exists_measurableSet_heavyBlockGood` (c): for `N ~ PPP(μ_β)`, there is a measurable set `G` of
  measures with `{B good for N} = {N|_{A_B} ∈ G}` almost surely.
* `heavyBlockBad_indep` (d): for a finite family of blocks whose indices are pairwise at distance
  `≥ 17`, the events `{B bad for N}` are independent.  This is exactly the hypothesis `hindep` of
  `es6_six_of_blockprob`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Every edge has a vertex. -/
theorem exists_mem_edge (e : Edge d) : ∃ z, e.Mem z := by
  obtain ⟨s, u, v, rfl, -⟩ := e
  exact ⟨u, Sym2.mem_mk_left u v⟩

theorem mem_heavyBlock_bounds {k : ℕ} {ι x : Fin d → ℤ} (h : x ∈ heavyBlock k ι) (c : Fin d) :
    (2 : ℤ) ^ k * ι c ≤ x c ∧ x c < (2 : ℤ) ^ k * ι c + 2 ^ k := by
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  have h1 := Int.emod_add_mul_ediv (x c) (2 ^ k)
  have h3 := Int.emod_nonneg (x c) hp.ne'
  have h4 := Int.emod_lt_of_pos (x c) hp
  have e : x c / 2 ^ k = ι c := h c
  rw [e] at h1
  constructor <;> linarith

theorem abs_sub_le_of_latDist {k : ℕ} {ι z : Fin d → ℤ}
    (h : latDist z (heavyBlock k ι) ≤ (2 : ℝ) ^ (k + 3)) :
    ∃ a ∈ heavyBlock k ι, ∀ c, |z c - a c| ≤ 8 * 2 ^ k := by
  have h' : latDist z (heavyBlock k ι) ≤ ((2 ^ (k + 3) : ℕ) : ℝ) := by
    push_cast; exact h
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (heavyBlock_nonempty k ι) h'
  refine ⟨a, haB, fun c => ?_⟩
  have h1 : ((|z c - a c| : ℤ) : ℝ) ≤ ((2 ^ (k + 3) : ℕ) : ℝ) := by
    have h2 : ‖(z - a) c‖ ≤ ‖z - a‖ := norm_le_pi_norm (z - a) c
    rw [Int.cast_abs]
    simpa [Int.norm_eq_abs] using h2.trans ha
  have h3 : |z c - a c| ≤ ((2 ^ (k + 3) : ℕ) : ℤ) := by exact_mod_cast h1
  have e : ((2 ^ (k + 3) : ℕ) : ℤ) = 8 * 2 ^ k := by push_cast; ring
  rwa [e] at h3

theorem disjoint_heavyBlockRegion (k : ℕ) {ι ι' : Fin d → ℤ}
    (h : ∃ c, (17 : ℤ) ≤ |ι c - ι' c|) :
    Disjoint (heavyBlockRegion d β k ι) (heavyBlockRegion d β k ι') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨z, hz⟩ := exists_mem_edge p.1
  obtain ⟨a, haB, ha⟩ := abs_sub_le_of_latDist (hp z hz)
  obtain ⟨a', ha'B, ha'⟩ := abs_sub_le_of_latDist (hp' z hz)
  obtain ⟨c, hc⟩ := h
  have hP : (0 : ℤ) < 2 ^ k := by positivity
  obtain ⟨b1, b2⟩ := mem_heavyBlock_bounds haB c
  obtain ⟨b3, b4⟩ := mem_heavyBlock_bounds ha'B c
  have e1 := abs_le.1 (ha c)
  have e2 := abs_le.1 (ha' c)
  rcases le_abs'.1 hc with h1 | h1
  · have : (2 : ℤ) ^ k * (-17) ≥ (2 : ℤ) ^ k * (ι c - ι' c) := mul_le_mul_of_nonneg_left h1 hP.le
    nlinarith
  · have : (2 : ℤ) ^ k * 17 ≤ (2 : ℤ) ^ k * (ι c - ι' c) := mul_le_mul_of_nonneg_left h1 hP.le
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (RingSpace d β)}

/-- Goodness is local; independence at distance (c). -/
theorem exists_measurableSet_heavyBlockGood
    (hN : IsPoissonPointProcess N (ringIntensity d β) P) (t₀ : ℝ) (n : ℕ) (ι : Fin d → ℤ) :
    ∃ G : Set (Measure (RingSpace d β)), MeasurableSet G ∧
      ∀ᵐ ω ∂P, ((Good (N ω) ∧ HeavyBlockGood d β t₀ n (N ω) ι) ↔
        (N ω).restrict (heavyBlockRegion d β (heavyLevel d n) ι) ∈ G) := by
  refine exists_measurable_set_of_local (A := heavyBlockRegion d β (heavyLevel d n) ι) (F :=
    {ν | Good ν ∧ HeavyBlockGood d β t₀ n ν ι}) (Gd := {ν | Good ν}) hN
    (measurableSet_heavyBlockRegion _ _) (measurableSet_good_and_heavyBlockGood t₀ n ι)
    Cyclic.measurableSet_good (Interchange.ae_good hN) ?_
  intro ν hν ν' hν' h
  simp only [mem_ofPred_eq] at hν hν' ⊢
  exact ⟨fun ⟨_, hg⟩ => ⟨hν', (heavyBlockGood_iff_of_restrict_eq hν hν' h).1 hg⟩,
    fun ⟨_, hg⟩ => ⟨hν, (heavyBlockGood_iff_of_restrict_eq hν hν' h).2 hg⟩⟩

/-- Goodness is local; independence at distance (d). For a finite family of blocks of `ℬ_k` whose indices are
pairwise at `ℓ^∞`-distance at least `17`, the events `{B bad for N}` are independent. -/
theorem heavyBlockBad_indep (hN : IsPoissonPointProcess N (ringIntensity d β) P) (t₀ : ℝ) (n : ℕ)
    (𝒜 : Finset (Fin d → ℤ))
    (hsep : ∀ x ∈ 𝒜, ∀ y ∈ 𝒜, x ≠ y → ∃ c, (17 : ℤ) ≤ |x c - y c|) :
    P (⋂ ι ∈ 𝒜, {ω | HeavyBlockBad d β t₀ n (N ω) ι}) =
      ∏ ι ∈ 𝒜, P {ω | HeavyBlockBad d β t₀ n (N ω) ι} := by
  classical
  choose! G hGm hG using fun ι => exists_measurableSet_heavyBlockGood hN t₀ n ι
  set k := heavyLevel d n with hk
  let A : 𝒜 → Set (RingSpace d β) := fun ι => heavyBlockRegion d β k ι
  have hind : iIndepFun (fun (ι : 𝒜) ω => (N ω).restrict (A ι)) P :=
    hN.iIndepFun_restrict (A := A) (fun ι => measurableSet_heavyBlockRegion _ _) (by
      intro i j hij
      exact disjoint_heavyBlockRegion k (hsep i i.2 j j.2 (fun h => hij (Subtype.ext h))))
  have hbad : ∀ ι : 𝒜, {ω | HeavyBlockBad d β t₀ n (N ω) ι} =ᵐ[P]
      (fun ω => (N ω).restrict (A ι)) ⁻¹' (G ι)ᶜ := by
    intro ι
    filter_upwards [hG ι, Interchange.ae_good hN] with ω h1 h2
    simp only [HeavyBlockBad, eq_iff_iff, mem_preimage, mem_compl_iff]
    rw [← h1]
    simp [h2]
  have hmeas : ∀ ι : 𝒜, MeasurableSet ((G ι)ᶜ) := fun ι => (hGm ι).compl
  have key := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hind) (Finset.univ : Finset 𝒜)
    (sets := fun ι => (G ι)ᶜ) (fun ι _ => hmeas ι)
  have e1 : P (⋂ ι ∈ 𝒜, {ω | HeavyBlockBad d β t₀ n (N ω) ι}) =
      P (⋂ ι ∈ (Finset.univ : Finset 𝒜), (fun ω => (N ω).restrict (A ι)) ⁻¹' (G ι)ᶜ) := by
    refine measure_congr ?_
    have : ∀ᵐ ω ∂P, ∀ ι : 𝒜, (ω ∈ {ω | HeavyBlockBad d β t₀ n (N ω) ι} ↔
        ω ∈ (fun ω => (N ω).restrict (A ι)) ⁻¹' (G ι)ᶜ) :=
      ae_all_iff.2 fun ι => Filter.eventuallyEqSet_iff.1 (hbad ι)
    filter_upwards [this] with ω hω
    simp only [eq_iff_iff, mem_iInter, Finset.mem_univ, true_implies]
    constructor
    · intro h ι
      exact (hω ι).1 (h ι ι.2)
    · intro h ι hι
      exact (hω ⟨ι, hι⟩).2 (h ⟨ι, hι⟩)
  rw [e1, key]
  have e2 : ∀ ι : 𝒜, P ((fun ω => (N ω).restrict (A ι)) ⁻¹' (G ι)ᶜ) =
      P {ω | HeavyBlockBad d β t₀ n (N ω) ι} := fun ι => (measure_congr (hbad ι)).symm
  simp_rw [e2]
  exact Finset.prod_coe_sort 𝒜 fun ι => P {ω | HeavyBlockBad d β t₀ n (N ω) ι}

end ElboimSly.Paper.Heavy
