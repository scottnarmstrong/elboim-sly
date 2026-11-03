/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodBlocks
public import ElboimSly.Paper.Heavy.NoFast
public import ElboimSly.Foundations.Cyclic.CycRegion
public import ElboimSly.Foundations.Cyclic.CycWalkTraj

/-!
# Goodness of a block is local

Goodness is local; independence at distance (b) (ES22 §6).

* `heavyBlockRegion d β k ι`: the set `A_B = E_B × 𝕋` of ring points whose edge has both endpoints
  in `N(B, 2^{k+3})`.
* `cycRegion_subset_heavyBlockRegion`: while the walk from `u ∈ N(B, 2^{k+2})` stays within `2^{k-1}`
  of `u`, its explored region lies in `A_B`.
* `cycWalk_eq_of_restrict_eq`: if two good environments agree on `A_B` and the walk from `(u, q)`
  satisfies (GB2) for the first, the two walks coincide on `[0, t'_k]`.
* `heavyBlockGood_iff_of_restrict_eq`: for good `ν, ν'` agreeing on `A_B`, `B` is good for `ν` iff
  it is good for `ν'`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Goodness is local; independence at distance. `A_B = E_B × 𝕋`, where `E_B` is the set of edges with both
endpoints in `N(B, 2^{k+3})`. -/
def heavyBlockRegion (d : ℕ) (β : ℝ) [Fact (0 < β)] (k : ℕ) (ι : Fin d → ℤ) :
    Set (RingSpace d β) :=
  {p | ∀ z, p.1.Mem z → z ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 3))}

theorem pow_bound_aux (k : ℕ) : (2 : ℝ) ^ (k + 2) + (2 : ℝ) ^ (k - 1) + 1 ≤ (2 : ℝ) ^ (k + 3) := by
  have h1 : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h3 : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by ring
  have h4 : (2 : ℝ) ^ (k + 3) = 8 * 2 ^ k := by ring
  rw [h3, h4]
  linarith

theorem cycRegion_subset_heavyBlockRegion {ν : Measure (RingSpace d β)} (hν : Good ν)
    {k : ℕ} {ι : Fin d → ℤ} {u : Fin d → ℤ} {q s : ℝ}
    (hu : u ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)))
    (hb : ∀ r ∈ Ico q (q + s), ‖fwdTraj hν u q r - u‖ ≤ (2 : ℝ) ^ (k - 1)) :
    cycRegion β (fwdTraj hν u q) q (q + s) ⊆ heavyBlockRegion d β k ι := by
  rintro p ⟨t, h1, h2, -, z, hz, hm⟩ z' hz'
  have hne : (Ioo q t).Nonempty := ⟨(q + t) / 2, by constructor <;> linarith⟩
  obtain ⟨u', hu'1, hu'2⟩ := (hz.and (Ioo_mem_nhdsLT h1)).exists
  have hzz : fwdTraj hν u q u' = z := hu'1 hu'2.1
  have hz1 : ‖z - u‖ ≤ (2 : ℝ) ^ (k - 1) := by
    rw [← hzz]; exact hb u' ⟨hu'2.1.le, by linarith [hu'2.2]⟩
  have hz2 : ‖z' - z‖ ≤ 1 := by
    have := norm_le_one_of_mem_edge hz' hm
    exact this
  have hzu : ‖z' - u‖ ≤ (2 : ℝ) ^ (k - 1) + 1 := by
    calc ‖z' - u‖ = ‖(z' - z) + (z - u)‖ := by congr 1; abel
      _ ≤ ‖z' - z‖ + ‖z - u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hB := heavyBlock_nonempty (d := d) k ι
  have := latDist_le_add hB z' u
  have hu2 : latDist u (heavyBlock k ι) ≤ (2 : ℝ) ^ (k + 2) := hu
  have := pow_bound_aux k
  show latDist z' (heavyBlock k ι) ≤ (2 : ℝ) ^ (k + 3)
  linarith [latDist_le_add hB z' u]

theorem measurableSet_heavyBlockRegion (k : ℕ) (ι : Fin d → ℤ) :
    MeasurableSet (heavyBlockRegion d β k ι) := by
  have : heavyBlockRegion d β k ι =
      Prod.fst ⁻¹' {e : Edge d | ∀ z, e.Mem z → z ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 3))} :=
    rfl
  rw [this]
  exact measurable_fst (MeasurableSet.of_discrete)

/-- If `ν, ν'` are good and agree on `A_B`, and the walk from `(u, q)` satisfies (GB2) for `ν`,
then the walks coincide on `[0, t'_k]`. -/
theorem cycWalk_eq_of_restrict_eq {ν ν' : Measure (RingSpace d β)} (hν : Good ν) (hν' : Good ν')
    {k : ℕ} {ι : Fin d → ℤ} (h : ν.restrict (heavyBlockRegion d β k ι) =
      ν'.restrict (heavyBlockRegion d β k ι))
    {u : Fin d → ℤ} (hu : u ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2))) {q tk : ℝ}
    (hb : ∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν u q s - u‖ ≤ (2 : ℝ) ^ (k - 1)) :
    ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u q s = cycWalk ν u q s := by
  intro s hs
  have htk : 0 ≤ tk := hs.1.trans hs.2
  have hsub := cycRegion_subset_heavyBlockRegion hν (q := q) (s := tk) hu (fun r hr => by
    have := hb (r - q) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rwa [cycWalk_of_nonneg hν u q (by linarith [hr.1]), show q + (r - q) = r by ring] at this)
  have hres : ν.restrict (cycRegion β (fwdTraj hν u q) q (q + tk)) =
      ν'.restrict (cycRegion β (fwdTraj hν u q) q (q + tk)) := by
    rw [← Measure.restrict_restrict_of_subset hsub (μ := ν),
      ← Measure.restrict_restrict_of_subset hsub (μ := ν'), h]
  obtain ⟨hloc, -⟩ := cyc_locality hν hν' u (by linarith : q ≤ q + tk) hres
  rw [cycWalk_of_nonneg hν' u q hs.1, cycWalk_of_nonneg hν u q hs.1]
  exact hloc (q + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩

omit [Fact (0 < β)] in
theorem isRelaxedTimeWrt_congr_Icc {w w' : ℝ → Fin d → ℤ} {a t : ℝ} (hβ : 0 < β) (hat : a ≤ t)
    (h : ∀ s ∈ Icc a t, w s = w' s) :
    IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' a t := by
  have hv : visitedSet w a t = visitedSet w' a t := Set.image_congr h
  have ht : w t = w' t := h t ⟨hat, le_rfl⟩
  have hb : 0 ≤ β ^ (3 * indDelta d) := (Real.rpow_pos_of_pos hβ _).le
  unfold IsRelaxedTimeWrt IsHeavy
  simp only [hv, ht]
  refine and_congr Iff.rfl (forall_congr' fun s => ?_)
  by_cases hs : a ≤ s
  · simp only [hs, true_implies]
    refine imp_congr_right fun hst => ?_
    rw [h s ⟨hs, by linarith⟩]
  · simp [hs]


theorem cycClosesBy_congr {ν ν' : Measure (RingSpace d β)} {tk : ℝ}
    {u : Fin d → ℤ} {q : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u q s = cycWalk ν u q s) :
    cycClosesBy ν' u q tk ↔ cycClosesBy ν u q tk := by
  have hβ : 0 < β := Fact.out
  have hm0 : ∀ m : ℕ, (m : ℝ) * β ≤ tk → (m : ℝ) * β ∈ Icc (0 : ℝ) tk :=
    fun m hm => ⟨by positivity, hm⟩
  constructor
  · rintro ⟨m, hm1, hm2, e⟩
    exact ⟨m, hm1, hm2, (h _ (hm0 m hm2)).symm.trans e⟩
  · rintro ⟨m, hm1, hm2, e⟩
    exact ⟨m, hm1, hm2, (h _ (hm0 m hm2)).trans e⟩

omit [Fact (0 < β)] in
theorem cycMerges_congr {ν ν' : Measure (RingSpace d β)} {tk : ℝ}
    {u₁ u₂ : Fin d → ℤ} {q₁ q₂ : ℝ}
    (h1 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₁ q₁ s = cycWalk ν u₁ q₁ s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₂ q₂ s = cycWalk ν u₂ q₂ s) :
    cycMerges ν' u₁ u₂ q₁ q₂ tk ↔ cycMerges ν u₁ u₂ q₁ q₂ tk := by
  constructor
  · rintro ⟨s₁, s₂, hs₁, hs₂, hk, e⟩
    exact ⟨s₁, s₂, hs₁, hs₂, hk, by rw [← h1 s₁ hs₁, ← h2 s₂ hs₂]; exact e⟩
  · rintro ⟨s₁, s₂, hs₁, hs₂, hk, e⟩
    exact ⟨s₁, s₂, hs₁, hs₂, hk, by rw [h1 s₁ hs₁, h2 s₂ hs₂]; exact e⟩

theorem cycOmega_congr {ν ν' : Measure (RingSpace d β)} {tk : ℝ}
    {u₁ u₂ : Fin d → ℤ} {q₁ q₂ : ℝ}
    (h1 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₁ q₁ s = cycWalk ν u₁ q₁ s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₂ q₂ s = cycWalk ν u₂ q₂ s) :
    cycOmega ν' u₁ u₂ q₁ q₂ tk ↔ cycOmega ν u₁ u₂ q₁ q₂ tk := by
  unfold cycOmega
  rw [cycMerges_congr h1 h2, cycClosesBy_congr h1, cycClosesBy_congr h2]

theorem relaxedSet_congr {ν ν' : Measure (RingSpace d β)} {tk : ℝ}
    {u : Fin d → ℤ} {q : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u q s = cycWalk ν u q s) :
    {s : ℝ | s ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν' u q r) 0 s} =
      {s : ℝ | s ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν u q r) 0 s} := by
  have hβ : 0 < β := Fact.out
  ext s
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hs => ?_
  exact isRelaxedTimeWrt_congr_Icc hβ hs.1 fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩

omit [Fact (0 < β)] in
theorem proxSet_congr {ν ν' : Measure (RingSpace d β)} {tk ρ : ℝ}
    {u₁ u₂ : Fin d → ℤ} {q₁ q₂ : ℝ}
    (h1 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₁ q₁ s = cycWalk ν u₁ q₁ s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) tk, cycWalk ν' u₂ q₂ s = cycWalk ν u₂ q₂ s) :
    {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk ν' u₁ q₁ s₁ - cycWalk ν' u₂ q₂ s₂‖ ≤ ρ} =
      {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk ν u₁ q₁ s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ ρ} := by
  ext s₂
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hs₂, s₁, hs₁, hle⟩
    exact ⟨hs₂, s₁, hs₁, by rwa [← h1 s₁ hs₁, ← h2 s₂ hs₂]⟩
  · rintro ⟨hs₂, s₁, hs₁, hle⟩
    exact ⟨hs₂, s₁, hs₁, by rwa [h1 s₁ hs₁, h2 s₂ hs₂]⟩

theorem heavyBlockGood_of_restrict_eq {ν ν' : Measure (RingSpace d β)} (hν : Good ν)
    (hν' : Good ν') {t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ}
    (h : ν.restrict (heavyBlockRegion d β (heavyLevel d n) ι) =
      ν'.restrict (heavyBlockRegion d β (heavyLevel d n) ι))
    (hg : HeavyBlockGood d β t₀ n ν ι) : HeavyBlockGood d β t₀ n ν' ι := by
  simp only [HeavyBlockGood] at hg ⊢
  intro u₁ hu₁ u₂ hu₂ q₁ q₂ hq₁ hq₁' hq₂ hq₂'
  have hb₁ := (hg u₁ hu₁ u₁ hu₁ q₁ q₁ hq₁ hq₁' hq₁ hq₁').2.1
  have hb₂ := (hg u₂ hu₂ u₂ hu₂ q₂ q₂ hq₂ hq₂' hq₂ hq₂').2.1
  have e₁ := cycWalk_eq_of_restrict_eq hν hν' h hu₁ hb₁
  have e₂ := cycWalk_eq_of_restrict_eq hν hν' h hu₂ hb₂
  obtain ⟨g1, g2, g3⟩ := hg u₁ hu₁ u₂ hu₂ q₁ q₂ hq₁ hq₁' hq₂ hq₂'
  refine ⟨?_, fun s hs => ?_, fun hΩ => ?_⟩
  · rcases g1 with c | v
    · exact Or.inl ((cycClosesBy_congr e₁).2 c)
    · exact Or.inr (by rw [relaxedSet_congr e₁]; exact v)
  · rw [e₁ s hs]; exact g2 s hs
  · rw [cycOmega_congr e₁ e₂] at hΩ
    rw [proxSet_congr e₁ e₂]
    exact g3 hΩ

/-- Goodness is local; independence at distance (b). If `ν, ν'` are good and agree on `A_B`, then `B` is good
for `ν` iff it is good for `ν'`. -/
theorem heavyBlockGood_iff_of_restrict_eq {ν ν' : Measure (RingSpace d β)} (hν : Good ν)
    (hν' : Good ν') {t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ}
    (h : ν.restrict (heavyBlockRegion d β (heavyLevel d n) ι) =
      ν'.restrict (heavyBlockRegion d β (heavyLevel d n) ι)) :
    HeavyBlockGood d β t₀ n ν ι ↔ HeavyBlockGood d β t₀ n ν' ι :=
  ⟨heavyBlockGood_of_restrict_eq hν hν' h, heavyBlockGood_of_restrict_eq hν' hν h.symm⟩

end ElboimSly.Paper.Heavy
