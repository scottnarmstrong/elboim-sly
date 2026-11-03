/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.EscInterface
public import ElboimSly.Paper.Heavy.MeasStop
public import Mathlib

/-!
# Measurability of the escape events

The escape event ("it is an event"), used in ES22 Lemma 6.2 Step 0.

For an adapted family of cyclic paths `W` and a measurable random time `ξ`, the escape event
`ℰ(ξ) = {ξ < ∞} ∩ {∀ s ∈ [4^j, 4^n], ‖W(ξ+s) - W(ξ)‖ ≥ √s/n}` is measurable.

* `escEvent_of_rational`: for a cyclic path it suffices to check rational `s` and `s = 4^n`.
* `measurableSet_walk_pair_at`: `{(W(τ + s), W(τ)) ∈ P}` is measurable for measurable `τ ≥ 0`
  (dyadic approximation from the right, using right-continuity).
* `measurableSet_heavyEscSet`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem escEvent_of_rational {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {n j : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ q : ℚ, (4 : ℝ) ^ j ≤ q → (q : ℝ) < 4 ^ n →
      Real.sqrt q / n ≤ ‖w (T + q) - w T‖)
    (hb : (4 : ℝ) ^ j ≤ 4 ^ n → Real.sqrt ((4 : ℝ) ^ n) / n ≤ ‖w (T + 4 ^ n) - w T‖) :
    EscEvent n j w T := by
  intro s hs1 hs2
  rcases hs2.eq_or_lt with rfl | hlt
  · exact hb hs1
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ s := (by positivity : (0 : ℝ) ≤ 4 ^ j).trans hs1
  set δ : ℝ := Real.sqrt s / n - ‖w (T + s) - w T‖ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc (T + s) (by linarith))
  have hcont : ContinuousAt (fun x : ℝ => Real.sqrt x / n) s :=
    (Real.continuous_sqrt.div_const _).continuousAt
  obtain ⟨η, hη, hηball⟩ := Metric.continuousAt_iff.1 hcont (δ / 2) (by linarith)
  have hu' : T + s < u := hu
  have hpos : 0 < min η (min (u - (T + s)) ((4 : ℝ) ^ n - s)) :=
    lt_min hη (lt_min (by linarith) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + min η (min (u - (T + s)) ((4 : ℝ) ^ n - s))
    by linarith)
  have hqη : (q : ℝ) < s + η := hq2.trans_le (by linarith [min_le_left η (min (u - (T + s)) ((4 : ℝ) ^ n - s))])
  have hqu : (q : ℝ) < s + (u - (T + s)) := hq2.trans_le (by
    linarith [(min_le_right η (min (u - (T + s)) ((4 : ℝ) ^ n - s))).trans
      (min_le_left (u - (T + s)) ((4 : ℝ) ^ n - s))])
  have hq4 : (q : ℝ) < 4 ^ n := hq2.trans_le (by
    linarith [(min_le_right η (min (u - (T + s)) ((4 : ℝ) ^ n - s))).trans
      (min_le_right (u - (T + s)) ((4 : ℝ) ^ n - s))])
  have hwq : w (T + q) = w (T + s) := hsub ⟨by linarith, by linarith⟩
  have h1 := hq q (by linarith) hq4
  rw [hwq] at h1
  have hd : dist (Real.sqrt q / n) (Real.sqrt s / n) < δ / 2 := hηball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at hd
  linarith [hd.1]

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {f : Filtration ℝ≥0 m0} {W : Ω → ℝ → Fin d → ℤ}

theorem measurable_walk_pair (hAd : AdaptedCyclic f W) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Measurable (fun ω => (W ω x, W ω y)) := by
  have h : ∀ {z : ℝ}, 0 ≤ z → Measurable (fun ω => W ω z) := fun {z} hz =>
    (hAd.measurable_at hz (t := z.toNNReal) (by rw [Real.coe_toNNReal z hz])).mono
      (f.le _) le_rfl
  exact (h hx).prodMk (h hy)

/-- The dyadic approximation `⌈2^k t⌉ / 2^k ≥ t` from the right. -/
noncomputable def dyadicUp (t : ℝ) (k : ℕ) : ℝ := (⌈(2 : ℝ) ^ k * t⌉₊ : ℝ) / 2 ^ k

theorem le_dyadicUp {t : ℝ} (_ht : 0 ≤ t) (k : ℕ) : t ≤ dyadicUp t k := by
  unfold dyadicUp
  rw [le_div_iff₀ (by positivity)]
  have := Nat.le_ceil ((2 : ℝ) ^ k * t)
  linarith

theorem dyadicUp_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : dyadicUp t k ≤ t + 1 / 2 ^ k := by
  unfold dyadicUp
  rw [div_le_iff₀ (by positivity)]
  have := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ k * t by positivity)
  rw [add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  linarith

theorem tendsto_dyadicUp {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    Tendsto (fun k => dyadicUp t k + c) atTop (𝓝[≥] (t + c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun k => ?_⟩
  · have h0 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 : Tendsto (fun k : ℕ => t + c + (1 / 2 : ℝ) ^ k) atTop (𝓝 (t + c + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => ?_)
      (fun k => ?_)
    · have := le_dyadicUp ht k; simp only; linarith
    · have := dyadicUp_le ht k
      have e : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [one_div_pow]
      simp only; rw [e]; linarith
  · have := le_dyadicUp ht k
    simp only [mem_Ici]; linarith

theorem measurableSet_walk_pair_at (hAd : AdaptedCyclic f W) {τ : Ω → ℝ} (hτ : Measurable τ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) {s : ℝ} (hs : 0 ≤ s) (P : Set ((Fin d → ℤ) × (Fin d → ℤ))) :
    MeasurableSet {ω | (W ω (τ ω + s), W ω (τ ω)) ∈ P} := by
  set Z : ℕ → Set Ω := fun k => {ω | (W ω (dyadicUp (τ ω) k + s), W ω (dyadicUp (τ ω) k)) ∈ P}
    with hZ
  have hZm : ∀ k, MeasurableSet (Z k) := by
    intro k
    have : Z k = ⋃ a : ℕ, {ω | ⌈(2 : ℝ) ^ k * τ ω⌉₊ = a} ∩
        {ω | (W ω ((a : ℝ) / 2 ^ k + s), W ω ((a : ℝ) / 2 ^ k)) ∈ P} := by
      ext ω
      simp only [hZ, mem_ofPred_eq, mem_iUnion, mem_inter_iff, dyadicUp]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨a, ha, h⟩; rw [ha]; exact h
    rw [this]
    refine MeasurableSet.iUnion fun a => MeasurableSet.inter ?_ ?_
    · exact (Nat.measurable_ceil.comp (measurable_const.mul hτ)) (measurableSet_singleton a)
    · exact (measurable_walk_pair hAd (by positivity) (by positivity))
        (P.to_countable.measurableSet)
  have heq : {ω | (W ω (τ ω + s), W ω (τ ω)) ∈ P} = ⋃ k0 : ℕ, ⋂ k ≥ k0, Z k := by
    ext ω
    have hev : ∀ᶠ k in atTop, (W ω (dyadicUp (τ ω) k + s), W ω (dyadicUp (τ ω) k)) =
        (W ω (τ ω + s), W ω (τ ω)) := by
      have h1 := ((hAd.path ω).rc (τ ω + s) (by linarith [hτ0 ω])).filter_mono le_rfl
      have h2 := ((hAd.path ω).rc (τ ω + 0) (by linarith [hτ0 ω]))
      have e1 := (tendsto_dyadicUp (hτ0 ω) s).eventually h1
      have e2 := (tendsto_dyadicUp (hτ0 ω) 0).eventually h2
      filter_upwards [e1, e2] with k hk1 hk2
      simp only [add_zero] at hk2
      rw [hk1, hk2]
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, hZ]
    constructor
    · intro h
      obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
      exact ⟨k0, fun k hk => by rw [hk0 k hk]; exact h⟩
    · rintro ⟨k0, hk0⟩
      obtain ⟨k1, hk1⟩ := eventually_atTop.1 hev
      have := hk0 (max k0 k1) (le_max_left _ _)
      rwa [hk1 (max k0 k1) (le_max_right _ _)] at this
  rw [heq]
  exact MeasurableSet.iUnion fun k0 => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hZm k

/-- The escape event, measurability. -/
theorem measurableSet_heavyEscSet (hAd : AdaptedCyclic f W) {ξ : Ω → ℝ≥0∞} (hξ : Measurable ξ)
    {n : ℕ} (hn : 0 < n) (j : ℕ) : MeasurableSet (heavyEscSet W n j ξ) := by
  classical
  set τ : Ω → ℝ := fun ω => (ξ ω).toReal with hτ
  have hτm : Measurable τ := ENNReal.measurable_toReal.comp hξ
  have hτ0 : ∀ ω, 0 ≤ τ ω := fun ω => ENNReal.toReal_nonneg
  have hfin : MeasurableSet {ω | ξ ω ≠ ⊤} := (measurableSet_singleton ⊤).compl.preimage hξ
  let A : ℝ → Set Ω := fun s => {ω | (W ω (τ ω + s), W ω (τ ω)) ∈
    {p : (Fin d → ℤ) × (Fin d → ℤ) | Real.sqrt s / n ≤ ‖p.1 - p.2‖}}
  have hA : ∀ s, 0 ≤ s → MeasurableSet (A s) := fun s hs =>
    measurableSet_walk_pair_at hAd hτm hτ0 hs _
  have hset : heavyEscSet W n j ξ = {ω | ξ ω ≠ ⊤} ∩ {ω | EscEvent n j (W ω) (τ ω)} := rfl
  rw [hset]
  refine hfin.inter ?_
  by_cases hab : (4 : ℝ) ^ j ≤ 4 ^ n
  · have e : {ω | EscEvent n j (W ω) (τ ω)} =
        (⋂ q : ℚ, ⋂ (_ : (4 : ℝ) ^ j ≤ q ∧ (q : ℝ) < 4 ^ n), A q) ∩ A ((4 : ℝ) ^ n) := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, A]
      constructor
      · intro h
        exact ⟨fun q hq => h q hq.1 hq.2.le, h _ hab le_rfl⟩
      · rintro ⟨h1, h2⟩
        exact escEvent_of_rational (hAd.path ω) hn (hτ0 ω)
          (fun q h3 h4 => h1 q ⟨h3, h4⟩) (fun _ => h2)
    rw [e]
    refine MeasurableSet.inter (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
      (hA _ (by positivity))
    exact hA q ((by positivity : (0 : ℝ) ≤ 4 ^ j).trans hq.1)
  · have e : {ω | EscEvent n j (W ω) (τ ω)} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro s h1 h2
      exact absurd (h1.trans h2) hab
    rw [e]; exact MeasurableSet.univ

end ElboimSly.Paper.Heavy
