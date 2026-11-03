/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Sets
public import ElboimSly.Paper.Step.Lemma78Incl
public import ElboimSly.Paper.Step.Lemma78Closing
public import Mathlib

/-!
# The reduction to events of `W'_i` (pathwise)

One excursion succeeds with probability at least frac12, "Reduction to events of `W'_i`". On `{ζ_i < t'_n}` with
`ζ'_i < t'_n`, one of the following holds, for `x = W₂(ζ_i)`, `V = W₁([0,t'_n])` and the fresh walk
`y = W'_i` (which agrees with `W₂(ζ_i + ·) - W₂(ζ_i)` up to `b_i`):
`τ' < 4ⁿ`, or `y ∈ E_cl`, or `y ∈ E_V`, or `y ∈ E_far`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

namespace Step78Data

variable (D : Step78Data d Ω)

/-- `b = thit^{(2)}(ζ) ∧ treg^{(2)} ∧ inf {r ≥ ζ : d(W₂(r), V) ≤ 1}`. -/
noncomputable def bTime (Z : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (min (D.thit Z ω) (D.treg ω)) (step78FirstGe D.nearSet1 Z ω)

theorem zetaPP_eq (Z : Ω → WithTop ℝ≥0) (ω : Ω) :
    D.zetaPP Z ω = min (D.bTime Z ω)
      (step78FirstGe D.nearSet2 (fun ω => Z ω + (D.gap : WithTop ℝ≥0)) ω) := by
  unfold zetaPP bTime
  simp only [min_assoc]

end Step78Data

variable {D : Step78Data d Ω} {f : Filtration ℝ≥0 m}

/-- Rational times for a right-continuous path. -/
theorem grid_near {n : ℕ} {X : ℝ≥0 → Fin d → ℤ} (hX : ∀ s, ∀ᶠ u in 𝓝[≥] s, X u = X s)
    {s : ℝ≥0} (hs : (s : ℝ) < (4 : ℝ) ^ n) :
    ∃ g ∈ step78Grid, s ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n ∧ X g = X s := by
  have hb : s < ((4 : ℝ) ^ n).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]; exact hs
  obtain ⟨g, hg, h1, h2, h3⟩ := exists_grid_rc hX hb
  refine ⟨g, hg, h1, ?_, h3⟩
  have := (NNReal.coe_lt_coe.2 h2)
  rwa [Real.coe_toNNReal _ (by positivity)] at this

/-- If `W₂` closes at `kβ > ζ`, then `thit(ζ) ≤ kβ`. -/
theorem Step78Data.thit_le_closing (hC : Step78Closing D) (ω : Ω) {r : ℝ≥0} (hr : 0 < r)
    {k : ℕ} (hk1 : 1 ≤ k) (hkw : D.w ((k : ℝ) * D.β).toNNReal ω = D.u)
    (hrk : (r : ℝ) < k * D.β) (hβ : 0 < D.β) :
    stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) (r : ℝ) ≤
      ENNReal.ofReal ((k : ℝ) * D.β) := by
  by_contra h
  rw [not_le] at h
  obtain ⟨c, hc0, hc1, hc2⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
  have hc1' : (k : ℝ) * D.β < c := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hc1
  set s := min c ((k : ℝ) * D.β + r / 2) with hs
  have hs1 : (k : ℝ) * D.β < s := lt_min hc1' (by have : (0 : ℝ) < r := hr; linarith)
  have hs2 : s < (k : ℝ) * D.β + r := lt_of_le_of_lt (min_le_right _ _)
    (by have : (0 : ℝ) < r := hr; linarith)
  have hs3 : ENNReal.ofReal s < stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) (r : ℝ) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hc2
  have hmem : stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) (r : ℝ) ≤ ENNReal.ofReal s := by
    unfold stepThit
    refine iInf₂_le s ⟨by linarith, s - k * D.β, ⟨-(k : ℤ), by push_cast; ring⟩, ?_, ?_, ?_⟩
    · simp only [NNReal.coe_zero]; linarith
    · linarith
    · have hper := hC ω k hk1 hkw (s - k * D.β) (by linarith)
      rw [show s - k * D.β + k * D.β = s by ring] at hper
      rw [hper]; simp
  exact absurd hs3 (not_lt.2 hmem)

/-- The pointwise reduction. -/
theorem Step78Data.decomp (hF : Step78Frame D f) (hC : Step78Closing D) (_hρ : 1 < D.ρ)
    (hT4 : (D.T : ℝ) < (4 : ℝ) ^ D.n) (h0 : ∀ ω, D.w 0 ω = D.u) (ω : Ω) (i : ℕ) {r : ℝ≥0}
    (hz : D.zeta (i + 1) ω = r) (hrT : r < D.T) (hzp : D.zp (i + 1) ω < (D.T : WithTop ℝ≥0))
    {X : ℝ≥0 → Fin d → ℤ} (hX : ∀ s, ∀ᶠ u in 𝓝[≥] s, X u = X s)
    (hcpl : ∀ s : ℝ≥0, (r : WithTop ℝ≥0) + (s : WithTop ℝ≥0) ≤ D.bTime (D.zeta (i + 1)) ω →
      D.w (r + s) ω = D.w r ω + X s) :
    X ∈ step78Sbad d D.β D.n (D.w r ω) (D.V ω) ∨
      hitTime D.β (D.path ω) 0 (r : ℝ) (fun s => D.path ω (r : ℝ) + X s.toNNReal) <
        ENNReal.ofReal ((4 : ℝ) ^ D.n) := by
  have hhz : D.zeta (i + 1) ω < (D.T : WithTop ℝ≥0) := by
    rw [hz]; exact WithTop.coe_lt_coe.2 hrT
  obtain ⟨r0, hz0, hrel, hfar, hlt, -⟩ := D.zeta_succ_attained hF hC ω i hhz
  have hr0 : r0 = r := WithTop.coe_injective (hz0.symm.trans hz)
  rw [hr0] at hrel hfar hlt
  set Z := D.zeta (i + 1) with hZdef
  -- `zpp < T`
  have hzpp : D.zetaPP Z ω < (D.T : WithTop ℝ≥0) := by
    rw [D.zp_succ_eq ω i] at hzp
    have h2 := (max_lt_iff.1 hzp).2
    by_contra hge
    rw [not_lt] at hge
    rw [min_eq_left hge] at h2
    exact lt_irrefl _ h2
  rw [Step78Data.zetaPP_eq] at hzpp
  have hTr : (r : ℝ) < (4 : ℝ) ^ D.n := lt_trans (by exact_mod_cast hrT) hT4
  have hgapR : (D.gap : ℝ) = (389 / 100 : ℝ) ^ D.n := by
    simp only [Step78Data.gap]; exact Real.coe_toNNReal _ (by positivity)
  have hβ : 0 < D.β := by have := hF.hβ; linarith
  rcases le_total (step78FirstGe D.nearSet2 (fun ω => Z ω + (D.gap : WithTop ℝ≥0)) ω)
      (D.bTime Z ω) with h4 | hb4
  · -- the far event
    rw [min_eq_right h4] at hzpp
    have hfin : step78FirstGe D.nearSet2 (fun ω => Z ω + (D.gap : WithTop ℝ≥0)) ω < ⊤ :=
      lt_trans hzpp (WithTop.coe_lt_top _)
    obtain ⟨r4, hr4U, hRr4, hr4e⟩ := step78FirstGe_attained (locIco_near2 hF ω) hfin
    have hR : (r : WithTop ℝ≥0) + (D.gap : WithTop ℝ≥0) ≤ r4 := by
      have : Z ω + (D.gap : WithTop ℝ≥0) ≤ r4 := hRr4
      rwa [hz] at this
    have hgap : r + D.gap ≤ r4 := by
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hR; exact hR
    have hr4T : r4 < D.T := by
      have := hr4e ▸ hzpp
      exact WithTop.coe_lt_coe.1 this
    have hrr4 : r ≤ r4 := le_trans le_self_add hgap
    have hrs : r + (r4 - r) = r4 := add_tsub_cancel_of_le hrr4
    have hb : (r : WithTop ℝ≥0) + ((r4 - r : ℝ≥0) : WithTop ℝ≥0) ≤ D.bTime Z ω := by
      rw [← WithTop.coe_add, hrs, ← hr4e]; exact h4
    have hw := hcpl (r4 - r) hb
    rw [hrs] at hw
    obtain ⟨v, hv, hvn⟩ := hr4U
    rw [Step78Data.path_coe, hw] at hvn
    have hgs : D.gap ≤ r4 - r := le_tsub_of_add_le_left (hgap)
    have hs4 : ((r4 - r : ℝ≥0) : ℝ) < (4 : ℝ) ^ D.n := by
      have : r4 - r ≤ r4 := tsub_le_self
      exact lt_of_le_of_lt (by exact_mod_cast this) (lt_trans (by exact_mod_cast hr4T) hT4)
    obtain ⟨g, hg, hsg, hg4, hXg⟩ := grid_near hX hs4
    refine Or.inl (Or.inr ⟨g, hg, ?_, hg4, v, hv, ?_⟩)
    · rw [← hgapR]; exact_mod_cast hgs.trans hsg
    · rw [hXg]; exact hvn
  · -- `b ≤ t4`
    rw [min_eq_left hb4] at hzpp
    unfold Step78Data.bTime at hzpp hb4
    by_cases h3 : step78FirstGe D.nearSet1 Z ω ≤ min (D.thit Z ω) (D.treg ω)
    · -- the near event
      rw [min_eq_right h3] at hzpp
      have hfin : step78FirstGe D.nearSet1 Z ω < ⊤ := lt_trans hzpp (WithTop.coe_lt_top _)
      obtain ⟨r3, hr3U, hRr3, hr3e⟩ := step78FirstGe_attained (locIco_near1 hF ω) hfin
      have hrr3 : r ≤ r3 := by
        have : Z ω ≤ r3 := hRr3
        rw [hz] at this; exact WithTop.coe_le_coe.1 this
      have hr3T : r3 < D.T := WithTop.coe_lt_coe.1 (hr3e ▸ hzpp)
      have hrs : r + (r3 - r) = r3 := add_tsub_cancel_of_le hrr3
      have hb : (r : WithTop ℝ≥0) + ((r3 - r : ℝ≥0) : WithTop ℝ≥0) ≤ D.bTime Z ω := by
        unfold Step78Data.bTime
        rw [← WithTop.coe_add, hrs, min_eq_right h3, ← hr3e]
      have hw := hcpl (r3 - r) hb
      rw [hrs] at hw
      obtain ⟨v, hv, hvn⟩ := hr3U
      rw [Step78Data.path_coe, hw] at hvn
      have hs4 : ((r3 - r : ℝ≥0) : ℝ) < (4 : ℝ) ^ D.n := by
        have : r3 - r ≤ r3 := tsub_le_self
        exact lt_of_le_of_lt (by exact_mod_cast this) (lt_trans (by exact_mod_cast hr3T) hT4)
      obtain ⟨g, hg, hsg, hg4, hXg⟩ := grid_near hX hs4
      refine Or.inl (Or.inl (Or.inr ⟨g, hg, hg4, v, hv, ?_⟩))
      rw [hXg]; exact hvn
    · rw [not_le] at h3
      rw [min_eq_left h3.le] at hzpp
      by_cases h12 : D.thit Z ω ≤ D.treg ω
      · -- hit time
        rw [min_eq_left h12] at hzpp h3
        right
        by_contra hge
        rw [not_lt] at hge
        have hne : Z ω ≠ ⊤ := by rw [hz]; exact WithTop.coe_ne_top
        have hsr : ElboimSly.SRW.stopReal Z ω = r := by
          unfold ElboimSly.SRW.stopReal; rw [hz]; rfl
        have hthit : D.thit Z ω =
            ((stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) (r : ℝ) : ℝ≥0∞) :
              WithTop ℝ≥0) := by
          unfold Step78Data.thit
          rw [stepThitStop_of_ne hne, hsr]
          rfl
        have hbeq : D.bTime Z ω = D.thit Z ω := by
          unfold Step78Data.bTime
          rw [min_eq_left h12]
          exact min_eq_left h3.le
        have hrc : ∀ s : ℝ, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), D.path ω s' = D.path ω s :=
          exists_Ico_const_stepExt (hF.hrc ω)
        have hcpl' : ∀ s : ℝ, 0 ≤ s →
            ENNReal.ofReal ((r : ℝ) + s) ≤ stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ))
              (r : ℝ) → D.path ω ((r : ℝ) + s) = D.path ω (r : ℝ) + X s.toNNReal := by
          intro s hs0 hle
          have hcast : (r : ℝ) + s = ((r + s.toNNReal : ℝ≥0) : ℝ) := by
            push_cast; rw [Real.coe_toNNReal _ hs0]
          have hof : ENNReal.ofReal ((r : ℝ) + s) = ((r + s.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcast, ENNReal.ofReal_coe_nnreal]
          have hb : (r : WithTop ℝ≥0) + ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ D.bTime Z ω := by
            rw [hbeq, hthit, ← WithTop.coe_add]
            rw [hof] at hle
            exact hle
          have hw := hcpl s.toNNReal hb
          rw [hcast, Step78Data.path_coe, Step78Data.path_coe, hw]
        have hmain := step78_ofReal_add_le_stepThit (β := D.β) (α := fun _ => ((0 : ℝ≥0) : ℝ))
          hF.hd hF.hβ hrc (NNReal.coe_nonneg r) hrel.2 hX hcpl' (n4 := (4 : ℝ) ^ D.n)
          (by simpa using hge)
        rw [hthit] at hzpp
        have h1 : (D.T : ℝ≥0∞) < ENNReal.ofReal ((r : ℝ) + (4 : ℝ) ^ D.n) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
            (by linarith [hT4, NNReal.coe_nonneg r])
        exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 hmain) hzpp.le) (lt_irrefl _)
      · -- treg
        rw [not_le] at h12
        rw [min_eq_right h12.le] at hzpp h3
        obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hzpp)
        obtain ⟨k, hk1, hkq, hkw⟩ := (D.treg_le_iff hF ω q).1 (le_of_eq hq.symm)
        have hkβ : (0 : ℝ) ≤ (k : ℝ) * D.β := by positivity
        have hqk : q = ((k : ℝ) * D.β).toNNReal := by
          refine le_antisymm ?_ hkq
          have : D.treg ω ≤ ((((k : ℝ) * D.β).toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
            iInf₂_le k ⟨hk1, hkw⟩
          rw [← hq] at this
          exact WithTop.coe_le_coe.1 this
        have hqR : (q : ℝ) = (k : ℝ) * D.β := by rw [hqk]; exact Real.coe_toNNReal _ hkβ
        have hqT : q < D.T := WithTop.coe_lt_coe.1 (hq ▸ hzpp)
        have hrq : r < q := WithTop.coe_lt_coe.1 (hq ▸ hlt)
        by_cases hr0 : r = 0
        · have hbeq : D.bTime Z ω = D.treg ω := by
            unfold Step78Data.bTime
            rw [min_eq_right h12.le]
            exact min_eq_left h3.le
          have hb : (r : WithTop ℝ≥0) + (q : WithTop ℝ≥0) ≤ D.bTime Z ω := by
            rw [hbeq, ← hq, hr0, WithTop.coe_zero, zero_add]
          have hw := hcpl q hb
          rw [hr0, zero_add, h0 ω] at hw
          have hwq : D.w q ω = D.u := by rw [hqk]; exact hkw
          rw [hwq] at hw
          have hX0 : X q = 0 := by simpa using hw
          refine Or.inl (Or.inl (Or.inl ⟨k, hk1, ?_, ?_⟩))
          · rw [← hqR]; exact lt_trans (by exact_mod_cast hqT) hT4
          · rw [← hqk]; exact hX0
        · exfalso
          have hrpos : 0 < r := pos_iff_ne_zero.2 hr0
          have hrk : (r : ℝ) < (k : ℝ) * D.β := by rw [← hqR]; exact_mod_cast hrq
          have hle := D.thit_le_closing hC ω hrpos hk1 hkw hrk (by have := hF.hβ; linarith)
          have hne : Z ω ≠ ⊤ := by rw [hz]; exact WithTop.coe_ne_top
          have hsr : ElboimSly.SRW.stopReal Z ω = r := by
            unfold ElboimSly.SRW.stopReal; rw [hz]; rfl
          have hthit : D.thit Z ω =
              ((stepThit D.β (D.path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) (r : ℝ) : ℝ≥0∞) :
                WithTop ℝ≥0) := by
            unfold Step78Data.thit
            rw [stepThitStop_of_ne hne, hsr]
            rfl
          have htr : D.treg ω = ((ENNReal.ofReal ((k : ℝ) * D.β) : ℝ≥0∞) : WithTop ℝ≥0) := by
            rw [← hq, hqk]; rfl
          apply h12.not_ge
          rw [hthit, htr]
          exact hle

end ElboimSly.Paper.Step

end
