/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleDet
public import ElboimSly.Paper.Step.Lemma78Setting
public import Mathlib

/-!
# The stretch `[ζ, b]` in terms of `Step78Data`

The data `D = step78SliceData N u q t'_n` has second walk `W₂ = W^N_{u,q}` and
`V = W₁([0, t'_n])`. If `ζ + s ≤ b := thit^{(2)}(ζ) ∧ treg^{(2)} ∧ inf{r ≥ ζ : d(W₂(r), V) ≤ 1}`
then the hypotheses of `step78_agree_det` and `step78_no_close` hold on `[0, s]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*}

/-- The path-level data of Lemma 7.8 attached to the environment `N`. -/
noncomputable def step78SliceData (N : Ω → Measure (CycS Unit d β)) (u : Fin d → ℤ) (q : ℝ)
    (Tn : ℝ≥0) (n : ℕ) (ρ : ℝ) : Step78Data d Ω where
  β := β
  T := Tn
  n := n
  ρ := ρ
  u := u
  w := fun t ω => cycWalk (cycSlice () (N ω)) u q t
  V := fun ω => cycWalk (cycSlice () (N ω)) 0 0 '' Icc 0 (Tn : ℝ)

variable (N : Ω → Measure (CycS Unit d β)) (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) (n : ℕ) (ρ : ℝ)

theorem step78SliceData_path (ω : Ω) {x : ℝ} (hx : 0 ≤ x) :
    (step78SliceData N u q Tn n ρ).path ω x = cycWalk (cycSlice () (N ω)) u q x := by
  simp [Step78Data.path, stepExt, step78SliceData, Real.coe_toNNReal _ hx]

variable {N u q Tn n ρ}

/-- `b ≥ ζ + s` implies the walk stays at distance `> 1` from `V` on `[ζ, ζ + s)`. -/
theorem step78_cond_near (ω : Ω) (Z : Ω → WithTop ℝ≥0) (ζ s : ℝ≥0) (hZ : Z ω = ζ)
    (h : ((ζ + s : ℝ≥0) : WithTop ℝ≥0) ≤
      step78FirstGe (step78SliceData N u q Tn n ρ).nearSet1 Z ω) :
    ∀ s'' : ℝ, (ζ : ℝ) ≤ s'' → s'' < ζ + s → ∀ s1 ∈ Icc (0 : ℝ) Tn,
      1 < ‖cycWalk (cycSlice () (N ω)) u q s'' - cycWalk (cycSlice () (N ω)) 0 0 s1‖ := by
  intro s'' h1 h2 s1 hs1
  by_contra hle
  rw [not_lt] at hle
  have hs0 : 0 ≤ s'' := le_trans ζ.2 h1
  set r : ℝ≥0 := s''.toNNReal with hr
  have hrR : (r : ℝ) = s'' := Real.coe_toNNReal _ hs0
  have hmem : (r : ℝ) ∈ (step78SliceData N u q Tn n ρ).nearSet1 ω := by
    refine ⟨cycWalk (cycSlice () (N ω)) 0 0 s1, ⟨s1, hs1, rfl⟩, ?_⟩
    rw [step78SliceData_path N u q Tn n ρ ω (by rw [hrR]; exact hs0), hrR]
    exact hle
  have hZr : Z ω ≤ r := by
    rw [hZ]
    exact WithTop.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, hrR]; exact h1)
  have hfirst : step78FirstGe (step78SliceData N u q Tn n ρ).nearSet1 Z ω ≤ r :=
    iInf₂_le r ⟨hmem, hZr⟩
  have := (h.trans hfirst)
  have h3 : ζ + s ≤ r := WithTop.coe_le_coe.1 this
  have h4 : ((ζ : ℝ) + s) ≤ r := by exact_mod_cast h3
  linarith

/-- `b ≥ ζ + s` implies there is no `thit`-type approach on `(ζ, ζ + s)`. -/
theorem step78_cond_thit (ω : Ω) (Z : Ω → WithTop ℝ≥0) (ζ s : ℝ≥0) (hZ : Z ω = ζ)
    (h : ((ζ + s : ℝ≥0) : WithTop ℝ≥0) ≤ (step78SliceData N u q Tn n ρ).thit Z ω) :
    ∀ s'' : ℝ, (ζ : ℝ) < s'' → s'' < ζ + s → ∀ s''' : ℝ, 0 < s''' → s''' < ζ →
      (∃ k : ℤ, s''' = s'' + k * β) →
        1 < ‖cycWalk (cycSlice () (N ω)) u q s'' - cycWalk (cycSlice () (N ω)) u q s'''‖ := by
  intro s'' h1 h2 s''' h3 h4 hk
  by_contra hle
  rw [not_lt] at hle
  have hs0 : 0 ≤ s'' := le_trans ζ.2 h1.le
  have hthit : (step78SliceData N u q Tn n ρ).thit Z ω =
      stepThit β ((step78SliceData N u q Tn n ρ).path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) ζ := by
    have hne : Z ω ≠ ⊤ := by rw [hZ]; exact WithTop.coe_ne_top
    have hst : ElboimSly.SRW.stopReal Z ω = ζ := by simp only [ElboimSly.SRW.stopReal, hZ]; rfl
    simp only [Step78Data.thit, stepThitStop, ite_eq_right hne, hst]
    rfl
  rw [hthit] at h
  have hmem : stepThit β ((step78SliceData N u q Tn n ρ).path ω) (fun _ => ((0 : ℝ≥0) : ℝ)) ζ ≤
      ENNReal.ofReal s'' := by
    refine iInf₂_le s'' ⟨h1, s''', hk, by simpa using h3, h4, ?_⟩
    rw [step78SliceData_path N u q Tn n ρ ω hs0, step78SliceData_path N u q Tn n ρ ω h3.le]
    exact hle
  have h5 : ((ζ + s : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal s'' := h.trans hmem
  have h6 : (ζ : ℝ) + s ≤ s'' := by
    have := (ENNReal.ofReal_le_ofReal_iff hs0).1
      (by rwa [ENNReal.ofReal_coe_nnreal] : ENNReal.ofReal ((ζ + s : ℝ≥0) : ℝ) ≤
        ENNReal.ofReal s'')
    simpa using this
  linarith

/-- `b ≥ ζ + s` with `ζ = 0` implies `s ≤ kβ` whenever `W₂(kβ) = u`, `k ≥ 1`. -/
theorem step78_cond_treg (ω : Ω) (ζ s : ℝ≥0)
    (h : ((ζ + s : ℝ≥0) : WithTop ℝ≥0) ≤ (step78SliceData N u q Tn n ρ).treg ω) :
    (ζ : ℝ) = 0 → ∀ k : ℕ, 1 ≤ k → cycWalk (cycSlice () (N ω)) u q (k * β) = u →
      (s : ℝ) ≤ k * β := by
  intro hz k hk hw
  have hβ : 0 < β := Fact.out
  have hkβ : (0 : ℝ) ≤ k * β := by positivity
  have hmem : (step78SliceData N u q Tn n ρ).treg ω ≤ (((k : ℝ) * β).toNNReal : WithTop ℝ≥0) := by
    refine iInf₂_le k ⟨hk, ?_⟩
    show cycWalk (cycSlice () (N ω)) u q (((k : ℝ) * β).toNNReal : ℝ≥0) = u
    rw [Real.coe_toNNReal _ hkβ]; exact hw
  have h2 := WithTop.coe_le_coe.1 (h.trans hmem)
  have h3 : ((ζ + s : ℝ≥0) : ℝ) ≤ k * β := by
    have := (NNReal.coe_le_coe.2 h2)
    rwa [Real.coe_toNNReal _ hkβ] at this
  rw [NNReal.coe_add, hz, zero_add] at h3
  exact h3


end ElboimSly.Paper.Step

end
