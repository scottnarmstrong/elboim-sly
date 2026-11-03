/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib

/-!
# Countable dense sets of times and continuous paths

Measurability of path functionals (a), (b), (c) (the deterministic part).

For an interval `J ⊆ [0,∞)` with more than one point, `denseSub J = (J ∩ ℚ) ∪ (J ∩ {inf J, sup J})`
is countable and dense in `J`. Suprema and infima of continuous functionals over `J` equal those
over `denseSub J`.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- The nonnegative rational times. -/
def ratTimes : Set ℝ≥0 := {t | ∃ q : ℚ, (t : ℝ) = q}

/-- Measurability of path functionals. `J' = (J ∩ ℚ) ∪ (J ∩ {inf J, sup J})`. -/
def denseSub (J : Set ℝ≥0) : Set ℝ≥0 := (J ∩ ratTimes) ∪ (J ∩ {sInf J, sSup J})

lemma ratTimes_countable : ratTimes.Countable := by
  refine (Set.countable_range (fun q : ℚ => Real.toNNReal q)).mono ?_
  rintro t ⟨q, hq⟩
  exact ⟨q, by show Real.toNNReal (q : ℝ) = t; rw [← hq]; exact Real.toNNReal_coe⟩

lemma denseSub_subset (J : Set ℝ≥0) : denseSub J ⊆ J := by
  rintro t (⟨h, -⟩ | ⟨h, -⟩) <;> exact h

lemma denseSub_countable (J : Set ℝ≥0) : (denseSub J).Countable :=
  (ratTimes_countable.mono Set.inter_subset_right |>.union
    ((Set.toFinite {sInf J, sSup J}).countable.mono Set.inter_subset_right)).mono
    (by rintro t (h | h) <;> [exact Or.inl h; exact Or.inr h])

/-- Rational times in an open interval. -/
lemma exists_ratTimes_btwn {a b : ℝ≥0} (hab : a < b) : ∃ t ∈ ratTimes, a < t ∧ t < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt a.2 hq1
  refine ⟨Real.toNNReal q, ⟨q, by simp [hq0.le]⟩, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]; exact hq1
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]; exact hq2

/-- Measurability of path functionals. `denseSub J` is dense in the interval `J`. -/
lemma subset_closure_denseSub {J : Set ℝ≥0} (hJ : J.OrdConnected) : J ⊆ closure (denseSub J) := by
  intro t ht
  by_cases hlow : ∃ a ∈ J, a < t
  · by_cases hhigh : ∃ b ∈ J, t < b
    · obtain ⟨a, haJ, hat⟩ := hlow
      obtain ⟨b, hbJ, htb⟩ := hhigh
      rw [Metric.mem_closure_iff]
      intro ε hε
      set c : ℝ≥0 := max a (t - Real.toNNReal (ε / 2)) with hc
      have hct : c < t := by
        refine max_lt hat ?_
        have : 0 < Real.toNNReal (ε / 2) := by simpa using hε
        exact tsub_lt_self (lt_of_le_of_lt bot_le hat) this
      obtain ⟨q, hqr, hcq, hqt⟩ := exists_ratTimes_btwn hct
      refine ⟨q, Or.inl ⟨hJ.out haJ ht ⟨(le_max_left _ _).trans hcq.le, hqt.le⟩, hqr⟩, ?_⟩
      rw [NNReal.dist_eq, abs_lt]
      have h1 : (c : ℝ) ≥ t - ε / 2 := by
        have : ((t - Real.toNNReal (ε / 2) : ℝ≥0) : ℝ) ≤ c := by
          exact_mod_cast le_max_right _ _
        have h2 : (t : ℝ) - ε / 2 ≤ ((t - Real.toNNReal (ε / 2) : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_sub_def, Real.coe_toNNReal _ (by positivity)]
          exact le_max_left _ _
        linarith
      have h5 : (c : ℝ) < q := hcq
      have h6 : (q : ℝ) < t := hqt
      constructor <;> linarith
    · -- `t` is the maximum of `J`
      push Not at hhigh
      refine subset_closure (Or.inr ⟨ht, Or.inr ?_⟩)
      refine le_antisymm (le_csSup ?_ ht) (csSup_le ⟨t, ht⟩ fun x hx => hhigh x hx)
      exact ⟨t, fun x hx => hhigh x hx⟩
  · push Not at hlow
    refine subset_closure (Or.inr ⟨ht, Or.inl ?_⟩)
    exact le_antisymm (le_csInf ⟨t, ht⟩ hlow) (csInf_le ⟨0, fun x _ => bot_le⟩ ht)

/-! ### Suprema and infima over dense sets -/

section Dense

variable {X α : Type*} [TopologicalSpace X] [CompleteLinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α]

lemma iSup_congr_dense {F : X → α} (hF : Continuous F) {D S : Set X} (hDS : D ⊆ S)
    (hS : S ⊆ closure D) : ⨆ x ∈ S, F x = ⨆ x ∈ D, F x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (biSup_mono hDS)
  have hcl : IsClosed {y | F y ≤ ⨆ x ∈ D, F x} := isClosed_le hF continuous_const
  have : D ⊆ {y | F y ≤ ⨆ x ∈ D, F x} := fun y hy => le_biSup F hy
  exact closure_minimal this hcl (hS hx)

lemma iInf_congr_dense {F : X → α} (hF : Continuous F) {D S : Set X} (hDS : D ⊆ S)
    (hS : S ⊆ closure D) : ⨅ x ∈ S, F x = ⨅ x ∈ D, F x := by
  refine le_antisymm (biInf_mono hDS) (le_iInf₂ fun x hx => ?_)
  have hcl : IsClosed {y | (⨅ x ∈ D, F x) ≤ F y} := isClosed_le continuous_const hF
  have : D ⊆ {y | (⨅ x ∈ D, F x) ≤ F y} := fun y hy => biInf_le F hy
  exact closure_minimal this hcl (hS hx)

end Dense

/-- Measurability of path functionals (a), infimum over `J` of a continuous function equals the
infimum over `denseSub J`. -/
lemma iInf_eq_denseSub {J : Set ℝ≥0} (hJ : J.OrdConnected) {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    ⨅ t ∈ J, (f t : EReal) = ⨅ t ∈ denseSub J, (f t : EReal) :=
  iInf_congr_dense (continuous_coe_real_ereal.comp hf) (denseSub_subset J)
    (subset_closure_denseSub hJ)

/-- Measurability of path functionals (a), supremum version. -/
lemma iSup_eq_denseSub {J : Set ℝ≥0} (hJ : J.OrdConnected) {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    ⨆ t ∈ J, (f t : EReal) = ⨆ t ∈ denseSub J, (f t : EReal) :=
  iSup_congr_dense (continuous_coe_real_ereal.comp hf) (denseSub_subset J)
    (subset_closure_denseSub hJ)

/-- Pairs of times in `J` at distance at most `h`. -/
def closePairs (J : Set ℝ≥0) (h : ℝ≥0) : Set (ℝ≥0 × ℝ≥0) :=
  {p | p.1 ∈ J ∧ p.2 ∈ J ∧ dist p.1 p.2 ≤ h}

lemma closePairs_mono {J K : Set ℝ≥0} (hJK : J ⊆ K) (h : ℝ≥0) : closePairs J h ⊆ closePairs K h :=
  fun _ hp => ⟨hJK hp.1, hJK hp.2.1, hp.2.2⟩

lemma closePairs_subset_closure {J : Set ℝ≥0} (hJ : J.OrdConnected) (h : ℝ≥0) :
    closePairs J h ⊆ closure (closePairs (denseSub J) h) := by
  have hsymm : ∀ p ∈ closePairs (denseSub J) h, Prod.swap p ∈ closePairs (denseSub J) h :=
    fun p hp => ⟨hp.2.1, hp.1, by rw [dist_comm]; exact hp.2.2⟩
  -- ordered pairs
  have key : ∀ s t, s ≤ t → (s, t) ∈ closePairs J h → (s, t) ∈ closure (closePairs (denseSub J) h) := by
    intro s t hst hp
    rcases hst.eq_or_lt with rfl | hlt
    · have hs : s ∈ closure (denseSub J) := subset_closure_denseSub hJ hp.1
      have := map_mem_closure (f := fun x : ℝ≥0 => (x, x)) (continuous_id.prodMk continuous_id)
        hs (t := closePairs (denseSub J) h) (fun x hx => ⟨hx, hx, by simp⟩)
      exact this
    · rw [Metric.mem_closure_iff]
      intro ε hε
      set e : ℝ≥0 := Real.toNNReal (ε / 2) with he
      have he0 : 0 < e := by simpa [he] using hε
      set mid : ℝ≥0 := (s + t) / 2 with hmid
      have hm1 : s < mid := by
        rw [hmid]
        have : (0 : ℝ≥0) < 2 := by norm_num
        rw [lt_div_iff₀ this]
        calc s * 2 = s + s := by ring
          _ < s + t := by gcongr
      have hm2 : mid < t := by
        rw [hmid]
        have : (0 : ℝ≥0) < 2 := by norm_num
        rw [div_lt_iff₀ this]
        calc s + t < t + t := by gcongr
          _ = t * 2 := by ring
      have hu : s < min (s + e) mid := lt_min (lt_add_of_pos_right _ he0) hm1
      have hv : max (t - e) mid < t := max_lt (tsub_lt_self (lt_of_le_of_lt bot_le hlt) he0) hm2
      obtain ⟨s', hs'r, hs'1, hs'2⟩ := exists_ratTimes_btwn hu
      obtain ⟨t', ht'r, ht'1, ht'2⟩ := exists_ratTimes_btwn hv
      have hs'J : s' ∈ J := hJ.out hp.1 hp.2.1 ⟨hs'1.le, (hs'2.trans_le (min_le_right _ _)).le.trans hm2.le⟩
      have ht'J : t' ∈ J := hJ.out hp.1 hp.2.1
        ⟨((hm1.trans_le (le_max_right _ _)).trans ht'1).le, ht'2.le⟩
      have hs'm : s' < mid := hs'2.trans_le (min_le_right _ _)
      have hmt' : mid < t' := (le_max_right _ _).trans_lt ht'1
      have hs't' : s' ≤ t' := (hs'm.trans hmt').le
      refine ⟨(s', t'), ⟨Or.inl ⟨hs'J, hs'r⟩, Or.inl ⟨ht'J, ht'r⟩, ?_⟩, ?_⟩
      · have := hp.2.2
        rw [NNReal.dist_eq, abs_of_nonpos (by exact_mod_cast (sub_nonpos.2 (NNReal.coe_le_coe.2 hst)))] at this
        rw [NNReal.dist_eq, abs_of_nonpos (by exact_mod_cast (sub_nonpos.2 (NNReal.coe_le_coe.2 hs't')))]
        have h1 : (s : ℝ) ≤ s' := hs'1.le
        have h2 : (t' : ℝ) ≤ t := ht'2.le
        linarith
      · rw [Prod.dist_eq, max_lt_iff, NNReal.dist_eq, NNReal.dist_eq]
        have h1 : (s : ℝ) < s' := hs'1
        have h2 : (t' : ℝ) < t := ht'2
        have h3 : (s' : ℝ) < s + e := by exact_mod_cast hs'2.trans_le (min_le_left _ _)
        have h4 : (t : ℝ) - e < t' := by
          have : t - e < t' := (le_max_left _ _).trans_lt ht'1
          have h5 : (t : ℝ) - e ≤ ((t - e : ℝ≥0) : ℝ) := by
            rw [NNReal.coe_sub_def]; exact le_max_left _ _
          have h6 : ((t - e : ℝ≥0) : ℝ) < t' := by exact_mod_cast this
          linarith
        have he' : (e : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
        constructor
        · rw [abs_lt]; constructor <;> linarith
        · rw [abs_lt]; constructor <;> linarith
  intro p hp
  rcases le_total p.1 p.2 with hle | hle
  · exact key p.1 p.2 hle hp
  · have hp' : Prod.swap p ∈ closePairs J h := ⟨hp.2.1, hp.1, by rw [dist_comm]; exact hp.2.2⟩
    have := key p.2 p.1 hle hp'
    have := map_mem_closure (f := Prod.swap) continuous_swap this (t := closePairs (denseSub J) h)
      hsymm
    simpa using this

/-- Measurability of path functionals (c). For compact `J` (an interval) and continuous `w`:
some point of `J` is within `r` of `x` iff the infimum over `denseSub J` is `≤ r`. -/
lemma exists_mem_le_iff_iInf_le {E : Type*} [SeminormedAddCommGroup E] {J : Set ℝ≥0}
    (hJ : J.OrdConnected) (hc : IsCompact J) (hne : J.Nonempty) {w : ℝ≥0 → E} (hw : Continuous w)
    (x : E) (r : ℝ) :
    (∃ t ∈ J, ‖w t - x‖ ≤ r) ↔ ⨅ t ∈ denseSub J, ((‖w t - x‖ : ℝ) : EReal) ≤ (r : EReal) := by
  have hg : Continuous fun t => ‖w t - x‖ := (hw.sub continuous_const).norm
  rw [← iInf_eq_denseSub hJ hg]
  constructor
  · rintro ⟨t, htJ, ht⟩
    exact (biInf_le _ htJ).trans (EReal.coe_le_coe_iff.2 ht)
  · intro h
    obtain ⟨t0, ht0, hmin⟩ := hc.exists_isMinOn hne hg.continuousOn
    refine ⟨t0, ht0, ?_⟩
    have : ((‖w t0 - x‖ : ℝ) : EReal) ≤ ⨅ t ∈ J, ((‖w t - x‖ : ℝ) : EReal) :=
      le_iInf₂ fun t ht => EReal.coe_le_coe_iff.2 (hmin ht)
    exact EReal.coe_le_coe_iff.1 (this.trans h)

end ElboimSly.Brownian
