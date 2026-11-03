/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLimFin2
public import ElboimSly.Foundations.Cyclic.CycTruncSpec
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalNth
public import Mathlib

/-!
# The entries of `Trunc_s(ρ^𝒫(ν))`

World-lines of a plan; joint exploration filtration (c), the environment scheme (b). `trunc_envFinal_nth`: entry `k` of the
truncation `Rec^𝒫(s) = Trunc_s(ρ^𝒫(ν))` at global time `s` is `tgt P ν s k` if the walk `k` is
appended by the recursion and `Λ_k ≤ s`, and absent otherwise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)}

open scoped Classical in
omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem trunc_envFinal_nth (junk : CycEntry I d) (s : ℝ≥0) (k : ℕ) :
    (CycRec.trunc s (P.envFinal ν)).nth k =
      if P.Cont (rule P ν) k ∧ lam P ν k ≤ (s : ℝ≥0∞) then some (tgt P ν s k) else none := by
  set ρ : CycRec I d := P.envFinal ν with hρ
  have hnth : ∀ i, ρ.nth i = if P.Cont (rule P ν) i then some (P.E (rule P ν) i) else none :=
    fun i => CycPlan.cycFinal_nth_gen P (rule P ν) i
  have hlt : ∀ i : ℕ, (i : ℕ∞) < ρ.num ↔ P.Cont (rule P ν) i := by
    intro i
    constructor
    · intro h
      obtain ⟨e, he⟩ := nth_of_lt_num h
      rw [hnth i] at he
      by_contra hc
      rw [ite_eq_right hc] at he
      exact absurd he (by simp)
    · intro hc
      refine lt_num_of_nth (e := P.E (rule P ν) i) ?_
      rw [hnth i, ite_eq_left hc]
  have hlen : ∀ i, P.Cont (rule P ν) i → ρ.lenAt i = (P.E (rule P ν) i).len := by
    intro i hc
    unfold CycRec.lenAt
    rw [hnth i, ite_eq_left hc]
    rfl
  have hcum : ∀ i, P.Cont (rule P ν) i → ρ.cum i = lam P ν i := by
    intro i hc
    unfold CycRec.cum lam
    refine Finset.sum_congr rfl fun i' hi' => ?_
    exact hlen i' (CycPlan.Cont.anti P (rule P ν) (Finset.mem_range.1 hi').le hc)
  obtain ⟨m, hm, hiff, hcoord, -⟩ := CycRec.trunc_spec junk s ρ
  by_cases hs : k ∈ ρ.surv s
  · have hkm : (k : ℕ∞) < (CycRec.trunc s ρ).num := by rw [hm]; exact (hiff k).2 hs
    obtain ⟨e, he⟩ := nth_of_lt_num hkm
    have hc : P.Cont (rule P ν) k := (hlt k).1 hs.1
    have hl : lam P ν k ≤ (s : ℝ≥0∞) := by rw [← hcum k hc]; exact hs.2
    rw [ite_eq_left ⟨hc, hl⟩, he]
    have hcoe : (CycRec.trunc s ρ).coord junk k = e := by
      unfold CycRec.coord; rw [he]; rfl
    have hco := (hcoord k hs).symm.trans hcoe
    rw [← hco]
    have hck : ρ.coord junk k = P.E (rule P ν) k := by
      unfold CycRec.coord; rw [hnth k, ite_eq_left hc]; rfl
    rw [hck]
    unfold CycRec.truncEntry tgt
    have hc1 : ρ.cum (k + 1) = lam P ν k + (P.E (rule P ν) k).len := by
      unfold CycRec.cum
      rw [Finset.sum_range_succ]
      have := hcum k hc
      unfold CycRec.cum at this
      rw [this, hlen k hc]
    rw [hc1, hcum k hc]
  · have hkm : ¬ (k : ℕ∞) < (CycRec.trunc s ρ).num := by rw [hm]; exact fun h => hs ((hiff k).1 h)
    have hn : (CycRec.trunc s ρ).nth k = none := by
      by_contra hne
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hne
      exact hkm (lt_num_of_nth he)
    rw [hn, ite_eq_right]
    rintro ⟨hc, hl⟩
    exact hs ⟨(hlt k).2 hc, by rw [hcum k hc]; exact hl⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
