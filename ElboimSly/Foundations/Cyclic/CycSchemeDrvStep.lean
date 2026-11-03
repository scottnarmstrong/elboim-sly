/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvEnd
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvEdge
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvMark
public import Mathlib

/-!
# The driving scheme (c): the driven step analysis

The driving scheme (c), (i)–(iii). `gstep_drv`: from a record with
`GAt P (drl P jx Ñ) k r ρ` and a good driving outcome `o'` (`DrvGood`), the four fields of `GStep`
(`CycSchemeGenUpd`) for the environment outcome `ψ(o')` hold: the driven path of walk `k` is constant
on `[r, r + s*)`, has left limit `p(r)` at `r + s*`, the new vertex of the scheme is `p(r + s*)`,
and a step that neither stops nor ends the global horizon ends at a jump of the path or at a
multiple of `β`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) {P : CycPlan I d β} {sc : ℝ≥0∞}
  {Ñ : Measure (DrvS d J)} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o' : Outcome (DrvS d J)}

local notation "𝒪" => drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o'
local notation "𝔰" => CycScheme.sStar P sc (ρ, false) (drvPsiOut (jx := jx) (β := β) j0 P sc
  (ρ, false) o')

theorem vec_ne_zero (v : Dir d) : v.vec ≠ 0 := by
  intro h
  have h2 : v.vec v.1 = 0 := by rw [h]; rfl
  rw [Dir.vec_apply_fst] at h2
  split_ifs at h2; simp at h2

theorem step_marked_drv (hj : ∀ k, Measurable (jx k))
    (hgood : ∀ j, relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) (hg : DrvGood jx j0 P sc Ñ (ρ, false) o')
    (hns : ¬ CycScheme.stops P sc (ρ, false) 𝒪)
    (hfl : ((𝔰 : ℝ≥0) : ℝ≥0∞) ≠ CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) :
    0 < 𝔰 ∧ ((r + 𝔰) ∈ CDisc (gpth P (drl P jx Ñ) k).1.fn ∨
      ∃ m : ℕ, ((r + 𝔰 : ℝ≥0) : ℝ) = β * m) := by
  obtain ⟨hs, hsh, hsβ, hsFr⟩ := sStar_facts j0 hg
  have hstep := drv_hstep j0 hgood h hg
  have hpos : (CycScheme.cur P (ρ, false)).pos = (gpth P (drl P jx Ñ) k).1.fn r := h.pos false
  set s := 𝔰 with hsdef
  have hleft : 0 < s → (gpth P (drl P jx Ñ) k).1.left (r + s) =
      (gpth P (drl P jx Ñ) k).1.fn r := fun hs0 => left_eq_of_step hs0 hstep
  have hdisc : (gpth P (drl P jx Ñ) k).1.fn (r + s) ≠ (gpth P (drl P jx Ñ) k).1.fn r →
      0 < s ∧ (r + s) ∈ CDisc (gpth P (drl P jx Ñ) k).1.fn := by
    intro hfn
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · rw [h0, add_zero] at hfn; exact absurd rfl hfn
      · exact h0
    refine ⟨hs0, ?_⟩
    have hp : 0 < r + s := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hs0)
    rw [(gpth P (drl P jx Ñ) k).1.mem_CDisc_iff hp, hleft hs0]
    exact fun hh => hfn hh.symm
  rcases step_end j0 hj hgood h hg with ⟨hF, hs0, e1, he1, hn, hf⟩ | ⟨hF, hz, hs0, v, hn, hf⟩ |
    ⟨hF, hz, hn, hf⟩
  · refine ⟨hs0, Or.inl (hdisc ?_).2⟩
    rw [hf]
    have h2 := latticeAdj_of_edge e1 (edgeOther_spec he1)
    intro hh
    rw [hh] at h2
    simp at h2
  · refine ⟨hs0, Or.inl (hdisc ?_).2⟩
    rw [hf]
    intro hh
    exact vec_ne_zero v (add_eq_left.1 hh)
  · have hz' : o'.2 Set.univ = 0 := by
      by_contra hne
      exact ((psiOut_univ_ne_zero_iff j0 hj h hg).2 hne) hz
    have hso : ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hOf P sc (ρ, false) := by
      have := hg.zero hz'
      rw [← this]; exact hs
    rw [CycSchemeEnv.hOf_coe] at hso
    unfold CycScheme.hAll at hso
    have hcases : ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ∨
        ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hCap β (CycScheme.cur P (ρ, false)) ∨
        ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) ∨
        ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)) := by
      rcases min_choice (min (CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)))
          (CycScheme.hCap β (CycScheme.cur P (ρ, false))))
        (min (CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)))
          (CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)))) with h1 | h1 <;> rw [h1] at hso
      · rcases min_choice (CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)))
          (CycScheme.hCap β (CycScheme.cur P (ρ, false))) with h2 | h2 <;> rw [h2] at hso
        · exact Or.inl hso
        · exact Or.inr (Or.inl hso)
      · rcases min_choice (CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)))
          (CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) with h2 | h2 <;> rw [h2] at hso
        · exact Or.inr (Or.inr (Or.inl hso))
        · exact Or.inr (Or.inr (Or.inr hso))
    rcases hcases with hF' | hC | hD | hG
    · exact absurd hF' hF
    · have hβ : 0 < β := Fact.out
      unfold CycScheme.hCap at hC
      rw [h.time false] at hC
      have h2 : (r : ℝ) < β * ((⌊(r : ℝ) / β⌋₊ : ℝ) + 1) := by
        have := Nat.lt_floor_add_one ((r : ℝ) / β)
        calc (r : ℝ) = β * ((r : ℝ) / β) := by field_simp
          _ < _ := by gcongr
      have hx : 0 < β * ((⌊(r : ℝ) / β⌋₊ : ℝ) + 1) - r := by linarith
      have hs_real : (s : ℝ) = β * ((⌊(r : ℝ) / β⌋₊ : ℝ) + 1) - r := by
        have := congrArg ENNReal.toReal hC
        rw [ENNReal.toReal_ofReal hx.le] at this
        simpa using this
      refine ⟨?_, Or.inr ⟨⌊(r : ℝ) / β⌋₊ + 1, ?_⟩⟩
      · rw [← NNReal.coe_pos]; linarith
      · push_cast; linarith
    · exfalso
      apply hns
      unfold CycScheme.stops
      rw [hn, hpos, ite_eq_right (not_not.2 rfl)]
      exact hD
    · exact absurd hG hfl

/-- The driving scheme (c): the four outputs of the correctness analysis of a driven
step. -/
theorem gstep_drv (hj : ∀ k, Measurable (jx k))
    (hgood : ∀ j, relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') :
    GStep P sc (drl P jx Ñ) k r ρ (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o') where
  const := fun t hrt hts => fn_const_of_step (drv_hstep j0 hgood h hg) t hrt hts
  left := fun hs0 => left_eq_of_step hs0 (drv_hstep j0 hgood h hg)
  newV := by
    rcases step_end j0 hj hgood h hg with ⟨-, -, e1, -, hn, hf⟩ | ⟨-, -, -, v, hn, hf⟩ |
      ⟨-, -, hn, hf⟩
    · rw [hn, hf]
    · rw [hn, hf]
    · rw [hn, hf]
  marked := fun hns hfl => step_marked_drv j0 hj hgood h hg hns hfl

end CycSchemeGen
end ElboimSly.Cyclic

end
