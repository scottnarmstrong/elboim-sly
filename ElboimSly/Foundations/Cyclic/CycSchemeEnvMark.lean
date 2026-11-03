/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvExt
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# The environment scheme (b): steps end at marked times

The environment scheme (b), non-explosion. `step_marked`: a step that neither stops the walk
nor sets the end flag has `s* > 0` and ends at a jump of the environment path or at a multiple of
`β` (the horizon `h = h_cap`). Used for the non-explosion of the steps of one walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

/-- A jump of the path at `r + s` forces `s > 0` and `r + s ∈ CDisc`. -/
theorem mem_CDisc_of_jump (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hfn : (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) ≠ (pth P ν k).1.fn r) :
    0 < CycScheme.sStar P sc (ρ, false) o ∧
      (r + CycScheme.sStar P sc (ρ, false) o) ∈ CDisc (pth P ν k).1.fn := by
  obtain ⟨hconst, hleft⟩ := quiet_facts hν h hg
  have hs : 0 < CycScheme.sStar P sc (ρ, false) o := by
    rcases eq_zero_or_pos (CycScheme.sStar P sc (ρ, false) o) with h0 | h0
    · rw [h0, add_zero] at hfn; exact absurd rfl hfn
    · exact h0
  refine ⟨hs, ?_⟩
  have hpos : 0 < r + CycScheme.sStar P sc (ρ, false) o := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hs)
  rw [(pth P ν k).1.mem_CDisc_iff hpos, hleft hs]
  exact fun hh => hfn hh.symm

omit [Countable I] in
/-- A ring on the front at `r + s` that is an atom of `ν` forces a jump at `r + s`. -/
theorem jump_of_atom (hν : CycGood ν) (_h : EnvAt P ν k r ρ) {s : ℝ≥0} (hs : 0 < s)
    (hleft : (pth P ν k).1.left (r + s) = (pth P ν k).1.fn r) {e : Edge d}
    (he : Edge.Mem ((pth P ν k).1.fn r) e)
    (hA : 1 ≤ ν {((dat P ν k).copy, (e, (dat P ν k).clock β (r + s)))}) :
    (pth P ν k).1.fn (r + s) ≠ (pth P ν k).1.fn r := by
  have hpos : 0 < r + s := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hs)
  have h1 := (swap_rules hν k).2 (r + s) hpos e (by rw [hleft]; exact he) hA
  rw [hleft] at h1
  have h2 := latticeAdj_of_edge e h1
  intro hh
  rw [hh] at h2
  simp at h2

theorem step_marked (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o)
    (hfl : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≠
      CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) :
    0 < CycScheme.sStar P sc (ρ, false) o ∧
      ((r + CycScheme.sStar P sc (ρ, false) o) ∈ CDisc (pth P ν k).1.fn ∨
        ∃ m : ℕ, ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ) = β * m) := by
  set s := CycScheme.sStar P sc (ρ, false) o with hsdef
  obtain ⟨hconst, hleft⟩ := quiet_facts hν h hg
  by_cases hjump : (pth P ν k).1.fn (r + s) ≠ (pth P ν k).1.fn r
  · exact ⟨(mem_CDisc_of_jump hν h hg hjump).1, Or.inl (mem_CDisc_of_jump hν h hg hjump).2⟩
  have hfn : (pth P ν k).1.fn (r + s) = (pth P ν k).1.fn r := not_not.1 hjump
  have hz : o.2 Set.univ = 0 := by
    by_contra hz
    obtain ⟨e1, he1, hs0, -, -, -, hat⟩ := fresh_conv hν h hg hz
    refine jump_of_atom hν h hs0 (hleft hs0) (e := e1) (by rw [← h.pos false]; exact he1) ?_ hfn
    rw [← fp_eq h]; exact hat
  have hso : (s : ℝ≥0∞) = CycScheme.hOf P sc (ρ, false) := by
    have := sStar_eq_of_le_h (P := P) (sc := sc) o hg.le_h
    rw [hg.zero hz] at this
    exact this
  rw [hOf_coe] at hso
  unfold CycScheme.hAll at hso
  have hcases : (s : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ∨
      (s : ℝ≥0∞) = CycScheme.hCap β (CycScheme.cur P (ρ, false)) ∨
      (s : ℝ≥0∞) = CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) ∨
      (s : ℝ≥0∞) = CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)) := by
    rcases min_choice (min (CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)))
        (CycScheme.hCap β (CycScheme.cur P (ρ, false))))
      (min (CycScheme.hDl P ρ (CycScheme.cur P (ρ, false))) (CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)))) with h1 | h1 <;> rw [h1] at hso
    · rcases min_choice (CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)))
        (CycScheme.hCap β (CycScheme.cur P (ρ, false))) with h2 | h2 <;> rw [h2] at hso
      · exact Or.inl hso
      · exact Or.inr (Or.inl hso)
    · rcases min_choice (CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)))
        (CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) with h2 | h2 <;> rw [h2] at hso
      · exact Or.inr (Or.inr (Or.inl hso))
      · exact Or.inr (Or.inr (Or.inr hso))
  rcases hcases with hF | hC | hD | hG
  · exfalso
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · exfalso
        rw [h0] at hF
        exact hFr_ne_zero h (by simpa using hF.symm)
      · exact h0
    have hsh : s ≤ CycScheme.hOf P sc (ρ, false) := sStar_le_h o
    obtain ⟨e0, he0, hring⟩ := ringSet_front_of_hFr h hs0 hsh hF
    have hy : fp P ρ e0 s ∈ ρ.region β := ringSet_subset_region ρ hring
    have hat := (h.atom_iff_ring hν hy).2 hring
    rw [fp_eq h] at hat
    exact jump_of_atom hν h hs0 (hleft hs0) (e := e0) (by rw [← h.pos false]; exact he0) hat hfn
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
    rw [newV_eq hν h hg, h.pos, ite_eq_right (not_not.2 hfn)]
    exact hD
  · exact absurd hG hfl

end CycSchemeEnv
end ElboimSly.Cyclic

end
