/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvFresh
public import Mathlib

/-!
# The driving scheme (c): the end of a driven step

The driving scheme (c), (i), (ii). For a record with `GAt P (drl P jx Ñ) k r ρ` and a
good driving outcome `o'` (`DrvGood`), with `𝒪 = ψ(o')` the environment outcome and
`s = s*(𝒪)`, the driven path of walk `k` is constant on `[r, r + s)`, has left limit `p(r)` at
`r + s` (`drvStep_const`, `drvStep_left`) and, at `r + s`, is in exactly one of three situations
(`step_end`): the ring of the least forced edge (`s = h_fr`), a fresh atom of `Ñ`, or no event. In
each the new vertex `CycScheme.newV` of the environment scheme is `p(r + s)`.
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

omit [Countable I] [MeasurableSingletonClass I] in
theorem sStar_facts (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') :
    ((𝔰 : ℝ≥0) : ℝ≥0∞) = o'.1 ∧ 𝔰 ≤ CycScheme.hOf P sc (ρ, false) ∧ (𝔰 : ℝ) ≤ β ∧
      ((𝔰 : ℝ≥0) : ℝ≥0∞) ≤ CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) := by
  have hsh : 𝔰 ≤ CycScheme.hOf P sc (ρ, false) := CycSchemeEnv.sStar_le_h _
  refine ⟨CycSchemeEnv.sStar_eq_of_le_h _ hg.le_h, hsh, ?_, ?_⟩
  · exact (by exact_mod_cast hsh : (𝔰 : ℝ) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycScheme.hOf_le_beta P sc _)
  · exact (by exact_mod_cast hsh : ((𝔰 : ℝ≥0) : ℝ≥0∞) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycSchemeEnv.hOf_le_hFr ρ)

omit [Countable I] [MeasurableSingletonClass I] in
/-- A fresh atom at the entrance time forces the revealed measure to be nonzero. -/
theorem atom_end_ne_zero (hj : ∀ k, Measurable (jx k)) (h : GAt P (drl P jx Ñ) k r ρ)
    (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') {v : Dir d} (hs0 : 0 < 𝔰)
    (hat : AtomAt P jx Ñ k r v 𝔰)
    (hfresh : CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) 𝔰 ∉
      ρ.region β) : 𝒪.2 Set.univ ≠ 0 := by
  obtain ⟨hs, hsh, -, -⟩ := sStar_facts j0 hg
  have hR := probeR_qpt j0 h v hs0 hsh (sc := sc)
  rw [ite_eq_right hfresh] at hR
  have h1 : o'.2 {qpt P jx Ñ k r v 𝔰} = Ñ {qpt P jx Ñ k r v 𝔰} :=
    V_apply_of_le j0 hg (by rw [hR, hs])
  refine (psiOut_univ_ne_zero_iff j0 hj h hg).2 fun h0 => hat ?_
  rw [← h1]
  exact measure_mono_null (Set.subset_univ _) h0

omit [Countable I] [MeasurableSingletonClass I] in
/-- The path does not move before the entrance time when its left limit is `p(r)`. -/
theorem drv_hstep
    (hgood : ∀ j, relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') :
    ∀ t, r < t → t < r + 𝔰 → (gpth P (drl P jx Ñ) k).1.left t =
      (gpth P (drl P jx Ñ) k).1.fn r → (gpth P (drl P jx Ñ) k).1.fn t =
        (gpth P (drl P jx Ñ) k).1.left t := by
  have hgo := hgood (gj P jx Ñ k)
  obtain ⟨hs, hsh, hsβ, hsFr⟩ := sStar_facts j0 hg
  set s := 𝔰 with hsdef
  have hpos : (CycScheme.cur P (ρ, false)).pos = (gpth P (drl P jx Ñ) k).1.fn r := h.pos false
  intro t hrt hts hl
  obtain ⟨u, rfl⟩ : ∃ u, t = r + u := ⟨t - r, (add_tsub_cancel_of_le hrt.le).symm⟩
  have hu0 : 0 < u := by
    rcases eq_zero_or_pos u with h0 | h0
    · rw [h0, add_zero] at hrt; exact absurd hrt (lt_irrefl _)
    · exact h0
  have hus : u < s := lt_of_add_lt_add_left hts
  have hubβ : (u : ℝ) ≤ β := (by exact_mod_cast hus.le : (u : ℝ) ≤ s).trans hsβ
  have hnr : NoRing P ρ ((gpth P (drl P jx Ñ) k).1.fn r) u := by
    intro e he hm
    have hle := CycScheme.hFr_le_of_front ρ (CycScheme.cur P (ρ, false))
      (e := e) (t := u) ⟨by exact_mod_cast hu0, hubβ⟩ (by rw [hpos]; exact he) hm
    have : ((u : ℝ≥0) : ℝ≥0∞) < ((s : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hus
    exact absurd (lt_of_le_of_lt hle (lt_of_lt_of_le this hsFr)) (lt_irrefl _)
  have hno : ∀ v : Dir d, AtomAt P jx Ñ k r v u →
      CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) u ∈ ρ.region β :=
    fun v hv => early_drv j0 h hg v hu0 (by rw [← hs]; exact_mod_cast hus) hv
  rw [hl]
  exact rule_stay_gAt hgo h hu0 hubβ hl hnr hno

/-- The three situations at the end of a step. -/
theorem step_end (hj : ∀ k, Measurable (jx k))
    (hgood : ∀ j, relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') :
    (((𝔰 : ℝ≥0) : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ∧ 0 < 𝔰 ∧
      ∃ e1 : Edge d, Edge.Mem ((gpth P (drl P jx Ñ) k).1.fn r) e1 ∧
        CycScheme.newV P sc (ρ, false) 𝒪 = edgeOther ((gpth P (drl P jx Ñ) k).1.fn r) e1 ∧
        (gpth P (drl P jx Ñ) k).1.fn (r + 𝔰) = edgeOther ((gpth P (drl P jx Ñ) k).1.fn r) e1) ∨
    (((𝔰 : ℝ≥0) : ℝ≥0∞) ≠ CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ∧
      𝒪.2 Set.univ ≠ 0 ∧ 0 < 𝔰 ∧ ∃ v : Dir d,
        CycScheme.newV P sc (ρ, false) 𝒪 = (gpth P (drl P jx Ñ) k).1.fn r + v.vec ∧
        (gpth P (drl P jx Ñ) k).1.fn (r + 𝔰) = (gpth P (drl P jx Ñ) k).1.fn r + v.vec) ∨
    (((𝔰 : ℝ≥0) : ℝ≥0∞) ≠ CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ∧
      𝒪.2 Set.univ = 0 ∧
      CycScheme.newV P sc (ρ, false) 𝒪 = (gpth P (drl P jx Ñ) k).1.fn r ∧
      (gpth P (drl P jx Ñ) k).1.fn (r + 𝔰) = (gpth P (drl P jx Ñ) k).1.fn r) := by
  classical
  have hgo := hgood (gj P jx Ñ k)
  obtain ⟨hs, hsh, hsβ, hsFr⟩ := sStar_facts j0 hg
  set o := 𝒪 with ho
  set s := 𝔰 with hsdef
  have hpos : (CycScheme.cur P (ρ, false)).pos = (gpth P (drl P jx Ñ) k).1.fn r := h.pos false
  have hstep := drv_hstep j0 hgood h hg
  have hleft : 0 < s → (gpth P (drl P jx Ñ) k).1.left (r + s) =
      (gpth P (drl P jx Ñ) k).1.fn r := fun hs0 => left_eq_of_step hs0 hstep
  by_cases hF : ((s : ℝ≥0) : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false))
  · left
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · exfalso
        rw [h0] at hF
        exact hFr_ne_zero' h (by simpa using hF.symm)
      · exact h0
    obtain ⟨e0, he0, hring⟩ := ringSet_front_of_hFr' h hs0 hsh hF
    obtain ⟨e1, hlq, -⟩ := CycSchemeEnv.leastEdge_spec
      (Q := fun e => Edge.Mem (CycScheme.cur P (ρ, false)).pos e ∧
        ((CycScheme.cur P (ρ, false)).data.copy, (e, (CycScheme.cur P (ρ, false)).data.clock β
          ((CycScheme.cur P (ρ, false)).time + s))) ∈ ρ.ringSet β) ⟨e0, he0, hring⟩
    obtain ⟨hQ, hmin⟩ := leastEdge_min hlq
    have he1 : Edge.Mem ((gpth P (drl P jx Ñ) k).1.fn r) e1 := by rw [← hpos]; exact hQ.1
    refine ⟨hF, hs0, e1, he1, ?_, ?_⟩
    · unfold CycScheme.newV
      rw [ite_eq_left hF]
      have hfe : CycScheme.forcedEdge P (ρ, false) s = some e1 := hlq
      rw [hfe]
      show edgeOther (CycScheme.cur P (ρ, false)).pos e1 = _
      rw [hpos]
    · exact rule_ring_gAt h hs0 hsβ (hleft hs0) he1 hQ.2 fun e' he' hm' =>
        hmin e' ⟨by rw [hpos]; exact he', hm'⟩
  · have hsFr' : ((s : ℝ≥0) : ℝ≥0∞) < CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) :=
      lt_of_le_of_ne hsFr hF
    by_cases hz : o.2 Set.univ = 0
    · right; right
      have hV0 : o.2 = 0 := Measure.measure_univ_eq_zero.1 hz
      have hfe : CycScheme.freshEdge P sc (ρ, false) o = none := by
        unfold CycScheme.freshEdge; rw [hV0, CycSchemeEnv.atomMap_zero]
      have hnv : CycScheme.newV P sc (ρ, false) o = (gpth P (drl P jx Ñ) k).1.fn r := by
        unfold CycScheme.newV
        rw [ite_eq_right hF]
        dsimp only
        rw [hfe]
        exact hpos
      refine ⟨hF, hz, hnv, ?_⟩
      rcases eq_zero_or_pos s with h0 | hs0
      · rw [h0, add_zero]
      · have hnr : NoRing P ρ ((gpth P (drl P jx Ñ) k).1.fn r) s := by
          intro e he hm
          have hle := CycScheme.hFr_le_of_front ρ (CycScheme.cur P (ρ, false))
            (e := e) (t := s) ⟨by exact_mod_cast hs0, hsβ⟩ (by rw [hpos]; exact he) hm
          exact absurd (lt_of_le_of_lt hle hsFr') (lt_irrefl _)
        refine rule_stay_gAt hgo h hs0 hsβ (hleft hs0) hnr fun v hv => ?_
        by_contra hfresh
        exact atom_end_ne_zero j0 hj h hg hs0 hv hfresh hz
    · right; left
      obtain ⟨v, t, ht0, hth, hfresh, hto, hat, hd⟩ :=
        dirac_data j0 hj h hg ((psiOut_univ_ne_zero_iff j0 hj h hg).1 hz)
      have hst : s = t := by
        have := hs.trans hto
        exact_mod_cast this
      subst hst
      have hs0 := ht0
      have hnr : NoRing P ρ ((gpth P (drl P jx Ñ) k).1.fn r) s := by
        intro e he hm
        have hle := CycScheme.hFr_le_of_front ρ (CycScheme.cur P (ρ, false))
          (e := e) (t := s) ⟨by exact_mod_cast hs0, hsβ⟩ (by rw [hpos]; exact he) hm
        exact absurd (lt_of_le_of_lt hle hsFr') (lt_irrefl _)
      have hnv : CycScheme.newV P sc (ρ, false) o =
          (gpth P (drl P jx Ñ) k).1.fn r + v.vec := by
        have hfe : CycScheme.freshEdge P sc (ρ, false) o =
            some (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) := by
          unfold CycScheme.freshEdge
          rw [hd, SepPartSeq.atomMap_dirac]
          have ho0 : 0 < o.1 := by
            show 0 < o'.1
            rw [hto]; exact_mod_cast ht0
          dsimp only
          rw [ite_eq_left ⟨ho0, hg.le_h, rfl, rfl, by rw [hpos]; exact mem_stepEdge _ _, hfresh⟩]
          rfl
        unfold CycScheme.newV
        rw [ite_eq_right hF]
        dsimp only
        rw [hfe]
        dsimp only
        rw [hpos]
        exact CycSchemeEnv.edgeOther_eq rfl
      refine ⟨hF, hz, hs0, v, hnv, ?_⟩
      exact rule_jump_gAt hgo h hs0 hsβ (hleft hs0) hnr hat hfresh

end CycSchemeGen
end ElboimSly.Cyclic

end
