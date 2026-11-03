/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCore
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPath
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# The environment scheme (b): the new vertex is the environment path at `r + s*`

The environment scheme (b) (i), (ii). For a good `ν`, a record with `EnvAt` and a good
outcome (`StepGood`), the environment path is constant on `[r, r + s*)` with left limit `p(r)`
at `r + s*` (`quiet_facts`), and the new vertex `CycScheme.newV` (forced, fresh or no event) is
`p(r + s*)` (`newV_eq`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable {P : CycPlan I d β} {sc : ℝ≥0∞} {ν : Measure (I × RingSpace d β)}
variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

theorem leastEdge_spec {Q : Edge d → Prop} (hQ : ∃ e, Q e) : ∃ e, leastEdge Q = some e ∧ Q e := by
  classical
  have hS : {n | ∃ e, Q e ∧ n = edgeEnc e}.Nonempty := by
    obtain ⟨e, he⟩ := hQ; exact ⟨_, e, he, rfl⟩
  obtain ⟨e0, he0, h3⟩ := Nat.sInf_mem hS
  have hex : ∃ e, Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e' :=
    ⟨e0, he0, fun e' he' => by rw [← h3]; exact Nat.sInf_le ⟨e', he', rfl⟩⟩
  refine ⟨hex.choose, ?_, hex.choose_spec.1⟩
  unfold leastEdge
  rw [dite_eq_left hex]

theorem atomMap_zero {d : ℕ} {β : ℝ} [Fact (0 < β)] :
    (cycSeq I d β).atomMap (0 : Measure (CycS I d β)) = Sum.inr () := by
  refine SepPartSeq.atomMap_of_not_mem _ fun hmem => ?_
  obtain ⟨x, hx⟩ := SepPartSeq.mem_diracSet_iff.1 hmem
  have := congrArg (fun m : Measure (CycS I d β) => m Set.univ) hx
  simp at this

omit [Countable I] [MeasurableSingletonClass I] in
theorem ringSet_front_of_hFr (h : EnvAt P ν k r ρ) {s : ℝ≥0} (hs0 : 0 < s)
    (hsh : s ≤ CycScheme.hOf P sc (ρ, false))
    (hs : (s : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false))) :
    ∃ e0, Edge.Mem (CycScheme.cur P (ρ, false)).pos e0 ∧ fp P ρ e0 s ∈ ρ.ringSet β := by
  have hsβ : (s : ℝ) ∈ Ioc 0 β :=
    ⟨by exact_mod_cast hs0, (by exact_mod_cast hsh : (s : ℝ) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycScheme.hOf_le_beta P sc _)⟩
  rcases CycScheme.hFr_attained ρ (CycScheme.cur P (ρ, false)) h.finite_clocks with htop | ⟨x, hx, h1, h2, h3⟩
  · rw [← hs] at htop; exact absurd htop ENNReal.coe_ne_top
  · refine ⟨x.2.1, h2, ?_⟩
    have hc : circS (CycScheme.cur P (ρ, false)).frontT (CycScheme.cur P (ρ, false)).frontS
        (x.1, x.2.1) x.2.2 = s := by
      have hpos := (CycScheme.circS_mem_Ioc (CycScheme.cur P (ρ, false)) (x.1, x.2.1) x.2.2).1
      have h4 : (s : ℝ≥0∞) = ENNReal.ofReal (circS (CycScheme.cur P (ρ, false)).frontT
          (CycScheme.cur P (ρ, false)).frontS (x.1, x.2.1) x.2.2) := hs.trans h3
      have h5 := congrArg ENNReal.toReal h4
      rw [ENNReal.toReal_ofReal hpos.le] at h5
      simpa using h5.symm
    have hx2 : x.2.2 = (CycScheme.cur P (ρ, false)).data.clock β
        ((CycScheme.cur P (ρ, false)).time + s) := by
      have h6 := circX_sinv (CycScheme.cur P (ρ, false)).frontT (CycScheme.cur P (ρ, false)).frontS
        (CycScheme.cur P (ρ, false)).frontS_cases (x.1, x.2.1) x.2.2
      rw [hc] at h6
      exact h6.symm.trans (CycEntry.circX_front (CycScheme.cur P (ρ, false)) (x.1, x.2.1) s)
    have : fp P ρ x.2.1 s = x := by
      unfold fp CycScheme.frontPt
      exact Prod.ext h1.symm (Prod.ext rfl hx2.symm)
    rw [this]; exact hx

omit [Countable I] in
theorem fresh_conv (_hν : CycGood ν) (_h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hz : o.2 Set.univ ≠ 0) :
    ∃ e1, Edge.Mem (CycScheme.cur P (ρ, false)).pos e1 ∧
      0 < CycScheme.sStar P sc (ρ, false) o ∧
      ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) = o.1 ∧
      o.2 = Measure.dirac (fp P ρ e1 (CycScheme.sStar P sc (ρ, false) o)) ∧
      fp P ρ e1 (CycScheme.sStar P sc (ρ, false) o) ∉ ρ.region β ∧
      1 ≤ ν ({fp P ρ e1 (CycScheme.sStar P sc (ρ, false) o)} : Set _) := by
  obtain ⟨x, hVx, hRm⟩ := hg.dirac hz
  have hxr : x ∉ ρ.region β := by
    intro hx
    have : Rm P sc ρ x = ⊤ := by unfold Rm; rw [ite_eq_left hx]
    rw [this] at hRm
    exact absurd (hg.le_h) (by rw [← hRm]; simp)
  have hR : CycScheme.probeR P sc (ρ, false) x = o.1 := by
    have := hRm; unfold Rm at this; rwa [ite_eq_right hxr] at this
  have hne : CycScheme.probeR P sc (ρ, false) x ≠ ⊤ := by
    rw [hR]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top hg.le_h
  obtain ⟨e1, t1, hx, hmem, ht0, hth, hRt⟩ := CycScheme.front_of_probeR_ne_top P sc (rfl : (ρ, false).2 = false) hne
  have hs : (CycScheme.sStar P sc (ρ, false) o : ℝ≥0∞) = o.1 := sStar_eq_of_le_h o hg.le_h
  have hst : CycScheme.sStar P sc (ρ, false) o = t1 := by
    have : (CycScheme.sStar P sc (ρ, false) o : ℝ≥0∞) = t1 := by rw [hs, ← hR, hRt]
    exact_mod_cast this
  have hxfp : x = fp P ρ e1 (CycScheme.sStar P sc (ρ, false) o) := by rw [hst]; exact hx
  refine ⟨e1, hmem, by rw [hst]; exact ht0, hs, by rw [hVx, hxfp], by rw [← hxfp]; exact hxr, ?_⟩
  rw [← hxfp]
  have h1 : o.2 {x} = ν {x} := V_apply_of_mem hg hRm.le
  rw [hVx, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at h1
  rw [← h1]

omit [Countable I] [MeasurableSingletonClass I] in
theorem fp_eq (h : EnvAt P ν k r ρ) (e : Edge d) (t : ℝ≥0) :
    fp P ρ e t = ((dat P ν k).copy, (e, (dat P ν k).clock β (r + t))) := by
  unfold fp CycScheme.frontPt
  rw [h.data, h.time]

omit [Countable I] in
theorem swap_rules (hν : CycGood ν) (k : ℕ) :
    QuietRule (pth P ν k).1
      (fun t e => 1 ≤ ν {((dat P ν k).copy, (e, (dat P ν k).clock β t))}) ∧
    RingRule (pth P ν k).1
      (fun t e => 1 ≤ ν {((dat P ν k).copy, (e, (dat P ν k).clock β t))}) :=
  ⟨fun _t ht hn => (envPath_swap (hν (dat P ν k).copy) ht).2 hn,
    fun _t ht e he hA => (envPath_swap (hν (dat P ν k).copy) ht).1 e he hA⟩

theorem quiet_facts (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    (∀ t, r ≤ t → t < r + CycScheme.sStar P sc (ρ, false) o →
        (pth P ν k).1.fn t = (pth P ν k).1.fn r) ∧
      (0 < CycScheme.sStar P sc (ρ, false) o →
        (pth P ν k).1.left (r + CycScheme.sStar P sc (ρ, false) o) = (pth P ν k).1.fn r) := by
  have hq : ∀ t, r < t → t < r + CycScheme.sStar P sc (ρ, false) o → ∀ e,
      Edge.Mem ((pth P ν k).1.fn r) e →
        ¬ (1 ≤ ν {((dat P ν k).copy, (e, (dat P ν k).clock β t))}) := by
    intro t hrt hts e he hA
    have ht0 : 0 < t - r := tsub_pos_of_lt hrt
    have hts' : ((t - r : ℝ≥0) : ℝ≥0∞) < CycScheme.sStar P sc (ρ, false) o := by
      have : t - r < CycScheme.sStar P sc (ρ, false) o := by
        rw [tsub_lt_iff_left hrt.le]; exact hts
      exact_mod_cast this
    have he' : Edge.Mem (CycScheme.cur P (ρ, false)).pos e := by rw [h.pos]; exact he
    have := claimA hν h hg he' ht0 hts'
    change ν ({fp P ρ e (t - r)} : Set _) = 0 at this
    rw [fp_eq h, add_tsub_cancel_of_le hrt.le] at this
    rw [this] at hA
    exact absurd hA (by simp)
  exact ⟨fun t h1 h2 => fn_eq_of_quiet (swap_rules hν k).1 (fun t h3 h4 e he => hq t h3 h4 e he) t h1 h2,
    fun hs => left_eq_of_quiet (swap_rules hν k).1 hs (fun t h3 h4 e he => hq t h3 h4 e he)⟩

omit [Countable I] [MeasurableSingletonClass I] in
theorem hFr_ne_zero (h : EnvAt P ν k r ρ) :
    CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ≠ 0 := by
  rcases CycScheme.hFr_attained ρ (CycScheme.cur P (ρ, false)) h.finite_clocks with htop | ⟨x, hx, h1, h2, h3⟩
  · rw [htop]; exact ENNReal.top_ne_zero
  · rw [h3]
    have hpos := (CycScheme.circS_mem_Ioc (CycScheme.cur P (ρ, false)) (x.1, x.2.1) x.2.2).1
    exact (ENNReal.ofReal_pos.2 hpos).ne'

theorem newV_eq (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    CycScheme.newV P sc (ρ, false) o =
      (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) := by
  classical
  set s := CycScheme.sStar P sc (ρ, false) o with hsdef
  have hsh : s ≤ CycScheme.hOf P sc (ρ, false) := sStar_le_h o
  obtain ⟨hconst, hleft⟩ := quiet_facts hν h hg
  have hpos : (CycScheme.cur P (ρ, false)).pos = (pth P ν k).1.fn r := h.pos false
  unfold CycScheme.newV
  by_cases hF : (s : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false))
  · have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · exfalso
        rw [h0] at hF
        exact hFr_ne_zero h (by simpa using hF.symm)
      · exact h0
    obtain ⟨e0, he0, hring⟩ := ringSet_front_of_hFr h hs0 hsh hF
    obtain ⟨e1, hlq, hQ⟩ := leastEdge_spec
      (Q := fun e => Edge.Mem (CycScheme.cur P (ρ, false)).pos e ∧
        ((CycScheme.cur P (ρ, false)).data.copy, (e, (CycScheme.cur P (ρ, false)).data.clock β
          ((CycScheme.cur P (ρ, false)).time + s))) ∈ ρ.ringSet β) ⟨e0, he0, hring⟩
    rw [ite_eq_left hF]
    have hfe : CycScheme.forcedEdge P (ρ, false) s = some e1 := hlq
    rw [hfe]
    show edgeOther (CycScheme.cur P (ρ, false)).pos e1 = _
    rw [hpos]
    have he1 : Edge.Mem ((pth P ν k).1.fn r) e1 := by rw [← hpos]; exact hQ.1
    have hA : 1 ≤ ν {((dat P ν k).copy, (e1, (dat P ν k).clock β (r + s)))} := by
      have hy : fp P ρ e1 s ∈ ρ.region β := ringSet_subset_region ρ hQ.2
      have := (h.atom_iff_ring hν hy).2 hQ.2
      rwa [fp_eq h] at this
    exact (fn_end_ring (swap_rules hν k).2 hs0 (hleft hs0) he1 hA).symm
  · rw [ite_eq_right hF]
    dsimp only
    by_cases hz : o.2 Set.univ = 0
    · have hV0 : o.2 = 0 := Measure.measure_univ_eq_zero.1 hz
      have hfe : CycScheme.freshEdge P sc (ρ, false) o = none := by
        unfold CycScheme.freshEdge; rw [hV0, atomMap_zero]
      rw [hfe]
      dsimp only
      rw [hpos]
      by_cases hs0 : 0 < s
      · symm
        refine fn_end_quiet (swap_rules hν k).1 hs0 (hleft hs0) ?_
        intro e he hA
        have he' : Edge.Mem (CycScheme.cur P (ρ, false)).pos e := by rw [hpos]; exact he
        have hA' : 1 ≤ ν ({fp P ρ e s} : Set _) := by rw [fp_eq h]; exact hA
        rcases atom_end hν h hg he' hs0 hA' with ⟨_, hh⟩ | ⟨_, hne⟩
        · exact hF hh
        · exact hne hz
      · have : s = 0 := by simpa using hs0
        rw [this, add_zero]
    · obtain ⟨e1, he1, hs0, hs, hVd, hnr, hat⟩ := fresh_conv hν h hg hz
      have hfe : CycScheme.freshEdge P sc (ρ, false) o = some e1 := by
        unfold CycScheme.freshEdge
        rw [hVd, SepPartSeq.atomMap_dirac]
        have ho0 : 0 < o.1 := by rw [← hs]; exact_mod_cast hs0
        dsimp only
        rw [ite_eq_left ⟨ho0, hg.le_h, rfl, rfl, he1, hnr⟩]
        rfl
      rw [hfe]
      dsimp only
      rw [hpos]
      have he1' : Edge.Mem ((pth P ν k).1.fn r) e1 := by rw [← hpos]; exact he1
      have hA : 1 ≤ ν {((dat P ν k).copy, (e1, (dat P ν k).clock β (r + s)))} := by
        rw [← fp_eq h]; exact hat
      exact (fn_end_ring (swap_rules hν k).2 hs0 (hleft hs0) he1' hA).symm

end CycSchemeEnv
end ElboimSly.Cyclic

end
