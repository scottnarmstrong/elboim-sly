/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWCore
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: no atom is read in the explored region

ES22 Lemma 5.5, Step 1, "Agreement on `E₅₆ ∩ E₀`", cases (i) and (ii).

* `pw_Z1`: a point of the explored region read by `P̃` before `t_*` is not an atom of `Ñ`
  (an atom would make `P̃` jump to a vertex that is not in `B⁻`, since every point of the explored
  region has an endpoint outside `B⁻`);
* `pw_Z2`: such a point is not an atom of `ν` either (the only candidates are `x_ent`, `x_ex`, and
  reading them contradicts `E₅₆`, using that `P̃` does not jump at the times `kβ` by `G2`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

section core

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {j : ℕ} {u : EscV k} {ν Ñ : Measure (CycS ℕ (k + 2) β)}
  {R : Set (CycS ℕ (k + 2) β)} {v w : EscV k} {ξ tstar : ℝ} {c : AddCircle β}

theorem pw_clock (v : EscV k) (ξ : ℝ) (s : ℝ≥0) :
    CycData.clock β (((0 : ℕ), v, ξ, true) : CycData ℕ (k + 2)) s = (((ξ + s : ℝ)) : AddCircle β) := by
  simp [CycData.clock, CycData.sgn, CycData.fwd, CycData.phase]

theorem pw_Z1 (hÑ : CycGood Ñ) (hP : PWPath β j u v w tstar (envPath Ñ ((0 : ℕ), v, ξ, true)))
    (hReg : PWReg j u ν R v w ξ c) {r : ℝ≥0} (hr : (r : ℝ) ≤ tstar) {x : CycS ℕ (k + 2) β}
    (hx : x ∈ CycEntry.region β ((((0 : ℕ), v, ξ, true) : CycData ℕ (k + 2)),
      (envPath Ñ ((0 : ℕ), v, ξ, true)).cut (r : ℝ≥0∞))) (hxR : x ∈ R) : Ñ {x} = 0 := by
  set δ : CycData ℕ (k + 2) := ((0 : ℕ), v, ξ, true) with hδ
  set Pt := envPath Ñ δ with hPt
  rcases pw_atom_zero_or_one hÑ x with h0 | h1
  · exact h0
  exfalso
  obtain ⟨r', hr'0, hr'l, hx1, hx2, hxm⟩ := (pw_mem_region_cut δ Pt _ x).1 hx
  have hr'r : r' ≤ r := by exact_mod_cast hr'l
  have hr't : (r' : ℝ) ≤ tstar := le_trans (by exact_mod_cast hr'r) hr
  have hleft := pw_left_mem hP.mem hr'0 hr't
  have hfn := hP.mem r' hr't
  have hgood : Good (cycSlice δ.copy Ñ) := hÑ δ.copy
  have hxeq : x = (δ.copy, (x.2.1, δ.clock β r')) := Prod.ext hx1 (Prod.ext rfl hx2)
  have hsw := (envPath_swap hgood hr'0).1 x.2.1 hxm (by rw [← hxeq, h1])
  obtain ⟨q, hq, hqB⟩ := hReg.out x hxR
  have hq' : q ∈ s(Pt.1.left r', Pt.1.fn r') := by rw [← hsw]; exact hq
  rcases Sym2.mem_iff.1 hq' with rfl | rfl
  · exact hqB hleft
  · exact hqB hfn

theorem pw_Z2 (hj : 1 ≤ j) (hν : CycGood ν) (hÑ : CycGood Ñ)
    (hP : PWPath β j u v w tstar (envPath Ñ ((0 : ℕ), v, ξ, true)))
    (hReg : PWReg j u ν R v w ξ c) (hÑR : ∀ x ∉ R, Ñ {x} = ν {x})
    (hphase : (((ξ + tstar : ℝ)) : AddCircle β) = c) {r : ℝ≥0} (hr : (r : ℝ) < tstar)
    {x : CycS ℕ (k + 2) β}
    (hx : x ∈ CycEntry.region β ((((0 : ℕ), v, ξ, true) : CycData ℕ (k + 2)),
      (envPath Ñ ((0 : ℕ), v, ξ, true)).cut (r : ℝ≥0∞))) (hxR : x ∈ R) : ν {x} = 0 := by
  set δ : CycData ℕ (k + 2) := ((0 : ℕ), v, ξ, true) with hδ
  set Pt := envPath Ñ δ with hPt
  rcases pw_atom_zero_or_one hν x with h0 | h1
  · exact h0
  exfalso
  obtain ⟨r', hr'0, hr'l, hx1, hx2, hxm⟩ := (pw_mem_region_cut δ Pt _ x).1 hx
  have hr'r : r' ≤ r := by exact_mod_cast hr'l
  have hr't : (r' : ℝ) ≤ tstar := le_trans (by exact_mod_cast hr'r) hr.le
  have hleft := pw_left_mem hP.mem hr'0 hr't
  have hgood : Good (cycSlice δ.copy Ñ) := hÑ δ.copy
  have hclock := pw_clock (β := β) v ξ r'
  rcases hReg.atoms x hxR h1.ge _ hleft hxm with ⟨hzv, hxc, a, haB, hxa⟩ | ⟨hzw, hxc⟩
  · -- case (i): the entrance atom
    have hcirc : (((ξ + r' : ℝ)) : AddCircle β) = ((ξ : ℝ) : AddCircle β) := by
      rw [← hclock, ← hx2, hxc]
    have hβr : β ≤ (r' : ℝ) := by
      have := pw_circle_ge hcirc (by have : (0 : ℝ) < r' := hr'0; linarith)
      linarith
    have hfn : Pt.1.fn r' = v := by
      by_contra hne
      have hswap := envPath_swap hgood hr'0
      have hex : ∃ e' : Edge (k + 2), Edge.Mem (Pt.1.left r') e' ∧
          1 ≤ Ñ {(δ.copy, (e', δ.clock β r'))} := by
        by_contra hno
        exact hne (by rw [hswap.2 hno, hzv])
      obtain ⟨e', he', hat'⟩ := hex
      have hsw' := hswap.1 e' he' hat'
      by_cases hx'R : ((δ.copy, (e', δ.clock β r')) : CycS ℕ (k + 2) β) ∈ R
      · have hreg' : ((δ.copy, (e', δ.clock β r')) : CycS ℕ (k + 2) β) ∈
            CycEntry.region β (δ, Pt.cut (r : ℝ≥0∞)) :=
          (pw_mem_region_cut δ Pt _ _).2 ⟨r', hr'0, by exact_mod_cast hr'r, rfl, rfl, he'⟩
        have := pw_Z1 hÑ hP hReg hr.le hreg' hx'R
        rw [this] at hat'
        simp at hat'
      · have hν' : 1 ≤ ν {((δ.copy, (e', δ.clock β r')) : CycS ℕ (k + 2) β)} := by
          rw [← hÑR _ hx'R]; exact hat'
        have hne_e : x.2.1 ≠ e' := by
          intro heq
          have h1 : x.2.1.1 = e'.1 := congrArg Subtype.val heq
          rw [hxa, hsw', hzv] at h1
          have hvB : v ∈ escBlock j u :=
            blockMinus_subset_block hj (hzv ▸ hleft)
          have hfB : Pt.1.fn r' ∈ escBlock j u :=
            blockMinus_subset_block hj (hP.mem r' hr't)
          rcases Sym2.eq_iff.1 h1 with ⟨h2, -⟩ | ⟨h2, -⟩
          · exact haB (h2 ▸ hvB)
          · exact haB (h2 ▸ hfB)
        have hdis := (hν δ.copy).2.2.1.2 x.2.1 e' hne_e
        have hA : δ.clock β r' ∈ ringSet (cycSlice δ.copy ν) x.2.1 := by
          show 1 ≤ cycSlice δ.copy ν {(x.2.1, δ.clock β r')}
          rw [cycSlice_singleton]
          have : ((δ.copy, (x.2.1, δ.clock β r')) : CycS ℕ (k + 2) β) = x :=
            Prod.ext hx1.symm (Prod.ext rfl hx2.symm)
          rw [this]; exact h1.ge
        have hB : δ.clock β r' ∈ ringSet (cycSlice δ.copy ν) e' := by
          show 1 ≤ cycSlice δ.copy ν {(e', δ.clock β r')}
          rw [cycSlice_singleton]; exact hν'
        exact Set.disjoint_left.1 hdis hA hB
    exact hP.ne_v r' hβr hr't (by rw [hfn])
  · -- case (ii): the exit atom
    have hcirc : (((ξ + tstar : ℝ)) : AddCircle β) = ((ξ + r' : ℝ) : AddCircle β) := by
      rw [hphase, ← hxc, hx2, hclock]
    have hle : ξ + r' + β ≤ ξ + tstar := pw_circle_ge hcirc (by linarith)
    obtain ⟨s, hsr, hs⟩ := pw_left_eq_fn (Pt := Pt) hr'0
    refine hP.ne_w s ?_ (by rw [hs, hzw])
    have : (s : ℝ) < r' := by exact_mod_cast hsr
    linarith

end core

end ElboimSly.Paper.Escape
