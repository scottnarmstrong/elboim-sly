/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWClose4
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the closing argument, `Con_i`

ES22 Lemma 5.5, Step 1, "Conclusion of Step 1".

`pwc_conSet`: from the agreement of `Ŵ = W^{N¹}` with the continuation `P̃` on `[ξ_B, t' - r_i)`,
the event `E₅₆` for `P̃` (`PWPath`), `𝒦(β')`, the geometry of the backward entry (in `𝒬` before
`r_i`, exit value `w`), and the absence of rings at `p_i` at `[β']`, conclude
`t' < t_reg` and `W(t') = p_i`, i.e. `ν ∈ Con_i`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- **The closing argument of Step 1 of ES22 Lemma 5.5.**

Data: `ν` a good environment; `𝒦(β')` for `ν`; `p = p_i ∈ 𝒬`; no edge at `p` rings at `β'` in the
first slice; the backward environment path `P^ν_{(0,p,β',-1)}` stays in `𝒬` at its left limits at
times `≤ r`, and has value `w` at `r`; the continuation `Pt` (the walk `P̃_c`) starts at `v`,
satisfies `PWPath` on `[0, t_*]` with `t_* = t' - r - ξ_B > 0`, equals `Ŵ(ξ_B + ·)` on `[0, t_*)`
and is `w` just before `t_*`. -/
theorem pwc_conSet {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {n : ℕ} {u : EscV k}
    {tn : ℝ} {β' i : ℕ} (hj : 3 ≤ escJ n) (hadm : EscAdmissible (escJ n) u)
    (hKev : EscK β tn (escJ n) (escBlockMinus (escJ n) u) (escWalk ν)
      (escXi (escWalk ν) (escBlock (escJ n) u)) (cycTreg (copyEnv ν 0)) β')
    (hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u)
    (hring : ¬ ∃ e : Edge (k + 2), e.Mem (escPoint n (escJ n) u i) ∧
      Rings (cycSlice 0 ν) e (β' : ℝ))
    {v w : EscV k} {r : ℝ≥0}
    (hbw : (envPath ν ((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false)).1.fn r = w)
    (hbQ : ∀ s : ℝ≥0, 0 < s → s ≤ r →
      (envPath ν ((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false)).1.left s ∈
        escQ (escJ n) u)
    {tstar : ℝ} {Pt : CycPath (k + 2)}
    (hts : tstar = cycFloor β ((escXi (escWalk ν) (escBlock (escJ n) u)).toReal + 4 ^ escJ n)
      - r - (escXi (escWalk ν) (escBlock (escJ n) u)).toReal)
    (htspos : 0 < tstar)
    (hP : PWPath β (escJ n) u v w tstar Pt) (hPt0 : Pt.1.fn 0 = v)
    (hagree : ∀ s : ℝ≥0, (s : ℝ) < tstar →
      cycWalk (copyEnv ν 0) 0 0
        ((escXi (escWalk ν) (escBlock (escJ n) u)).toReal + s) = Pt.1.fn s)
    (hlim : ∃ l : ℝ, l < tstar ∧ ∀ s : ℝ≥0, l < s → (s : ℝ) < tstar → Pt.1.fn s = w) :
    ν ∈ escConSet β n u i := by
  classical
  have hβ : 0 < β := Fact.out
  set j := escJ n with hjdef
  set ξ := escXi (escWalk ν) (escBlock j u) with hξdef
  obtain ⟨hξtn, hξtreg, hWB, hphase⟩ := hKev
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hξtn
  set ξr : ℝ := ξ.toReal with hξr
  have hξr0 : 0 ≤ ξr := ENNReal.toReal_nonneg
  set tp : ℝ := cycFloor β (ξr + 4 ^ j) with htp
  set p := escPoint n j u i with hpdef
  have hμ : Good (cycSlice 0 ν) := hν 0
  have hcopy : copyEnv ν 0 = cycSlice 0 ν := copyEnv_eq_cycSlice ν 0
  rw [hcopy] at hξtreg hagree
  have hWh : ∀ x, 0 ≤ x → cycWalk (cycSlice 0 ν) 0 0 x = fwdTraj hμ 0 0 x := by
    intro x hx
    rw [cycWalk_of_nonneg hμ 0 0 hx, zero_add]
  have hagree' : ∀ s : ℝ≥0, (s : ℝ) < tstar → fwdTraj hμ 0 0 (ξr + s) = Pt.1.fn s := by
    intro s hs
    rw [← hWh _ (by positivity)]
    exact hagree s hs
  -- the phase
  set m : ℤ := ⌊tp / β⌋ with hm
  have ht' : tp = (β' : ℝ) + m * β := by
    have : cycIntPhase β tp = β' := hphase
    unfold cycIntPhase at this
    linarith
  have hr0 : 0 ≤ (r : ℝ) := r.2
  have hrt : (r : ℝ) < tp := by linarith
  -- the backward entry
  have hη : ∃ a0 < (β' : ℝ) - r, ∀ τ ∈ Ioo a0 ((β' : ℝ) - r),
      bwdTraj hμ p (β' : ℝ) τ = w := by
    obtain ⟨a0, ha0, h⟩ := pwc_bwd_eventually hν p (β' : ℝ) hring r
    exact ⟨a0, ha0, fun τ hτ => (h τ hτ).trans hbw⟩
  have hW : ∃ s0 < tp - r, ∀ s ∈ Ioo s0 (tp - r), fwdTraj hμ 0 0 s = w := by
    obtain ⟨l, hl, hlw⟩ := hlim
    refine ⟨ξr + max l 0, by linarith [max_lt hl htspos], fun s hs => ?_⟩
    have hs1 : max l 0 < s - ξr := by linarith [hs.1]
    have hs2 : s - ξr < tstar := by linarith [hs.2]
    set s' : ℝ≥0 := (s - ξr).toNNReal with hs'
    have hs'R : (s' : ℝ) = s - ξr := Real.coe_toNNReal _ (le_trans (le_max_right _ _) hs1.le)
    have h1 : fwdTraj hμ 0 0 (ξr + s') = Pt.1.fn s' := hagree' s' (by rw [hs'R]; exact hs2)
    rw [hs'R, show ξr + (s - ξr) = s by ring] at h1
    rw [h1]
    exact hlw s' (by rw [hs'R]; exact lt_of_le_of_lt (le_max_left _ _) hs1)
      (by rw [hs'R]; exact hs2)
  have hbQ' : ∀ s : ℝ≥0, 0 < s → (s : ℝ) ≤ r →
      bwdTraj hμ p (β' : ℝ) ((β' : ℝ) - s) ∈ escQ j u := by
    intro s hs hsr
    rw [pwc_bwd_left hν p (β' : ℝ) hring hs]
    exact hbQ s hs (by exact_mod_cast hsr)
  have hQ := pwc_back_mem_Q (j := j) (u := u) hμ p w m ht' hr0 hrt hη hW hpQ hbQ'
  -- the walk at `0`
  have hW0 : escWalk ν 0 = 0 := by
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < cycTreg (copyEnv ν 0) := by
      rw [hcopy]; exact lt_of_le_of_lt zero_le hξtreg
    have := regenWalk_of_lt_treg (fun i => copyEnv ν i) (u := 0) h0
    simp only [NNReal.coe_zero] at this
    unfold escWalk
    rw [this, hcopy, hWh _ le_rfl]
    exact fwdTraj_self hμ 0 0
  have hzero : (0 : EscV k) ∈ escBlockMinus j u → ξr = 0 ∧ v = 0 := by
    intro hz
    have hξ0 : ξ = 0 := pwc_zero_case (by omega) hadm (escWalk ν) hW0 hz
    have hξr0' : ξr = 0 := by rw [hξr, hξ0]; simp
    refine ⟨hξr0', ?_⟩
    have := hagree' 0 (by simpa using htspos)
    rw [hPt0, hξr0'] at this
    simpa [fwdTraj_self] using this.symm
  have hK : ∀ n : ℕ, 1 ≤ n → fwdTraj hμ 0 0 ((n : ℝ) * β) = 0 → ξr < (n : ℝ) * β := by
    intro N hN hz
    have hle : cycTreg (cycSlice 0 ν) ≤ ENNReal.ofReal ((N : ℝ) * β) := by
      unfold cycTreg
      exact iInf_le (fun x : {k : ℕ // 1 ≤ k ∧ cycWalk (cycSlice 0 ν) 0 0 ((k : ℝ) * β) = 0} =>
        ENNReal.ofReal ((x.1 : ℝ) * β)) ⟨N, hN, by rw [hWh _ (by positivity)]; exact hz⟩
    have := lt_of_lt_of_le hξtreg hle
    exact (ENNReal.lt_ofReal_iff_toReal_lt hξtop).1 this
  have hno := pwc_noZero (j := j) (u := u) (v := v) (w := w) (ξ := ξr) (tp := tp) (r := r)
    (β' := (β' : ℝ)) (m := m) (fun x => fwdTraj hμ 0 0 x) (Pt := Pt)
    (by rw [show tp - r - ξr = tstar by rw [hts]]; exact hP)
    (fun s hs => hagree' s (by rw [hts]; exact hs)) ht' hQ
    (zero_not_mem_escQ hj hadm) hzero hK
  have htp0 : 0 ≤ tp := by linarith
  have hlt : ENNReal.ofReal tp < cycTreg (copyEnv ν 0) := by
    rw [hcopy]
    refine pwc_lt_cycTreg htp0 fun N hN hNt => ?_
    rw [hWh _ (by positivity)]
    exact hno N hN hNt
  have hWt : escWalk ν tp = p := by
    have hlt' : ((tp.toNNReal : ℝ≥0) : ℝ≥0∞) < cycTreg (copyEnv ν 0) := hlt
    have := regenWalk_of_lt_treg (fun i => copyEnv ν i) (u := tp.toNNReal) hlt'
    rw [Real.coe_toNNReal _ htp0] at this
    unfold escWalk
    rw [this, hcopy, hWh _ htp0]
    exact pwc_restart_end hμ p w m ht' hr0 hrt hη hW
  exact ⟨hν, hξtop, hlt, hWt⟩

end ElboimSly.Paper.Escape
