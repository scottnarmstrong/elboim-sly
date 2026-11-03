/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWClose5
public import ElboimSly.Paper.Escape.Es55PWDet
public import ElboimSly.Paper.Escape.Es55PWGlue
public import ElboimSly.Paper.Escape.Es55PWRestart
public import ElboimSly.Paper.Escape.Es55PWCore2
public import ElboimSly.Paper.Escape.C57Ae
public import ElboimSly.Paper.Escape.PlanCoupling
public import ElboimSly.Paper.Escape.Es55Step1
public import ElboimSly.Paper.Escape.Es53NumA
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the deterministic assembly of the pathwise step

ES22 Lemma 5.5, Step 1.  `pw_det`: for good `ν`, `Ñ` and the data of the coupling
(agreement off the discrepancy, the glued continuation `y`), the rational `E₅₆` for `y` and the
absence of rings at `p_i` at the phase `β'` imply `ν ∈ Con_i`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The phase of `t'` and the circle position of `ξ + t_*`. -/
theorem pw_phase_circle {x r : ℝ} {β' : ℕ} (h : cycIntPhase β (cycFloor β x) = (β' : ℝ)) :
    (((cycFloor β x - r : ℝ)) : AddCircle β) = (((β' : ℝ) - r : ℝ) : AddCircle β) := by
  have hc : (((cycFloor β x - r) - ((β' : ℝ) - r) : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨⌊cycFloor β x / β⌋, ?_⟩
    unfold cycIntPhase at h
    rw [zsmul_eq_mul]
    nlinarith [h]
  rw [AddCircle.coe_sub] at hc
  exact sub_eq_zero.1 hc

theorem pth5_back_eq (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (ν : Measure (CycS ℕ (k + 2) β)) :
    (pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).1 =
      (envPath ν ((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false)).1 := by
  have h : dat (plan5 n β tn u β' i hlog) ν (escIstar n (escJ n) + 1) =
      (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) :=
    ent5_data_back n tn u β' i hlog ν
  unfold pth5 pth
  rw [h]

section det

variable {n : ℕ} {tn : ℝ} {u : EscV k} {β' i : ℕ} {hlog : 1 < Real.log β}
  {ν Ñ : Measure (CycS ℕ (k + 2) β)}

/-- **The deterministic pathwise step.** -/
theorem pw_det (hj4 : 4 ≤ escJ n) (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n))
    (hadm : EscAdmissible (escJ n) u) (hν : CycGood ν) (hÑ : CycGood Ñ)
    (hH : ν ∈ (escKSet β tn n β' u ∩ escASet n u β' hlog i) ∩ es55Exit β n u β' i)
    (hdet : Es55Det n tn u β' i hlog ν)
    {R D : Set (CycS ℕ (k + 2) β)}
    (hR : R ⊆ ⋃ m ∈ Finset.range (escIstar n (escJ n) + 2),
      (ent5 n tn u β' i hlog ν m).region β)
    (hDR : D ⊆ R) (hD : ∀ x ∈ D, Ñ {x} ≠ 0 ∨ ν {x} ≠ 0)
    (hÑR : ∀ x ∉ R, Ñ {x} = ν {x})
    (hb : ∀ r : ℝ≥0, Disjoint (CycEntry.region β
        ((((0 : ℕ), entEnd (ent5 n tn u β' i hlog ν 0),
          (ent5 n tn u β' i hlog ν 0).len.toReal, true) : CycData ℕ (k + 2)),
          (envPath Ñ ((0 : ℕ), entEnd (ent5 n tn u β' i hlog ν 0),
            (ent5 n tn u β' i hlog ν 0).len.toReal, true)).cut (r : ℝ≥0∞))) D →
      ∀ s : ℝ≥0, s ≤ r →
        envWalk Ñ ((0 : ℕ), entEnd (ent5 n tn u β' i hlog ν 0),
          (ent5 n tn u β' i hlog ν 0).len.toReal, true) s =
        envWalk ν ((0 : ℕ), entEnd (ent5 n tn u β' i hlog ν 0),
          (ent5 n tn u β' i hlog ν 0).len.toReal, true) s)
    {q : ℕ → ℝ≥0 → Fin (k + 2) → ℤ} (hq0 : ∀ m, q m 0 = 0)
    (hqrc : ∀ m s, ∀ᶠ u in 𝓝[≥] s, q m u = q m s)
    {y : ℝ≥0 → Fin (k + 2) → ℤ}
    (hy : y = contGlue β.toNNReal (fun s => envWalk Ñ ((0 : ℕ), entEnd (ent5 n tn u β' i hlog ν 0),
          (ent5 n tn u β' i hlog ν 0).len.toReal, true) s - entEnd (ent5 n tn u β' i hlog ν 0)) q)
    (hmem : ((ent5 n tn u β' i hlog ν 0, ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)), y) ∈
      d55S β (escJ n) u)
    (hring : ¬ ∃ e : Edge (k + 2), e.Mem (escPoint n (escJ n) u i) ∧
      Rings (cycSlice 0 ν) e (β' : ℝ)) :
    ν ∈ escConSet β n u i := by
  classical
  have hβ : 0 < β := Fact.out
  have hj3 : 3 ≤ escJ n := by omega
  have hj1 : 1 ≤ escJ n := by omega
  obtain ⟨⟨⟨hgood, hKev⟩, -⟩, hX⟩ := hH
  obtain ⟨hle, hlt, hBm, hphase⟩ := hKev
  set j := escJ n with hjdef
  set ξ := escXi (escWalk ν) (escBlock j u) with hξdef
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set e0 := ent5 n tn u β' i hlog ν 0 with he0
  set eB := ent5 n tn u β' i hlog ν (escIstar n j + 1) with heB
  have hpQ : escPoint n j u i ∈ escQ j u :=
    escPoint_mem_escQ (by omega)
      (le_trans (Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ hiI)) (escIstar_spec n j))
  have hBmB : escWalk ν ξ.toReal ∈ escBlock j u := escBlockMinus_subset u hBm
  have hL : e0.len = ξ := ent5_zero_len n tn u β' i hlog ν hν hle hlt hBmB
  have hLr : e0.len.toReal = ξ.toReal := by rw [hL]
  have hv : entEnd e0 = escWalk ν ξ.toReal := ent5_zero_entEnd n tn u β' i hlog ν hν hle hlt hBmB
  have hcopy : copyEnv ν 0 = cycSlice 0 ν := copyEnv_eq_cycSlice ν 0
  have hμ : Good (cycSlice 0 ν) := hν 0
  have hξr0 : 0 ≤ ξ.toReal := ENNReal.toReal_nonneg
  have hvc : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 ξ.toReal = entEnd e0 := by
    rw [hv, pw_escWalk_eq hξr0 (by
      rw [ENNReal.ofReal_toReal hξtop]; exact hlt), ]
  -- the exit index
  obtain ⟨a, hDa, hEsc, hNo⟩ := hmem
  obtain ⟨a0, hD0, -, -, hT1, hT2⟩ := hdet
  have ha : a = a0 := d55Exit_unique hj1 hDa hD0
  subst ha
  obtain ⟨hlen, hjtle⟩ := ent5_back_len n tn u β' i hlog ν hν hj1 hpQ hX hDa
  have hjtfin : eB.path.jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hjtle
  set r : ℝ≥0 := (eB.path.jt a).toNNReal with hr
  have hrR : (r : ℝ) = (eB.path.jt a).toReal := rfl
  have hwdef : entEnd eB = eB.path.jv a := by
    unfold entEnd; rw [hlen]; rfl
  have hEBlen : eB.len.toReal = (r : ℝ) := by rw [hlen]; rfl
  set tstar : ℝ := d55T β j e0 eB a with htstar
  have hts : tstar = cycFloor β (ξ.toReal + 4 ^ j) - r - ξ.toReal := by
    rw [htstar]; unfold d55T; rw [hLr, hrR]
  have htspos : 0 < tstar := lt_of_lt_of_le (by positivity) hT1
  -- the glued continuation
  set δ : CycData ℕ (k + 2) := ((0 : ℕ), entEnd e0, e0.len.toReal, true) with hδ
  set Pt := envPath Ñ δ with hPt
  have hgÑ : Good (cycSlice δ.copy Ñ) := hÑ δ.copy
  have hqfn : ∀ s, Pt.1.fn s = envWalk Ñ δ s := fun s => by
    rw [hPt, (envPath_len hgÑ).2, envWalk_of_good hÑ]
  have hPt0 : Pt.1.fn 0 = entEnd e0 := envPath_zero hgÑ
  have hpfrc : ∀ s, ∀ᶠ u' in 𝓝[≥] s,
      (fun s => envWalk Ñ δ s - entEnd e0) u' = (fun s => envWalk Ñ δ s - entEnd e0) s := by
    intro s
    filter_upwards [Pt.1.rc s] with u' hu'
    simp only [← hqfn, hu']
  have hyrc : ∀ s, ∀ᶠ u' in 𝓝[≥] s, y u' = y s := by
    rw [hy]; exact contGlue_rc (Real.toNNReal_pos.2 hβ) hpfrc hqrc
  have hE56 := (esc56_iff_rat hβ.le htspos.le hyrc).2 hEsc
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hE56
  have hnz : ∀ s : ℝ≥0, β.toNNReal ≤ s → s ≤ tstar.toNNReal → y s ≠ 0 := by
    intro s hs1 hs2 h0
    have hsβ : β ≤ (s : ℝ) := (Real.toNNReal_le_iff_le_coe).1 hs1
    have hst : (s : ℝ) ≤ tstar := by
      exact (Real.le_toNNReal_iff_coe_le htspos.le).1 hs2
    exact hE3 (s : ℝ) hsβ hst (by simp [h0])
  have hgl := contGlue_lt_treg (Real.toNNReal_pos.2 hβ) (fun s => envWalk Ñ δ s - entEnd e0) q hq0
    (t := tstar.toNNReal) (by rw [← hy]; exact hnz)
  have hyP : ∀ s : ℝ≥0, (s : ℝ) ≤ tstar → Pt.1.fn s = entEnd e0 + y s := by
    intro s hs
    have h1 : y s = envWalk Ñ δ s - entEnd e0 := by
      rw [hy]; exact hgl.2 s ((Real.le_toNNReal_iff_coe_le htspos.le).2 hs)
    rw [hqfn, h1]; abel
  -- PWPath
  have hP : PWPath β j u (entEnd e0) (eB.path.jv a) tstar Pt := by
    refine ⟨fun s hs => ?_, fun s hs1 hs2 => ?_, fun s hs => ?_⟩
    · have := hE2 (s : ℝ) s.2 hs
      simp only [Real.toNNReal_coe] at this
      rw [hyP s hs]; exact this
    · have := hE3 (s : ℝ) hs1 hs2
      simp only [Real.toNNReal_coe] at this
      rw [hyP s hs2]; exact this
    · have := hE4 (s : ℝ) s.2 hs
      simp only [Real.toNNReal_coe] at this
      rw [hyP s (by linarith)]; exact this
  -- agreement
  have hreg := pw_reg_of_ent5 (n := n) (tn := tn) (u := u) (β' := β') (i := i) (hlog := hlog)
    (ν := ν) hν hj3 ⟨hi1, hiI⟩ hpQ hR
  have hphase' : (((e0.len.toReal + tstar : ℝ)) : AddCircle β) =
      (((β' : ℝ) - eB.len.toReal : ℝ) : AddCircle β) := by
    have h1 : e0.len.toReal + tstar = cycFloor β (ξ.toReal + 4 ^ j) - r := by rw [hts, hLr]; ring
    rw [h1, hEBlen]
    exact pw_phase_circle hphase
  have hagr : ∀ s : ℝ≥0, (s : ℝ) < tstar →
      envWalk Ñ δ s = envWalk ν δ s := by
    intro s hs
    refine hb s ?_ s le_rfl
    rw [Set.disjoint_left]
    intro x hx hxD
    have hxR := hDR hxD
    have h1 := pw_Z1 hÑ hP (hwdef ▸ hreg) hs.le hx hxR
    have h2 := pw_Z2 hj1 hν hÑ hP (hwdef ▸ hreg) hÑR hphase' hs hx hxR
    rcases hD x hxD with h | h
    · exact h h1
    · exact h h2
  -- assemble
  have hagree : ∀ s : ℝ≥0, (s : ℝ) < tstar →
      ElboimSly.cycWalk (copyEnv ν 0) 0 0 (ξ.toReal + s) = Pt.1.fn s := by
    intro s hs
    rw [hcopy, ← hLr]
    have hvc' : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 e0.len.toReal = entEnd e0 := by
      rw [hLr]; exact hvc
    rw [pw_restart hν (by rw [hLr]; exact hξr0) hvc' s, hqfn, hagr s hs]
  have hlim : ∃ l : ℝ, l < tstar ∧ ∀ s : ℝ≥0, l < s → (s : ℝ) < tstar →
      Pt.1.fn s = eB.path.jv a := by
    obtain ⟨hnj⟩ := (⟨hNo⟩ : Nonempty (noJumpRat y tstar))
    obtain ⟨l, -, hl, hls⟩ := (noJumpRat_iff hyrc htspos).1 hnj
    refine ⟨l, hl, fun s hs1 hs2 => ?_⟩
    rw [hyP s hs2.le]
    have := hls s hs1 hs2
    rw [Real.toNNReal_coe] at this
    rw [this]
    simpa using hE1
  have hbw : (envPath ν ((0 : ℕ), escPoint n j u i, (β' : ℝ), false)).1.fn r = eB.path.jv a := by
    rw [← pth5_back_eq n tn u β' i hlog ν, ← ent5_fn n tn u β' i hlog ν _ (s := r)
      (by rw [hlen]; exact ENNReal.coe_toNNReal_le_self)]
    rfl
  have hbQ : ∀ s : ℝ≥0, 0 < s → s ≤ r →
      (envPath ν ((0 : ℕ), escPoint n j u i, (β' : ℝ), false)).1.left s ∈ escQ j u := by
    intro s hs hsr
    have hl : (s : ℝ≥0∞) ≤ eB.len := by
      rw [hlen]; exact le_trans (by exact_mod_cast hsr) ENNReal.coe_toNNReal_le_self
    rw [← pth5_back_eq n tn u β' i hlog ν, ← ent5_left n tn u β' i hlog ν _ hs hl]
    exact ent5_back_left_mem n tn u β' i hlog ν hν hpQ hs hl
  exact pwc_conSet hν hj3 hadm ⟨hle, hlt, hBm, hphase⟩ hpQ hring hbw hbQ hts htspos hP
    hPt0 hagree hlim

end det

end ElboimSly.Paper.Escape
