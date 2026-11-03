/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan53Cond
public import ElboimSly.Paper.Escape.Plan53Stop
public import ElboimSly.Paper.Escape.DensityG
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalNth
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingDef
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# The records of the plan `𝒫_𝒜` in an environment

The walks W_i and the stopping times tau_i; 𝒜_i, 𝒜, 𝒢(β').  For a good environment `ν`, the entry `m` of the final
record of `planA` is the walk `W_{m+1}` cut at its stopping length `τ_{m+1}`.

* `escEntry`: the entry `m` (the `m`-th world-line of the ideal record);
* `escTauE`, `escWalkE`: the stopping times and the walks, as real-time functions;
* `escAgree_ideal`: the ideal record agrees with the walks (`EscAgree`);
* `escBefore_planA`: none of the conditions (1)-(7) holds strictly before `τ_i` (`EscBefore`);
* `escWalkE_zero`, `escWalkE_nn`: `W_ℓ(0) = p_ℓ`, nearest-neighbour jumps.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] (n : ℕ) (u : Fin (k + 2) → ℤ) (b : ℕ)
  (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β))

/-- The path rule of `planA` in the environment `ν`. -/
noncomputable def envRuleA : PathRule ℕ (k + 2) :=
  fun m ρ => envPath ν ((planA n β u b hlog).start m ρ)

/-- The entry `m` of the ideal record of `planA` in `ν`: the walk `W_{m+1}` cut at `τ_{m+1}`. -/
noncomputable def escEntry (m : ℕ) : CycEntry ℕ (k + 2) :=
  (planA n β u b hlog).E (envRuleA n u b hlog ν) m

/-- The stopping times `τ_ℓ` (`1 ≤ ℓ ≤ I`), as reals; `0` outside. -/
noncomputable def escTauE (ℓ : ℕ) : ℝ :=
  if 1 ≤ ℓ ∧ ℓ ≤ escIstar n (escJ n) then (escEntry n u b hlog ν (ℓ - 1)).len.toReal else 0

/-- The walks `W_ℓ` as real-time functions. -/
noncomputable def escWalkE (ℓ : ℕ) (s : ℝ) : Fin (k + 2) → ℤ :=
  envWalk ν (0, escPoint n (escJ n) u ℓ, (b : ℝ), true) s.toNNReal

variable {n u b hlog ν}

theorem escWalkE_eq_envPath (hν : CycGood ν) (ℓ : ℕ) (s : ℝ) :
    escWalkE n u b ν ℓ s =
      (envPath ν (0, escPoint n (escJ n) u ℓ, (b : ℝ), true)).1.fn s.toNNReal := by
  unfold escWalkE envWalk
  rw [ite_eq_left hν]
  exact (congrFun (envPath_len (δ := (0, escPoint n (escJ n) u ℓ, (b : ℝ), true))
    (hν _)).2 _).symm

theorem escEntry_eq (m : ℕ) :
    escEntry n u b hlog ν m =
      ((planA n β u b hlog).start m ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m),
        (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).cut
          ((planA n β u b hlog).stopLen m ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m)
            (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)))) := rfl

theorem escEntry_len (m : ℕ) :
    (escEntry n u b hlog ν m).len =
      (planA n β u b hlog).stopLen m ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m)
        (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)) := by
  rw [escEntry_eq]
  simp [CycEntry.len, CycPath.cut]

theorem escEntry_len_le (m : ℕ) : (escEntry n u b hlog ν m).len ≤ (4 : ℝ≥0∞) ^ n := by
  rw [escEntry_len]
  exact stopLen_le_pow (planA_ruleAt n u b hlog m) hlog _ _

theorem escEntry_len_ne_top (m : ℕ) : (escEntry n u b hlog ν m).len ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.pow_ne_top (by simp)) (escEntry_len_le m)

theorem escEntry_fn (m : ℕ) (s : ℝ≥0) :
    (escEntry n u b hlog ν m).path.fn s =
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn
        (min (s : ℝ≥0∞) (escEntry n u b hlog ν m).len).toNNReal := by
  rw [escEntry_len]
  conv_lhs => rw [escEntry_eq]
  simp only [CycEntry.path, CycPath.cut]
  rw [CPath.cut_fn]

theorem ideal_apply' (m : ℕ) (i : Fin m) :
    (planA n β u b hlog).ideal (envRuleA n u b hlog ν) m i = escEntry n u b hlog ν i :=
  (planA n β u b hlog).ideal_apply _ m i

theorem escAgree_ideal (hν : CycGood ν) {m : ℕ} (hm : m ≤ escIstar n (escJ n)) :
    EscAgree (escWalkE n u b ν) (escTauE n u b hlog ν)
      ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m) where
  len ℓ := by
    rw [ideal_apply']
    have hℓ : 1 ≤ (ℓ : ℕ) + 1 ∧ (ℓ : ℕ) + 1 ≤ escIstar n (escJ n) := ⟨by omega, by omega⟩
    unfold escTauE
    rw [ite_eq_left hℓ]
    simp only [Nat.add_sub_cancel]
    rw [ENNReal.ofReal_toReal (escEntry_len_ne_top _)]
  nonneg ℓ := by
    unfold escTauE
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  fn ℓ s := by
    rw [ideal_apply', escEntry_fn, escWalkE_eq_envPath hν]
    have hℓ : 1 ≤ (ℓ : ℕ) + 1 ∧ (ℓ : ℕ) + 1 ≤ escIstar n (escJ n) := ⟨by omega, by omega⟩
    unfold escTauE
    rw [ite_eq_left hℓ]
    simp only [Nat.add_sub_cancel]
    congr 1
    have hne := escEntry_len_ne_top (n := n) (u := u) (b := b) (hlog := hlog) (ν := ν) ℓ
    obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, (escEntry n u b hlog ν ℓ).len = L := ⟨_, (ENNReal.coe_toNNReal hne).symm⟩
    rw [hL, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.coe_toReal, ← NNReal.coe_min,
      Real.toNNReal_coe]

theorem nn_of_cyclic {d : ℕ} {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {t : ℝ} (ht : 0 < t)
    {ε : ℝ} (hε : 0 < ε) : ∃ s, t - ε < s ∧ s < t ∧ ‖w t - w s‖ ≤ 1 := by
  have hev : ∀ᶠ u in 𝓝[<] t, ‖w t - w u‖ ≤ 1 := by
    by_cases hj : t ∈ cycJumpSet w
    · filter_upwards [hw.jump_size t hj] with u hu
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : |w t i - w u i| ≤ ∑ j, |w t j - w u j| :=
        Finset.single_le_sum (f := fun j => |w t j - w u j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
      rw [hu] at h1
      rw [Pi.sub_apply, Int.norm_eq_abs]
      exact_mod_cast h1
    · have : ∀ᶠ u in 𝓝[<] t, w u = w t := by
        by_contra h
        exact hj ⟨ht, h⟩
      filter_upwards [this] with u hu
      simp [hu]
  obtain ⟨s, hs1, hs2⟩ := (hev.and (Ioo_mem_nhdsLT (show t - ε < t by linarith))).exists
  exact ⟨s, hs2.1, hs2.2, hs1⟩

theorem escWalkE_zero (hν : CycGood ν) (ℓ : ℕ) :
    escWalkE n u b ν ℓ 0 = escPoint n (escJ n) u ℓ := by
  rw [escWalkE_eq_envPath hν, Real.toNNReal_zero]
  exact envPath_zero (δ := (0, escPoint n (escJ n) u ℓ, (b : ℝ), true)) (hν _)

theorem escWalkE_nn (hν : CycGood ν) (ℓ : ℕ) (t : ℝ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ s, t - ε < s ∧ s < t ∧ ‖escWalkE n u b ν ℓ t - escWalkE n u b ν ℓ s‖ ≤ 1 := by
  set p := envPath ν (0, escPoint n (escJ n) u ℓ, (b : ℝ), true) with hp
  obtain ⟨s, h1, h2, h3⟩ := nn_of_cyclic (isCyclicPath_shift p) ht hε
  refine ⟨s, h1, h2, ?_⟩
  rw [escWalkE_eq_envPath hν, escWalkE_eq_envPath hν]
  simpa [sub_sub_sub_cancel_right] using h3

theorem escBefore_planA (hν : CycGood ν) :
    EscBefore n (escJ n) β (escIstar n (escJ n)) (escPoint n (escJ n) u) (escWalkE n u b ν)
      (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) := by
  intro i t ht0 hti hc
  by_cases hi : 1 ≤ i ∧ i ≤ escIstar n (escJ n)
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hag := escAgree_ideal (n := n) (u := u) (b := b) (hlog := hlog) hν (m := m) (by omega)
    have hWi : ∀ s : ℝ, 0 ≤ s → escWalkE n u b ν (m + 1) s =
        (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn s.toNNReal :=
      fun s _ => escWalkE_eq_envPath hν _ s
    have hcany := EscStopCond_imp_Cany n β u (escWalkE n u b ν) (escTauE n u b hlog ν)
      ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m) hag
      ((planA n β u b hlog).start m ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m))
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)) hWi hlog
      (t := t.toNNReal) (Real.toNNReal_pos.2 ht0) (by rwa [Real.coe_toNNReal _ ht0.le])
    have hstop := stopLen_le_of_cond (planA_ruleAt n u b hlog m) hlog
      ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m)
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)) t.toNNReal hcany
    rw [← escEntry_len] at hstop
    have hle : (escEntry n u b hlog ν m).len.toReal ≤ t := by
      have := ENNReal.toReal_mono ENNReal.coe_ne_top hstop
      simpa [Real.coe_toNNReal _ ht0.le] using this
    have hτ : escTauE n u b hlog ν (m + 1) = (escEntry n u b hlog ν m).len.toReal := by
      unfold escTauE; rw [ite_eq_left hi]; simp
    rw [hτ] at hti
    linarith
  · have : escTauE n u b hlog ν i = 0 := by unfold escTauE; rw [ite_eq_right hi]
    rw [this] at hti
    linarith

end ElboimSly.Paper.Escape
