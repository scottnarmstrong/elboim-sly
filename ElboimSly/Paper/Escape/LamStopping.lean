/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.StopLenCut
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncNth
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycRecMeasStop
public import Mathlib

/-!
# The cumulative lengths `Λ_k` are stopping times of the joint exploration

The connecting plan ("`S₁ := Λ₁`, `S₂ := Λ_{I+1}`, `S₃ := Λ_{I+2}`").

For a plan `P` all of whose walks have finite length (`PlanFin`):

* `isStoppingTime_lam`: `ω ↦ Λ_k(cycNgood N ω)` is a stopping time of `cycMultiFilt` for `k < K`
  (the start of walk `k + 1`; the event `{Λ_k ≤ s}` says that entry `k` of `Trunc_s(ρ)` exists);
* `isStoppingTime_lam_last`: the same for `Λ_K` if `K = k + 1` is finite (the end of the last walk;
  here the non-anticipation of the stopping length, `stopLen_cut_le_iff`, tells from the truncated
  last entry whether the walk is complete).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

/-- All walks of the plan have finite length, in every good environment. -/
def PlanFin (P : CycPlan I d β) : Prop :=
  ∀ ν : Measure (CycS I d β), CycGood ν → ∀ i : ℕ, (i : ℕ∞) < P.K →
    (P.E (rule P ν) i).len < ⊤

theorem PlanFin.cont_iff {P : CycPlan I d β} (h : PlanFin P) {ν : Measure (CycS I d β)}
    (hν : CycGood ν) (k : ℕ) : P.Cont (rule P ν) k ↔ (k : ℕ∞) < P.K := by
  refine ⟨fun hc => hc.1, fun hk => ⟨hk, fun i hi => h ν hν i ?_⟩⟩
  exact lt_of_lt_of_le (by exact_mod_cast hi) hk.le

theorem PlanFin.nth_trunc {P : CycPlan I d β} (h : PlanFin P) {ν : Measure (CycS I d β)}
    (hν : CycGood ν) {k : ℕ} (hk : (k : ℕ∞) < P.K) (s : ℝ≥0) :
    (k : ℕ∞) < (CycRec.trunc s (P.envFinal ν)).num ↔ lam P ν k ≤ s := by
  classical
  have := trunc_envFinal_nth (P := P) (ν := ν) P.junk s k
  constructor
  · intro hlt
    obtain ⟨e, he⟩ := nth_of_lt_num hlt
    rw [this] at he
    by_contra hc
    rw [ite_eq_right (fun hh => hc hh.2)] at he
    exact absurd he (by simp)
  · intro hl
    refine lt_num_of_nth (e := tgt P ν s k) ?_
    rw [this, ite_eq_left ⟨(h.cont_iff hν k).2 hk, hl⟩]

section filtration

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS I d β)} (P : CycPlan I d β)

/-- Events determined by `Trunc_s(ρ)` lie in `ℱ_s`. -/
theorem measurableSet_trunc_cycMultiFilt (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω)
    (s : ℝ≥0) {A : Set (CycRec I d)} (hA : MeasurableSet A) :
    MeasurableSet[cycMultiFilt P 𝒢₀ hNm h𝒢 Pr s]
      {ω | CycRec.trunc s (P.envFinal (cycNgood N ω)) ∈ A} := by
  show MeasurableSet[cycFiltration Pr 𝒢₀ (fun ω => P.envFinal (cycNgood N ω)) s] _
  rw [cycFiltration_eq 𝒢₀ P.junk Pr]
  have hc : MeasurableSet[MeasurableSpace.comap
      (fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω))) inferInstance]
      {ω | CycRec.trunc s (P.envFinal (cycNgood N ω)) ∈ A} := ⟨A, hA, rfl⟩
  have hle : MeasurableSpace.comap (fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω)))
      inferInstance ≤ 𝒢₀ ⊔ MeasurableSpace.comap
        (fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω))) inferInstance ⊔ cycNull Pr :=
    le_sup_right.trans le_sup_left
  exact hle _ hc

/-- `Λ_k` of the (good version of the) environment, as a time. -/
noncomputable def lamT (P : CycPlan I d β) (N : Ω → Measure (CycS I d β)) (k : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  lam P (cycNgood N ω) k

include P in
/-- **`Λ_k` is a stopping time** (`k < K`): the start of walk `k + 1`. -/
theorem isStoppingTime_lam (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω)
    (hP : PlanFin P) {k : ℕ} (hk : (k : ℕ∞) < P.K) :
    IsStoppingTime (cycMultiFilt P 𝒢₀ hNm h𝒢 Pr) (lamT P N k) := by
  intro s
  have hset : {ω | lamT P N k ω ≤ (s : WithTop ℝ≥0)} =
      {ω | CycRec.trunc s (P.envFinal (cycNgood N ω)) ∈ {σ : CycRec I d | (k : ℕ∞) < σ.num}} := by
    ext ω
    exact (hP.nth_trunc (cycGood_cycNgood N ω) hk s).symm
  rw [hset]
  exact measurableSet_trunc_cycMultiFilt 𝒢₀ P hNm h𝒢 Pr s
    (CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (k : ℕ∞) < x})))

end filtration

section last

/-- The last walk `k` of a record `σ` is complete: its entry exists and its path has reached the
stopping length. -/
def LastDone (P : CycPlan I d β) (k : ℕ) (σ : CycRec I d) : Prop :=
  (k : ℕ∞) < σ.num ∧
    P.stopLen k (fun i : Fin k => σ.coord P.junk i) (σ.coord P.junk k).2 ≤
      (σ.coord P.junk k).len

theorem measurableSet_lastDone (P : CycPlan I d β) (k : ℕ) :
    MeasurableSet {σ : CycRec I d | LastDone P k σ} := by
  have h1 : MeasurableSet {σ : CycRec I d | (k : ℕ∞) < σ.num} :=
    CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (k : ℕ∞) < x}))
  have h0 : Measurable fun σ : CycRec I d => (fun i : Fin k => σ.coord P.junk i) :=
    measurable_pi_iff.2 fun i => CycRec.measurable_coord P.junk (i : ℕ)
  have h2 : Measurable fun σ : CycRec I d =>
      ((fun i : Fin k => σ.coord P.junk i), (σ.coord P.junk k).2) :=
    h0.prodMk (measurable_snd.comp (CycRec.measurable_coord P.junk k))
  have h3 : Measurable fun σ : CycRec I d =>
      P.stopLen k (fun i : Fin k => σ.coord P.junk i) (σ.coord P.junk k).2 := by
    have h := (P.measurable_stopLen k).comp h2
    exact h
  have h4 : Measurable fun σ : CycRec I d => (σ.coord P.junk k).len :=
    measurable_entry_len'.comp (CycRec.measurable_coord P.junk k)
  have := h1.inter (measurableSet_le h3 h4)
  exact this

theorem tgt_lt_eq (ν : Measure (CycS I d β)) (P : CycPlan I d β) (s : ℝ≥0) {i k : ℕ}
    (hik : i < k) (hl : lam P ν k ≤ s) : tgt P ν s i = P.E (rule P ν) i := by
  unfold tgt
  rw [ite_eq_left]
  rw [← lam_succ]
  exact (lam_mono (Nat.succ_le_of_lt hik)).trans hl

theorem cycPath_cut_len (p : CycPath d) (ℓ : ℝ≥0∞) : (p.cut ℓ).1.len = ℓ :=
  CPath.cut_len _ _

theorem len_E_eq (ν : Measure (CycS I d β)) (P : CycPlan I d β) (k : ℕ) :
    (P.E (rule P ν) k).len = P.stopLen k (P.ideal (rule P ν) k) (pth P ν k) := by
  rw [E_eq, stopLen_eq_sInf]
  show ((pth P ν k).1.cut _).len = _
  rw [CPath.cut_len]

theorem PlanFin.lastDone_iff {P : CycPlan I d β} (h : PlanFin P) {ν : Measure (CycS I d β)}
    (hν : CycGood ν) {k : ℕ} (hk : (k : ℕ∞) < P.K) (s : ℝ≥0) :
    LastDone P k (CycRec.trunc s (P.envFinal ν)) ↔ lam P ν (k + 1) ≤ s := by
  classical
  by_cases hl : lam P ν k ≤ s
  · have hnth : ∀ i ≤ k, (CycRec.trunc s (P.envFinal ν)).nth i = some (tgt P ν s i) := by
      intro i hi
      have := trunc_envFinal_nth (P := P) (ν := ν) P.junk s i
      rw [this, ite_eq_left]
      exact ⟨(h.cont_iff hν i).2 (lt_of_le_of_lt (by exact_mod_cast hi) hk),
        (lam_mono hi).trans hl⟩
    have hcoord : ∀ i ≤ k, (CycRec.trunc s (P.envFinal ν)).coord P.junk i = tgt P ν s i := by
      intro i hi
      unfold CycRec.coord
      rw [hnth i hi]; rfl
    have hpre : (fun i : Fin k => (CycRec.trunc s (P.envFinal ν)).coord P.junk i) =
        P.ideal (rule P ν) k := by
      funext i
      rw [hcoord i i.2.le, tgt_lt_eq ν P s i.2 hl, CycPlan.ideal_apply]
    have hnum : (k : ℕ∞) < (CycRec.trunc s (P.envFinal ν)).num :=
      lt_num_of_nth (hnth k le_rfl)
    unfold LastDone
    rw [hpre, hcoord k le_rfl]
    refine (and_iff_right hnum).trans ?_
    have hlenfin := h ν hν k hk
    have hlen := len_E_eq ν P k
    set ℓ := P.stopLen k (P.ideal (rule P ν) k) (pth P ν k) with hℓ
    have hℓtop : ℓ ≠ ⊤ := by rw [← hlen]; exact hlenfin.ne
    obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, ℓ = r := ⟨ℓ.toNNReal, (ENNReal.coe_toNNReal hℓtop).symm⟩
    have hEe : P.E (rule P ν) k = (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) := by
      rw [E_eq, ← stopLen_eq_sInf, ← hℓ, hr]
    rw [lam_succ, hlen]
    by_cases hc : lam P ν k + ℓ ≤ s
    · have : tgt P ν s k = P.E (rule P ν) k := by
        unfold tgt; rw [ite_eq_left]; rw [hlen]; exact hc
      rw [this, hEe]
      refine iff_of_true ?_ hc
      show P.stopLen k (P.ideal (rule P ν) k) ((pth P ν k).cut (r : ℝ≥0∞)) ≤
        ((pth P ν k).cut (r : ℝ≥0∞)).1.len
      rw [cycPath_cut_len]
      exact (stopLen_cut_le_iff P k _ _ r).2 (by rw [← hℓ, hr])
    · have hlt : (s : ℝ≥0∞) < lam P ν k + ℓ := not_le.1 hc
      have hlk : lam P ν k ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hl
      have hm : (s : ℝ≥0∞) - lam P ν k < ℓ := by
        rw [add_comm] at hlt
        exact (ENNReal.sub_lt_iff_lt_right hlk hl).2 hlt
      have : tgt P ν s k = (P.E (rule P ν) k).cut ((s : ℝ≥0∞) - lam P ν k) := by
        unfold tgt; rw [ite_eq_right]; rw [hlen]; exact hc
      rw [this]
      refine iff_of_false ?_ hc
      obtain ⟨m, hmeq⟩ : ∃ m : ℝ≥0, (s : ℝ≥0∞) - lam P ν k = m :=
        ⟨s - (lam P ν k).toNNReal, by
          rw [ENNReal.coe_sub, ENNReal.coe_toNNReal hlk]⟩
      rw [hmeq] at hm ⊢
      have hmr : m ≤ r := by
        have : (m : ℝ≥0∞) ≤ r := by rw [← hr]; exact hm.le
        exact_mod_cast this
      have hcut : (P.E (rule P ν) k).cut (m : ℝ≥0∞) = (dat P ν k, (pth P ν k).cut (m : ℝ≥0∞)) := by
        rw [hEe]
        show (_, (((pth P ν k).cut (r : ℝ≥0∞))).cut (m : ℝ≥0∞)) = _
        congr 1
        exact Subtype.ext (CPath.cut_cut (pth P ν k).1 (a := (r : ℝ≥0∞)) (b := (m : ℝ≥0∞))
          (by exact_mod_cast hmr))
      rw [hcut]
      show ¬ (P.stopLen k (P.ideal (rule P ν) k) ((pth P ν k).cut (m : ℝ≥0∞)) ≤
        ((pth P ν k).cut (m : ℝ≥0∞)).1.len)
      rw [cycPath_cut_len]
      intro hh
      have := (stopLen_cut_le_iff P k _ _ m).1 hh
      rw [← hℓ, hr] at this
      exact absurd hm (not_lt.2 (by rw [hr]; exact this))
  · have h1 : ¬ (k : ℕ∞) < (CycRec.trunc s (P.envFinal ν)).num := fun hh => hl ((h.nth_trunc hν hk s).1 hh)
    have h2 : ¬ lam P ν (k + 1) ≤ s := fun hh => hl ((lam_mono (Nat.le_succ k)).trans hh)
    exact iff_of_false (fun hh => h1 hh.1) h2

end last

section last_stopping

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS I d β)} (P : CycPlan I d β)

include P in
/-- **`Λ_{k+1}` is a stopping time** (`k < K`): the end of walk `k + 1`.  In particular `Λ_K`
for `K` finite.  This uses the non-anticipation of the stopping length. -/
theorem isStoppingTime_lam_succ (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω)
    (hP : PlanFin P) {k : ℕ} (hk : (k : ℕ∞) < P.K) :
    IsStoppingTime (cycMultiFilt P 𝒢₀ hNm h𝒢 Pr) (lamT P N (k + 1)) := by
  intro s
  have hset : {ω | lamT P N (k + 1) ω ≤ (s : WithTop ℝ≥0)} =
      {ω | CycRec.trunc s (P.envFinal (cycNgood N ω)) ∈ {σ : CycRec I d | LastDone P k σ}} := by
    ext ω
    exact (hP.lastDone_iff (cycGood_cycNgood N ω) hk s).symm
  rw [hset]
  exact measurableSet_trunc_cycMultiFilt 𝒢₀ P hNm h𝒢 Pr s (measurableSet_lastDone P k)

/-- `Λ_k` is finite when the first `k` walks have finite length. -/
theorem lamT_ne_top (hP : PlanFin P) (ω : Ω) {k : ℕ} (hk : (k : ℕ∞) ≤ P.K) :
    lamT P N k ω ≠ ⊤ := by
  have hν := cycGood_cycNgood N ω
  refine lam_ne_top (fun i hi => hP _ hν i ?_)
  exact lt_of_lt_of_le (by exact_mod_cast hi) hk

end last_stopping

end ElboimSly.Paper.Escape
