/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAtt
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvWalk
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import Mathlib

/-!
# The environment scheme (b), finite horizon: the global time budget

The environment scheme (b), `h_gl`. `lam P ν k = Λ_k` is the total length of the first `k`
environment world-lines. `Bud` is the invariant of a trajectory of states for a global horizon `sc`:
an unfinished state `EnvAt k r` has `Λ_k + r ≤ sc`, and a finished state is a record `shape k r`
whose end is explained either by the horizon (`Λ_k + r = sc`) or by the end of the plan
(`r = ℓ_k` and `k + 1 ≥ K`). `Traj.bud` shows it along a trajectory.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}

/-- `Λ_k`: the total length of the first `k` environment world-lines. -/
noncomputable def lam (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (k : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range k, (P.E (rule P ν) i).len

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem lam_succ (k : ℕ) : lam P ν (k + 1) = lam P ν k + (P.E (rule P ν) k).len :=
  Finset.sum_range_succ _ _

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem lam_mono {k k' : ℕ} (h : k ≤ k') : lam P ν k ≤ lam P ν k' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem lam_ne_top {k : ℕ} (h : P.AllFin (rule P ν) k) : lam P ν k ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun i hi => (h i (Finset.mem_range.1 hi)).ne

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem cum_shape_self (k : ℕ) (r : ℝ≥0) : (shape P ν k r).cum k = lam P ν k := by
  unfold CycRec.cum lam
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold CycRec.lenAt
  rw [nth_shape_lt (P := P) (ν := ν) k r (Finset.mem_range.1 hi)]
  rfl

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem total_shape (k : ℕ) (r : ℝ≥0) : (shape P ν k r).total = lam P ν k := by
  show CycRec.cum _ (k + 1 - 1) = _
  rw [Nat.add_sub_cancel]
  exact cum_shape_self k r

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem EnvAt.total_eq {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    ρ.total = lam P ν k := by
  rw [h.eq_shape]; exact total_shape k r

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem EnvAt.hGl_eq {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)) = sc - (lam P ν k + r) := by
  unfold CycScheme.hGl
  rw [h.time, h.total_eq, tsub_tsub]

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem E_len' (k : ℕ) : (P.E (rule P ν) k).len = sInf (cand P ν k) := by
  rw [E_eq]
  exact CPath.cut_len _ _

omit [Countable I] [MeasurableSingletonClass I] in
/-- One step does not exceed the budget. -/
theorem step_bud (_hν : CycGood ν) {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}
    (h : EnvAt P ν k r ρ) (_hg : StepGood P sc ν ρ o) (hb : lam P ν k + r ≤ sc) :
    lam P ν k + ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤ sc := by
  have hfin : lam P ν k + r ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨lam_ne_top h.allFin, ENNReal.coe_ne_top⟩
  have h1 : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤ sc - (lam P ν k + r) := by
    rw [← h.hGl_eq]
    exact (by exact_mod_cast sStar_le_h (P := P) (sc := sc) (ρ := ρ) o :
      ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (hOf_le_hGl ρ)
  have h2 := (ENNReal.le_sub_iff_add_le_right hfin hb).1 h1
  rw [ENNReal.coe_add]
  calc _ = ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) + (lam P ν k + r) := by ring
    _ ≤ sc := h2

/-- The budget invariant of a state. -/
def Bud (P : CycPlan I d β) (sc : ℝ≥0∞) (ν : Measure (I × RingSpace d β))
    (st : CycScheme.State I d) : Prop :=
  (st.2 = false → ∀ (k : ℕ) (r : ℝ≥0), EnvAt P ν k r st.1 → lam P ν k + r ≤ sc) ∧
  (st.2 = true → ∃ (k : ℕ) (r : ℝ≥0), st.1 = shape P ν k r ∧ (r : ℝ≥0∞) ≤ sInf (cand P ν k) ∧
    lam P ν k + r ≤ sc ∧ (lam P ν k + r = sc ∨
      ((r : ℝ≥0∞) = sInf (cand P ν k) ∧ ¬ ((k + 1 : ℕ) : ℕ∞) < P.K)))

omit [Countable I] in
omit [MeasurableSingletonClass I] in
theorem bud_init (hν : CycGood ν) (hK : 0 < P.K) : Bud P sc ν (CycScheme.init P) := by
  refine ⟨fun _ k r h => ?_, fun h => absurd h (by simp [CycScheme.init])⟩
  have h0 := envAt_init (P := P) hν hK
  have hk := h.k_unique h0
  subst hk
  have hr := h.r_unique h0
  subst hr
  simp [lam]

theorem bud_upd (hν : CycGood ν) {st : CycScheme.State I d} (o : Outcome (CycS I d β))
    (hI : Inv P sc ν st) (hB : Bud P sc ν st)
    (hg : st.2 = false → StepGood P sc ν st.1 o) : Bud P sc ν (CycScheme.upd P sc st o) := by
  by_cases hend : st.2 = true
  · have : CycScheme.upd P sc st o = st := by
      unfold CycScheme.upd
      rw [ite_eq_left hend]
    rw [this]
    exact hB
  · have hf : st.2 = false := by simpa using hend
    obtain ⟨ρ, b⟩ := st
    simp only at hf
    subst hf
    obtain ⟨k, r, h⟩ : ∃ (k : ℕ) (r : ℝ≥0), EnvAt P ν k r ρ := by
      rcases hI with ⟨-, k, r, h⟩ | ⟨h, -⟩
      · exact ⟨k, r, h⟩
      · exact absurd h (by simp)
    have hb := hB.1 rfl k r h
    have hg' := hg rfl
    simp only at hg'
    have hsb := step_bud hν h hg' hb
    by_cases hs : CycScheme.stops P sc (ρ, false) o
    · have hcs := sInf_cand_eq hν h hg' hs
      by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
      · obtain ⟨h1, h2⟩ := upd_stop_next hν h hg' hs hK
        refine ⟨fun _ k' r' h' => ?_, fun hh => absurd hh (by simp [h1])⟩
        have hk := h'.k_unique h2
        subst hk
        have hr := h'.r_unique h2
        subst hr
        rw [lam_succ, E_len', hcs] at *
        simpa [lam_succ, E_len', hcs] using hsb
      · rw [upd_stop_end hν h hg' hs hK]
        refine ⟨fun hh => absurd hh (by simp), fun _ => ⟨k, r + CycScheme.sStar P sc (ρ, false) o, ?_, hcs.ge, hsb, Or.inr ⟨hcs.symm, hK⟩⟩⟩
        show (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k)⟩ : CycRec I d) = _
        rw [E_eq_of_stops hν h hg' hs]
        rfl
    · obtain ⟨h1, h2⟩ := upd_notStop hν h hg' hs
      refine ⟨fun _ k' r' h' => ?_, fun hh => ?_⟩
      · have hk := h'.k_unique h1
        subst hk
        have hr := h'.r_unique h1
        subst hr
        exact hsb
      · refine ⟨k, r + CycScheme.sStar P sc (ρ, false) o, h1.eq_shape, h1.le_sInf, hsb, Or.inl ?_⟩
        rw [h2] at hh
        have hd := of_decide_eq_true hh
        rw [h.hGl_eq] at hd
        have hfin : lam P ν k + r ≠ ⊤ :=
          ENNReal.add_ne_top.2 ⟨lam_ne_top h.allFin, ENNReal.coe_ne_top⟩
        rw [ENNReal.coe_add, ← add_assoc, hd]
        exact add_tsub_cancel_of_le hb

variable (T : Traj P sc ν)

theorem Traj.bud (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ j, Bud P sc ν (T.S j) := by
  intro j
  induction j with
  | zero => rw [h0]; exact bud_init hν hK
  | succ j ih =>
    rw [T.step]
    exact bud_upd hν _ (T.inv hν hK h0 j) ih (T.good j)

/-- A finished state is a fixed point of the update. -/
theorem Traj.stay_finished {j : ℕ} (hf : (T.S j).2 = true) : ∀ j', j ≤ j' → T.S j' = T.S j := by
  intro j' hj'
  induction j', hj' using Nat.le_induction with
  | base => rfl
  | succ j' hj' ih =>
    rw [T.step, ih]
    unfold CycScheme.upd
    rw [ite_eq_left hf]

end CycSchemeEnv
end ElboimSly.Cyclic

end
