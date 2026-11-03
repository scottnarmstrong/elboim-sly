/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoupleAux
public import ElboimSly.Foundations.Cyclic.CycRegenFiltWalk
public import ElboimSly.Foundations.Cyclic.CycRegenRecordTrunc
public import Mathlib

/-!
# ES22 §4: Lemma 4.1, reading the history off the record

ES22 Lemma 4.1 (proof: the encoded history and `α(T)` are measurable functions of the
record `cycRec(T)`, paths (b)).

* `measurable_recWalkAt_var`: `(ρ, r) ↦ W_ρ(r)` is jointly measurable.
* `recAlpha ρ`: the start of the last (running) piece of a record, `cum (num - 1)`; for the
  truncated record of a good environment it is `σ_{count(s)}`, i.e. `α(s) = regenStart`.
* `isRCPath_comp_mono`: composition of a right-continuous path with a continuous monotone map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

section meas

variable {d : ℕ}

theorem measurable_gluedCount_var {α : Type*} [MeasurableSpace α] {σ : α → ℕ → ℝ≥0∞}
    (hσ : ∀ n, Measurable fun a => σ a n) {t : α → ℝ≥0} (ht : Measurable t) :
    Measurable fun a => gluedCount (σ a) (t a) := by
  have hS : ∀ m, MeasurableSet {a | σ a m ≤ (t a : ℝ≥0∞)} := fun m =>
    measurableSet_le (hσ m) (measurable_coe_nnreal_ennreal.comp ht)
  refine measurable_to_countable' fun n => ?_
  have : (fun a => gluedCount (σ a) (t a)) ⁻¹' {n} =
      ({a | σ a n ≤ (t a : ℝ≥0∞)} ∩ ⋂ m, ⋂ (_ : n < m), {a | σ a m ≤ (t a : ℝ≥0∞)}ᶜ) ∪
      ({_a | n = 0} ∩ ((⋂ m, {a | σ a m ≤ (t a : ℝ≥0∞)}ᶜ) ∪
        ⋂ N, ⋃ m, ⋃ (_ : N < m), {a | σ a m ≤ (t a : ℝ≥0∞)})) := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, gluedCount, sSup_nat_eq_iff, mem_union,
      mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, exists_prop]
  rw [this]
  refine MeasurableSet.union ((hS n).inter ?_) (MeasurableSet.inter (MeasurableSet.const _) ?_)
  · exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hS m).compl
  · refine MeasurableSet.union (MeasurableSet.iInter fun m => (hS m).compl) ?_
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
      hS m

/-- `(ρ, r) ↦ W_ρ(r)` is jointly measurable. -/
theorem measurable_recWalkAt_var (junk : CycEntry ℕ d) :
    Measurable fun p : CycRec ℕ d × ℝ≥0 => recWalkAt junk p.2 p.1 := by
  have hσ : ∀ n, Measurable fun p : CycRec ℕ d × ℝ≥0 => cumTop p.1 n := fun n =>
    (measurable_cumTop junk n).comp measurable_fst
  have hF : ∀ k, Measurable fun p : CycRec ℕ d × ℝ≥0 =>
      (p.1.coord junk k).path.fn (p.2 - (cumTop p.1 k).toNNReal) := fun k =>
    measurable_fn_at (fun p : CycRec ℕ d × ℝ≥0 => (p.1.coord junk k).path)
      (measurable_entry_path.comp ((CycRec.measurable_coord junk k).comp measurable_fst)) _
      (measurable_snd.sub (ENNReal.measurable_toNNReal.comp (hσ k)))
  exact measurable_index (measurable_gluedCount_var hσ measurable_snd) hF

/-- The start of the running piece of a record: `cum (num - 1)`. -/
noncomputable def recAlpha (ρ : CycRec ℕ d) : ℝ≥0∞ := cumTop ρ (ρ.num.toNat - 1)

theorem measurable_recAlpha (junk : CycEntry ℕ d) : Measurable (recAlpha (d := d)) := by
  have hm : Measurable fun ρ : CycRec ℕ d => ρ.num.toNat - 1 := by
    have h1 : Measurable fun ρ : CycRec ℕ d => ρ.num := CycRec.measurable_num
    exact (measurable_from_top (f := fun e : ℕ∞ => e.toNat - 1)).comp h1
  exact measurable_index (m := fun ρ : CycRec ℕ d => ρ.num.toNat - 1) hm
    (F := fun k ρ => cumTop ρ k) (measurable_cumTop junk)

end meas

section regen

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (CycS ℕ d β)}

/-- For the truncated record of a good environment, `recAlpha` is `σ_{count(s)}`. -/
theorem recAlpha_trunc_regPlan (hν : CycGood ν) (s : ℝ≥0) :
    recAlpha (CycRec.trunc s ((regPlan d β).envFinal ν)) =
      ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (s : ℝ)) := by
  unfold recAlpha
  rw [num_trunc_regPlan hν s]
  simp only [ENat.toNat_natCast, Nat.add_sub_cancel]
  rw [cumTop_trunc_regPlan hν s, ite_eq_left le_rfl]

end regen

section congr

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*}

omit [Fact (0 < β)] in
theorem avoidEnv_congr {N₁ N₂ : Ω → Measure (CycS ℕ d β)} {ω : Ω} (h : N₁ ω = N₂ ω) :
    avoidEnv N₁ ω = avoidEnv N₂ ω := by
  unfold avoidEnv
  rw [h]

omit [Fact (0 < β)] in
theorem avoidWalk_congr {N₁ N₂ : Ω → Measure (CycS ℕ d β)} {ω : Ω} (h : N₁ ω = N₂ ω) :
    avoidWalk N₁ ω = avoidWalk N₂ ω := by
  unfold avoidWalk
  rw [avoidEnv_congr h]

end congr

/-- A right-continuous path composed with a monotone continuous time change is right-continuous. -/
theorem isRCPath_comp_mono {d : ℕ} {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) {g : ℝ≥0 → ℝ≥0}
    (hg : Continuous g) (hmono : Monotone g) : IsRCPath (x ∘ g) := by
  intro t
  have h1 : Tendsto g (𝓝[≥] t) (𝓝[≥] g t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hmono hs
  exact h1.eventually (hx (g t))

end ElboimSly.Paper

end
