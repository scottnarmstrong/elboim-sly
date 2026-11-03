/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWFinal
public import ElboimSly.Paper.Escape.Es55DetProof
public import ElboimSly.Paper.Escape.Es55JumpProof
public import Mathlib

/-!
# Lemma 5.5, Step 1: the pathwise step `es55PW`

ES22 Lemma 5.5, Step 1.  Coupling glue: `es5_plan_coupling` at `S₃ = Λ_{I+2}` with the
`ℱ_{S₃}`-measurable datum `δ_c`, and the deterministic assembly `pw_det`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

theorem tilde_singleton_mem {Ω S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (N N' : Ω → Measure S) (Z : Ω → Set S) (ω : Ω) {x : S} (hx : x ∈ Z ω) :
    tildeMeasure N N' Z ω {x} = N' ω {x} := by
  unfold tildeMeasure
  rw [Measure.add_apply, Measure.restrict_apply (measurableSet_singleton x),
    Measure.restrict_apply (measurableSet_singleton x)]
  have : ({x} : Set S) ∩ (Z ω)ᶜ = ∅ := by
    ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false,
      iff_false, not_and, not_not]; rintro rfl; exact hx
  rw [this, measure_empty, zero_add, inter_eq_left.2 (singleton_subset_iff.2 hx)]

theorem tilde_singleton_notMem {Ω S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (N N' : Ω → Measure S) (Z : Ω → Set S) (ω : Ω) {x : S} (hx : x ∉ Z ω) :
    tildeMeasure N N' Z ω {x} = N ω {x} := by
  unfold tildeMeasure
  rw [Measure.add_apply, Measure.restrict_apply (measurableSet_singleton x),
    Measure.restrict_apply (measurableSet_singleton x)]
  have : ({x} : Set S) ∩ Z ω = ∅ := by
    ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false,
      iff_false, not_and]; rintro rfl; exact hx
  rw [this, measure_empty, add_zero, inter_eq_left.2 (singleton_subset_iff.2 hx)]

variable {k : ℕ}

/-- **The pathwise step of Step 1 of ES22 Lemma 5.5.** -/
theorem es55PW : Es55PW k := by
  obtain ⟨bD, HD⟩ := es55DetAll k
  refine ⟨bD, ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' N'' hS hN'' hI3 hβ u hadm β' i hi1 hiI
  have hn : 2 ≤ n := by
    have h1 := hS.params.eight_le
    have h2 := hS.params.lt
    have h3 := hS.params.five_le
    omega
  have hj4 : 4 ≤ escJ n := by have := escJ_ge_twenty hn; omega
  have hN := hS.space.ppp
  have hN' := hS.space.ppp'
  have hI1 := hS.space.indep
  have hI2 := hS.space.indep'
  have h𝒢 := hS.space.le
  have := hN.isProbabilityMeasure
  set hlog := hlog_of_params hS.params with hhlog
  set P := plan5 n β (indScale t₀ n) u β' i hlog with hP
  set I := escIstar n (escJ n) with hI
  have hPfin : PlanFin P := plan5_planFin n β (indScale t₀ n) u β' i hlog
  have hKeq : P.K = ((I + 2 : ℕ) : ℕ∞) := rfl
  have hK0 : 0 < P.K := by rw [hKeq]; exact_mod_cast Nat.succ_pos _
  have hk1 : ((I + 1 : ℕ) : ℕ∞) < P.K := by rw [hKeq]; exact_mod_cast Nat.lt_succ_self _
  have hk2 : ((I + 2 : ℕ) : ℕ∞) ≤ P.K := le_rfl
  have hT := isStoppingTime_lam_succ 𝒢₀ P hN.measurable h𝒢 Pr hPfin hk1
  have hfin : ∀ ω, lamT P N (I + 2) ω ≠ ⊤ := fun ω => lamT_ne_top P hPfin ω hk2
  have hδ := (measurable_z55 𝒢₀ hN hN' hI1 hI2 (n := n) (tn := indScale t₀ n) (u := u)
    (β' := β') (i := i) hlog hK0 h𝒢 hT rfl).2
  obtain ⟨⟨hfresh, -⟩, -, -, hb, -, -⟩ :=
    es5_plan_coupling.{0, 0, 0} P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK0 h𝒢 hT hδ
  obtain ⟨-, -, -, hrm, -⟩ := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT
  have hgoodN : ∀ᵐ ω ∂Pr, CycGood (N ω) := by
    filter_upwards [ae_cycNgood_eq hN] with ω h
    rw [← h]; exact cycGood_cycNgood N ω
  have hgoodT : ∀ᵐ ω ∂Pr, CycGood (tildeMeasure N N'
      (cycRegionStop P (cycNgood N) (lamT P N (I + 2))) ω) := by
    have hF : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν} :=
      measurableSet_cycGood.compl
    have h := hfresh (A := univ) MeasurableSet.univ hF
    have e : {ω | lamT P N (I + 2) ω ≠ ⊤} = univ := by ext ω; simp [hfin ω]
    simp only [e, univ_inter, measure_univ, one_mul, Measure.map_apply hN.measurable hF] at h
    have h0 : Pr (N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}) = 0 :=
      ae_iff.1 hgoodN
    rw [h0] at h
    exact ae_iff.2 h
  have hno := pwc_ae_noRings hN (escPoint n (escJ n) u i) (β' : ℝ)
  filter_upwards [hb, hrm, hgoodN, hgoodT, hno] with ω hbω hrmω hgN hgT hnoω
  intro hH hmem
  have hdet := HD hS hβ u hadm β' i hi1 hiI (N ω) hH
  have hng : cycNgood N ω = N ω := by unfold cycNgood; rw [ite_eq_left hgN]
  set T := lamT P N (I + 2) with hTdef
  set R := cycRegionStop P (cycNgood N) T ω with hRdef
  have hR : R ⊆ ⋃ m ∈ Finset.range (I + 2),
      (ent5 n (indScale t₀ n) u β' i hlog (N ω) m).region β := by
    have := cycRegionStop_lamT_subset hPfin N hk2 ω
    rwa [hng] at this
  have hδω : delta55 n (indScale t₀ n) u β' i hlog N ω =
      ((0 : ℕ), entEnd (ent5 n (indScale t₀ n) u β' i hlog (N ω) 0),
        (ent5 n (indScale t₀ n) u β' i hlog (N ω) 0).len.toReal, true) := by
    unfold delta55; rw [z55_eq hgN]
  have hzω := z55_eq (n := n) (tn := indScale t₀ n) (u := u) (β' := β') (i := i) (hlog := hlog)
    (N := N) hgN
  rw [hzω] at hmem
  have hRN : (N ω).restrict R = (cycRecStop P (cycNgood N) T ω).rm β := hrmω (hfin ω)
  refine pw_det hj4 hi1 hiI hadm hgN hgT hH hdet hR (D := cycDiscrepancy P N N' T ω)
    (fun x hx => hx.1) ?_ ?_ ?_ (fun m => contSeq_zero_apply (N'' ω) m) (fun m s => walkMap_rc _ s) ?_
    hmem hnoω
  · intro x hx
    obtain ⟨hxR, hne⟩ := hx
    have h1 : tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω {x} = N' ω {x} := tilde_singleton_mem N N' _ ω hxR
    have h2 : (cycRecStop P (cycNgood N) T ω).rm β {x} = N ω {x} := by
      rw [← hRN, Measure.restrict_apply (measurableSet_singleton x),
        inter_eq_left.2 (singleton_subset_iff.2 hxR)]
    by_contra hcon
    push Not at hcon
    rw [h1] at hcon
    rw [h2, hcon.2] at hne
    exact hne hcon.1
  · intro x hx
    exact tilde_singleton_notMem N N' _ ω hx
  · intro r hr s hs
    have := hbω (hfin ω) r (Or.inl (by rw [hδω]; exact hr)) s hs
    rw [hδω] at this
    exact this
  · unfold regenY planFirst
    rw [hδω]
    rfl

end ElboimSly.Paper.Escape
