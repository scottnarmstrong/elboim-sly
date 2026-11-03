/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Meas
public import ElboimSly.Paper.Escape.LamStopping
public import ElboimSly.Paper.Escape.C57Rec
public import ElboimSly.Paper.Escape.Plan5Shift
public import ElboimSly.Paper.Avoid.Setting
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import ElboimSly.Foundations.Cyclic.CycMultiCond
public import Mathlib

/-!
# `{N ∈ 𝒦}` and `{N ∈ 𝒦 ∩ 𝒜_i}` lie in the stopped σ-algebras `ℱ_{Λ₁}` and `ℱ_{Λ_{I+1}}`

t' and escK(β'); 𝒜_i, 𝒜, 𝒢(β'); ES22 Proposition 5.2.

For the plan `𝒫₅(B, β', i)` with filtration `ℱ = cycMultiFilt`:

* `isStoppingTime_lamT1`, `isStoppingTime_lamTI1`: `S₁ = Λ₁` and `S₂ = Λ_{I+1}` are stopping times;
* `ae_lamT1_ne_top`, `ae_lamTI1_ne_top`: they are almost surely finite;
* `measurableSet_K_S1`: `{N ∈ 𝒦(β')} ∈ ℱ_{S₁}`;
* `measurableSet_KA_S2`: `{N ∈ 𝒦(β') ∩ 𝒜_i} ∈ ℱ_{S₂}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem plan5_K (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) :
    (plan5 n β tn u β' i hlog).K = ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞) := rfl

/-- A set determined by the good event of `N` and a measurable set of the stopped record. -/
theorem measurableSet_good_inter_rec {P : CycPlan ℕ (k + 2) β}
    (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ S.space.ppp.measurable S.space.le Pr) T)
    {A : Set (CycRec ℕ (k + 2))} (hA : MeasurableSet A) :
    MeasurableSet[hT.measurableSpace]
      ({ω | CycGood (N ω)} ∩ (cycRecStop P (cycNgood N) T) ⁻¹' A) := by
  refine MeasurableSet.inter ?_ ?_
  · have hnull : MeasurableSet[cycNull Pr] {ω | CycGood (N ω)}ᶜ := by
      refine MeasurableSpace.measurableSet_generateFrom ⟨?_, ?_⟩
      · exact (S.space.ppp.measurable measurableSet_cycGood).compl
      · have := ae_cycGood' S.space.ppp
        rw [ae_iff] at this
        show Pr {ω | ¬CycGood (N ω)} = 0
        exact this
    have hF : ∀ t, MeasurableSet[cycMultiFilt P 𝒢₀ S.space.ppp.measurable S.space.le Pr t]
        {ω | CycGood (N ω)} := by
      intro t
      show MeasurableSet[cycFiltration Pr 𝒢₀ (fun ω => P.envFinal (cycNgood N ω)) t] _
      unfold cycFiltration
      exact (le_sup_right (a := 𝒢₀ ⊔ _) (b := cycNull Pr)) _ hnull.of_compl
    refine ⟨?_, fun t => (hF t).inter (hT t)⟩
    exact le_iSup (cycMultiFilt P 𝒢₀ S.space.ppp.measurable S.space.le Pr) 0 _ (hF 0)
  · have hm := measurable_cycRecStop
      (measurable_trunc_multiFilt P 𝒢₀ S.space.le Pr
        (measurable_envFinal_cycNgood P S.space.ppp.measurable)) hT
    exact hm hA

theorem cycNgood_of_good {ω : Ω} (hω : CycGood (N ω)) : cycNgood N ω = N ω := by
  simp [cycNgood, hω]

/-- The entries `0, …, K - 1` of the record stopped at `Λ_K` are the final entries of `𝒫₅`. -/
theorem coord_recStop_lamT (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    {K m : ℕ} (hK : K ≤ escIstar n (escJ n) + 2) (hm : m < K) {ω : Ω} (hω : CycGood (N ω)) :
    (cycRecStop (plan5 n β tn u β' i hlog) (cycNgood N)
      (lamT (plan5 n β tn u β' i hlog) N K) ω).coord (plan5 n β tn u β' i hlog).junk m =
      ent5 n tn u β' i hlog (N ω) m := by
  have h := coord_trunc_lam (plan5_planFin n β tn u β' i hlog) (cycGood_cycNgood N ω)
    (K := K) (by rw [plan5_K]; exact_mod_cast hK) hm
  have e := cycNgood_of_good hω
  rw [e] at h
  have hs : SRW.stopReal (lamT (plan5 n β tn u β' i hlog) N K) ω =
      (lam (plan5 n β tn u β' i hlog) (N ω) K).toNNReal := by
    show (lam (plan5 n β tn u β' i hlog) (cycNgood N ω) K).toNNReal = _
    rw [e]
  unfold cycRecStop
  rw [hs, e]
  exact h

theorem isStoppingTime_lamT1 (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (n' : ℕ) (u : EscV k)
    (β' i : ℕ) (hlog : 1 < Real.log β) :
    IsStoppingTime (cycMultiFilt (plan5 n' β (indScale t₀ n) u β' i hlog) 𝒢₀
      S.space.ppp.measurable S.space.le Pr)
      (lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N 1) :=
  isStoppingTime_lam_succ (k := 0) 𝒢₀ _ S.space.ppp.measurable S.space.le Pr
    (plan5_planFin n' β _ u β' i hlog) (by rw [plan5_K]; exact_mod_cast Nat.succ_pos _)

theorem isStoppingTime_lamTI1 (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (n' : ℕ)
    (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) :
    IsStoppingTime (cycMultiFilt (plan5 n' β (indScale t₀ n) u β' i hlog) 𝒢₀
      S.space.ppp.measurable S.space.le Pr)
      (lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N (escIstar n' (escJ n') + 1)) :=
  isStoppingTime_lam_succ (k := escIstar n' (escJ n')) 𝒢₀ _ S.space.ppp.measurable S.space.le Pr
    (plan5_planFin n' β _ u β' i hlog) (by rw [plan5_K]; exact_mod_cast (by omega : escIstar n' (escJ n') < escIstar n' (escJ n') + 2))

theorem ae_lamT1_ne_top (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (n' : ℕ) (u : EscV k)
    (β' i : ℕ) (hlog : 1 < Real.log β) :
    Pr {ω | lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N 1 ω ≠ ⊤} = 1 := by
  have := S.space.ppp.isProbabilityMeasure
  have : {ω | lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N 1 ω ≠ ⊤} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact lamT_ne_top _ (plan5_planFin n' β _ u β' i hlog) ω
      (by rw [plan5_K]; exact_mod_cast (by omega : 1 ≤ escIstar n' (escJ n') + 2))
  rw [this]; exact measure_univ

theorem ae_lamTI1_ne_top (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (n' : ℕ) (u : EscV k)
    (β' i : ℕ) (hlog : 1 < Real.log β) :
    Pr {ω | lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N (escIstar n' (escJ n') + 1) ω ≠ ⊤} =
      1 := by
  have := S.space.ppp.isProbabilityMeasure
  have : {ω | lamT (plan5 n' β (indScale t₀ n) u β' i hlog) N (escIstar n' (escJ n') + 1) ω ≠ ⊤} =
      univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact lamT_ne_top _ (plan5_planFin n' β _ u β' i hlog) ω
      (by rw [plan5_K]; exact_mod_cast (by omega : escIstar n' (escJ n') + 1 ≤ escIstar n' (escJ n') + 2))
  rw [this]; exact measure_univ

/-- `{N ∈ 𝒦(β')} ∈ ℱ_{S₁}`, `S₁ = Λ₁`. -/
theorem measurableSet_K_S1 (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (u : EscV k)
    (hadm : EscAdmissible (escJ n) u) (htn : 0 < indScale t₀ n) (β' i : ℕ)
    (hlog : 1 < Real.log β)
    (hT : IsStoppingTime (cycMultiFilt (plan5 n β (indScale t₀ n) u β' i hlog) 𝒢₀
      S.space.ppp.measurable S.space.le Pr)
      (lamT (plan5 n β (indScale t₀ n) u β' i hlog) N 1)) :
    MeasurableSet[hT.measurableSpace] (N ⁻¹' escKSet β (indScale t₀ n) n β' u) := by
  have hA : MeasurableSet {ρ : CycRec ℕ (k + 2) | EscKEnt β (indScale t₀ n) n u β'
      (ρ.coord (plan5 n β (indScale t₀ n) u β' i hlog).junk 0)} :=
    (CycRec.measurable_coord _ 0) (measurableSet_escKEnt β (indScale t₀ n) n u β')
  have h := measurableSet_good_inter_rec (P := plan5 n β (indScale t₀ n) u β' i hlog) S hT hA
  convert h using 1
  ext ω
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
  rw [escK_iff_ent5 n (indScale t₀ n) u β' i hlog hadm htn]
  constructor
  · rintro ⟨hω, h2⟩
    refine ⟨hω, ?_⟩
    rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := 1) (by omega) (by omega) hω]
    exact h2
  · rintro ⟨hω, h2⟩
    refine ⟨hω, ?_⟩
    rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := 1) (by omega) (by omega) hω] at h2
    exact h2

/-- `{N ∈ 𝒦(β') ∩ 𝒜_i} ∈ ℱ_{S₂}`, `S₂ = Λ_{I+1}`. -/
theorem measurableSet_KA_S2 (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (u : EscV k)
    (hadm : EscAdmissible (escJ n) u) (htn : 0 < indScale t₀ n) (β' i : ℕ)
    (hlog : 1 < Real.log β) (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n))
    (hT : IsStoppingTime (cycMultiFilt (plan5 n β (indScale t₀ n) u β' i hlog) 𝒢₀
      S.space.ppp.measurable S.space.le Pr)
      (lamT (plan5 n β (indScale t₀ n) u β' i hlog) N (escIstar n (escJ n) + 1))) :
    MeasurableSet[hT.measurableSpace]
      (N ⁻¹' (escKSet β (indScale t₀ n) n β' u ∩ escASet n u β' hlog i)) := by
  set P := plan5 n β (indScale t₀ n) u β' i hlog with hP
  have hA : MeasurableSet {ρ : CycRec ℕ (k + 2) |
      EscKEnt β (indScale t₀ n) n u β' (ρ.coord P.junk 0) ∧
        (ρ.coord P.junk i).len = (4 : ℝ≥0∞) ^ n} := by
    refine MeasurableSet.inter ?_ ?_
    · exact (CycRec.measurable_coord _ 0) (measurableSet_escKEnt β (indScale t₀ n) n u β')
    · exact (measurable_entry_len'.comp (CycRec.measurable_coord _ i)) (measurableSet_singleton _)
  have h := measurableSet_good_inter_rec (P := P) S hT hA
  convert h using 1
  ext ω
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, escASet]
  rw [escK_iff_ent5 n (indScale t₀ n) u β' i hlog hadm htn]
  have hI : 0 + 1 ≤ escIstar n (escJ n) + 1 := by omega
  constructor
  · rintro ⟨⟨hω, h2⟩, -, h3⟩
    refine ⟨hω, ?_, ?_⟩
    · rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := escIstar n (escJ n) + 1)
        (by omega) (by omega) hω]
      exact h2
    · rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := escIstar n (escJ n) + 1)
        (by omega) (by omega) hω]
      have := ent5_succ_eq_escEntry n (indScale t₀ n) u β' i hlog (N ω) (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      rw [this]; exact h3
  · rintro ⟨hω, h2, h3⟩
    refine ⟨⟨hω, ?_⟩, hω, ?_⟩
    · rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := escIstar n (escJ n) + 1)
        (by omega) (by omega) hω] at h2
      exact h2
    · rw [coord_recStop_lamT n (indScale t₀ n) u β' i hlog (K := escIstar n (escJ n) + 1)
        (by omega) (by omega) hω] at h3
      have := ent5_succ_eq_escEntry n (indScale t₀ n) u β' i hlog (N ω) (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      rw [← this]; exact h3

end ElboimSly.Paper.Escape
