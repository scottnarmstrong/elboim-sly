/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Assemble
public import ElboimSly.Paper.Escape.C57Rec
public import Mathlib

/-!
# Events determined by the first `K` entries are stopped events

ES22 Lemma 5.5 (measurability data of Step 2).

For a plan `P` with all walks finite, a set `S` of environments of the form
`{ν | CycGood ν ∧ (E_0(ν), …, E_{K-1}(ν)) ∈ Φ}` is, as an event of the environment `N`, measurable
for the stopping σ-algebra at `Λ_K` (`measurableSet_preimage_lam`), and measurable for the ambient
σ-algebra of the environments (`measurableSet_entries`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The first `K` coordinates of a truncated final record agree with the final entries once
`Λ_K ≤ t`. -/
theorem coord_trunc_of_lam_le {P : CycPlan ℕ (k + 2) β} (hP : PlanFin P)
    {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {K : ℕ} (hK : (K : ℕ∞) ≤ P.K)
    {t : ℝ≥0} (ht : lam P ν K ≤ (t : ℝ≥0∞)) {m : ℕ} (hm : m < K) :
    (CycRec.trunc t (P.envFinal ν)).coord P.junk m = P.E (rule P ν) m := by
  have hnth := trunc_envFinal_nth (P := P) (ν := ν) P.junk t m
  have hc : P.Cont (rule P ν) m ∧ lam P ν m ≤ (t : ℝ≥0∞) :=
    ⟨(hP.cont_iff hν m).2 (lt_of_lt_of_le (by exact_mod_cast hm) hK),
      (lam_mono hm.le).trans ht⟩
  rw [ite_eq_left hc] at hnth
  have : tgt P ν t m = P.E (rule P ν) m := by
    unfold tgt; rw [ite_eq_left]
    rw [← lam_succ]; exact (lam_mono (Nat.succ_le_of_lt hm)).trans ht
  unfold CycRec.coord
  rw [hnth, this]; rfl

/-- The coordinates of the (untruncated) final record are the final entries, in a good
environment, below `K`. -/
theorem coord_envFinal_of_good_pf {P : CycPlan ℕ (k + 2) β} (hP : PlanFin P)
    {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {m : ℕ} (hm : (m : ℕ∞) < P.K) :
    (P.envFinal ν).coord P.junk m = P.E (rule P ν) m := by
  have h := CycPlan.cycFinal_nth_gen P (rule P ν) m
  have e : P.envFinal ν = P.cycFinal (rule P ν) := rfl
  unfold CycRec.coord
  rw [e, h, ite_eq_left ((hP.cont_iff hν m).2 hm)]
  rfl

/-- The first `K` coordinates of a record, as a tuple of entries. -/
def recTuple (junk : CycEntry ℕ (k + 2)) (K : ℕ) (σ : CycRec ℕ (k + 2)) :
    Fin K → CycEntry ℕ (k + 2) :=
  fun m => σ.coord junk m

theorem measurable_recTuple (junk : CycEntry ℕ (k + 2)) (K : ℕ) :
    Measurable (recTuple junk K) :=
  measurable_pi_iff.2 fun m => CycRec.measurable_coord junk m

/-- An environment event that is `CycGood` and a measurable property of the first `K` final
entries is measurable. -/
theorem measurableSet_entries {P : CycPlan ℕ (k + 2) β} (hP : PlanFin P) {K : ℕ}
    (hK : (K : ℕ∞) ≤ P.K) {Φ : Set (Fin K → CycEntry ℕ (k + 2))} (hΦ : MeasurableSet Φ)
    {S : Set (Measure (CycS ℕ (k + 2) β))}
    (hS : ∀ ν, ν ∈ S ↔ CycGood ν ∧ (fun m : Fin K => P.E (rule P ν) m) ∈ Φ) :
    MeasurableSet S := by
  have hR := measurable_envFinal_cycNgood P
    (N := fun ν : Measure (CycS ℕ (k + 2) β) => ν) measurable_id
  have h1 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
      recTuple P.junk K (P.envFinal (cycNgood (fun ν => ν) ν)) ∈ Φ} :=
    ((measurable_recTuple P.junk K).comp hR) hΦ
  have e : S = {ν | CycGood ν} ∩
      {ν | recTuple P.junk K (P.envFinal (cycNgood (fun ν => ν) ν)) ∈ Φ} := by
    ext ν
    rw [hS ν]
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun hν => ?_
    have : cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν = ν := by simp [cycNgood, hν]
    rw [this]
    have hE : recTuple P.junk K (P.envFinal ν) = fun m : Fin K => P.E (rule P ν) m := by
      funext m
      exact coord_envFinal_of_good_pf hP hν (lt_of_lt_of_le (by exact_mod_cast m.2) hK)
    rw [hE]
  rw [e]
  exact measurableSet_cycGood.inter h1

section stopped

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS ℕ (k + 2) β)} (P : CycPlan ℕ (k + 2) β)

theorem measurableSet_filt_of_null (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω) (s : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet A) (h0 : Pr A = 0) :
    MeasurableSet[cycMultiFilt P 𝒢₀ hNm h𝒢 Pr s] A := by
  show MeasurableSet[cycFiltration Pr 𝒢₀ (fun ω => P.envFinal (cycNgood N ω)) s] _
  rw [cycFiltration_eq 𝒢₀ P.junk Pr]
  exact le_sup_right (a := 𝒢₀ ⊔ MeasurableSpace.comap
    (fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω))) inferInstance) _
    (MeasurableSpace.measurableSet_generateFrom ⟨hA, h0⟩)

/-- **An event determined by the first `K` entries lies in `ℱ_{Λ_K}`.** -/
theorem measurableSet_preimage_lam (hP : PlanFin P) (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ)
    (Pr : Measure Ω) (hgood : ∀ᵐ ω ∂Pr, CycGood (N ω)) {K : ℕ} (hK : (K : ℕ∞) ≤ P.K)
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hNm h𝒢 Pr) (lamT P N K))
    {Φ : Set (Fin K → CycEntry ℕ (k + 2))} (hΦ : MeasurableSet Φ)
    {S : Set (Measure (CycS ℕ (k + 2) β))}
    (hS : ∀ ν, ν ∈ S ↔ CycGood ν ∧ (fun m : Fin K => P.E (rule P ν) m) ∈ Φ) :
    MeasurableSet[hT.measurableSpace] (N ⁻¹' S) := by
  have key : ∀ t : ℝ≥0, MeasurableSet[cycMultiFilt P 𝒢₀ hNm h𝒢 Pr t]
      (N ⁻¹' S ∩ {ω | lamT P N K ω ≤ (t : WithTop ℝ≥0)}) := by
    intro t
    have hbad : MeasurableSet (N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}) :=
      hNm measurableSet_cycGood.compl
    have hbad0 : Pr (N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}) = 0 := ae_iff.1 hgood
    have hgoodF : MeasurableSet[cycMultiFilt P 𝒢₀ hNm h𝒢 Pr t] (N ⁻¹' {ν | CycGood ν}) := by
      have : N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | CycGood ν} =
          (N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν})ᶜ := by
        ext ω; simp
      rw [this]
      exact (measurableSet_filt_of_null 𝒢₀ P hNm h𝒢 Pr t hbad hbad0).compl
    have hΨ : MeasurableSet {σ : CycRec ℕ (k + 2) | recTuple P.junk K σ ∈ Φ} :=
      (measurable_recTuple P.junk K) hΦ
    have hset : N ⁻¹' S ∩ {ω | lamT P N K ω ≤ (t : WithTop ℝ≥0)} =
        N ⁻¹' {ν | CycGood ν} ∩
          ({ω | CycRec.trunc t (P.envFinal (cycNgood N ω)) ∈
            {σ : CycRec ℕ (k + 2) | recTuple P.junk K σ ∈ Φ}} ∩
            {ω | lamT P N K ω ≤ (t : WithTop ℝ≥0)}) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      have hle : lamT P N K ω ≤ (t : WithTop ℝ≥0) ↔ lam P (cycNgood N ω) K ≤ (t : ℝ≥0∞) := Iff.rfl
      constructor
      · rintro ⟨hω, hlam⟩
        have hg := ((hS _).1 hω).1
        have hng : cycNgood N ω = N ω := by simp [cycNgood, hg]
        refine ⟨hg, ?_, hlam⟩
        have hE : recTuple P.junk K (CycRec.trunc t (P.envFinal (cycNgood N ω))) =
            fun m : Fin K => P.E (rule P (N ω)) m := by
          funext m
          have := hle.1 hlam
          rw [hng] at this ⊢
          exact coord_trunc_of_lam_le hP hg hK this m.2
        rw [hE]; exact ((hS _).1 hω).2
      · rintro ⟨hg, hmem, hlam⟩
        have hng : cycNgood N ω = N ω := by simp [cycNgood, hg]
        refine ⟨(hS _).2 ⟨hg, ?_⟩, hlam⟩
        have hE : recTuple P.junk K (CycRec.trunc t (P.envFinal (cycNgood N ω))) =
            fun m : Fin K => P.E (rule P (N ω)) m := by
          funext m
          have := hle.1 hlam
          rw [hng] at this ⊢
          exact coord_trunc_of_lam_le hP hg hK this m.2
        rw [hE] at hmem; exact hmem
    rw [hset]
    exact hgoodF.inter ((measurableSet_trunc_cycMultiFilt 𝒢₀ P hNm h𝒢 Pr t hΨ).inter (hT t))
  have hU : N ⁻¹' S = ⋃ n : ℕ, N ⁻¹' S ∩ {ω | lamT P N K ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · intro h
      have hne := lamT_ne_top (N := N) P hP ω hK
      obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, lamT P N K ω = r := ⟨_, (ENNReal.coe_toNNReal hne).symm⟩
      obtain ⟨n, hn⟩ := exists_nat_ge r
      exact ⟨n, h, by rw [hr]; exact_mod_cast hn⟩
    · rintro ⟨n, h, -⟩; exact h
  rw [hT.measurableSet]
  refine ⟨?_, key⟩
  rw [hU]
  exact MeasurableSet.iUnion fun n => le_iSup (cycMultiFilt P 𝒢₀ hNm h𝒢 Pr) (n : ℝ≥0) _ (key n)

end stopped

end ElboimSly.Paper.Escape
