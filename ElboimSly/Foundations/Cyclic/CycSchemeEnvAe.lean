/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPPP
public import ElboimSly.Foundations.Cyclic.CycRingMeasure
public import ElboimSly.Foundations.Interchange.GoodAs
public import ElboimSly.Foundations.PPP.Restriction
public import ElboimSly.Foundations.PPP.Operations
public import Mathlib

/-!
# The environment scheme (b): the states reproduce the environment world-lines, almost surely

The environment scheme (b). `ae_inv`: for a run of the environment scheme (any plan with
`K ≥ 1`), almost surely `N` is good and for every `j` the state `(ρ_j(H_j), ε_j(H_j))` satisfies
`Inv`. `ae_initial_pieces`: almost surely, for every `j`, `ρ_j(H_j)` consists of the first `k`
environment world-lines in full and the initial piece, at its current time `r_j ≤ ℓ_k`, of the
environment world-line `E k`; and `N|_{𝒵_j} = cycRM(ρ_j(H_j))` (`restrict_region_eq_rm`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)]

omit [Countable I] [Fact (0 < β)] in
/-- The slice `ν^ι` is the restriction to `{ι} × S_β` projected to `S_β`. -/
theorem cycSlice_eq_map_restrict' (ι : I) (ν : Measure (I × RingSpace d β)) :
    cycSlice ι ν = (ν.restrict ({ι} ×ˢ univ)).map Prod.snd := by
  ext A hA
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left ι).comap_apply, Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext ⟨a, x⟩
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_univ,
    and_true, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl, rfl⟩

omit [Countable I] in
theorem slice_intensity' (ι : I) :
    (((Measure.count : Measure I).prod (ringIntensity d β)).restrict ({ι} ×ˢ univ)).map
      Prod.snd = ringIntensity d β := by
  have : SFinite (ringIntensity d β) := by unfold ringIntensity; infer_instance
  ext A hA
  rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA)]
  have : Prod.snd ⁻¹' A ∩ ({ι} ×ˢ univ : Set (I × RingSpace d β)) = {ι} ×ˢ A := by
    ext ⟨a, x⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_univ, and_true]
    tauto
  rw [this, Measure.prod_prod, Measure.count_singleton, one_mul]

omit [Countable I] in
/-- The copies `N^ι` of a `PPP(# ⊗ μ_β)` are `PPP(μ_β)`. -/
theorem isPoissonPointProcess_slice' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (I × RingSpace d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) P) (ι : I) :
    IsPoissonPointProcess (fun ω => cycSlice ι (N ω)) (ringIntensity d β) P := by
  have h := (hN.restrict (A := {ι} ×ˢ univ)
    ((measurableSet_singleton ι).prod MeasurableSet.univ)).map_measure
    (measurable_snd : Measurable (Prod.snd : I × RingSpace d β → RingSpace d β))
  have e : ((cycIntensity I d β).restrict ({ι} ×ˢ univ)).map Prod.snd = ringIntensity d β :=
    slice_intensity' ι
  rw [e] at h
  simpa only [cycSlice_eq_map_restrict'] using h

/-- A `PPP(# ⊗ μ_β)` is almost surely good in every copy. Configurations are a.s. good. -/
theorem ae_cycGood' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (I × RingSpace d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) P) : ∀ᵐ ω ∂P, CycGood (N ω) :=
  ae_all_iff.2 fun ι => Interchange.ae_good (isPoissonPointProcess_slice' hN ι)

variable {P : CycPlan I d β} {sc : ℝ≥0∞} {ν : Measure (I × RingSpace d β)}

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem EnvAt.le_sInf {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    (r : ℝ≥0∞) ≤ sInf (cand P ν k) := by
  rcases h.pre with rfl | h
  · simp
  · exact _root_.le_sInf fun c hc => (h c hc).le

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_rec_lt {k : ℕ} (e : CycEntry I d) {i : ℕ} (hi : i < k) :
    CycRec.nth (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k) e⟩ : CycRec I d) i =
      some (P.E (rule P ν) i) := by
  simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_of_lt hi)]
  congr 1
  have : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this]
  simp only [CycRec.snoc, Fin.snoc_castSucc]
  exact P.ideal_apply (rule P ν) k ⟨i, hi⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem total_ne_top {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) : ρ.total ≠ ⊤ := by
  rw [h.rec_eq]
  show CycRec.cum _ (k + 1 - 1) ≠ ⊤
  rw [Nat.add_sub_cancel]
  unfold CycRec.cum
  refine ENNReal.sum_ne_top.2 fun i hi => ?_
  have hik : i < k := Finset.mem_range.1 hi
  unfold CycRec.lenAt
  rw [nth_rec_lt (P := P) (ν := ν) _ hik]
  exact (h.allFin i hik).ne

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem hGl_top {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    CycScheme.hGl ⊤ ρ (CycScheme.cur P (ρ, false)) = ⊤ := by
  unfold CycScheme.hGl
  rw [ENNReal.top_sub (total_ne_top h)]
  exact ENNReal.top_sub ENNReal.coe_ne_top

/-- The invariant of the states along the scheme: unfinished states satisfy `EnvAt`, finished ones
are an `EnvRec`-shaped record (full earlier world-lines and an initial piece of walk `k`). -/
def Inv (P : CycPlan I d β) (sc : ℝ≥0∞) (ν : Measure (I × RingSpace d β))
    (st : CycScheme.State I d) : Prop :=
  (st.2 = false ∧ ∃ (k : ℕ) (r : ℝ≥0), EnvAt P ν k r st.1) ∨
  (st.2 = true ∧ ∃ (k : ℕ) (r : ℝ≥0), st.1 = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k)
      (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞))⟩ ∧ P.AllFin (rule P ν) k ∧ (k : ℕ∞) < P.K ∧
      (r : ℝ≥0∞) ≤ sInf (cand P ν k) ∧
      (sc = ⊤ → (r : ℝ≥0∞) = sInf (cand P ν k) ∧ ¬ ((k + 1 : ℕ) : ℕ∞) < P.K))

omit [Countable I] in
omit [MeasurableSingletonClass I] in
theorem inv_init (hν : CycGood ν) (hK : 0 < P.K) : Inv P sc ν (CycScheme.init P) :=
  Or.inl ⟨rfl, 0, 0, envAt_init hν hK⟩

theorem inv_upd (hν : CycGood ν) {st : CycScheme.State I d} (o : Outcome (CycS I d β))
    (hI : Inv P sc ν st)
    (hg : st.2 = false → StepGood P sc ν st.1 o) : Inv P sc ν (CycScheme.upd P sc st o) := by
  rcases hI with ⟨hst, k, r, h⟩ | ⟨hst, rest⟩
  · obtain ⟨ρ, b⟩ := st
    simp only at hst h
    subst hst
    have hg' := hg rfl
    simp only at hg'
    by_cases hs : CycScheme.stops P sc (ρ, false) o
    · by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
      · obtain ⟨h1, h2⟩ := upd_stop_next hν h hg' hs hK
        exact Or.inl ⟨h1, k + 1, 0, h2⟩
      · rw [upd_stop_end hν h hg' hs hK]
        refine Or.inr ⟨rfl, k, r + CycScheme.sStar P sc (ρ, false) o, ?_, h.allFin, h.lt_K,
          (sInf_cand_eq hν h hg' hs).ge, fun _ => ⟨(sInf_cand_eq hν h hg' hs).symm, hK⟩⟩
        show (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k)⟩ : CycRec I d) = _
        rw [E_eq_of_stops hν h hg' hs]
    · obtain ⟨h1, h2⟩ := upd_notStop hν h hg' hs
      by_cases hf : (CycScheme.upd P sc (ρ, false) o).2 = true
      · refine Or.inr ⟨hf, k, _, h1.rec_eq, h1.allFin, h1.lt_K, h1.le_sInf, fun hsc => ?_⟩
        exfalso
        rw [h2] at hf
        have hd := of_decide_eq_true hf
        rw [hsc, hGl_top h] at hd
        exact ENNReal.coe_ne_top hd
      · exact Or.inl ⟨by simpa using hf, k, _, h1⟩
  · have : CycScheme.upd P sc st o = st := by
      unfold CycScheme.upd
      rw [ite_eq_left hst]
    rw [this]
    exact Or.inr ⟨hst, rest⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem E_cut_eq (k : ℕ) {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ sInf (cand P ν k)) :
    (P.E (rule P ν) k).cut (r : ℝ≥0∞) = (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) := by
  rw [E_eq]
  refine Prod.ext rfl (Subtype.ext ?_)
  exact CPath.cut_cut _ hr

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem Inv.rec_form {st : CycScheme.State I d} (hI : Inv P sc ν st) :
    ∃ (k : ℕ) (r : ℝ≥0), st.1 = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k)
        (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞))⟩ ∧ P.AllFin (rule P ν) k ∧ (k : ℕ∞) < P.K ∧
      (r : ℝ≥0∞) ≤ sInf (cand P ν k) := by
  rcases hI with ⟨-, k, r, h⟩ | ⟨-, k, r, hr⟩
  · exact ⟨k, r, h.rec_eq, h.allFin, h.lt_K, h.le_sInf⟩
  · exact ⟨k, r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem entries_of_rec_form {ρ : CycRec I d} {k : ℕ} {r : ℝ≥0}
    (hρ : ρ = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k)
      (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞))⟩) :
    ∀ e, ρ.IsEntry e → ∃ ℓ : ℝ≥0∞, e = (e.1, (envPath ν e.1).cut ℓ) := by
  rintro e ⟨j, hj⟩
  rw [hρ] at hj
  simp only [CycRec.nth] at hj
  split_ifs at hj with hjk
  · have hj' := Option.some.inj hj
    subst hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hlt | heq
    · have : (⟨j, hjk⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
      rw [this]
      simp only [CycRec.snoc, Fin.snoc_castSucc]
      rw [P.ideal_apply]
      exact ⟨_, rfl⟩
    · have : (⟨j, hjk⟩ : Fin (k + 1)) = Fin.last k := Fin.ext heq
      rw [this]
      simp only [CycRec.snoc, Fin.snoc_last]
      exact ⟨_, rfl⟩

variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

theorem stateAt_H_succ (run : ExplRun (cycScheme P sc U) Pr) (j : ℕ) (ω : Ω) :
    CycScheme.stateAt P sc (j + 1) (run.H (j + 1) ω) =
      CycScheme.upd P sc (CycScheme.stateAt P sc j (run.H j ω)) (run.H (j + 1) ω).last := by
  show CycScheme.upd P sc (CycScheme.stateAt P sc j (run.H (j + 1) ω).init) _ = _
  rw [show (run.H (j + 1) ω).init = run.H j ω from (cycScheme P sc U).Hfun_init j _]

/-- The environment scheme (b), the induction: almost surely `N` is good and, for every `j`,
the state `(ρ_j(H_j), ε_j(H_j))` satisfies the invariant `Inv`: it consists of the first `k` full
environment world-lines and an initial piece of the environment world-line of walk `k`. -/
theorem ae_inv (run : ExplRun (cycScheme P sc U) Pr) (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, CycGood (run.N ω) ∧
      ∀ j : ℕ, Inv P sc (run.N ω) (CycScheme.stateAt P sc j (run.H j ω)) := by
  filter_upwards [ae_cycGood' run.isPPP, ae_stepGood run] with ω hgood hstep
  refine ⟨hgood, fun j => ?_⟩
  induction j with
  | zero => exact inv_init hgood hK
  | succ j ih =>
    rw [stateAt_H_succ]
    exact inv_upd hgood _ ih fun hst => hstep j hst

/-- The environment scheme (b): almost surely, for every `j`, the record `ρ_j(H_j)` consists
of the first `k` environment world-lines in full and the initial piece, at its current time
`r_j ≤ ℓ_k`, of the environment world-line `E k` of walk `k`; and `N|_{𝒵_j} = cycRM(ρ_j(H_j))`. -/
theorem ae_initial_pieces (run : ExplRun (cycScheme P sc U) Pr) (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, ∀ j : ℕ, ∃ (k : ℕ) (r : ℝ≥0), (r : ℝ≥0∞) ≤ (P.E (rule P (run.N ω)) k).len ∧
      (CycScheme.stateAt P sc j (run.H j ω)).1 = Sum.inl ⟨k + 1,
        CycRec.snoc (P.ideal (rule P (run.N ω)) k) ((P.E (rule P (run.N ω)) k).cut (r : ℝ≥0∞))⟩ ∧
      P.AllFin (rule P (run.N ω)) k ∧ (k : ℕ∞) < P.K ∧
      (run.N ω).restrict ((cycScheme P sc U).Z j (run.H j ω)) =
        (CycScheme.stateAt P sc j (run.H j ω)).1.rm β := by
  filter_upwards [ae_inv run hK] with ω ⟨hgood, hinv⟩ j
  obtain ⟨k, r, hrec, hall, hlt, hle⟩ := (hinv j).rec_form
  refine ⟨k, r, ?_, ?_, hall, hlt, ?_⟩
  · show (r : ℝ≥0∞) ≤ ((pth P (run.N ω) k).1.cut (sInf (cand P (run.N ω) k))).len
    rw [CPath.cut_len]; exact hle
  · rw [hrec, E_cut_eq k hle]
  · rw [CycScheme.Z_eq_region P sc (cycScheme P sc U) (fun _ _ => rfl) (fun _ _ => rfl) j]
    exact restrict_region_eq_rm hgood (entries_of_rec_form hrec)

end CycSchemeEnv
end ElboimSly.Cyclic

end
