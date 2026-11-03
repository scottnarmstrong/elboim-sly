/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmInfLaw3
import Mathlib

/-!
# Sequential first-point exploration: stopping indices

Sequential first-point exploration (g). A `𝒢`-stopping index is `κ : Ω → ℕ ∪ {∞}` with
`{κ = k} ∈ 𝒢_k = σ(H_k)` for `k ∈ ℕ`. Its `σ`-algebra is
`𝒢_κ = {G | G ∩ {κ = k} ∈ 𝒢_k for k ∈ ℕ ∪ {∞}}`. Then `Ñ_κ` is a `PPP(μ)` independent of `𝒢_κ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (run : ExplRun sch P)

namespace ExplRun

include run

/-- `κ` is a `𝒢`-stopping index: `{κ = k} ∈ 𝒢_k = σ(H_k)`. -/
def IsStopping (κ : Ω → ℕ∞) : Prop :=
  ∀ k : ℕ, ∃ A : Set (Hist U S k), MeasurableSet A ∧ {ω | κ ω = k} = run.H k ⁻¹' A

/-- `G ∈ 𝒢_κ`: `G ∩ {κ = k} ∈ 𝒢_k` for `k ∈ ℕ ∪ {∞}`. -/
def InGkappa (κ : Ω → ℕ∞) (G : Set Ω) : Prop :=
  (∀ k : ℕ, ∃ A : Set (Hist U S k), MeasurableSet A ∧ G ∩ {ω | κ ω = k} = run.H k ⁻¹' A) ∧
    ∃ A : Set (U × (ℕ → Outcome S)), MeasurableSet A ∧ G ∩ {ω | κ ω = ⊤} = run.Hinf ⁻¹' A

/-- `Ñ_κ = Ñ_k` on `{κ = k}`, `k ∈ ℕ ∪ {∞}`. -/
noncomputable def NtilKappa (κ : Ω → ℕ∞) (ω : Ω) : Measure S :=
  (κ ω).recTopCoe (run.NtilInf ω) (fun k => run.Ntil k ω)

theorem NtilKappa_coe {κ : Ω → ℕ∞} {k : ℕ} {ω : Ω} (h : κ ω = k) :
    run.NtilKappa κ ω = run.Ntil k ω := by
  simp [NtilKappa, h]

theorem NtilKappa_top {κ : Ω → ℕ∞} {ω : Ω} (h : κ ω = ⊤) :
    run.NtilKappa κ ω = run.NtilInf ω := by
  simp [NtilKappa, h]

theorem prob_rect_Ntil (k : ℕ) {A : Set (Hist U S k)} (hA : MeasurableSet A) {F : Set (Measure S)}
    (hF : MeasurableSet F) :
    P (run.H k ⁻¹' A ∩ run.Ntil k ⁻¹' F) = P (run.H k ⁻¹' A) * (P.map run.N) F := by
  have := run.prob
  have hmA : Measurable fun ω => A.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) :=
    (measurable_one.indicator hA).comp (run.measurable_H k)
  have h := run.resample (k := k)
    (F := fun q => A.indicator (1 : Hist U S k → ℝ≥0∞) q.1 *
      F.indicator (1 : Measure S → ℝ≥0∞) q.2)
    (((measurable_one.indicator hA).comp measurable_fst).mul
      ((measurable_one.indicator hF).comp measurable_snd))
  have e2 : ∀ ω, ∫⁻ ν, A.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) *
      F.indicator (1 : Measure S → ℝ≥0∞) ν ∂(P.map run.N) =
      A.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) * (P.map run.N) F := by
    intro ω
    rw [lintegral_const_mul _ (measurable_one.indicator hF), lintegral_indicator_one hF]
  simp_rw [e2] at h
  rw [lintegral_mul_const _ hmA] at h
  classical
  have hl : P (run.H k ⁻¹' A ∩ run.Ntil k ⁻¹' F) = ∫⁻ ω,
      A.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) *
        F.indicator (1 : Measure S → ℝ≥0∞) (run.Ntil k ω) ∂P := by
    rw [← lintegral_indicator_one ((run.measurable_H k hA).inter (run.measurable_Ntil k hF))]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : run.H k ω ∈ A <;> by_cases h2 : run.Ntil k ω ∈ F <;>
      simp [Set.indicator, h1, h2]
  have hr : P (run.H k ⁻¹' A) = ∫⁻ ω, A.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) ∂P := by
    rw [← lintegral_indicator_one (run.measurable_H k hA)]
    refine lintegral_congr fun ω => ?_
    simp only [Set.indicator, Set.mem_preimage]
    rfl
  rw [hl, hr]
  exact h

/-- Sequential first-point exploration (g): `Ñ_κ` is independent of `𝒢_κ`, and has law `W`. -/
theorem stopping_indep {κ : Ω → ℕ∞} (hκ : run.IsStopping κ) {G : Set Ω}
    (hG : run.InGkappa κ G) {F : Set (Measure S)} (hF : MeasurableSet F) :
    P (G ∩ {ω | run.NtilKappa κ ω ∈ F}) = P G * (P.map run.N) F := by
  have := run.prob
  obtain ⟨hGk, Ainf, hAinf, hGinf⟩ := hG
  choose Ak hAk hAkeq using hGk
  have hκm : ∀ k : ℕ, MeasurableSet {ω | κ ω = k} := by
    intro k
    obtain ⟨A, hA, he⟩ := hκ k
    rw [he]; exact (run.measurable_H k) hA
  have hκtop : ∀ ω, κ ω = ⊤ ∨ ∃ k : ℕ, κ ω = k := fun ω => by
    induction κ ω using ENat.recTopCoe with
    | top => exact Or.inl rfl
    | coe k => exact Or.inr ⟨k, rfl⟩
  have hGm : ∀ k : ℕ, MeasurableSet (G ∩ {ω | κ ω = k}) := fun k => by
    rw [hAkeq k]; exact (run.measurable_H k) (hAk k)
  have hGtopm : MeasurableSet (G ∩ {ω | κ ω = ⊤}) := by
    rw [hGinf]; exact run.measurable_Hinf hAinf
  have hdecomp : ∀ E : Set Ω, E = (⋃ k : ℕ, E ∩ {ω | κ ω = k}) ∪ (E ∩ {ω | κ ω = ⊤}) := by
    intro E
    ext ω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hω
      rcases hκtop ω with h | ⟨k, hk⟩
      · exact Or.inr ⟨hω, h⟩
      · exact Or.inl ⟨k, hω, hk⟩
    · rintro (⟨k, hω, -⟩ | ⟨hω, -⟩) <;> exact hω
  have hdisj : ∀ E : Set Ω, Pairwise (Function.onFun Disjoint fun k : ℕ => E ∩ {ω | κ ω = k}) := by
    intro E i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, hi⟩ ⟨-, hj⟩
    have : ((i : ℕ∞)) = j := hi.symm.trans hj
    exact hij (by exact_mod_cast this)
  have hdisj' : ∀ E : Set Ω, Disjoint (⋃ k : ℕ, E ∩ {ω | κ ω = k}) (E ∩ {ω | κ ω = ⊤}) := by
    intro E
    rw [Set.disjoint_left]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rintro ω ⟨k, -, hk⟩ ⟨-, ht⟩
    rw [hk] at ht
    exact absurd ht (by simp)
  -- the finite part
  have hfin : ∀ k : ℕ, P (G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = k}) =
      P (G ∩ {ω | κ ω = k}) * (P.map run.N) F := by
    intro k
    have e : G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = k} =
        (run.H k ⁻¹' Ak k) ∩ (run.Ntil k ⁻¹' F) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      have hω := Set.ext_iff.1 (hAkeq k) ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hω
      constructor
      · rintro ⟨⟨hg, hm⟩, hk⟩
        exact ⟨hω.1 ⟨hg, hk⟩, by rwa [run.NtilKappa_coe hk] at hm⟩
      · rintro ⟨ha, hm⟩
        have := hω.2 ha
        exact ⟨⟨this.1, by rwa [run.NtilKappa_coe this.2]⟩, this.2⟩
    rw [e, hAkeq k]
    exact run.prob_rect_Ntil k (hAk k) hF
  -- the point at infinity
  have hmeasI : Measurable fun ω => (run.Hinf ω, run.NtilInf ω) :=
    run.measurable_Hinf.prodMk run.measurable_NtilInf
  have htop : P (G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = ⊤}) =
      P (G ∩ {ω | κ ω = ⊤}) * (P.map run.N) F := by
    have e : G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = ⊤} =
        (run.Hinf ⁻¹' Ainf) ∩ (run.NtilInf ⁻¹' F) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      have hω := Set.ext_iff.1 hGinf ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hω
      constructor
      · rintro ⟨⟨hg, hm⟩, hk⟩
        exact ⟨hω.1 ⟨hg, hk⟩, by rwa [run.NtilKappa_top hk] at hm⟩
      · rintro ⟨ha, hm⟩
        have := hω.2 ha
        exact ⟨⟨this.1, by rwa [run.NtilKappa_top this.2]⟩, this.2⟩
    rw [e, hGinf]
    have := congrArg (fun m => m (Ainf ×ˢ F)) run.resample_inf
    rw [Measure.map_apply hmeasI (hAinf.prod hF), Measure.prod_prod,
      Measure.map_apply run.measurable_Hinf hAinf] at this
    exact this
  -- assembling
  have hEpieces : ∀ k : ℕ, MeasurableSet (G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = k}) := by
    intro k
    have e : G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = k} =
        (run.H k ⁻¹' Ak k) ∩ (run.Ntil k ⁻¹' F) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      have hω := Set.ext_iff.1 (hAkeq k) ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hω
      constructor
      · rintro ⟨⟨hg, hm⟩, hk⟩
        exact ⟨hω.1 ⟨hg, hk⟩, by rwa [run.NtilKappa_coe hk] at hm⟩
      · rintro ⟨ha, hm⟩
        have := hω.2 ha
        exact ⟨⟨this.1, by rwa [run.NtilKappa_coe this.2]⟩, this.2⟩
    rw [e]
    exact ((run.measurable_H k) (hAk k)).inter ((run.measurable_Ntil k) hF)
  have hEtop : MeasurableSet (G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = ⊤}) := by
    have e : G ∩ {ω | run.NtilKappa κ ω ∈ F} ∩ {ω | κ ω = ⊤} =
        (run.Hinf ⁻¹' Ainf) ∩ (run.NtilInf ⁻¹' F) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      have hω := Set.ext_iff.1 hGinf ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hω
      constructor
      · rintro ⟨⟨hg, hm⟩, hk⟩
        exact ⟨hω.1 ⟨hg, hk⟩, by rwa [run.NtilKappa_top hk] at hm⟩
      · rintro ⟨ha, hm⟩
        have := hω.2 ha
        exact ⟨⟨this.1, by rwa [run.NtilKappa_top this.2]⟩, this.2⟩
    rw [e]
    exact (run.measurable_Hinf hAinf).inter (run.measurable_NtilInf hF)
  have step : ∀ E : Set Ω, (∀ k : ℕ, MeasurableSet (E ∩ {ω | κ ω = k})) →
      MeasurableSet (E ∩ {ω | κ ω = ⊤}) →
      P E = (∑' k : ℕ, P (E ∩ {ω | κ ω = k})) + P (E ∩ {ω | κ ω = ⊤}) := by
    intro E hk ht
    conv_lhs => rw [hdecomp E]
    rw [measure_union (hdisj' E) ht, measure_iUnion (hdisj E) hk]
  rw [step _ hEpieces hEtop, step G hGm hGtopm]
  simp_rw [hfin, htop]
  rw [ENNReal.tsum_mul_right, add_mul]

omit run in
theorem ENat_top_or_coe (m : ℕ∞) : m = ⊤ ∨ ∃ k : ℕ, m = k := by
  induction m using ENat.recTopCoe with
  | top => exact Or.inl rfl
  | coe k => exact Or.inr ⟨k, rfl⟩

theorem H_eq_trunc (k : ℕ) (ω : Ω) : run.H k ω = truncHist k (run.Hinf ω) :=
  (sch.truncHist_Hinf k (run.X ω)).symm

theorem IsStopping.top {κ : Ω → ℕ∞} (hκ : run.IsStopping κ) :
    ∃ A : Set (U × (ℕ → Outcome S)), MeasurableSet A ∧ {ω | κ ω = ⊤} = run.Hinf ⁻¹' A := by
  choose Ak hAk hAkeq using hκ
  refine ⟨(⋃ k, truncHist k ⁻¹' Ak k)ᶜ, (MeasurableSet.iUnion fun k =>
    (measurable_truncHist k) (hAk k)).compl, ?_⟩
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  have hk : ∀ k : ℕ, κ ω = k ↔ truncHist k (run.Hinf ω) ∈ Ak k := by
    intro k
    have := Set.ext_iff.1 (hAkeq k) ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at this
    rw [this, run.H_eq_trunc]
  constructor
  · intro h k hmem
    have := (hk k).2 hmem
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    rcases ENat_top_or_coe (κ ω) with h' | ⟨k, hk'⟩
    · exact h'
    · exact absurd ((hk k).1 hk') (h k)

theorem measurable_NtilKappa {κ : Ω → ℕ∞} (hκ : run.IsStopping κ) : Measurable (run.NtilKappa κ) := by
  obtain ⟨Ainf, hAinf, hAeq⟩ := hκ.top
  choose Ak hAk hAkeq using hκ
  intro B hB
  have hdec : run.NtilKappa κ ⁻¹' B = (⋃ k : ℕ, (run.H k ⁻¹' Ak k) ∩ (run.Ntil k ⁻¹' B)) ∪
      ((run.Hinf ⁻¹' Ainf) ∩ (run.NtilInf ⁻¹' B)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
    have h1 : ∀ k : ℕ, κ ω = k ↔ run.H k ω ∈ Ak k := by
      intro k
      have := Set.ext_iff.1 (hAkeq k) ω
      simpa using this
    have h2 : κ ω = ⊤ ↔ run.Hinf ω ∈ Ainf := by
      have := Set.ext_iff.1 hAeq ω
      simpa using this
    induction hκω : κ ω using ENat.recTopCoe with
    | top =>
      rw [run.NtilKappa_top hκω]
      constructor
      · intro h; exact Or.inr ⟨h2.1 hκω, h⟩
      · rintro (⟨k, hk, -⟩ | ⟨-, h⟩)
        · exact absurd ((h1 k).2 hk) (by rw [hκω]; simp)
        · exact h
    | coe k =>
      rw [run.NtilKappa_coe hκω]
      constructor
      · intro h; exact Or.inl ⟨k, (h1 k).1 hκω, h⟩
      · rintro (⟨j, hj, h⟩ | ⟨ha, -⟩)
        · have := (h1 j).2 hj
          rw [hκω] at this
          have : k = j := by exact_mod_cast this
          subst this
          exact h
        · exact absurd (h2.2 ha) (by rw [hκω]; simp)
  rw [hdec]
  exact (MeasurableSet.iUnion fun k => ((run.measurable_H k) (hAk k)).inter
    ((run.measurable_Ntil k) hB)).union ((run.measurable_Hinf hAinf).inter
      (run.measurable_NtilInf hB))

end ExplRun

end ElboimSly
