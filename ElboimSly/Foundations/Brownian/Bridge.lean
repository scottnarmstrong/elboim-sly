/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Existence
import Mathlib

/-!
# Brownian interpolation of a Gaussian walk

Brownian interpolation of a Gaussian walk (and existence, which is
`exists_standardBrownianMotion` in `Existence.lean`).

Let `(X_m)_{m ∈ ℕ}` be independent `N_d(0, I)` vectors, `(η_α)` independent `N(0,1)` variables
indexed by the bridge index set `Idx_d^br = {α ∈ Idx d : α.2.2 ≠ none}`, and the families `X` and `η`
independent. With `ξ_{(i,m,∗)} = (X_m)_i` and `ξ_α = η_α` otherwise, the process `LC[ξ]` is a
standard `d`-dimensional Brownian motion with `B(j) = ∑_{m<j} X_m` for all `j ∈ ℕ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The bridge index set `Idx_d^br`: the indices of `Idx d` that are not of the form `(i,m,∗)`. -/
abbrev BridgeIdx (d : ℕ) : Type := {α : Idx d // α.2.2 ≠ none}

/-- Brownian interpolation of a Gaussian walk. `ξ_{(i,m,∗)} = (X_m)_i` and `ξ_α = η_α` for bridge
indices. -/
def interpXi (X : ℕ → Ω → (Fin d → ℝ)) (η : BridgeIdx d → Ω → ℝ) (α : Idx d) (ω : Ω) : ℝ :=
  if h : α.2.2 = none then X α.2.1 ω α.1 else η ⟨α, h⟩ ω

section

variable [IsProbabilityMeasure P] {X : ℕ → Ω → (Fin d → ℝ)} {η : BridgeIdx d → Ω → ℝ}

lemma measurable_interpXi (hXm : ∀ m, Measurable (X m)) (hηm : ∀ β, Measurable (η β))
    (α : Idx d) : Measurable (interpXi X η α) := by
  unfold interpXi
  split_ifs with h
  · exact (measurable_pi_apply _).comp (hXm _)
  · exact hηm _

/-- The coordinates `(m,i) ↦ (X_m)_i` of independent `N_d(0,I)` vectors are independent
`N(0,1)`. -/
lemma iIndepFun_coords (hXm : ∀ m, Measurable (X m)) (hXind : iIndepFun X P)
    (hXlaw : ∀ m, HasLaw (X m) (Measure.pi fun _ : Fin d => gaussianReal 0 1) P) :
    iIndepFun (fun (p : ℕ × Fin d) ω => X p.1 ω p.2) P ∧
      ∀ p : ℕ × Fin d, HasLaw (fun ω => X p.1 ω p.2) (gaussianReal 0 1) P := by
  have hXmap := hXind.map_fun_eq_infinitePi_map hXm
  have hmapm : ∀ m, P.map (X m) = Measure.pi fun _ : Fin d => gaussianReal 0 1 :=
    fun m => (hXlaw m).map_eq
  simp_rw [hmapm] at hXmap
  let Yp : Ω → ℕ × Fin d → ℝ := fun ω p => X p.1 ω p.2
  have hYm : Measurable Yp := measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp (hXm _)
  have hcurry : (fun ω m => X m ω) = (MeasurableEquiv.curry ℕ (Fin d) ℝ) ∘ Yp := rfl
  have hlaw : P.map Yp = Measure.infinitePi fun _ : ℕ × Fin d => gaussianReal 0 1 := by
    have h1 : (P.map Yp).map (MeasurableEquiv.curry ℕ (Fin d) ℝ) =
        (Measure.infinitePi fun _ : ℕ × Fin d => gaussianReal 0 1).map
          (MeasurableEquiv.curry ℕ (Fin d) ℝ) := by
      rw [Measure.map_map (MeasurableEquiv.curry ℕ (Fin d) ℝ).measurable hYm, ← hcurry, hXmap,
        Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin d) => gaussianReal 0 1)]
      congr 1
      funext m
      rw [Measure.infinitePi_eq_pi]
    exact (MeasurableEquiv.map_measurableEquiv_injective _) h1
  have hlawp : ∀ p : ℕ × Fin d, HasLaw (fun ω => X p.1 ω p.2) (gaussianReal 0 1) P := fun p => by
    refine ⟨((measurable_pi_apply _).comp (hXm _)).aemeasurable, ?_⟩
    have : (fun ω => X p.1 ω p.2) = (fun y : ℕ × Fin d → ℝ => y p) ∘ Yp := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply p) hYm, hlaw, Measure.infinitePi_map_eval]
  refine ⟨?_, hlawp⟩
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun (p : ℕ × Fin d) ω => X p.1 ω p.2)
    (fun p => (measurable_pi_apply _).comp (hXm _))).2 ?_
  have : (fun p : ℕ × Fin d => P.map fun ω => X p.1 ω p.2) = fun _ => gaussianReal 0 1 := by
    funext p; exact (hlawp p).map_eq
  rw [this]
  exact hlaw

/-- Brownian interpolation of a Gaussian walk, the proof. The family `ξ` is independent with laws
`N(0,1)`. -/
theorem iIndepFun_interpXi (hXm : ∀ m, Measurable (X m)) (hηm : ∀ β, Measurable (η β))
    (hXind : iIndepFun X P)
    (hXlaw : ∀ m, HasLaw (X m) (Measure.pi fun _ : Fin d => gaussianReal 0 1) P)
    (hηind : iIndepFun η P) (hηlaw : ∀ β, HasLaw (η β) (gaussianReal 0 1) P)
    (hXη : IndepFun (fun ω m => X m ω) (fun ω β => η β ω) P) :
    iIndepFun (interpXi X η) P ∧ ∀ α, HasLaw (interpXi X η α) (gaussianReal 0 1) P := by
  classical
  obtain ⟨hYind, hYlaw⟩ := iIndepFun_coords hXm hXind hXlaw
  have hξlaw : ∀ α, HasLaw (interpXi X η α) (gaussianReal 0 1) P := by
    intro α
    unfold interpXi
    split_ifs with h
    · exact hYlaw (α.2.1, α.1)
    · exact hηlaw _
  refine ⟨?_, hξlaw⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let Yp : Ω → ℕ × Fin d → ℝ := fun ω p => X p.1 ω p.2
  let ηp : Ω → BridgeIdx d → ℝ := fun ω β => η β ω
  have hYm : Measurable Yp := measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp (hXm _)
  have hηpm : Measurable ηp := measurable_pi_iff.2 hηm
  have hYη : IndepFun Yp ηp P := by
    have hg : Measurable fun (x : ℕ → Fin d → ℝ) (p : ℕ × Fin d) => x p.1 p.2 :=
      measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp (measurable_pi_apply _)
    exact hXη.comp hg measurable_id
  -- decomposition of the index set
  let S₁ : Finset (Idx d) := S.filter (fun α => α.2.2 = none)
  let S₂ : Finset (BridgeIdx d) := S.subtype (fun α => α.2.2 ≠ none)
  let φ : Idx d → ℕ × Fin d := fun α => (α.2.1, α.1)
  let T : Finset (ℕ × Fin d) := S₁.image φ
  let u : ℕ × Fin d → Set ℝ := fun p => sets (p.2, p.1, none)
  have hφinj : Set.InjOn φ (S₁ : Set (Idx d)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    obtain ⟨i, m, h⟩ := a
    obtain ⟨j, n, k⟩ := b
    simp only [φ, Prod.mk.injEq] at hab ha' hb'
    subst ha' hb'
    rw [hab.1, hab.2]
  have hu : ∀ α ∈ S₁, u (φ α) = sets α := by
    intro α hα
    have := (Finset.mem_filter.1 hα).2
    obtain ⟨i, m, h⟩ := α
    have h0 : h = none := this
    subst h0
    rfl
  -- the event splits
  have hsplit : (⋂ α ∈ S, interpXi X η α ⁻¹' sets α) =
      Yp ⁻¹' (⋂ p ∈ T, (fun y : ℕ × Fin d → ℝ => y p) ⁻¹' u p) ∩
        ηp ⁻¹' (⋂ β ∈ S₂, (fun z : BridgeIdx d → ℝ => z β) ⁻¹' sets β.1) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, T, S₂, S₁, Finset.mem_image,
      Finset.mem_filter, Finset.mem_subtype]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rintro p ⟨α, ⟨hαS, hα⟩, rfl⟩
        have := h α hαS
        unfold interpXi at this
        rw [dite_eq_left hα] at this
        obtain ⟨i, m, hh⟩ := α
        simp only at hα
        subst hα
        exact this
      · intro β hβ
        have := h β.1 hβ
        unfold interpXi at this
        rw [dite_eq_right β.2] at this
        exact this
    · rintro ⟨h1, h2⟩ α hαS
      unfold interpXi
      by_cases hα : α.2.2 = none
      · rw [dite_eq_left hα]
        have := h1 (φ α) ⟨α, ⟨hαS, hα⟩, rfl⟩
        obtain ⟨i, m, hh⟩ := α
        simp only at hα
        subst hα
        exact this
      · rw [dite_eq_right hα]
        exact h2 ⟨α, hα⟩ hαS
  have hsetsY : MeasurableSet (⋂ p ∈ T, (fun y : ℕ × Fin d → ℝ => y p) ⁻¹' u p) :=
    Finset.measurableSet_biInter _ fun p hp => measurable_pi_apply p (hsets _ (by
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hp
      have h1 := (Finset.mem_filter.1 hα)
      obtain ⟨i, m, hh⟩ := α
      have := h1.2
      simp only at this
      subst this
      exact h1.1) )
  have hsetsη : MeasurableSet (⋂ β ∈ S₂, (fun z : BridgeIdx d → ℝ => z β) ⁻¹' sets β.1) :=
    Finset.measurableSet_biInter _ fun β hβ => measurable_pi_apply β
      (hsets _ (Finset.mem_subtype.1 hβ))
  -- the two factors
  have hP1 : P (Yp ⁻¹' (⋂ p ∈ T, (fun y : ℕ × Fin d → ℝ => y p) ⁻¹' u p)) =
      ∏ α ∈ S₁, gaussianReal 0 1 (sets α) := by
    have e : Yp ⁻¹' (⋂ p ∈ T, (fun y : ℕ × Fin d → ℝ => y p) ⁻¹' u p) =
        ⋂ p ∈ T, (fun ω => X p.1 ω p.2) ⁻¹' u p := by
      ext ω; simp [Yp]
    rw [e, hYind.meas_biInter (fun p hp => ?_)]
    · rw [Finset.prod_image hφinj]
      refine Finset.prod_congr rfl fun α hα => ?_
      rw [hu α hα]
      have := (hξlaw α)
      have hα' := (Finset.mem_filter.1 hα).2
      have e2 : (fun ω => X (φ α).1 ω (φ α).2) ⁻¹' sets α = interpXi X η α ⁻¹' sets α := by
        ext ω; simp only [Set.mem_preimage]; unfold interpXi; rw [dite_eq_left hα']
      rw [e2, ← Measure.map_apply (measurable_interpXi hXm hηm α)
        (hsets α (Finset.mem_filter.1 hα).1), this.map_eq]
    · refine ⟨u p, ?_, rfl⟩
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hp
      have h1 := (Finset.mem_filter.1 hα)
      obtain ⟨i, m, hh⟩ := α
      have := h1.2
      simp only at this
      subst this
      exact hsets _ h1.1
  have hP2 : P (ηp ⁻¹' (⋂ β ∈ S₂, (fun z : BridgeIdx d → ℝ => z β) ⁻¹' sets β.1)) =
      ∏ β ∈ S₂, gaussianReal 0 1 (sets β.1) := by
    have e : ηp ⁻¹' (⋂ β ∈ S₂, (fun z : BridgeIdx d → ℝ => z β) ⁻¹' sets β.1) =
        ⋂ β ∈ S₂, η β ⁻¹' sets β.1 := by
      ext ω; simp [ηp]
    rw [e, hηind.meas_biInter (fun β hβ => ?_)]
    · refine Finset.prod_congr rfl fun β hβ => ?_
      rw [← Measure.map_apply (hηm β) (hsets _ (Finset.mem_subtype.1 hβ)), (hηlaw β).map_eq]
    · exact ⟨sets β.1, hsets _ (Finset.mem_subtype.1 hβ), rfl⟩
  rw [hsplit, hYη.measure_inter_preimage_eq_mul _ _ hsetsY hsetsη, hP1, hP2]
  -- the right-hand side
  have hrhs : ∏ α ∈ S, P (interpXi X η α ⁻¹' sets α) = ∏ α ∈ S, gaussianReal 0 1 (sets α) := by
    refine Finset.prod_congr rfl fun α hα => ?_
    rw [← Measure.map_apply (measurable_interpXi hXm hηm α) (hsets α hα), (hξlaw α).map_eq]
  rw [hrhs, ← Finset.prod_filter_mul_prod_filter_not S (fun α => α.2.2 = none)]
  congr 1
  rw [← Finset.prod_subtype_eq_prod_filter (f := fun α => gaussianReal 0 1 (sets α))
    (p := fun α => ¬ α.2.2 = none)]

end

/-- **Brownian interpolation of a Gaussian walk.** Brownian interpolation of a Gaussian walk. Let
`(X_m)` be independent `N_d(0,I)` vectors, `(η_α)_{α ∈ Idx_d^br}` independent `N(0,1)`
variables, the two families independent. Then `LC[ξ]` is a standard `d`-dimensional Brownian
motion. -/
theorem isStandardBrownianMotion_interp [IsProbabilityMeasure P]
    {X : ℕ → Ω → (Fin d → ℝ)} {η : BridgeIdx d → Ω → ℝ}
    (hXm : ∀ m, Measurable (X m)) (hηm : ∀ β, Measurable (η β))
    (hXind : iIndepFun X P)
    (hXlaw : ∀ m, HasLaw (X m) (Measure.pi fun _ : Fin d => gaussianReal 0 1) P)
    (hηind : iIndepFun η P) (hηlaw : ∀ β, HasLaw (η β) (gaussianReal 0 1) P)
    (hXη : IndepFun (fun ω m => X m ω) (fun ω β => η β ω) P) :
    IsStandardBrownianMotion d (levyCiesielski (interpXi X η)) P := by
  obtain ⟨hind, hlaw⟩ := iIndepFun_interpXi hXm hηm hXind hXlaw hηind hηlaw hXη
  exact isStandardBrownianMotion_levyCiesielski (measurable_interpXi hXm hηm) hind hlaw

omit mΩ in
/-- Brownian interpolation of a Gaussian walk, the integer values: `B(j) = ∑_{m<j} X_m` everywhere. -/
theorem levyCiesielski_interpXi_nat (X : ℕ → Ω → (Fin d → ℝ)) (η : BridgeIdx d → Ω → ℝ)
    (j : ℕ) (ω : Ω) :
    levyCiesielski (interpXi X η) (j : ℝ≥0) ω = ∑ m ∈ Finset.range j, X m ω := by
  funext i
  rw [levyCiesielski_nat, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [interpXi]

end ElboimSly.Brownian
