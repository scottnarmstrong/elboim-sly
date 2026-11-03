/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Independence tools

Independence tools.

* `iIndep_of_pi_systems`: (a), independence from `π`-systems.
* `iIndep_blocks`, `iIndepFun_blocks`: (b), independent blocks.
* `lintegral_freeze`, `measurable_lintegral_freeze`, `indepFun_of_lintegral_rect`: (e), freezing
  and its converse.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Independence tools (a): independence from `π`-systems. -/
theorem iIndep_of_pi_systems {ι : Type*} {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (π : ι → Set (Set Ω)) (hπ : ∀ i, IsPiSystem (π i))
    (hgen : ∀ i, m i = MeasurableSpace.generateFrom (π i))
    (hprod : ∀ (J : Finset ι) {f : ι → Set Ω}, (∀ i ∈ J, f i ∈ π i) →
      P (⋂ i ∈ J, f i) = ∏ i ∈ J, P (f i)) : iIndep m P :=
  iIndepSets.iIndep hm π hπ hgen ((iIndepSets_iff π P).2 fun J _ h => hprod J h)

/-- Independence tools (b): blocks of an independent family of `σ`-algebras. -/
theorem iIndep_blocks {ι κ : Type*} {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (h : iIndep m P) (J : κ → Set ι) (hJ : Pairwise (Function.onFun Disjoint J)) :
    iIndep (fun k => ⨆ j ∈ J k, m j) P := by
  classical
  refine iIndep_of_pi_systems (fun k => iSup₂_le fun j _ => hm j)
    (fun k => piiUnionInter (fun j => {s | MeasurableSet[m j] s}) (J k))
    (fun k => isPiSystem_piiUnionInter _ (fun j => @MeasurableSpace.isPiSystem_measurableSet _ (m j)) _)
    (fun k => (generateFrom_piiUnionInter_measurableSet m (J k)).symm) ?_
  intro s f hf
  choose! t htJ g hg hfeq using hf
  -- the global index and the chosen sets
  let G : ι → Set Ω := fun j =>
    if hj : ∃ k ∈ s, j ∈ t k then g (Classical.choose hj) j else Set.univ
  have hdisj : ∀ k ∈ s, ∀ k' ∈ s, ∀ j, j ∈ t k → j ∈ t k' → k = k' := by
    intro k hk k' hk' j hj hj'
    by_contra hne
    exact Set.disjoint_left.1 (hJ hne) (htJ k hk hj) (htJ k' hk' hj')
  have hG : ∀ k ∈ s, ∀ j ∈ t k, G j = g k j := by
    intro k hk j hj
    have hex : ∃ k ∈ s, j ∈ t k := ⟨k, hk, hj⟩
    simp only [G, dite_eq_left hex]
    have := Classical.choose_spec hex
    rw [hdisj _ this.1 k hk j this.2 hj]
  have hmeasG : ∀ j ∈ s.biUnion t, MeasurableSet[m j] (G j) := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.1 hj
    rw [hG k hk j hjk]
    exact hg k hk j hjk
  have hU : (⋂ k ∈ s, f k) = ⋂ j ∈ s.biUnion t, G j := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_biUnion]
    constructor
    · intro hx j ⟨k, hk, hjk⟩
      have := hx k hk
      rw [hfeq k hk] at this
      simp only [Set.mem_iInter] at this
      rw [hG k hk j hjk]
      exact this j hjk
    · intro hx k hk
      rw [hfeq k hk]
      simp only [Set.mem_iInter]
      intro j hjk
      rw [← hG k hk j hjk]
      exact hx j ⟨k, hk, hjk⟩
  rw [hU, h.meas_biInter hmeasG,
    Finset.prod_biUnion (fun k hk k' hk' hne => Finset.disjoint_left.2 fun j hj hj' =>
      hne (hdisj k hk k' hk' j hj hj'))]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [hfeq k hk, h.meas_biInter (fun j hj => hg k hk j hj)]
  exact Finset.prod_congr rfl fun j hj => by rw [hG k hk j hj]

/-- Independence tools (b), function form: functions measurable with respect to the blocks
of an independent family are independent. -/
theorem iIndepFun_blocks {ι κ : Type*} {𝓧 : ι → Type*} [∀ j, MeasurableSpace (𝓧 j)]
    {X : ∀ j, Ω → 𝓧 j} (hX : ∀ j, Measurable (X j)) (h : iIndepFun X P)
    (J : κ → Set ι) (hJ : Pairwise (Function.onFun Disjoint J))
    {𝓨 : κ → Type*} [∀ k, MeasurableSpace (𝓨 k)] {Y : ∀ k, Ω → 𝓨 k}
    (hY : ∀ k, Measurable[⨆ j ∈ J k, MeasurableSpace.comap (X j) inferInstance] (Y k)) :
    iIndepFun Y P := by
  have hb := iIndep_blocks (fun j => (hX j).comap_le) ((iIndepFun_iff_iIndep _ _ _).1 h) J hJ
  rw [iIndepFun_iff_iIndep _ _ _]
  rw [iIndep_iff] at hb ⊢
  intro s f hf
  refine hb s (f := f) fun k hk => ?_
  obtain ⟨B, hB, hBf⟩ := hf k hk
  exact hBf ▸ hY k hB

/-! ### Freezing -/

variable {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-- Independence tools (e): measurability of the partial integral. -/
theorem measurable_lintegral_freeze (ν : Measure 𝒴) [SFinite ν] {F : 𝒳 × 𝒴 → ℝ≥0∞}
    (hF : Measurable F) : Measurable fun x => ∫⁻ y, F (x, y) ∂ν :=
  hF.lintegral_prod_right'

/-- Independence tools (e): freezing. -/
theorem lintegral_freeze [IsProbabilityMeasure P] {X : Ω → 𝒳} {Y : Ω → 𝒴} (hX : Measurable X)
    (hY : Measurable Y) (hi : IndepFun X Y P) [SFinite (P.map Y)] {F : 𝒳 × 𝒴 → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (X ω, Y ω) ∂P = ∫⁻ x, ∫⁻ y, F (x, y) ∂(P.map Y) ∂(P.map X) := by
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hi
  calc ∫⁻ ω, F (X ω, Y ω) ∂P = ∫⁻ z, F z ∂(P.map fun ω => (X ω, Y ω)) :=
        (lintegral_map hF (hX.prodMk hY)).symm
    _ = _ := by rw [hp, lintegral_prod _ hF.aemeasurable]

/-- Independence tools (e), converse: the freezing identity for measurable rectangles
implies independence. -/
theorem indepFun_of_lintegral_rect [IsProbabilityMeasure P] {X : Ω → 𝒳} {Y : Ω → 𝒴}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (G : Set 𝒳) (G' : Set 𝒴), MeasurableSet G → MeasurableSet G' →
      ∫⁻ ω, (G ×ˢ G').indicator 1 (X ω, Y ω) ∂P =
        ∫⁻ x, ∫⁻ y, (G ×ˢ G').indicator 1 (x, y) ∂(P.map Y) ∂(P.map X)) :
    IndepFun X Y P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro G G' hG hG'
  have h1 := h G G' hG hG'
  have e1 : ∫⁻ ω, (G ×ˢ G').indicator 1 (X ω, Y ω) ∂P = P (X ⁻¹' G ∩ Y ⁻¹' G') := by
    rw [← lintegral_indicator_one ((hX hG).inter (hY hG'))]
    refine lintegral_congr fun ω => ?_
    by_cases a : X ω ∈ G <;> by_cases b : Y ω ∈ G' <;> simp [Set.indicator, a, b]
  have e2 : ∫⁻ x, ∫⁻ y, (G ×ˢ G').indicator 1 (x, y) ∂(P.map Y) ∂(P.map X) =
      P (X ⁻¹' G) * P (Y ⁻¹' G') := by
    have : ∀ x, ∫⁻ y, (G ×ˢ G').indicator 1 (x, y) ∂(P.map Y) =
        G.indicator (fun _ => P.map Y G') x := by
      intro x
      by_cases a : x ∈ G
      · have : (fun y => (G ×ˢ G').indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (x, y)) = G'.indicator 1 := by
          funext y
          by_cases b : y ∈ G'
          · rw [Set.indicator_of_mem (show (x, y) ∈ G ×ˢ G' from ⟨a, b⟩),
              Set.indicator_of_mem b]
            rfl
          · rw [Set.indicator_of_notMem (show (x, y) ∉ G ×ˢ G' from fun h => b h.2),
              Set.indicator_of_notMem b]
        rw [this, lintegral_indicator_one hG']
        simp [a]
      · simp [Set.indicator, a]
    simp_rw [this]
    rw [lintegral_indicator_const hG, Measure.map_apply hX hG, Measure.map_apply hY hG', mul_comm]
  rw [e1, e2] at h1
  exact h1

end ElboimSly
