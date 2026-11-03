/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiRecT
public import ElboimSly.Foundations.Cyclic.CycMultiStopT
public import Mathlib

/-!
# Several walks explored one after another (a), Step 2 (II): `cycRec^𝒫(T)` and `R_T` are `ℱ_T`-measurable

Several walks explored one after another (a), Step 2.
* `measurable_truncStop`: `ω ↦ Trunc_{T(ω)}(R ω)` is `ℱ_T`-measurable (a total function; on
  `{T = ∞}` it is `Trunc_0(R)`), for a final record `R` with `Trunc_s ∘ R` being `ℱ_s`-measurable;
* `measurableSet_regionStop`: `{(ω, x) : x ∈ R_T(ω)} ∈ ℱ_T ⊗ ℬ(𝒮)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem CycRec.surv_eventually (ρ : CycRec I d) (s : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s', s ≤ s' → s' < s + ε → ρ.surv s' = ρ.surv s := by
  obtain ⟨ε, hε, hgap⟩ := ρ.exists_cum_gap s
  refine ⟨ε, hε, fun s' hs hs' => ?_⟩
  ext k
  simp only [CycRec.surv, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hh
    push Not at hh
    exact hgap k ⟨hh, lt_of_le_of_lt h2 (by exact_mod_cast hs')⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans (by exact_mod_cast hs)⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
/-- The length of each entry of `Trunc_s(ρ)` is right-continuous in `s`. -/
theorem CycRec.trunc_len_tendsto (junk : CycEntry I d) (ρ : CycRec I d) (s : ℝ≥0) (j : ℕ) :
    Tendsto (fun s' : ℝ≥0 => ((CycRec.trunc s' ρ).coord junk j).len) (𝓝[≥] s)
      (𝓝 ((CycRec.trunc s ρ).coord junk j).len) := by
  by_cases hj : j ∈ ρ.surv s
  · have hup : Tendsto (fun s' : ℝ≥0 => ((CycRec.trunc s ρ).coord junk j).len +
        ((s' - s : ℝ≥0) : ℝ≥0∞)) (𝓝[≥] s) (𝓝 ((CycRec.trunc s ρ).coord junk j).len) := by
      have h1 : Continuous fun s' : ℝ≥0 => ((s' - s : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.continuous_coe.comp (continuous_id.sub continuous_const)
      have h2 := (h1.tendsto s).mono_left (nhdsWithin_le_nhds (s := Ici s))
      simp only [tsub_self, ENNReal.coe_zero] at h2
      simpa using tendsto_const_nhds.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact (CycRec.trunc_len_bounds junk ρ (mem_Ici.1 hs') hj).1
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact (CycRec.trunc_len_bounds junk ρ (mem_Ici.1 hs') hj).2
  · obtain ⟨ε, hε, hsurv⟩ := ρ.surv_eventually s
    obtain ⟨-, -, -, -, hco⟩ := CycRec.trunc_spec junk s ρ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ico_mem_nhdsGE (lt_add_of_pos_right s hε)] with s' hs'
    obtain ⟨-, -, -, -, hco'⟩ := CycRec.trunc_spec junk s' ρ
    rw [hco j hj, hco' j (by rwa [hsurv s' hs'.1 hs'.2])]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}

omit [Countable I] [MeasurableSingletonClass I] in
/-- Several walks explored one after another (a), Step 2. If `Trunc_s ∘ R` is `ℱ_s`-measurable for
every `s`, then `Trunc_T ∘ R` is `ℱ_T`-measurable. -/
theorem measurable_truncStop (junk : CycEntry I d) (R : Ω → CycRec I d)
    (hR : ∀ s, Measurable[f s] fun ω => CycRec.trunc s (R ω)) (hT : IsStoppingTime f T) :
    Measurable[hT.measurableSpace] fun ω => CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω) := by
  have hcoord : ∀ (j : ℕ) (i : ℝ≥0), ∀ t ≤ i,
      Measurable[f i] fun ω => (CycRec.trunc t (R ω)).coord junk j := fun j i t ht =>
    (CycRec.measurable_coord junk j).comp ((hR t).mono (f.mono ht) le_rfl)
  have hnum : Measurable[hT.measurableSpace]
      fun ω => (CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).num := by
    refine measurable_stoppedValue_of_bdd (fun s ω => (CycRec.trunc s (R ω)).num) hT
      (fun i => measurable_stopped_bdd_const _ _ i (hT.measurable_stopMin i)
        (fun ω => min_le_right _ _)
        (fun t ht => CycRec.measurable_num.comp ((hR t).mono (f.mono ht) le_rfl)) ?_) ?_
    · intro ω s
      obtain ⟨ε, hε, h⟩ := CycRec.trunc_num_eventually junk (R ω) s
      exact ⟨ε, hε, h⟩
    · exact CycRec.measurable_num.comp ((hR 0))
  refine @measurable_cycRec_of_coords I _ d Ω hT.measurableSpace _ junk hnum fun j => ?_
  have hdata : Measurable[hT.measurableSpace] fun ω =>
      ((CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).coord junk j).data := by
    refine measurable_stoppedValue_of_bdd
      (fun s ω => ((CycRec.trunc s (R ω)).coord junk j).data) hT
      (fun i => measurable_stopped_bdd_const _ _ i (hT.measurable_stopMin i)
        (fun ω => min_le_right _ _)
        (fun t ht => measurable_fst.comp (hcoord j i t ht)) ?_) ?_
    · intro ω s
      obtain ⟨ε, hε, h⟩ := CycRec.trunc_coord_eventually junk (R ω) s j 0
      exact ⟨ε, hε, fun s' h1 h2 => (h s' h1 h2).1⟩
    · exact measurable_fst.comp (CycRec.measurable_coord junk j |>.comp (hR 0))
  have hfn : ∀ r : ℝ≥0, Measurable[hT.measurableSpace] fun ω =>
      ((CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).coord junk j).path.fn r := by
    intro r
    refine measurable_stoppedValue_of_bdd
      (fun s ω => ((CycRec.trunc s (R ω)).coord junk j).path.fn r) hT
      (fun i => measurable_stopped_bdd_const _ _ i (hT.measurable_stopMin i)
        (fun ω => min_le_right _ _)
        (fun t ht => (CPath.measurable_eval r).comp
          (measurable_subtype_coe.comp (measurable_snd.comp (hcoord j i t ht)))) ?_) ?_
    · intro ω s
      obtain ⟨ε, hε, h⟩ := CycRec.trunc_coord_eventually junk (R ω) s j r
      exact ⟨ε, hε, fun s' h1 h2 => (h s' h1 h2).2⟩
    · exact (CPath.measurable_eval r).comp
        (measurable_subtype_coe.comp (measurable_snd.comp
          (CycRec.measurable_coord junk j |>.comp (hR 0))))
  have hlen : Measurable[hT.measurableSpace] fun ω =>
      ((CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).coord junk j).len := by
    refine measurable_stoppedValue_of_bdd
      (fun s ω => ((CycRec.trunc s (R ω)).coord junk j).len) hT
      (fun i => measurable_stopped_bdd_tendsto _ _ i (hT.measurable_stopMin i)
        (fun ω => min_le_right _ _)
        (fun t ht => CPath.measurable_len.comp
          (measurable_subtype_coe.comp (measurable_snd.comp (hcoord j i t ht)))) ?_) ?_
    · intro ω s
      exact CycRec.trunc_len_tendsto junk (R ω) s j
    · exact CPath.measurable_len.comp
        (measurable_subtype_coe.comp (measurable_snd.comp
          (CycRec.measurable_coord junk j |>.comp (hR 0))))
  have hpath : Measurable[hT.measurableSpace] fun ω =>
      ((CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).coord junk j).2 := by
    have hc : Measurable[hT.measurableSpace] fun ω =>
        (((CycRec.trunc (ElboimSly.SRW.stopReal T ω) (R ω)).coord junk j).2.1 : CPath (Fin d → ℤ)) :=
      (@CPath.measurable_iff (Fin d → ℤ) _ Ω hT.measurableSpace _).2 ⟨hlen, hfn⟩
    exact hc.subtype_mk
  exact hdata.prodMk hpath

section region

variable {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β) (N : Ω → Measure (CycS I d β))

/-- `cycRec^𝒫(T) = Trunc_T(ρ^𝒫(N))` (a total function: on `{T = ∞}` it is `Trunc_0(ρ^𝒫(N))`). -/
noncomputable def cycRecStop (T : Ω → WithTop ℝ≥0) (ω : Ω) : CycRec I d :=
  CycRec.trunc (ElboimSly.SRW.stopReal T ω) (P.envFinal (N ω))

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- On `{T < ∞}` the region `R_T` is the region of `cycRec^𝒫(T)`. -/
theorem mem_cycRegionStop_iff (T : Ω → WithTop ℝ≥0) (ω : Ω) (x : CycS I d β) :
    x ∈ cycRegionStop P N T ω ↔ T ω ≠ ⊤ ∧ x ∈ (cycRecStop P N T ω).region β := by
  cases hh : T ω using WithTop.recTopCoe with
  | top => simp [cycRegionStop, hh]
  | coe a =>
    have e1 : ElboimSly.SRW.stopReal T ω = a := by
      unfold ElboimSly.SRW.stopReal; rw [hh]; rfl
    simp only [cycRegionStop, hh, cycRegionAt, cycRecStop, e1]
    exact ⟨fun h => ⟨WithTop.coe_ne_top, h⟩, fun h => h.2⟩

variable {P N}

omit [Fact (0 < β)] in
omit [Countable I] [MeasurableSingletonClass I] in
/-- Several walks explored one after another (a), Step 2: `cycRec^𝒫(T)` is `ℱ_T`-measurable. -/
theorem measurable_cycRecStop
    (hR : ∀ s, Measurable[f s] fun ω => CycRec.trunc s (P.envFinal (N ω)))
    (hT : IsStoppingTime f T) : Measurable[hT.measurableSpace] (cycRecStop P N T) :=
  measurable_truncStop P.junk _ hR hT

/-- Several walks explored one after another (a), Step 2:
`{(ω, x) : x ∈ R_T(ω)} ∈ ℱ_T ⊗ ℬ(𝒮)`. -/
theorem measurableSet_regionStop
    (hR : ∀ s, Measurable[f s] fun ω => CycRec.trunc s (P.envFinal (N ω)))
    (hT : IsStoppingTime f T) :
    MeasurableSet[hT.measurableSpace.prod inferInstance]
      {p : Ω × CycS I d β | p.2 ∈ cycRegionStop P N T p.1} := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  have hm := measurable_cycRecStop hR hT
  have hfst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
      (Prod.fst : Ω × CycS I d β → Ω) := @measurable_fst _ _ hT.measurableSpace _
  have hsnd : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
      (Prod.snd : Ω × CycS I d β → CycS I d β) := @measurable_snd _ _ hT.measurableSpace _
  have hg : Measurable[hT.measurableSpace.prod inferInstance]
      (fun p : Ω × CycS I d β => (cycRecStop P N T p.1, p.2)) :=
    (hm.comp hfst).prodMk hsnd
  have h1 : MeasurableSet[hT.measurableSpace.prod inferInstance]
      {p : Ω × CycS I d β | T p.1 ≠ ⊤} := hfst (measurableSet_ne_top hT)
  have h2 := hg (measurableSet_region (I := I) (d := d) (β := β))
  have : {p : Ω × CycS I d β | p.2 ∈ cycRegionStop P N T p.1} =
      {p : Ω × CycS I d β | T p.1 ≠ ⊤} ∩
        (fun p : Ω × CycS I d β => (cycRecStop P N T p.1, p.2)) ⁻¹'
          {q : CycRec I d × CycS I d β | q.2 ∈ q.1.region β} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_cycRegionStop_iff]
  rw [this]
  exact h1.inter h2

end region

end ElboimSly.Cyclic

end
