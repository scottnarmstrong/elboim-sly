/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiFixed
public import ElboimSly.Foundations.Cyclic.CycMultiDyadic
public import ElboimSly.Foundations.Cyclic.CycMultiAtoms
public import ElboimSly.Foundations.PPP.Exploration.CountF
public import ElboimSly.Foundations.PPP.Exploration.Section
public import Mathlib

/-!
# Several walks explored one after another (a), Step 3: finite stopping times

Several walks explored one after another (a), Step 3. For an everywhere finite `(ℱ^𝒫_s)`-stopping time
`T`, `Ñ_T = N|_{S ∖ R_T} + N'|_{R_T}` has the law of `N` and is independent of `ℱ^𝒫_T`
(`multi_stopped_fin`). This is `multi_fixed_time` (Step 1) combined with the dyadic approximation
`dyadic_indep`, the right-continuity `CycRec.mem_region_trunc_of_forall_gt` of the regions and the
counting structure of `N`, `N'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}

/-- `Ñ_t` built from the truncated versions `τ ∘ N`, `τ ∘ N'` (equal to `N`, `N'` almost surely),
which makes it measurable. -/
noncomputable def multiM (t : ℝ≥0) (ω : Ω) : Measure (CycS I d β) :=
  tildeMeasure (fun ω => tau (cycIntensity I d β) (N ω))
    (fun ω => tau (cycIntensity I d β) (N' ω)) (cycRegionAt P N t) ω

theorem multiM_ae_eq (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr) :
    ∀ᵐ ω ∂Pr, ∀ t, multiM P (N := N) (N' := N') t ω =
      tildeMeasure N N' (cycRegionAt P N t) ω := by
  filter_upwards [hN.tau_comp_ae_eq, hN'.tau_comp_ae_eq] with ω h1 h2 t
  unfold multiM tildeMeasure
  beta_reduce
  rw [h1, h2]

omit mΩ in
theorem measurableSet_cycRegionAt (junk : CycEntry I d) (t : ℝ≥0) (ω : Ω)
    (N : Ω → Measure (CycS I d β)) :
    MeasurableSet (cycRegionAt P N t ω) := by
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  have h := (measurableSet_region (I := I) (d := d) (β := β)).preimage
    (measurable_prodMk_left (x := CycRec.trunc t (P.envFinal (N ω))))
  exact h

omit mΩ in
omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem cycRegionAt_mono (junk : CycEntry I d) (ω : Ω) :
    Monotone fun t => cycRegionAt P N t ω := fun _ _ h =>
  CycRec.region_trunc_mono junk h _

omit mΩ in
omit [Countable I] [MeasurableSingletonClass I] in
theorem cycRegionAt_rc (junk : CycEntry I d) (ω : Ω) (s0 : ℝ≥0) (x : CycS I d β)
    (h : ∀ s, s0 < s → x ∈ cycRegionAt P N s ω) : x ∈ cycRegionAt P N s0 ω :=
  CycRec.mem_region_trunc_of_forall_gt junk _ s0 x h

theorem measurable_multiM (hR : Measurable fun ω => P.envFinal (N ω)) (hN : Measurable N)
    (hN' : Measurable N') {g : Ω → ℝ≥0} (hg : Measurable g) :
    Measurable fun ω => multiM P (N := N) (N' := N') (g ω) ω := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  have hZ : MeasurableSet {p : Ω × CycS I d β | p.2 ∈ cycRegionAt P N (g p.1) p.1} := by
    have h1 : Measurable fun p : Ω × CycS I d β =>
        (CycRec.trunc (g p.1) (P.envFinal (N p.1)), p.2) :=
      (measurable_trunc.comp ((hR.comp measurable_fst).prodMk (hg.comp measurable_fst))).prodMk
        measurable_snd
    exact (measurableSet_region (I := I) (d := d) (β := β)).preimage h1
  have h1 := measurable_tau_restrict_section (cycIntensity I d β) hZ.compl
  have h2 := measurable_tau_restrict_section (cycIntensity I d β) hZ
  exact measurable_add_measure.comp
    ((h1.comp (measurable_id.prodMk hN)).prodMk (h2.comp (measurable_id.prodMk hN')))

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] mΩ in
theorem cycRegionStop_of_fin (T : Ω → WithTop ℝ≥0) (hfin : ∀ ω, T ω ≠ ⊤) (ω : Ω) :
    cycRegionStop P N T ω = cycRegionAt P N (ElboimSly.SRW.stopReal T ω) ω := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (hfin ω)
  unfold cycRegionStop ElboimSly.SRW.stopReal
  rw [← ha]
  rw [WithTop.untopD_coe]
  rfl

theorem eventually_dyUp_le (s0 s : ℝ≥0) (hs : s0 < s) : ∀ᶠ m : ℕ in atTop, dyUp m s0 ≤ s := by
  have h0 : Tendsto (fun m : ℕ => ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
  filter_upwards [h0.eventually_lt_const (tsub_pos_of_lt hs)] with m hm
  refine (dyUp_lt m s0).le.trans ?_
  calc s0 + (1 / 2) ^ m ≤ s0 + (s - s0) := add_le_add le_rfl hm.le
    _ = s := add_tsub_cancel_of_le hs.le

section main

variable (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), Step 3, for an everywhere finite stopping time. -/
theorem multi_stopped_fin (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω))
    {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) T)
    (hfin : ∀ ω, T ω ≠ ⊤) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {F : Set (Measure (CycS I d β))} (hF : MeasurableSet F) :
    Pr (A ∩ {ω | tildeMeasure N N' (cycRegionStop P N T) ω ∈ F}) = Pr A * (Pr.map N) F := by
  have := hN.isProbabilityMeasure
  have hae := multiM_ae_eq P hN hN'
  have hstep : ∀ t, ∀ A, MeasurableSet[multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR t] A →
      ∀ F : Set (Measure (CycS I d β)), MeasurableSet F →
      Pr (A ∩ {ω | multiM P (N := N) (N' := N') t ω ∈ F}) = Pr A * (Pr.map N) F := by
    intro t A hA F hF
    rw [← multi_fixed_time P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hR t hA hF]
    refine measure_congr (EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
    filter_upwards [hae] with ω hω
    apply propext
    rw [hω t]
  have hMmeas : ∀ g : Ω → ℝ≥0, Measurable g →
      Measurable fun ω => multiM P (N := N) (N' := N') (g ω) ω := fun g hg =>
    measurable_multiM P hR hN.measurable hN'.measurable hg
  have hPi : (Pr.map N) univ = 1 := by
    rw [Measure.map_apply hN.measurable MeasurableSet.univ]; simp
  have hlim : ∀ F ∈ countEventsFin (cycIntensity I d β), ∀ᵐ ω ∂Pr, ∀ᶠ m in atTop,
      (multiM P (N := N) (N' := N') (dyUp m (ElboimSly.SRW.stopReal T ω)) ω ∈ F ↔
        multiM P (N := N) (N' := N') (ElboimSly.SRW.stopReal T ω) ω ∈ F) := by
    intro F hF
    obtain ⟨l, B, C, hB, hBfin, hC, rfl⟩ := hF
    have hcount : ∀ᵐ ω ∂Pr, ∀ i : Fin l, N ω (B i) ≠ ⊤ ∧ N' ω (B i) ≠ ⊤ := by
      refine ae_all_iff.2 fun i => ?_
      filter_upwards [hN.ae_natCast_count (hB i) (hBfin i),
        hN'.ae_natCast_count (hB i) (hBfin i)] with ω ⟨n, hn⟩ ⟨n', hn'⟩
      rw [hn, hn']
      exact ⟨ENNReal.natCast_ne_top n, ENNReal.natCast_ne_top n'⟩
    filter_upwards [hae, hcount, ae_cyc_count hN, ae_cyc_count hN'] with ω hω hfa ⟨a, ha⟩ ⟨a', ha'⟩
    set s0 := ElboimSly.SRW.stopReal T ω with hs0
    have hev : ∀ i : Fin l, ∀ᶠ m in atTop,
        (multiM P (N := N) (N' := N') (dyUp m s0) ω) (B i) =
          (multiM P (N := N) (N' := N') s0 ω) (B i) := fun i => by
      have := eventually_tilde_apply (fun s => cycRegionAt P N s ω)
        (fun s => measurableSet_cycRegionAt P P.junk s ω N) (cycRegionAt_mono P P.junk ω)
        (cycRegionAt_rc P P.junk ω) (N ω) (N' ω) a a' ha ha' (hB i) (hfa i).1 (hfa i).2 s0
        (fun m => dyUp m s0) (fun m => le_dyUp m s0) (fun s hs => eventually_dyUp_le s0 s hs)
      simpa only [hω, tildeMeasure] using this
    filter_upwards [Filter.eventually_all.2 hev] with m hm
    rw [show (fun i => (multiM P (N := N) (N' := N') (dyUp m s0) ω) (B i)) =
      fun i => (multiM P (N := N) (N' := N') s0 ω) (B i) from funext hm]
  have key := dyadic_indep (f := multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) Pr
    (multiM P (N := N) (N' := N')) (Pr.map N) hPi hMmeas hstep (countEventsFin (cycIntensity I d β))
    generateFrom_countEventsFin.symm isPiSystem_countEventsFin hT hfin hlim hA hF
  rw [← key]
  refine measure_congr (EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
  filter_upwards [hae] with ω hω
  apply propext
  rw [hω]
  unfold tildeMeasure
  rw [cycRegionStop_of_fin P T hfin]

end main

end ElboimSly.Cyclic

end
