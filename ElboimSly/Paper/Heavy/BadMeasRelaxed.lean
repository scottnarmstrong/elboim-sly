/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasPath
public import ElboimSly.Paper.Heavy.BadCongr
public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import ElboimSly.Paper.Base.Progressive

/-!
# Measurability of relaxedness of a segment

Properties of discovered bad blocks (c), (d), the relaxedness clause.

`AdaptedCyclic.measurableSet_segRelaxed`: for an adapted family of cyclic paths, the event
`SegRelaxed β t'_k (W ω) k' x` is `ℱ_t`-measurable when `x + t'_k ≤ t`.  We apply
Measurability of relaxed times (`measurableSet_isRelaxedTimeWrt`) to the path clipped at time `t`,
which is jointly measurable because an adapted right-continuous process is progressive
(`Base.isStronglyProgressive_of_rc`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {W : Ω → ℝ → Fin d → ℤ}

/-- The path clipped at time `t`. -/
noncomputable def clipPath (W : Ω → ℝ → Fin d → ℤ) (t : ℝ≥0) (ω : Ω) (u : ℝ) : Fin d → ℤ :=
  W ω ((min u.toNNReal t : ℝ≥0) : ℝ)

theorem clipPath_eq (t : ℝ≥0) (ω : Ω) {u : ℝ} (h0 : 0 ≤ u) (hu : u ≤ t) :
    clipPath W t ω u = W ω u := by
  unfold clipPath
  congr 1
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hu)]
  exact Real.coe_toNNReal u h0

theorem AdaptedCyclic.measurable_clipPath (h : AdaptedCyclic f W) (t : ℝ≥0) :
    @Measurable (Ω × ℝ) (Fin d → ℤ) (@Prod.instMeasurableSpace Ω ℝ (f t) _) _
      (fun p => clipPath W t p.1 p.2) := by
  let : MeasurableSpace Ω := f t
  have hprog := Base.isStronglyProgressive_of_rc f (fun (s : ℝ≥0) ω => W ω (s : ℝ))
    h.adapted (fun ω s => by
      have := (h.path ω).rc s s.2
      have ht : Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact (NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds
        · exact eventually_nhdsWithin_of_forall fun u hu => by exact_mod_cast hu
      exact ht.eventually this) t
  have hm := hprog.measurable
  have hcl : Measurable (fun p : Ω × ℝ => (⟨min p.2.toNNReal t, min_le_right _ _⟩ : Set.Iic t)) :=
    Measurable.subtype_mk ((measurable_real_toNNReal.comp measurable_snd).min measurable_const)
  exact (hm.comp (hcl.prodMk measurable_fst) : _)

theorem AdaptedCyclic.clipPath_rc (h : AdaptedCyclic f W) (t : ℝ≥0) (ω : Ω) (s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), clipPath W t ω s' = clipPath W t ω s := by
  set c : ℝ → ℝ := fun u => ((min u.toNNReal t : ℝ≥0) : ℝ) with hc
  have hcont : Continuous c := by
    refine NNReal.continuous_coe.comp ?_
    exact (continuous_real_toNNReal).min continuous_const
  have hmono : Monotone c := fun a b hab => by
    exact_mod_cast min_le_min_right _ (Real.toNNReal_le_toNNReal hab)
  have hrc := (h.path ω).rc (c s) (NNReal.coe_nonneg _)
  have ht : Tendsto c (𝓝[≥] s) (𝓝[≥] (c s)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    exact eventually_nhdsWithin_of_forall fun u hu => hmono hu
  have := ht.eventually hrc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 this
  exact ⟨u - s, sub_pos.2 (mem_Ioi.1 hu), fun s' hs' => hsub ⟨hs'.1, by linarith [hs'.2]⟩⟩

theorem AdaptedCyclic.measurableSet_segRelaxed (h : AdaptedCyclic f W) {β tk x : ℝ}
    (hβ : 0 < β) {k' : ℕ} {t : ℝ≥0} (_htk : 0 ≤ tk) (hx : 0 ≤ x) (hxt : x + tk ≤ t) :
    MeasurableSet[f t] {ω | SegRelaxed β tk (W ω) k' x} := by
  have : Fact (0 < β) := ⟨hβ⟩
  let : MeasurableSpace Ω := f t
  have hjoint := h.measurable_clipPath t
  have key := measurableSet_isRelaxedTimeWrt (β := β) (clipPath W t) (fun _ _ => x) hjoint
    measurable_const (h.clipPath_rc t)
  obtain ⟨S, hS⟩ : ∃ S : Set (Ω × ℝ), S = {p | p.2 ∈ Icc 0 tk ∧
    IsRelaxedTimeWrt β (clipPath W t p.1) x (x + p.2)} := ⟨_, rfl⟩
  have hg : Measurable (fun p : Ω × ℝ => (p.1, x + p.2)) :=
    measurable_fst.prodMk (measurable_const.add measurable_snd)
  have hSm : MeasurableSet S := by
    rw [hS]
    have h1 : MeasurableSet {p : Ω × ℝ | p.2 ∈ Icc (0 : ℝ) tk} := measurable_snd measurableSet_Icc
    have h2 : MeasurableSet {p : Ω × ℝ | IsRelaxedTimeWrt β (clipPath W t p.1) x (x + p.2)} :=
      hg key
    exact h1.inter h2
  have hvol := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hSm
  have hset : {ω | SegRelaxed β tk (W ω) k' x} =
      {ω | ENNReal.ofReal ((9 / 10 + 1 / (k' : ℝ)) * tk) ≤ volume (Prod.mk ω ⁻¹' S)} := by
    ext ω
    simp only [SegRelaxed, mem_ofPred_eq]
    have : {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (W ω) x (x + u)} = Prod.mk ω ⁻¹' S := by
      ext u
      simp only [mem_ofPred_eq, mem_preimage, hS]
      refine and_congr_right fun hu => isRelaxedTimeWrt_congr hβ (fun s hs =>
        (clipPath_eq t ω (by linarith [hs.1]) (by linarith [hs.2, hu.2])).symm)
        (by linarith [hu.1])
    rw [this]
  rw [hset]
  exact measurableSet_le measurable_const hvol

end ElboimSly.Paper
