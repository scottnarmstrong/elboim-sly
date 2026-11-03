/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.RelaxedMeasRegen
public import Mathlib

/-!
# Measurability of relaxed times: the regenerated walk, measurable part

Measurability of relaxed times (Steps 2 and 5).

For `ν : Ω → ℕ → Measure (RingSpace d β)` with every `ν · k` measurable and every `ν ω k` good:

* `measurableSet_relaxedTimes`: `{(ω, t) | 0 ≤ t ∧ IsRelaxedTime (ν ω) t}` is measurable;
* `measurable_volume_relaxedTimes`: `ω ↦ |𝒯(ω) ∩ I|` is measurable for measurable `I`;
* `measurableSet_isRelaxedPath`: `{ω | IsRelaxedPath (ν ω) t}` is measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- Selecting a measurable family along a measurable countable index is measurable. -/
theorem measurable_select {X γ : Type*} [MeasurableSpace X] [MeasurableSpace γ] {N : X → ℕ}
    (hN : Measurable N) {f : ℕ → X → γ} (hf : ∀ k, Measurable (f k)) :
    Measurable fun x => f (N x) x :=
  (measurable_from_prod_countable_left (f := fun q : X × ℕ => f q.2 q.1) fun k => hf k).comp
    (measurable_id.prodMk hN)

section Regen

variable (ν : Ω → ℕ → Measure (RingSpace d β)) (hν : ∀ k, Measurable fun ω => ν ω k)
  (hg : ∀ ω k, Good (ν ω k))

include hν hg

theorem measurable_cycTreg_seq (k : ℕ) : Measurable fun ω => cycTreg (ν ω k) := by
  refine measurable_of_Iic fun x => ?_
  by_cases hx : x = ⊤
  · simp [hx]
  · have : (fun ω => cycTreg (ν ω k)) ⁻¹' Iic x =
        (fun ω => ν ω k) ⁻¹' {μ | Good μ ∧ cycTreg μ ≤ ENNReal.ofReal x.toReal} := by
      ext ω
      simp [ENNReal.ofReal_toReal hx, hg ω k]
    rw [this]
    exact hν k (Cyclic.measurableSet_cycTreg_le x.toReal)

theorem measurable_regenSigma_seq (i : ℕ) : Measurable fun ω => regenSigma (ν ω) i :=
  Finset.measurable_sum _ fun k _ => measurable_cycTreg_seq ν hν hg k

theorem measurable_regenCount_max :
    Measurable fun p : Ω × ℝ => regenCount (ν p.1) (max p.2 0) := by
  refine measurable_to_countable' fun k => ?_
  have hT : Measurable fun p : Ω × ℝ => ENNReal.ofReal (max p.2 0) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.max measurable_const)
  have : (fun p : Ω × ℝ => regenCount (ν p.1) (max p.2 0)) ⁻¹' {k} =
      {p | regenSigma (ν p.1) k ≤ ENNReal.ofReal (max p.2 0)} ∩
        {p | ENNReal.ofReal (max p.2 0) < regenSigma (ν p.1) (k + 1)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq]
    exact regenCount_eq_iff (ν p.1) (le_max_right _ _) k
  rw [this]
  exact (measurableSet_le ((measurable_regenSigma_seq ν hν hg k).comp measurable_fst) hT).inter
    (measurableSet_lt hT ((measurable_regenSigma_seq ν hν hg (k + 1)).comp measurable_fst))

theorem measurable_regenStart_max :
    Measurable fun p : Ω × ℝ => regenStart (ν p.1) (max p.2 0) := by
  have := measurable_select (measurable_regenCount_max ν hν hg)
    (f := fun k (p : Ω × ℝ) => (regenSigma (ν p.1) k).toReal) fun k =>
      ENNReal.measurable_toReal.comp ((measurable_regenSigma_seq ν hν hg k).comp measurable_fst)
  exact this

theorem measurable_regenWalk_max :
    Measurable fun p : Ω × ℝ => regenWalk (ν p.1) (max p.2 0) := by
  have hα := measurable_regenStart_max ν hν hg
  have := measurable_select (measurable_regenCount_max ν hν hg)
    (f := fun k (p : Ω × ℝ) => cycWalk (ν p.1 k) 0 0 (max p.2 0 - regenStart (ν p.1) (max p.2 0)))
    fun k => by
      have hk : Measurable fun p : Ω × ℝ => (⟨ν p.1 k, hg p.1 k⟩ : Cyclic.GoodSet d β) :=
        ((hν k).comp measurable_fst).subtype_mk
      exact (Cyclic.measurable_cycWalk_joint (β := β) 0).comp
        (hk.prodMk (measurable_const.prodMk ((measurable_snd.max measurable_const).sub hα)))
  exact this

end Regen

omit [Fact (0 < β)] in
theorem ind_isRelaxedTimeWrt_congr {w w' : ℝ → Fin d → ℤ} {a t : ℝ} (h : ∀ s, 0 ≤ s → w s = w' s)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' a t := by
  have hv : visitedSet w a t = visitedSet w' a t :=
    Set.image_congr fun s hs => h s (ha.trans hs.1)
  unfold IsRelaxedTimeWrt IsHeavy
  simp only [hv, h t ht]
  refine and_congr Iff.rfl (forall_congr' fun s => ?_)
  by_cases hs : a ≤ s
  · simp only [hs, true_implies]
    refine imp_congr_right fun _ => ?_
    rw [h s (ha.trans hs)]
  · simp [hs]

section Main

variable (ν : Ω → ℕ → Measure (RingSpace d β)) (hν : ∀ k, Measurable fun ω => ν ω k)
  (hg : ∀ ω k, Good (ν ω k))

include hν hg

/-- **Measurability of relaxed times** (measurability of relaxed times): the set
`{(ω, t) | t ∈ 𝒯(ω)}` is jointly measurable. -/
theorem measurableSet_relaxedTimes :
    MeasurableSet {p : Ω × ℝ | 0 ≤ p.2 ∧ IsRelaxedTime (ν p.1) p.2} := by
  have hW := measurable_regenWalk_max ν hν hg
  have hA := measurable_regenStart_max ν hν hg
  have hrc : ∀ (ω : Ω) (s : ℝ), ∃ ε > 0, ∀ s' ∈ Ico s (s + ε),
      regenWalk (ν ω) (max s' 0) = regenWalk (ν ω) (max s 0) := by
    intro ω s
    by_cases hs : 0 ≤ s
    · obtain ⟨ε, hε, hc⟩ := regenWalk_rlc (fun k => hg ω k) hs
      refine ⟨ε, hε, fun s' hs' => ?_⟩
      rw [max_eq_left (hs.trans hs'.1), max_eq_left hs]
      exact hc s' hs'
    · push Not at hs
      refine ⟨-s, by linarith, fun s' hs' => ?_⟩
      rw [max_eq_right (by linarith [hs'.2] : s' ≤ 0), max_eq_right hs.le]
  have key := measurableSet_isRelaxedTimeWrt (β := β) (fun ω s => regenWalk (ν ω) (max s 0))
    (fun ω t => regenStart (ν ω) (max t 0)) hW hA hrc
  have e : {p : Ω × ℝ | 0 ≤ p.2 ∧ IsRelaxedTime (ν p.1) p.2} =
      {p : Ω × ℝ | 0 ≤ p.2} ∩ {p : Ω × ℝ | IsRelaxedTimeWrt β (fun s => regenWalk (ν p.1) (max s 0))
        (regenStart (ν p.1) (max p.2 0)) p.2} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun ht => ?_
    rw [max_eq_left ht]
    unfold IsRelaxedTime
    exact ind_isRelaxedTimeWrt_congr (fun s hs => by rw [max_eq_left hs])
      ENNReal.toReal_nonneg ht
  rw [e]
  exact (measurableSet_le measurable_const measurable_snd).inter key

/-- `ω ↦ |𝒯(ω) ∩ I|` is a random variable for every measurable `I`. -/
theorem measurable_volume_relaxedTimes {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable fun ω => volume (I ∩ {t : ℝ | 0 ≤ t ∧ IsRelaxedTime (ν ω) t}) := by
  have hS := (measurable_snd hI).inter (measurableSet_relaxedTimes ν hν hg)
  exact measurable_measure_prodMk_left hS

/-- The event that the regenerated walk is a relaxed path of length `t` is measurable. -/
theorem measurableSet_isRelaxedPath (t : ℝ) :
    MeasurableSet {ω : Ω | IsRelaxedPath (ν ω) t} := by
  have h := measurable_volume_relaxedTimes ν hν hg (measurableSet_Icc (a := (0 : ℝ)) (b := t))
  have e : {ω : Ω | IsRelaxedPath (ν ω) t} = {ω | ENNReal.ofReal
      ((9 / 10 + 1 / (scaleIndex t : ℝ)) * t) ≤
      volume (Icc 0 t ∩ {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (ν ω) s})} := by
    ext ω
    simp only [mem_ofPred_eq, IsRelaxedPath]
    have : {s : ℝ | s ∈ Icc 0 t ∧ IsRelaxedTime (ν ω) s} =
        Icc 0 t ∩ {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (ν ω) s} := by
      ext s
      simp only [mem_ofPred_eq, mem_inter_iff]
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
  rw [e]
  exact measurableSet_le measurable_const h

end Main

end ElboimSly.Paper

end
