/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsG3
public import ElboimSly.Foundations.PPP.SimpleSet2
public import ElboimSly.Foundations.PPP.Finite
public import ElboimSly.Frozen.Defs.Good
public import Mathlib

/-!
# Configurations are almost surely good

Configurations are a.s. good.

A Poisson point process with intensity `μ_β` is almost surely `Good`. (G1) is finiteness and local finiteness;
the counting-measure property and (G2) follow from simplicity (including part (e)) for the
projection `(e, θ) ↦ θ`; (G3) is the Mecke bound of `GoodAsProb`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {N : Ω → Measure (RingSpace d β)} {P : Measure Ω}

theorem ae_mem_bProj_ring (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    ∀ᵐ ω ∂P, N ω ∈ (ringSeq (Edge d) β).bProj (circleSeq β) Prod.snd := by
  refine h.ae_mem_bProj (ringSeq (Edge d) β) (ringSeq_isDissecting (Edge d) β)
    (ring_singleton (Edge d) β) (circleSeq β) measurable_snd fun c => ?_
  have : (Prod.snd : RingSpace d β → AddCircle β) ⁻¹' {c} = Set.univ ×ˢ {c} := by
    ext x; simp
  rw [this]
  show (Measure.count.prod (volume : Measure (AddCircle β))) (Set.univ ×ˢ {c}) = 0
  rw [Measure.prod_prod, volume_singleton_circle β c, mul_zero]

theorem isRingConfig_of_mem_bSimple {ν : Measure (RingSpace d β)}
    (hν : ν ∈ (ringSeq (Edge d) β).bSimple) : IsRingConfig ν := by
  intro A hA
  have h := (SepPartSeq.structure_of_mem_bSimple hν).2.2.2 A hA
  by_cases hfin : (A ∩ SepPartSeq.atoms ν).Finite
  · right
    refine ⟨(A ∩ SepPartSeq.atoms ν).ncard, ?_⟩
    rw [h, ← hfin.cast_ncard_eq]
    simp
  · left
    rw [h, Set.Infinite.encard_eq hfin]
    simp

theorem ae_ringIntensity_edge (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    ∀ᵐ ω ∂P, ∀ e : Edge d, N ω ({e} ×ˢ Set.univ) < ⊤ := by
  have hfin : ∀ e : Edge d, ringIntensity d β ({e} ×ˢ Set.univ) < ⊤ := by
    intro e
    show (Measure.count.prod (volume : Measure (AddCircle β))) _ < ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  filter_upwards [h.ae_forall_natCast_count (A := fun e : Edge d => {e} ×ˢ Set.univ)
    (fun e => (measurableSet_singleton e).prod MeasurableSet.univ) hfin] with ω hω e
  obtain ⟨n, hn⟩ := hω e
  rw [hn]
  exact ENNReal.natCast_lt_top n

/-- Configurations are a.s. good: a Poisson point process with intensity `μ_β` is almost surely
good. -/
theorem ae_good (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    ∀ᵐ ω ∂P, Good (N ω) := by
  filter_upwards [ae_mem_bProj_ring h, ae_ringIntensity_edge h, ae_goodG3 h] with ω hproj hG1 hG3
  rw [SepPartSeq.mem_bProj_iff _ _ measurable_snd] at hproj
  obtain ⟨hs, hinj⟩ := hproj
  refine ⟨isRingConfig_of_mem_bSimple hs, hG1, ⟨fun e θ => ?_, fun e f hef => ?_⟩, hG3⟩
  · rcases (SepPartSeq.structure_of_mem_bSimple hs).1 (e, θ) with h0 | h1
    · rw [h0]; exact zero_le_one
    · rw [h1]
  · rw [Set.disjoint_left]
    intro θ he hf
    have hat : ∀ g : Edge d, θ ∈ ringSet (N ω) g → (g, θ) ∈ SepPartSeq.atoms (N ω) := by
      intro g hg
      have : 1 ≤ N ω {(g, θ)} := hg
      intro h0
      have h0' : N ω {(g, θ)} = 0 := h0
      rw [h0'] at this
      simp at this
    exact hef (congrArg Prod.fst (hinj (hat e he) (hat f hf) rfl))

end ElboimSly.Interchange
