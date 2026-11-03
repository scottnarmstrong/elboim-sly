/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Meas
public import Mathlib

/-!
# `G_i ∈ ℱ_{ζ_i}`

Phases, radii and events of Claim 5.6.  `stopP N t m i ω` is the walk stopped at `ζ_i`; it is
`ℱ_{ζ_i}`-measurable, and `ℬ_i` is a measurable function of `(stopP, ζ_{i-1}, ζ_i)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
  {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The walk stopped at `ζ_i`. -/
noncomputable def stopP (N : Ω → Measure (CycS ℕ (k + 2) β)) (t : ℝ) (m i : ℕ) (ω : Ω) :
    CPath (Fin (k + 2) → ℤ) := (escCPath N ω).stop (escZt N t m i ω)

theorem escZt_mono (N : Ω → Measure (CycS ℕ (k + 2) β)) {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    {i i' : ℕ} (h : i ≤ i') (ω : Ω) : escZt N t m i ω ≤ escZt N t m i' ω := by
  induction h with
  | refl => exact le_rfl
  | @step i2 _ ih =>
    refine ih.trans ?_
    rw [← NNReal.coe_le_coe, coe_escZt N ht, coe_escZt N ht]
    exact ((escZeta_mem β (escY N ω) ht m i2).2.trans
      (es56B_le_escPhaseA_succ ht m i2)).trans (escZeta_mem β (escY N ω) ht m (i2 + 1)).1

variable (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')

include S in
theorem measurable_stopP {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) :
    Measurable[(isStoppingTime_escZt S ht m i).measurableSpace] (stopP N t m i) := by
  have h := measurable_stoppedPath (f := avoidFilt 𝒢₀ S.space) (escCPath N)
    (fun s => escW_adapted S s) (isStoppingTime_escZt S ht m i)
  exact h

include S in
theorem measurable_escZt_real {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) :
    Measurable[(isStoppingTime_escZt S ht m i).measurableSpace]
      (fun ω => ((escZt N t m i ω : ℝ≥0) : ℝ)) :=
  (measurable_stopReal_stop (isStoppingTime_escZt S ht m i)).coe_nnreal_real

include S in
theorem measurable_escZt_real_mono {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {i i' : ℕ} (h : i ≤ i') :
    Measurable[(isStoppingTime_escZt S ht m i').measurableSpace]
      (fun ω => ((escZt N t m i ω : ℝ≥0) : ℝ)) := by
  have hle : (isStoppingTime_escZt S ht m i).measurableSpace ≤
      (isStoppingTime_escZt S ht m i').measurableSpace :=
    (isStoppingTime_escZt S ht m i).measurableSpace_mono (isStoppingTime_escZt S ht m i')
      (fun ω => WithTop.coe_le_coe.2 (escZt_mono N ht m h ω))
  exact (measurable_escZt_real S ht m i).mono hle le_rfl

section Iff

variable (j : ℕ) (u v z : Fin (k + 2) → ℤ) {t : ℝ} (ht : 0 ≤ t)

include ht

theorem escZeta_yv (ω : Ω) (m i : ℕ) :
    escZeta β (escYv N v ω) t m i = ((escZt N t m i ω : ℝ≥0) : ℝ) := by
  rw [coe_escZt N ht]
  exact escZeta_add_const β v (escY N ω) t m i

omit ht in
theorem escYv_stop (ω : Ω) (m i : ℕ) : ∀ s : ℝ, 0 ≤ s →
    s ≤ ((escZt N t m i ω : ℝ≥0) : ℝ) →
    escYv N v ω s = v + (stopP N t m i ω).fn s.toNNReal := by
  intro s hs0 hs
  unfold stopP
  rw [stop_fn_toNNReal _ _ hs0 hs]
  rfl

theorem EscB0_iff (ω : Ω) :
    EscB0 β j u v z t (escYv N v ω) ↔
      (stopP N t (escPhaseM β t) 0 ω, (0 : ℝ), ((escZt N t (escPhaseM β t) 0 ω : ℝ≥0) : ℝ)) ∈
        setB0 β j u v z t := by
  have hz := escZeta_yv (N := N) v ht ω (escPhaseM β t) 0
  unfold EscB0 setB0
  dsimp only
  rw [hz]
  simp only [mem_inter_iff, mem_ofPred_eq, forallBetween]
  have hy0 := escYv_stop (N := N) (t := t) v ω (escPhaseM β t) 0
  have hend : escYv N v ω ((escZt N t (escPhaseM β t) 0 ω : ℝ≥0) : ℝ) =
      v + (stopP N t (escPhaseM β t) 0 ω).fn
        (((escZt N t (escPhaseM β t) 0 ω : ℝ≥0) : ℝ)).toNNReal :=
    hy0 _ (NNReal.coe_nonneg _) le_rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun s hs0 hs => ?_⟩, ?_⟩
    · rw [← hy0 s hs0 hs]; exact h2 s hs0 hs
    · rw [← hend]; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun s hs0 hs => ?_, ?_⟩
    · rw [hy0 s hs0 hs]; exact h2 s hs0 hs
    · rw [hend]; exact h3

theorem EscBi_iff (ω : Ω) (i : ℕ) (_hi : 1 ≤ i) :
    EscBi β j u v z t (escYv N v ω) i ↔
      (stopP N t (escPhaseM β t) i ω,
        ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ),
        ((escZt N t (escPhaseM β t) i ω : ℝ≥0) : ℝ)) ∈ setBi β j u v z t i := by
  have hz := escZeta_yv (N := N) v ht ω (escPhaseM β t) i
  have hz' := escZeta_yv (N := N) v ht ω (escPhaseM β t) (i - 1)
  unfold EscBi setBi
  dsimp only
  rw [hz, hz']
  simp only [mem_inter_iff, mem_ofPred_eq, forallBetween]
  have hy0 := escYv_stop (N := N) (t := t) v ω (escPhaseM β t) i
  have hend : escYv N v ω ((escZt N t (escPhaseM β t) i ω : ℝ≥0) : ℝ) =
      v + (stopP N t (escPhaseM β t) i ω).fn
        (((escZt N t (escPhaseM β t) i ω : ℝ≥0) : ℝ)).toNNReal :=
    hy0 _ (NNReal.coe_nonneg _) le_rfl
  have hlo : ∀ s : ℝ, ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ) ≤ s → 0 ≤ s :=
    fun s hs => (NNReal.coe_nonneg _).trans hs
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun s hs0 hs => ?_⟩, ?_⟩
    · rw [← hy0 s (hlo s hs0) hs]; exact h2 s hs0 hs
    · rw [← hend]; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun s hs0 hs => ?_, ?_⟩
    · rw [hy0 s (hlo s hs0) hs]; exact h2 s hs0 hs
    · rw [hend]; exact h3

end Iff

section Meas

variable (j : ℕ) (u v z : Fin (k + 2) → ℤ) {t : ℝ} (ht : 0 < t)

include S ht

theorem measurableSet_EscB0 :
    MeasurableSet[(isStoppingTime_escZt S ht.le (escPhaseM β t) 0).measurableSpace]
      {ω | EscB0 β j u v z t (escYv N v ω)} := by
  have hm : Measurable[(isStoppingTime_escZt S ht.le (escPhaseM β t) 0).measurableSpace]
      (fun ω => (stopP N t (escPhaseM β t) 0 ω, (0 : ℝ),
        ((escZt N t (escPhaseM β t) 0 ω : ℝ≥0) : ℝ))) :=
    (measurable_stopP S ht.le _ 0).prodMk
      (measurable_const.prodMk (measurable_escZt_real S ht.le _ 0))
  have := hm (measurableSet_setB0 β j u v z t ht.ne')
  convert this using 1
  ext ω
  exact EscB0_iff j u v z ht.le ω

theorem measurableSet_EscBi {i : ℕ} (hi : 1 ≤ i) :
    MeasurableSet[(isStoppingTime_escZt S ht.le (escPhaseM β t) i).measurableSpace]
      {ω | EscBi β j u v z t (escYv N v ω) i} := by
  have hm : Measurable[(isStoppingTime_escZt S ht.le (escPhaseM β t) i).measurableSpace]
      (fun ω => (stopP N t (escPhaseM β t) i ω,
        ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ),
        ((escZt N t (escPhaseM β t) i ω : ℝ≥0) : ℝ))) :=
    (measurable_stopP S ht.le _ i).prodMk
      ((measurable_escZt_real_mono S ht.le _ (Nat.sub_le i 1)).prodMk
        (measurable_escZt_real S ht.le _ i))
  have := hm (measurableSet_setBi β j u v z t ht.ne' i)
  convert this using 1
  ext ω
  exact EscBi_iff j u v z ht.le ω i hi

theorem measurableSet_EscG (i : ℕ) :
    MeasurableSet[(isStoppingTime_escZt S ht.le (escPhaseM β t) i).measurableSpace]
      {ω | EscG β j u v z t (escYv N v ω) i} := by
  have hmono : ∀ i', i' ≤ i → (isStoppingTime_escZt S ht.le (escPhaseM β t) i').measurableSpace ≤
      (isStoppingTime_escZt S ht.le (escPhaseM β t) i).measurableSpace := fun i' h =>
    (isStoppingTime_escZt S ht.le (escPhaseM β t) i').measurableSpace_mono
      (isStoppingTime_escZt S ht.le (escPhaseM β t) i)
      (fun ω => WithTop.coe_le_coe.2 (escZt_mono N ht.le _ h ω))
  have e : {ω | EscG β j u v z t (escYv N v ω) i} =
      {ω | EscB0 β j u v z t (escYv N v ω)} ∩
        ⋂ i' ∈ Finset.Icc 1 i, {ω | EscBi β j u v z t (escYv N v ω) i'} := by
    ext ω
    simp only [EscG, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_Icc]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, fun i' hi' => h i' hi'.1 hi'.2⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, fun i' h1 h2 => h i' ⟨h1, h2⟩⟩
  rw [e]
  refine MeasurableSet.inter (hmono 0 (Nat.zero_le _) _ (measurableSet_EscB0 S j u v z ht)) ?_
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun i' hi' => ?_
  have hi'' := Finset.mem_Icc.1 (Finset.mem_coe.1 hi')
  exact hmono i' hi''.2 _ (measurableSet_EscBi S j u v z ht hi''.1)

end Meas

end ElboimSly.Paper.Escape

end
