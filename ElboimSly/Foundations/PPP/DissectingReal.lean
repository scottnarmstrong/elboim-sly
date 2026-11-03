/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Dissecting
public import Mathlib

/-!
# Dissecting systems: general constructions and the real line

Examples (a), (c).

* `SepPartSeq.comap`: pull back along a measurable injection.
* `SepPartSeq.IsGenerating`, `isGenerating_of_small_cells`.
* `realSeq`: the dyadic partitions `[k2⁻ᵐ, (k+1)2⁻ᵐ)` of `ℝ`, with `isGenerating_realSeq`.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

namespace SepPartSeq

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- Pull back a separating partition sequence along a measurable injection. -/
def comap (P : SepPartSeq S) (f : T → S) (hf : Measurable f) (hinj : Function.Injective f) :
    SepPartSeq T where
  idx m x := P.idx m (f x)
  measurable_idx m := (P.measurable_idx m).comp hf
  refine m _x _y h := P.refine m _ _ h
  separate _x _y hxy := P.separate _ _ (fun e => hxy (hinj e))

/-- The cells generate the `σ`-algebra. -/
def IsGenerating (P : SepPartSeq S) : Prop :=
  MeasurableSpace.generateFrom {s | ∃ m i, s = P.cell m i} = (inferInstance : MeasurableSpace S)

/-- If cells shrink into every open neighbourhood, the cells generate the Borel `σ`-algebra. -/
theorem isGenerating_of_small_cells [TopologicalSpace S] [BorelSpace S] (P : SepPartSeq S)
    (h : ∀ U : Set S, IsOpen U → ∀ x ∈ U, ∃ m, P.cellOf m x ⊆ U) : P.IsGenerating := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨m, i, rfl⟩
    exact P.measurableSet_cell m i
  · refine (BorelSpace.measurable_eq (α := S)).le.trans ?_
    show MeasurableSpace.generateFrom _ ≤ _
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    have : U = ⋃ p : ℕ × ℕ, ⋃ (_ : P.cell p.1 p.2 ⊆ U), P.cell p.1 p.2 := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := h U hU x hx
        exact ⟨(m, P.idx m x), hm, rfl⟩
      · rintro ⟨p, hp, hxp⟩
        exact hp hxp
    rw [this]
    exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨p.1, p.2, rfl⟩

end SepPartSeq

/-! ### The real line -/

theorem floor_eq_of_floor_two_mul_eq {a b : ℝ} (h : ⌊2 * a⌋ = ⌊2 * b⌋) : ⌊a⌋ = ⌊b⌋ := by
  have key : ∀ a : ℝ, ⌊a⌋ = ⌊2 * a⌋ / 2 := by
    intro a
    rw [Int.floor_eq_iff]
    have h1 := Int.floor_le (2 * a)
    have h2 := Int.lt_floor_add_one (2 * a)
    have e : 2 * (⌊2 * a⌋ / 2) ≤ ⌊2 * a⌋ ∧ ⌊2 * a⌋ + 1 ≤ 2 * (⌊2 * a⌋ / 2) + 2 := by omega
    have e1 : (2 : ℝ) * ((⌊2 * a⌋ / 2 : ℤ) : ℝ) ≤ (⌊2 * a⌋ : ℝ) := by exact_mod_cast e.1
    have e2 : (⌊2 * a⌋ : ℝ) + 1 ≤ 2 * ((⌊2 * a⌋ / 2 : ℤ) : ℝ) + 2 := by exact_mod_cast e.2
    constructor <;> linarith
  rw [key a, key b, h]

/-- The dyadic partitions `[k 2⁻ᵐ, (k+1) 2⁻ᵐ)` of `ℝ`. Examples (a). -/
noncomputable def realSeq : SepPartSeq ℝ where
  idx m x := Equiv.intEquivNat ⌊x * 2 ^ m⌋
  measurable_idx m := Measurable.of_discrete.comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))
  refine m x y h := by
    have h1 := Equiv.injective _ h
    have : ⌊2 * (x * 2 ^ m)⌋ = ⌊2 * (y * 2 ^ m)⌋ := by
      have e : ∀ z : ℝ, 2 * (z * 2 ^ m) = z * 2 ^ (m + 1) := fun z => by ring
      rw [e, e]; exact h1
    exact congrArg _ (floor_eq_of_floor_two_mul_eq this)
  separate x y hxy := by
    have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / |x - y|) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, fun h => ?_⟩
    have h1 : ⌊x * 2 ^ m⌋ = ⌊y * 2 ^ m⌋ := Equiv.injective _ h
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h1
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m)] at h2
    rw [div_lt_iff₀ hpos] at hm
    nlinarith

theorem isGenerating_realSeq : realSeq.IsGenerating := by
  refine realSeq.isGenerating_of_small_cells fun U hU x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨m, fun y hy => hball ?_⟩
  have h1 : ⌊y * 2 ^ m⌋ = ⌊x * 2 ^ m⌋ := Equiv.injective _ hy
  have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h1
  rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m)] at h2
  rw [div_lt_iff₀ hε] at hm
  rw [Metric.mem_ball, Real.dist_eq]
  nlinarith [abs_nonneg (y - x)]

end ElboimSly
