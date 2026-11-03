/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import ElboimSly.Foundations.Cyclic.DrivenMeas
import Mathlib

/-!
# Measurability of the regenerated driven walk

ES22 Lemma 2.1 (d).  For a measurable family `X : α → CPath`
of driving paths, the pieces `x^{(i)}`, the regeneration times `σ_i` and the values
`W^x_reg(t)` are measurable in the parameter.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {α : Type*} [MeasurableSpace α] {d : ℕ}

theorem isRegPath_drivenPieces (b : ℝ≥0) {x : ℝ≥0 → Fin d → ℤ} (hx : IsRegPath x) :
    ∀ n, IsRegPath (drivenPieces b x n)
  | 0 => hx
  | n + 1 => isRegPath_shiftPath (isRegPath_drivenPieces b hx n) _

/-- The pieces `x^{(n)}` as `CPath`s. -/
noncomputable def pieceCPath (b : ℝ≥0) (p : CPath (Fin d → ℤ)) (n : ℕ) : CPath (Fin d → ℤ) :=
  mkCPath (drivenPieces b p.fn n) (isRegPath_drivenPieces b p.isRegPath n)

theorem pieceCPath_fn (b : ℝ≥0) (p : CPath (Fin d → ℤ)) (n : ℕ) :
    (pieceCPath b p n).fn = drivenPieces b p.fn n := rfl

theorem measurable_pieceCPath {b : ℝ≥0} (hb : 0 < b) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) : ∀ n, Measurable fun a => pieceCPath b (X a) n
  | 0 => by
    rw [CPath.measurable_iff]
    exact ⟨measurable_const, fun s => by
      simp only [pieceCPath_fn, drivenPieces]; exact (CPath.measurable_eval s).comp hX⟩
  | n + 1 => by
    have ih := measurable_pieceCPath hb hX n
    have hT : Measurable fun a => (drivenTreg b (pieceCPath b (X a) n).fn).toNNReal :=
      ENNReal.measurable_toNNReal.comp ((measurable_drivenTreg hb).comp ih)
    rw [CPath.measurable_iff]
    refine ⟨measurable_const, fun s => ?_⟩
    have h1 := measurable_fn_at _ ih (fun a => (drivenTreg b (pieceCPath b (X a) n).fn).toNNReal
      + s) (hT.add_const s)
    have h2 := measurable_fn_at _ ih _ hT
    exact h1.sub h2

theorem measurable_drivenSigma {b : ℝ≥0} (hb : 0 < b) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) (n : ℕ) : Measurable fun a => drivenSigma b (X a).fn n := by
  have h : ∀ k, Measurable fun a => drivenTreg b (drivenPieces b (X a).fn k) := fun k => by
    have e : (fun a => drivenTreg b (drivenPieces b (X a).fn k)) =
        (fun p : CPath (Fin d → ℤ) => drivenTreg b p.fn) ∘ (fun a => pieceCPath b (X a) k) := by
      funext a; rw [Function.comp_apply, pieceCPath_fn]
    rw [e]
    exact (measurable_drivenTreg hb).comp (measurable_pieceCPath hb hX k)
  have := Finset.measurable_sum (Finset.range n) (fun k _ => h k)
  convert this using 2 with a
  simp [drivenSigma, partialSums]

theorem drivenSigma_ge (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n : ℕ) :
    (n : ℝ≥0∞) * b ≤ drivenSigma b x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [drivenSigma_succ, Nat.cast_succ, add_mul, one_mul]
    exact add_le_add ih (le_pathTreg _ _)

theorem exists_gluedCount (b : ℝ≥0) (hb : 0 < b) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    ∃ n, drivenSigma b x n ≤ t ∧ (t : ℝ≥0∞) < drivenSigma b x (n + 1) := by
  classical
  have hex : ∃ n : ℕ, (t : ℝ≥0∞) < drivenSigma b x (n + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / b)
    refine ⟨n, lt_of_lt_of_le ?_ (drivenSigma_ge b x (n + 1))⟩
    have : t < ((n + 1 : ℕ) : ℝ≥0) * b := by
      have h := (div_lt_iff₀ hb).1 hn
      calc t < n * b := h
        _ ≤ _ := by push_cast; nlinarith
    exact_mod_cast this
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, drivenSigma_zero]; exact zero_le
  · have := Nat.find_min hex (Nat.pred_lt h.ne')
    rw [Nat.pred_eq_sub_one, Nat.sub_add_cancel h] at this
    exact not_lt.1 this

theorem measurable_gluedCount {b : ℝ≥0} (hb : 0 < b) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) (t : ℝ≥0) :
    Measurable fun a => gluedCount (drivenSigma b (X a).fn) t := by
  refine measurable_to_countable' fun n => ?_
  have : (fun a => gluedCount (drivenSigma b (X a).fn) t) ⁻¹' {n} =
      {a | drivenSigma b (X a).fn n ≤ t} ∩ {a | (t : ℝ≥0∞) < drivenSigma b (X a).fn (n + 1)} := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨m, h1, h2⟩ := exists_gluedCount b hb (X a).fn t
      rw [gluedCount_eq (drivenSigma_mono b _) h1 h2] at h
      subst h; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact gluedCount_eq (drivenSigma_mono b _) h1 h2
  rw [this]
  exact (measurableSet_le (measurable_drivenSigma hb hX n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_drivenSigma hb hX (n + 1)))

/-- ES22 Lemma 2.1 (d): `W^x_reg(t)` is measurable in the driving path. -/
theorem measurable_drivenRegenFrom_at {b : ℝ≥0} (hb : 0 < b) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) (t : ℝ≥0) : Measurable fun a => drivenRegenFrom b (X a).fn t := by
  have hF : ∀ n, Measurable fun a => drivenWalk b (drivenPieces b (X a).fn n)
      (t - (drivenSigma b (X a).fn n).toNNReal) := by
    intro n
    have hs : Measurable fun a => t - (drivenSigma b (X a).fn n).toNNReal :=
      measurable_const.sub (ENNReal.measurable_toNNReal.comp (measurable_drivenSigma hb hX n))
    exact measurable_drivenWalk_at (X := fun a => pieceCPath b (X a) n) hb
      (measurable_pieceCPath hb hX n) hs
  exact measurable_index (measurable_gluedCount hb hX t) hF

/-- `W^x_reg(t)` is measurable on the set of regular driving paths, with the trace of the product
`σ`-algebra. -/
theorem measurable_drivenRegenFrom_subtype {b : ℝ≥0} (hb : 0 < b) (t : ℝ≥0) :
    Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => drivenRegenFrom b x.1 t := by
  have hX : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      mkCPath x.1 x.2 := by
    unfold mkCPath
    rw [CPath.measurable_iff]
    exact ⟨measurable_const, fun s => (measurable_pi_apply s).comp measurable_subtype_coe⟩
  exact measurable_drivenRegenFrom_at hb hX t

end ElboimSly.Cyclic

end
