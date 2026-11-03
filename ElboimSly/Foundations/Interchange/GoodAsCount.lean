/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.Edge
public import ElboimSly.Frozen.Defs.LatticeAdj
public import ElboimSly.Frozen.Defs.IsRingPath
public import Mathlib

/-!
# Counting vertex paths

Configurations are a.s. good (proof of (G3): "at most `(2d)^n` vertex paths").

The vertex paths of length `n` from `y` all lie in an explicit finite set of cardinality at most
`K ^ n`, where `K` is the number of unit steps of `ℤᵈ` (which is `2d`).
-/

@[expose] public section

namespace ElboimSly.Interchange

variable {d : ℕ}

/-- The unit steps of `ℤᵈ`. -/
def unitSteps (d : ℕ) : Set (Fin d → ℤ) := {u | ∑ i, |u i| = 1}

theorem unitSteps_finite (d : ℕ) : (unitSteps d).Finite := by
  refine (Set.finite_Icc (-(fun _ : Fin d => (1 : ℤ))) (fun _ => 1)).subset ?_
  intro u hu
  have hle : ∀ i, |u i| ≤ 1 := fun i => by
    have : |u i| ≤ ∑ j, |u j| :=
      Finset.single_le_sum (f := fun j => |u j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [show ∑ j, |u j| = 1 from hu] at this
    exact this
  exact ⟨fun i => (abs_le.1 (hle i)).1, fun i => (abs_le.1 (hle i)).2⟩

/-- The number of unit steps. -/
noncomputable def stepCount (d : ℕ) : ℕ := (unitSteps_finite d).toFinset.card

theorem latticeAdj_iff (a b : Fin d → ℤ) : LatticeAdj d a b ↔ b - a ∈ unitSteps d := by
  unfold LatticeAdj unitSteps
  simp only [Set.mem_ofPred_eq, Pi.sub_apply]
  rw [show ∑ i, |a i - b i| = ∑ i, |b i - a i| from
    Finset.sum_congr rfl fun i _ => abs_sub_comm _ _]

/-- Vertex paths of length `n` from `y` lie in a finite set of size at most `K ^ n`. -/
theorem exists_finset_paths (y : Fin d → ℤ) (n : ℕ) :
    ∃ F : Finset (Fin (n + 1) → Fin d → ℤ), F.card ≤ stepCount d ^ n ∧
      ∀ v : Fin (n + 1) → Fin d → ℤ, v 0 = y →
        (∀ i : Fin n, LatticeAdj d (v i.castSucc) (v i.succ)) → v ∈ F := by
  classical
  induction n with
  | zero =>
    refine ⟨{fun _ => y}, by simp, fun v hv _ => ?_⟩
    simp only [Finset.mem_singleton]
    funext i
    rw [show i = 0 from Fin.fin_one_eq_zero i]; exact hv
  | succ n ih =>
    obtain ⟨F, hcard, hF⟩ := ih
    let f : (Fin (n + 1) → Fin d → ℤ) × (Fin d → ℤ) → (Fin (n + 2) → Fin d → ℤ) :=
      fun p => Fin.snoc (α := fun _ => Fin d → ℤ) p.1 (p.1 (Fin.last n) + p.2)
    refine ⟨(F ×ˢ (unitSteps_finite d).toFinset).image f, ?_, fun v hv0 hadj => ?_⟩
    · calc _ ≤ (F ×ˢ (unitSteps_finite d).toFinset).card := Finset.card_image_le
        _ = F.card * stepCount d := Finset.card_product _ _
        _ ≤ stepCount d ^ n * stepCount d := Nat.mul_le_mul_right _ hcard
        _ = stepCount d ^ (n + 1) := (pow_succ _ _).symm
    · rw [Finset.mem_image]
      have hinit : Fin.init v ∈ F := hF _ (by simpa [Fin.init] using hv0) fun i => by
        simpa [Fin.init] using hadj i.castSucc
      have hl := hadj (Fin.last n)
      rw [latticeAdj_iff] at hl
      refine ⟨(Fin.init v, v (Fin.last (n + 1)) - Fin.init v (Fin.last n)),
        Finset.mem_product.2 ⟨hinit, ?_⟩, ?_⟩
      · simpa [Fin.init] using hl
      · simp only [f]
        rw [add_sub_cancel]
        exact Fin.snoc_init_self v

/-- The two endpoints of an edge are adjacent. -/
theorem latticeAdj_of_edge {e : Edge d} {u w : Fin d → ℤ} (h : e.1 = s(u, w)) :
    LatticeAdj d u w := by
  obtain ⟨a, b, hab, hadj⟩ := e.2
  rw [h] at hab
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · unfold LatticeAdj at hadj ⊢
    rw [show ∑ i, |u i - w i| = ∑ i, |w i - u i| from
      Finset.sum_congr rfl fun i _ => abs_sub_comm _ _]
    exact hadj

end ElboimSly.Interchange
