/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadCongr
public import ElboimSly.Paper.Heavy.Claim69Aux

/-!
# Finitely many blocks are bad by time `t`

Properties of discovered bad blocks (a), `b_t < ∞`.

* `blocks_near_finite`: only finitely many blocks of `ℬ_k` lie within distance `R` of a vertex.
* `badSet_finite`: `{ι | B_ι bad by time t}` is finite, for every `t` (so `b_t < ∞`).
* `badSet_mono`, `badCount_mono`: monotonicity in `t`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem blocks_near_finite (v : Fin d → ℤ) (k R : ℕ) :
    {ι : Fin d → ℤ | latDist v (heavyBlock k ι) ≤ R}.Finite := by
  have hball : {a : Fin d → ℤ | ‖v - a‖ ≤ R}.Finite := by
    refine (Set.Finite.pi (t := fun c : Fin d => Set.Icc (v c - R) (v c + R))
      fun c => Set.finite_Icc _ _).subset ?_
    intro a ha c _
    have h1 : ‖(v - a) c‖ ≤ ‖v - a‖ := norm_le_pi_norm (v - a) c
    have h2 : |v c - a c| ≤ (R : ℝ) := by
      simpa [Int.norm_eq_abs] using h1.trans ha
    have h3 : |v c - a c| ≤ (R : ℤ) := by exact_mod_cast h2
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  refine (hball.image (heavyBlockIdx k)).subset ?_
  intro ι hι
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (heavyBlock_nonempty k ι) hι
  exact ⟨a, ha, (heavyBlock_eq_of_mem haB (mem_heavyBlock_idx k a)).symm⟩

variable {β t₀ : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ}

theorem badSet_mono {t t' : ℝ} (h : t ≤ t') :
    {ι | BadByTime d β t₀ n w ι t} ⊆ {ι | BadByTime d β t₀ n w ι t'} :=
  fun _ hι => BadByTime.mono hι h

/-- Properties of discovered bad blocks (a): `b_t < ∞` (as finiteness of the set of bad blocks). -/
theorem badSet_finite (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ) :
    {ι | BadByTime d β t₀ n w ι t}.Finite := by
  set k := heavyLevel d n
  have hX : (cycIntTimes β ∩ Icc 0 t).Finite := cycIntTimes_inter_Icc_finite hβ t
  have hnear : ∀ x : ℝ, {ι : Fin d → ℤ | w x ∈ latNbhd (heavyBlock k ι) (2 ^ (k + 2))}.Finite := by
    intro x
    have := blocks_near_finite (w x) k (2 ^ (k + 2))
    refine this.subset fun ι hι => ?_
    simpa [latNbhd] using hι
  refine (hX.biUnion fun x _ => hnear x).subset ?_
  intro ι hι
  unfold BadByTime at hι
  dsimp only at hι
  rcases hι with ⟨x, hx, h1, h2, -⟩ | ⟨x, hx, h1, h2, -⟩ | ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, -⟩
  · exact mem_iUnion₂.2 ⟨x, ⟨hx, hx.1, by linarith⟩, h1⟩
  · exact mem_iUnion₂.2 ⟨x, ⟨hx, hx.1, h1⟩, h2⟩
  · exact mem_iUnion₂.2 ⟨x₁, ⟨hx₁, hx₁.1, by linarith⟩, h1⟩

theorem badCount_mono (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) {t t' : ℝ} (h : t ≤ t') :
    badCount d β t₀ n w t ≤ badCount d β t₀ n w t' :=
  Set.ncard_le_ncard (badSet_mono h) (badSet_finite hβ htk t')

end ElboimSly.Paper
