/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPath
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFront
public import ElboimSly.Foundations.Cyclic.CycFinalNth
public import Mathlib

/-!
# The environment scheme (b): the invariant of the scheme along an environment

The environment scheme (b).

`EnvAt P ν k r ρ` says that the record `ρ` consists of the first `k` environment world-lines of the
plan `P` in full (the record `P.ideal` of the recursion of world-lines of a plan; joint exploration filtration (a) that always appends)
followed by the initial piece `(δ_k, P^ν_{δ_k}(· ∧ r))` of the environment world-line of walk `k`.
It also records the three facts that make the recursion append walk `k`: the earlier world-lines
have finite length, `k < K`, and no stopping candidate of walk `k` lies in `(0, r]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycSchemeEnv

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The environment path rule of a plan. -/
noncomputable abbrev rule (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) : PathRule I d :=
  fun k ρ => envPath ν (P.start k ρ)

variable (P : CycPlan I d β) (ν : Measure (I × RingSpace d β))

/-- The data of walk `k` (0-indexed) after the first `k` full environment world-lines. -/
noncomputable def dat (k : ℕ) : CycData I d := P.start k (P.ideal (rule P ν) k)

/-- The full environment path of walk `k`. -/
noncomputable def pth (k : ℕ) : CycPath d := envPath ν (dat P ν k)

/-- The set whose infimum is the stopping length of walk `k`. -/
def cand (k : ℕ) : Set ℝ≥0∞ :=
  {t | ∃ a : ℕ, 1 ≤ a ∧ (pth P ν k).1.jt a < ⊤ ∧
      P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) a) = true ∧
        t = (pth P ν k).1.jt a} ∪
    {t | ∃ a : ℕ, (pth P ν k).1.jt a < ⊤ ∧
      t = (pth P ν k).1.jt a + P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) a) ∧
        t < (pth P ν k).1.jt (a + 1)}

omit [Fact (0 < β)] in
theorem stopLen_eq_sInf (k : ℕ) :
    P.stopLen k (P.ideal (rule P ν) k) (pth P ν k) = sInf (cand P ν k) := rfl

omit [Fact (0 < β)] in
/-- The world-line `E k`: the full environment path of walk `k`, cut at its stopping length. -/
theorem E_eq (k : ℕ) : P.E (rule P ν) k = (dat P ν k, (pth P ν k).cut (sInf (cand P ν k))) := rfl

/-- The scheme's record is `k` full environment world-lines and an initial piece of walk `k`. -/
structure EnvAt (k : ℕ) (r : ℝ≥0) (ρ : CycRec I d) : Prop where
  rec_eq : ρ = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k)
    (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞))⟩
  allFin : P.AllFin (rule P ν) k
  lt_K : (k : ℕ∞) < P.K
  pre : r = 0 ∨ ∀ c ∈ cand P ν k, (r : ℝ≥0∞) < c

end CycSchemeEnv

end ElboimSly.Cyclic

end
