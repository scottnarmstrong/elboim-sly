/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5
public import ElboimSly.Paper.Escape.InclusionRestart
public import Mathlib

/-!
# The walks `W_i` of the plan as environment paths; the inclusion at ES22 §5 for the plan

The connecting plan; The inclusion at ES22 §5.

* `envFn_fwd'`: for forward walk data, the environment path is the cyclic walk of the slice.
* `plan5Start_envFn`: the environment path of the walk data of entry `m` of the plan.
* `es5_inclusion_env`: `es5_inclusion` with `W_i` the environment path `P^ν_{(0,p_i,β',+1)}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem envFn_fwd' {I : Type*} [MeasurableSpace I] (ν : Measure (I × RingSpace d β))
    (δ : CycData I d) (hf : δ.fwd = true) (s : ℝ≥0) :
    envFn ν δ s = ElboimSly.cycWalk (cycSlice δ.copy ν) δ.start δ.phase (s : ℝ) := by
  unfold envFn ElboimSly.cycWalk
  have h0 : (0 : ℝ) ≤ s := s.2
  simp only [h0, ↓reduceIte]
  rw [Real.toNNReal_coe]
  simp [envMeasure, hf, CycData.sgn]

omit [Fact (0 < β)] in
/-- The environment path of the walk `W_m` of the plan (entry `m`, `1 ≤ m ≤ I`) is the cyclic
walk of copy `0` started at `p_m` at phase `β'`. -/
theorem plan5Start_envFn {k : ℕ} (ν : Measure (ℕ × RingSpace (k + 2) β)) (D : EscRP k) (i β' m : ℕ)
    (hm0 : m ≠ 0) (hm : m ≤ D.I) (s : ℝ≥0) :
    envFn ν (plan5Start D i β' m) s =
      ElboimSly.cycWalk (cycSlice 0 ν) (D.P m) (β' : ℝ) (s : ℝ) := by
  have : plan5Start D i β' m = (0, D.P m, (β' : ℝ), true) := by
    unfold plan5Start; simp [hm0, hm]
  rw [this]
  exact envFn_fwd' ν _ rfl s

/-- The inclusion at ES22 §5 for the walk `W_i = P^ν_{(0, p, β', +1)}` of the plan: all three claims,
with `W` the first piece `cycWalk (ν^0) 0 0`. -/
theorem es5_inclusion_env {ν : Measure (ℕ × RingSpace d β)} (hν : Good (cycSlice 0 ν))
    {n j : ℕ} (hn : 2000 ≤ n) (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ j) (hj2 : (2 : ℝ) ^ j < 2 * n ^ 20)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) {ξ : ℝ} (hξ : 0 ≤ ξ) {p : Fin d → ℤ} {β' : ℝ}
    {Bm : Set (Fin d → ℤ)}
    (hphase : cycIntPhase β (cycFloor β (ξ + 4 ^ j)) = β')
    (hcon : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 (cycFloor β (ξ + 4 ^ j)) = p)
    (hlt : ENNReal.ofReal (cycFloor β (ξ + 4 ^ j)) < cycTreg (cycSlice 0 ν))
    (h1 : ∀ t : ℝ, 0 < t → t < 4 ^ n → envFn ν (0, p, β', true) t.toNNReal ≠ 0)
    (h2 : ∀ t : ℝ, 0 < t → t < 4 ^ n → Real.log β ≤ t →
      2 * Real.sqrt t / Real.log t < ‖envFn ν (0, p, β', true) t.toNNReal - p‖)
    (h6 : ∀ t : ℝ, 0 ≤ t → t < 4 ^ n →
      (2 : ℝ) ^ j / 8 < Metric.infDist
        (fun c => (envFn ν (0, p, β', true) t.toNNReal c : ℝ))
        ((fun x c => (x c : ℝ)) '' Bm))
    (hWξ : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 ξ ∈ Bm)
    (hpB : ‖ElboimSly.cycWalk (cycSlice 0 ν) 0 0 ξ - p‖ ≤ 2 ^ j) :
    ENNReal.ofReal (cycFloor β (ξ + 4 ^ j) + 4 ^ n) ≤ cycTreg (cycSlice 0 ν) ∧
      (∀ s' : ℝ, 0 ≤ s' →
        ElboimSly.cycWalk (cycSlice 0 ν) 0 0 (cycFloor β (ξ + 4 ^ j) + s') =
          envFn ν (0, p, β', true) s'.toNNReal) ∧
      EscEvent n j (fun t => ElboimSly.cycWalk (cycSlice 0 ν) 0 0 t) ξ := by
  have hW : ∀ t : ℝ, 0 ≤ t →
      ElboimSly.cycWalk (cycSlice 0 ν) p (cycIntPhase β (cycFloor β (ξ + 4 ^ j))) t =
        envFn ν (0, p, β', true) t.toNNReal := by
    intro t ht
    rw [hphase, envFn_fwd' ν _ rfl]
    simp [CycData.copy, CycData.start, CycData.phase, Real.coe_toNNReal t ht]
  have := es5_inclusion hν hn hj1 hj2 hlb hξ (p := p) (Bm := Bm) hcon hlt
    (fun t ht ht' => by rw [hW t ht.le]; exact h1 t ht ht')
    (fun t ht ht' hl => by rw [hW t ht.le]; exact h2 t ht ht' hl)
    (fun t ht ht' => by rw [hW t ht]; exact h6 t ht ht') hWξ hpB
  refine ⟨this.1, fun s' hs' => ?_, this.2.2⟩
  rw [this.2.1 s' hs', hW s' hs']

end ElboimSly.Paper.Escape
