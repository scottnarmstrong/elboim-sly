/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Segments
public import ElboimSly.Paper.Step.Driven
public import Mathlib

/-!
# `Γ(w)` takes values in driving paths

A driving path from independent segments: "`Γ(w)` is right-continuous with `Γ(w)(0) = 0`, and its jumps are
those of the `w_j`, of `ℓ¹`-size `1`."

`isDrivingPath_stepCat`: the concatenation `a ⌢ b` of a driving path `a` (on `[0, T]`) and a
driving path `b` is a driving path. Consequently `stepGamma T ℓ w` is a driving path whenever
every `w i` is.
-/

@[expose] public section

open Filter Topology Set ElboimSly.Cyclic
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

theorem tendsto_tsub_nhdsGE (T s : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => u - T) (𝓝[≥] s) (𝓝[≥] (s - T)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_sub_right T).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u (hu : s ≤ u) => (tsub_le_tsub_right (α := ℝ≥0) hu T : s - T ≤ u - T)⟩

theorem tendsto_tsub_nhdsLT {T s : ℝ≥0} (hTs : T < s) :
    Tendsto (fun u : ℝ≥0 => u - T) (𝓝[<] s) (𝓝[<] (s - T)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_sub_right T).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u hu => by
      have hu' : u < s := hu
      rcases le_or_gt u T with h | h
      · rw [tsub_eq_zero_of_le h]
        exact tsub_pos_of_lt hTs
      · exact (tsub_lt_tsub_iff_right h.le).2 hu'⟩

end ElboimSly.Paper
