/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.LatticeAdj
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Edge

Lattice, norms, edges, boxes, blocks.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

/-- The set of nearest-neighbour edges `{u, v}` of `ℤᵈ` (unordered pairs with `‖u - v‖₁ = 1`).
Lattice, norms, edges, boxes, blocks. -/
@[expose] def Edge (d : ℕ) : Type :=
  {e : Sym2 (Fin d → ℤ) // ∃ u v, e = s(u, v) ∧ LatticeAdj d u v}

end ElboimSly

end
