/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LatticeAdj

Lattice, norms, edges, boxes, blocks.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

/-- Lattice points `x, y : ℤᵈ` are nearest neighbours: `‖x - y‖₁ = 1`.
Lattice, norms, edges, boxes, blocks. -/
@[expose] def LatticeAdj (d : ℕ) (u v : Fin d → ℤ) : Prop :=
  ∑ i, |u i - v i| = 1

end ElboimSly

end
