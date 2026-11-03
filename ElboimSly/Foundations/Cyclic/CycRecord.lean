/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPathType
public import ElboimSly.Frozen.Defs.EdgeMem
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.RingSpace
public import Mathlib

/-!
# Walk data, world-lines and records

World-lines, records, exploration plans (first half: walk data, clocks, world-lines, records, explored region,
known rings, ring measure, truncations).

## Design

* `CycData I d := I × (Fin d → ℤ) × ℝ × Bool` is the walk data `δ = (ι, u, q, σ)`. The sign `σ ∈ {1,-1}`
  is a `Bool` (`true` is `+1`, see `CycData.sgn`). A product type has the right σ-algebra for free
  (`I` is a countable measurable space with measurable singletons, i.e. discrete).
* `CycEntry I d := CycData I d × CycPath d` is a *world-line* `(δ, ℓ, p)`: the length `ℓ` is the
  length field of the `CPath`. The written proof also demands `p(0) = u`; we do not put this in the type
  (it would make the type a non-trivial subtype and every later measurability proof pay for it).
  It is the predicate `CycEntry.IsStart`, which is proved for all the records built by the plan
  recursion in basic properties of world-lines.
* A record is `CycRec := (Σ k, Fin k → CycEntry) ⊕ (ℕ → CycEntry)`: the disjoint union over
  `k ∈ ℕ ∪ {∞}` of the sets of `k`-tuples, with the disjoint-union σ-algebra (Mathlib's instances on
  `Sum` and `Sigma`). Entries are indexed from `0`, so entry `k` is the written proof's walk `k + 1`, and
  the written proof's `cycRec_{k-1}` is `CycRecN (k - 1)`.
* Uniform access to entries is `CycRec.nth ρ k : Option CycEntry`.
* The explored region is stated with left limits `p(r-)` (`CPath.left`) exactly as in the written proof.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

/-- Walk data `δ = (ι, u, q, σ)`: copy, start vertex, phase, orientation (`true` is `σ = +1`). -/
abbrev CycData (I : Type*) (d : ℕ) : Type _ := I × (Fin d → ℤ) × ℝ × Bool

namespace CycData

variable {I : Type*} {d : ℕ}

/-- The copy `ι`. -/
def copy (δ : CycData I d) : I := δ.1
/-- The start vertex `u`. -/
def start (δ : CycData I d) : Fin d → ℤ := δ.2.1
/-- The phase `q`. -/
def phase (δ : CycData I d) : ℝ := δ.2.2.1
/-- The orientation: `true` for `σ = +1`. -/
def fwd (δ : CycData I d) : Bool := δ.2.2.2
/-- The sign `σ ∈ {1, -1}`. -/
def sgn (δ : CycData I d) : ℝ := if δ.fwd then 1 else -1

/-- The clock `c_δ(r) = [q + σ r] ∈ ℝ / βℤ`. -/
def clock (β : ℝ) (δ : CycData I d) (r : ℝ≥0) : AddCircle β :=
  ((δ.phase + δ.sgn * (r : ℝ) : ℝ) : AddCircle β)

end CycData

/-- A world-line `(δ, ℓ, p)`: walk data and a nearest-neighbour path with a length. -/
abbrev CycEntry (I : Type*) (d : ℕ) : Type _ := CycData I d × CycPath d

namespace CycEntry

variable {I : Type*} {d : ℕ}

/-- The walk data. -/
def data (e : CycEntry I d) : CycData I d := e.1
/-- The path. -/
def path (e : CycEntry I d) : CPath (Fin d → ℤ) := e.2.1
/-- The length `ℓ`. -/
def len (e : CycEntry I d) : ℝ≥0∞ := e.2.1.len

/-- The world-line condition `p(0) = u`. -/
def IsStart (e : CycEntry I d) : Prop := e.path.fn 0 = e.data.start

/-- Truncation of the entry to length `t`: `(δ, t, p(· ∧ t))`. -/
noncomputable def cut (e : CycEntry I d) (t : ℝ≥0∞) : CycEntry I d := (e.1, e.2.cut t)

/-- The explored region of a world-line:
`{(ι, e, c_δ(r)) : 0 < r ≤ ℓ, r < ∞, e ∋ p(r-)}`. -/
def region (β : ℝ) (e : CycEntry I d) : Set (I × RingSpace d β) :=
  {x | ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ e.len ∧ x.1 = e.data.copy ∧
    x.2.2 = e.data.clock β r ∧ Edge.Mem (e.path.left r) x.2.1}

/-- The known rings of a world-line:
`{(ι, {p(r-), p(r)}, c_δ(r)) : 0 < r ≤ ℓ, p(r) ≠ p(r-)}`. -/
def ringSet (β : ℝ) (e : CycEntry I d) : Set (I × RingSpace d β) :=
  {x | ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ e.len ∧ e.path.left r ≠ e.path.fn r ∧
    x.1 = e.data.copy ∧ x.2.2 = e.data.clock β r ∧ x.2.1.1 = s(e.path.left r, e.path.fn r)}

end CycEntry

/-- Records of exactly `k` world-lines. -/
abbrev CycRecN (I : Type*) (d k : ℕ) : Type _ := Fin k → CycEntry I d

/-- Records: finite or infinite sequences of world-lines (disjoint union). -/
abbrev CycRec (I : Type*) (d : ℕ) : Type _ :=
  (Σ k : ℕ, CycRecN I d k) ⊕ (ℕ → CycEntry I d)

namespace CycRec

variable {I : Type*} {d : ℕ}

/-- The empty record. -/
def empty : CycRec I d := Sum.inl ⟨0, Fin.elim0⟩

/-- The `k`-th entry (from `0`), if it exists. -/
def nth : CycRec I d → ℕ → Option (CycEntry I d)
  | Sum.inl ⟨n, f⟩, k => if h : k < n then some (f ⟨k, h⟩) else none
  | Sum.inr f, k => some (f k)

/-- `e` is an entry of `ρ`. -/
def IsEntry (ρ : CycRec I d) (e : CycEntry I d) : Prop := ∃ k, ρ.nth k = some e

/-- The length of entry `k` (`0` if there is none). -/
def lenAt (ρ : CycRec I d) (k : ℕ) : ℝ≥0∞ := (ρ.nth k).elim 0 CycEntry.len

/-- `Λ_k`: the sum of the lengths of the first `k` entries. -/
noncomputable def cum (ρ : CycRec I d) (k : ℕ) : ℝ≥0∞ := ∑ i ∈ Finset.range k, ρ.lenAt i

/-- The explored region `R(ρ)`. -/
def region (β : ℝ) (ρ : CycRec I d) : Set (I × RingSpace d β) :=
  {x | ∃ e, ρ.IsEntry e ∧ x ∈ e.region β}

/-- The known rings `Ring(ρ)`. -/
def ringSet (β : ℝ) (ρ : CycRec I d) : Set (I × RingSpace d β) :=
  {x | ∃ e, ρ.IsEntry e ∧ x ∈ e.ringSet β}

/-- The ring measure `Σ_{x ∈ Ring(ρ)} δ_x`: counting measure on the known rings. -/
noncomputable def rm [MeasurableSpace I] (β : ℝ) (ρ : CycRec I d) :
    Measure (I × RingSpace d β) :=
  Measure.count.restrict (ρ.ringSet β)

/-- Append a world-line to a record of `k` entries. -/
def snoc {k : ℕ} (ρ : CycRecN I d k) (e : CycEntry I d) : CycRecN I d (k + 1) :=
  Fin.snoc (α := fun _ => CycEntry I d) ρ e

/-- `ρ|s`: replace the last entry `(δ, ℓ, p)` of a finite record by `(δ, s, p(· ∧ s))`. -/
noncomputable def restrictLast (s : ℝ≥0) : CycRec I d → CycRec I d
  | Sum.inl ⟨0, f⟩ => Sum.inl ⟨0, f⟩
  | Sum.inl ⟨n + 1, f⟩ => Sum.inl ⟨n + 1, Function.update f (Fin.last n) ((f (Fin.last n)).cut s)⟩
  | Sum.inr f => Sum.inr f

/-- The total length `Λ(ρ)`: the sum of the lengths of all entries but the last (of all entries, for
an infinite record). -/
noncomputable def total : CycRec I d → ℝ≥0∞
  | ρ@(Sum.inl ⟨n, _⟩) => CycRec.cum ρ (n - 1)
  | Sum.inr f => ∑' k, (f k).len

/-- The truncation of entry `k` of a record at global time `s`: complete if `Λ_{k+1} ≤ s`, and cut
at `s - Λ_k` otherwise. -/
noncomputable def truncEntry (s : ℝ≥0) (ρ : CycRec I d) (k : ℕ) (e : CycEntry I d) :
    CycEntry I d :=
  open scoped Classical in
  if CycRec.cum ρ (k + 1) ≤ s then e else e.cut (s - CycRec.cum ρ k)

/-- `Rec^𝒫(s) = Trunc_s(ρ)`: the record of all walks `k` with `Λ_{k-1} ≤ s`, complete if
`Λ_k ≤ s` and truncated at `s - Λ_{k-1}` otherwise. -/
noncomputable def trunc (s : ℝ≥0) : CycRec I d → CycRec I d
  | ρ@(Sum.inl ⟨n, f⟩) =>
      open scoped Classical in
      let m := (Finset.univ.filter fun i : Fin n => CycRec.cum ρ i ≤ s).card
      have hm : m ≤ n := (Finset.card_le_univ _).trans (by simp)
      Sum.inl ⟨m, fun i => CycRec.truncEntry s ρ i (f (Fin.castLE hm i))⟩
  | ρ@(Sum.inr f) =>
      open scoped Classical in
      if {k : ℕ | CycRec.cum ρ k ≤ s}.Infinite then Sum.inr fun k => CycRec.truncEntry s ρ k (f k)
      else Sum.inl ⟨{k : ℕ | CycRec.cum ρ k ≤ s}.ncard, fun i => CycRec.truncEntry s ρ i (f i)⟩

end CycRec

end ElboimSly.Cyclic

end
