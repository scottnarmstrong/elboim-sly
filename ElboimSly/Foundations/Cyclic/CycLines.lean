/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlan
public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
public import ElboimSly.Frozen.Defs.Good
public import ElboimSly.Frozen.Defs.EdgeInstCountable
public import Mathlib

/-!
# World-lines of a plan and the joint exploration filtration

World-lines of a plan; joint exploration filtration.

## Design

* The environment is a measure `ν` on `I × RingSpace d β` (the written proof's `𝒮 = I × Ed × 𝕋`).
  `cycSlice ι ν` is `ν^ι`, `CycGood ν` says every slice is good, and `envMeasure ν δ` is
  `ν^{ι,σ}` (the slice, reflected by `reflectMeasure` when `σ = -1`).
* The environment path `P^ν_δ` is `envFn ν δ`, the forward trajectory `γ_{u,σq}` of `envMeasure ν δ`,
  chosen by `Classical.epsilon` as in `cycWalk` (D16): on good `ν` it exists and is unique, off
  good `ν` it is junk that nothing uses. As a record entry it is `envPath ν δ : CycPath d`, which is
  the same function whenever it lies in `CycPath` (basic properties of world-lines (a)), and a constant junk path
  otherwise.
* The driven path is likewise defined by `Classical.choose` from the specification
  `IsDriven` = the conditions of world-lines of a plan; joint exploration filtration (b) with rules (D1′)–(D3′); basic properties of world-lines (c)
  proves existence and uniqueness, so this is the driven path.
* Both recursions are one recursion, `CycPlan.cycFinal`, parametrised by the *path rule*
  `path k ρ : CycPath d` giving the full path of walk `k + 1` after the record `ρ` of the first
  `k` walks. The environment instance is `path k ρ = envPath ν (start k ρ)`. The driven instance
  is `drivenPath`.
* The final record is `state n` for the first `n` at which the recursion has ended, and otherwise the
  infinite record whose `k`-th entry is the last entry of `state (k + 1)`.
* Walks of a driven record are driven by `X (J k ρ)` from the offset
  `Σ_{k' < k, J k' = J k} ℓ_{k'}` (`drvOffset`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `ν^ι`, the restriction of `ν` to `{ι} × S_β ≅ S_β`. -/
noncomputable def cycSlice (ι : I) (ν : Measure (I × RingSpace d β)) : Measure (RingSpace d β) :=
  ν.comap (Prod.mk ι)

/-- `ν` is good if every slice `ν^ι` is good. -/
def CycGood (ν : Measure (I × RingSpace d β)) : Prop := ∀ ι : I, Good (cycSlice ι ν)

/-- `ν^{ι,σ}`: `ν^ι` if `σ = 1`, and `ϱ_* ν^ι` if `σ = -1`. -/
noncomputable def envMeasure (ν : Measure (I × RingSpace d β)) (δ : CycData I d) :
    Measure (RingSpace d β) :=
  open scoped Classical in
  if δ.fwd then cycSlice δ.copy ν else Interchange.reflectMeasure β (cycSlice δ.copy ν)

/-- The environment path `P^ν_δ(r) = γ^{ν^{ι,σ}}_{u,σq}(σq + r)` as a function `ℝ≥0 → ℤᵈ`. -/
noncomputable def envFn (ν : Measure (I × RingSpace d β)) (δ : CycData I d) :
    ℝ≥0 → Fin d → ℤ :=
  Classical.epsilon fun γ => IsForwardTrajectory (envMeasure ν δ) δ.start (δ.sgn * δ.phase) γ

/-- The environment path as an element of `CycPath` (a constant junk path if `envFn` is not one). -/
noncomputable def envPath (ν : Measure (I × RingSpace d β)) (δ : CycData I d) : CycPath d :=
  open scoped Classical in
  if h : ∃ p : CycPath d, p.1.len = ⊤ ∧ p.1.fn = envFn ν δ then h.choose
  else CycPath.const δ.start

/-- The path rule of a plan: the full path of walk `k + 1` after the record of the first `k`. -/
abbrev PathRule (I : Type*) (d : ℕ) : Type _ := ∀ k : ℕ, CycRecN I d k → CycPath d

namespace CycPlan

variable (P : CycPlan I d β)

/-- The recursion has ended: `K` walks are done, or the last walk has infinite length. -/
def Ended : CycRec I d → Prop
  | Sum.inl ⟨k, f⟩ => P.K ≤ k ∨ ∃ h : 0 < k, (f ⟨k - 1, by omega⟩).len = ⊤
  | Sum.inr _ => True

/-- One step of the recursion of world-lines of a plan; joint exploration filtration (a): append walk `k + 1` unless ended. -/
noncomputable def cycStep (path : PathRule I d) : CycRec I d → CycRec I d
  | Sum.inl ⟨k, f⟩ =>
      open scoped Classical in
      if P.Ended (Sum.inl ⟨k, f⟩) then Sum.inl ⟨k, f⟩
      else Sum.inl ⟨k + 1, CycRec.snoc f
        (P.start k f, (path k f).cut (P.stopLen k f (path k f)))⟩
  | Sum.inr f => Sum.inr f

/-- The record after `n` steps. -/
noncomputable def cycState (path : PathRule I d) (n : ℕ) : CycRec I d :=
  (P.cycStep path)^[n] CycRec.empty

/-- The final record of the recursion with path rule `path`. -/
noncomputable def cycFinal (path : PathRule I d) : CycRec I d :=
  open scoped Classical in
  if h : ∃ n, P.Ended (P.cycState path n) then P.cycState path (Nat.find h)
  else Sum.inr fun k => ((P.cycState path (k + 1)).nth k).getD P.junk

/-- The final record `ρ^𝒫(ν)` of the environment world-lines. World-lines of a plan; joint exploration filtration (a). -/
noncomputable def envFinal (ν : Measure (I × RingSpace d β)) : CycRec I d :=
  P.cycFinal fun k ρ => envPath ν (P.start k ρ)

end CycPlan

/-! ### Driven world-lines -/

/-- The fixed enumeration of `Ed` used in (D1′). -/
noncomputable def edgeEnc {d : ℕ} (e : Edge d) : ℕ := (Encodable.ofCountable (Edge d)).encode e

/-- The conditions defining the driven path of world-lines of a plan; joint exploration filtration (b), for walk data `δ`, previously
explored region `R` and known rings `Q`, driving path `X` and driving offset `a`:
`p` has length `∞`, `p(0) = u`, and (D1′)–(D3′) hold at every `r > 0`. -/
def IsDriven (β : ℝ) [Fact (0 < β)] (R Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) (p : CPath (Fin d → ℤ)) : Prop :=
  p.len = ⊤ ∧ p.fn 0 = δ.start ∧ ∀ r : ℝ≥0, 0 < r →
    let w := p.left r
    let θ := δ.clock β r
    let Z : Set (I × RingSpace d β) := R ∪ {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧ Edge.Mem (p.left r') x.2.1}
    let Q' : Set (I × RingSpace d β) := Q ∪ {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
      x.2.1.1 = s(p.left r', p.fn r')}
    -- (D1′)
    (∀ e : Edge d, Edge.Mem w e → (δ.copy, (e, θ)) ∈ Q' →
      (∀ e' : Edge d, Edge.Mem w e' → (δ.copy, (e', θ)) ∈ Q' → edgeEnc e ≤ edgeEnc e') →
        e.1 = s(w, p.fn r)) ∧
    -- (D2′)
    ((¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') →
      X.left (a + r) ≠ X.fn (a + r) →
      (∀ e : Edge d, e.1 = s(w, w + (X.fn (a + r) - X.left (a + r))) →
        (δ.copy, (e, θ)) ∉ Z) →
      p.fn r = w + (X.fn (a + r) - X.left (a + r))) ∧
    -- (D3′)
    ((¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') →
      ¬ (X.left (a + r) ≠ X.fn (a + r) ∧
        (∀ e : Edge d, e.1 = s(w, w + (X.fn (a + r) - X.left (a + r))) →
          (δ.copy, (e, θ)) ∉ Z)) →
      p.fn r = w)

/-- The driven path (world-lines of a plan; joint exploration filtration (b)); it exists and is unique by basic properties of world-lines (c). -/
noncomputable def drivenPath (β : ℝ) [Fact (0 < β)] (R Q : Set (I × RingSpace d β))
    (δ : CycData I d) (X : CPath (Fin d → ℤ)) (a : ℝ≥0) : CycPath d :=
  open scoped Classical in
  if h : ∃ p : CycPath d, IsDriven β R Q δ X a p.1 then h.choose else CycPath.const δ.start

/-- The driving offset `a_k = Σ_{k' < k, J_{k'} = J_k} ℓ_{k'}` of walk `k + 1` after the record `ρ`
of the first `k` walks (the lengths of the earlier walks are finite). -/
noncomputable def drvOffset {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) {k : ℕ}
    (ρ : CycRecN I d k) (j : J) : ℝ≥0 :=
  open scoped Classical in
  ∑ i : Fin k, if jx i (fun m : Fin i => ρ ⟨m, lt_trans m.2 i.2⟩) = j then (ρ i).len.toNNReal
    else 0

namespace CycPlan

variable (P : CycPlan I d β)

/-- The driven final record `ρ^𝒫(X)`. World-lines of a plan; joint exploration filtration (b). -/
noncomputable def drivenFinal {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d) :
    CycRec I d :=
  P.cycFinal fun k ρ =>
    drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩)) (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩))
      (P.start k ρ) (X (jx k ρ)).1 (drvOffset jx ρ (jx k ρ))

end CycPlan

/-- The null-set σ-algebra: generated by the `μ`-null measurable sets. -/
@[instance_reducible] def cycNull {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {A | MeasurableSet A ∧ μ A = 0}

/-- The joint exploration filtration `F_s = G₀ ∨ σ(Rec(s') : s' ≤ s) ∨ 𝒩`, where `R : Ω → CycRec`
is the (random) final record and `Rec(s') = Trunc_{s'}(R)`. World-lines of a plan; joint exploration filtration (c). -/
@[instance_reducible] noncomputable def cycFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : @Measure Ω mΩ) (𝒢₀ : MeasurableSpace Ω)
    (R : Ω → CycRec I d) (s : ℝ≥0) : MeasurableSpace Ω :=
  𝒢₀ ⊔ (⨆ s' ≤ s, MeasurableSpace.comap (fun ω => CycRec.trunc s' (R ω)) inferInstance) ⊔
    @cycNull Ω mΩ μ

end ElboimSly.Cyclic

end
