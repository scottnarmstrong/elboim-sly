/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEquiv
public import ElboimSly.Foundations.Cyclic.CycSchemeRec
public import ElboimSly.Foundations.Cyclic.CycLines
public import ElboimSly.Foundations.Cyclic.CycRingPiece
public import ElboimSly.Foundations.PPP.Dirac
public import ElboimSly.Foundations.PPP.DissectingExamples
public import ElboimSly.Foundations.PPP.Exploration.Scheme
public import Mathlib

/-!
# The environment scheme as a pure function

The environment scheme of a plan.

## Design note (read this before building on the scheme)

**The space.** The scheme lives on the cyclic space `CycS I d β = I × RingSpace d β`
(the written proof's `𝒮 = I × Ed × 𝕋`) with the intensity `cycIntensity I d β = # ⊗ μ_β`. The segment
API (segment probes on E×mathbbT_β and E×mathbbR) is stated on `E × X`, `E = I × Edge d`, `X = AddCircle β`; the bridge is the
measurable equivalence `cycEquiv : CycS ≃ᵐ E × X` of `CycSchemeEquiv`, which is measure preserving
(`cycEquiv_measurePreserving`). `cycSegR A x sinv h Z` is the segment probe on `CycS` with mask
`Z ⊆ CycS`, defined as `segR A x sinv h (cycEquiv.symm ⁻¹' Z) ∘ cycEquiv`; it is a probe
(`isProbe_cycSegR`).

**The state.** A *state* is `CycScheme.State I d = CycRec I d × Bool`: the record `ρ_j(η)` (always a
*finite* record, `Sum.inl`) and the flag `ε_j(η)` (`true` is `ended`). Entries are indexed from `0`;
the current walk `k` is the *last* entry of `ρ` (`CycRec.lastEntry`), of which `CycScheme.cur`
extracts the data `(δ, r, p)` as follows (`E := cur P st`):

* `r = E.time = ℓ.toNNReal` (finite for finite records), `w = E.pos = p(r)`,
  `ς = E.lastJump = ς_{cnt(r)}` (`0` if no jump);
* `h_fr`, `h_cap`, `h_dl`, `h_gl` are `hFr`, `hCap`, `hDl`, `hGl`, `h` is `hOf` (`0` if ended);
* `h_dl` uses `cycdl_k(ρ|ς)` via `CycPlan.dlOf (ρ.restrictLast ς)`, and the stop test uses
  `CycPlan.stOf`, `CycPlan.dlOf` on the *updated* record; `CycPlan.startOf` is `cycStart_{k+1}`.

**The probe.** `probeA st` is `{(ι, e) : e ∋ w}` (or `∅` when ended), `t_{(ι,e)} = q + σ r`
(`E.frontT`), `σ_{(ι,e)} = σ` (`E.frontS`), horizon `hOf`. The raw probe of step `j` is
`cycSegR (probeA st) (circX E.frontT E.frontS) (circS E.frontT E.frontS) (hOf st) ∅`
(`probeR`); the masked probe in the scheme is `cycSegR … (Z_j η)`, with the mask `Z_j(η)` being
(to be shown) `cycReg(ρ_j(η))`. The front point of `(ι, e)` at parameter `t` is
`circX … (ι,e) t = (ι, e, c_δ(r + t))` (`circX_front`).

**The update.** `CycScheme.upd P sc st o` is the total function `(ρ, ε), (r', ν) ↦ (ρ', ε')`:
`s* = min(r', h)` (`sStar`), the new vertex `newV` (forced event if `s* = h_fr`, using
`CycScheme.forcedEdge`, the `edgeEnc`-least edge `e ∋ w` with `(ι, e, c_δ(r + s*)) ∈ Ring(ρ)`;
otherwise fresh, via the atom map of `cycSeq`, the dissecting system of `CycS`; otherwise `w`),
the extended entry `(δ, p.extend (r + s*) newV)` (`CycPath.extend`, **guarded**, see
`CycSchemePath`), the stop test `stops`, and the start of the next walk
(`CycData.newEntry (CycPlan.startOf ρ')`, an entry of length `0`).
The history recursion is `stateAt`, with `stateAt 0 η = init P` and
`stateAt (k+1) η = upd P sc (stateAt k η.init) η.last`.

**Total functions, junk values.** Everything is total; "junk" values (e.g. on infinite records) are
never reached by the recursion. The correctness lemmas (the environment scheme) must prove that the
guards are true along the recursion: `p` is constant after its length `r`, `p(T-) = w`, the
inf `h_fr` is attained, `Ring(ρ)` is finite, `0 ≤ h_dl, h_gl`, `h ≤ β`. In particular
`hOf_le_beta` below is proved here (needed for the probe).

**Measurability** is in `CycSchemeMeas` (`measurable_upd`, `measurable_stateAt`) and the
instance `cycScheme : ExplScheme (cycIntensity I d β) U` in `CycSchemeInst`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-! ### Edges at a vertex -/

theorem latticeAdj_finite (w : Fin d → ℤ) : {v : Fin d → ℤ | LatticeAdj d w v}.Finite := by
  refine (Set.Finite.pi (t := fun i => Set.Icc (w i - 1) (w i + 1))
    (fun i => Set.finite_Icc _ _)).subset ?_
  intro v hv i _
  have h1 : |w i - v i| ≤ ∑ j, |w j - v j| :=
    Finset.single_le_sum (f := fun j => |w j - v j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : |w i - v i| ≤ 1 := by
    have : ∑ j, |w j - v j| = 1 := hv
    omega
  rw [abs_le] at h2
  constructor <;> omega

theorem edgesAt_finite (w : Fin d → ℤ) : {e : Edge d | Edge.Mem w e}.Finite := by
  have h1 : ((fun v : Fin d → ℤ => (s(w, v) : Sym2 (Fin d → ℤ))) ''
      {v | LatticeAdj d w v}).Finite := (latticeAdj_finite w).image _
  refine (h1.preimage (Subtype.val_injective.injOn)).subset ?_
  intro e he
  obtain ⟨u, v, huv, hadj⟩ := e.2
  have hw : w ∈ e.1 := he
  rw [huv, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · exact ⟨v, hadj, huv.symm⟩
  · exact ⟨u, latticeAdj_symm hadj, by rw [huv]; exact Sym2.eq_swap⟩

/-- The other endpoint of an edge at `w` (`e ∖ w`); `w` if `w ∉ e`. -/
noncomputable def edgeOther (w : Fin d → ℤ) (e : Edge d) : Fin d → ℤ :=
  open scoped Classical in if h : w ∈ e.1 then Sym2.Mem.other h else w

/-- The least element of a set of edges for the fixed enumeration `edgeEnc`, if there is one. -/
noncomputable def leastEdge (Q : Edge d → Prop) : Option (Edge d) :=
  open scoped Classical in
  if h : ∃ e, Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e' then some h.choose else none

/-- The edges `(ι, e)` with `e ∋ w`, as a finset of `E = I × Edge d`. -/
noncomputable def edgesAt (ι : I) (w : Fin d → ℤ) : Finset (I × Edge d) :=
  ((edgesAt_finite w).image (Prod.mk ι)).toFinset

omit [MeasurableSpace I] in
theorem mem_edgesAt {ι : I} {w : Fin d → ℤ} {x : I × Edge d} :
    x ∈ edgesAt ι w ↔ x.1 = ι ∧ Edge.Mem w x.2 := by
  unfold edgesAt
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨rfl, he⟩
  · rintro ⟨h1, h2⟩; exact ⟨x.2, h2, by rw [← h1]⟩

/-! ### The dissecting system of `CycS` -/

/-- The dissecting system of `𝒮 = I × Ed × 𝕋`, used for the atom map (fresh events). -/
noncomputable def cycSeq (I : Type*) [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (d : ℕ) (β : ℝ) [Fact (0 < β)] : SepPartSeq (CycS I d β) :=
  SepPartSeq.prodCount I (ringSeq (Edge d) β)

/-! ### Data of the current walk -/

namespace CycEntry

/-- The current time `r` of a world-line (its length; `0` if infinite). -/
noncomputable def time (E : CycEntry I d) : ℝ≥0 := E.len.toNNReal

/-- The current position `w = p(r)`. -/
noncomputable def pos (E : CycEntry I d) : Fin d → ℤ := E.path.fn E.time

/-- The last jump time `ς` of `p` in `(0, r]` (`0` if none). -/
noncomputable def lastJump (E : CycEntry I d) : ℝ≥0∞ := E.path.jt (E.path.cnt E.time)

/-- The phases `t_{(ι,e)} = q + σ r` of the segment probe. -/
noncomputable def frontT (E : CycEntry I d) : I × Edge d → ℝ :=
  fun _ => E.data.phase + E.data.sgn * (E.time : ℝ)

/-- The orientations `σ_{(ι,e)} = σ` of the segment probe. -/
noncomputable def frontS (E : CycEntry I d) : I × Edge d → ℝ := fun _ => E.data.sgn

omit [MeasurableSpace I] in
theorem frontS_cases (E : CycEntry I d) (e : I × Edge d) : E.frontS e = 1 ∨ E.frontS e = -1 := by
  unfold frontS CycData.sgn
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [MeasurableSpace I] [Fact (0 < β)] in
/-- The front point of `(ι, e)` at parameter `t` is `(ι, e, c_δ(r + t))`. -/
theorem circX_front (E : CycEntry I d) (e : I × Edge d) (t : ℝ≥0) :
    (circX E.frontT E.frontS e (t : ℝ) : AddCircle β) = E.data.clock β (E.time + t) := by
  unfold circX frontT frontS CycData.clock
  congr 1
  push_cast
  ring

end CycEntry

namespace CycScheme

/-- A state of the scheme: the finite record `ρ_j(η)` and the flag `ε_j(η)` (`true` is *ended*). -/
abbrev State (I : Type*) (d : ℕ) : Type _ := CycRec I d × Bool

variable (P : CycPlan I d β) (sc : ℝ≥0∞)

/-- The initial state `(ρ_0, ε_0)`: one entry of length `0` at the start of `cycStart_1`. -/
noncomputable def init : State I d :=
  (CycRec.empty.push (P.startOf CycRec.empty).newEntry, false)

/-- The current walk (last entry of the record). -/
noncomputable def cur (st : State I d) : CycEntry I d := st.1.lastEntry P.junk

/-- `h_fr`: the inf over the known rings `(ι, e, θ')` at the current copy, `e ∋ w`, of the
representative in `(0, β]` of `σ(θ' - c_δ(r))`. -/
noncomputable def hFr (β : ℝ) [Fact (0 < β)] (ρ : CycRec I d) (E : CycEntry I d) : ℝ≥0∞ :=
  open scoped Classical in
  ⨅ x ∈ ρ.ringSet β, if x.1 = E.data.copy ∧ Edge.Mem E.pos x.2.1 then
    ENNReal.ofReal (circS E.frontT E.frontS (x.1, x.2.1) x.2.2) else ⊤

/-- `h_cap = β(⌊r/β⌋ + 1) - r`. -/
noncomputable def hCap (β : ℝ) (E : CycEntry I d) : ℝ≥0∞ :=
  ENNReal.ofReal (β * (⌊(E.time : ℝ) / β⌋₊ + 1) - E.time)

/-- `h_dl = ς + cycdl_k(ρ|ς) - r`. -/
noncomputable def hDl (ρ : CycRec I d) (E : CycEntry I d) : ℝ≥0∞ :=
  E.lastJump + P.dlOf (ρ.restrictLast E.lastJump.toNNReal) - E.time

/-- `h_gl = s_∘ - Λ(ρ) - r`. -/
noncomputable def hGl (ρ : CycRec I d) (E : CycEntry I d) : ℝ≥0∞ := sc - ρ.total - E.time

/-- `min(h_fr, h_cap, h_dl, h_gl)` (as an element of `[0, ∞]`). -/
noncomputable def hAll (st : State I d) : ℝ≥0∞ :=
  min (min (hFr β st.1 (cur P st)) (hCap β (cur P st)))
    (min (hDl P st.1 (cur P st)) (hGl sc st.1 (cur P st)))

/-- The horizon `h` of the probe of the next step (`0` if ended). -/
noncomputable def hOf (st : State I d) : ℝ≥0 := if st.2 then 0 else (hAll P sc st).toNNReal

/-- `A = {(ι, e) : e ∋ w}` (empty if ended). -/
noncomputable def probeA (st : State I d) : Finset (I × Edge d) :=
  if st.2 then ∅ else edgesAt (cur P st).data.copy (cur P st).pos

/-- The raw probe of the next step: the segment probe of segment probes on E×mathbbT_β and E×mathbbR (i) on `𝒮`, unmasked. -/
noncomputable def probeR (st : State I d) : CycS I d β → ℝ≥0∞ :=
  cycSegR (probeA P st) (circX (cur P st).frontT (cur P st).frontS)
    (circS (cur P st).frontT (cur P st).frontS) (hOf P sc st) ∅


/-- `s* = min(r', h)` for the outcome `o = (r', ν)` (finite, since `h` is). -/
noncomputable def sStar (st : State I d) (o : Outcome (CycS I d β)) : ℝ≥0 :=
  (min o.1 (hOf P sc st : ℝ≥0∞)).toNNReal

/-- The forced edge: the `edgeEnc`-least `e ∋ w` with `(ι, e, c_δ(r + s*)) ∈ Ring(ρ)`. -/
noncomputable def forcedEdge (st : State I d) (s : ℝ≥0) : Option (Edge d) :=
  leastEdge fun e => Edge.Mem (cur P st).pos e ∧
    ((cur P st).data.copy, (e, (cur P st).data.clock β ((cur P st).time + s))) ∈ st.1.ringSet β

/-- The fresh edge: `ν = δ_x` with `x = (ι, e, c_δ(r + s*))`, `e ∋ w`, `0 < r' ≤ h`, `x ∉ R(ρ)`. -/
noncomputable def freshEdge [Countable I] [MeasurableSingletonClass I] (st : State I d)
    (o : Outcome (CycS I d β)) : Option (Edge d) :=
  open scoped Classical in
  match (cycSeq I d β).atomMap o.2 with
  | Sum.inl x =>
      if 0 < o.1 ∧ o.1 ≤ (hOf P sc st : ℝ≥0∞) ∧ x.1 = (cur P st).data.copy ∧
          x.2.2 = (cur P st).data.clock β ((cur P st).time + sStar P sc st o) ∧
          Edge.Mem (cur P st).pos x.2.1 ∧ x ∉ st.1.region β
      then some x.2.1 else none
  | Sum.inr _ => none

/-- The new value of the path at `r + s*`: `e ∖ w` for a forced or a fresh event, and `w` otherwise. -/
noncomputable def newV [Countable I] [MeasurableSingletonClass I] (st : State I d)
    (o : Outcome (CycS I d β)) : Fin d → ℤ :=
  open scoped Classical in
  match (if (sStar P sc st o : ℝ≥0∞) = hFr β st.1 (cur P st)
      then forcedEdge P st (sStar P sc st o) else none) with
  | some e => edgeOther (cur P st).pos e
  | none =>
      match freshEdge P sc st o with
      | some e => edgeOther (cur P st).pos e
      | none => (cur P st).pos

/-- The updated last entry `(δ, r + s*, p')`. -/
noncomputable def newEntry [Countable I] [MeasurableSingletonClass I] (st : State I d)
    (o : Outcome (CycS I d β)) : CycEntry I d :=
  ((cur P st).data, (cur P st).2.extend ((cur P st).time + sStar P sc st o)
    (newV P sc st o))

/-- The record `ρ'`: `ρ` with its last entry replaced. -/
noncomputable def newRec [Countable I] [MeasurableSingletonClass I] (st : State I d)
    (o : Outcome (CycS I d β)) : CycRec I d :=
  st.1.setLast (newEntry P sc st o)

/-- Walk `k` stops: either no jump at `r + s*` and `s* = h_dl`, or a jump and
`cycst_k(ρ') = 1` or `cycdl_k(ρ') = 0`. -/
noncomputable def stops [Countable I] [MeasurableSingletonClass I] (st : State I d)
    (o : Outcome (CycS I d β)) : Prop :=
  if newV P sc st o ≠ (cur P st).pos then
    P.stOf (newRec P sc st o) = true ∨ P.dlOf (newRec P sc st o) = 0
  else (sStar P sc st o : ℝ≥0∞) = hDl P st.1 (cur P st)

/-- The update `(ρ_j, ε_j), o ↦ (ρ_{j+1}, ε_{j+1})` of the environment scheme of a plan. -/
noncomputable def upd [Countable I] [MeasurableSingletonClass I] (P : CycPlan I d β) (sc : ℝ≥0∞)
    (st : State I d) (o : Outcome (CycS I d β)) : State I d :=
  open scoped Classical in
  if st.2 then st
  else if stops P sc st o then
    if (st.1.num : ℕ∞) < P.K then
      ((newRec P sc st o).push (P.startOf (newRec P sc st o)).newEntry,
        false)
    else (newRec P sc st o, true)
  else (newRec P sc st o, decide ((sStar P sc st o : ℝ≥0∞) = hGl sc st.1 (cur P st)))

/-- The states `(ρ_j(η), ε_j(η))` along a history. -/
noncomputable def stateAt [Countable I] [MeasurableSingletonClass I] {U : Type*}
    [MeasurableSpace U] (P : CycPlan I d β) (sc : ℝ≥0∞) :
    (k : ℕ) → Hist U (CycS I d β) k → State I d
  | 0, _ => init P
  | k + 1, η => upd P sc (stateAt P sc k η.init) η.last

theorem hOf_le_beta (st : State I d) : (hOf P sc st : ℝ) ≤ β := by
  unfold hOf
  split_ifs
  · simpa using (Fact.out : 0 < β).le
  · have hβ : 0 < β := Fact.out
    have hmin : hAll P sc st ≤ hCap β (cur P st) := by
      unfold hAll
      exact (min_le_left _ _).trans (min_le_right _ _)
    have hcap : hCap β (cur P st) ≤ ENNReal.ofReal β := by
      unfold hCap
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (⌊((cur P st).time : ℝ) / β⌋₊ : ℝ) ≤ ((cur P st).time : ℝ) / β :=
        Nat.floor_le (by positivity)
      have h2 : β * (⌊((cur P st).time : ℝ) / β⌋₊ : ℝ) ≤ ((cur P st).time : ℝ) := by
        calc β * (⌊((cur P st).time : ℝ) / β⌋₊ : ℝ) ≤ β * (((cur P st).time : ℝ) / β) := by gcongr
          _ = _ := by field_simp
      nlinarith
    have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmin.trans hcap)
    rw [ENNReal.toReal_ofReal hβ.le] at h3
    exact h3

end CycScheme

end ElboimSly.Cyclic

end
