/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycChainLimit
public import ElboimSly.Foundations.Cyclic.CycDrivenUnique
public import Mathlib

/-!
# The limit path of a chain of initial pieces

Measurability of record functionals (e). Let `(p_j)` be a chain of initial pieces whose limiting jump
times `τ_a` tend to `∞` (`∀ M, ∃ a, M < τ_a`). Then the pointwise limit `q(r) = lim_j p_j(r)`
exists (the sequence is eventually constant, uniformly on bounded intervals), `q` is a path of length
`⨆ len p_j`, every `p_j` is an initial piece of `q`, and `ς_a(q) = τ_a`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem mem_CDisc_congr_le {f g : ℝ≥0 → V} {T s : ℝ≥0} (h : ∀ u, u ≤ T → f u = g u) (hs : s ≤ T) :
    s ∈ CDisc f ↔ s ∈ CDisc g := by
  have key : ∀ f g : ℝ≥0 → V, (∀ u, u ≤ T → f u = g u) → s ∈ CDisc f → s ∈ CDisc g := by
    intro f g h ⟨hs0, hn⟩
    refine ⟨hs0, fun hev => hn ?_⟩
    filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
    rw [h u ((le_of_lt hus).trans hs), h s hs]
    exact hu
  exact ⟨key f g h, key g f fun u hu => (h u hu).symm⟩

namespace CPath.IsChain

variable {p : ℕ → CPath V} (hp : CPath.IsChain p)
  (hgood : ∀ M : ℝ≥0, ∃ a, (M : ℝ≥0∞) < tau p a)
include hp hgood

/-- Uniform eventual constancy on bounded intervals. -/
theorem stab (T : ℝ≥0) : ∃ J, ∀ j, J ≤ j → ∀ r, r ≤ T → (p j).fn r = (p J).fn r := by
  obtain ⟨J, hJ⟩ := hp.agree_step hgood T
  refine ⟨J, fun j hj r hr => ?_⟩
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [hJ n hn r hr, ih]

open scoped Classical in
/-- The pointwise limit of the chain. -/
noncomputable def limFn (p : ℕ → CPath V) (r : ℝ≥0) : V :=
  if h : ∃ J, ∀ j, J ≤ j → (p j).fn r = (p J).fn r then (p (Nat.find h)).fn r else (p 0).fn r

theorem limFn_spec (T : ℝ≥0) : ∃ J, ∀ j, J ≤ j → ∀ r, r ≤ T → limFn p r = (p j).fn r := by
  obtain ⟨J, hJ⟩ := hp.stab hgood T
  refine ⟨J, fun j hj r hr => ?_⟩
  classical
  have hex : ∃ J', ∀ j, J' ≤ j → (p j).fn r = (p J').fn r := ⟨J, fun j hj => hJ j hj r hr⟩
  unfold limFn
  rw [dite_eq_left hex]
  have h1 : Nat.find hex ≤ J := Nat.find_min' hex (fun j hj => hJ j hj r hr)
  rw [← Nat.find_spec hex J h1]
  exact (hJ j hj r hr).symm

/-- The limit path of a chain of initial pieces with jump times tending to `∞`. -/
noncomputable def limPath : CPath V where
  len := ⨆ j, (p j).len
  fn := limFn p
  rc s := by
    obtain ⟨J, hJ⟩ := hp.limFn_spec hgood (s + 1)
    filter_upwards [(p J).rc s, eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds (lt_add_one s))] with u hu hlt
    rw [hJ J le_rfl u (le_of_lt hlt), hJ J le_rfl s (le_add_of_nonneg_right zero_le)]
    exact hu
  fin T := by
    obtain ⟨J, hJ⟩ := hp.limFn_spec hgood T
    refine ((p J).fin T).subset fun s hs => ⟨?_, hs.2⟩
    obtain ⟨hs0, hs1⟩ := hs.1
    refine ⟨hs0, fun hev => hs1 ?_⟩
    filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
    have hsT : s ≤ T := hs.2
    rw [hJ J le_rfl u ((le_of_lt hus).trans hsT), hJ J le_rfl s hsT]
    exact hu
  const s s' h h' := by
    obtain ⟨J, hJ⟩ := hp.limFn_spec hgood (max s s')
    rw [hJ J le_rfl s (le_max_left _ _), hJ J le_rfl s' (le_max_right _ _)]
    exact (p J).const s s' (le_trans (le_iSup (fun j => (p j).len) J) h)
      (le_trans (le_iSup (fun j => (p j).len) J) h')

theorem limPath_fn : (limPath hp hgood).fn = limFn p := rfl

theorem limPath_len : (limPath hp hgood).len = ⨆ j, (p j).len := rfl

theorem isPiece_limPath (j : ℕ) : (p j).IsPiece (limPath hp hgood) := by
  refine ⟨le_iSup (fun j => (p j).len) j, ?_⟩
  refine CPath.ext' (CPath.cut_len _ _).symm (funext fun s => ?_)
  rw [CPath.cut_fn]
  obtain ⟨J, hJ⟩ := hp.limFn_spec hgood s
  set u : ℝ≥0 := (min (s : ℝ≥0∞) (p j).len).toNNReal with hu
  have hus : u ≤ s := by
    have hm : (min (s : ℝ≥0∞) (p j).len) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    rw [hu, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hm]
    exact min_le_left _ _
  have h1 : limFn p u = (p (max J j)).fn u := hJ _ (le_max_left _ _) u hus
  show (p j).fn s = limFn p u
  rw [h1]
  conv_lhs => rw [(hp.piece (le_max_right J j)).2]
  rw [CPath.cut_fn]

end CPath.IsChain

theorem unitJumps_limPath {d : ℕ} {p : ℕ → CPath (Fin d → ℤ)} (hp : CPath.IsChain p)
    (hgood : ∀ M : ℝ≥0, ∃ a, (M : ℝ≥0∞) < CPath.IsChain.tau p a)
    (hu : ∀ j, (p j).UnitJumps) : (hp.limPath hgood).UnitJumps := by
  intro s hs
  have hs0 : 0 < s := hs.1
  obtain ⟨J, hJ⟩ := hp.limFn_spec hgood s
  have hq : ∀ u, u ≤ s → (hp.limPath hgood).fn u = (p J).fn u := fun u hu => hJ J le_rfl u hu
  have hsd : s ∈ CDisc (p J).fn := (mem_CDisc_congr_le (T := s) hq le_rfl).mp hs
  have hl : (hp.limPath hgood).left s = (p J).left s :=
    CPath.left_congr _ _ hs0 fun t ht => hq t ht.le
  have := hu J s hsd
  rwa [hl, hq s le_rfl]

end ElboimSly.Cyclic

end
