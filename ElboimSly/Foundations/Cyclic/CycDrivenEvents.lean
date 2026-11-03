/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenSol
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# The event set `E_k` and basic properties of world-lines (c)

Basic properties of world-lines (c). `cycEvents` is
`E_k = ({r > 0 : a + r a jump time of X} ∪ {r > 0 : c_δ(r) ∈ C}) + βℤ_{≥0}`, where `C` is the set of
cyclic times of the known rings in copy `ι`. It is locally finite when `C` is finite
(`evtSet_cycEvents`), and then the driven path exists and is unique and jumps only in `E_k`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] in
/-- Two times with the same clock value differ by a positive multiple of `β`. -/
theorem clock_eq_shift (δ : CycData I d) {r' r : ℝ≥0} (hlt : r' < r)
    (h : δ.clock β r' = δ.clock β r) : ∃ k : ℕ, 1 ≤ k ∧ (r : ℝ) = r' + k * β := by
  have hβ : 0 < β := Fact.out
  have hc : (((δ.phase + δ.sgn * (r' : ℝ)) - (δ.phase + δ.sgn * (r : ℝ)) : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp hc
  have hlt' : (r' : ℝ) < r := by exact_mod_cast hlt
  by_cases hf : δ.fwd = true
  · have hs : δ.sgn = 1 := by simp [CycData.sgn, hf]
    rw [hs] at hn
    have hnneg : n < 0 := by
      have : (n : ℝ) * β < 0 := by simp only [zsmul_eq_mul] at hn; linarith
      have : (n : ℝ) < 0 := by
        by_contra hh; push Not at hh; nlinarith
      exact_mod_cast this
    refine ⟨(-n).toNat, by omega, ?_⟩
    have : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by
      have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have h2 : (((-n).toNat : ℕ) : ℝ) = (((-n).toNat : ℤ) : ℝ) := by norm_cast
      rw [h2, this]; push_cast; ring
    rw [this]
    simp only [zsmul_eq_mul] at hn
    linarith
  · have hs : δ.sgn = -1 := by simp [CycData.sgn, hf]
    rw [hs] at hn
    have hnpos : 0 < n := by
      have : (n : ℝ) * β > 0 := by simp only [zsmul_eq_mul] at hn; linarith
      have : (0 : ℝ) < n := by
        by_contra hh; push Not at hh; nlinarith
      exact_mod_cast this
    refine ⟨n.toNat, by omega, ?_⟩
    have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
      have h2 : ((n.toNat : ℕ) : ℝ) = ((n.toNat : ℤ) : ℝ) := by norm_cast
      rw [h2, this]
    rw [this]
    simp only [zsmul_eq_mul] at hn
    linarith

/-- The set of base event times. -/
def cycBase (β : ℝ) [Fact (0 < β)] (Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) : Set ℝ≥0 :=
  {r | 0 < r ∧ (X.left (a + r) ≠ X.fn (a + r) ∨ ∃ e : Edge d, (δ.copy, (e, δ.clock β r)) ∈ Q)}

/-- The event set `E_k`. -/
def cycEvents (β : ℝ) [Fact (0 < β)] (Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) : Set ℝ≥0 :=
  {r | ∃ r0 ∈ cycBase β Q δ X a, ∃ k : ℕ, r = r0 + k * β.toNNReal}

variable {Q : Set (I × RingSpace d β)} {δ : CycData I d} {X : CPath (Fin d → ℤ)} {a : ℝ≥0}

theorem toNNReal_coe (k : ℕ) : ((k * β.toNNReal : ℝ≥0) : ℝ) = k * β := by
  have hβ : 0 < β := Fact.out
  push_cast
  rw [Real.coe_toNNReal _ hβ.le]

omit [MeasurableSpace I] in
/-- Fibres of the clock are `β`-separated hence finite on bounded intervals. -/
theorem finite_clock_fiber (δ : CycData I d) (θ : AddCircle β) (T : ℝ≥0) :
    {r : ℝ≥0 | r ≤ T ∧ δ.clock β r = θ}.Finite := by
  have hβ : 0 < β := Fact.out
  have hβ' : 0 < β.toNNReal := Real.toNNReal_pos.mpr hβ
  refine Set.Finite.of_injOn (f := fun r : ℝ≥0 => ⌊r / β.toNNReal⌋₊)
    (t := Finset.range (⌊T / β.toNNReal⌋₊ + 1)) (fun r hr => ?_) ?_ (Finset.finite_toSet _)
  · simp only [Finset.coe_range, mem_Iio]
    exact Nat.lt_succ_of_le (Nat.floor_le_floor (by gcongr; exact hr.1))
  · intro r hr r' hr' hfl
    by_contra hne
    wlog hlt : r < r' generalizing r r'
    · exact this hr' hr hfl.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    obtain ⟨k, hk, hkk⟩ := clock_eq_shift δ hlt (hr.2.trans hr'.2.symm)
    have h1 : (r' : ℝ) = r + k * β := hkk
    have h2 : r' / β.toNNReal = r / β.toNNReal + k := by
      have : (r' : ℝ≥0) = r + k * β.toNNReal := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, toNNReal_coe]; exact h1
      rw [this, add_div, mul_div_assoc, div_self hβ'.ne', mul_one]
    have h3 : ⌊r' / β.toNNReal⌋₊ = ⌊r / β.toNNReal⌋₊ + k := by
      rw [h2, Nat.floor_add_natCast (by positivity)]
    simp only at hfl
    omega

omit [MeasurableSpace I] in
theorem finite_cycBase (hQ : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite)
    (T : ℝ≥0) : (cycBase β Q δ X a ∩ Iic T).Finite := by
  have hsub : cycBase β Q δ X a ∩ Iic T ⊆
      (fun s : ℝ≥0 => s - a) '' (CDisc X.fn ∩ Iic (a + T)) ∪
      ⋃ θ ∈ {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q},
        {r : ℝ≥0 | r ≤ T ∧ δ.clock β r = θ} := by
    rintro r ⟨⟨hr0, hjr | ⟨e, he⟩⟩, hrT⟩
    · left
      refine ⟨a + r, ⟨(X.mem_CDisc_iff (by positivity)).2 hjr, mem_Iic.mpr (add_le_add le_rfl hrT)⟩, ?_⟩
      simp
    · right
      simp only [mem_iUnion]
      exact ⟨δ.clock β r, ⟨e, he⟩, hrT, rfl⟩
  refine Set.Finite.subset (Set.Finite.union ((X.fin _).image _) (hQ.biUnion fun θ _ =>
    finite_clock_fiber δ θ T)) hsub

omit [MeasurableSpace I] in
theorem evtSet_cycEvents (hQ : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite) :
    EvtSet β Q δ X a (cycEvents β Q δ X a) where
  pos r := by
    rintro ⟨r0, ⟨h0, -⟩, k, rfl⟩
    exact lt_of_lt_of_le h0 le_self_add
  fin T := by
    have hβ' : 0 < β.toNNReal := Real.toNNReal_pos.mpr (Fact.out)
    have hsub : cycEvents β Q δ X a ∩ Iic T ⊆
        ⋃ r0 ∈ cycBase β Q δ X a ∩ Iic T,
          (fun k : ℕ => r0 + k * β.toNNReal) '' Iic ⌊T / β.toNNReal⌋₊ := by
      rintro r ⟨⟨r0, hr0, k, rfl⟩, hrT⟩
      simp only [mem_iUnion]
      refine ⟨r0, ⟨hr0, (show r0 ≤ r0 + (k : ℝ≥0) * β.toNNReal from le_self_add).trans hrT⟩, k, ?_, rfl⟩
      simp only [mem_Iic]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hβ']
      calc (k : ℝ≥0) * β.toNNReal ≤ r0 + k * β.toNNReal := le_add_self
        _ ≤ T := hrT
    exact Set.Finite.subset ((finite_cycBase hQ T).biUnion fun r0 _ =>
      (Set.finite_Iic _).image _) hsub
  noJump r hr hrE := by
    by_contra hne
    exact hrE ⟨r, ⟨hr, Or.inl hne⟩, 0, by simp⟩
  noRing r hr hrE e he := hrE ⟨r, ⟨hr, Or.inr ⟨e, he⟩⟩, 0, by simp⟩
  shift r' r h0 hlt := by
    rintro ⟨r0, hr0, k, rfl⟩ hc
    obtain ⟨m, hm, hmm⟩ := clock_eq_shift δ hlt hc
    refine ⟨r0, hr0, k + m, ?_⟩
    apply NNReal.coe_injective
    have hb := Real.coe_toNNReal β (Fact.out : 0 < β).le
    push_cast at hmm ⊢
    rw [hb] at hmm ⊢
    linarith

omit [MeasurableSpace I] in
/-- Basic properties of world-lines (c), existence, uniqueness, and the location of the jumps. -/
theorem existsUnique_driven {R : Set (I × RingSpace d β)}
    (hQ : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite) :
    ∃ p : CPath (Fin d → ℤ), IsDriven β R Q δ X a p ∧
      (∀ s ∈ CDisc p.fn, s ∈ cycEvents β Q δ X a) ∧
      ∀ p' : CPath (Fin d → ℤ), IsDriven β R Q δ X a p' → p'.fn = p.fn := by
  obtain ⟨p, hp, hd⟩ := exists_driven_of_evtSet (R := R) (evtSet_cycEvents hQ)
  exact ⟨p, hp, hd, fun p' hp' => hp'.fn_eq hp⟩

omit [MeasurableSpace I] in
/-- A driven path driven by a nearest-neighbour path is a nearest-neighbour path. -/
theorem IsDriven.unitJumps {R : Set (I × RingSpace d β)} {p : CPath (Fin d → ℤ)}
    (hX : X.UnitJumps) (h : IsDriven β R Q δ X a p) : p.UnitJumps := by
  classical
  intro s hs
  have hs0 : 0 < s := hs.1
  have hne : p.left s ≠ p.fn s := (p.mem_CDisc_iff hs0).1 hs
  obtain ⟨d1, d2, d3⟩ := h.2.2 s hs0
  set w := p.left s
  show ∑ i, |p.fn s i - w i| = 1
  by_cases hc : ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, δ.clock β s)) ∈
      (Q ∪ drvQown β δ p s)
  · let S : Set ℕ := {n | ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, δ.clock β s)) ∈
      (Q ∪ drvQown β δ p s) ∧ n = edgeEnc e}
    obtain ⟨e0, h1, h2, h3⟩ := Nat.sInf_mem (show S.Nonempty from by
      obtain ⟨e, h1, h2⟩ := hc
      exact ⟨_, e, h1, h2, rfl⟩)
    have := d1 e0 h1 h2 (fun e' a b => by rw [← h3]; exact Nat.sInf_le ⟨e', a, b, rfl⟩)
    exact latticeAdj_of_edge e0 this
  · by_cases hj : X.left (a + s) ≠ X.fn (a + s) ∧
        (∀ e : Edge d, e.1 = s(w, w + (X.fn (a + s) - X.left (a + s))) →
          (δ.copy, (e, δ.clock β s)) ∉ (R ∪ drvZown β δ p s))
    · have := d2 hc hj.1 hj.2
      rw [this]
      have hX' := hX (a + s) ((X.mem_CDisc_iff (by positivity)).2 hj.1)
      simpa using hX'
    · exact absurd (d3 hc hj).symm hne

omit [MeasurableSpace I] in
/-- The chosen `drivenPath` is the driven path. -/
theorem drivenPath_spec {R : Set (I × RingSpace d β)} (hX : X.UnitJumps)
    (hQ : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite) :
    IsDriven β R Q δ X a (drivenPath β R Q δ X a).1 := by
  classical
  obtain ⟨p, hp, -⟩ := existsUnique_driven (R := R) (X := X) (a := a) hQ
  have hex : ∃ p : CycPath d, IsDriven β R Q δ X a p.1 := ⟨⟨p, hp.unitJumps hX⟩, hp⟩
  unfold drivenPath
  rw [dite_eq_left hex]
  exact hex.choose_spec

end ElboimSly.Cyclic

end
