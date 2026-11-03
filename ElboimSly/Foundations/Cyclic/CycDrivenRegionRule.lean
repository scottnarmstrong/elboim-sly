/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionClass
public import Mathlib

/-!
# The driven walk satisfies the rules (D1')-(D3') up to its closing time

The driven walk is a driven world-line, "The rules agree": for `x ∈ cycCF`, `w = w^x`, `τ = treg^x`
and `r ∈ (0, τ]`, the walk `w` obeys the rule (D1')-(D3') at `r` for the one-walk plan `𝒫₁`
(no previously explored region, no known rings).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {ι : I} {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {x : ℝ≥0 → Fin d → ℤ}

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem mem_drvZown {p : CPath (Fin d → ℤ)} {r : ℝ≥0} {e : Edge d} {θ : AddCircle β} :
    ((ι, (e, θ)) : I × RingSpace d β) ∈ drvZown β (regionData d ι) p r ↔
      ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧ θ = (regionData d ι).clock β r' ∧
        Edge.Mem (p.left r') e := by
  simp [drvZown, regionData, CycData.copy]

theorem CPath.left_eq_leftVal (p : CPath (Fin d → ℤ)) {r : ℝ≥0} (hr : 0 < r) :
    p.left r = leftVal p.fn r :=
  (leftVal_eq_of_eventually hr (p.eventually_left hr)).symm

/-- `x` is the driver `X` seen from time `a`, up to a constant: `x(r) = X(a + r) - c`. -/
def IsShiftOf (X : CPath (Fin d → ℤ)) (a : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : Prop :=
  ∃ c : Fin d → ℤ, ∀ r : ℝ≥0, 0 < r → X.left (a + r) = leftVal x r + c ∧ X.fn (a + r) = x r + c

theorem isShiftOf_self (X : CPath (Fin d → ℤ)) : IsShiftOf X 0 X.fn :=
  ⟨0, fun r hr => by simp [CPath.left_eq_leftVal X hr]⟩

section Rule

variable (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal)
  (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β.toNNReal)
include hx hβ hi

omit [MeasurableSpace I] in
/-- A known ring in the class of `r` through `w(r-)` comes from a forced `k`. -/
theorem forced_edge {r : ℝ≥0} (_hr : 0 < r) (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x)
    {e : Edge d} (hmem : Edge.Mem (leftVal (drivenWalk β.toNNReal x) r) e)
    (hq : ((ι, (e, (regionData d ι).clock β r)) : I × RingSpace d β) ∈
      drvQown β (regionData d ι) (drivenCPath hx hβ) r) :
    ∃ k, ForcedAt β.toNNReal (drivenWalk β.toNNReal x) r k ∧
      e.1 = s(leftVal (drivenWalk β.toNNReal x) (r - k * β.toNNReal),
        drivenWalk β.toNNReal x (r - k * β.toNNReal)) := by
  obtain ⟨-, -, -, -, -, b2, -⟩ := drivenWalk_closing hx hβ hi
  rw [mem_drvQown] at hq
  obtain ⟨r', hr'0, hr'r, hne, hclock, he⟩ := hq
  obtain ⟨k, hk1, hshift⟩ := clock_eq_shift (regionData d ι) hr'r hclock.symm
  have hsh := shift_nnreal.1 hshift
  have hsub : r - k * β.toNNReal = r' := by rw [hsh]; simp
  have hdisc : r' ∈ CDisc (drivenWalk β.toNNReal x) :=
    ((drivenCPath hx hβ).mem_CDisc_iff hr'0).2 hne
  rw [drivenCPath_left hx hβ hr'0] at he
  have hmem' : leftVal (drivenWalk β.toNNReal x) r ∈ e.1 := hmem
  rw [he, Sym2.mem_iff] at hmem'
  rcases hmem' with h | h
  · exact absurd h.symm (b2 r r' k hr'0 hk1 hsh hrτ ∘ Eq.symm)
  · refine ⟨k, ⟨⟨hk1, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [hsh]; exact le_add_self
    · rw [hsub]; exact hdisc
    · rw [hsub]; exact h.symm
    · rw [hsub]; exact he

omit [MeasurableSpace I] in
/-- The jump of the driver at `r` is suppressed iff a known region in the class of `r` contains
`w(r-) + Δx(r)`, in the form of a known region on the edge `{w(r-), w(r-) + Δx(r)}`. -/
theorem zmem_imp_not_taken {r : ℝ≥0} (hrx : r ∈ CDisc x)
    (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x) {e : Edge d}
    (he : e.1 = s(leftVal (drivenWalk β.toNNReal x) r,
      leftVal (drivenWalk β.toNNReal x) r + (x r - leftVal x r)))
    (hz : ((ι, (e, (regionData d ι).clock β r)) : I × RingSpace d β) ∈
      drvZown β (regionData d ι) (drivenCPath hx hβ) r) :
    ¬ TakenAt β.toNNReal x (drivenWalk β.toNNReal x) r := by
  obtain ⟨-, -, -, -, -, b2, -⟩ := drivenWalk_closing hx hβ hi
  intro hT
  rw [mem_drvZown] at hz
  obtain ⟨r', hr'0, hr'r, hclock, hmem⟩ := hz
  obtain ⟨k, hk1, hshift⟩ := clock_eq_shift (regionData d ι) hr'r hclock.symm
  have hsh := shift_nnreal.1 hshift
  have hsub : r - k * β.toNNReal = r' := by rw [hsh]; simp
  rw [drivenCPath_left hx hβ hr'0] at hmem
  have hmem' : leftVal (drivenWalk β.toNNReal x) r' ∈ e.1 := hmem
  rw [he, Sym2.mem_iff] at hmem'
  have hk : IsDelayIdx β.toNNReal r k := ⟨hk1, by rw [hsh]; exact le_add_self⟩
  rcases hmem' with h | h
  · exact b2 r r' k hr'0 hk1 hsh hrτ h.symm
  · have hnj := no_jump_in_class hx hβ hi hrx hrτ hk (by rw [hsub]; exact hr'0)
    rw [hsub] at hnj
    have hl : leftVal (drivenWalk β.toNNReal x) r' = drivenWalk β.toNNReal x r' :=
      (drivenWalk_isRegPath hx.toIsRegPath hβ).leftVal_eq_of_not_mem hr'0 hnj
    apply hT k hk
    rw [hsub, ← hl]; exact h.symm

omit [MeasurableSpace I] in
/-- Conversely, if the jump at `r` is suppressed, the edge lies in the known region. -/
theorem not_taken_imp_zmem (hno : ∀ k : ℕ, 1 ≤ k → (k : ℝ≥0) * β.toNNReal ∉ CDisc x)
    {r : ℝ≥0} (hrx : r ∈ CDisc x)
    (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x)
    (hT : ¬ TakenAt β.toNNReal x (drivenWalk β.toNNReal x) r) :
    ∃ e : Edge d, e.1 = s(leftVal (drivenWalk β.toNNReal x) r,
      leftVal (drivenWalk β.toNNReal x) r + (x r - leftVal x r)) ∧
    ((ι, (e, (regionData d ι).clock β r)) : I × RingSpace d β) ∈
      drvZown β (regionData d ι) (drivenCPath hx hβ) r := by
  unfold TakenAt at hT
  push Not at hT
  obtain ⟨k, hk, heq⟩ := hT
  have hpos : 0 < r - k * β.toNNReal := by
    rcases (zero_le : (0 : ℝ≥0) ≤ r - k * β.toNNReal).eq_or_lt with h0 | h0
    · exfalso
      have : r = k * β.toNNReal := le_antisymm (tsub_eq_zero_iff_le.1 h0.symm) hk.2
      exact hno k hk.1 (this ▸ hrx)
    · exact h0
  set r' := r - k * β.toNNReal with hr'
  have hlt : r' < r := delayIdx_lt β.toNNReal hβ hk
  have hnj := no_jump_in_class hx hβ hi hrx hrτ hk hpos
  have hl : leftVal (drivenWalk β.toNNReal x) r' = drivenWalk β.toNNReal x r' :=
    (drivenWalk_isRegPath hx.toIsRegPath hβ).leftVal_eq_of_not_mem hpos hnj
  have hunit := hx.unit r hrx
  have hadj : ∑ i, |leftVal (drivenWalk β.toNNReal x) r i -
      (leftVal (drivenWalk β.toNNReal x) r + (x r - leftVal x r)) i| = 1 := by
    rw [← hunit]
    exact Finset.sum_congr rfl fun i _ => by simp [abs_sub_comm]
  refine ⟨unitEdge _ _ hadj, rfl, ?_⟩
  rw [mem_drvZown]
  refine ⟨r', hpos, hlt, ?_, ?_⟩
  · symm
    apply clock_eq_of_shift (k := k)
    rw [shift_nnreal, hr']; exact (tsub_add_cancel_of_le hk.2).symm
  · rw [drivenCPath_left hx hβ hpos, hl]
    show _ ∈ s(_, _)
    rw [Sym2.mem_iff]; right; exact heq.symm

omit [MeasurableSpace I] in
/-- **the driven walk is a driven world-line, the rules agree**: for `r ∈ (0, τ]` the driven walk `w^x` obeys the
rule (D1')-(D3') at `r` for the plan `𝒫₁` (empty previous region and rings, offset `0`). -/
theorem drvRule_drivenCPath (hno : ∀ k : ℕ, 1 ≤ k → (k : ℝ≥0) * β.toNNReal ∉ CDisc x)
    {R Q : Set (I × RingSpace d β)} (hR : ∀ (e : Edge d) (θ : AddCircle β), ((ι, (e, θ)) : I × RingSpace d β) ∉ R)
    (hQ : ∀ (e : Edge d) (θ : AddCircle β), ((ι, (e, θ)) : I × RingSpace d β) ∉ Q)
    (X : CPath (Fin d → ℤ)) {a : ℝ≥0} (hXa : IsShiftOf X a x) {r : ℝ≥0} (hr : 0 < r)
    (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x) :
    DrvRule β R Q (regionData d ι) X a (drivenCPath hx hβ) r := by
  obtain ⟨-, -, -, -, -, -, c, -⟩ := drivenWalk_closing hx hβ hi
  have hD := drivenWalk_D123 hx.toIsRegPath hβ hr
  have hQiff := exists_edge_iff (ι := ι) hx hβ hi hr hrτ
  obtain ⟨c0, hc0⟩ := hXa
  obtain ⟨hXl, hXf⟩ := hc0 r hr
  unfold DrvRule
  rw [hXl, hXf, drivenCPath_left hx hβ hr]
  simp only [ne_eq, add_left_inj, add_sub_add_right_eq_sub]
  have hRz : ∀ (e : Edge d) (A : Set (I × RingSpace d β)),
      ((regionData d ι).copy, (e, (regionData d ι).clock β r)) ∈ R ∪ A ↔
        ((regionData d ι).copy, (e, (regionData d ι).clock β r)) ∈ A := fun e A => by
    simp only [Set.mem_union]; exact or_iff_right (hR e _)
  have hQz : ∀ (e : Edge d) (A : Set (I × RingSpace d β)),
      ((regionData d ι).copy, (e, (regionData d ι).clock β r)) ∈ Q ∪ A ↔
        ((regionData d ι).copy, (e, (regionData d ι).clock β r)) ∈ A := fun e A => by
    simp only [Set.mem_union]; exact or_iff_right (hQ e _)
  unfold RuleFn
  simp only [hRz, hQz]
  refine ⟨?_, ?_, ?_⟩
  · intro e hmem hq _
    obtain ⟨k, hF, he⟩ := forced_edge (ι := ι) hx hβ hi hr hrτ hmem hq
    have h1 := hD.1 k hF (fun k' hk' hF' => by have := c r hrτ k' k hF' hF; omega)
    rw [he]
    show _ = s(_, drivenWalk β.toNNReal x r)
    rw [h1, hF.2.2]
    exact Sym2.eq_swap
  · intro hnoe hjmp hZ
    have hnoF : ∀ k, ¬ ForcedAt β.toNNReal (drivenWalk β.toNNReal x) r k :=
      fun k hk => hnoe (hQiff.2 ⟨k, hk⟩)
    have hrx : r ∈ CDisc x := (hx.toIsRegPath.mem_CDisc_iff).2 ⟨hr, hjmp⟩
    have hT : TakenAt β.toNNReal x (drivenWalk β.toNNReal x) r := by
      by_contra h
      obtain ⟨e, he, hz⟩ := not_taken_imp_zmem (ι := ι) hx hβ hi hno hrx hrτ h
      exact hZ e he hz
    have := hD.2.1 hnoF hrx
    rw [ite_eq_left hT] at this
    exact this
  · intro hnoe hnot
    have hnoF : ∀ k, ¬ ForcedAt β.toNNReal (drivenWalk β.toNNReal x) r k :=
      fun k hk => hnoe (hQiff.2 ⟨k, hk⟩)
    by_cases hrx : r ∈ CDisc x
    · have hjmp : leftVal x r ≠ x r := (hx.toIsRegPath.mem_CDisc_iff.1 hrx).2
      have hT : ¬ TakenAt β.toNNReal x (drivenWalk β.toNNReal x) r := fun hT =>
        hnot ⟨hjmp, fun e he hz => zmem_imp_not_taken (ι := ι) hx hβ hi hrx hrτ he hz hT⟩
      have := hD.2.1 hnoF hrx
      rw [ite_eq_right hT] at this
      exact this
    · exact hD.2.2 hnoF hrx

end Rule

end ElboimSly.Cyclic

end
