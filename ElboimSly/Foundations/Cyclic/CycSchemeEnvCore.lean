/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAtoms
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import Mathlib

/-!
# The environment scheme (b): one step of the scheme, atoms on the front

The environment scheme (b) (i), (ii). `StepGood` collects what the exploration theorem gives
about the outcome of one step; `claimA` says no atom of `ν` on the front before `s*`;
`atom_end` classifies an atom at the front point at `s*` (known ring, or the revealed point).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

open scoped Classical in
/-- The masked raw probe `R̃` of an unfinished state with record `ρ`: `∞` on `cycReg(ρ)`. -/
noncomputable def Rm (P : CycPlan I d β) (sc : ℝ≥0∞) (ρ : CycRec I d) (y : I × RingSpace d β) :
    ℝ≥0∞ := if y ∈ ρ.region β then ⊤ else CycScheme.probeR P sc (ρ, false) y

/-- What the exploration theorem provides about the outcome `o = (ρ_j, V_j)` of step `j`
(sequential first-point exploration (d), (f)), in terms of the masked probe. -/
structure StepGood (P : CycPlan I d β) (sc : ℝ≥0∞) (ν : Measure (I × RingSpace d β))
    (ρ : CycRec I d) (o : Outcome (CycS I d β)) : Prop where
  V_eq : o.2 = ν.restrict {y | Rm P sc ρ y ≤ o.1}
  le_h : o.1 ≤ (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞)
  front : o.2 {y | Rm P sc ρ y ≠ o.1} = 0
  dirac : o.2 Set.univ ≠ 0 → ∃ x, o.2 = Measure.dirac x ∧ Rm P sc ρ x = o.1
  zero : o.2 Set.univ = 0 → o.1 = (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞)

/-- The front point `(ι, e, c_δ(r + t))` of the current walk of the unfinished state with record `ρ`. -/
noncomputable abbrev fp (P : CycPlan I d β) (ρ : CycRec I d) (e : Edge d) (t : ℝ≥0) :
    I × RingSpace d β := CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t

variable {P : CycPlan I d β} {sc : ℝ≥0∞} {ν : Measure (I × RingSpace d β)}

omit [Countable I] [MeasurableSingletonClass I] in
theorem hOf_coe (ρ : CycRec I d) :
    (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞) = CycScheme.hAll P sc (ρ, false) := by
  unfold CycScheme.hOf
  simp only [Bool.false_eq_true, ite_false]
  refine ENNReal.coe_toNNReal ?_
  refine ne_top_of_le_ne_top ?_ ((min_le_left _ _).trans (min_le_right _ _))
  unfold CycScheme.hCap
  exact ENNReal.ofReal_ne_top

omit [Countable I] [MeasurableSingletonClass I] in
theorem hOf_le_hFr (ρ : CycRec I d) :
    (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞) ≤ CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) := by
  rw [hOf_coe]
  unfold CycScheme.hAll
  exact (min_le_left _ _).trans (min_le_left _ _)

omit [Countable I] [MeasurableSingletonClass I] in
theorem hOf_le_hDl (ρ : CycRec I d) :
    (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞) ≤ CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) := by
  rw [hOf_coe]
  unfold CycScheme.hAll
  exact (min_le_right _ _).trans (min_le_left _ _)

omit [Countable I] [MeasurableSingletonClass I] in
theorem hOf_le_hGl (ρ : CycRec I d) :
    (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞) ≤ CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)) := by
  rw [hOf_coe]
  unfold CycScheme.hAll
  exact (min_le_right _ _).trans (min_le_right _ _)

omit [Countable I] [MeasurableSingletonClass I] in
theorem sStar_coe {ρ : CycRec I d} (o : Outcome (CycS I d β)) :
    (CycScheme.sStar P sc (ρ, false) o : ℝ≥0∞) =
      min o.1 (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

omit [Countable I] [MeasurableSingletonClass I] in
theorem sStar_le_o {ρ : CycRec I d} (o : Outcome (CycS I d β)) :
    (CycScheme.sStar P sc (ρ, false) o : ℝ≥0∞) ≤ o.1 := by
  rw [sStar_coe]; exact min_le_left _ _

omit [Countable I] [MeasurableSingletonClass I] in
theorem sStar_le_h {ρ : CycRec I d} (o : Outcome (CycS I d β)) :
    CycScheme.sStar P sc (ρ, false) o ≤ CycScheme.hOf P sc (ρ, false) := by
  rw [← ENNReal.coe_le_coe, sStar_coe]; exact min_le_right _ _

omit [Countable I] [MeasurableSingletonClass I] in
theorem sStar_eq_of_le_h {ρ : CycRec I d} (o : Outcome (CycS I d β)) (ho : o.1 ≤ (CycScheme.hOf P sc (ρ, false) : ℝ≥0∞)) :
    (CycScheme.sStar P sc (ρ, false) o : ℝ≥0∞) = o.1 := by
  rw [sStar_coe, min_eq_left ho]

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem ringSet_subset_region (ρ : CycRec I d) : ρ.ringSet β ⊆ ρ.region β := by
  rintro x ⟨e, he, r, hr0, hrl, hne, h1, h2, h3⟩
  refine ⟨e, he, r, hr0, hrl, h1, h2, ?_⟩
  show (e.path.left r) ∈ x.2.1.1
  rw [h3]; exact Sym2.mem_mk_left _ _

omit [Countable I] in
theorem one_le_atom_iff (hν : CycGood ν) (y : I × RingSpace d β) : 1 ≤ ν {y} ↔ ν {y} ≠ 0 := by
  constructor
  · intro h; exact ne_of_gt (lt_of_lt_of_le one_pos h)
  · intro hat
    have hb := SepPartSeq.singleton_eq_zero_or_one (good_mem_bSimple (hν y.1)) y.2
    rw [cycSlice_singleton] at hb
    have : ν {(y.1, y.2)} = ν {y} := rfl
    rw [this] at hb
    rcases hb with hb | hb
    · exact absurd hb hat
    · exact hb.ge

variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

theorem claimA (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    {e : Edge d} {t : ℝ≥0} (he : Edge.Mem (CycScheme.cur P (ρ, false)).pos e) (ht0 : 0 < t)
    (hts : (t : ℝ≥0∞) < CycScheme.sStar P sc (ρ, false) o) :
    ν {CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t} = 0 := by
  have hth : t ≤ CycScheme.hOf P sc (ρ, false) :=
    (ENNReal.coe_lt_coe.1 (lt_of_lt_of_le hts (by exact_mod_cast sStar_le_h (P := P) (sc := sc) (ρ := ρ) o))).le
  have htβ : (t : ℝ) ∈ Ioc 0 β :=
    ⟨by exact_mod_cast ht0, (by exact_mod_cast hth : (t : ℝ) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycScheme.hOf_le_beta P sc _)⟩
  by_cases hy : CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t ∈ ρ.region β
  · by_contra hne
    have hring := (h.atom_iff_ring hν hy).1 ((one_le_atom_iff hν _).2 hne)
    have h1 := CycScheme.hFr_le_of_front ρ _ htβ he hring
    have h2 := hOf_le_hFr (P := P) (sc := sc) ρ
    have h3 : (t : ℝ≥0∞) < CycScheme.hOf P sc (ρ, false) :=
      lt_of_lt_of_le hts (by exact_mod_cast sStar_le_h (P := P) (sc := sc) (ρ := ρ) o)
    exact absurd (lt_of_le_of_lt h1 h3) (not_lt.2 h2)
  · have hRm : Rm P sc ρ (CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t) = t := by
      unfold Rm
      rw [ite_eq_right hy]
      exact CycScheme.probeR_front P sc rfl he ht0 hth
    have hto : (t : ℝ≥0∞) < o.1 := lt_of_lt_of_le hts (sStar_le_o o)
    have hmem : CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t ∈
        {y | Rm P sc ρ y ≤ o.1} := by
      show Rm P sc ρ _ ≤ _
      rw [hRm]; exact hto.le
    have hV : o.2 {CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t} =
        ν {CycScheme.frontPt β (CycScheme.cur P (ρ, false)) e t} := by
      rw [hg.V_eq, Measure.restrict_apply (measurableSet_singleton _),
        Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hmem)]
    rw [← hV]
    refine measure_mono_null ?_ hg.front
    rintro _ rfl
    show Rm P sc ρ _ ≠ o.1
    rw [hRm]; exact hto.ne

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem EnvAt.finite_clocks (h : EnvAt P ν k r ρ) :
    {θ : AddCircle β | ∃ x ∈ ρ.ringSet β, x.2.2 = θ}.Finite := by
  rw [h.rec_eq]
  refine finite_clock_ringSet _ (fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [CycRec.snoc, Fin.snoc_last]
    show ((pth P ν k).1.cut (r : ℝ≥0∞)).len ≠ ⊤
    rw [CPath.cut_len]; exact ENNReal.coe_ne_top
  · simp only [CycRec.snoc, Fin.snoc_castSucc]
    rw [P.ideal_apply]
    have := h.allFin j j.2
    exact this.ne

omit [Countable I] in
theorem V_apply_of_mem (hg : StepGood P sc ν ρ o) {y : I × RingSpace d β}
    (hy : Rm P sc ρ y ≤ o.1) : o.2 {y} = ν {y} := by
  rw [hg.V_eq, Measure.restrict_apply (measurableSet_singleton _),
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (show y ∈ {y | Rm P sc ρ y ≤ o.1} from hy))]

theorem atom_end (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    {e : Edge d} (he : Edge.Mem (CycScheme.cur P (ρ, false)).pos e)
    (hs0 : 0 < CycScheme.sStar P sc (ρ, false) o)
    (hat : 1 ≤ ν ({fp P ρ e (CycScheme.sStar P sc (ρ, false) o)} : Set _)) :
    (fp P ρ e (CycScheme.sStar P sc (ρ, false) o) ∈
        ρ.ringSet β ∧
      ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false))) ∨
    (fp P ρ e (CycScheme.sStar P sc (ρ, false) o) ∉
        ρ.region β ∧ o.2 Set.univ ≠ 0) := by
  set s := CycScheme.sStar P sc (ρ, false) o with hsdef
  have hsh : s ≤ CycScheme.hOf P sc (ρ, false) := sStar_le_h o
  have hsβ : (s : ℝ) ∈ Ioc 0 β :=
    ⟨by exact_mod_cast hs0, (by exact_mod_cast hsh : (s : ℝ) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycScheme.hOf_le_beta P sc _)⟩
  by_cases hy : fp P ρ e s ∈ ρ.region β
  · left
    have hring := (h.atom_iff_ring hν hy).1 hat
    refine ⟨hring, le_antisymm ?_ ?_⟩
    · exact (by exact_mod_cast hsh : (s : ℝ≥0∞) ≤ CycScheme.hOf P sc (ρ, false)).trans (hOf_le_hFr ρ)
    · exact CycScheme.hFr_le_of_front ρ _ hsβ he hring
  · right
    refine ⟨hy, ?_⟩
    have hRm : Rm P sc ρ (fp P ρ e s) = s := by
      unfold Rm
      rw [ite_eq_right hy]
      exact CycScheme.probeR_front P sc rfl he hs0 hsh
    have hmem : Rm P sc ρ (fp P ρ e s) ≤ o.1 := by
      rw [hRm]; exact sStar_le_o o
    have := V_apply_of_mem hg hmem
    intro hz
    have h0 : o.2 {fp P ρ e s} = 0 :=
      measure_mono_null (Set.subset_univ _) hz
    rw [this] at h0
    exact (one_le_atom_iff hν _).1 hat h0

end CycSchemeEnv
end ElboimSly.Cyclic

end
