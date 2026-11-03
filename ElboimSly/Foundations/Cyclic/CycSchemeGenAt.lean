/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPath
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFront
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvStopPath
public import ElboimSly.Foundations.Cyclic.CycFinalNth
public import Mathlib

/-!
# The invariant of the scheme along a path rule (generic form of `EnvAt`)

The environment scheme (b), the driving scheme (c).

`GAt P rl k r ρ` is `EnvAt` with the path rule `rl : PathRule I d` of the recursion of
World-lines of a plan; joint exploration filtration (a) left abstract: the record `ρ` consists of the first `k` world-lines of the
recursion with rule `rl` in full (`P.ideal rl`) followed by the initial piece
`(δ_k, rl_k(· ∧ r))` of the world-line of walk `k`. For the environment rule this is `EnvAt`; for the
driven rule it is the invariant of the driving scheme (c).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycSchemeGen

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

variable (P : CycPlan I d β) (rl : PathRule I d)

/-- The data of walk `k` (0-indexed) after the first `k` full world-lines. -/
noncomputable def gdat (k : ℕ) : CycData I d := P.start k (P.ideal rl k)

/-- The full path of walk `k`. -/
noncomputable def gpth (k : ℕ) : CycPath d := rl k (P.ideal rl k)

/-- The set whose infimum is the stopping length of walk `k`. -/
def gcand (k : ℕ) : Set ℝ≥0∞ :=
  {t | ∃ a : ℕ, 1 ≤ a ∧ (gpth P rl k).1.jt a < ⊤ ∧
      P.st k (P.hatRec k (P.ideal rl k) (gpth P rl k) a) = true ∧
        t = (gpth P rl k).1.jt a} ∪
    {t | ∃ a : ℕ, (gpth P rl k).1.jt a < ⊤ ∧
      t = (gpth P rl k).1.jt a + P.dl k (P.hatRec k (P.ideal rl k) (gpth P rl k) a) ∧
        t < (gpth P rl k).1.jt (a + 1)}

omit [Fact (0 < β)] in
/-- The world-line `E k`: the full path of walk `k`, cut at its stopping length. -/
theorem E_eq' (k : ℕ) : P.E rl k = (gdat P rl k, (gpth P rl k).cut (sInf (gcand P rl k))) := rfl

/-- The scheme's record is `k` full world-lines and an initial piece of walk `k`. -/
structure GAt (k : ℕ) (r : ℝ≥0) (ρ : CycRec I d) : Prop where
  rec_eq : ρ = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k)
    (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞))⟩
  allFin : P.AllFin rl k
  lt_K : (k : ℕ∞) < P.K
  pre : r = 0 ∨ ∀ c ∈ gcand P rl k, (r : ℝ≥0∞) < c

omit [MeasurableSpace I] in
theorem lastEntry_snoc (junk : CycEntry I d) {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) :
    CycRec.lastEntry junk (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) = e := by
  have h : ((k : ℕ∞) + 1).toNat = k + 1 := by
    rw [← Nat.cast_succ]; exact ENat.toNat_natCast _
  have h2 : CycRec.lastIdx (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) = k := by
    simp [CycRec.lastIdx, CycRec.num, h]
  unfold CycRec.lastEntry
  rw [h2]
  simp only [CycRec.coord, CycRec.nth, dite_eq_left (Nat.lt_succ_self k), Option.getD_some]
  exact Fin.snoc_last _ _ |>.trans rfl

omit [MeasurableSpace I] in
theorem restrictLast_snoc {k : ℕ} (g : CycRecN I d k) (e : CycEntry I d) (s : ℝ≥0) :
    CycRec.restrictLast s (Sum.inl ⟨k + 1, CycRec.snoc g e⟩ : CycRec I d) =
      Sum.inl ⟨k + 1, CycRec.snoc g (e.cut s)⟩ := by
  show (Sum.inl ⟨k + 1, Function.update (CycRec.snoc g e) (Fin.last k)
    (((CycRec.snoc g e) (Fin.last k)).cut s)⟩ : CycRec I d) = _
  unfold CycRec.snoc
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    simp

variable {P rl}
omit [Fact (0 < β)] in
theorem GAt.cur {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    CycScheme.cur P (ρ, b) = (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞)) := by
  unfold CycScheme.cur
  simp only
  rw [h.rec_eq]
  exact lastEntry_snoc _ _ _

theorem mem_CDisc_cut_iff (p : CPath (Fin d → ℤ)) {r s : ℝ≥0} (hs : s ≤ r) :
    s ∈ CDisc (p.cut (r : ℝ≥0∞)).fn ↔ s ∈ CDisc p.fn := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp [CDisc]
  have hs0 : 0 < s := pos_iff_ne_zero.mpr h0
  rw [(p.cut (r : ℝ≥0∞)).mem_CDisc_iff hs0, p.mem_CDisc_iff hs0,
    CPath.left_cut p _ hs0 (by exact_mod_cast hs), CPath.cut_fn]
  have : min (s : ℝ≥0∞) (r : ℝ≥0∞) = s := min_eq_left (by exact_mod_cast hs)
  rw [this]; simp

theorem cnt_cut_eq (p : CPath (Fin d → ℤ)) {r s : ℝ≥0} (hs : s ≤ r) :
    (p.cut (r : ℝ≥0∞)).cnt s = p.cnt s := by
  unfold CPath.cnt
  congr 1
  ext t
  simp only [mem_inter_iff, mem_Iic]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(mem_CDisc_cut_iff p (h2.trans hs)).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(mem_CDisc_cut_iff p (h2.trans hs)).2 h1, h2⟩

theorem jt_cut_eq (p : CPath (Fin d → ℤ)) {r : ℝ≥0} {a : ℕ} (ha : a ≤ p.cnt r) :
    (p.cut (r : ℝ≥0∞)).jt a = p.jt a := by
  have h1 : p.jt a ≤ (r : ℝ≥0∞) := (p.jt_le_iff a r).2 ha
  have h2 : (p.cut (r : ℝ≥0∞)).jt a ≤ (r : ℝ≥0∞) :=
    ((p.cut (r : ℝ≥0∞)).jt_le_iff a r).2 (by rwa [cnt_cut_eq p le_rfl])
  have key : ∀ s : ℝ≥0, s ≤ r → ((p.cut (r : ℝ≥0∞)).jt a ≤ s ↔ p.jt a ≤ s) := fun s hs => by
    rw [(p.cut _).jt_le_iff, p.jt_le_iff, cnt_cut_eq p hs]
  have hfin1 : p.jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  have hfin2 : (p.cut (r : ℝ≥0∞)).jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h2
  lift p.jt a to ℝ≥0 using hfin1 with x hx
  lift (p.cut (r : ℝ≥0∞)).jt a to ℝ≥0 using hfin2 with y hy
  have hxr : x ≤ r := by exact_mod_cast h1
  have hyr : y ≤ r := by exact_mod_cast h2
  have a1 := (key x hxr).2 le_rfl
  have a2 := (key y hyr).1 le_rfl
  exact le_antisymm a1 a2

omit [Fact (0 < β)] in
theorem GAt.len_cur {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    (CycScheme.cur P (ρ, b)).len = r := by
  rw [h.cur]; exact CPath.cut_len _ _

omit [Fact (0 < β)] in
theorem GAt.time {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    (CycScheme.cur P (ρ, b)).time = r := by
  unfold CycEntry.time; rw [h.len_cur]; simp

omit [Fact (0 < β)] in
theorem GAt.pos {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    (CycScheme.cur P (ρ, b)).pos = (gpth P rl k).1.fn r := by
  unfold CycEntry.pos
  rw [h.time]
  rw [h.cur]
  show ((gpth P rl k).1.cut (r : ℝ≥0∞)).fn r = _
  rw [CPath.cut_fn]
  simp

omit [Fact (0 < β)] in
theorem GAt.data {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    (CycScheme.cur P (ρ, b)).data = gdat P rl k := by
  rw [h.cur]; rfl

omit [Fact (0 < β)] in
theorem GAt.lastJump {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) (b : Bool) :
    (CycScheme.cur P (ρ, b)).lastJump = (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) := by
  unfold CycEntry.lastJump
  rw [h.time, h.cur]
  show ((gpth P rl k).1.cut (r : ℝ≥0∞)).jt (((gpth P rl k).1.cut (r : ℝ≥0∞)).cnt r) = _
  rw [cnt_cut_eq _ le_rfl, jt_cut_eq _ le_rfl]

omit [Fact (0 < β)] in
theorem GAt.dlOf_restrict {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) :
    P.dlOf (CycRec.restrictLast ((gpth P rl k).1.jt ((gpth P rl k).1.cnt r)).toNNReal ρ) =
      P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r)) := by
  have hle : (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) ≤ r := ((gpth P rl k).1.jt_le_iff _ r).2 le_rfl
  have hfin : (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  rw [h.rec_eq, restrictLast_snoc]
  show P.dl k _ = _
  unfold CycPlan.hatRec
  congr 1
  refine congrArg (CycRec.snoc _) (Prod.ext rfl (Subtype.ext ?_))
  change ((gpth P rl k).1.cut (r : ℝ≥0∞)).cut ((((gpth P rl k).1.jt ((gpth P rl k).1.cnt r)).toNNReal : ℝ≥0) : ℝ≥0∞) = (gpth P rl k).1.cut ((gpth P rl k).1.jt ((gpth P rl k).1.cnt r))
  rw [CPath.cut_cut _ (by rw [ENNReal.coe_toNNReal hfin]; exact hle), ENNReal.coe_toNNReal hfin]

omit [Fact (0 < β)] in
theorem GAt.hDl {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) :
    CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) =
      (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) +
        P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r)) - r := by
  unfold CycScheme.hDl
  rw [h.lastJump, h.time, h.dlOf_restrict]

end CycSchemeGen

end ElboimSly.Cyclic

end
