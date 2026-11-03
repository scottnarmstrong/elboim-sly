/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenConstruct
public import Mathlib

/-!
# Solutions up to a time `T`

Basic properties of world-lines (c). `Sol T p`: `p` satisfies the rules on `(0, T]`, has all jumps in `E`
and is constant after `T`. By induction on `|E ∩ (0, T]|` such a `p` exists for every `T`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {R Q : Set (I × RingSpace d β)} {δ : CycData I d} {X : CPath (Fin d → ℤ)} {a : ℝ≥0}
  {E : Set ℝ≥0}

/-- A solution up to time `T`. -/
def DrvSol (β : ℝ) [Fact (0 < β)] (R Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) (E : Set ℝ≥0) (T : ℝ≥0) (p : CPath (Fin d → ℤ)) : Prop :=
  p.len = ⊤ ∧ p.fn 0 = δ.start ∧ (∀ s ∈ CDisc p.fn, s ∈ E) ∧ (∀ r, T ≤ r → p.fn r = p.fn T) ∧
    ∀ r, 0 < r → r ≤ T → DrvRule β R Q δ X a p r

omit [MeasurableSpace I] in
theorem exists_drvSol (hE : EvtSet β Q δ X a E) :
    ∀ n : ℕ, ∀ T : ℝ≥0, (E ∩ Iic T).ncard = n → ∃ p, DrvSol β R Q δ X a E T p := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn
  by_cases hF : (E ∩ Iic T).Nonempty
  swap
  · -- no events: the constant path
    rw [Set.not_nonempty_iff_eq_empty] at hF
    let p : CPath (Fin d → ℤ) := (CycPath.const δ.start).1
    have hpfn : ∀ r, p.fn r = δ.start := fun _ => rfl
    have hdisc : ∀ s ∈ CDisc p.fn, s ∈ E := fun s hs =>
      absurd (Filter.Eventually.of_forall fun u => rfl) hs.2
    refine ⟨p, rfl, rfl, hdisc, fun r _ => rfl, fun r hr hrT => ?_⟩
    have hrE : r ∉ E := fun h => by
      have : r ∈ E ∩ Iic T := ⟨h, hrT⟩
      rw [hF] at this; exact this
    refine hE.rule_stay hdisc hr hrE ?_
    rw [hpfn]
    exact (p.left_eq_of_eventually hr (z := δ.start)
      (Filter.Eventually.of_forall fun u => rfl)).symm
  · have hfin := hE.fin T
    set e := hfin.toFinset.max' (by simpa using hF) with he_def
    have heF : e ∈ E ∩ Iic T := by
      have := hfin.toFinset.max'_mem (by simpa using hF)
      exact (Set.Finite.mem_toFinset hfin).1 this
    have hmax : ∀ x ∈ E, x ≤ T → x ≤ e := fun x hx hxT =>
      hfin.toFinset.le_max' x (by simpa using ⟨hx, hxT⟩)
    have he0 : 0 < e := hE.pos e heF.1
    obtain ⟨t, hte, hgap⟩ := exists_gap_of_finite (hE.fin e) he0
    have hset : E ∩ Iic t = (E ∩ Iic T) \ {e} := by
      ext x
      simp only [mem_inter_iff, mem_Iic, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hxt⟩
        exact ⟨⟨hx, hxt.trans (hte.le.trans heF.2)⟩, (hxt.trans_lt hte).ne⟩
      · rintro ⟨⟨hx, hxT⟩, hxe⟩
        refine ⟨hx, ?_⟩
        by_contra hxt
        push Not at hxt
        exact hgap x hx hxt ((hmax x hx hxT).lt_of_ne hxe)
    have hpos : 0 < n := by rw [← hn]; exact (Set.ncard_pos hfin).2 hF
    obtain ⟨p0, h0len, h0start, h0disc, h0const, h0rule⟩ := ih (n - 1) (by omega) t (by
      rw [hset, ncard_sdiff_singleton_of_mem heF, hn])
    obtain ⟨v, hv⟩ := RuleFn.exists_val δ (δ.clock β e) (p0.left e)
      (R ∪ drvZown β δ p0 e) (Q ∪ drvQown β δ p0 e) (X.left (a + e) ≠ X.fn (a + e))
      (X.fn (a + e) - X.left (a + e))
    set q := p0.extendAt e v with hq
    have hq_lt : ∀ r, r < e → q.fn r = p0.fn r := fun r h => CPath.extendAt_fn_lt p0 e v h
    have hq_ge : ∀ r, e ≤ r → q.fn r = v := fun r h => CPath.extendAt_fn_ge p0 e v h
    have hql_le : ∀ r, 0 < r → r ≤ e → q.left r = p0.left r := fun r hr hle =>
      CPath.left_congr q p0 hr fun u hu => hq_lt u (hu.trans_le hle)
    have hql_gt : ∀ r, e < r → q.left r = v := fun r h => by
      refine q.left_eq_of_eventually (he0.trans h) ?_
      have h1 : ∀ᶠ u in 𝓝[<] r, e < u :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds h)
      filter_upwards [h1] with u hu using hq_ge u hu.le
    have hqdisc : ∀ s ∈ CDisc q.fn, s ∈ E := fun s hs => by
      rcases CPath.CDisc_extendAt p0 e v hs with h | ⟨_, h⟩
      · rw [h]; exact heF.1
      · exact h0disc s h
    refine ⟨q, rfl, ?_, hqdisc, fun r hr => ?_, fun r hr hrT => ?_⟩
    · rw [hq_lt 0 he0]; exact h0start
    · rw [hq_ge r (heF.2.trans hr), hq_ge T heF.2]
    · rcases le_or_gt r t with hrt | htr
      · have := h0rule r hr hrt
        exact this.congr hr fun x hx => (hq_lt x ((hx.trans hrt).trans_lt hte)).symm
      · rcases lt_trichotomy r e with hre | hre | hre
        · have hrE : r ∉ E := fun h => hgap r h htr hre
          refine hE.rule_stay hqdisc hr hrE ?_
          rw [hq_lt r hre, hql_le r hr hre.le]
          symm
          refine p0.left_eq_of_eventually hr ?_
          filter_upwards [Ioo_mem_nhdsLT htr] with u hu
          rw [h0const u hu.1.le, h0const r htr.le]
        · rw [hre]
          unfold DrvRule
          have hZ : drvZown β δ q e = drvZown β δ p0 e := by
            ext x
            simp only [drvZown, mem_ofPred_eq]
            refine exists_congr fun r' => and_congr_right fun h0 =>
              and_congr_right fun h1 => ?_
            rw [hql_le r' h0 h1.le]
          have hQ : drvQown β δ q e = drvQown β δ p0 e := by
            ext x
            simp only [drvQown, mem_ofPred_eq]
            refine exists_congr fun r' => and_congr_right fun h0 =>
              and_congr_right fun h1 => ?_
            rw [hql_le r' h0 h1.le, hq_lt r' h1]
          rw [hZ, hQ, hql_le e he0 le_rfl, hq_ge e le_rfl]
          exact hv
        · have hrE : r ∉ E := fun h => absurd (hmax r h hrT) (not_le.mpr hre)
          refine hE.rule_stay hqdisc hr hrE ?_
          rw [hq_ge r hre.le, hql_gt r hre]

omit [MeasurableSpace I] in
/-- Basic properties of world-lines (c), existence: for an event set `E`, a driven path exists and all
its jumps lie in `E`. -/
theorem exists_driven_of_evtSet (hE : EvtSet β Q δ X a E) :
    ∃ p : CPath (Fin d → ℤ), IsDriven β R Q δ X a p ∧ ∀ s ∈ CDisc p.fn, s ∈ E := by
  classical
  have hex : ∀ T : ℝ≥0, ∃ p, DrvSol β R Q δ X a E T p := fun T => exists_drvSol hE _ T rfl
  choose P hP using hex
  have hagree : ∀ T r : ℝ≥0, r ≤ T → (P r).fn r = (P T).fn r := fun T r hrT =>
    drv_eq_of_le (T := r) ((hP r).2.1.trans (hP T).2.1.symm)
      (fun x hx hxr => (hP r).2.2.2.2 x hx hxr)
      (fun x hx hxr => (hP T).2.2.2.2 x hx (hxr.trans hrT)) r le_rfl
  let pfn : ℝ≥0 → (Fin d → ℤ) := fun r => (P r).fn r
  have hpe : ∀ T r : ℝ≥0, r ≤ T → pfn r = (P T).fn r := hagree
  have hdisc_sub : ∀ T s : ℝ≥0, s ≤ T → s ∈ CDisc pfn → s ∈ CDisc (P (T + 1)).fn := by
    rintro T s hsT ⟨hs0, hs1⟩
    refine ⟨hs0, fun hev => hs1 ?_⟩
    filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
    have hu1 : u ≤ T + 1 := (le_of_lt (Set.mem_Iio.mp hus)).trans (hsT.trans le_self_add)
    rw [hpe (T + 1) u hu1, hpe (T + 1) s (hsT.trans le_self_add)]
    exact hu
  let pc : CPath (Fin d → ℤ) :=
    ⟨⊤, pfn, fun s => by
      have h1 : ∀ᶠ u in 𝓝[≥] s, u < s + 1 :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (lt_add_of_pos_right s one_pos))
      filter_upwards [(P (s + 1)).rc s, h1] with u hu hu'
      rw [hpe (s + 1) u hu'.le, hpe (s + 1) s le_self_add]; exact hu,
      fun T => ((P (T + 1)).fin T).subset fun s hs => ⟨hdisc_sub T s hs.2 hs.1, hs.2⟩,
      fun s s' h _ => absurd h (by simp)⟩
  have hpc : ∀ T r : ℝ≥0, r ≤ T → pc.fn r = (P T).fn r := hpe
  have hdisc : ∀ s ∈ CDisc pc.fn, s ∈ E := fun s hs =>
    (hP (s + 1)).2.2.1 s (hdisc_sub s s le_rfl hs)
  refine ⟨pc, ⟨rfl, ?_, fun r hr => ?_⟩, hdisc⟩
  · rw [hpc 0 0 le_rfl]; exact (hP 0).2.1
  · exact ((hP r).2.2.2.2 r hr le_rfl).congr hr fun x hx => (hagree r x hx).symm

end ElboimSly.Cyclic

end
