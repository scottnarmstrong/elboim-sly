/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenEvents
import Mathlib

/-!
# The driven construction: measurability, part 1 (lookups, events)

Well-definedness and measurability of the driven construction (b).  Generic measurability tools on a family of `CPath`s:
left values and counts at random times, and the first event after a random time.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {α : Type*} [MeasurableSpace α] {d : ℕ}

theorem CPath.isRegPath (p : CPath (Fin d → ℤ)) : IsRegPath p.fn := ⟨p.rc, p.fin⟩

/-- A regular path as a `CPath` of length `⊤`. -/
def mkCPath (f : ℝ≥0 → Fin d → ℤ) (hf : IsRegPath f) : CPath (Fin d → ℤ) :=
  ⟨⊤, f, hf.rc, hf.fin, fun _ _ h _ => absurd h (not_le.2 ENNReal.coe_lt_top)⟩

theorem measurable_index {m : α → ℕ} (hm : Measurable m) {β : Type*} [MeasurableSpace β]
    {F : ℕ → α → β} (hF : ∀ n, Measurable (F n)) : Measurable fun a => F (m a) a := by
  have : Measurable fun q : α × ℕ => F q.2 q.1 := measurable_from_prod_countable_left hF
  exact this.comp (measurable_id.prodMk hm)

theorem measurable_leftVal_at {Q : α → CPath (Fin d → ℤ)} (hQ : Measurable Q) {g : α → ℝ≥0}
    (hg : Measurable g) : Measurable fun a => leftVal (Q a).fn (g a) := by
  classical
  set c0 : Fin d → ℤ := leftVal (fun _ : ℝ≥0 => (0 : Fin d → ℤ)) 0 with hc0
  let h : ℕ → α → Fin d → ℤ := fun m a =>
    if g a = 0 then c0 else (Q a).fn (g a - (1 / 2) ^ m)
  have hm : ∀ m, Measurable (h m) := fun m =>
    Measurable.ite (measurableSet_eq_fun hg measurable_const) measurable_const
      (measurable_fn_at Q hQ _ (hg.sub_const _))
  refine measurable_of_tendsto_metrizable' atTop hm ?_
  rw [tendsto_pi_nhds]
  intro a
  by_cases h0 : g a = 0
  · have : leftVal (Q a).fn (g a) = c0 := by
      rw [h0, hc0]; exact leftVal_congr fun u hu => absurd hu (not_lt_zero)
    refine tendsto_nhds_of_eventually_eq (Eventually.of_forall fun m => ?_)
    show h m a = leftVal (Q a).fn (g a)
    rw [this]
    simp only [h, h0, ite_true]
  · have hs : 0 < g a := pos_iff_ne_zero.2 h0
    refine tendsto_nhds_of_eventually_eq ?_
    have hev := (Q a).isRegPath.eventually_leftVal hs
    have hT : Tendsto (fun m : ℕ => g a - (1 / 2 : ℝ≥0) ^ m) atTop (𝓝[<] g a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (fun m : ℕ => (1 / 2 : ℝ≥0) ^ m) atTop (𝓝 0) :=
          NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
            rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => g a) atTop (𝓝 (g a))).sub h1
      · exact Eventually.of_forall fun m => tsub_lt_self hs (by positivity)
    filter_upwards [hT.eventually hev] with m hm
    simp only [h, h0, ite_false]
    exact hm

theorem measurable_cnt_at {P : α → CPath (Fin d → ℤ)} (hP : Measurable P) {g : α → ℝ≥0}
    (hg : Measurable g) : Measurable fun a => (P a).cnt (g a) := by
  refine measurable_of_Ici fun m => ?_
  have : (fun a => (P a).cnt (g a)) ⁻¹' Ici m = {a | (P a).jt m ≤ (g a : ℝ≥0∞)} := by
    ext a; simp [CPath.jt_le_iff]
  rw [this]
  exact measurableSet_le ((CPath.measurable_jt m).comp hP) (measurable_coe_nnreal_ennreal.comp hg)

theorem cnt_lt_iff (p : CPath (Fin d → ℤ)) (u v : ℝ≥0) :
    p.cnt u < p.cnt v ↔ ∃ s ∈ CDisc p.fn, u < s ∧ s ≤ v := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hsub : CDisc p.fn ∩ Iic v ⊆ CDisc p.fn ∩ Iic u := by
      rintro s ⟨hs, hsv⟩
      refine ⟨hs, ?_⟩
      by_contra hus
      exact absurd (hne s hs (not_le.1 hus)) (not_lt.2 hsv)
    exact absurd (Set.ncard_le_ncard hsub (p.fin u)) (not_le.2 h)
  · rintro ⟨s, hs, hus, hsv⟩
    refine Set.ncard_lt_ncard ⟨inter_subset_inter_right _ (Iic_subset_Iic.2 (hus.le.trans hsv)), ?_⟩
      (p.fin v)
    intro hsub
    exact absurd (hsub ⟨hs, hsv⟩).2 (not_le.2 hus)

theorem nextEvent_le_iff {x : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0} (hx : IsRegPath x) (hβ : 0 < β)
    (r : ℝ≥0∞) (c : ℝ≥0) :
    nextEvent β x r ≤ c ↔ r < ⊤ ∧ ∃ t ∈ drivenEvents β x, r < (t : ℝ≥0∞) ∧ t ≤ c := by
  by_cases hr : r < ⊤
  · rcases nextEvent_spec hx hβ hr with ⟨h1, h2⟩ | ⟨m, hm, h1, h2, h3⟩
    · rw [h1]
      refine ⟨fun h => absurd h (by simp), fun ⟨_, t, ht, h, _⟩ => absurd h (h2 t ht)⟩
    · rw [h1]
      refine ⟨fun h => ⟨hr, m, hm, h2, by exact_mod_cast h⟩, fun ⟨_, t, ht, h, hc⟩ => ?_⟩
      exact_mod_cast (h3 t ht h).trans hc
  · rw [not_lt, top_le_iff] at hr
    subst hr
    rw [nextEvent_top]
    simp

theorem measurable_nextEvent {β : ℝ≥0} (hβ : 0 < β) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) {e : α → ℝ≥0∞} (he : Measurable e) :
    Measurable fun a => nextEvent β (X a).fn (e a) := by
  refine measurable_of_Iic fun c => ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  lift c to ℝ≥0 using hc
  have key : ∀ a, nextEvent β (X a).fn (e a) ≤ c ↔
      e a < ⊤ ∧ ∃ k : ℕ, (k : ℝ≥0) * β ≤ c ∧
        (X a).cnt ((e a).toNNReal - k * β) < (X a).cnt (c - k * β) := by
    intro a
    rw [nextEvent_le_iff (X a).isRegPath hβ]
    refine and_congr_right fun hr => ?_
    obtain ⟨r, hr'⟩ : ∃ r : ℝ≥0, e a = r := ⟨_, (ENNReal.coe_toNNReal hr.ne).symm⟩
    simp only [hr', ENNReal.toNNReal_coe]
    constructor
    · rintro ⟨t, ⟨s, hs, k, rfl⟩, h1, h2⟩
      have h1' : r < s + k * β := by exact_mod_cast h1
      have hkc : (k : ℝ≥0) * β ≤ c := (le_add_self : (k : ℝ≥0) * β ≤ s + k * β).trans h2
      refine ⟨k, hkc, (cnt_lt_iff _ _ _).2 ⟨s, hs, ?_, le_tsub_of_add_le_right h2⟩⟩
      by_cases hk : (k : ℝ≥0) * β ≤ r
      · exact (tsub_lt_iff_right hk).2 h1'
      · rw [not_le] at hk
        rw [tsub_eq_zero_of_le hk.le]; exact hs.1
    · rintro ⟨k, hkc, h⟩
      obtain ⟨s, hs, h1, h2⟩ := (cnt_lt_iff _ _ _).1 h
      refine ⟨s + k * β, ⟨s, hs, k, rfl⟩, ?_, ?_⟩
      · exact_mod_cast lt_add_of_tsub_lt_right h1
      · exact (le_tsub_iff_right hkc).1 h2
  have hset : (fun a => nextEvent β (X a).fn (e a)) ⁻¹' Iic (c : ℝ≥0∞) =
      {a | e a < ⊤} ∩ ⋃ k : ℕ, {a | (k : ℝ≥0) * β ≤ c ∧
        (X a).cnt ((e a).toNNReal - k * β) < (X a).cnt (c - k * β)} := by
    ext a
    simp only [mem_preimage, mem_Iic, key, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
  rw [hset]
  refine (measurableSet_lt he measurable_const).inter (MeasurableSet.iUnion fun k => ?_)
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  exact measurableSet_lt
    (measurable_cnt_at hX ((ENNReal.measurable_toNNReal.comp he).sub_const _))
    (measurable_cnt_at hX measurable_const)

/-! ### The rule value at a random time -/

section Rule

variable {β : ℝ≥0} {X Q : α → CPath (Fin d → ℤ)} {g : α → ℝ≥0}

theorem measurable_fn_at' (hQ : Measurable Q) {h : α → ℝ≥0} (hh : Measurable h) :
    Measurable fun a => (Q a).fn (h a) := measurable_fn_at Q hQ h hh

theorem measurableSet_mem_CDisc (hQ : Measurable Q) {h : α → ℝ≥0} (hh : Measurable h) :
    MeasurableSet {a | h a ∈ CDisc (Q a).fn} := by
  have : {a | h a ∈ CDisc (Q a).fn} = {a | 0 < h a} ∩ {a | leftVal (Q a).fn (h a) ≠ (Q a).fn (h a)} := by
    ext a
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact (Q a).isRegPath.mem_CDisc_iff
  rw [this]
  exact (measurableSet_lt measurable_const hh).inter
    (measurableSet_eq_fun (measurable_leftVal_at hQ hh) (measurable_fn_at' hQ hh)).compl

theorem measurableSet_isDelayIdx (hg : Measurable g) (β : ℝ≥0) (k : ℕ) :
    MeasurableSet {a | IsDelayIdx β (g a) k} := by
  by_cases hk : 1 ≤ k
  · have : {a | IsDelayIdx β (g a) k} = {a | (k : ℝ≥0) * β ≤ g a} := by
      ext a; simp [IsDelayIdx, hk]
    rw [this]
    exact measurableSet_le measurable_const hg
  · have : {a | IsDelayIdx β (g a) k} = ∅ := by
      ext a; simp [IsDelayIdx, hk]
    rw [this]; exact MeasurableSet.empty

theorem measurableSet_forcedAt (hQ : Measurable Q) (hg : Measurable g) (β : ℝ≥0) (k : ℕ) :
    MeasurableSet {a | ForcedAt β (Q a).fn (g a) k} := by
  have : {a | ForcedAt β (Q a).fn (g a) k} = {a | IsDelayIdx β (g a) k} ∩
      ({a | g a - k * β ∈ CDisc (Q a).fn} ∩
        {a | (Q a).fn (g a - k * β) = leftVal (Q a).fn (g a)}) := rfl
  rw [this]
  exact (measurableSet_isDelayIdx hg β k).inter
    ((measurableSet_mem_CDisc hQ (hg.sub_const _)).inter
      (measurableSet_eq_fun (measurable_fn_at' hQ (hg.sub_const _))
        (measurable_leftVal_at hQ hg)))

theorem nat_sInf_eq_iff (S : Set ℕ) (n : ℕ) :
    sInf S = n ↔ (n ∈ S ∧ ∀ k < n, k ∉ S) ∨ (n = 0 ∧ ∀ k, k ∉ S) := by
  constructor
  · intro h
    by_cases hne : S.Nonempty
    · left
      refine ⟨h ▸ Nat.sInf_mem hne, fun k hk hkS => ?_⟩
      exact absurd (Nat.sInf_le hkS) (by omega)
    · right
      rw [Set.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp at h
      exact ⟨h.symm, by simp⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
    · refine le_antisymm (Nat.sInf_le h1) ?_
      by_contra hlt
      exact h2 _ (not_le.1 hlt) (Nat.sInf_mem ⟨n, h1⟩)
    · have : S = ∅ := Set.eq_empty_iff_forall_notMem.2 h2
      simp [this]

theorem measurable_forcedIdx (hQ : Measurable Q) (hg : Measurable g) (β : ℝ≥0) :
    Measurable fun a => sInf {k | ForcedAt β (Q a).fn (g a) k} := by
  refine measurable_to_countable' fun n => ?_
  have : (fun a => sInf {k | ForcedAt β (Q a).fn (g a) k}) ⁻¹' {n} =
      ({a | ForcedAt β (Q a).fn (g a) n} ∩ ⋂ k, ⋂ (_ : k < n), {a | ForcedAt β (Q a).fn (g a) k}ᶜ) ∪
      ({a | n = 0} ∩ ⋂ k, {a | ForcedAt β (Q a).fn (g a) k}ᶜ) := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, nat_sInf_eq_iff, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, mem_compl_iff]
  rw [this]
  refine MeasurableSet.union
    ((measurableSet_forcedAt hQ hg β n).inter (MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => (measurableSet_forcedAt hQ hg β k).compl))
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun k =>
      (measurableSet_forcedAt hQ hg β k).compl))

theorem measurableSet_takenAt (hX : Measurable X) (hQ : Measurable Q) (hg : Measurable g)
    (β : ℝ≥0) : MeasurableSet {a | TakenAt β (X a).fn (Q a).fn (g a)} := by
  have : {a | TakenAt β (X a).fn (Q a).fn (g a)} = ⋂ k : ℕ,
      ({a | IsDelayIdx β (g a) k}ᶜ ∪ {a | leftVal (Q a).fn (g a) +
        ((X a).fn (g a) - leftVal (X a).fn (g a)) ≠ (Q a).fn (g a - k * β)}) := by
    ext a
    simp only [TakenAt, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [this]
  refine MeasurableSet.iInter fun k => (measurableSet_isDelayIdx hg β k).compl.union ?_
  refine (measurableSet_eq_fun ?_ (measurable_fn_at' hQ (hg.sub_const _))).compl
  exact (measurable_leftVal_at hQ hg).add ((measurable_fn_at' hX hg).sub (measurable_leftVal_at hX hg))

theorem measurable_drivenRuleVal (hX : Measurable X) (hQ : Measurable Q) (hg : Measurable g)
    (β : ℝ≥0) : Measurable fun a => drivenRuleVal β (X a).fn (Q a).fn (g a) := by
  classical
  have hforced : MeasurableSet {a | ∃ k, ForcedAt β (Q a).fn (g a) k} := by
    have : {a | ∃ k, ForcedAt β (Q a).fn (g a) k} = ⋃ k, {a | ForcedAt β (Q a).fn (g a) k} := by
      ext a; simp
    rw [this]
    exact MeasurableSet.iUnion fun k => measurableSet_forcedAt hQ hg β k
  have hL := measurable_leftVal_at hQ hg
  unfold drivenRuleVal
  refine Measurable.ite hforced ?_ (Measurable.ite (measurableSet_mem_CDisc hX hg)
    (Measurable.ite (measurableSet_takenAt hX hQ hg β)
      (hL.add ((measurable_fn_at' hX hg).sub (measurable_leftVal_at hX hg))) hL) hL)
  exact measurable_index (measurable_forcedIdx hQ hg β)
    (F := fun n a => leftVal (Q a).fn (g a - n * β))
    (fun n => measurable_leftVal_at hQ (hg.sub_const _))

end Rule

/-! ### Stages, the walk, the closing time -/

theorem isRegPath_drivenStage (β : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) :
    ∀ n, IsRegPath (drivenStage β x n)
  | 0 => ⟨fun _ => Eventually.of_forall fun _ => rfl, fun _ =>
      Set.Finite.subset Set.finite_empty fun _ hs => absurd (Eventually.of_forall fun _ => rfl) hs.1.2⟩
  | n + 1 => by
    classical
    have ih := isRegPath_drivenStage β x n
    set f := drivenStage β x n with hf
    set e := drivenTimes β x (n + 1) with he
    set r := drivenRuleVal β x f e.toNNReal with hr
    have hg : drivenStage β x (n + 1) = fun s : ℝ≥0 => if (s : ℝ≥0∞) < e then f s else r := rfl
    rw [hg]
    refine ⟨fun s => ?_, fun T => ?_⟩
    · by_cases hs : (s : ℝ≥0∞) < e
      · have hU : {u : ℝ≥0 | (u : ℝ≥0∞) < e} ∈ 𝓝 s :=
          (isOpen_Iio.preimage ENNReal.continuous_coe).mem_nhds hs
        filter_upwards [mem_nhdsWithin_of_mem_nhds hU, ih.rc s] with u hu hu2
        have hu' : (u : ℝ≥0∞) < e := hu
        simp only [hu', hs, ite_true, hu2]
      · filter_upwards [self_mem_nhdsWithin (s := Ici s)] with u hu
        have : ¬ (u : ℝ≥0∞) < e := fun h =>
          hs (lt_of_le_of_lt (by exact_mod_cast (hu : s ≤ u)) h)
        simp only [this, hs, ite_false]
    · refine ((ih.fin T).union (Set.finite_singleton e.toNNReal)).subset ?_
      rintro s ⟨hs, hsT⟩
      by_cases hse : (s : ℝ≥0∞) < e
      · left
        refine ⟨(mem_CDisc_congr (f := fun s : ℝ≥0 => if (s : ℝ≥0∞) < e then f s else r) (g := f)
          fun u hu => ?_).1 hs, hsT⟩
        have : (u : ℝ≥0∞) < e := lt_of_le_of_lt (by exact_mod_cast hu) hse
        simp only [this, ite_true]
      · right
        by_contra hne
        have he_top : e ≠ ⊤ := fun h => hse (h ▸ ENNReal.coe_lt_top)
        obtain ⟨e', he'⟩ : ∃ e' : ℝ≥0, e = e' := ⟨_, (ENNReal.coe_toNNReal he_top).symm⟩
        have hle : e' ≤ s := by rw [he'] at hse; exact_mod_cast not_lt.1 hse
        have hlt : e' < s := lt_of_le_of_ne hle (fun h => hne (by simp [he', h]))
        refine hs.2 ?_
        filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
        have h1 : ¬ (u : ℝ≥0∞) < e := by
          rw [he']; exact not_lt.2 (by exact_mod_cast hu.1.le)
        simp only [h1, hse, ite_false]

theorem measurable_drivenTimes {β : ℝ≥0} (hβ : 0 < β) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) : ∀ n, Measurable fun a => drivenTimes β (X a).fn n
  | 0 => measurable_const
  | n + 1 => measurable_nextEvent hβ hX (measurable_drivenTimes hβ hX n)

/-- The stages as `CPath`s. -/
noncomputable def stageCPath (β : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n : ℕ) : CPath (Fin d → ℤ) :=
  mkCPath (drivenStage β x n) (isRegPath_drivenStage β x n)

theorem measurable_stageCPath {β : ℝ≥0} (hβ : 0 < β) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) : ∀ n, Measurable fun a => stageCPath β (X a).fn n
  | 0 => by
    rw [CPath.measurable_iff]
    exact ⟨measurable_const, fun s => measurable_const⟩
  | n + 1 => by
    classical
    have ih := measurable_stageCPath hβ hX n
    rw [CPath.measurable_iff]
    refine ⟨measurable_const, fun s => ?_⟩
    have hT := measurable_drivenTimes hβ hX (n + 1)
    have hfun : (fun a => (stageCPath β (X a).fn (n + 1)).fn s) = fun a =>
        if (s : ℝ≥0∞) < drivenTimes β (X a).fn (n + 1) then (stageCPath β (X a).fn n).fn s
        else drivenRuleVal β (X a).fn (stageCPath β (X a).fn n).fn
          (drivenTimes β (X a).fn (n + 1)).toNNReal := rfl
    rw [hfun]
    exact Measurable.ite (measurableSet_lt measurable_const hT)
      (((CPath.measurable_iff _).1 ih).2 s)
      (measurable_drivenRuleVal hX ih (ENNReal.measurable_toNNReal.comp hT) β)

theorem measurable_drivenWalk_at {β : ℝ≥0} (hβ : 0 < β) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) {g : α → ℝ≥0} (hg : Measurable g) :
    Measurable fun a => drivenWalk β (X a).fn (g a) := by
  classical
  have hex : ∀ a, ∃ n, (g a : ℝ≥0∞) < drivenTimes β (X a).fn (n + 1) :=
    fun a => exists_times_gt (X a).isRegPath hβ (g a)
  have hfun : (fun a => drivenWalk β (X a).fn (g a)) =
      fun a => (stageCPath β (X a).fn (Nat.find (hex a))).fn (g a) := by
    funext a
    unfold drivenWalk
    rw [dite_eq_left (hex a)]
    rfl
  rw [hfun]
  refine Measurable.find (p := fun n a => (g a : ℝ≥0∞) < drivenTimes β (X a).fn (n + 1))
    (f := fun n a => (stageCPath β (X a).fn n).fn (g a)) (fun n =>
      measurable_fn_at _ (measurable_stageCPath hβ hX n) g hg) (fun n => ?_) hex
  exact measurableSet_lt (measurable_coe_nnreal_ennreal.comp hg)
    (measurable_drivenTimes hβ hX (n + 1))

/-- Well-definedness and measurability of the driven construction (b): `w^x(t)` is a measurable function of the path. -/
theorem measurable_drivenWalk {β : ℝ≥0} (hβ : 0 < β) (t : ℝ≥0) :
    Measurable fun p : CPath (Fin d → ℤ) => drivenWalk β p.fn t :=
  measurable_drivenWalk_at (X := id) hβ measurable_id measurable_const

theorem pathTreg_le_iff (β : ℝ≥0) (w : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    pathTreg β w ≤ t ↔ ∃ k : ℕ, 1 ≤ k ∧ w (k * β) = 0 ∧ (k : ℝ≥0) * β ≤ t := by
  classical
  constructor
  · intro h
    by_cases hK : ∃ k : ℕ, 1 ≤ k ∧ w (k * β) = 0
    · refine ⟨Nat.find hK, (Nat.find_spec hK).1, (Nat.find_spec hK).2, ?_⟩
      have h1 : (((Nat.find hK : ℝ≥0) * β : ℝ≥0) : ℝ≥0∞) ≤ pathTreg β w :=
        le_iInf fun k => by
          have : Nat.find hK ≤ k.1 := Nat.find_min' hK k.2
          exact_mod_cast mul_le_mul_left (by exact_mod_cast this) β
      exact_mod_cast h1.trans h
    · exfalso
      have : IsEmpty {k : ℕ // 1 ≤ k ∧ w ((k : ℝ≥0) * β) = 0} := ⟨fun k => hK ⟨k.1, k.2⟩⟩
      unfold pathTreg at h
      rw [iInf_of_empty] at h
      exact absurd h (by simp)
  · rintro ⟨k, hk, hw, hkt⟩
    unfold pathTreg
    exact (iInf_le _ ⟨k, hk, hw⟩).trans (by exact_mod_cast hkt)

theorem measurableSet_drivenTreg_le {β : ℝ≥0} (hβ : 0 < β) (t : ℝ≥0) :
    MeasurableSet {p : CPath (Fin d → ℤ) | drivenTreg β p.fn ≤ t} := by
  have : {p : CPath (Fin d → ℤ) | drivenTreg β p.fn ≤ t} =
      ⋃ k : ℕ, {p | 1 ≤ k ∧ (k : ℝ≥0) * β ≤ t ∧ drivenWalk β p.fn (k * β) = 0} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, drivenTreg, pathTreg_le_iff]
    constructor
    · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, h1, h3, h2⟩
    · rintro ⟨k, h1, h3, h2⟩; exact ⟨k, h1, h2, h3⟩
  rw [this]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases h : 1 ≤ k ∧ (k : ℝ≥0) * β ≤ t
  · have : {p : CPath (Fin d → ℤ) | 1 ≤ k ∧ (k : ℝ≥0) * β ≤ t ∧ drivenWalk β p.fn (k * β) = 0} =
        {p | drivenWalk β p.fn (k * β) = 0} := by
      ext p; simp [h]
    rw [this]
    exact measurableSet_eq_fun (measurable_drivenWalk hβ _) measurable_const
  · have : {p : CPath (Fin d → ℤ) | 1 ≤ k ∧ (k : ℝ≥0) * β ≤ t ∧ drivenWalk β p.fn (k * β) = 0} =
        ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _⟩; exact h ⟨h1, h2⟩
    rw [this]; exact MeasurableSet.empty

/-- Well-definedness and measurability of the driven construction (b): `treg^x` is a measurable function of the path. -/
theorem measurable_drivenTreg {β : ℝ≥0} (hβ : 0 < β) :
    Measurable fun p : CPath (Fin d → ℤ) => drivenTreg β p.fn := by
  refine measurable_of_Iic fun c => ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  lift c to ℝ≥0 using hc
  exact measurableSet_drivenTreg_le hβ c

/-- Well-definedness and measurability of the driven construction (b): `w^x(t ∧ treg^x)` is a measurable function of the path. -/
theorem measurable_drivenStopped {β : ℝ≥0} (hβ : 0 < β) (t : ℝ≥0) :
    Measurable fun p : CPath (Fin d → ℤ) => drivenStopped β p.fn t :=
  measurable_drivenWalk_at (X := id) hβ measurable_id
    (ENNReal.measurable_toNNReal.comp (measurable_const.min (measurable_drivenTreg hβ)))

end ElboimSly.Cyclic

end
