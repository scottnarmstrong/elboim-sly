/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Escape.C56MeasGen
public import ElboimSly.Paper.Escape.Phases
public import ElboimSly.Paper.Avoid.Hyp
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.Brownian.Tube
public import Mathlib

/-!
# The tube event for the walk, from the (H4) coupling

ES22 Claim 5.6, event `E^a`, using the induction hypothesis at arbitrary times (d) and tube lemma.

`tubeRat x f R R' T` is the set of `CPath`s `p` with `‖x + p(q) - f(q)‖ ≤ R` for all rational
`q ∈ [0, T]` and at `T`, and `≤ R'` for rational `q ∈ [T/2, T]` and at `T`.  For a path with
finitely many jumps it implies the same conditions at all real times
(`tubeRat_real`, from `forallBetween`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The rational-time tube condition. -/
def tubeRat (x : Fin (k + 2) → ℤ) (f : ℝ → Fin (k + 2) → ℝ) (R R' T : ℝ) :
    Set (CPath (Fin (k + 2) → ℤ)) :=
  {p | (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T →
      ‖escCast (x + p.fn (q : ℝ).toNNReal) - f q‖ ≤ R) ∧
    ‖escCast (x + p.fn T.toNNReal) - f T‖ ≤ R ∧
    (∀ q : ℚ, T / 2 ≤ (q : ℝ) → (q : ℝ) ≤ T → ‖escCast (x + p.fn (q : ℝ).toNNReal) - f q‖ ≤ R') ∧
    ‖escCast (x + p.fn T.toNNReal) - f T‖ ≤ R'}

/-- For a path with finitely many jumps and a continuous `f`, the rational tube condition gives
the tube condition at all real times. -/
theorem tubeRat_real {x : Fin (k + 2) → ℤ} {f : ℝ → Fin (k + 2) → ℝ} (hf : Continuous f)
    {R R' T : ℝ} {p : CPath (Fin (k + 2) → ℤ)} (hp : p ∈ tubeRat x f R R' T) :
    (∀ s : ℝ, 0 ≤ s → s ≤ T → ‖escCast (x + p.fn s.toNNReal) - f s‖ ≤ R) ∧
    (∀ s : ℝ, T / 2 ≤ s → s ≤ T → ‖escCast (x + p.fn s.toNNReal) - f s‖ ≤ R') := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hcl : ∀ (r : ℝ) (y : Fin (k + 2) → ℤ), IsClosed {s : ℝ | ‖escCast (x + y) - f s‖ ≤ r} :=
    fun r y => isClosed_le (by fun_prop) continuous_const
  have key : ∀ (r a : ℝ), (∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ T →
      ‖escCast (x + p.fn (q : ℝ).toNNReal) - f q‖ ≤ r) →
      (a ≤ T → ‖escCast (x + p.fn T.toNNReal) - f T‖ ≤ r) →
      ∀ s : ℝ, a ≤ s → s ≤ T → ‖escCast (x + p.fn s.toNNReal) - f s‖ ≤ r := by
    intro r a hq he
    have hfb := mem_forallBetween_of_rat (ψ := fun y s => ‖escCast (x + y) - f s‖ ≤ r)
      (fun y => hcl r y) p a T hq he
    exact hfb
  refine ⟨?_, ?_⟩
  · intro s hs0 hs
    exact key R 0 (fun q hq0 hqT => h1 q hq0 hqT) (fun _ => h2) s hs0 hs
  · intro s hs0 hs
    exact key R' (T / 2) (fun q hq0 hqT => h3 q hq0 hqT) (fun _ => h4) s hs0 hs

theorem escCast_add (x y : Fin (k + 2) → ℤ) : escCast (x + y) = escCast x + escCast y := by
  ext c; simp [escCast]

section Walk

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The point of `[0, T]` at (the clipped) time `r`. -/
def ptT (T0 : ℝ≥0) (r : ℝ) : Set.Icc (0 : ℝ≥0) T0 := ⟨min r.toNNReal T0, bot_le, min_le_right _ _⟩

/-- The cylinder on `[0,T] → ℤ^d` corresponding to `tubeRat`. -/
def tubeCyl (T0 : ℝ≥0) (x : Fin (k + 2) → ℤ) (f : ℝ → Fin (k + 2) → ℝ) (R R' : ℝ) :
    Set (Set.Icc (0 : ℝ≥0) T0 → Fin (k + 2) → ℤ) :=
  {w | (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T0 → ‖escCast (x + w (ptT T0 q)) - f q‖ ≤ R) ∧
    ‖escCast (x + w (ptT T0 T0)) - f T0‖ ≤ R ∧
    (∀ q : ℚ, (T0 : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) ≤ T0 → ‖escCast (x + w (ptT T0 q)) - f q‖ ≤ R') ∧
    ‖escCast (x + w (ptT T0 T0)) - f T0‖ ≤ R'}

theorem measurableSet_tubeCyl (T0 : ℝ≥0) (x : Fin (k + 2) → ℤ) (f : ℝ → Fin (k + 2) → ℝ)
    (R R' : ℝ) : MeasurableSet (tubeCyl T0 x f R R') := by
  have hm : ∀ (r s ρ : ℝ), MeasurableSet
      {w : Set.Icc (0 : ℝ≥0) T0 → Fin (k + 2) → ℤ | ‖escCast (x + w (ptT T0 r)) - f s‖ ≤ ρ} := by
    intro r s ρ
    exact (measurable_pi_apply (X := fun _ : Set.Icc (0 : ℝ≥0) T0 => Fin (k + 2) → ℤ)
      (ptT T0 r)) (Set.to_countable
      {y : Fin (k + 2) → ℤ | ‖escCast (x + y) - f s‖ ≤ ρ}).measurableSet
  have hq : ∀ (a b : Prop) (r s ρ : ℝ), MeasurableSet
      {w : Set.Icc (0 : ℝ≥0) T0 → Fin (k + 2) → ℤ |
        a → b → ‖escCast (x + w (ptT T0 r)) - f s‖ ≤ ρ} := by
    intro a b r s ρ
    by_cases ha : a
    · by_cases hb : b
      · simp only [ha, hb, forall_true_left]; exact hm _ _ _
      · simp [hb]
    · simp [ha]
  have e : tubeCyl T0 x f R R' =
      (⋂ q : ℚ, {w | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T0 →
        ‖escCast (x + w (ptT T0 q)) - f q‖ ≤ R}) ∩
      ({w | ‖escCast (x + w (ptT T0 T0)) - f T0‖ ≤ R} ∩
      ((⋂ q : ℚ, {w | (T0 : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) ≤ T0 →
        ‖escCast (x + w (ptT T0 q)) - f q‖ ≤ R'}) ∩
      {w | ‖escCast (x + w (ptT T0 T0)) - f T0‖ ≤ R'})) := by
    ext w
    simp only [tubeCyl, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  exact MeasurableSet.inter (MeasurableSet.iInter fun q => hq _ _ _ _ _)
    (MeasurableSet.inter (hm _ _ _) (MeasurableSet.inter
      (MeasurableSet.iInter fun q => hq _ _ _ _ _) (hm _ _ _)))

theorem ptT_val {T0 : ℝ≥0} {r : ℝ} (_h0 : 0 ≤ r) (h1 : r ≤ T0) :
    ((ptT T0 r : Set.Icc (0 : ℝ≥0) T0) : ℝ≥0) = r.toNNReal := by
  show min r.toNNReal T0 = r.toNNReal
  exact min_eq_left (Real.toNNReal_le_iff_le_coe.2 h1)

/-- The cylinder is the tube condition for the path read on `[0, T]`. -/
theorem mem_tubeCyl_iff {T0 : ℝ≥0} (p : CPath (Fin (k + 2) → ℤ)) (x : Fin (k + 2) → ℤ)
    (f : ℝ → Fin (k + 2) → ℝ) (R R' : ℝ) :
    (fun t : Set.Icc (0 : ℝ≥0) T0 => p.fn t) ∈ tubeCyl T0 x f R R' ↔
      p ∈ tubeRat x f R R' (T0 : ℝ) := by
  have hT : ((ptT T0 (T0 : ℝ) : Set.Icc (0 : ℝ≥0) T0) : ℝ≥0) = ((T0 : ℝ)).toNNReal :=
    ptT_val (NNReal.coe_nonneg _) le_rfl
  have hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T0 →
      ((ptT T0 (q : ℝ) : Set.Icc (0 : ℝ≥0) T0) : ℝ≥0) = (q : ℝ).toNNReal :=
    fun q h0 h1 => ptT_val h0 h1
  unfold tubeCyl tubeRat
  simp only [mem_ofPred_eq]
  rw [hT]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun q h0 h1' => ?_, h2, fun q h0 h1' => ?_, h4⟩
    · have := h1 q h0 h1'; rwa [hq q h0 h1'] at this
    · have := h3 q h0 h1'
      have hq0 : 0 ≤ (q : ℝ) := le_trans (by positivity) h0
      rwa [hq q hq0 h1'] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun q h0 h1' => ?_, h2, fun q h0 h1' => ?_, h4⟩
    · have := h1 q h0 h1'; rwa [← hq q h0 h1'] at this
    · have hq0 : 0 ≤ (q : ℝ) := le_trans (by positivity) h0
      have := h3 q h0 h1'; rwa [← hq q hq0 h1'] at this

/-- **The tube event for the walk** (ES22 Claim 5.6, `E^a`; the induction hypothesis at arbitrary times (d) and tube lemma). -/
theorem walk_tube_prob (hp : Es4Params (k + 2) β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    {T : ℝ} (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) {K ρ : ℝ} (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hT1 : ρ ^ 2 / K ≤ T) (hT2 : T ≤ K * ρ ^ 2) {f : ℝ → Fin (k + 2) → ℝ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T, ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (x : Fin (k + 2) → ℤ) (hx : ‖escCast x - f 0‖ ≤ 3 * ρ / 5) :
    ENNReal.ofReal (ctube (k + 2) K) - ENNReal.ofReal (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | escCPath N ω ∈ tubeRat x f (ρ + T ^ indThetaH) (ρ / 5 + T ^ indThetaH) T} := by
  have := hN.isProbabilityMeasure
  have hT0pos : 0 < T := lt_of_le_of_lt (by positivity) h1
  set T0 : ℝ≥0 := T.toNNReal with hT0def
  have hT0 : (T0 : ℝ) = T := Real.coe_toNNReal _ hT0pos.le
  obtain ⟨σ, hσ, hc⟩ := es4_hyp_d hp hN h1 h2
  obtain ⟨Q, hQ, hlaw, hB, hae, hfail⟩ :=
    Bridge.exists_standardBrownianMotion_of_admitsBMCoupling hc
  set ε : ℝ := T ^ indThetaH with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hT0pos _
  set Bz := Bridge.zeroMod (Prod.snd : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) → _) with hBz
  have htube := tube_lemma_event (P := Q) hB hK hσ.1 hσ.2 hρ (T := T0)
    (by rw [hT0]; exact hT1) (by rw [hT0]; exact hT2) (f := f) (x := escCast x)
    (by rw [hT0]; exact hf) hx
  obtain ⟨-, -, hbound⟩ := htube
  set TE : Set (WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ)) :=
    {ω | (∀ u : ℝ≥0, u ≤ T0 → ‖escCast x + σ • Bz u ω - f u‖ ≤ ρ) ∧
      (∀ u : ℝ≥0, T0 / 2 ≤ u → u ≤ T0 → ‖escCast x + σ • Bz u ω - f u‖ ≤ ρ / 5)} with hTE
  set S0 := tubeCyl T0 x f (ρ + ε) (ρ / 5 + ε) with hS0
  have hS0m : MeasurableSet S0 := measurableSet_tubeCyl _ _ _ _ _
  set Φ : Ω → Set.Icc (0 : ℝ≥0) T0 → Fin (k + 2) → ℤ :=
    fun ω t => avoidWalk N ω ((t : ℝ≥0) : ℝ) with hΦ
  have hΦm : AEMeasurable Φ Pr := by
    have : Φ = (fun (y : ℝ≥0 → Fin (k + 2) → ℤ) (t : Set.Icc (0 : ℝ≥0) T0) => y t) ∘
        avoidPath N := rfl
    rw [this]
    exact (Measurable.of_eval fun t => measurable_pi_apply _).comp_aemeasurable
      (aemeasurable_avoidPath hN)
  have hπ : Measurable (fun p : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have hA : Pr (Φ ⁻¹' S0) = Q ((fun p : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹' S0) := by
    calc Pr (Φ ⁻¹' S0) = (Pr.map Φ) S0 := (Measure.map_apply_of_aemeasurable hΦm hS0m).symm
      _ = (Q.map (fun p : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1)) S0 :=
        (congrArg (fun m => m S0) hlaw).symm
      _ = _ := Measure.map_apply hπ hS0m
  set G : Set (WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ)) := {p | ENNReal.ofReal ε ≤
    ⨆ t : Set.Icc (0 : ℝ≥0) T0,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖} with hG
  have hsub : TE ⊆ (fun p : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹' S0 ∪ G := by
    intro p hp'
    by_cases hg : p ∈ G
    · exact Or.inr hg
    left
    have hgt : ∀ t : Set.Icc (0 : ℝ≥0) T0,
        ‖escCast (p.1.1 t) - σ • Bz (t : ℝ≥0) p‖ < ε := by
      intro t
      have h2' : ⨆ t : Set.Icc (0 : ℝ≥0) T0, ENNReal.ofReal
          ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖ < ENNReal.ofReal ε := not_le.1 hg
      have := lt_of_le_of_lt (le_iSup _ t) h2'
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 this
    obtain ⟨hp1, hp2⟩ := hp'
    have key : ∀ (r : ℝ) (ρ' : ℝ), 0 ≤ r → r ≤ T0 →
        ‖escCast x + σ • Bz r.toNNReal p - f r‖ ≤ ρ' →
        ‖escCast (x + p.1.1 (ptT T0 r)) - f r‖ ≤ ρ' + ε := by
      intro r ρ' hr0 hrT hbd
      have hpt := ptT_val hr0 hrT
      have hg2 := hgt (ptT T0 r)
      rw [hpt] at hg2
      have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
      calc ‖escCast (x + p.1.1 (ptT T0 r)) - f r‖
          = ‖(escCast x + σ • Bz r.toNNReal p - f r) +
              (escCast (p.1.1 (ptT T0 r)) - σ • Bz r.toNNReal p)‖ := by
            rw [escCast_add]; congr 1; abel
        _ ≤ ‖escCast x + σ • Bz r.toNNReal p - f r‖ +
              ‖escCast (p.1.1 (ptT T0 r)) - σ • Bz r.toNNReal p‖ := norm_add_le _ _
        _ ≤ ρ' + ε := by linarith
    have key' : ∀ (r ρ' : ℝ), 0 ≤ r → r ≤ T0 →
        ‖escCast x + σ • Bz r.toNNReal p - f ((r.toNNReal : ℝ≥0) : ℝ)‖ ≤ ρ' →
        ‖escCast (x + p.1.1 (ptT T0 r)) - f r‖ ≤ ρ' + ε := by
      intro r ρ' hr0 hrT hbd
      rw [Real.coe_toNNReal _ hr0] at hbd
      exact key r ρ' hr0 hrT hbd
    have e0 : ((T0 : ℝ)).toNNReal = T0 := Real.toNNReal_coe
    have hhalf : T0 / 2 ≤ T0 := half_le_self bot_le
    refine ⟨fun q hq0 hqT => ?_, ?_, fun q hq0 hqT => ?_, ?_⟩
    · exact key' q _ hq0 hqT (hp1 _ (Real.toNNReal_le_iff_le_coe.2 hqT))
    · exact key (T0 : ℝ) _ (NNReal.coe_nonneg _) le_rfl (by rw [e0]; exact hp1 T0 le_rfl)
    · have hq0' : 0 ≤ (q : ℝ) := le_trans (by positivity) hq0
      refine key' q _ hq0' hqT (hp2 _ ?_ (Real.toNNReal_le_iff_le_coe.2 hqT))
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0']
      push_cast
      exact hq0
    · exact key (T0 : ℝ) _ (NNReal.coe_nonneg _) le_rfl
        (by rw [e0]; exact hp2 T0 hhalf le_rfl)
  have hB1 : ENNReal.ofReal (ctube (k + 2) K) ≤ Q TE := hbound
  have hfail' : Q G ≤ ENNReal.ofReal (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) := hfail
  have hmain : ENNReal.ofReal (ctube (k + 2) K) ≤
      Q ((fun p : WalkPath (k + 2) T0 × C(ℝ≥0, Fin (k + 2) → ℝ) => p.1.1) ⁻¹' S0) +
        ENNReal.ofReal (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) :=
    hB1.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl hfail')))
  have hlow : ENNReal.ofReal (ctube (k + 2) K) -
      ENNReal.ofReal (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) ≤ Pr (Φ ⁻¹' S0) := by
    rw [hA]; exact tsub_le_iff_right.2 hmain
  refine hlow.trans (measure_mono_ae ?_)
  have hNg : ∀ᵐ ω ∂Pr, cycNgood N ω = N ω := ae_cycNgood_eq hN
  filter_upwards [hNg] with ω hω hmem
  have hW : ∀ t : ℝ≥0, (escCPath N ω).fn t = avoidWalk N ω (t : ℝ) := fun t => by
    show avoidPath (cycNgood N) ω t = _
    exact congrFun (avoidWalk_congr hω) _
  have : (fun t : Set.Icc (0 : ℝ≥0) T0 => (escCPath N ω).fn t) = Φ ω := by
    funext t; exact hW t
  have h3 : (fun t : Set.Icc (0 : ℝ≥0) T0 => (escCPath N ω).fn t) ∈ tubeCyl T0 x f (ρ + ε) (ρ / 5 + ε) := by
    rw [this]; exact hmem
  have := (mem_tubeCyl_iff (T0 := T0) (escCPath N ω) x f (ρ + ε) (ρ / 5 + ε)).1 h3
  rw [hT0] at this
  exact this

end Walk

end ElboimSly.Paper.Escape

end
