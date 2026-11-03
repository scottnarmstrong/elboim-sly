/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.BernoulliStopping
public import ElboimSly.Foundations.Concentration.BinomialTail

/-!
# Few excursions (abstract form)

Few excursions (ES22 §7). For stopping times `ζ_i ≤ ζ'_i ≤ ζ_{i+1} ≤ T`
and an event `H ∈ ℱ_{ζ_1}` such that every `ℱ_{ζ_i}`-event `G ⊆ H ∩ {ζ_i < T}` satisfies
`P(G ∩ {ζ'_i < T}) ≤ ½ P(G)` (one excursion succeeds with probability at least frac12), the probability that `H` holds and
`ζ_1, …, ζ_{n³}` are all `< T` is at most `exp(-n³/17)`; this is `P(H ∩ {J > n³})`.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Paper.Step

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ι : Type*} [LinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- Few excursions. -/
theorem step78_few_excursions {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ι m0}
    {ζ ζ' : ℕ → Ω → WithTop ι} (T : ι)
    (hζ : ∀ i, IsStoppingTime ℱ (ζ i)) (hζ' : ∀ i, IsStoppingTime ℱ (ζ' i))
    (hleT : ∀ i ω, ζ i ω ≤ (T : WithTop ι))
    (h1 : ∀ i ω, ζ i ω ≤ ζ' i ω) (h2 : ∀ i ω, ζ' i ω ≤ ζ (i + 1) ω)
    {H : Set Ω} (hH : MeasurableSet[(hζ 1).measurableSpace] H)
    (hex : ∀ i, 1 ≤ i → ∀ G : Set Ω, MeasurableSet[(hζ i).measurableSpace] G →
      G ⊆ H ∩ {ω | ζ i ω < (T : WithTop ι)} →
        μ.real (G ∩ {ω | ζ' i ω < (T : WithTop ι)}) ≤ (1 / 2) * μ.real G)
    {n : ℕ} (hn : 3 ≤ n) :
    μ.real (H ∩ {ω | ∀ i, 1 ≤ i → i ≤ n ^ 3 → ζ i ω < (T : WithTop ι)}) ≤
      Real.exp (-((n : ℝ) ^ 3 / 17)) := by
  have hTst : IsStoppingTime ℱ (fun _ : Ω => (T : WithTop ι)) := isStoppingTime_const ℱ T
  have hmono : ∀ i, ∀ ω, ζ i ω ≤ ζ (i + 1) ω := fun i ω => (h1 _ ω).trans (h2 _ ω)
  have h1le : ∀ i, ∀ ω, ζ 1 ω ≤ ζ (1 + i) ω := by
    intro i; induction i with
    | zero => intro ω; exact le_rfl
    | succ i ih => intro ω; exact (ih ω).trans (hmono _ ω)
  set K := n ^ 3 - 1 with hK
  have hn1 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hs : ∀ i, IsStoppingTime ℱ ((fun j => ζ (1 + j)) i) := fun i => hζ _
  let G : ℕ → Set Ω := fun j => H ∩ {ω | ζ (1 + j) ω < (T : WithTop ι)}
  let A : ℕ → Set Ω := fun j => {ω | ζ' (1 + j) ω = (T : WithTop ι)}
  have hGm : ∀ i < K, MeasurableSet[(hs i).measurableSpace] (G i) := fun i _ =>
    measurableSet_inter_lt_stopping (hζ 1) (hs i) hTst (h1le i) hH
  have hltm : ∀ i, MeasurableSet[(hζ' (1 + i)).measurableSpace]
      {ω | ζ' (1 + i) ω < (T : WithTop ι)} := by
    intro i
    have := measurableSet_inter_lt_stopping (hζ' (1 + i)) (hζ' (1 + i)) hTst (fun _ => le_rfl)
      (H := Set.univ) MeasurableSet.univ
    simpa using this
  have hAm : ∀ i < K, MeasurableSet[(hs (i + 1)).measurableSpace] (A i) := by
    intro i _
    have hAeq : A i = {ω | ζ' (1 + i) ω < (T : WithTop ι)}ᶜ := by
      ext ω
      simp only [A, Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
      constructor
      · intro h; exact h.ge
      · intro h; exact le_antisymm ((h2 _ ω).trans (hleT _ ω)) h
    rw [hAeq]
    exact (hζ' (1 + i)).measurableSpace_mono (hs (i + 1)) (fun ω => h2 _ ω) _ (hltm i).compl
  have hB : ∀ i < K, ∀ F, MeasurableSet[(hs i).measurableSpace] F →
      (1 / 2 : ℝ) * μ.real (G i ∩ F) ≤ μ.real (A i ∩ G i ∩ F) := by
    intro i hi F hF
    have hGF : MeasurableSet[(hζ (1 + i)).measurableSpace] (G i ∩ F) := (hGm i hi).inter hF
    have hsub : G i ∩ F ⊆ H ∩ {ω | ζ (1 + i) ω < (T : WithTop ι)} := fun x hx => hx.1
    have hx := hex (1 + i) (by omega) _ hGF hsub
    have hmeas : MeasurableSet (G i ∩ F) := (hζ (1 + i)).measurableSpace_le _ hGF
    have hsetM : MeasurableSet {ω | ζ' (1 + i) ω < (T : WithTop ι)} :=
      (hζ' (1 + i)).measurableSpace_le _ (hltm i)
    have hsplit : μ.real (G i ∩ F) =
        μ.real (G i ∩ F ∩ {ω | ζ' (1 + i) ω < (T : WithTop ι)}) +
          μ.real (A i ∩ G i ∩ F) := by
      rw [← measureReal_inter_add_sdiff (μ := μ) (s := G i ∩ F) hsetM]
      congr 2
      ext ω
      simp only [A, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_lt]
      constructor
      · rintro ⟨hω, hz⟩
        exact ⟨⟨le_antisymm ((h2 _ ω).trans (hleT _ ω)) hz, hω.1⟩, hω.2⟩
      · rintro ⟨⟨hz, hG⟩, hF'⟩
        exact ⟨⟨hG, hF'⟩, hz.ge⟩
    linarith
  have hb := concBernoulli_lower_stopping (μ := μ) (K := K) (s := fun j => ζ (1 + j)) hs
    (fun i _ ω => by simpa [add_assoc, add_comm, add_left_comm] using hmono (1 + i) ω)
    hGm hAm (p := 1 / 2) (by norm_num) (by norm_num) hB 2
  have hsub : H ∩ {ω | ∀ i, 1 ≤ i → i ≤ n ^ 3 → ζ i ω < (T : WithTop ι)} ⊆
      concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ 2} := by
    intro ω ⟨hωH, hω⟩
    refine ⟨fun j hj => ⟨hωH, hω (1 + j) (by omega) (by omega)⟩, ?_⟩
    have hz : concCount A K ω = 0 := by
      unfold concCount
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : j < K := Finset.mem_range.1 hj
      have hnA : ω ∉ A j := by
        intro hA
        have hA' : ζ' (1 + j) ω = (T : WithTop ι) := hA
        have h3 := hω (1 + j + 1) (by omega) (by omega)
        have h4 : (T : WithTop ι) ≤ ζ (1 + j + 1) ω := hA' ▸ h2 _ ω
        exact absurd h3 (not_lt.2 h4)
      simp [hnA]
    simp [hz]
  calc _ ≤ μ.real (concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ 2}) :=
        measureReal_mono hsub
    _ ≤ concBinomLE K (1 / 2) 2 := hb
    _ ≤ _ := concBinomLE_le_exp_cube_sub_one_half hn

end ElboimSly.Paper.Step

end
