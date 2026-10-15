import Submission.IndependentSetPolynomial
import Mathlib.Combinatorics.Matroid.Map

set_option autoImplicit false

/-! Exact transfer from an arbitrary ambient type to the finite ground subtype. -/

namespace StrongMasonAudit

variable {α : Type*}

noncomputable def groundFinsetEmbedding (M : Matroid α) :
    Finset M.E ↪ Finset α :=
  ⟨Finset.map (Function.Embedding.subtype _), Finset.map_injective _⟩

@[simp] theorem groundFinsetEmbedding_card (M : Matroid α) (I : Finset M.E) :
    (groundFinsetEmbedding M I).card = I.card := Finset.card_map _

theorem independentFinsets_ground_map (M : Matroid α) [M.Finite] :
    (independentFinsets (M.restrictSubtype M.E)).map (groundFinsetEmbedding M) =
      independentFinsets M := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
    apply (mem_independentFinsets M _).mpr
    have hJ' := (mem_independentFinsets (M.restrictSubtype M.E) J).mp hJ
    rw [Matroid.restrictSubtype_indep_iff] at hJ'
    change M.Indep (J.map (Function.Embedding.subtype _) : Set α)
    simpa using hJ'
  · intro hI
    have hInd := (mem_independentFinsets M I).mp hI
    let J : Finset M.E := I.subtype (· ∈ M.E)
    have hmap : groundFinsetEmbedding M J = I :=
      Finset.subtype_map_of_mem (fun x hx => hInd.subset_ground hx)
    apply Finset.mem_map.mpr
    refine ⟨J, ?_, hmap⟩
    apply (mem_independentFinsets (M.restrictSubtype M.E) J).mpr
    rw [Matroid.restrictSubtype_indep_iff]
    have hcoe : Subtype.val '' (J : Set M.E) =
        (groundFinsetEmbedding M J : Set α) := by
      simp [groundFinsetEmbedding]
    rw [hcoe, hmap]
    exact hInd

/-- Passing to the ground subtype preserves the exact challenge count. -/
theorem independentSetCount_ground_eq (M : Matroid α) [M.Finite] (k : ℕ) :
    {I ∈ Set.powersetCard M.E k | (M.restrictSubtype M.E).Indep I}.ncard =
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard := by
  classical
  rw [independentSetCount_finset_bridge, independentSetCount_finset_bridge,
    ← independentFinsets_ground_map M, Finset.filter_map]
  simp only [Function.comp_apply, groundFinsetEmbedding_card, Finset.card_map]

@[simp] theorem groundMatroid_ncard (M : Matroid α) :
    (M.restrictSubtype M.E).E.ncard = M.E.ncard := by
  rw [Matroid.restrictSubtype_ground, Set.ncard_univ, Nat.card_coe_set_eq]

/-- The ground subtype is finite, so finite-coordinate polynomial results apply
without an additional assumption on the original ambient type. -/
@[reducible] noncomputable def groundFintype (M : Matroid α) [M.Finite] : Fintype M.E :=
  M.ground_finite.fintype

#print axioms independentFinsets_ground_map
#print axioms independentSetCount_ground_eq
#print axioms groundMatroid_ncard

end StrongMasonAudit
