import Submission.MatroidBinaryInequality
import Submission.BinaryCoefficients
import Submission.GroundReduction

set_option autoImplicit false

/-! The division-free Strong Mason inequality for the exact challenge count. -/

namespace StrongMasonAudit

variable {α : Type*}

theorem strong_mason_count_finite_ambient [Fintype α]
    (M : Matroid α) [M.Finite] (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    {I ∈ Set.powersetCard α (k - 1) | M.Indep I}.ncard *
        {I ∈ Set.powersetCard α (k + 1) | M.Indep I}.ncard *
          (k + 1) * (M.E.ncard - k + 1) ≤
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard ^ 2 * k * (M.E.ncard - k) := by
  classical
  let I : ℕ → ℕ := fun j => {J ∈ Set.powersetCard α j | M.Indep J}.ncard
  have hpoly : MvPolynomial.rename binaryVariable (independencePolynomial M) =
      binaryCountPolynomial M.E.ncard I :=
    rename_independencePolynomial_binary_counts M
  apply nat_count_inequality_of_binaryQuadratic_certificate I M.E.ncard k hk hkn
  rw [binaryQuadraticDerivative_eq_iteratedDirectionalDerivative]
  rw [← hpoly]
  apply independencePolynomial_binary_hessian_inequality M (by omega)
    ((binaryDerivativeIndices M.E.ncard k).map (fun i => Pi.single i 1))
    ?_ 0 (by simp) (Pi.single false 1) (Pi.single true 1) ?_
  · intro v hv i
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num

/-- The ambient type is arbitrary. Passing to the finite ground subtype
preserves both the exact independent-set counts and the ground cardinality. -/
theorem strong_mason_count
    (M : Matroid α) [M.Finite] (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    {I ∈ Set.powersetCard α (k - 1) | M.Indep I}.ncard *
        {I ∈ Set.powersetCard α (k + 1) | M.Indep I}.ncard *
          (k + 1) * (M.E.ncard - k + 1) ≤
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard ^ 2 * k * (M.E.ncard - k) := by
  letI : Fintype M.E := groundFintype M
  simpa only [independentSetCount_ground_eq, groundMatroid_ncard] using
    strong_mason_count_finite_ambient (M.restrictSubtype M.E) k hk
      (by simpa only [groundMatroid_ncard] using hkn)

#print axioms strong_mason_count_finite_ambient
#print axioms strong_mason_count

end StrongMasonAudit
