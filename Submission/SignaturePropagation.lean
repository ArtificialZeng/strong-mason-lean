import Submission.CommonNormal
import Submission.HessianPositivity

set_option autoImplicit false

/-! A connected finite-sum form of ALGV Lemma 3.4. The argument is algebraic:
it glues summands with a common nonzero normal, and uses no continuity of inertia. -/

namespace StrongMasonAudit

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem sigPos_smul_le (B : LinearMap.BilinForm ℝ V) {a : ℝ} (ha : 0 < a) :
    sigPos (a • B).toQuadraticMap ≤ sigPos B.toQuadraticMap := by
  obtain ⟨S, hdim, hpos⟩ :=
    exists_finrank_eq_sigPos_and_posDef (a • B).toQuadraticMap
  rw [← hdim]
  apply le_sigPos_of_posDef
  intro x hx
  have h := hpos x hx
  change 0 < a * B (x : V) (x : V) at h
  exact (mul_pos_iff_of_pos_left ha).mp h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Abstract symmetric third-derivative tensors propagate positive index through
connected support. Connectivity is the cut condition: every nonempty proper
set of indices has a positive tensor entry crossing its cut. -/
theorem sigPos_sum_le_one_of_connected_tensor_on
    (B : ι → LinearMap.BilinForm ℝ V) (e : ι → V)
    (hB : ∀ i, (B i).IsSymm)
    (hsig : ∀ i, sigPos (B i).toQuadraticMap ≤ 1)
    (hentry : ∀ i j k, 0 ≤ B i (e j) (e k))
    (hmixed : ∀ i j, B i (e j) = B j (e i))
    (t : Finset ι) (ht : t.Nonempty)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ ∃ k, 0 < B i (e j) (e k))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    sigPos (∑ i ∈ t, a i • B i).toQuadraticMap ≤ 1 := by
  classical
  let A : Finset ι → LinearMap.BilinForm ℝ V := fun s => ∑ i ∈ s, a i • B i
  have hstep (s : Finset ι) (hst : s ⊆ t) (hs : s.Nonempty)
      (hsigS : sigPos (A s).toQuadraticMap ≤ 1) (hsu : s ≠ t) :
      ∃ j ∈ t, j ∉ s ∧ sigPos (A (insert j s)).toQuadraticMap ≤ 1 := by
    obtain ⟨i, hi, j, hjt, hj, k, hijk⟩ := hconnected s hst hs hsu
    let b : V := ∑ i ∈ s, a i • e i
    let c : V := a j • e j
    have hAsymm : (A s).IsSymm := by
      constructor
      intro x y
      simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro l hl
      rw [(hB l).eq]
    have hCsymm : (a j • B j).IsSymm := by
      constructor
      intro x y
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [(hB j).eq]
    have hnormal : (A s) c = (a j • B j) b := by
      ext z
      simp only [A, b, c, LinearMap.sum_apply, LinearMap.smul_apply,
        map_sum, map_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have h := congrArg (fun f : V →ₗ[ℝ] ℝ => f z) (hmixed l j)
      rw [h]
      ring
    have hAeval (x y : V) : (A s) x y = ∑ l ∈ s, a l * B l x y := by
      simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hnonzero : (A s) c ≠ 0 := by
      intro hz
      have heq : (A s) c (e k) = 0 := by rw [hz, LinearMap.zero_apply]
      have hpos : 0 < (A s) c (e k) := by
        rw [hAeval]
        simp only [c, LinearMap.BilinForm.smul_left]
        apply Finset.sum_pos'
        · intro l hl
          exact mul_nonneg (ha l).le (mul_nonneg (ha j).le (hentry l j k))
        · exact ⟨i, hi, mul_pos (ha i) (mul_pos (ha j) hijk)⟩
      exact (ne_of_gt hpos) heq
    have hcc : 0 ≤ (A s) c c := by
      rw [hAeval]
      simp only [c, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (ha l).le (mul_nonneg (ha j).le
          (mul_nonneg (ha j).le (hentry l j j)))
    have hbb : 0 ≤ (a j • B j) b b := by
      change 0 ≤ a j * B j b b
      apply mul_nonneg (ha j).le
      simp only [b, map_sum, map_smul]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_nonneg
      intro l hl
      apply mul_nonneg (ha l).le
      apply Finset.sum_nonneg
      intro m hm
      exact mul_nonneg (ha m).le (hentry j m l)
    refine ⟨j, hjt, hj, ?_⟩
    have hadd := sigPos_add_le_one_of_common_normal (A s) (a j • B j)
      hAsymm hCsymm hsigS ((sigPos_smul_le (B j) (ha j)).trans (hsig j))
      c b hcc hbb hnormal hnonzero
    have hAinsert : A (insert j s) = A s + a j • B j := by
      simp only [A, Finset.sum_insert hj]
      exact add_comm _ _
    rwa [hAinsert]
  have hgrow : ∀ n : ℕ, ∀ s : Finset ι, (t \ s).card = n → s ⊆ t →
      s.Nonempty → sigPos (A s).toQuadraticMap ≤ 1 →
      sigPos (A t).toQuadraticMap ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hst hs hsigS
      by_cases hsu : s = t
      · simpa only [hsu] using hsigS
      · obtain ⟨j, hjt, hj, hsigIns⟩ := hstep s hst hs hsigS hsu
        apply ih ((t \ insert j s).card) ?_ (insert j s) rfl (Finset.insert_subset hjt hst)
          (Finset.insert_nonempty j s) hsigIns
        rw [← hn, Finset.sdiff_insert]
        exact Finset.card_erase_lt_of_mem (by simp [hjt, hj])
  obtain ⟨i, hit⟩ := ht
  have hinit : sigPos (A {i}).toQuadraticMap ≤ 1 := by
    simpa only [A, Finset.sum_singleton] using
      (sigPos_smul_le (B i) (ha i)).trans (hsig i)
  simpa only [A] using hgrow (t \ {i}).card {i} rfl
    (Finset.singleton_subset_iff.mpr hit) (Finset.singleton_nonempty i) hinit

section Polynomial

open MvPolynomial

/-- Coordinate evaluation of the actual polynomial Hessian bilinear form. -/
theorem hessianBilin_coordinate (p : MvPolynomial ι ℝ) (w : ι → ℝ) (i j : ι) :
    hessianBilin p w (Pi.single i 1) (Pi.single j 1) = formalHessian p w i j := by
  classical
  simp [hessianBilin, Matrix.toBilin'_apply, Pi.single_apply]

/-- Equality of mixed third partials gives the common normals required in the
finite-sum gluing argument. -/
theorem hessianBilin_pderiv_mixed (p : MvPolynomial ι ℝ) (w : ι → ℝ) (i j : ι) :
    hessianBilin (pderiv i p) w (Pi.single j 1) =
      hessianBilin (pderiv j p) w (Pi.single i 1) := by
  classical
  have hthird (k : ι) : pderiv j (pderiv k (pderiv i p)) =
      pderiv i (pderiv k (pderiv j p)) := by
    rw [pderiv_commutation p k i, pderiv_commutation (pderiv k p) j i,
      pderiv_commutation p k j]
  ext z
  simp [hessianBilin, Matrix.toBilin'_apply, Pi.single_apply, formalHessian, hthird]

/-- A nonzero mixed second partial of degree at least one has a positive
third-partial entry at every strictly positive point. -/
theorem exists_pos_third_of_second_ne_zero
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (i j : ι)
    (hij : pderiv i (pderiv j p) ≠ 0) :
    ∃ k, 0 < hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
  have hc : 0 < ((d - 2 : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 3) hd))
  have hsecond : 0 < formalHessian p w i j :=
    eval_pos_of_nonnegativeCoefficients ((hp.pderiv j).pderiv i) hij hw
  have hsum : 0 < ∑ k, w k * formalHessian (pderiv i p) w k j := by
    rw [formalHessian_euler_row hhom]
    exact mul_pos hc hsecond
  have hnonneg (k : ι) : 0 ≤ w k * formalHessian (pderiv i p) w k j := by
    apply mul_nonneg (hw k).le
    exact eval_nonneg_of_nonnegativeCoefficients (((hp.pderiv i).pderiv j).pderiv k)
      (fun l => (hw l).le)
  obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => hnonneg k)).mp hsum
  refine ⟨k, ?_⟩
  rw [hessianBilin_coordinate, formalHessian_symm (pderiv i p) w j k]
  exact (mul_pos_iff_of_pos_left (hw k)).mp hk

/-- Pointwise ALGV connected-derivative propagation. Connectivity is stated on
nonzero mixed second partials; entry positivity and equality of mixed third
partials are derived from the actual polynomial. -/
theorem homogeneous_derivative_sum_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (t : Finset ι) (ht : t.Nonempty)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    sigPos (∑ i ∈ t, a i • hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1 := by
  have hentry (i j k : ι) :
      0 ≤ hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
    rw [hessianBilin_coordinate]
    exact eval_nonneg_of_nonnegativeCoefficients (((hp.pderiv i).pderiv k).pderiv j)
      (fun l => (hw l).le)
  have hconn : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ ∃ k,
        0 < hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
    intro s hst hs hne
    obtain ⟨i, hi, j, hjt, hj, hij⟩ := hconnected s hst hs hne
    obtain ⟨k, hk⟩ := exists_pos_third_of_second_ne_zero hhom hd hp hw i j hij
    exact ⟨i, hi, j, hjt, hj, k, hk⟩
  exact sigPos_sum_le_one_of_connected_tensor_on
    (fun i => hessianBilin (pderiv i p) w) (fun i => Pi.single i 1)
    (fun i => hessianBilin_isSymm (pderiv i p) w) hsig
    hentry (hessianBilin_pderiv_mixed p w) t ht hconn a ha

/-- The parent Hessian has positive index at most one if its nonzero derivative
support is connected and every derivative Hessian has positive index at most
one. Variables outside `t` are retained in the ambient Hessian and are required
to be inactive; no nonsingularity assumption is used. -/
theorem homogeneous_hessian_sigPos_le_one_of_connected
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (t : Finset ι) (ht : t.Nonempty)
    (hinactive : ∀ i ∉ t, pderiv i p = 0)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0) :
    sigPos (hessianBilin p w).toQuadraticMap ≤ 1 := by
  have hc : 0 < ((d - 2 : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 3) hd))
  have hsum := homogeneous_derivative_sum_sigPos_le_one hhom hd hp hw hsig
    t ht hconnected w hw
  have hEuler : (∑ i ∈ t, w i • hessianBilin (pderiv i p) w) =
      ((d - 2 : ℕ) : ℝ) • hessianBilin p w := by
    have hfull : (∑ i ∈ t, w i • hessianBilin (pderiv i p) w) =
        ∑ i, w i • hessianBilin (pderiv i p) w := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro i _ hi
      simp [hinactive i hi]
    rw [hfull]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
      (hessianBilin_euler hhom w x y).symm
  rw [hEuler] at hsum
  have hcancel : (((d - 2 : ℕ) : ℝ)⁻¹) •
      (((d - 2 : ℕ) : ℝ) • hessianBilin p w) = hessianBilin p w := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hbound := (sigPos_smul_le
    (((d - 2 : ℕ) : ℝ) • hessianBilin p w) (inv_pos.mpr hc)).trans hsum
  rwa [hcancel] at hbound

end Polynomial

#print axioms hessianBilin_coordinate
#print axioms hessianBilin_pderiv_mixed
#print axioms exists_pos_third_of_second_ne_zero
#print axioms homogeneous_derivative_sum_sigPos_le_one
#print axioms homogeneous_hessian_sigPos_le_one_of_connected

#print axioms sigPos_smul_le
#print axioms sigPos_sum_le_one_of_connected_tensor_on

end StrongMasonAudit
