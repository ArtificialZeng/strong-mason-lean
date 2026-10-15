import Submission.SignaturePropagation
import Submission.SignatureClosure

set_option autoImplicit false

/-! The coordinate-quadratic sufficient criterion underlying ALGV Theorem 3.2.
This module uses positive-index language; it does not redefine log-concavity. -/

namespace StrongMasonAudit

open Filter MvPolynomial
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def iteratedPartialDerivative : List ι → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | i :: is, p => pderiv i (iteratedPartialDerivative is p)

noncomputable def iteratedDirectionalDerivative :
    List (ι → ℝ) → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | v :: vs, p => directionalDerivative v (iteratedDirectionalDerivative vs p)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pderiv_iteratedPartialDerivative (is : List ι)
    (p : MvPolynomial ι ℝ) (i : ι) :
    pderiv i (iteratedPartialDerivative is p) =
      iteratedPartialDerivative is (pderiv i p) := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    change pderiv i (pderiv j (iteratedPartialDerivative js p)) =
      pderiv j (iteratedPartialDerivative js (pderiv i p))
    rw [pderiv_commutation (iteratedPartialDerivative js p) i j, ih]

omit [DecidableEq ι] in
@[simp] theorem pderiv_iteratedDirectionalDerivative (vs : List (ι → ℝ))
    (p : MvPolynomial ι ℝ) (i : ι) :
    pderiv i (iteratedDirectionalDerivative vs p) =
      iteratedDirectionalDerivative vs (pderiv i p) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [iteratedDirectionalDerivative, pderiv_directionalDerivative, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem iteratedPartialDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (is : List ι) :
    (iteratedPartialDerivative is p).IsHomogeneous (d - is.length) := by
  induction is with
  | nil => simpa only [iteratedPartialDerivative, List.length_nil, Nat.sub_zero] using hp
  | cons i is ih =>
    simpa only [iteratedPartialDerivative, List.length_cons, Nat.sub_sub] using ih.pderiv (i := i)

omit [DecidableEq ι] in
theorem iteratedDirectionalDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d)
    (vs : List (ι → ℝ)) :
    (iteratedDirectionalDerivative vs p).IsHomogeneous (d - vs.length) := by
  induction vs with
  | nil => simpa only [iteratedDirectionalDerivative, List.length_nil, Nat.sub_zero] using hp
  | cons v vs ih =>
    simpa only [iteratedDirectionalDerivative, List.length_cons, Nat.sub_sub] using
      directionalDerivative_isHomogeneous ih v

omit [DecidableEq ι] in
theorem NonnegativeCoefficients.iteratedDirectionalDerivative
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i) :
    NonnegativeCoefficients (iteratedDirectionalDerivative vs p) := by
  induction vs with
  | nil => exact hp
  | cons v vs ih =>
    exact (ih (fun u hu => hv u (List.mem_cons_of_mem v hu))).directionalDerivative
      (hv v (List.mem_cons_self))

/-- Positive directions detect every nonzero homogeneous polynomial of positive
degree with nonnegative coefficients. -/
theorem directionalDerivative_eq_zero_iff_of_pos
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 1 ≤ d) (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    directionalDerivative v p = 0 ↔ p = 0 := by
  constructor
  · intro hzero
    by_contra hp0
    have hpos : 0 < eval v (directionalDerivative v p) := by
      rw [eval_directionalDerivative, homogeneous_euler_eval hhom]
      exact mul_pos (Nat.cast_pos.mpr (by omega))
        (eval_pos_of_nonnegativeCoefficients hp hp0 hv)
    exact (ne_of_gt hpos) (by rw [hzero, map_zero])
  · intro hp0
    simp [hp0, directionalDerivative]

/-- An explicit cut formulation of connected active variable support. The zero
polynomial is included as a separate case. -/
def ConnectedPartialSupport (p : MvPolynomial ι ℝ) : Prop :=
  p = 0 ∨ ∃ t : Finset ι, t.Nonempty ∧
    (∀ i ∉ t, pderiv i p = 0) ∧
    ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0

/-- Strictly positive directional differentiation preserves the cut graph when
the initial degree is at least three. -/
theorem ConnectedPartialSupport.directionalDerivative
    {p : MvPolynomial ι ℝ} {d : ℕ} (hconn : ConnectedPartialSupport p)
    (hhom : p.IsHomogeneous d) (hd : 3 ≤ d)
    (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    ConnectedPartialSupport (directionalDerivative v p) := by
  rcases hconn with hzero | ⟨t, ht, hinactive, hcut⟩
  · left
    simp [hzero, StrongMasonAudit.directionalDerivative]
  · right
    refine ⟨t, ht, ?_, ?_⟩
    · intro i hi
      rw [pderiv_directionalDerivative, hinactive i hi]
      simp [StrongMasonAudit.directionalDerivative]
    · intro s hst hs hne
      obtain ⟨i, hi, j, hjt, hj, hij⟩ := hcut s hst hs hne
      refine ⟨i, hi, j, hjt, hj, ?_⟩
      simp only [pderiv_directionalDerivative]
      exact mt (directionalDerivative_eq_zero_iff_of_pos
        ((hhom.pderiv (i := j)).pderiv (i := i)) (by omega)
        ((hp.pderiv j).pderiv i) hv).mp hij

/-- A positive directional derivative preserves connected support throughout
all iterations whose final degree is at least two. -/
theorem ConnectedPartialSupport.iteratedDirectionalDerivative
    {p : MvPolynomial ι ℝ} {d : ℕ} (hconn : ConnectedPartialSupport p)
    (hhom : p.IsHomogeneous d) (hp : NonnegativeCoefficients p)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2) (hd : 2 ≤ d)
    (hv : ∀ v ∈ vs, ∀ i, 0 < v i) :
    ConnectedPartialSupport (iteratedDirectionalDerivative vs p) := by
  induction vs with
  | nil => exact hconn
  | cons v vs ih =>
    have hvvs : ∀ u ∈ vs, ∀ i, 0 < u i := fun u hu => hv u (List.mem_cons_of_mem v hu)
    exact (ih (by simp only [List.length_cons] at hlen; omega) hvvs).directionalDerivative
      (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by simp only [List.length_cons] at hlen; omega)
      (hp.iteratedDirectionalDerivative vs (fun u hu i => (hvvs u hu i).le))
      (hv v List.mem_cons_self)

/-- Pointwise parent-signature propagation with the zero-support case included. -/
theorem hessian_sigPos_le_one_of_connectedPartialSupport
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ConnectedPartialSupport p) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1) :
    sigPos (hessianBilin p w).toQuadraticMap ≤ 1 := by
  rcases hconn with hz | ⟨t, ht, hinactive, hcut⟩
  · rw [hz, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · exact homogeneous_hessian_sigPos_le_one_of_connected hhom hd hp hw hsig
      t ht hinactive hcut

/-- Pointwise positive-direction propagation with inactive variables retained. -/
theorem directionalDerivative_sigPos_le_one_of_connectedPartialSupport
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ConnectedPartialSupport p) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1 := by
  rcases hconn with hz | ⟨t, ht, hinactive, hcut⟩
  · simp only [hz, StrongMasonAudit.directionalDerivative, map_zero,
      smul_zero, Finset.sum_const_zero, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · rw [hessianBilin_directionalDerivative]
    have hfull : (∑ i ∈ t, v i • hessianBilin (pderiv i p) w) =
        ∑ i, v i • hessianBilin (pderiv i p) w := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro i _ hi
      simp [hinactive i hi]
    rw [← hfull]
    exact homogeneous_derivative_sum_sigPos_le_one hhom hd hp hw hsig t ht hcut v hv

/-- Positive-direction part of the ALGV coordinate-quadratic criterion. The
connectivity hypothesis concerns only coordinate derivatives, and the signature
hypothesis only terminal quadratic coordinate derivatives. -/
theorem positive_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2)
    (hv : ∀ v ∈ vs, ∀ i, 0 < v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  induction d using Nat.strong_induction_on generalizing p vs with
  | h d ih =>
    by_cases hd2 : d = 2
    · have hvs : vs = [] := List.length_eq_zero_iff.mp (by omega)
      subst vs
      exact hbase [] (by simp [hd2]) w hw
    · have hd3 : 3 ≤ d := by omega
      have hpartial (i : ι) (us : List (ι → ℝ)) (hus : us.length ≤ (d - 1) - 2)
          (hu : ∀ u ∈ us, ∀ j, 0 < u j) :
          sigPos (hessianBilin (iteratedDirectionalDerivative us (pderiv i p)) w).toQuadraticMap ≤ 1 := by
        apply ih (d - 1) (by omega) hhom.pderiv (by omega) (hp.pderiv i) ?_ ?_ us hus hu
        · intro is his
          have hh := hconn (i :: is) (by simp only [List.length_cons]; omega)
          simpa only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative] using hh
        · intro is his z hz
          have hh := hbase (i :: is) (by simp only [List.length_cons]; omega) z hz
          simpa only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative] using hh
      cases vs with
      | nil =>
        apply hessian_sigPos_le_one_of_connectedPartialSupport hhom hd3 hp
          (hconn [] (by simp)) hw
        intro i
        exact hpartial i [] (by simp) (by simp)
      | cons v vs =>
        have hvs : vs.length ≤ d - 3 := by simp only [List.length_cons] at hlen; omega
        have hvvs : ∀ u ∈ vs, ∀ i, 0 < u i := fun u hu => hv u (List.mem_cons_of_mem v hu)
        change sigPos (hessianBilin
          (directionalDerivative v (iteratedDirectionalDerivative vs p)) w).toQuadraticMap ≤ 1
        apply directionalDerivative_sigPos_le_one_of_connectedPartialSupport
          (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega)
          (hp.iteratedDirectionalDerivative vs (fun u hu i => (hvvs u hu i).le))
          ((hconn [] (by simp)).iteratedDirectionalDerivative hhom hp vs (by omega) hd hvvs) hw
        · intro i
          rw [pderiv_iteratedDirectionalDerivative]
          exact hpartial i vs (by omega) hvvs
        · exact hv v List.mem_cons_self

omit [DecidableEq ι] in
/-- Simultaneous regularization of a finite list of directions is continuous
under every polynomial evaluation. No positivity assumption is needed here. -/
theorem tendsto_eval_iteratedDirectionalDerivative_add
    (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    Tendsto (fun ε : ℝ => eval w (iteratedDirectionalDerivative
      (vs.map (fun v i => v i + ε)) p)) (𝓝[>] (0 : ℝ))
      (𝓝 (eval w (iteratedDirectionalDerivative vs p))) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  induction vs generalizing p with
  | nil => exact tendsto_const_nhds
  | cons v vs ih =>
    simp only [List.map_cons, iteratedDirectionalDerivative, eval_directionalDerivative,
      pderiv_iteratedDirectionalDerivative]
    apply tendsto_finsetSum Finset.univ
    intro i _
    have hvi : Tendsto (fun ε : ℝ => v i + ε) (𝓝[>] (0 : ℝ)) (𝓝 (v i)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := v i)).add heps
    exact hvi.mul (ih (pderiv i p))

/-- Pointwise Hessian convergence under simultaneous list regularization. -/
theorem tendsto_hessianBilin_iteratedDirectionalDerivative_add
    (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) (w x y : ι → ℝ) :
    Tendsto (fun ε : ℝ => hessianBilin (iteratedDirectionalDerivative
      (vs.map (fun v i => v i + ε)) p) w x y) (𝓝[>] (0 : ℝ))
      (𝓝 (hessianBilin (iteratedDirectionalDerivative vs p) w x y)) := by
  simp only [hessianBilin, Matrix.toBilin'_apply, formalHessian,
    pderiv_iteratedDirectionalDerivative]
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((tendsto_const_nhds (x := x i)).mul
    (tendsto_eval_iteratedDirectionalDerivative_add vs (pderiv i (pderiv j p)) w)).mul
    (tendsto_const_nhds (x := y j))

/-- The ALGV coordinate-quadratic criterion for arbitrary nonnegative
iterated directions down to degree two, expressed by positive index. -/
theorem nonnegative_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2)
    (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  by_cases hz : iteratedDirectionalDerivative vs p = 0
  · rw [hz, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
      hessianBilin (iteratedDirectionalDerivative (vs.map (fun v i => v i + ε)) p) w
    apply sigPos_le_one_of_tendsto_of_positive_witness B
      (hessianBilin (iteratedDirectionalDerivative vs p) w) (𝓝[>] (0 : ℝ))
    · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
    · apply Filter.Eventually.mono (self_mem_nhdsWithin :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
      intro ε hε
      apply positive_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase
        (vs.map (fun v i => v i + ε)) (by simpa only [List.length_map] using hlen) ?_ w hw
      intro v hvmap i
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hvmap
      exact add_pos_of_nonneg_of_pos (hv u hu i) hε
    · intro x y
      exact tendsto_hessianBilin_iteratedDirectionalDerivative_add vs p w x y
    · exact hessianBilin_pos_of_nonnegativeCoefficients
        (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega)
        (hp.iteratedDirectionalDerivative vs hv) hz hw

/-- Homogeneous constants and linear polynomials have zero Hessian. -/
theorem hessianBilin_eq_zero_of_isHomogeneous_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hd : d ≤ 1)
    (w : ι → ℝ) : hessianBilin p w = 0 := by
  have hm : formalHessian p w = 0 := by
    ext i j
    have hj : (pderiv j p).IsHomogeneous 0 := by
      simpa only [show d - 1 = 0 by omega] using hhom.pderiv (i := j)
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hj
    change eval w (pderiv i (pderiv j p)) = 0
    rw [hj, pderiv_C, map_zero]
  simp only [hessianBilin, hm, map_zero]

/-- The coordinate-quadratic criterion controls arbitrary finite lists of
nonnegative directions, including derivatives of order beyond the degree. -/
theorem all_nonnegative_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  by_cases hlen : vs.length ≤ d - 2
  · exact nonnegative_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase vs hlen hv w hw
  · rw [hessianBilin_eq_zero_of_isHomogeneous_le_one
      (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega) w,
      sigPos_zero_bilinForm]
    exact Nat.zero_le 1

omit [Fintype ι] [DecidableEq ι] in
/-- Polynomial evaluation is continuous when the same scalar is added to every
coordinate. This finite-sum proof needs no topology on the polynomial ring. -/
theorem tendsto_eval_add_scalar (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    Tendsto (fun ε : ℝ => eval (fun i => w i + ε) p) (𝓝[>] (0 : ℝ))
      (𝓝 (eval w p)) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simp only [eval_eq]
  apply tendsto_finsetSum p.support
  intro m _
  apply Tendsto.mul tendsto_const_nhds
  apply tendsto_finsetProd m.support
  intro i _
  have hi : Tendsto (fun ε : ℝ => w i + ε) (𝓝[>] (0 : ℝ)) (𝓝 (w i)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := w i)).add heps
  exact hi.pow (m i)

/-- Pointwise Hessian closure as the evaluation vector approaches the boundary. -/
theorem tendsto_hessianBilin_add_scalar (p : MvPolynomial ι ℝ) (w x y : ι → ℝ) :
    Tendsto (fun ε : ℝ => hessianBilin p (fun i => w i + ε) x y) (𝓝[>] (0 : ℝ))
      (𝓝 (hessianBilin p w x y)) := by
  simp only [hessianBilin, Matrix.toBilin'_apply, formalHessian]
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((tendsto_const_nhds (x := x i)).mul
    (tendsto_eval_add_scalar (pderiv i (pderiv j p)) w)).mul
    (tendsto_const_nhds (x := y j))

/-- The full Hessian positive-index consequence of ALGV Theorem 3.2: all finite
nonnegative directional derivatives at all nonnegative evaluation vectors. -/
theorem complete_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
    hessianBilin (iteratedDirectionalDerivative vs p) (fun i => w i + ε)
  apply sigPos_le_one_of_tendsto B
    (hessianBilin (iteratedDirectionalDerivative vs p) w) (𝓝[>] (0 : ℝ))
  · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
  · apply Filter.Eventually.mono (self_mem_nhdsWithin :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
    intro ε hε
    exact all_nonnegative_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase vs hv
      (fun i => w i + ε) (fun i => add_pos_of_nonneg_of_pos (hw i) hε)
  · intro x y
    exact tendsto_hessianBilin_add_scalar (iteratedDirectionalDerivative vs p) w x y

#print axioms hessianBilin_eq_zero_of_isHomogeneous_le_one
#print axioms all_nonnegative_iterated_hessian_sigPos_le_one
#print axioms tendsto_eval_add_scalar
#print axioms tendsto_hessianBilin_add_scalar
#print axioms complete_hessian_sigPos_le_one

#print axioms tendsto_eval_iteratedDirectionalDerivative_add
#print axioms tendsto_hessianBilin_iteratedDirectionalDerivative_add
#print axioms nonnegative_iterated_hessian_sigPos_le_one

#print axioms hessian_sigPos_le_one_of_connectedPartialSupport
#print axioms directionalDerivative_sigPos_le_one_of_connectedPartialSupport
#print axioms positive_iterated_hessian_sigPos_le_one

#print axioms directionalDerivative_eq_zero_iff_of_pos
#print axioms ConnectedPartialSupport.directionalDerivative
#print axioms ConnectedPartialSupport.iteratedDirectionalDerivative

end StrongMasonAudit
