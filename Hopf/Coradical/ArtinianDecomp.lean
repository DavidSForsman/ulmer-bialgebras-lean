module

public import Mathlib.RingTheory.Artinian.Ring

/-!
# Powers of the maximal ideals of a commutative Artinian ring

This file collects the commutative-algebra input for Kostant's decomposition theorem.  Let `A` be
a commutative Artinian ring.  It has only finitely many maximal ideals, and its Jacobson radical
`J = ⋂ M` is nilpotent, say `J^N = 0` with `N ≥ 1`.  Since distinct maximal ideals are comaximal,
so are their `N`-th powers, whence

```
⋂_{M maximal} M^N = ∏_{M maximal} M^N = (⋂_{M maximal} M)^N = J^N = 0 .
```

Two consequences are recorded: the powers `M^n` stabilise at `n = N`, and `M^N` is comaximal with
the intersection of the `T^N` for the *other* maximal ideals `T`.  Dually (in
`Hopf/Coradical/PointedDecomposition.lean`) these say that a finite-dimensional cocommutative
coalgebra is the direct sum of the irreducible components of its simple subcoalgebras.

## Main results

* `Coalgebra.Coradical.ArtinianAux.exists_inf_pow_maximal_eq_bot`;
* `Coalgebra.Coradical.ArtinianAux.pow_succ_eq_pow`;
* `Coalgebra.Coradical.ArtinianAux.sup_biInf_ne_eq_top`.

## References

* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 8
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
-/

@[expose] public section

namespace Coalgebra.Coradical.ArtinianAux

variable {A : Type*} [CommRing A]

/-- For a finite family of pairwise comaximal ideals, intersection equals product. -/
theorem finset_inf_eq_prod_of_isCoprime (s : Finset (Ideal A)) (f : Ideal A → Ideal A)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) : s.inf f = s.prod f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.inf_insert, Finset.prod_insert ha]
      have hcop : IsCoprime (f a) (s.inf f) := by
        rw [Finset.inf_eq_iInf]
        refine Ideal.isCoprime_biInf (s := s) ?_
        intro j hj
        exact h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      rw [ih (fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij)] at hcop ⊢
      exact (Ideal.mul_eq_inf_of_isCoprime hcop).symm

/-- Powers `M ^ n` and `T ^ n` of distinct maximal ideals are coprime. -/
theorem isCoprime_pow_of_ne {M T : Ideal A} (hM : M.IsMaximal) (hT : T.IsMaximal) (h : M ≠ T)
    (n : ℕ) : IsCoprime (M ^ n) (T ^ n) :=
  IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 (hM.coprime_of_ne hT h))

variable (A) in
/-- The (finite) set of maximal ideals of a commutative Artinian ring. -/
noncomputable def maximalFinset [IsArtinianRing A] : Finset (Ideal A) :=
  (IsArtinianRing.setOfPred_isMaximal_finite A).toFinset

variable [IsArtinianRing A]

/-- An ideal lies in `maximalFinset A` iff it is maximal. -/
@[simp] theorem mem_maximalFinset {M : Ideal A} : M ∈ maximalFinset A ↔ M.IsMaximal := by
  rw [maximalFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The intersection of the maximal ideals of a commutative Artinian ring is its Jacobson
radical. -/
theorem inf_maximalFinset_id : (maximalFinset A).inf id = Ideal.jacobson (⊥ : Ideal A) := by
  rw [Finset.inf_id_eq_sInf, Ideal.jacobson]
  congr 1
  ext M
  simp

/-- **Some common power of all the maximal ideals vanishes**: there is `N ≥ 1` with
`⋂_M M^N = 0`. -/
theorem exists_inf_pow_maximal_eq_bot :
    ∃ N : ℕ, 0 < N ∧ (maximalFinset A).inf (fun M => M ^ N) = ⊥ := by
  obtain ⟨N, hN⟩ : IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) :=
    Ideal.jacobson_bot (R := A) ▸ IsArtinianRing.isNilpotent_jacobson A
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hcop : ∀ i ∈ maximalFinset A, ∀ j ∈ maximalFinset A, i ≠ j →
      IsCoprime (i ^ (N + 1)) (j ^ (N + 1)) := fun i hi j hj hij =>
    isCoprime_pow_of_ne (mem_maximalFinset.1 hi) (mem_maximalFinset.1 hj) hij _
  rw [finset_inf_eq_prod_of_isCoprime _ _ hcop, Finset.prod_pow]
  have hprod : (maximalFinset A).prod id = Ideal.jacobson (⊥ : Ideal A) := by
    rw [← inf_maximalFinset_id, finset_inf_eq_prod_of_isCoprime]
    intro i hi j hj hij
    exact Ideal.isCoprime_iff_sup_eq.2
      ((mem_maximalFinset.1 hi).coprime_of_ne (mem_maximalFinset.1 hj) hij)
  simp only [id] at hprod
  rw [hprod, pow_succ, hN]
  simp

/-- `M^n` is comaximal with the intersection of the `n`-th powers of the other maximal ideals. -/
theorem sup_biInf_ne_eq_top {M : Ideal A} (hM : M.IsMaximal) (n : ℕ) :
    M ^ n ⊔ (⨅ T ∈ {T : Ideal A | T.IsMaximal ∧ T ≠ M}, T ^ n) = ⊤ := by
  classical
  have hle : (⨅ T ∈ (maximalFinset A).erase M, T ^ n)
      ≤ ⨅ T ∈ {T : Ideal A | T.IsMaximal ∧ T ≠ M}, T ^ n := by
    refine le_iInf₂ fun T hT => ?_
    exact iInf₂_le T (Finset.mem_erase.2 ⟨hT.2, mem_maximalFinset.2 hT.1⟩)
  refine eq_top_iff.2 (le_trans (le_of_eq ?_) (sup_le_sup_left hle _))
  refine (Ideal.isCoprime_iff_sup_eq.1 (Ideal.isCoprime_biInf ?_)).symm
  intro T hT
  exact isCoprime_pow_of_ne hM (mem_maximalFinset.1 (Finset.mem_of_mem_erase hT))
    (Ne.symm (Finset.ne_of_mem_erase hT)) n

section Fixed

variable {N : ℕ} (hN : (maximalFinset A).inf (fun M => M ^ N) = ⊥)
include hN

/-- An element lying in `M^N` for every maximal ideal `M` is zero. -/
theorem eq_zero_of_mem_pow_maximal {x : A} (hx : ∀ M : Ideal A, M.IsMaximal → x ∈ M ^ N) :
    x = 0 := by
  have hxs : x ∈ (maximalFinset A).inf (fun M => M ^ N) := by
    rw [Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf]
    intro M hM
    exact hx M (mem_maximalFinset.1 hM)
  rw [hN] at hxs
  simpa using hxs

/-- The powers of a maximal ideal of a commutative Artinian ring stabilise at the exponent `N`
for which `⋂_M M^N = 0`. -/
theorem pow_succ_eq_pow (hN1 : 0 < N) {M : Ideal A} (hM : M.IsMaximal) :
    M ^ (N + 1) = M ^ N := by
  refine le_antisymm (Ideal.pow_le_pow_right (Nat.le_succ N)) ?_
  have htop := sup_biInf_ne_eq_top hM N
  have h1 : (1 : A) ∈ M ^ N ⊔ (⨅ T ∈ {T : Ideal A | T.IsMaximal ∧ T ≠ M}, T ^ N) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  intro x hx
  have hxab : x = a * x + b * x := by
    rw [← add_mul, hab, one_mul]
  have hbx : b * x = 0 := by
    refine eq_zero_of_mem_pow_maximal hN fun T hT => ?_
    by_cases hTM : T = M
    · subst hTM
      exact Ideal.mul_mem_left _ _ hx
    · simp only [Submodule.mem_iInf] at hb
      exact Ideal.mul_mem_right _ _ (hb T ⟨hT, hTM⟩)
  have hax : a * x ∈ M ^ (N + 1) := by
    have hmem : a * x ∈ M ^ N * M ^ N := Ideal.mul_mem_mul ha hx
    have hle : M ^ N * M ^ N ≤ M ^ (N + 1) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    exact hle hmem
  rw [hxab, hbx, add_zero]
  exact hax

/-- All powers beyond `N` agree with `M^N`. -/
theorem pow_add_eq_pow (hN1 : 0 < N) {M : Ideal A} (hM : M.IsMaximal) (j : ℕ) :
    M ^ (N + j) = M ^ N := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show N + (j + 1) = (N + j) + 1 from rfl, pow_succ, ih, ← pow_succ,
        pow_succ_eq_pow hN hN1 hM]

/-- `M^N` is contained in every power of `M`. -/
theorem pow_le_pow_maximal (hN1 : 0 < N) {M : Ideal A} (hM : M.IsMaximal) (n : ℕ) :
    M ^ N ≤ M ^ n := by
  rcases le_or_gt n N with h | h
  · exact Ideal.pow_le_pow_right h
  · have : n = N + (n - N) := by omega
    rw [this, pow_add_eq_pow hN hN1 hM]

end Fixed

end Coalgebra.Coradical.ArtinianAux
