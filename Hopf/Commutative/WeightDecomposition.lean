module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Hopf.Commutative.RelInvGroupLike
public import Hopf.Basic.HopfQuotient
public import Hopf.Basic.ComoduleTransl
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The weight decomposition of a comodule spanned by relatively invariant vectors

Let `H` be a commutative Hopf algebra over a field `k` and `I` an ideal of `H`.  A vector `v` of
a right `H`-comodule `M` which is *relatively invariant modulo `I`* with character `g`
(`HopfAlgebra.Commutative.IsRelInvMod`) spans a line which is a subcomodule of `M` modulo `I`, of
character `ḡ`.

If `M` is spanned by such vectors, with group-like characters, then `M` decomposes into weight
spaces — group-like elements of `H/I` being linearly independent — and every weight admits a
*functional* carrying it: this is the step of Takeuchi's Lemma 4.15 which converts a
one-dimensional subcomodule into a one-dimensional quotient comodule.

## Main results

* `HopfAlgebra.Commutative.mk_comoduleCoeff_of_isRelInvMod`: the matrix coefficient of a relatively
  invariant vector is `⟨θ, v⟩ ḡ` modulo `I`;
* `HopfAlgebra.Commutative.transl_of_isRelInvMod`: a relatively invariant vector is an eigenvector
  of the translation operators factoring through `H/I`;
* `HopfAlgebra.Commutative.exists_charFunctional_of_weights`: if a comodule is spanned by finitely
  many vectors which are relatively invariant modulo `I` with group-like characters, then every
  non-zero relatively invariant vector with a group-like character is carried by a functional of the
  same character.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {M : Type u} [AddCommGroup M] [Module k M] [RightComodule k H M]

/-- The matrix coefficient of a relatively invariant vector against a functional is a multiple of
its character modulo `I`. -/
theorem mk_comoduleCoeff_of_isRelInvMod {I : Ideal H} {m : M} {g : H}
    (hm : IsRelInvMod k I m g) (θ : Module.Dual k M) :
    Ideal.Quotient.mk I (comoduleCoeff θ m) = θ m • Ideal.Quotient.mk I g := by
  rw [comoduleCoeff, quot_contractFst, hm, contractFstQuot_tmul]

/-- A vector which is relatively invariant modulo `I` with character `g` is an eigenvector of
every translation operator by a functional factoring through `H/I`. -/
theorem transl_of_isRelInvMod {I : Ideal H} {m : M} {g : H} (hm : IsRelInvMod k I m g)
    (φ : (H ⧸ I) →ₗ[k] k) :
    Coalgebra.Comodule.transl (R := k) (C := H) (φ ∘ₗ (Ideal.Quotient.mkₐ k I).toLinearMap) m
      = φ (Ideal.Quotient.mk I g) • m := by
  have hlt : LinearMap.lTensor M (φ ∘ₗ (Ideal.Quotient.mkₐ k I).toLinearMap)
      = LinearMap.lTensor M φ ∘ₗ
        LinearMap.lTensor M (Ideal.Quotient.mkₐ k I).toLinearMap := by
    rw [← LinearMap.lTensor_comp]
  rw [Coalgebra.Comodule.transl]
  simp only [hlt, LinearMap.comp_apply]
  rw [hm]
  simp

/-- If `x` does not lie in a subspace `W` of a vector space, some functional is `1` at `x` and
vanishes on `W`. -/
theorem exists_dual_eq_one_of_notMem {V : Type u} [AddCommGroup V] [Module k V]
    (W : Submodule k V) {x : V} (hx : x ∉ W) :
    ∃ φ : Module.Dual k V, φ x = 1 ∧ ∀ y ∈ W, φ y = 0 := by
  have hne : W.mkQ x ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using hx
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hne
  refine ⟨ψ ∘ₗ W.mkQ, hψ, fun y hy => ?_⟩
  have : W.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero W).2 hy
  simp [this]

/-- A group-like element does not lie in the span of a set of group-like elements different from
it. -/
theorem notMem_span_of_isGroupLikeElem {A : Type u} [AddCommGroup A] [Module k A]
    [Coalgebra k A] {x : A} (hx : IsGroupLikeElem k x) (S : Set A)
    (hS : ∀ y ∈ S, IsGroupLikeElem k y ∧ y ≠ x) : x ∉ Submodule.span k S := by
  intro hmem
  have hsub : S ⊆ {a | IsGroupLikeElem k a} \ {x} := by
    intro y hy
    exact ⟨(hS y hy).1, by simpa using (hS y hy).2⟩
  have hspan : Submodule.span k S ≤
      Submodule.span k (id '' ({a : A | IsGroupLikeElem k a} \ {x})) := by
    refine Submodule.span_mono ?_
    simpa using hsub
  exact (linearIndepOn_isGroupLikeElem (R := k) (A := A)).notMem_span (i := x) hx (hspan hmem)

/-- The character property `mk (coeff θ y) = θ y • mk g` extends from a set to its span. -/
theorem mk_comoduleCoeff_eq_smul_of_mem_span {I : Ideal H} (θ : Module.Dual k M) (g : H)
    (S : Set M)
    (hS : ∀ y ∈ S, Ideal.Quotient.mk I (comoduleCoeff θ y) = θ y • Ideal.Quotient.mk I g)
    {m : M} (hm : m ∈ Submodule.span k S) :
    Ideal.Quotient.mk I (comoduleCoeff θ m) = θ m • Ideal.Quotient.mk I g := by
  refine Submodule.span_induction
    (p := fun y _ => Ideal.Quotient.mk I (comoduleCoeff θ y) = θ y • Ideal.Quotient.mk I g)
    hS ?_ ?_ ?_ hm
  · simp [comoduleCoeff]
  · intro a b _ _ ha hb
    have hadd : comoduleCoeff (H := H) θ (a + b)
        = comoduleCoeff (H := H) θ a + comoduleCoeff (H := H) θ b := by
      simp [comoduleCoeff]
    rw [hadd, map_add, ha, hb, map_add, add_smul]
  · intro t a _ ha
    have hsmul : comoduleCoeff (H := H) θ (t • a) = t • comoduleCoeff (H := H) θ a := by
      simp [comoduleCoeff]
    have hmk : Ideal.Quotient.mk I (t • comoduleCoeff (H := H) θ a)
        = t • Ideal.Quotient.mk I (comoduleCoeff (H := H) θ a) :=
      map_smul (Ideal.Quotient.mkₐ k I).toLinearMap t _
    rw [hsmul, hmk, ha, map_smul, smul_smul, smul_eq_mul]

/-- **The weight functional.**  Let `M` be a right `H`-comodule spanned by finitely many vectors
`s i` which are relatively invariant modulo `I` with group-like characters `c i`, and let `v` be
a non-zero vector of `M` which is relatively invariant with a group-like character `g`.  Then `M`
carries a functional `θ` with `⟨θ, v⟩ = 1` all of whose matrix coefficients are multiples of `g`
modulo `I` — the character `ḡ` is realised on a one-dimensional *quotient* of `M`. -/
theorem exists_charFunctional_of_weights (I : Ideal H) [Fact (IsHopfIdeal k I)] {n : ℕ}
    (s : Fin n → M)
    (hspan : Submodule.span k (Set.range s) = ⊤)
    (c : Fin n → H) (hc : ∀ i, IsRelInvMod k I (s i) (c i))
    (hcgl : ∀ i, IsGroupLikeElem k (Ideal.Quotient.mk I (c i)))
    {v : M} {g : H} (hv : IsRelInvMod k I v g)
    (hg : IsGroupLikeElem k (Ideal.Quotient.mk I g)) (hv0 : v ≠ 0) :
    ∃ θ : Module.Dual k M, θ v = 1 ∧
      ∀ m : M, Ideal.Quotient.mk I (comoduleCoeff θ m) = θ m • Ideal.Quotient.mk I g := by
  classical
  set J : Finset (Fin n) :=
    Finset.univ.filter (fun i => Ideal.Quotient.mk I (c i) ≠ Ideal.Quotient.mk I g) with hJ
  set W : Submodule k M := Submodule.span k (s '' (J : Set (Fin n))) with hW
  -- a functional on `H/I` separating the character of `v` from the other characters
  obtain ⟨φ, hφg, hφJ⟩ : ∃ φ : (H ⧸ I) →ₗ[k] k, φ (Ideal.Quotient.mk I g) = 1 ∧
      ∀ i ∈ J, φ (Ideal.Quotient.mk I (c i)) = 0 := by
    have hnot : Ideal.Quotient.mk I g ∉
        Submodule.span k ((fun i => Ideal.Quotient.mk I (c i)) '' (J : Set (Fin n))) := by
      refine notMem_span_of_isGroupLikeElem hg _ ?_
      rintro y ⟨i, hi, rfl⟩
      refine ⟨hcgl i, ?_⟩
      have : Ideal.Quotient.mk I (c i) ≠ Ideal.Quotient.mk I g := by
        simpa [hJ] using hi
      exact this
    obtain ⟨φ, hφ1, hφ0⟩ := exists_dual_eq_one_of_notMem _ hnot
    exact ⟨φ, hφ1, fun i hi => hφ0 _ (Submodule.subset_span ⟨i, hi, rfl⟩)⟩
  -- `v` is not in the span of the other weight vectors
  have hvW : v ∉ W := by
    intro hmem
    set w : H →ₗ[k] k := φ ∘ₗ (Ideal.Quotient.mkₐ k I).toLinearMap with hw
    have hzero : ∀ x ∈ W, Coalgebra.Comodule.transl (R := k) (C := H) w x = 0 := by
      intro x hx
      refine LinearMap.mem_ker.1 ((Submodule.span_le (p := LinearMap.ker _)).2 ?_ hx)
      rintro y ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hw, transl_of_isRelInvMod (hc i) φ,
        hφJ i (by simpa using hi), zero_smul]
    have h1 := hzero v hmem
    rw [hw, transl_of_isRelInvMod hv φ, hφg, one_smul] at h1
    exact hv0 h1
  -- a functional cutting out that weight
  obtain ⟨θ, hθv, hθW⟩ := exists_dual_eq_one_of_notMem W hvW
  refine ⟨θ, hθv, fun m => ?_⟩
  -- the character property holds on the spanning family, hence everywhere
  have hm : m ∈ Submodule.span k (Set.range s) := by rw [hspan]; trivial
  refine mk_comoduleCoeff_eq_smul_of_mem_span θ g _ ?_ hm
  rintro y ⟨i, rfl⟩
  rw [mk_comoduleCoeff_of_isRelInvMod (hc i) θ]
  by_cases hi : i ∈ J
  · have hzero : θ (s i) = 0 := hθW _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [hzero, zero_smul, zero_smul]
  · have : Ideal.Quotient.mk I (c i) = Ideal.Quotient.mk I g := by
      by_contra hne
      exact hi (by simpa [hJ] using hne)
    rw [this]

end HopfAlgebra.Commutative
end
