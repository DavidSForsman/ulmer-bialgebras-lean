module

public import Hopf.Commutative.FaithfulFlatnessFiniteType
public import Hopf.Basic.HopfLocallyFinite
public import Hopf.Basic.SubHopfMap

/-!
# Reduction of Takeuchi's theorem to finitely generated Hopf algebras

A commutative Hopf algebra over a field is the directed union of its finitely generated sub-Hopf
algebras (`HopfAlgebra.LocallyFinite.exists_finset_isSubHopfAlgebra`). Both halves of faithful
flatness are statements about finitely many elements at a time, so they descend from the finitely
generated case:

* *flatness* by the equational criterion: a relation `∑ cᵢ • xᵢ = 0` involves finitely many
  elements, hence lives in a pair of finitely generated sub-Hopf algebras `A₀ ⊆ A`, `B₀ ⊆ B` with
  `f A₀ ⊆ B₀`, over which it is trivial;
* *faithfulness*: if `m • B = B` for a maximal ideal `m` of `A`, then `1` is a finite combination
  `∑ aᵢ • bᵢ` with `aᵢ ∈ m`, so a proper ideal of some finitely generated `A₀` generates the unit
  ideal of some finitely generated `B₀`, contradicting faithful flatness there.

## Main results

* `HopfAlgebra.Commutative.exists_fg_square`: the pair of finitely generated sub-Hopf algebras;
* `HopfAlgebra.Commutative.faithfullyFlat_of_injective_algClosed`: Takeuchi's Theorem 3.1 over an
  algebraically closed field (using Cartier's theorem in characteristic zero).

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Sections 3.3, 11.4
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra HopfAlgebra.Commutative

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

universe u

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
  (f : A →ₐc[k] B)

/-- Any two finite subsets of `A` and of `B` are contained in finitely generated sub-Hopf algebras
`A₀ ⊆ A` and `B₀ ⊆ B` with `f A₀ ⊆ B₀`. -/
theorem exists_fg_square (SA : Finset A) (SB : Finset B) :
    ∃ (A₀ : Subalgebra k A) (B₀ : Subalgebra k B), ∃ (_ : IsSubHopfAlgebra k A₀)
      (_ : IsSubHopfAlgebra k B₀), Algebra.FiniteType k ↥A₀ ∧ Algebra.FiniteType k ↥B₀ ∧
      (∀ a ∈ SA, a ∈ A₀) ∧ (∀ b ∈ SB, b ∈ B₀) ∧ ∀ a ∈ A₀, f a ∈ B₀ := by
  classical
  obtain ⟨G, hG, hGS⟩ := HopfAlgebra.LocallyFinite.exists_finset_isSubHopfAlgebra (k := k) SA
  obtain ⟨G', hG', hGS'⟩ :=
    HopfAlgebra.LocallyFinite.exists_finset_isSubHopfAlgebra (k := k) (SB ∪ G.image (fun a => f a))
  refine ⟨Algebra.adjoin k (G : Set A), Algebra.adjoin k (G' : Set B), hG, hG',
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset G),
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset G'), hGS,
    fun b hb => hGS' b (Finset.mem_union_left _ hb), ?_⟩
  intro a ha
  have hle : Algebra.adjoin k (G : Set A)
      ≤ Subalgebra.comap (f : A →ₐ[k] B) (Algebra.adjoin k (G' : Set B)) := by
    refine Algebra.adjoin_le ?_
    intro y hy
    exact hGS' (f y) (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using hy, rfl⟩))
  exact hle ha

/-- A proper ideal of a ring over which a module is faithfully flat does not generate the whole
module. -/
lemma smul_top_ne_top_of_ne_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R M] {I : Ideal R} (hI : I ≠ ⊤) : I • (⊤ : Submodule R M) ≠ ⊤ := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  intro hcon
  refine Module.FaithfullyFlat.submodule_ne_top (R := R) (M := M) hm (top_le_iff.1 ?_)
  calc (⊤ : Submodule R M) = I • ⊤ := hcon.symm
    _ ≤ m • ⊤ := Submodule.smul_mono hIm le_rfl

section Sub

variable [IsAlgClosed k] (hinj : Function.Injective f)

include hinj in
/-- The restriction of `f` to a square of finitely generated sub-Hopf algebras is faithfully
flat, by Takeuchi's theorem for finitely generated Hopf algebras. -/
theorem faithfullyFlat_sub (hReduced : CharZeroReduced.{u}) (A₀ : Subalgebra k A)
    (B₀ : Subalgebra k B) [IsSubHopfAlgebra k A₀] [IsSubHopfAlgebra k B₀]
    [Algebra.FiniteType k ↥A₀] [Algebra.FiniteType k ↥B₀] (hsub : ∀ a ∈ A₀, f a ∈ B₀) :
    letI := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
    Module.FaithfullyFlat ↥A₀ ↥B₀ := by
  let := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
  have : IsScalarTower k ↥A₀ ↥B₀ := .of_algebraMap_eq fun r =>
    (((subBialgHom f A₀ B₀ hsub : (↥A₀) →ₐ[k] (↥B₀))).commutes r).symm
  exact faithfullyFlat_of_injective_finiteType hReduced (subBialgHom f A₀ B₀ hsub)
    (fun _ => rfl) (subBialgHom_injective f A₀ B₀ hsub hinj)

end Sub

section Main

variable [Algebra A B]

/-- Every element of `m • B` is a finite combination `∑ aᵢ • bᵢ` with `aᵢ ∈ m`. -/
lemma exists_finite_repr_of_mem_smul_top (m : Ideal A) {z : B}
    (hz : z ∈ m • (⊤ : Submodule A B)) :
    ∃ (n : ℕ) (a : Fin n → A) (b : Fin n → B), (∀ i, a i ∈ m) ∧ z = ∑ i, a i • b i := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr t _
    exact ⟨1, fun _ => r, fun _ => t, fun _ => hr, by simp⟩
  · rintro z w ⟨n, a, b, ha, rfl⟩ ⟨n', a', b', ha', rfl⟩
    refine ⟨n + n', Fin.append a a', Fin.append b b', ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact ha i
      · rw [Fin.append_right]; exact ha' i
    · rw [Fin.sum_univ_add]
      simp

variable (halg : ∀ a, algebraMap A B a = f a)

include halg in
/-- Coercion of the module structure: the `A₀`-action on `B₀` is the restriction of the
`A`-action on `B`. -/
lemma coe_sub_smul (A₀ : Subalgebra k A) (B₀ : Subalgebra k B) [IsSubHopfAlgebra k A₀]
    [IsSubHopfAlgebra k B₀] (hsub : ∀ a ∈ A₀, f a ∈ B₀) (a : ↥A₀) (b : ↥B₀) :
    letI := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
    ((a • b : ↥B₀) : B) = (a : A) • (b : B) := by
  let := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
  change ((algebraMap (↥A₀) (↥B₀) a * b : ↥B₀) : B) = (a : A) • (b : B)
  rw [Algebra.smul_def, halg, Subalgebra.coe_mul]
  rfl

variable [IsAlgClosed k] (hinj : Function.Injective f)

include halg hinj

/-- **Flatness**, by the equational criterion and the finitely generated case. -/
theorem flat_of_injective_algClosed (hReduced : CharZeroReduced.{u}) : Module.Flat A B := by
  classical
  -- the equational criterion: a relation `∑ cᵢ xᵢ = 0` in `B` is trivial
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l c x hx
  -- the relation lives in a square of finitely generated sub-Hopf algebras `A₀ → B₀`, where
  -- `B₀` is faithfully flat over `A₀`
  obtain ⟨A₀, B₀, hA₀, hB₀, hftA, hftB, hSA, hSB, hsub⟩ :=
    exists_fg_square f (Finset.image c Finset.univ) (Finset.image x Finset.univ)
  let := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
  have : Module.FaithfullyFlat ↥A₀ ↥B₀ := faithfullyFlat_sub f hinj hReduced A₀ B₀ hsub
  set c₀ : Fin l → ↥A₀ := fun i => ⟨c i, hSA _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩
    with hc₀
  set x₀ : Fin l → ↥B₀ := fun i => ⟨x i, hSB _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩
    with hx₀
  have hrel : ∑ i, c₀ i • x₀ i = 0 := by
    apply Subtype.ext
    have h : ((∑ i, c₀ i • x₀ i : ↥B₀) : B) = ∑ i, ((c₀ i • x₀ i : ↥B₀) : B) := by
      simp
    rw [h, ZeroMemClass.coe_zero, ← hx]
    exact Finset.sum_congr rfl fun i _ => coe_sub_smul f halg A₀ B₀ hsub (c₀ i) (x₀ i)
  -- so it is trivial over `A₀`, and its trivialization maps to one over `A`
  have key : Module.IsTrivialRelation c₀ x₀ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨n, a, y, hy1, hy2⟩ := key
  refine ⟨n, fun i j => ((a i j : A)), fun j => ((y j : B)), fun i => ?_, fun j => ?_⟩
  · have h := Subtype.ext_iff.1 (hy1 i)
    rw [show ((x₀ i : ↥B₀) : B) = x i from rfl] at h
    rw [h]
    have h2 : ((∑ j, a i j • y j : ↥B₀) : B) = ∑ j, ((a i j • y j : ↥B₀) : B) := by
      simp
    rw [h2]
    exact Finset.sum_congr rfl fun j _ => coe_sub_smul f halg A₀ B₀ hsub (a i j) (y j)
  · have h := Subtype.ext_iff.1 (hy2 j)
    have h2 : ((∑ i, c₀ i * a i j : ↥A₀) : A) = ∑ i, ((c₀ i : A) * (a i j : A)) := by
      simp
    rw [h2] at h
    simpa using h

/-- **Takeuchi's Theorem 3.1 over an algebraically closed field** ([Takeuchi1972]), for arbitrary
commutative Hopf algebras: an injective morphism `f : A →ₐc[k] B` of commutative Hopf algebras over
an algebraically closed field makes `B` faithfully flat over `A`.

In characteristic zero this uses Cartier's theorem, which enters through the hypothesis
`hReduced`. -/
theorem faithfullyFlat_of_injective_algClosed (hReduced : CharZeroReduced.{u}) :
    Module.FaithfullyFlat A B := by
  classical
  have : Module.Flat A B := flat_of_injective_algClosed f halg hinj hReduced
  refine ⟨fun {m} hm hcon => ?_⟩
  -- `1` lies in `m • B`
  have h1 : (1 : B) ∈ m • (⊤ : Submodule A B) := by rw [hcon]; trivial
  obtain ⟨n, a, b, ha, hab⟩ := exists_finite_repr_of_mem_smul_top m h1
  obtain ⟨A₀, B₀, hA₀, hB₀, hftA, hftB, hSA, hSB, hsub⟩ :=
    exists_fg_square f (Finset.image a Finset.univ) (Finset.image b Finset.univ)
  let := algebraOfBialgHom (subBialgHom f A₀ B₀ hsub)
  have : Module.FaithfullyFlat ↥A₀ ↥B₀ := faithfullyFlat_sub f hinj hReduced A₀ B₀ hsub
  set a₀ : Fin n → ↥A₀ := fun i => ⟨a i, hSA _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩
    with ha₀
  set b₀ : Fin n → ↥B₀ := fun i => ⟨b i, hSB _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩
    with hb₀
  -- the ideal of `A₀` generated by the `aᵢ` is proper
  set I₀ : Ideal ↥A₀ := Ideal.span (Set.range a₀) with hI₀
  have hI₀ne : I₀ ≠ ⊤ := by
    intro htop
    have h1' : (1 : ↥A₀) ∈ I₀ := htop ▸ Submodule.mem_top
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥A₀)).1 h1'
    have := Subtype.ext_iff.1 hcc
    have hcoe : ∀ i, ((cc i • a₀ i : ↥A₀) : A) = (cc i : A) * a i := by
      intro i
      rw [smul_eq_mul, Subalgebra.coe_mul]
    have h2 : ((∑ i, cc i • a₀ i : ↥A₀) : A) = ∑ i, (cc i : A) * (a i : A) := by
      rw [show ((∑ i, cc i • a₀ i : ↥A₀) : A) = ∑ i, ((cc i • a₀ i : ↥A₀) : A) from
        map_sum (A₀.subtype) _ Finset.univ]
      exact Finset.sum_congr rfl fun i _ => hcoe i
    rw [h2] at this
    have hmem : (1 : A) ∈ m := by
      rw [show (1 : A) = ∑ i, (cc i : A) * (a i : A) by simpa using this.symm]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (ha i)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem isUnit_one)
  -- but it generates the unit ideal of `B₀`
  refine smul_top_ne_top_of_ne_top (R := ↥A₀) (M := ↥B₀) hI₀ne ?_
  have hsum : (1 : ↥B₀) = ∑ i, a₀ i • b₀ i := by
    apply Subtype.ext
    have h : ((∑ i, a₀ i • b₀ i : ↥B₀) : B) = ∑ i, ((a₀ i • b₀ i : ↥B₀) : B) := by
      simp
    rw [OneMemClass.coe_one, h, hab]
    exact Finset.sum_congr rfl fun i _ =>
      (coe_sub_smul f halg A₀ B₀ hsub (a₀ i) (b₀ i)).symm
  refine top_le_iff.1 fun z _ => ?_
  have hz : z = ∑ i, a₀ i • (b₀ i * z) := by
    conv_lhs => rw [← one_mul z, hsum]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => smul_mul_assoc _ _ _
  rw [hz]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top

end Main

end HopfAlgebra.Commutative
end
