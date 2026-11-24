module

public import Hopf.Basic.NormalHopfIdeal
public import Hopf.Basic.AntipodeBialgHom
public import Hopf.Commutative.AugIdeal

/-!
# Restricting a normal Hopf ideal along an injective morphism of Hopf algebras

Let `f : A →ₐc[k] H` be an **injective** morphism of commutative Hopf algebras over a field `k`
and let `I` be a (normal) Hopf ideal of `H`.  This file shows that the restricted ideal
`f⁻¹(I)` is again a (normal) Hopf ideal of `A`, that its coinvariants map into the coinvariants
of `I`, and consequently that the ideal `K(f⁻¹ I)⁺A` is carried into `K(I)⁺H`.

The point is that over a field `A ⧸ f⁻¹(I) → H ⧸ I` is injective, so all the defining conditions
of a (normal) Hopf ideal, which are equalities in tensor products of `A` and `A ⧸ f⁻¹(I)`, may be
tested after applying the injective maps to the corresponding tensor products for `H`.

This is the ingredient which allows Takeuchi's Theorem 4.3 to be reduced to *finitely generated*
Hopf algebras: a commutative Hopf algebra is the directed union of its finitely generated
sub-Hopf algebras.

## Main definitions

## Main results

* `HopfAlgebra.Commutative.isHopfIdeal_comapIdeal`,
  `HopfAlgebra.Commutative.isNormalHopfIdeal_comapIdeal`;
* `HopfAlgebra.Commutative.mem_coinvLeft_of_mem_coinvLeft_comapIdeal`: the coinvariants of `f⁻¹(I)`
  are carried into those of `I`;
* `HopfAlgebra.Commutative.augIdeal_coinv_comapIdeal_le`: hence `K(f⁻¹ I)⁺A` is carried into
  `K(I)⁺H`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 4.3
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

universe u

variable {k A H : Type u} [Field k] [CommRing A] [CommRing H] [HopfAlgebra k A] [HopfAlgebra k H]

/-! ### Pushing Sweedler representations along a morphism of coalgebras -/

variable (f : A →ₐc[k] H)

/-- A morphism of Hopf algebras, as a `k`-linear map. -/
noncomputable def linMap : A →ₗ[k] H := (f : A →ₐ[k] H).toLinearMap
/-- `linMap f a = f a`. -/
@[simp] lemma linMap_apply (a : A) : linMap f a = f a := rfl

/-- `f` commutes with the comultiplications: `(f ⊗ f) (Δ x) = Δ (f x)`. -/
lemma map_comul (x : A) :
    TensorProduct.map (linMap f) (linMap f) (comul (R := k) (A := A) x)
      = comul (R := k) (A := H) (f x) := by
  have h := CoalgHomClass.map_comp_comul_apply f x
  rw [← h]
  congr 1

/-- The image under a morphism of coalgebras of a Sweedler representation of `x` is a Sweedler
representation of `f x`. -/
noncomputable def reprMap {x : A} {ι : Type*} (r : Coalgebra.Repr k x ι) :
    Coalgebra.Repr k (f x) ι where
  index := r.index
  left := fun i => f (r.left i)
  right := fun i => f (r.right i)
  eq := by
    calc ∑ i ∈ r.index, f (r.left i) ⊗ₜ[k] f (r.right i)
        = TensorProduct.map (linMap f) (linMap f)
            (∑ i ∈ r.index, r.left i ⊗ₜ[k] r.right i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => rfl
      _ = comul (R := k) (A := H) (f x) := by rw [r.eq]; exact map_comul f x

/-- A morphism of Hopf algebras commutes with the adjoint coaction. -/
lemma map_adAlgHom (x : A) :
    TensorProduct.map (linMap f) (linMap f) (adAlgHom k A x) = adAlgHom k H (f x) := by
  classical
  set r : Coalgebra.Repr k x (A × A) := Coalgebra.Repr.arbitrary k x with hr
  set r2 : ∀ i, Coalgebra.Repr k (r.right i) (A × A) :=
    fun i => Coalgebra.Repr.arbitrary k (r.right i) with hr2
  rw [adAlgHom_apply x r r2,
    adAlgHom_apply (f x) (reprMap f r) (fun i => reprMap f (r2 i))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change TensorProduct.map (linMap f) (linMap f)
      ((r.left i * antipode k ((r2 i).right j)) ⊗ₜ[k] ((r2 i).left j))
      = (f (r.left i) * antipode k (f ((r2 i).right j))) ⊗ₜ[k] (f ((r2 i).left j))
  rw [TensorProduct.map_tmul, linMap_apply, linMap_apply, map_mul, ← antipode_bialgHom_apply]

/-! ### The restricted ideal -/

variable (I : Ideal H)

/-- The restriction `f⁻¹(I)` of an ideal of `H` along a morphism of Hopf algebras. -/
def comapIdeal : Ideal A := Ideal.comap ((f : A →ₐ[k] H) : A →+* H) I

/-- `a ∈ f⁻¹(I) ↔ f a ∈ I` (true by definition). -/
lemma mem_comapIdeal {a : A} : a ∈ comapIdeal f I ↔ f a ∈ I := Iff.rfl

/-- The injection `A ⧸ f⁻¹(I) ↪ H ⧸ I`. -/
noncomputable def quotMap : (A ⧸ comapIdeal f I) →ₐ[k] (H ⧸ I) :=
  Ideal.quotientMapₐ I (f : A →ₐ[k] H) le_rfl

/-- `quotMap [a] = [f a]`. -/
@[simp] lemma quotMap_mk (a : A) :
    quotMap f I (Ideal.Quotient.mk (comapIdeal f I) a) = Ideal.Quotient.mk I (f a) := rfl

/-- The induced map `A ⧸ f⁻¹(I) → H ⧸ I` is injective. -/
lemma quotMap_injective : Function.Injective (quotMap f I) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [quotMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hz

/-! ### Commutation of the various tensor maps -/

/-- `(quotMap ⊗ quotMap) ∘ (π_A ⊗ π_A) = (π ⊗ π) ∘ (f ⊗ f)` on `A ⊗ A`, for the quotient maps
`π_A : A → A ⧸ f⁻¹(I)` and `π : H → H ⧸ I`. -/
lemma map_quotMap_comm (z : A ⊗[k] A) :
    TensorProduct.map (quotMap f I).toLinearMap (quotMap f I).toLinearMap
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (comapIdeal f I))
          (Ideal.Quotient.mkₐ k (comapIdeal f I)) z)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
          (TensorProduct.map (linMap f) (linMap f) z) := by
  induction z with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- `(f ⊗ quotMap) ∘ (id ⊗ π_A) = (id ⊗ π) ∘ (f ⊗ f)` on `A ⊗ A`, for the quotient maps
`π_A : A → A ⧸ f⁻¹(I)` and `π : H → H ⧸ I`. -/
lemma map_lTensorQuot_comm (z : A ⊗[k] A) :
    TensorProduct.map (linMap f) (quotMap f I).toLinearMap
        (lTensorQuot (comapIdeal f I) z)
      = lTensorQuot I (TensorProduct.map (linMap f) (linMap f) z) := by
  induction z with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-! ### The restricted ideal is a (normal) Hopf ideal -/

/-- The restriction of a Hopf ideal along an injective morphism of Hopf algebras is a Hopf
ideal. -/
theorem isHopfIdeal_comapIdeal (hI : IsHopfIdeal k I) : IsHopfIdeal k (comapIdeal f I) := by
  apply IsHopfIdeal.mk
  case hc =>
    intro a ha
    have h := IsHopfIdeal.counit_eq_zero k hI (f a) ha
    rwa [CoalgHomClass.counit_comp_apply f a] at h
  case hd =>
    intro a ha
    refine TensorProduct.map_injective_of_flat_flat (quotMap f I).toLinearMap
      (quotMap f I).toLinearMap (quotMap_injective f I) (quotMap_injective f I) ?_
    rw [map_quotMap_comm, map_zero, map_comul]
    exact IsHopfIdeal.comul_mem k hI (f a) ha
  case hs =>
    intro a ha
    rw [mem_comapIdeal, ← antipode_bialgHom_apply]
    exact IsHopfIdeal.antipode_mem k hI (f a) ha

/-- The restriction of a normal Hopf ideal along an injective morphism of Hopf algebras is a
normal Hopf ideal. -/
theorem isNormalHopfIdeal_comapIdeal (hf : Function.Injective f) (hI : IsNormalHopfIdeal k I) :
    IsNormalHopfIdeal k (comapIdeal f I) where
  toIsHopfIdeal := isHopfIdeal_comapIdeal f I hI.toIsHopfIdeal
  ad_mem := by
    intro a ha
    refine TensorProduct.map_injective_of_flat_flat (linMap f) (quotMap f I).toLinearMap
      (fun x y hxy => hf hxy) (quotMap_injective f I) ?_
    rw [map_lTensorQuot_comm, map_zero, map_adAlgHom]
    exact hI.ad_mem (f a) ha

/-! ### Coinvariants and augmentation ideals -/

/-- The coinvariants of the restricted ideal are carried into the coinvariants of `I`. -/
theorem mem_coinvLeft_of_mem_coinvLeft_comapIdeal {a : A}
    (ha : a ∈ (coinvLeft (comapIdeal f I) : Subalgebra k A)) :
    f a ∈ (coinvLeft I : Subalgebra k H) := by
  rw [mem_coinvLeft] at ha ⊢
  have h := congrArg (TensorProduct.map (linMap f) (quotMap f I).toLinearMap) ha
  rw [map_lTensorQuot_comm, map_comul, TensorProduct.map_tmul] at h
  rw [h]
  congr 1
  rw [AlgHom.toLinearMap_apply, map_one]

/-- The image of `K(f⁻¹ I)⁺A` lies in `K(I)⁺H`. -/
theorem augIdeal_coinv_comapIdeal_le {a : A}
    (ha : a ∈ augIdeal (coinvOfIdeal (k := k) (comapIdeal f I))) :
    f a ∈ augIdeal (coinvOfIdeal (k := k) I) := by
  have hsub : ((f : A →ₐ[k] H) : A →+* H) '' (augSet (coinvOfIdeal (k := k) (comapIdeal f I)))
      ⊆ (augIdeal (coinvOfIdeal (k := k) I) : Set H) := by
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine Ideal.subset_span ⟨?_, ?_⟩
    · exact mem_coinvLeft_of_mem_coinvLeft_comapIdeal f I hy1
    · exact (CoalgHomClass.counit_comp_apply f y).trans hy2
  have hmap : Ideal.map ((f : A →ₐ[k] H) : A →+* H) (augIdeal (coinvOfIdeal (k
      := k) (comapIdeal f I)))
      ≤ augIdeal (coinvOfIdeal (k := k) I) := by
    rw [augIdeal, Ideal.map_span, Ideal.span_le]
    exact hsub
  exact hmap (Ideal.mem_map_of_mem _ ha)

end HopfAlgebra.Commutative
end
