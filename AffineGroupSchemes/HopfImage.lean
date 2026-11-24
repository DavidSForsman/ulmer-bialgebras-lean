module

public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.AntipodeBialgHom

/-!
# The image of a morphism of commutative Hopf algebras over a field

This file contains the "surjection/injection factorization" half of Theorem 3.12 of
[forsman2026semiabeliannessaffinegroupschemes]: every morphism of commutative Hopf algebras over a
*field* factors as a surjective morphism of Hopf algebras followed by an injective one.

The construction is carried out in the following generality.  Let `f : A →ₐc[k] B` be a morphism
of Hopf algebras over a field `k`, and suppose `f` is factored as `m ∘ e` with `e : A →ₐ[k] S`
a surjection of algebras and `m : S →ₐ[k] B` an injection.  Then `S` carries a (unique) Hopf
algebra structure making both `e` and `m` morphisms of Hopf algebras.  Applying this to the
image `S = range f` gives the factorization.

The comultiplication of `S` is obtained by transporting `comul` along `e`: this is well defined
because `m ⊗ m` is injective (over a field the tensor product of injections is injective), and
the antipode of `S` is obtained in the same way, using that a morphism of bialgebras between
Hopf algebras commutes with the antipodes (`HopfAlgebra.antipode_bialgHom_apply`).

## Main results

* `AffineGroupSchemes.HopfImage.imageHopfAlgebra`: the Hopf algebra structure on `S` transported
  along the factorization `f = m ∘ e`.
* `AffineGroupSchemes.exists_hopfAlgebra_image_factorization`: every morphism of commutative Hopf
  algebras over a field factors as `m ∘ e` with `e` a surjective and `m` an injective morphism of
  Hopf algebras.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.4
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra Function

namespace AffineGroupSchemes


universe u v w

namespace HopfImage

variable {k A B S : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing S]
  [HopfAlgebra k A] [HopfAlgebra k B] [Algebra k S]
  (e : A →ₐ[k] S) (he : Surjective e) (sec : S →ₗ[k] A) (hsec : ∀ s, e (sec s) = s)
  (f : A →ₐc[k] B) (m : S →ₐ[k] B)
  (hm : Injective m) (hcomp : ∀ a, m (e a) = f a)

/-- The comultiplication of the image of `f`, transported from `A` along `e`. -/
noncomputable def imageComul : S →ₗ[k] S ⊗[k] S :=
  TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ comul ∘ₗ sec

/-- The counit of the image of `f`, restricted from `B` along `m`. -/
noncomputable def imageCounit : S →ₗ[k] k := (counit : B →ₗ[k] k) ∘ₗ m.toLinearMap

/-- The antipode of the image of `f`, transported from `A` along `e`. -/
noncomputable def imageAntipode : S →ₗ[k] S :=
  e.toLinearMap ∘ₗ (antipode k : A →ₗ[k] A) ∘ₗ sec

include hcomp in
/-- Given `m ∘ e = f`, `(m ⊗ m) ∘ (e ⊗ e) = f ⊗ f` on `A ⊗[k] A`. -/
lemma map_e_map_e (x : A ⊗[k] A) :
    TensorProduct.map m.toLinearMap m.toLinearMap
        (TensorProduct.map e.toLinearMap e.toLinearMap x)
      = TensorProduct.map (f : A →ₗc[k] B).toLinearMap (f : A →ₗc[k] B).toLinearMap x := by
  induction x with
  | tmul a b => simp [hcomp]
  | add u v hu hv => simp [hu, hv]

/-- `(f ⊗ f) (Δ a) = Δ (f a)`. -/
lemma map_f_comul (a : A) :
    TensorProduct.map (f : A →ₗc[k] B).toLinearMap (f : A →ₗc[k] B).toLinearMap (comul a)
      = comul (f a) := by
  simp

include hsec hm hcomp in
/-- The defining property of the comultiplication of the image: `e` is a morphism of
coalgebras. -/
lemma imageComul_e [IsAbsFlat k] (a : A) :
    imageComul e sec (e a) = TensorProduct.map e.toLinearMap e.toLinearMap (comul a) := by
  apply TensorProduct.map_injective_of_flat_flat m.toLinearMap m.toLinearMap hm hm
  simp only [imageComul, LinearMap.comp_apply, map_e_map_e e f m hcomp, map_f_comul]
  rw [← hcomp, ← hcomp, hsec]

include hcomp in
/-- The defining property of the counit of the image. -/
lemma imageCounit_e (a : A) : imageCounit (k := k) m (e a) = counit a := by
  simp [imageCounit, hcomp]

include hsec hm hcomp in
/-- The defining property of the antipode of the image: `e` commutes with the antipodes. -/
lemma imageAntipode_e (a : A) : imageAntipode e sec (e a) = e (antipode k a) := by
  apply hm
  simp only [imageAntipode, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    hcomp]
  rw [← antipode_bialgHom_apply, ← antipode_bialgHom_apply, ← hcomp, ← hcomp, hsec]

/-! ### Naturality lemmas -/

include hsec hm hcomp in
/-- `(imageComul ⊗ id) ∘ (e ⊗ e) = ((e ⊗ e) ⊗ e) ∘ (Δ ⊗ id)` on `A ⊗[k] A`. -/
lemma rTensor_imageComul [IsAbsFlat k] (x : A ⊗[k] A) :
    TensorProduct.map (imageComul e sec) LinearMap.id
        (TensorProduct.map e.toLinearMap e.toLinearMap x)
      = TensorProduct.map (TensorProduct.map e.toLinearMap e.toLinearMap) e.toLinearMap
          (TensorProduct.map (comul (R := k) (A := A)) LinearMap.id x) := by
  induction x with
  | tmul a b => simp [imageComul_e e sec hsec f m hm hcomp]
  | add u v hu hv => simp [hu, hv]

include hsec hm hcomp in
/-- `(id ⊗ imageComul) ∘ (e ⊗ e) = (e ⊗ (e ⊗ e)) ∘ (id ⊗ Δ)` on `A ⊗[k] A`. -/
lemma lTensor_imageComul [IsAbsFlat k] (x : A ⊗[k] A) :
    TensorProduct.map LinearMap.id (imageComul e sec)
        (TensorProduct.map e.toLinearMap e.toLinearMap x)
      = TensorProduct.map e.toLinearMap (TensorProduct.map e.toLinearMap e.toLinearMap)
          (TensorProduct.map LinearMap.id (comul (R := k) (A := A)) x) := by
  induction x with
  | tmul a b => simp [imageComul_e e sec hsec f m hm hcomp]
  | add u v hu hv => simp [hu, hv]

include hcomp in
/-- `(imageCounit ⊗ id) ∘ (e ⊗ e) = (id ⊗ e) ∘ (ε ⊗ id)` on `A ⊗[k] A`. -/
lemma rTensor_imageCounit (x : A ⊗[k] A) :
    TensorProduct.map (imageCounit (k := k) m) LinearMap.id
        (TensorProduct.map e.toLinearMap e.toLinearMap x)
      = TensorProduct.map LinearMap.id e.toLinearMap
          (TensorProduct.map (counit (R := k) (A := A)) LinearMap.id x) := by
  induction x with
  | tmul a b => simp [imageCounit_e e f m hcomp]
  | add u v hu hv => simp [hu, hv]

include hcomp in
/-- `(id ⊗ imageCounit) ∘ (e ⊗ e) = (e ⊗ id) ∘ (id ⊗ ε)` on `A ⊗[k] A`. -/
lemma lTensor_imageCounit (x : A ⊗[k] A) :
    TensorProduct.map LinearMap.id (imageCounit (k := k) m)
        (TensorProduct.map e.toLinearMap e.toLinearMap x)
      = TensorProduct.map e.toLinearMap LinearMap.id
          (TensorProduct.map LinearMap.id (counit (R := k) (A := A)) x) := by
  induction x with
  | tmul a b => simp [imageCounit_e e f m hcomp]
  | add u v hu hv => simp [hu, hv]

/-! ### The coalgebra axioms -/

include he hsec hm hcomp in
/-- Coassociativity of `imageComul e sec`. -/
lemma image_coassoc [IsAbsFlat k] :
    TensorProduct.assoc k S S S ∘ₗ (imageComul e sec).rTensor S ∘ₗ imageComul e sec
      = (imageComul e sec).lTensor S ∘ₗ imageComul e sec := by
  apply LinearMap.ext; intro s; obtain ⟨a, rfl⟩ := he s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor, LinearMap.lTensor,
    imageComul_e e sec hsec f m hm hcomp, rTensor_imageComul e sec hsec f m hm hcomp,
    lTensor_imageComul e sec hsec f m hm hcomp, LinearEquiv.coe_coe]
  rw [← TensorProduct.map_map_assoc]
  congr 1
  exact Coalgebra.coassoc_apply a

include he hsec hm hcomp in
/-- Left counit law: `(imageCounit ⊗ id) ∘ imageComul = (s ↦ 1 ⊗ s)`. -/
lemma image_rTensor_counit [IsAbsFlat k] :
    (imageCounit (k := k) m).rTensor S ∘ₗ imageComul e sec = TensorProduct.mk k k S 1 := by
  apply LinearMap.ext; intro s; obtain ⟨a, rfl⟩ := he s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor,
    imageComul_e e sec hsec f m hm hcomp, rTensor_imageCounit e f m hcomp, TensorProduct.mk_apply]
  rw [show TensorProduct.map (counit (R := k) (A := A)) LinearMap.id (comul a) = 1 ⊗ₜ[k] a from
    Coalgebra.rTensor_counit_comul a]
  simp

include he hsec hm hcomp in
/-- Right counit law: `(id ⊗ imageCounit) ∘ imageComul = (s ↦ s ⊗ 1)`. -/
lemma image_lTensor_counit [IsAbsFlat k] :
    (imageCounit (k := k) m).lTensor S ∘ₗ imageComul e sec = (TensorProduct.mk k S k).flip 1 := by
  apply LinearMap.ext; intro s; obtain ⟨a, rfl⟩ := he s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor,
    imageComul_e e sec hsec f m hm hcomp, lTensor_imageCounit e f m hcomp, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  rw [show TensorProduct.map LinearMap.id (counit (R := k) (A := A)) (comul a) = a ⊗ₜ[k] 1 from
    Coalgebra.lTensor_counit_comul a]
  simp

/-! ### The bialgebra axioms -/

/-- The algebra map `e ⊗ e` has underlying linear map `TensorProduct.map e e`. -/
lemma map_e_e_eq : (Algebra.TensorProduct.map e e).toLinearMap
    = TensorProduct.map e.toLinearMap e.toLinearMap := by
  ext
  simp

/-- `e ⊗ e` sends `1` to `1`. -/
lemma map_e_e_one : TensorProduct.map e.toLinearMap e.toLinearMap (1 : A ⊗[k] A) = 1 := by
  rw [← map_e_e_eq e]
  exact map_one (Algebra.TensorProduct.map e e)

/-- `e ⊗ e` is multiplicative. -/
lemma map_e_e_mul (x y : A ⊗[k] A) :
    TensorProduct.map e.toLinearMap e.toLinearMap (x * y)
      = TensorProduct.map e.toLinearMap e.toLinearMap x
        * TensorProduct.map e.toLinearMap e.toLinearMap y := by
  rw [← map_e_e_eq e]
  exact map_mul (Algebra.TensorProduct.map e e) x y

/-- `imageCounit m 1 = 1`. -/
lemma image_counit_one : imageCounit (k := k) m (1 : S) = 1 := by
  simp [imageCounit]

/-- `imageCounit m` is multiplicative. -/
lemma image_counit_mul (s t : S) :
    imageCounit (k := k) m (s * t) = imageCounit (k := k) m s * imageCounit (k := k) m t := by
  simp [imageCounit, Bialgebra.counit_mul]

include hsec hm hcomp in
/-- `imageComul e sec 1 = 1`. -/
lemma image_comul_one [IsAbsFlat k] : imageComul e sec (1 : S) = 1 := by
  rw [show (1 : S) = e 1 from (map_one e).symm, imageComul_e e sec hsec f m hm hcomp,
    Bialgebra.comul_one, map_e_e_one e]

include he hsec hm hcomp in
/-- `imageComul e sec` is multiplicative. -/
lemma image_comul_mul [IsAbsFlat k] (s t : S) :
    imageComul e sec (s * t) = imageComul e sec s * imageComul e sec t := by
  obtain ⟨a, rfl⟩ := he s
  obtain ⟨b, rfl⟩ := he t
  rw [← map_mul e, imageComul_e e sec hsec f m hm hcomp, imageComul_e e sec hsec f m hm hcomp,
    imageComul_e e sec hsec f m hm hcomp, Bialgebra.comul_mul, map_e_e_mul e]

/-! ### The antipode axioms -/

include hsec hm hcomp in
/-- `μ ∘ (imageAntipode ⊗ id) ∘ (e ⊗ e) = e ∘ μ ∘ (S ⊗ id)` on `A ⊗[k] A`. -/
lemma mul_rTensor_imageAntipode (x : A ⊗[k] A) :
    LinearMap.mul' k S (TensorProduct.map (imageAntipode e sec) LinearMap.id
        (TensorProduct.map e.toLinearMap e.toLinearMap x))
      = e (LinearMap.mul' k A (TensorProduct.map (antipode k) LinearMap.id x)) := by
  induction x with
  | tmul a b => simp [imageAntipode_e e sec hsec f m hm hcomp]
  | add u v hu hv => simp [hu, hv]

include hsec hm hcomp in
/-- `μ ∘ (id ⊗ imageAntipode) ∘ (e ⊗ e) = e ∘ μ ∘ (id ⊗ S)` on `A ⊗[k] A`. -/
lemma mul_lTensor_imageAntipode (x : A ⊗[k] A) :
    LinearMap.mul' k S (TensorProduct.map LinearMap.id (imageAntipode e sec)
        (TensorProduct.map e.toLinearMap e.toLinearMap x))
      = e (LinearMap.mul' k A (TensorProduct.map LinearMap.id (antipode k) x)) := by
  induction x with
  | tmul a b => simp [imageAntipode_e e sec hsec f m hm hcomp]
  | add u v hu hv => simp [hu, hv]

include he hsec hm hcomp in
/-- Antipode axiom for the image: `μ ∘ (imageAntipode ⊗ id) ∘ imageComul = η ∘ imageCounit`. -/
lemma image_mul_antipode_rTensor_comul [IsAbsFlat k] :
    LinearMap.mul' k S ∘ₗ (imageAntipode e sec).rTensor S ∘ₗ imageComul e sec
      = Algebra.linearMap k S ∘ₗ imageCounit (k := k) m := by
  apply LinearMap.ext; intro s; obtain ⟨a, rfl⟩ := he s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor,
    imageComul_e e sec hsec f m hm hcomp, mul_rTensor_imageAntipode e sec hsec f m hm hcomp,
    imageCounit_e e f m hcomp, Algebra.linearMap_apply]
  rw [show LinearMap.mul' k A (TensorProduct.map (antipode k) LinearMap.id (comul a))
      = algebraMap k A (counit a) from HopfAlgebra.mul_antipode_rTensor_comul_apply a]
  simp

include he hsec hm hcomp in
/-- Antipode axiom for the image: `μ ∘ (id ⊗ imageAntipode) ∘ imageComul = η ∘ imageCounit`. -/
lemma image_mul_antipode_lTensor_comul [IsAbsFlat k] :
    LinearMap.mul' k S ∘ₗ (imageAntipode e sec).lTensor S ∘ₗ imageComul e sec
      = Algebra.linearMap k S ∘ₗ imageCounit (k := k) m := by
  apply LinearMap.ext; intro s; obtain ⟨a, rfl⟩ := he s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor,
    imageComul_e e sec hsec f m hm hcomp, mul_lTensor_imageAntipode e sec hsec f m hm hcomp,
    imageCounit_e e f m hcomp, Algebra.linearMap_apply]
  rw [show LinearMap.mul' k A (TensorProduct.map LinearMap.id (antipode k) (comul a))
      = algebraMap k A (counit a) from HopfAlgebra.mul_antipode_lTensor_comul_apply a]
  simp

/-! ### The Hopf algebra structure on the image -/

include he hsec hm hcomp in
/-- The coalgebra structure transported to `S`. -/
@[instance_reducible]
noncomputable def imageCoalgebra [IsAbsFlat k] : Coalgebra k S where
  comul := imageComul e sec
  counit := imageCounit m
  coassoc := image_coassoc e he sec hsec f m hm hcomp
  rTensor_counit_comp_comul := image_rTensor_counit e he sec hsec f m hm hcomp
  lTensor_counit_comp_comul := image_lTensor_counit e he sec hsec f m hm hcomp

include he hsec hm hcomp in
/-- The bialgebra structure transported to `S`. -/
@[instance_reducible]
noncomputable def imageBialgebra [IsAbsFlat k] : Bialgebra k S :=
  letI := imageCoalgebra e he sec hsec f m hm hcomp
  Bialgebra.mk' k S (image_counit_one m) (fun {s t} => image_counit_mul m s t)
    (image_comul_one e sec hsec f m hm hcomp)
        (fun {s t} => image_comul_mul e he sec hsec f m hm hcomp s t)

include he hsec hm hcomp in
/-- The Hopf algebra structure transported to `S`. -/
@[instance_reducible]
noncomputable def imageHopfAlgebra [IsAbsFlat k] : HopfAlgebra k S :=
  letI := imageBialgebra e he sec hsec f m hm hcomp
  { antipode := imageAntipode e sec
    mul_antipode_rTensor_comul := image_mul_antipode_rTensor_comul e he sec hsec f m hm hcomp
    mul_antipode_lTensor_comul := image_mul_antipode_lTensor_comul e he sec hsec f m hm hcomp }

end HopfImage

open HopfImage in
/-- **The image factorization for commutative Hopf algebras over a field.**  Every morphism of
commutative Hopf algebras over a field factors as a surjective morphism of Hopf algebras
followed by an injective one.  This is the first half of Theorem 3.12 of
[forsman2026semiabeliannessaffinegroupschemes]. -/
theorem exists_hopfAlgebra_image_factorization {k : Type u} {A : Type v} {B : Type w} [Field k]
    [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] (f : A →ₐc[k] B) :
    ∃ (S : Type w) (_ : CommRing S) (_ : HopfAlgebra k S) (e : A →ₐc[k] S) (m : S →ₐc[k] B),
      Surjective e ∧ Injective m ∧ ∀ a, m (e a) = f a := by
  set g : A →ₐ[k] B := (f : A →ₐ[k] B)
  set e₀ : A →ₐ[k] g.range := g.rangeRestrict
  set m₀ : g.range →ₐ[k] B := g.range.val
  have he : Surjective e₀ := g.rangeRestrict_surjective
  have hm : Injective m₀ := Subtype.val_injective
  have hcomp : ∀ a, m₀ (e₀ a) = f a := fun _ => rfl
  obtain ⟨sec, hsec0⟩ := LinearMap.exists_rightInverse_of_surjective e₀.toLinearMap
    (LinearMap.range_eq_top.2 he)
  have hsec : ∀ s, e₀ (sec s) = s := fun s => congr($hsec0 s)
  let : HopfAlgebra k g.range := imageHopfAlgebra e₀ he sec hsec f m₀ hm hcomp
  have hcounit : ∀ s : g.range, (counit s : k) = counit (m₀ s) := fun _ => rfl
  have hcomul : ∀ a : A, comul (e₀ a)
      = TensorProduct.map e₀.toLinearMap e₀.toLinearMap (comul a) :=
    imageComul_e e₀ sec hsec f m₀ hm hcomp
  refine ⟨↥g.range, inferInstance, inferInstance,
    BialgHom.ofAlgHom e₀ ?_ ?_, BialgHom.ofAlgHom m₀ ?_ ?_, he, hm, hcomp⟩
  · ext a
    exact imageCounit_e e₀ f m₀ hcomp a
  · ext a
    exact congr($(map_e_e_eq e₀) (comul a)).trans (hcomul a).symm
  · ext s
    exact (hcounit s).symm
  · ext s
    obtain ⟨a, rfl⟩ := he s
    change TensorProduct.map m₀.toLinearMap m₀.toLinearMap (comul (e₀ a)) = comul (m₀ (e₀ a))
    rw [hcomul a, map_e_map_e e₀ f m₀ hcomp, map_f_comul f a, hcomp]

end AffineGroupSchemes
