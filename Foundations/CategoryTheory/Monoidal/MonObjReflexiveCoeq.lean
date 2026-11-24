module

public import Foundations.CategoryTheory.Monoidal.ReflexiveTensor

/-!
# Reflexive coequalizers of monoid objects

Let `C` be a monoidal category in which tensoring on either side preserves the coequalizers of
reflexive pairs.  This file shows that the coequalizer of a reflexive pair of morphisms of monoid
objects, computed in `C`, carries a monoid structure making the coequalizer projection a morphism
of monoid objects.

Everything rests on the fact, proved in `Foundations/CategoryTheory/Monoidal/ReflexiveTensor.lean`,
that `q ⊗ₘ q`
is again a coequalizer.

## Main results

* `CategoryTheory.MonReflexiveCoeq.monObj`: the monoid structure on the coequalizer;
* `CategoryTheory.MonReflexiveCoeq.isMonHom_q`: the projection is a morphism of monoid objects.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.17
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj

section
open CategoryTheory

namespace CategoryTheory.MonReflexiveCoeq

section DescMon

variable {C : Type u} [Category.{v} C] {M N Q : C} {u v : M ⟶ N} {q : N ⟶ Q} {w : u ≫ q = v ≫ q}
  (hq : IsColimit (Cofork.ofπ q w)) {Z : C} (h : N ⟶ Z) (hh : u ≫ h = v ≫ h)

/-- The morphism induced on the coequalizer by a morphism coequalizing the pair. -/
noncomputable def descMon : Q ⟶ Z := Cofork.IsColimit.desc hq h hh

/-- The induced morphism satisfies `q ≫ descMon hq h hh = h`. -/
@[reassoc (attr := simp)]
lemma comp_descMon : q ≫ descMon hq h hh = h :=
  Cofork.IsColimit.π_desc' hq h hh

end DescMon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable {M N Q : C} [MonObj M] [MonObj N] {u v : M ⟶ N} [IsMonHom u] [IsMonHom v]
  (hr : IsReflexivePair u v) {q : N ⟶ Q} {w : u ≫ q = v ≫ q} (hq : IsColimit (Cofork.ofπ q w))

/-- If `u ≫ q = v ≫ q`, then `(u ⊗ₘ u) ≫ (μ[N] ≫ q) = (v ⊗ₘ v) ≫ (μ[N] ≫ q)`. -/
lemma mul_aux (w : u ≫ q = v ≫ q) : (u ⊗ₘ u) ≫ (μ[N] ≫ q) = (v ⊗ₘ v) ≫ (μ[N] ≫ q) := by
  rw [← Category.assoc, ← Category.assoc, ← IsMonHom.mul_hom u, ← IsMonHom.mul_hom v,
    Category.assoc, Category.assoc, w]

include hr hq

variable [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- The multiplication induced on a reflexive coequalizer of monoid objects. -/
noncomputable def mul : Q ⊗ Q ⟶ Q :=
  (CategoryTheory.ReflexiveTensor.existsUnique_desc_tensorHom hr hq (μ[N] ≫ q) (mul_aux w)).choose

/-- The multiplication of the coequalizer satisfies `(q ⊗ₘ q) ≫ mul hr hq = μ[N] ≫ q`. -/
@[reassoc]
lemma tensorHom_comp_mul : (q ⊗ₘ q) ≫ mul hr hq = μ[N] ≫ q :=
  (CategoryTheory.ReflexiveTensor.existsUnique_desc_tensorHom hr hq (μ[N] ≫ q)
      (mul_aux w)).choose_spec.1

/-- The multiplication of the coequalizer satisfies
`(q ▷ N) ≫ (Q ◁ q) ≫ mul hr hq = μ[N] ≫ q`. -/
lemma whiskerRight_whiskerLeft_comp_mul :
    (q ▷ N) ≫ (Q ◁ q) ≫ mul hr hq = μ[N] ≫ q := by
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def, tensorHom_comp_mul hr hq]

/-- The left unit law for the multiplication of the reflexive coequalizer. -/
lemma one_mul_aux : ((η[N] ≫ q) ▷ Q) ≫ mul hr hq = (λ_ Q).hom := by
  have := CategoryTheory.ReflexiveTensor.epi_whiskerLeft hr hq (𝟙_ C)
  rw [← cancel_epi (𝟙_ C ◁ q), ← Category.assoc, whisker_exchange, Category.assoc,
    comp_whiskerRight, Category.assoc, whiskerRight_whiskerLeft_comp_mul hr hq,
    ← Category.assoc, MonObj.one_mul, leftUnitor_naturality]

/-- The right unit law for the multiplication of the reflexive coequalizer. -/
lemma mul_one_aux : (Q ◁ (η[N] ≫ q)) ≫ mul hr hq = (ρ_ Q).hom := by
  have := CategoryTheory.ReflexiveTensor.epi_whiskerRight hr hq (𝟙_ C)
  rw [← cancel_epi (q ▷ 𝟙_ C), ← Category.assoc, ← whisker_exchange, Category.assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, ← Category.assoc (N ◁ q),
    whisker_exchange q q, Category.assoc,
    whiskerRight_whiskerLeft_comp_mul hr hq, ← Category.assoc, MonObj.mul_one,
    rightUnitor_naturality]

/-- The associativity law for the multiplication of the reflexive coequalizer. -/
lemma mul_assoc_aux :
    (mul hr hq ▷ Q) ≫ mul hr hq
      = (α_ Q Q Q).hom ≫ (Q ◁ mul hr hq) ≫ mul hr hq := by
  have := CategoryTheory.ReflexiveTensor.epi_tensorHom_tensorHom' hr hq
  rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
  have hl : ((q ⊗ₘ q) ⊗ₘ q) ≫ (mul hr hq ▷ Q) = (μ[N] ▷ N) ≫ (q ⊗ₘ q) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_mul hr hq, Category.comp_id, Category.id_comp]
  have hrr : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ (Q ◁ mul hr hq)
      = (α_ N N N).hom ≫ (N ◁ μ[N]) ≫ (q ⊗ₘ q) := by
    rw [← Category.assoc, associator_naturality, Category.assoc, ← id_tensorHom, ← id_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_mul hr hq,
      Category.comp_id, Category.id_comp]
  rw [reassoc_of% hl, tensorHom_comp_mul hr hq, reassoc_of% hrr, tensorHom_comp_mul hr hq,
    ← Category.assoc, MonObj.mul_assoc]
  simp

/-- The monoid structure induced on a reflexive coequalizer of monoid objects. -/
@[instance_reducible]
noncomputable def monObj : MonObj Q where
  one := η[N] ≫ q
  mul := mul hr hq
  one_mul := one_mul_aux hr hq
  mul_one := mul_one_aux hr hq
  mul_assoc := mul_assoc_aux hr hq

/-- The unit of `monObj hr hq` is `η[N] ≫ q`. -/
lemma monObj_one : (monObj hr hq).one = η[N] ≫ q := rfl

/-- The multiplication of `monObj hr hq` is `mul hr hq`. -/
lemma monObj_mul : (monObj hr hq).mul = mul hr hq := rfl

/-- The projection onto a reflexive coequalizer is a morphism of monoid objects. -/
lemma isMonHom_q : letI := monObj hr hq; IsMonHom q :=
  letI := monObj hr hq
  { one_hom := rfl
    mul_hom := (tensorHom_comp_mul hr hq).symm }

section Desc

variable {Z : C} [MonObj Z] (h : N ⟶ Z) [IsMonHom h] (hh : u ≫ h = v ≫ h)

/-- The induced morphism is again a morphism of monoid objects. -/
lemma isMonHom_descMon : letI := monObj hr hq; IsMonHom (descMon hq h hh) :=
  letI := monObj hr hq
  { one_hom := by
      rw [monObj_one, Category.assoc, comp_descMon, IsMonHom.one_hom]
    mul_hom := by
      have := CategoryTheory.ReflexiveTensor.epi_tensorHom hr hq
      rw [← cancel_epi (q ⊗ₘ q), monObj_mul, ← Category.assoc, tensorHom_comp_mul hr hq,
        Category.assoc, comp_descMon, ← Category.assoc, tensorHom_comp_tensorHom, comp_descMon,
        IsMonHom.mul_hom] }

end Desc

end CategoryTheory.MonReflexiveCoeq

end
