module

public import Mathlib.CategoryTheory.Bicategory.Yoneda

/-!
# Bi-dense pseudofunctors (Hofstra–Karvonen)

We formalize the bicategorical notion of density of Hofstra and Karvonen
[hofstraInnerAutoequivalencesGeneral2024], which we call **bi-density**. In
arXiv:2205.03683v2 (§6, "Isotropy and two-dimensional density"), Proposition 6.1 lists four
equivalent conditions on a pseudofunctor `F : 𝒞 → 𝒟` between bicategories, and

> **Definition 6.2.** A pseudofunctor is called *dense* if it satisfies the equivalent
> conditions of Proposition 6.1.

The conditions (ii) and (iii) of Proposition 6.1 read:

> (ii) the restricted Yoneda embedding `𝒟 --Y--> [𝒟^op, Cat] --F̂--> [𝒞^op, Cat]` is a local
> equivalence;
>
> (iii) for all objects `A, B` of `𝒟`, the functor `𝒟(A, B) → [𝒞^op, Cat](𝒟(F-, A), 𝒟(F-, B))`
> is an equivalence;

where (§3) `[𝒞, 𝒟]` denotes "the 2-category of pseudofunctors `𝒞 → 𝒟`, pseudonatural
transformations and modifications". HK note that (iii) "is just a rephrasing of (ii)". The
remaining conditions, (i) (restriction along `F` is an equivalence on hom-categories between
cocontinuous pseudofunctors) and (iv) (each `A` is the `𝒟(F-, A)`-weighted bicolimit of `F`),
involve bicolimits, which Mathlib does not have; we take condition (iii) as the definition
(`CategoryTheory.Pseudofunctor.IsBiDense`).

In Mathlib's language, `[𝒞ᵒᵖ, Cat]` is the bicategory `𝒞ᵒᵖ ⥤ᵖ Cat` of pseudofunctors, strong
transformations and modifications, the representable `𝒟(-, A)` is `Bicategory.yoneda.obj A`, and
`𝒟(F-, A)` is the composite `F.op.comp (Bicategory.yoneda.obj A)`, where `F.op : 𝒞ᵒᵖ ⥤ᵖ 𝒟ᵒᵖ` is
the pseudofunctor induced by `F` on the 1-cell duals (`CategoryTheory.Pseudofunctor.op`). The
functor of (iii) is the action of the Yoneda pseudofunctor on hom-categories followed by
whiskering with `F.op` (`CategoryTheory.Pseudofunctor.restrictedYonedaFunctor`).

This is HK's notion for a *pseudofunctor*. The paper's Definition 7.1
([forsman2026syntactic], `UlmerBialgebras.Paper.IsBiDense` in `UlmerBialgebras/Paper/Sec3Defs.lean`)
is the
corresponding notion for a *class of objects* of a strict 2-category; the two are compared in
`UlmerBialgebras/Paper/Sec7Variant.lean`.

## Main definitions

* `CategoryTheory.Pseudofunctor.op`: the pseudofunctor `Bᵒᵖ ⥤ᵖ Cᵒᵖ` induced by `B ⥤ᵖ C`.
* `CategoryTheory.Pseudofunctor.whiskerLeft`, `CategoryTheory.Pseudofunctor.whiskerLeftFunctor`:
  whiskering strong transformations and modifications on the left by a pseudofunctor.
* `CategoryTheory.Pseudofunctor.restrictedYonedaFunctor`: the functor
  `𝒟(c, d) ⥤ [𝒞ᵒᵖ, Cat](𝒟(F-, c), 𝒟(F-, d))`.
* `CategoryTheory.Pseudofunctor.IsBiDense`: Hofstra–Karvonen bi-density.

## References

* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Proposition 6.1 and
  Definition 6.2 (arXiv:2205.03683v2)
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched], Theorem 5.1
-/

@[expose] public section

universe w₁ v₁ u₁ w₂ v₂ u₂

open CategoryTheory Bicategory _root_.Bicategory.Opposite _root_.Bicategory.Opposite.Hom2 Opposite

/-- Two 2-morphisms of the opposite bicategory are equal if their underlying 2-morphisms are. -/
lemma Bicategory.Opposite.unop2_injective {C : Type u₂} [Bicategory.{w₂, v₂} C] {a b : Cᵒᵖ}
    {f g : a ⟶ b}
    {η θ : f ⟶ g} (h : unop2 η = unop2 θ) : η = θ := by
  cases η; cases θ; cases h; rfl

namespace CategoryTheory.Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- The pseudofunctor `Bᵒᵖ ⥤ᵖ Cᵒᵖ` between 1-cell duals induced by a pseudofunctor
`F : B ⥤ᵖ C`. -/
@[simps]
def op (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ where
  obj a := Opposite.op (F.obj a.unop)
  map f := (F.map f.unop).op
  map₂ η := op2 (F.map₂ (unop2 η))
  map₂_id f := congrArg op2 (F.map₂_id f.unop)
  map₂_comp η θ := congrArg op2 (F.map₂_comp _ _)
  mapId a := (F.mapId a.unop).op2
  mapComp f g := (F.mapComp g.unop f.unop).op2
  map₂_whisker_left f g h η := unop2_injective (by simp)
  map₂_whisker_right η h := unop2_injective (by simp)
  map₂_associator f g h := unop2_injective (by
    simp only [unop_comp, Quiver.Hom.unop_op, bicategory_associator_hom_unop2, unop2_op2,
      Functor.mapIso_hom, opFunctor_map, Functor.mapIso_inv, homCategory_comp_unop2,
      bicategory_whiskerRight_unop2, bicategory_whiskerLeft_unop2]
    rw [reassoc_of% (F.mapComp_assoc_right_hom h.unop g.unop f.unop)]
    simp)
  map₂_left_unitor f := unop2_injective (by simp)
  map₂_right_unitor f := unop2_injective (by simp)

section Whisker

open StrongTrans
variable {A : Type*} [Bicategory A] {D : Type*} [Bicategory D]

/-- Whiskering a strong transformation `η : F ⟶ G` on the left by a pseudofunctor `H`. -/
@[simps]
def whiskerLeft (H : A ⥤ᵖ B) {F G : B ⥤ᵖ C} (η : F ⟶ G) : H.comp F ⟶ H.comp G where
  app a := η.app (H.obj a)
  naturality f := η.naturality (H.map f)
  naturality_naturality θ := η.naturality_naturality (H.map₂ θ)
  naturality_id a := by
    change (η.naturality (H.map (𝟙 a))).hom ≫
        η.app _ ◁ (G.map₂ (H.mapId a).hom ≫ (G.mapId (H.obj a)).hom) =
      (F.map₂ (H.mapId a).hom ≫ (F.mapId (H.obj a)).hom) ▷ η.app _ ≫ (λ_ _).hom ≫ (ρ_ _).inv
    rw [whiskerLeft_comp, comp_whiskerRight, Category.assoc, ← η.naturality_naturality_assoc,
      η.naturality_id]
  naturality_comp f g := by
    change (η.naturality (H.map (f ≫ g))).hom ≫
        η.app _ ◁ (G.map₂ (H.mapComp f g).hom ≫ (G.mapComp (H.map f) (H.map g)).hom) =
      (F.map₂ (H.mapComp f g).hom ≫ (F.mapComp (H.map f) (H.map g)).hom) ▷ η.app _ ≫
        (α_ _ _ _).hom ≫ F.map (H.map f) ◁ (η.naturality (H.map g)).hom ≫
        (α_ _ _ _).inv ≫ (η.naturality (H.map f)).hom ▷ G.map (H.map g) ≫ (α_ _ _ _).hom
    rw [whiskerLeft_comp, comp_whiskerRight, Category.assoc, ← η.naturality_naturality_assoc,
      η.naturality_comp]

/-- Whiskering on the left by a pseudofunctor `H`, as a functor between hom-categories of
the bicategories of pseudofunctors. -/
@[simps]
def whiskerLeftFunctor (H : A ⥤ᵖ B) (F G : B ⥤ᵖ C) : (F ⟶ G) ⥤ (H.comp F ⟶ H.comp G) where
  obj η := H.whiskerLeft η
  map Γ := ⟨{ app a := Γ.as.app (H.obj a), naturality f := Γ.as.naturality (H.map f) }⟩

end Whisker

section BiDense

open StrongTrans

variable (F : B ⥤ᵖ C)

/-- The restricted Yoneda functor `C(c, d) ⥤ [Bᵒᵖ, Cat](C(F-, c), C(F-, d))`: the action of the
Yoneda pseudofunctor `C ⥤ᵖ Cᵒᵖ ⥤ᵖ Cat` on hom-categories, followed by whiskering with
`F.op : Bᵒᵖ ⥤ᵖ Cᵒᵖ`. It sends `f : c ⟶ d` to post-composition with `f`. -/
@[simps!]
def restrictedYonedaFunctor (c d : C) :
    (c ⟶ d) ⥤ (F.op.comp (Bicategory.yoneda.obj c) ⟶ F.op.comp (Bicategory.yoneda.obj d)) :=
  Bicategory.yoneda.mapFunctor c d ⋙ F.op.whiskerLeftFunctor _ _

/-- **Bi-density** in the sense of Hofstra–Karvonen
([hofstraInnerAutoequivalencesGeneral2024], Definition 6.2, condition (iii) of
Proposition 6.1): a pseudofunctor `F : B ⥤ᵖ C` is bi-dense if for all objects `c, d` of `C`
the functor `C(c, d) ⥤ [Bᵒᵖ, Cat](C(F-, c), C(F-, d))` (`restrictedYonedaFunctor`), sending a
1-cell `f` to post-composition with `f`, is an equivalence of categories. -/
class IsBiDense : Prop where
  /-- The functors `C(c, d) ⥤ [Bᵒᵖ, Cat](C(F-, c), C(F-, d))` are equivalences. -/
  isEquivalence (c d : C) : (F.restrictedYonedaFunctor c d).IsEquivalence

end BiDense

end CategoryTheory.Pseudofunctor
