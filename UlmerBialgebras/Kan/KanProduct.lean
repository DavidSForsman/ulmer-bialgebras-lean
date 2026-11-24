module

public import UlmerBialgebras.Kan.Kan

/-!
# Theorem 4.7 (1): Kan extensions and products

This file proves part (1) of Theorem 4.7 of *A Syntactic Approach to Ulmer's Bialgebras*:
the projections `π i : ∏ cᵢ ⟶ cᵢ` of a strict product in a strict 2-category preserve all
left Kan extensions, and jointly strictly create them.

The proof goes through the comparison functor

`UlmerBialgebras.Product.kanFunctorLeft : LeftExt k d ⥤ (∀ i, LeftExt k (d ≫ P.π i))`

which is shown to be fully faithful and bijective on objects, so that initial objects are
transported back and forth along it; the componentwise description of initial objects in a
product of categories then gives the statement.

The right Kan case is the left Kan case in `K^co` (`UlmerBialgebras/Kan/CoKan.lean`); it is derived
in
`UlmerBialgebras/Proofs/Sec4/Sec4.lean`.

## Main results

* `UlmerBialgebras.Product.preserves_leftKan`: the projections of a product preserve all left Kan
  extensions (Theorem 4.7 (1)).
* `UlmerBialgebras.Product.jointlyStrictlyCreates_leftKan`: the projections jointly strictly create
  all left Kan extensions (Theorem 4.7 (1)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.6 (1) and Theorem 4.7 (1)
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe s u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Product

variable {ι : Type s} {cs : ι → Obj} (P : Product cs) {I X : Obj}

/-! ## The comparison functor for left extensions -/

/-- The comparison functor sending a left extension of `d` along `k` to the family of its
push-forwards along the projections of the product. -/
@[simps]
def kanFunctorLeft (k : I ⟶ X) (d : I ⟶ P.pt) :
    LeftExt k d ⥤ (∀ i, LeftExt k (d ≫ P.π i)) where
  obj L i := (LeftExt.push k d (P.π i)).obj L
  map a i := (LeftExt.push k d (P.π i)).map a
  map_id L := funext fun i => (LeftExt.push k d (P.π i)).map_id L
  map_comp a b := funext fun i => (LeftExt.push k d (P.π i)).map_comp a b

/-- The comparison functor `kanFunctorLeft P k d` into families of left extensions is faithful. -/
instance kanFunctorLeft_faithful (k : I ⟶ X) (d : I ⟶ P.pt) :
    (kanFunctorLeft P k d).Faithful where
  map_injective {_ _ _ _} h :=
    LeftExt.hom_ext (P.cell_ext fun i => LeftExt.hom_ext_iff.mp (funext_iff.mp h i))

/-- The comparison functor `kanFunctorLeft P k d` into families of left extensions is full. -/
instance kanFunctorLeft_full (k : I ⟶ X) (d : I ⟶ P.pt) : (kanFunctorLeft P k d).Full where
  map_surjective {L L'} β := by
    -- the components of `β`, typed by the 1-cells `L.ext ≫ P.π i` they are 2-cells between
    let γ : ∀ i, L.ext ≫ P.π i ⟶ L'.ext ≫ P.π i := fun i => LeftExt.homCell (β i)
    have hβ : ∀ i, ((L.unit ▷ P.π i) ≫ eqToHom (Category.assoc k L.ext (P.π i))) ≫
        (k ◁ γ i) = (L'.unit ▷ P.π i) ≫ eqToHom (Category.assoc k L'.ext (P.π i)) :=
      fun i => LeftExt.w (β i)
    refine ⟨LeftExt.homMk (P.lift₂ γ) ?_, ?_⟩
    · refine P.cell_ext (fun i => ?_)
      rw [Bicategory.comp_whiskerRight, Bicategory.Strict.whisker_assoc', P.lift₂_π]
      slice_lhs 1 3 => rw [← Category.assoc, hβ i]
      simp
    · refine funext fun i => LeftExt.hom_ext ?_
      exact P.lift₂_π γ i

/-- The comparison functor is bijective on objects: a family of left extensions along the
projections has a unique lift to a left extension into the product. -/
lemma existsUnique_leftExt (k : I ⟶ X) (d : I ⟶ P.pt) (b : ∀ i, LeftExt k (d ≫ P.π i)) :
    ∃! L : LeftExt k d, ∀ i, (LeftExt.push k d (P.π i)).obj L = b i := by
  have hi : ∀ i, (k ≫ P.lift (fun i => (b i).ext)) ≫ P.π i = k ≫ (b i).ext := by
    intro i; rw [Category.assoc, P.lift_π]
  refine ⟨LeftExt.mk (P.lift (fun i => (b i).ext))
      (P.lift₂ (fun i => (b i).unit ≫ eqToHom (hi i).symm)), ?_, ?_⟩
  · intro i
    refine LeftExt.eq_of_ext_eq (P.lift_π (fun i => (b i).ext) i) ?_
    simp only [LeftExt.push_obj_unit]
    rw [LeftExt.mk_unit, P.lift₂_π]
    simp
  · intro L' hL'
    have hext : ∀ i, L'.ext ≫ P.π i = (b i).ext := fun i => congrArg LeftExt.ext (hL' i)
    have hunit : ∀ i, ((L'.unit ▷ P.π i) ≫ eqToHom (Category.assoc k L'.ext (P.π i))) ≫
        eqToHom (by rw [hext i]) = (b i).unit := by
      intro i
      simpa only [LeftExt.push_obj_unit] using LeftExt.unit_congr (hL' i)
    refine LeftExt.eq_of_ext_eq (P.hom_ext fun i => by
      rw [hext i, LeftExt.mk_ext, P.lift_π]) ?_
    refine P.cell_ext (fun i => ?_)
    rw [LeftExt.mk_unit, Bicategory.comp_whiskerRight, P.lift₂_π, Bicategory.eqToHom_whiskerRight,
      ← hunit i]
    simp

/-- Theorem 4.7 (1): the projections of a product preserve all left Kan extensions. -/
theorem preserves_leftKan (k : I ⟶ X) (d : I ⟶ P.pt) (i : ι) :
    PreservesLeftKan k d (P.π i) := by
  intro L hL
  have hsurj : ∀ b : (∀ i, LeftExt k (d ≫ P.π i)), ∃ a, (kanFunctorLeft P k d).obj a = b := by
    intro b
    obtain ⟨a, ha, -⟩ := existsUnique_leftExt P k d b
    exact ⟨a, funext ha⟩
  exact ⟨isInitialPiApply
    (isInitialObjOfFullyFaithful (kanFunctorLeft P k d) hsurj hL.some) i⟩

/-- Theorem 4.7 (1): the projections of a product jointly strictly create all left Kan
extensions. -/
theorem jointlyStrictlyCreates_leftKan (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesInitial (fun i : ι => LeftExt.push k d (P.π i)) := by
  intro b hb
  refine ⟨existsUnique_leftExt P k d b, ?_⟩
  intro L hL
  have hobj : (kanFunctorLeft P k d).obj L = b := funext hL
  refine ⟨isInitialOfFullyFaithful (kanFunctorLeft P k d) ?_⟩
  rw [hobj]
  exact hb.some

end Product

end UlmerBialgebras
