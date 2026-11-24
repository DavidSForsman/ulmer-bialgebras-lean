module

public import UlmerBialgebras.Kan.KanProduct

/-!
# Quotient initiality in products (Theorem 4.7 (1))

## Main results

* `UlmerBialgebras.Paper.pi_quotientInitial_iff`: in a product of categories, an object has
  subsingleton hom-sets out of it iff each component does.
* `UlmerBialgebras.Paper.quotientInitial_iff_of_full_faithful_surj`: this property transfers along a
  full, faithful functor that is surjective on objects (such as the comparison functor
  `Product.kanFunctorLeft`).
* `UlmerBialgebras.Paper.product_quotientInitial_iff`: quotient initiality of a left extension into
  a product is detected componentwise.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 4.7 (1)
-/

@[expose] public section

universe s u v w

namespace UlmerBialgebras.Paper

open CategoryTheory

section Pi

variable {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Category (A i)]

/-- A morphism out of `x` that is `f` at `i` and the identity elsewhere. -/
noncomputable def piUpdateHom (x : ∀ j, A j) (i : ι) {z : A i} (f : x i ⟶ z) :
    x ⟶ Function.update x i z := fun j =>
  if h : j = i then by subst h; exact f ≫ eqToHom (Function.update_self j z x).symm
  else eqToHom (Function.update_of_ne h z x).symm

/-- The `i`-component of `piUpdateHom x i f` is `f`, up to an `eqToHom`. -/
lemma piUpdateHom_self (x : ∀ j, A j) (i : ι) {z : A i} (f : x i ⟶ z) :
    piUpdateHom x i f i = f ≫ eqToHom (Function.update_self i z x).symm := by
  simp [piUpdateHom]

omit [DecidableEq ι] in
/-- In a product category `∏ᵢ Aᵢ`, all hom-sets out of `x` are subsingletons iff, for every `i`,
    all hom-sets out of `xᵢ` in `Aᵢ` are subsingletons. -/
theorem pi_quotientInitial_iff (x : ∀ j, A j) :
    (∀ y : ∀ j, A j, Subsingleton (x ⟶ y)) ↔ ∀ (i : ι) (z : A i), Subsingleton (x i ⟶ z) := by
  classical
  refine ⟨fun h i z => ⟨fun p q => ?_⟩, fun h y =>
      ⟨fun p q => funext fun i => (h i (y i)).elim _ _⟩⟩
  have := congrFun ((h _).elim (piUpdateHom x i p) (piUpdateHom x i q)) i
  rw [piUpdateHom_self, piUpdateHom_self] at this
  exact (cancel_mono _).1 this

end Pi

section Transfer

variable {C D : Type*} [Category C] [Category D]

/-- For a full, faithful functor `F : C ⥤ D` surjective on objects, all hom-sets out of `x` are
    subsingletons iff all hom-sets out of `F x` are. -/
theorem quotientInitial_iff_of_full_faithful_surj (F : C ⥤ D) [F.Full] [F.Faithful]
    (hsurj : ∀ y : D, ∃ x, F.obj x = y) (x : C) :
    (∀ x' : C, Subsingleton (x ⟶ x')) ↔ ∀ y : D, Subsingleton (F.obj x ⟶ y) := by
  refine ⟨fun h y => ?_, fun h x' => ⟨fun a b => F.map_injective ((h _).elim _ _)⟩⟩
  obtain ⟨x', rfl⟩ := hsurj y
  exact ⟨fun a b => by
    rw [← F.map_preimage a, ← F.map_preimage b, (h x').elim (F.preimage a) (F.preimage b)]⟩

end Transfer

open scoped CategoryTheory.Bicategory

/-- Quotient initiality of a left extension into a product is detected componentwise. -/
theorem product_quotientInitial_iff {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    {ι : Type s} {cs : ι → Obj} (P : Product cs) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) (L : LeftExt k d) :
    QuotientInitial L ↔ ∀ i, QuotientInitial ((LeftExt.push k d (P.π i)).obj L) := by
  classical
  have hsurj : ∀ b : (∀ i, LeftExt k (d ≫ P.π i)),
      ∃ a, (Product.kanFunctorLeft P k d).obj a = b := fun b => by
    obtain ⟨a, ha, -⟩ := Product.existsUnique_leftExt P k d b
    exact ⟨a, funext ha⟩
  exact (quotientInitial_iff_of_full_faithful_surj (Product.kanFunctorLeft P k d) hsurj L).trans
    (pi_quotientInitial_iff _)

end UlmerBialgebras.Paper
