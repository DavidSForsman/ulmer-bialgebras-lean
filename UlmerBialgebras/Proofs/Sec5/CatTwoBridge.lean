module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Proofs.Sec5.CatOneDense
public import UlmerBialgebras.Density.AAdjointRep

/-!
# Monadicity in the strict 2-category `CAT` versus Mathlib's monadicity

For a 2-adjunction `A : F ⊣ G` in `Cat.{v, u}` with underlying adjunction
`adj := A.toAdjunction` (`UlmerBialgebras.TwoAdj.toAdjunction`), the induced adjunction
`CAT(X, F) ⊣ CAT(X, G)` on hom-categories (`UlmerBialgebras.TwoAdj.postcompAdj`) is the pointwise
adjunction on functor categories `X ⥤ -`. Its algebras are functors into the `adj`-algebras
(`UlmerBialgebras.Paper.CatTwo.algebraFunctor`, an equivalence), and its comparison functor is the
pointwise comparison of `adj` (`UlmerBialgebras.Paper.CatTwo.comparisonPostcompIso`). Hence
Definition 5.1 of monadicity in the 2-category `CAT` agrees with Mathlib's `MonadicRightAdjoint`:
one direction evaluates at the terminal category `1`, the other applies `Equivalence.congrRight`.
Dually for comonadicity.

We also transport the `{1}`-properties of Definition 7.2 along `CAT(1, C) ≃ C`
(`UlmerBialgebras.oneEquiv`).

## Main results

* `UlmerBialgebras.Paper.CatTwo.isMonadic2_iff`: `IsMonadic2 G ↔ Nonempty (MonadicRightAdjoint G)`
  in `CAT`.
* `UlmerBialgebras.Paper.CatTwo.isComonadic2_iff`:
  `IsComonadic2 F ↔ Nonempty (ComonadicLeftAdjoint F)`.
* `UlmerBialgebras.Paper.CatTwo.isARightAdjoint_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isALeftAdjoint_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isAComplete_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isACocomplete_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isAContinuous_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isACocontinuous_one_iff`: the `{1}`-properties of objects and
  1-cells of `CAT` are the ordinary properties.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 5.1
  (monadicity in a 2-category), Definition 7.2 (`A`-properties) and Section 7.1 (the case
  `K = CAT`, `A = {1}`)
* [R. Street, *The formal theory of monads*][STREET1972149]
-/

@[expose] public section

universe v u v₁ u₁

namespace UlmerBialgebras.Paper.CatTwo

open CategoryTheory UlmerBialgebras Limits

/-! ## Evaluation at the point of `1`, for an arbitrary category -/

section Eval

variable (E : Type u₁) [Category.{v₁} E]

/-- Evaluation `(1 ⥤ E) ⥤ E` at the unique object of the terminal category. -/
abbrev evalOne : (One.{v, u} ⥤ E) ⥤ E := (evaluation One.{v, u} E).obj One.star

/-- Evaluation at the point of `1` is faithful. -/
instance : (evalOne.{v, u} E).Faithful where
  map_injective {F G} α β h := by
    ext x
    obtain rfl : x = One.star := Subsingleton.elim _ _
    exact h

/-- Evaluation at the point of `1` is full. -/
instance : (evalOne.{v, u} E).Full where
  map_surjective {F G} f :=
    ⟨{ app := fun x => eqToHom (congrArg F.obj (Subsingleton.elim x One.star)) ≫ f ≫
          eqToHom (congrArg G.obj (Subsingleton.elim One.star x))
       naturality := fun x y g => by
        obtain rfl : x = One.star := Subsingleton.elim _ _
        obtain rfl : y = One.star := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
        simp }, by simp⟩

/-- Evaluation at the point of `1` is essentially surjective. -/
instance : (evalOne.{v, u} E).EssSurj where
  mem_essImage X := ⟨(Functor.const _).obj X, ⟨Iso.refl _⟩⟩

/-- Evaluation at the point of `1` is an equivalence. -/
instance : (evalOne.{v, u} E).IsEquivalence where

end Eval

/-! ## Algebras for the induced adjunction on hom-categories -/

section Algebras

variable {C D : Cat.{v, u}} {F : C ⟶ D} {G : D ⟶ C} (A : TwoAdj (Obj := Cat.{v, u}) F G)

/-- The components of the unit of the induced adjunction on hom-categories are those of the unit
of `A`. -/
@[simp] lemma postcompAdj_unit_app_app (X : Cat.{v, u}) (k : X ⟶ C) (x : X) :
    ((A.postcompAdj X).unit.app k).toNatTrans.app x = A.unit'.toNatTrans.app (k.toFunctor.obj x)
        := by
  simp [TwoAdj.postcompAdj]

/-- The components of the counit of the induced adjunction on hom-categories are those of the
counit of `A`. -/
@[simp] lemma postcompAdj_counit_app_app (X : Cat.{v, u}) (k : X ⟶ D) (x : X) :
    ((A.postcompAdj X).counit.app k).toNatTrans.app x = A.counit'.toNatTrans.app (k.toFunctor.obj
        x) := by
  simp [TwoAdj.postcompAdj]

/-- The monad of the induced adjunction on hom-categories acts on objects pointwise. -/
@[simp] lemma postcompAdj_toMonad_obj_obj (X : Cat.{v, u}) (k : X ⟶ C) (x : X) :
    (((A.postcompAdj X).toMonad : (X ⟶ C) ⥤ (X ⟶ C)).obj k).toFunctor.obj x = G.toFunctor.obj
        (F.toFunctor.obj (k.toFunctor.obj x)) :=
  rfl

/-- The monad of the induced adjunction on hom-categories acts on morphisms pointwise. -/
@[simp] lemma postcompAdj_toMonad_map_app (X : Cat.{v, u}) {k k' : X ⟶ C} (α : k ⟶ k')
    (x : X) :
    (((A.postcompAdj X).toMonad : (X ⟶ C) ⥤ (X ⟶ C)).map α).toNatTrans.app x = G.toFunctor.map
        (F.toFunctor.map (α.toNatTrans.app x)) :=
  rfl

/-- The monad of `A.toAdjunction` acts on morphisms as `G ∘ F`. -/
@[simp] lemma toAdjunction_toMonad_map {x y : C} (f : x ⟶ y) :
    (A.toAdjunction.toMonad : C ⥤ C).map f = G.toFunctor.map (F.toFunctor.map f) := rfl

/-- The unit of the monad of the induced adjunction on hom-categories, componentwise. -/
@[simp] lemma postcompAdj_toMonad_η_app_app (X : Cat.{v, u}) (k : X ⟶ C) (x : X) :
    ((A.postcompAdj X).toMonad.η.app k).toNatTrans.app x = A.unit'.toNatTrans.app (k.toFunctor.obj
        x) :=
  postcompAdj_unit_app_app A X k x

/-- The multiplication of the monad of the induced adjunction on hom-categories,
componentwise. -/
@[simp] lemma postcompAdj_toMonad_μ_app_app (X : Cat.{v, u}) (k : X ⟶ C) (x : X) :
    ((A.postcompAdj X).toMonad.μ.app k).toNatTrans.app x = G.toFunctor.map
        (A.counit'.toNatTrans.app (F.toFunctor.obj (k.toFunctor.obj x))) :=
  G.toFunctor.congr_map (postcompAdj_counit_app_app A X (k ≫ F) x)

/-- A functor into the algebras of `adj = A.toAdjunction` gives an algebra for the monad of the
induced adjunction `CAT(X, F) ⊣ CAT(X, G)`, pointwise. -/
@[simps]
def algebraOfFunctor (X : Cat.{v, u}) (H : X ⥤ Monad.Algebra A.toAdjunction.toMonad) :
    Monad.Algebra (A.postcompAdj X).toMonad where
  A := (H ⋙ Monad.forget _).toCatHom
  a :=
    NatTrans.toCatHom₂ {
      app := fun x => (H.obj x).a
      naturality := fun _ _ f => (H.map f).h }
  unit := catVU_cell_ext fun x =>
    (Cat.Hom₂.comp_app _ _ x).trans
      ((postcompAdj_toMonad_η_app_app A X _ x =≫ _).trans (H.obj x).unit)
  assoc := catVU_cell_ext fun x => by
    refine (Cat.Hom₂.comp_app _ _ x).trans
        ((postcompAdj_toMonad_μ_app_app A X _ x =≫ _).trans ?_)
    refine (H.obj x).assoc.trans ?_
    refine Eq.symm ((Cat.Hom₂.comp_app _ _ x).trans ?_)
    exact (postcompAdj_toMonad_map_app A X _ x =≫ _)

/-- The functor from functors into `adj`-algebras to algebras for the induced adjunction on
hom-categories out of `X`. -/
@[simps]
def algebraFunctor (X : Cat.{v, u}) :
    (X ⥤ Monad.Algebra A.toAdjunction.toMonad) ⥤ Monad.Algebra (A.postcompAdj X).toMonad where
  obj H := algebraOfFunctor A X H
  map {H H'} τ :=
    { f := (Functor.whiskerRight τ (Monad.forget _)).toCatHom₂
      h := catVU_cell_ext fun x => (τ.app x).h }

/-- The functor `algebraFunctor` is faithful. -/
instance (X : Cat.{v, u}) : (algebraFunctor A X).Faithful where
  map_injective {H H'} τ τ' h := by
    ext x
    exact congr(($(h)).f.toNatTrans.app x)

/-- The functor `algebraFunctor` is full. -/
instance (X : Cat.{v, u}) : (algebraFunctor A X).Full where
  map_surjective {H H'} φ :=
    ⟨{ app := fun x =>
          { f := φ.f.toNatTrans.app x
            h := by
              have h := congr(($(φ.h)).toNatTrans.app x)
              simp only [Cat.Hom₂.comp_app, postcompAdj_toMonad_map_app] at h
              exact h }
       naturality := fun _ _ f => Monad.Algebra.Hom.ext (φ.f.toNatTrans.naturality f) },
      Monad.Algebra.Hom.ext (catVU_cell_ext fun _ => rfl)⟩

/-- An algebra for the monad of the induced adjunction on hom-categories out of `X`, as a functor
into the algebras of `A.toAdjunction`. -/
@[simps]
def functorOfAlgebra (X : Cat.{v, u}) (M : Monad.Algebra (A.postcompAdj X).toMonad) :
    X ⥤ Monad.Algebra A.toAdjunction.toMonad where
  obj x :=
    { A := M.A.toFunctor.obj x
      a := M.a.toNatTrans.app x
      unit := by
        have h := congr(($(M.unit)).toNatTrans.app x)
        simp only [Cat.Hom₂.comp_app, postcompAdj_toMonad_η_app_app] at h
        exact h
      assoc := by
        have h := congr(($(M.assoc)).toNatTrans.app x)
        simp only [Cat.Hom₂.comp_app, postcompAdj_toMonad_μ_app_app,
          postcompAdj_toMonad_map_app] at h
        exact h }
  map f := { f := M.A.toFunctor.map f, h := M.a.toNatTrans.naturality f }

/-- `functorOfAlgebra` is a section of `algebraOfFunctor`, on the nose. -/
lemma algebraOfFunctor_functorOfAlgebra (X : Cat.{v, u})
    (M : Monad.Algebra (A.postcompAdj X).toMonad) :
    algebraOfFunctor A X (functorOfAlgebra A X M) = M :=
  rfl

/-- The functor `algebraFunctor` is essentially surjective. -/
instance (X : Cat.{v, u}) : (algebraFunctor A X).EssSurj where
  mem_essImage M := ⟨functorOfAlgebra A X M, ⟨eqToIso (algebraOfFunctor_functorOfAlgebra A X M)⟩⟩

/-- The functor `algebraFunctor` is an equivalence. -/
instance (X : Cat.{v, u}) : (algebraFunctor A X).IsEquivalence where

/-- The comparison functor of the induced adjunction `CAT(X, F) ⊣ CAT(X, G)` is the pointwise
comparison functor of `A.toAdjunction`, followed by `algebraFunctor`. -/
def comparisonPostcompIso (X : Cat.{v, u}) :
    ((catHomEquivalence X D).functor ⋙ (CategoryTheory.Functor.whiskeringRight X D _).obj
        (Monad.comparison A.toAdjunction) ⋙
      algebraFunctor A X :
      (X ⟶ D) ⥤ _) ≅ Monad.comparison (A.postcompAdj X) :=
  NatIso.ofComponents
    (fun M => Monad.Algebra.isoMk (Iso.refl _) (by
      refine ((eq_whisker (CategoryTheory.Functor.map_id _ _) _).trans (Category.id_comp _)).trans
        (Eq.trans ?_ (Category.comp_id _).symm)
      exact catVU_cell_ext fun x =>
        G.toFunctor.congr_map (postcompAdj_counit_app_app A X M x)))
    (fun _ => Monad.Algebra.Hom.ext (catVU_cell_ext fun _ =>
      (Category.comp_id _).trans (Category.id_comp _).symm))

/-- If the comparison functor of `A.toAdjunction` is an equivalence, so is the comparison functor
of each induced adjunction on hom-categories. -/
theorem isEquivalence_comparison_postcompAdj
    [(Monad.comparison A.toAdjunction).IsEquivalence] (X : Cat.{v, u}) :
    (Monad.comparison (A.postcompAdj X)).IsEquivalence := by
  have : ((catHomEquivalence X D).functor ⋙ (CategoryTheory.Functor.whiskeringRight X D _).obj
      (Monad.comparison A.toAdjunction)).IsEquivalence :=
    by
      have : ((CategoryTheory.Functor.whiskeringRight X D _).obj
          (Monad.comparison A.toAdjunction)).IsEquivalence :=
        ((Monad.comparison A.toAdjunction).asEquivalence.congrRight (E := X)).isEquivalence_functor
      infer_instance
  exact Functor.isEquivalence_of_iso (comparisonPostcompIso A X)

/-- If the comparison functor of the induced adjunction on hom-categories out of `1` is an
equivalence, so is the comparison functor of `A.toAdjunction`. -/
theorem isEquivalence_comparison_of_postcompAdj_one
    [h : (Monad.comparison (A.postcompAdj One.{v, u})).IsEquivalence] :
    (Monad.comparison A.toAdjunction).IsEquivalence := by
  have : ((catHomEquivalence One D).functor ⋙
      (CategoryTheory.Functor.whiskeringRight One.{v, u} D _).obj
      (Monad.comparison A.toAdjunction) ⋙ algebraFunctor A One.{v, u}).IsEquivalence :=
    Functor.isEquivalence_of_iso (comparisonPostcompIso A One.{v, u}).symm
  have : ((CategoryTheory.Functor.whiskeringRight One.{v, u} D _).obj
      (Monad.comparison A.toAdjunction) ⋙ algebraFunctor A One.{v, u}).IsEquivalence :=
    Functor.isEquivalence_of_comp_left (catHomEquivalence One D).functor _
  have := Functor.isEquivalence_of_comp_right
    ((CategoryTheory.Functor.whiskeringRight One.{v, u} D _).obj (Monad.comparison A.toAdjunction))
    (algebraFunctor A One.{v, u})
  have : (evalOne.{v, u} D ⋙ Monad.comparison A.toAdjunction).IsEquivalence :=
    Functor.isEquivalence_of_iso (Iso.refl
      ((CategoryTheory.Functor.whiskeringRight One.{v, u} D _).obj
        (Monad.comparison A.toAdjunction) ⋙ evalOne.{v, u} _))
  exact Functor.isEquivalence_of_comp_left (evalOne.{v, u} D) _

end Algebras

/-- **Monadicity in `CAT`** ([forsman2026syntactic], Definition 5.1): a functor is monadic in the
sense of the 2-category `CAT` if and only if it is a monadic right adjoint in Mathlib's sense. -/
theorem isMonadic2_iff {C D : Cat.{v, u}} (G : D ⟶ C) :
    IsMonadic2 (Obj := Cat.{v, u}) G ↔ Nonempty (MonadicRightAdjoint G.toFunctor) := by
  constructor
  · rintro ⟨F, A, h⟩
    have := h One.{v, u}
    exact ⟨⟨F.toFunctor, A.toAdjunction, isEquivalence_comparison_of_postcompAdj_one A⟩⟩
  · rintro ⟨⟨L, adj, eqv⟩⟩
    refine ⟨L.toCatHom, Adjunction.toTwoAdj adj, fun X => ?_⟩
    have : (Monad.comparison (Adjunction.toTwoAdj adj).toAdjunction).IsEquivalence := eqv
    exact isEquivalence_comparison_postcompAdj _ X

/-! ## Coalgebras for the induced adjunction on hom-categories -/

section Coalgebras

variable {C D : Cat.{v, u}} {F : C ⟶ D} {G : D ⟶ C} (A : TwoAdj (Obj := Cat.{v, u}) F G)

/-- The comonad of the induced adjunction on hom-categories acts on morphisms pointwise. -/
@[simp] lemma postcompAdj_toComonad_map_app (X : Cat.{v, u}) {k k' : X ⟶ D} (α : k ⟶ k')
    (x : X) :
    (((A.postcompAdj X).toComonad : (X ⟶ D) ⥤ (X ⟶ D)).map α).toNatTrans.app x
      = F.toFunctor.map (G.toFunctor.map (α.toNatTrans.app x)) :=
  rfl

/-- The counit of the comonad of the induced adjunction on hom-categories, componentwise. -/
@[simp] lemma postcompAdj_toComonad_ε_app_app (X : Cat.{v, u}) (k : X ⟶ D) (x : X) :
    ((A.postcompAdj X).toComonad.ε.app k).toNatTrans.app x = A.counit'.toNatTrans.app
        (k.toFunctor.obj x) :=
  postcompAdj_counit_app_app A X k x

/-- The comultiplication of the comonad of the induced adjunction on hom-categories,
componentwise. -/
@[simp] lemma postcompAdj_toComonad_δ_app_app (X : Cat.{v, u}) (k : X ⟶ D) (x : X) :
    ((A.postcompAdj X).toComonad.δ.app k).toNatTrans.app x = F.toFunctor.map
        (A.unit'.toNatTrans.app (G.toFunctor.obj (k.toFunctor.obj x))) :=
  F.toFunctor.congr_map (postcompAdj_unit_app_app A X (k ≫ G) x)

/-- A functor into the coalgebras of `A.toAdjunction` gives a coalgebra for the comonad of the
induced adjunction `CAT(X, F) ⊣ CAT(X, G)`, pointwise. -/
@[simps]
def coalgebraOfFunctor (X : Cat.{v, u}) (H : X ⥤ Comonad.Coalgebra A.toAdjunction.toComonad) :
    Comonad.Coalgebra (A.postcompAdj X).toComonad where
  A := (H ⋙ Comonad.forget _).toCatHom
  a :=
    NatTrans.toCatHom₂ {
      app := fun x => (H.obj x).a
      naturality := fun _ _ f => (H.map f).h.symm }
  counit := catVU_cell_ext fun x =>
    (Cat.Hom₂.comp_app _ _ x).trans
      ((_ ≫= postcompAdj_toComonad_ε_app_app A X _ x).trans (H.obj x).counit)
  coassoc := catVU_cell_ext fun x => by
    refine (Cat.Hom₂.comp_app _ _ x).trans
        ((_ ≫= postcompAdj_toComonad_δ_app_app A X _ x).trans ?_)
    refine (H.obj x).coassoc.trans ?_
    refine Eq.symm ((Cat.Hom₂.comp_app _ _ x).trans ?_)
    exact (_ ≫= postcompAdj_toComonad_map_app A X _ x)

/-- The functor from functors into coalgebras of `A.toAdjunction` to coalgebras for the induced
adjunction on hom-categories out of `X`. -/
@[simps]
def coalgebraFunctor (X : Cat.{v, u}) :
    (X ⥤ Comonad.Coalgebra A.toAdjunction.toComonad) ⥤
      Comonad.Coalgebra (A.postcompAdj X).toComonad where
  obj H := coalgebraOfFunctor A X H
  map {H H'} τ :=
    { f := (Functor.whiskerRight τ (Comonad.forget _)).toCatHom₂
      h := catVU_cell_ext fun x => (τ.app x).h }

/-- The functor `coalgebraFunctor` is faithful. -/
instance (X : Cat.{v, u}) : (coalgebraFunctor A X).Faithful where
  map_injective {H H'} τ τ' h := by
    ext x
    exact congr(($(h)).f.toNatTrans.app x)

/-- The functor `coalgebraFunctor` is full. -/
instance (X : Cat.{v, u}) : (coalgebraFunctor A X).Full where
  map_surjective {H H'} φ :=
    ⟨{ app := fun x =>
          { f := φ.f.toNatTrans.app x
            h := by
              have h := congr(($(φ.h)).toNatTrans.app x)
              simp only [Cat.Hom₂.comp_app, postcompAdj_toComonad_map_app] at h
              exact h }
       naturality := fun _ _ f => Comonad.Coalgebra.Hom.ext (φ.f.toNatTrans.naturality f) },
      Comonad.Coalgebra.Hom.ext (catVU_cell_ext fun _ => rfl)⟩

/-- A coalgebra for the comonad of the induced adjunction on hom-categories out of `X`, as a
functor into the coalgebras of `A.toAdjunction`. -/
@[simps]
def functorOfCoalgebra (X : Cat.{v, u}) (M : Comonad.Coalgebra (A.postcompAdj X).toComonad) :
    X ⥤ Comonad.Coalgebra A.toAdjunction.toComonad where
  obj x :=
    { A := M.A.toFunctor.obj x
      a := M.a.toNatTrans.app x
      counit := by
        have h := congr(($(M.counit)).toNatTrans.app x)
        simp only [Cat.Hom₂.comp_app, postcompAdj_toComonad_ε_app_app] at h
        exact h
      coassoc := by
        have h := congr(($(M.coassoc)).toNatTrans.app x)
        simp only [Cat.Hom₂.comp_app, postcompAdj_toComonad_δ_app_app,
          postcompAdj_toComonad_map_app] at h
        exact h }
  map f := { f := M.A.toFunctor.map f, h := (M.a.toNatTrans.naturality f).symm }

/-- `functorOfCoalgebra` is a section of `coalgebraOfFunctor`, on the nose. -/
lemma coalgebraOfFunctor_functorOfCoalgebra (X : Cat.{v, u})
    (M : Comonad.Coalgebra (A.postcompAdj X).toComonad) :
    coalgebraOfFunctor A X (functorOfCoalgebra A X M) = M :=
  rfl

/-- The functor `coalgebraFunctor` is essentially surjective. -/
instance (X : Cat.{v, u}) : (coalgebraFunctor A X).EssSurj where
  mem_essImage M :=
    ⟨functorOfCoalgebra A X M, ⟨eqToIso (coalgebraOfFunctor_functorOfCoalgebra A X M)⟩⟩

/-- The functor `coalgebraFunctor` is an equivalence. -/
instance (X : Cat.{v, u}) : (coalgebraFunctor A X).IsEquivalence where

/-- The comparison functor of the induced adjunction `CAT(X, F) ⊣ CAT(X, G)` into coalgebras is
the pointwise comparison functor of `A.toAdjunction`, followed by `coalgebraFunctor`. -/
def coComparisonPostcompIso (X : Cat.{v, u}) :
    ((catHomEquivalence X C).functor ⋙ (CategoryTheory.Functor.whiskeringRight X C _).obj
        (Comonad.comparison A.toAdjunction) ⋙
      coalgebraFunctor A X : (X ⟶ C) ⥤ _) ≅ Comonad.comparison (A.postcompAdj X) :=
  NatIso.ofComponents
    (fun M => Comonad.Coalgebra.isoMk (Iso.refl _) (by
      refine ((whisker_eq _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).trans
        (Eq.trans ?_ (Category.id_comp _).symm)
      exact catVU_cell_ext fun x =>
        (F.toFunctor.congr_map (postcompAdj_unit_app_app A X M x)).symm))
    (fun _ => Comonad.Coalgebra.Hom.ext (catVU_cell_ext fun _ =>
      (Category.comp_id _).trans (Category.id_comp _).symm))

/-- If the coalgebra comparison functor of `A.toAdjunction` is an equivalence, so is that of each
induced adjunction on hom-categories. -/
theorem isEquivalence_coComparison_postcompAdj
    [(Comonad.comparison A.toAdjunction).IsEquivalence] (X : Cat.{v, u}) :
    (Comonad.comparison (A.postcompAdj X)).IsEquivalence := by
  have : ((catHomEquivalence X C).functor ⋙ (CategoryTheory.Functor.whiskeringRight X C _).obj
      (Comonad.comparison A.toAdjunction)).IsEquivalence :=
    by
      have : ((CategoryTheory.Functor.whiskeringRight X C _).obj
          (Comonad.comparison A.toAdjunction)).IsEquivalence :=
        ((Comonad.comparison A.toAdjunction).asEquivalence.congrRight (E :=
            X)).isEquivalence_functor
      infer_instance
  exact Functor.isEquivalence_of_iso (coComparisonPostcompIso A X)

/-- If the coalgebra comparison functor of the induced adjunction on hom-categories out of `1` is
an equivalence, so is that of `A.toAdjunction`. -/
theorem isEquivalence_coComparison_of_postcompAdj_one
    [h : (Comonad.comparison (A.postcompAdj One.{v, u})).IsEquivalence] :
    (Comonad.comparison A.toAdjunction).IsEquivalence := by
  have : ((catHomEquivalence One C).functor ⋙
      (CategoryTheory.Functor.whiskeringRight One.{v, u} C _).obj
      (Comonad.comparison A.toAdjunction) ⋙ coalgebraFunctor A One.{v, u}).IsEquivalence :=
    Functor.isEquivalence_of_iso (coComparisonPostcompIso A One.{v, u}).symm
  have : ((CategoryTheory.Functor.whiskeringRight One.{v, u} C _).obj
      (Comonad.comparison A.toAdjunction) ⋙ coalgebraFunctor A One.{v, u}).IsEquivalence :=
    Functor.isEquivalence_of_comp_left (catHomEquivalence One C).functor _
  have := Functor.isEquivalence_of_comp_right
    ((CategoryTheory.Functor.whiskeringRight One.{v, u} C _).obj
      (Comonad.comparison A.toAdjunction))
    (coalgebraFunctor A One.{v, u})
  have : (evalOne.{v, u} C ⋙ Comonad.comparison A.toAdjunction).IsEquivalence :=
    Functor.isEquivalence_of_iso (Iso.refl
      ((CategoryTheory.Functor.whiskeringRight One.{v, u} C _).obj
        (Comonad.comparison A.toAdjunction) ⋙ evalOne.{v, u} _))
  exact Functor.isEquivalence_of_comp_left (evalOne.{v, u} C) _

end Coalgebras

/-- **Comonadicity in `CAT`** ([forsman2026syntactic], Definition 5.1, dual): a functor is
comonadic in the sense of the 2-category `CAT` if and only if it is a comonadic left adjoint in
Mathlib's sense. -/
theorem isComonadic2_iff {C D : Cat.{v, u}} (F : C ⟶ D) :
    IsComonadic2 (Obj := Cat.{v, u}) F ↔ Nonempty (ComonadicLeftAdjoint F.toFunctor) := by
  constructor
  · rintro ⟨G, A, h⟩
    have := h One.{v, u}
    exact ⟨⟨G.toFunctor, A.toAdjunction, isEquivalence_coComparison_of_postcompAdj_one A⟩⟩
  · rintro ⟨⟨R, adj, eqv⟩⟩
    refine ⟨R.toCatHom, Adjunction.toTwoAdj adj, fun X => ?_⟩
    have : (Comonad.comparison (Adjunction.toTwoAdj adj).toAdjunction).IsEquivalence := eqv
    exact isEquivalence_coComparison_postcompAdj _ X

/-! ## The `{1}`-properties of Definition 7.2 in `CAT`

`CAT(1, C) = (1 ⥤ C)` is equivalent to `C` by evaluation at `*` (`UlmerBialgebras.oneEval`), and
post-composition with `g` is conjugate to `g` itself: `postcomp 1 g ⋙ oneEval c = oneEval d ⋙ g`
on the nose. So each `{1}`-property of an object or a 1-cell of `CAT` is the corresponding
ordinary property. -/

section OneProperties

variable {c d : Cat.{v, u}}

/-- Evaluation at `*`, as a functor out of the hom-category `CAT(1, c)`. -/
def homOneEval (c : Cat.{v, u}) : (One.{v, u} ⟶ c) ⥤ c :=
  (catHomEquivalence One c).functor ⋙ oneEval c

/-- Evaluation at `*` on the hom-category `CAT(1, c)` is an equivalence. -/
instance (c : Cat.{v, u}) : (homOneEval c).IsEquivalence :=
  inferInstanceAs (((catHomEquivalence One c).functor ⋙ oneEval c).IsEquivalence)

/-- Post-composition with `g` on `CAT(1, -)` is conjugate to `g` by evaluation at `*`. -/
lemma postcomp_one_comp_homOneEval (g : d ⟶ c) :
    postcomp One.{v, u} g ⋙ homOneEval c = homOneEval d ⋙ g.toFunctor :=
  rfl

/-- `g ≅ E⁻¹ ⋙ E ⋙ g` for an equivalence `E`. -/
private noncomputable def isoInvComp {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    {C₃ : Type*} [Category C₃] (E : C₁ ⥤ C₂) [E.IsEquivalence] (g : C₂ ⥤ C₃) :
    E.asEquivalence.inverse ⋙ E ⋙ g ≅ g :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.asEquivalence.counitIso g ≪≫
    Functor.leftUnitor g

/-- `P ≅ (P ⋙ E) ⋙ E⁻¹` for an equivalence `E`. -/
private noncomputable def isoCompInv {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    {C₃ : Type*} [Category C₃] (P : C₁ ⥤ C₂) (E : C₂ ⥤ C₃) [E.IsEquivalence] :
    (P ⋙ E) ⋙ E.asEquivalence.inverse ≅ P :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P E.asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor P

/-- The `{1}`-right adjoints of `CAT` are the right adjoints. -/
theorem isARightAdjoint_one_iff (g : d ⟶ c) :
    IsARightAdjoint (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) g ↔
      g.toFunctor.IsRightAdjoint := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have := h rfl
    rw [← Functor.isRightAdjoint_comp_iff_left (postcomp One.{v, u} g) (homOneEval c),
      postcomp_one_comp_homOneEval] at this
    exact (Functor.isRightAdjoint_comp_iff_right (homOneEval d) _).1 this
  · subst ha
    rw [← Functor.isRightAdjoint_comp_iff_left (postcomp One.{v, u} g) (homOneEval c),
      postcomp_one_comp_homOneEval]
    infer_instance

/-- The `{1}`-left adjoints of `CAT` are the left adjoints. -/
theorem isALeftAdjoint_one_iff (g : d ⟶ c) :
    IsALeftAdjoint (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) g ↔
      g.toFunctor.IsLeftAdjoint := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have := h rfl
    rw [← Functor.isLeftAdjoint_comp_iff_left (postcomp One.{v, u} g) (homOneEval c),
      postcomp_one_comp_homOneEval] at this
    exact (Functor.isLeftAdjoint_comp_iff_right (homOneEval d) _).1 this
  · subst ha
    rw [← Functor.isLeftAdjoint_comp_iff_left (postcomp One.{v, u} g) (homOneEval c),
      postcomp_one_comp_homOneEval]
    infer_instance

/-- An object of `CAT` is `{1}`-complete if and only if it is complete. -/
theorem isAComplete_one_iff.{w₀} (c : Cat.{v, u}) :
    IsAComplete.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) c ↔
      HasLimitsOfSize.{w₀, w₀} c := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have : HasLimitsOfSize.{w₀, w₀} (One.{v, u} ⟶ c) := h rfl
    exact Adjunction.has_limits_of_equivalence (homOneEval c).asEquivalence.inverse
  · subst ha
    exact Adjunction.has_limits_of_equivalence (homOneEval c)

/-- An object of `CAT` is `{1}`-cocomplete if and only if it is cocomplete. -/
theorem isACocomplete_one_iff.{w₀} (c : Cat.{v, u}) :
    IsACocomplete.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) c ↔
      HasColimitsOfSize.{w₀, w₀} c := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have : HasColimitsOfSize.{w₀, w₀} (One.{v, u} ⟶ c) := h rfl
    exact Adjunction.has_colimits_of_equivalence (homOneEval c).asEquivalence.inverse
  · subst ha
    exact Adjunction.has_colimits_of_equivalence (homOneEval c)

/-- A 1-cell of `CAT` is `{1}`-continuous if and only if it preserves limits. -/
theorem isAContinuous_one_iff.{w₀} (g : d ⟶ c) :
    IsAContinuous.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) g ↔
      PreservesLimitsOfSize.{w₀, w₀} g.toFunctor := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have : PreservesLimitsOfSize.{w₀, w₀} (postcomp One.{v, u} g) := h rfl
    have : PreservesLimitsOfSize.{w₀, w₀} (homOneEval d ⋙ g.toFunctor) := by
      rw [← postcomp_one_comp_homOneEval]; infer_instance
    exact preservesLimits_of_natIso (isoInvComp (homOneEval d) g.toFunctor)
  · subst ha
    have : PreservesLimitsOfSize.{w₀, w₀} (postcomp One.{v, u} g ⋙ homOneEval c) := by
      rw [postcomp_one_comp_homOneEval]; infer_instance
    exact preservesLimits_of_natIso (isoCompInv (postcomp One.{v, u} g) (homOneEval c))

/-- A 1-cell of `CAT` is `{1}`-cocontinuous if and only if it preserves colimits. -/
theorem isACocontinuous_one_iff.{w₀} (g : d ⟶ c) :
    IsACocontinuous.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) g ↔
      PreservesColimitsOfSize.{w₀, w₀} g.toFunctor := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have : PreservesColimitsOfSize.{w₀, w₀} (postcomp One.{v, u} g) := h rfl
    have : PreservesColimitsOfSize.{w₀, w₀} (homOneEval d ⋙ g.toFunctor) := by
      rw [← postcomp_one_comp_homOneEval]; infer_instance
    exact preservesColimits_of_natIso (isoInvComp (homOneEval d) g.toFunctor)
  · subst ha
    have : PreservesColimitsOfSize.{w₀, w₀} (postcomp One.{v, u} g ⋙ homOneEval c) := by
      rw [postcomp_one_comp_homOneEval]; infer_instance
    exact preservesColimits_of_natIso (isoCompInv (postcomp One.{v, u} g) (homOneEval c))

end OneProperties

end UlmerBialgebras.Paper.CatTwo
