module

public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3
public import UlmerBialgebras.Kan.ColimKan
public import UlmerBialgebras.Kan.LimKan

/-!
# Algebras over a monad as an equifier over an inserter (for Corollary 4.13)

`monadDatum T` is the bialgebraic datum in `CAT` with function supports `T, 𝟭 : C ⟶ C`
(so the inserter is the category of `T`-structured objects) and equational supports
`(T T, 𝟭), (𝟭, 𝟭) : C ⟶ C × C`, whose two equations are associativity and the unit law;
`monadEquif T` exhibits `T.Algebra` as its equifier, with `u_B = T.forget`.

## Main results

* `UlmerBialgebras.Paper.monadEqnLeft`, `UlmerBialgebras.Paper.monadEqnRight`: the two sides of
  the associativity and unit laws on the inserter `Ins(T, 𝟭)`, for a monad `T` on any category.
* `UlmerBialgebras.Paper.monadAlgebraEquivEquif`: `T.Algebra` is equivalent to their equifier.
* `UlmerBialgebras.Paper.monadDatum`: the bialgebraic datum in `CAT` of algebras over a monad `T`.
* `UlmerBialgebras.Paper.monadEquif`: `T.Algebra` as the equifier of the two equations of
  `monadDatum T`.
* `UlmerBialgebras.Paper.quotientInitial_of_jointlyEpi'`: a left extension along `I ⟶ 1` with
  jointly epimorphic legs is quotient initial.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.13
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Plain

variable {C : Type u} [Category.{v} C] (T : Monad C)

/-- The left-hand sides of the associativity and unit laws on `T`-structured objects: the natural
transformation with components `(T a ≫ a, η ≫ a) : (T T X, X) ⟶ (X, X)` at `a : T X ⟶ X`. -/
@[simps]
def monadEqnLeft : Ins.forget (T : C ⥤ C) (𝟭 C) ⋙ ((T : C ⥤ C) ⋙ (T : C ⥤ C)).prod' (𝟭 C) ⟶
    Ins.forget (T : C ⥤ C) (𝟭 C) ⋙ (𝟭 C).prod' (𝟭 C) where
  app X := (T.map X.cell ≫ X.cell, T.η.app X.pt ≫ X.cell)
  naturality X Y f := by
    have hw : X.cell ≫ f.base = T.map f.base ≫ Y.cell := f.w
    refine Prod.ext ?_ ?_
    · have h1 : (T.map X.cell ≫ X.cell) ≫ f.base =
          T.map (T.map f.base) ≫ T.map Y.cell ≫ Y.cell := by
        rw [Category.assoc, hw, ← Category.assoc, ← T.map_comp, hw, T.map_comp,
          Category.assoc]
      exact h1.symm
    · have h2 : (T.η.app X.pt ≫ X.cell) ≫ f.base = f.base ≫ T.η.app Y.pt ≫ Y.cell := by
        rw [Category.assoc, hw, ← Category.assoc, ← T.η.naturality f.base]
        simp
      exact h2.symm

/-- The right-hand sides of the associativity and unit laws on `T`-structured objects: the natural
transformation with components `(μ ≫ a, 𝟙) : (T T X, X) ⟶ (X, X)` at `a : T X ⟶ X`. -/
@[simps]
def monadEqnRight : Ins.forget (T : C ⥤ C) (𝟭 C) ⋙ ((T : C ⥤ C) ⋙ (T : C ⥤ C)).prod' (𝟭 C) ⟶
    Ins.forget (T : C ⥤ C) (𝟭 C) ⋙ (𝟭 C).prod' (𝟭 C) where
  app X := (T.μ.app X.pt ≫ X.cell, 𝟙 X.pt)
  naturality X Y f := by
    have hw : X.cell ≫ f.base = T.map f.base ≫ Y.cell := f.w
    refine Prod.ext ?_ ?_
    · have h1 : (T.μ.app X.pt ≫ X.cell) ≫ f.base =
          T.map (T.map f.base) ≫ T.μ.app Y.pt ≫ Y.cell := by
        rw [Category.assoc, hw, ← Category.assoc, ← T.μ.naturality f.base]
        simp
      exact h1.symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- A `T`-algebra as an object of the equifier of `monadEqnLeft T` and `monadEqnRight T`. -/
@[simps]
def monadAlgebraToEquif : T.Algebra ⥤ Equif (monadEqnLeft T) (monadEqnRight T) where
  obj A := ⟨⟨A.A, A.a⟩, Prod.ext A.assoc.symm A.unit⟩
  map f := ObjectProperty.homMk ⟨f.f, f.h.symm⟩

/-- An object of the equifier of `monadEqnLeft T` and `monadEqnRight T` as a `T`-algebra. -/
@[simps]
def equifToMonadAlgebra : Equif (monadEqnLeft T) (monadEqnRight T) ⥤ T.Algebra where
  obj X :=
    { A := X.obj.pt
      a := X.obj.cell
      unit := congrArg Prod.snd X.property
      assoc := (congrArg Prod.fst X.property).symm }
  map f := { f := f.hom.base, h := f.hom.w.symm }

/-- The category of `T`-algebras is equivalent to the equifier of the associativity and unit
laws (`monadEqnLeft T`, `monadEqnRight T`) on the inserter `Ins(T, 𝟭)` of `T`-structured
objects. -/
def monadAlgebraEquivEquif : T.Algebra ≌ Equif (monadEqnLeft T) (monadEqnRight T) :=
  CategoryTheory.Equivalence.mk (monadAlgebraToEquif T) (equifToMonadAlgebra T)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
      apply ObjectProperty.hom_ext
      apply Ins.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Plain

variable {C : Cat.{v, max u v}} (T : Monad (C : Type (max u v)))

/-- The bialgebraic datum of `T`-algebras. -/
abbrev monadDatum : BialgDatum (Obj := Cat.{v, max u v}) where
  c := C
  x := C
  y := Cat.of (Prod (C : Type (max u v)) (C : Type (max u v)))
  f := T.toFunctor.toCatHom
  g := 𝟙 C
  f' := ((T.toFunctor ⋙ T.toFunctor).prod' (𝟭 (C : Type (max u v)))).toCatHom
  g' := ((𝟭 (C : Type (max u v))).prod' (𝟭 (C : Type (max u v)))).toCatHom
  ins := catInserter T.toFunctor.toCatHom (𝟙 C)
  α := (monadEqnLeft T).toCatHom₂
  β := (monadEqnRight T).toCatHom₂

/-- `T.Algebra` is the equifier of the two equations of `monadDatum T`. -/
def monadEquif : Equifier (monadDatum T).α (monadDatum T).β where
  pt := Cat.of T.Algebra
  e := Functor.toCatHom {
         obj := fun A => ⟨A.A, A.a⟩
         map := fun {A B} f => ⟨f.f, f.h.symm⟩ }
  cond := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    exact Prod.ext A.assoc.symm A.unit
  lift h H :=
    Functor.toCatHom {
      obj := fun x =>
        { A := (h.toFunctor.obj x).pt
          a := (h.toFunctor.obj x).cell
          unit := congrArg Prod.snd (congr_app (congrArg Cat.Hom₂.toNatTrans H) x)
          assoc := (congrArg Prod.fst (congr_app (congrArg Cat.Hom₂.toNatTrans H) x)).symm }
      map := fun {x y} f => { f := (h.toFunctor.map f).base, h := (h.toFunctor.map f).w.symm }
      map_id := fun x => Monad.Algebra.Hom.ext' _ _ _ _ (by simp; rfl)
      map_comp := fun f g => Monad.Algebra.Hom.ext' _ _ _ _ (by simp; rfl) }
  lift_e h H := rfl
  lift_uniq k h H hk := by
    subst hk
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y f => ?_)
    exact Monad.Algebra.Hom.ext' _ _ _ _ (by simp; rfl)
  full {X k₁ k₂} β :=
    ⟨NatTrans.toCatHom₂ {
       app := fun x => { f := (β.toNatTrans.app x).base, h := (β.toNatTrans.app x).w.symm }
       naturality := fun x y f => by
         exact Monad.Algebra.Hom.ext' _ _ _ _ (congrArg Ins.Hom.base (β.toNatTrans.naturality f)) },
     by
       apply Cat.Hom₂.ext
       apply NatTrans.ext
       funext x
       rfl⟩
  faithful α β h := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    exact Monad.Algebra.Hom.ext' _ _ _ _ (congrArg Ins.Hom.base (congr_app (congrArg
        Cat.Hom₂.toNatTrans h) x))

section JointlyEpi

variable {I D : Cat.{v, max u v}}

/-- A left extension along `I ⟶ 1` whose legs are jointly epimorphic is quotient initial. -/
theorem quotientInitial_of_jointlyEpi' {d : I ⟶ D} (L : LeftExt (toOne I) d)
    (h : ∀ ⦃Y : (D : Type (max u v))⦄ (p q : L.ext.toFunctor.obj One.star ⟶ Y),
      (∀ i, L.unit.toNatTrans.app i ≫ p = L.unit.toNatTrans.app i ≫ q) → p = q) : QuotientInitial L
          := by
  intro Y
  refine ⟨fun a b => (leftExtHomEquiv L Y).injective ?_⟩
  ext
  exact h _ _ fun i => (((leftExtHomEquiv L Y) a).w i).trans (((leftExtHomEquiv L Y) b).w i).symm

/-- The legs of a quotient initial left extension along `I ⟶ 1` are jointly epimorphic. -/
theorem jointlyEpi_of_quotientInitial' {d : I ⟶ D} (L : LeftExt (toOne I) d)
    (hL : QuotientInitial L) ⦃Y : (D : Type (max u v))⦄ (p q : L.ext.toFunctor.obj One.star ⟶ Y)
    (hpq : ∀ i, L.unit.toNatTrans.app i ≫ p = L.unit.toNatTrans.app i ≫ q) : p = q := by
  let c := (coconeOfLeftExt L).extend p
  let ma : coconeOfLeftExt L ⟶ c := { hom := p, w := fun i => rfl }
  let mb : coconeOfLeftExt L ⟶ c := { hom := q, w := fun i => (hpq i).symm }
  have := (hL (leftExtOfCocone c)).elim ((leftExtHomEquiv L _).symm ma)
    ((leftExtHomEquiv L _).symm mb)
  exact congrArg (fun m => m.hom) ((leftExtHomEquiv L _).symm.injective this)

/-- The counit legs of a terminal right extension along `I ⟶ 1` are jointly monomorphic. -/
theorem jointlyMono_of_isTerminal' {d : I ⟶ D} (R : RightExt (toOne I) d) (hR : IsTerminal R)
    ⦃Y : (D : Type (max u v))⦄ (p q : Y ⟶ R.ext.toFunctor.obj One.star)
    (hpq : ∀ i, p ≫ R.counit.toNatTrans.app i = q ≫ R.counit.toNatTrans.app i) : p = q :=
  (isLimitConeOfRightExt hR).hom_ext hpq

/-- A right extension along `I ⟶ 1` with jointly monic counit legs is subterminal. -/
theorem subterminal_of_jointlyMono' {d : I ⟶ D} (R : RightExt (toOne I) d)
    (h : ∀ ⦃y : (D : Type (max u v))⦄ (p q : y ⟶ R.ext.toFunctor.obj One.star),
      (∀ i, p ≫ R.counit.toNatTrans.app i = q ≫ R.counit.toNatTrans.app i) → p = q) :
    Subterminal R := by
  intro Y a b
  refine (rightExtHomEquiv Y R).injective ?_
  ext
  exact h _ _ fun i => (((rightExtHomEquiv Y R) a).w i).trans (((rightExtHomEquiv Y R) b).w i).symm

end JointlyEpi

end UlmerBialgebras.Paper
