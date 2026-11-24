module

public import UlmerBialgebras.Monadicity.CoalgChainIteration
public import Foundations.CategoryTheory.Limits.CoprodConnected
public import UlmerBialgebras.Monadicity.FreeIns

/-!
# Free objects for the forgetful functor of an inserter, by a transfinite chain

Let `F, G : C ⥤ D` be a parallel pair of functors, let `L ⊣ G` be an adjunction and let
`X : C`.  The objects of the inserter `Ins F G` equipped with a morphism from `X` are
exactly the algebras of the endofunctor

  `S : C ⥤ C`,  `S Y = X ⨿ L (F Y)`

(`UlmerBialgebras.Ins.freeEndo`), the correspondence being given by the adjunction `L ⊣ G`.  The
free object on `X` is therefore the initial `S`-algebra, which is produced by the
transfinite chain of `InitialAlgebraChain.lean` as soon as `S` preserves colimits of shape
a well-ordered type `J` without maximal element (`C` having the colimits needed to run the
chain).

## Main results

* `UlmerBialgebras.Ins.hasInitial_structuredArrow_of_shape` — the comma category
  `X ↓ Ins.forget F G` has an initial object;
* `UlmerBialgebras.Ins.forget_isRightAdjoint_of_shape` — the forgetful functor `Ins F G ⥤ C` has a
  left adjoint.

This is Theorem 5.5 (1), for a general well-ordered chain.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits Endofunctor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Ins

/-- A morphism of the underlying objects of two objects of the inserter is a morphism of
the inserter exactly when it is compatible with the transposed structure morphisms. -/
lemma insHom_iff_transpose {F G : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ G) (Y Z : Ins F G)
    (k : Y.pt ⟶ Z.pt) :
    (Y.cell ≫ G.map k = F.map k ≫ Z.cell) ↔
      (cellTranspose adj Y ≫ k = L.map (F.map k) ≫ cellTranspose adj Z) := by
  constructor
  · intro h
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      cellTranspose, cellTranspose, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  · intro h
    have := congr(adj.homEquiv _ _ $h)
    rwa [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      cellTranspose, cellTranspose, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

section FreeEndo

variable (F : C ⥤ D) (L : D ⥤ C) [HasBinaryCoproducts C] (X : C)

/-- The endofunctor `Y ↦ X ⨿ L (F Y)` of `C`, whose algebras are the objects of the
inserter `Ins F G` equipped with a morphism from `X`. -/
@[simps, implicit_reducible]
noncomputable def freeEndo : C ⥤ C where
  obj Y := X ⨿ L.obj (F.obj Y)
  map f := coprod.map (𝟙 X) (L.map (F.map f))
  map_id _ := by simp
  map_comp f g := by simp

/-- The left coprojection `X ⟶ X ⨿ L (F Y)` is preserved by `(freeEndo F L X).map f`. -/
@[reassoc (attr := simp)]
lemma inl_freeEndo_map {Y Y' : C} (f : Y ⟶ Y') :
    (coprod.inl : X ⟶ X ⨿ L.obj (F.obj Y)) ≫ (freeEndo F L X).map f
      = (coprod.inl : X ⟶ X ⨿ L.obj (F.obj Y')) := by
  simp

/-- `freeEndo F L X` is the composite of `F ⋙ L` with `X ⨿ -`. -/
noncomputable def freeEndoIso : freeEndo F L X ≅ (F ⋙ L) ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp)

/-- The base coalgebra of the chain: `X` with the coproduct injection. -/
@[implicit_reducible]
noncomputable def baseCoalgebra : Endofunctor.Coalgebra (freeEndo F L X) :=
  ⟨X, coprod.inl⟩

/-- For connected `J`, if `F` and `L` preserve colimits of shape `J`, so does
`freeEndo F L X`. -/
lemma preservesColimitsOfShape_freeEndo {J : Type w} [LinearOrder J] [IsConnected J]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J L] :
    PreservesColimitsOfShape J (freeEndo F L X) := by
  have h₁ : PreservesColimitsOfShape J (coprod.functor.obj X) :=
    coprod_preservesConnectedColimits X
  have h₂ : PreservesColimitsOfShape J ((F ⋙ L) ⋙ coprod.functor.obj X) := inferInstance
  exact preservesColimitsOfShape_of_natIso (freeEndoIso F L X).symm

variable {F L X}

/-- The object of the inserter underlying an algebra of `freeEndo F L X`. -/
@[implicit_reducible]
noncomputable def ofAlgebra {G : C ⥤ D} (adj : L ⊣ G) (Z : Endofunctor.Algebra (freeEndo F L X)) :
    Ins F G :=
  ⟨Z.a, adj.homEquiv _ _ (coprod.inr ≫ Z.str)⟩

/-- The morphism from `X` attached to an algebra of `freeEndo F L X`. -/
noncomputable def algebraUnit (Z : Endofunctor.Algebra (freeEndo F L X)) : X ⟶ Z.a :=
  coprod.inl ≫ Z.str

/-- The transposed structure morphism of `ofAlgebra adj Z` is `coprod.inr ≫ Z.str`. -/
lemma cellTranspose_ofAlgebra {G : C ⥤ D} (adj : L ⊣ G)
    (Z : Endofunctor.Algebra (freeEndo F L X)) :
    cellTranspose adj (ofAlgebra adj Z) = coprod.inr ≫ Z.str :=
  (adj.homEquiv _ _).symm_apply_apply _

/-- The algebra of `freeEndo F L X` attached to an object of the inserter under `X`. -/
@[implicit_reducible]
noncomputable def toAlgebra {G : C ⥤ D} (adj : L ⊣ G) (Y : Ins F G) (h : X ⟶ Y.pt) :
    Endofunctor.Algebra (freeEndo F L X) :=
  ⟨Y.pt, coprod.desc h (cellTranspose adj Y)⟩

/-- Morphisms of algebras of `freeEndo F L X` are exactly the morphisms of the inserter
which are compatible with the morphisms from `X`. -/
lemma algHom_iff {G : C ⥤ D} (adj : L ⊣ G) (Z : Endofunctor.Algebra (freeEndo F L X))
    (Y : Ins F G) (h : X ⟶ Y.pt) (k : Z.a ⟶ Y.pt) :
    ((freeEndo F L X).map k ≫ (toAlgebra adj Y h).str = Z.str ≫ k) ↔
      ((ofAlgebra adj Z).cell ≫ G.map k = F.map k ≫ Y.cell ∧ algebraUnit Z ≫ k = h) := by
  rw [insHom_iff_transpose adj, cellTranspose_ofAlgebra]
  constructor
  · intro hk
    refine ⟨?_, ?_⟩
    · have h' := (coprod.inr : L.obj (F.obj Z.a) ⟶ _) ≫= hk
      simpa [toAlgebra] using h'.symm
    · have h' := (coprod.inl : X ⟶ _) ≫= hk
      simpa [toAlgebra, algebraUnit] using h'.symm
  · rintro ⟨h₁, h₂⟩
    refine coprod.hom_ext ?_ ?_
    · simpa [toAlgebra, algebraUnit] using h₂.symm
    · simpa [toAlgebra] using h₁.symm

/-- The base of the chain has the universal property required by
`UlmerBialgebras.CoalgChain.isInitialAlgebra`. -/
lemma existsUnique_base (X : C) (Z : Endofunctor.Algebra (freeEndo F L X)) :
    ∃! k : X ⟶ Z.a, k = (baseCoalgebra F L X).str ≫ (freeEndo F L X).map k ≫ Z.str := by
  refine ⟨coprod.inl ≫ Z.str, ?_, ?_⟩
  · change coprod.inl ≫ Z.str
        = coprod.inl ≫ (freeEndo F L X).map (coprod.inl ≫ Z.str) ≫ Z.str
    rw [← Category.assoc, inl_freeEndo_map]
  · intro k hk
    simpa [baseCoalgebra] using hk

end FreeEndo

section Main

variable {F G : C ⥤ D} {L : D ⥤ C} [HasBinaryCoproducts C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

variable (F L)

/-- The transfinite chain computing the free object of `Ins F G` on `X`. -/
noncomputable def freeChain (X : C) (hmax : ∀ j : J, ¬ IsMax j) :
    CoalgChain (freeEndo F L X) J :=
  coalgChain (freeEndo F L X) hmax (baseCoalgebra F L X)

/-- At the bottom stage of `freeChain`, there is a unique `k` to an algebra `Z`
satisfying `Cond Z ⊥ k`. -/
lemma freeChain_base (X : C) (hmax : ∀ j : J, ¬ IsMax j)
    (Z : Endofunctor.Algebra (freeEndo F L X)) :
    ∃! k : (freeChain F L X hmax).W.obj (⊥ : J) ⟶ Z.a, (freeChain F L X hmax).Cond Z ⊥ k :=
  CoalgChain.existsUnique_cond_bot_of_iso
    (coalgChainBotIso (freeEndo F L X) hmax (baseCoalgebra F L X))
    (coalgChainBotIso_str (freeEndo F L X) hmax (baseCoalgebra F L X))
    (existsUnique_base X Z)

variable [IsConnected J] [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J L]

/-- The initial algebra of `freeEndo F L X`. -/
noncomputable def freeAlgebra (X : C) (hmax : ∀ j : J, ¬ IsMax j) :
    Endofunctor.Algebra (freeEndo F L X) :=
  letI := preservesColimitsOfShape_freeEndo (J := J) F L X
  (freeChain F L X hmax).algebra

/-- The free algebra is an initial algebra. -/
noncomputable def isInitialFreeAlgebra (X : C) (hmax : ∀ j : J, ¬ IsMax j) :
    IsInitial (freeAlgebra F L X hmax) :=
  letI := preservesColimitsOfShape_freeEndo (J := J) F L X
  (freeChain F L X hmax).isInitialAlgebra (freeChain_base F L X hmax)

variable {F L}

/-- **Free objects for the inserter**: the comma category `X ↓ Ins.forget F G` has an
initial object. -/
noncomputable def isInitialStructuredArrow (adj : L ⊣ G) (X : C)
    (hmax : ∀ j : J, ¬ IsMax j) :
    IsInitial (StructuredArrow.mk (S := X) (T := Ins.forget F G)
      (Y := ofAlgebra adj (freeAlgebra F L X hmax))
      (algebraUnit (freeAlgebra F L X hmax))) := by
  set A := freeAlgebra F L X hmax with hA
  refine IsInitial.ofUniqueHom (fun T => ?_) (fun T m => ?_)
  · refine StructuredArrow.homMk (⟨((isInitialFreeAlgebra F L X hmax).to
      (toAlgebra adj T.right T.hom)).f, ?_⟩ : ofAlgebra adj A ⟶ T.right) ?_
    · exact ((algHom_iff adj A T.right T.hom _).1
        ((isInitialFreeAlgebra F L X hmax).to (toAlgebra adj T.right T.hom)).h).1
    · simpa using ((algHom_iff adj A T.right T.hom _).1
        ((isInitialFreeAlgebra F L X hmax).to (toAlgebra adj T.right T.hom)).h).2
  · apply StructuredArrow.hom_ext
    apply Ins.hom_ext
    have hm : (freeEndo F L X).map m.right.base ≫ (toAlgebra adj T.right T.hom).str
        = A.str ≫ m.right.base := by
      refine (algHom_iff adj A T.right T.hom _).2 ⟨m.right.w, ?_⟩
      simpa using StructuredArrow.w m
    have hu := (isInitialFreeAlgebra F L X hmax).hom_ext
      (⟨m.right.base, hm⟩ : A ⟶ toAlgebra adj T.right T.hom)
      ((isInitialFreeAlgebra F L X hmax).to (toAlgebra adj T.right T.hom))
    exact Endofunctor.Algebra.Hom.ext_iff.mp hu

/-- **Free objects for the inserter.** -/
theorem hasInitial_structuredArrow_of_shape (adj : L ⊣ G) (X : C)
    (hmax : ∀ j : J, ¬ IsMax j) :
    HasInitial (StructuredArrow X (Ins.forget F G)) :=
  (isInitialStructuredArrow adj X hmax).hasInitial

end Main

/-- **The forgetful functor of an inserter has a left adjoint** (Theorem 5.5 (1) of
[forsman2026syntactic]). -/
theorem forget_isRightAdjoint_of_shape {F G : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ G)
    [HasBinaryCoproducts C]
    (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J C] [IsConnected J] [PreservesColimitsOfShape J F]
    (hmax : ∀ j : J, ¬ IsMax j) :
    (Ins.forget F G).IsRightAdjoint := by
  have : PreservesColimitsOfShape J L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := fun X : C => hasInitial_structuredArrow_of_shape (F := F) (J := J) adj X hmax
  exact isRightAdjointOfStructuredArrowInitials _

end Ins

end UlmerBialgebras
