module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Models.CatTwoAdj

/-!
# The terminal category is bi-dense in `CAT`

The class `{1}`, consisting of the terminal category `UlmerBialgebras.One` alone, is bi-dense
(Definition 7.1) in the strict 2-category `Cat.{v, u}` (`CategoryTheory.Cat.bicategory`). This is
the density that makes Section 5 the case `K = CAT`, `A = {1}` of Section 7: the hom-category
`CAT(1, C) = (1 ⥤ C)` is `C` itself (`UlmerBialgebras.oneEquiv`).

Both halves of bi-density come from the equivalence `UlmerBialgebras.oneEval C : (1 ⥤ C) ⥤ C`:
* a compatible family of 2-cells on `1`-representables is determined by its components at the
  constant functors (`isACellDense_one`);
* a pseudonatural family `F : (1 ⥤ d) ⥤ (1 ⥤ c)` is represented by the functor
  `const ⋙ F ⋙ eval : d ⥤ c` (`PsFamily.oneRepresentation`).
The only 1-cell `1 ⟶ 1` is the identity (`eq_id₁_of_one`), so the coherence conditions of a
pseudonatural family reduce to their unit condition.

## Main results

* `UlmerBialgebras.Paper.isACellDense_one`: the local half of bi-density.
* `UlmerBialgebras.Paper.PsFamily.oneRepresentation`: every pseudonatural family is representable.
* `UlmerBialgebras.Paper.isBiDense_one`: `{1}` is bi-dense in `Cat.{v, u}`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
  and Section 7.1 (the class `{1}` in `CAT`)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper

open CategoryTheory UlmerBialgebras

/-- The terminal category has a single object. -/
instance subsingleton_one : Subsingleton (One.{v, u} : Type u) := ⟨fun ⟨⟩ ⟨⟩ => rfl⟩

/-- The terminal category has at most one morphism between any two objects. -/
instance subsingleton_one_hom (a b : One.{v, u}) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The only 1-cell `1 ⟶ 1` of `CAT` is the identity. -/
lemma eq_id₁_of_one (e : One.{v, u} ⟶ One.{v, u}) : e = 𝟙 One.{v, u} :=
  Cat.Hom.ext (CategoryTheory.Functor.ext (fun _ => Subsingleton.elim _ _) (fun _ _ _ =>
      Subsingleton.elim _ _))

/-- Evaluation at the unique object of `1` is fully faithful. -/
noncomputable def oneEvalFullyFaithful (C : Cat.{v, u}) : ((catHomEquivalence One C).functor ⋙
    oneEval C).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- Constant functors regarded as CAT 1-cells, functorially in their value. -/
def oneConst (C : Cat.{v, u}) : C ⥤ (One.{v, u} ⟶ C) where
  obj c := ((Functor.const One.{v, u}).obj c).toCatHom
  map f := ((Functor.const One.{v, u}).map f).toCatHom₂

/-- A functor `k : 1 ⥤ C` is isomorphic to the constant functor at `k(*)`, by the identity at
`*`. -/
noncomputable def isoConstOne {C : Cat.{v, u}} (k : One.{v, u} ⟶ C) :
    k ≅ (oneConst C).obj (k.toFunctor.obj One.star) :=
  (oneEvalFullyFaithful C).preimageIso (Iso.refl (k.toFunctor.obj One.star))

/-- The component of `isoConstOne k` at `*` is the identity. -/
@[simp] lemma isoConstOne_hom_app {C : Cat.{v, u}} (k : One.{v, u} ⟶ C) :
    (isoConstOne k).hom.toNatTrans.app One.star = 𝟙 _ :=
  (oneEvalFullyFaithful C).map_preimage _

/-- The inverse of `isoConstOne k` has the identity as component at `*`. -/
@[simp] lemma isoConstOne_inv_app {C : Cat.{v, u}} (k : One.{v, u} ⟶ C) :
    (isoConstOne k).inv.toNatTrans.app One.star = 𝟙 _ :=
  (oneEvalFullyFaithful C).map_preimage _

/-- Two natural transformations between functors out of `1` agree once they agree at `*`. -/
lemma natTrans_one_ext {C : Cat.{v, u}} {F G : One.{v, u} ⟶ C} {α β : F ⟶ G}
    (h : α.toNatTrans.app One.star = β.toNatTrans.app One.star) : α = β :=
  (oneEvalFullyFaithful C).map_injective h

/-! ## The local half -/

/-- The 2-cell `p ⟶ q` of `CAT` defined by a family of 2-cells on the `{1}`-representables: its
component at `c` is the component at `*` of the family at the constant functor `c`. -/
@[simps]
def ACellFamily.oneCell {C D : Cat.{v, u}} {p q : C ⟶ D}
    (Φ : ACellFamily (fun X : Cat.{v, u} => X = One.{v, u}) p q) : p ⟶ q where
  toNatTrans := {
    app c := ((Φ.app rfl).app ((oneConst C).obj c)).toNatTrans.app One.star
    naturality c c' f := by
      have h := congr(($((Φ.app rfl).naturality ((oneConst C).map f))).toNatTrans.app One.star)
      simpa [oneConst] using h }

/-- The family of 2-cells at `k : 1 ⥤ C` agrees at `*` with the family at the constant functor
at `k(*)`. -/
lemma ACellFamily.app_app_star {C D : Cat.{v, u}} {p q : C ⟶ D}
    (Φ : ACellFamily (fun X : Cat.{v, u} => X = One.{v, u}) p q) (k : One.{v, u} ⟶ C) :
    ((Φ.app rfl).app k).toNatTrans.app One.star
      = ((Φ.app rfl).app ((oneConst C).obj (k.toFunctor.obj One.star))).toNatTrans.app One.star
          := by
  have h := congr(($((Φ.app rfl).naturality (isoConstOne k).hom)).toNatTrans.app One.star)
  simp only [postcomp_map, Cat.Hom₂.comp_app, Cat.whiskerRight_app, isoConstOne_hom_app] at h
  simpa [oneConst] using h.symm

/-- **The local half of bi-density of `{1}` in `CAT`**: 2-cells `p ⟶ q` correspond to compatible
families of 2-cells on the `{1}`-representables. -/
theorem isACellDense_one : IsACellDense (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) := by
  intro C D p q Φ
  refine ⟨ACellFamily.oneCell Φ, fun x hx => ?_, fun α hα => ?_⟩
  · subst hx
    ext k : 2
    refine natTrans_one_ext ?_
    simp only [postcompNat_app, Cat.whiskerLeft_app, ACellFamily.oneCell_toNatTrans_app]
    exact (ACellFamily.app_app_star Φ k).symm
  · refine catVU_cell_ext fun c => ?_
    have h := congrArg (fun β : postcomp One.{v, u} p ⟶ postcomp One.{v, u} q =>
        (NatTrans.app β ((oneConst C).obj c)).toNatTrans.app One.star)
      (hα rfl)
    simpa [oneConst] using h

/-! ## Representability of pseudonatural families -/

section Representation

variable {d c : Cat.{v, u}} (G : PsFamily (fun X : Cat.{v, u} => X = One.{v, u}) d c)

/-- The functor `d ⥤ c` representing a pseudonatural family on the `{1}`-representables:
`const ⋙ F ⋙ eval`, where `F : (1 ⥤ d) ⥤ (1 ⥤ c)` is the component of the family at `1`. -/
def PsFamily.oneFunctor : d ⥤ c :=
  oneConst d ⋙ G.fn rfl ⋙ (catHomEquivalence One c).functor ⋙ oneEval c

/-- The comparison `k ⋙ G.oneFunctor ≅ F(k)`, at `k : 1 ⥤ d`. -/
noncomputable def PsFamily.oneIsoApp (k : One.{v, u} ⟶ d) :
    (postcomp One.{v, u} G.oneFunctor.toCatHom).obj k ≅ (G.fn rfl).obj k :=
  (oneEvalFullyFaithful c).preimageIso (by
    let e := ((catHomEquivalence One c).functor ⋙ oneEval c).mapIso
      ((G.fn rfl).mapIso (isoConstOne k).symm)
    exact e)

/-- The component of `G.oneIsoApp k` at `*`. -/
@[simp] lemma PsFamily.oneIsoApp_hom_app (k : One.{v, u} ⟶ d) :
    (G.oneIsoApp k).hom.toNatTrans.app One.star = ((G.fn rfl).map (isoConstOne
        k).inv).toNatTrans.app One.star :=
  (oneEvalFullyFaithful c).map_preimage _

/-- The comparison `postcomp 1 G.oneFunctor ≅ F`, natural in `k`. -/
noncomputable def PsFamily.oneIso :
    postcomp One.{v, u} G.oneFunctor.toCatHom ≅ G.fn rfl :=
  NatIso.ofComponents G.oneIsoApp fun {k k'} β => by
    have key : ((oneConst d).map (β.toNatTrans.app One.star)) ≫
        (isoConstOne k').inv = (isoConstOne k).inv ≫ β :=
      natTrans_one_ext (by simp [oneConst])
    refine natTrans_one_ext ?_
    simp only [postcomp_map, Cat.Hom₂.comp_app, Cat.whiskerRight_app, oneIsoApp_hom_app]
    have h := congr(((G.fn rfl).map $key).toNatTrans.app One.star)
    simp only [CategoryTheory.Functor.map_comp, Cat.Hom₂.comp_app] at h
    exact h

/-- **Representability**: a pseudonatural family on the `{1}`-representables is induced by the
functor `G.oneFunctor`. -/
noncomputable def PsFamily.oneRepresentation : G.toAHomFamily.Representation where
  g := G.oneFunctor.toCatHom
  iso x hx := by subst hx; exact G.oneIso
  iso_nat x y hx hy e k := by
    subst hx; subst hy
    obtain rfl := eq_id₁_of_one e
    rw [G.nat_id]
    refine catVU_cell_ext fun z => ?_
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, eqToHom_refl, Category.id_comp]
    exact (Category.comp_id _).trans rfl

end Representation

/-- **`{1}` is bi-dense in `CAT`** ([forsman2026syntactic], Definition 7.1): the class consisting
of the terminal category alone is bi-dense in the strict 2-category `Cat.{v, u}`. -/
theorem isBiDense_one : IsBiDense (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) :=
  ⟨isACellDense_one, fun _ _ G => ⟨G.oneRepresentation⟩⟩

end UlmerBialgebras.Paper
