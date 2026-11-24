module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Models.CatProductPi

/-!
# Abstract inserters and equifiers in `CAT` and the concrete ones

For an inserter `I` of `f, g` in `CAT`, the canonical functor `I.pt ⥤ Ins f g` is an equivalence,
and likewise for the equifier of a bialgebraic datum. This identifies `u_B : E.pt ⥤ B.c` with the
forgetful functor of a concrete equifier category over `Ins f g`, up to an equivalence
(Theorem 5.7). It works in `Cat.{v, u}` for all `u, v`: the concrete categories `Ins f g` live in
`Type (max u v)`, so the comparisons are equivalences rather than isomorphisms of objects of `CAT`.

## Main results

* `UlmerBialgebras.CatBridge.insTo`: the comparison functor from an inserter in `CAT` to `Ins f g`,
  an equivalence.
* `UlmerBialgebras.CatBridge.α₀`, `UlmerBialgebras.CatBridge.β₀`: the equations of a bialgebraic
  datum, transported to `Ins.forget f g`.
* `UlmerBialgebras.CatBridge.equifTo`: the comparison functor from an equifier of `B.α, B.β` to the
  concrete category of bialgebras `Q B`, an equivalence.
* `UlmerBialgebras.CatBridge.uB_eq`: `u_B` is `equifTo B E` followed by the concrete forgetful
  functor.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1, Remark 2.2, Definition 3.1 and Theorem 5.7
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe v u

namespace UlmerBialgebras.CatBridge

open CategoryTheory
open Product (constOne constCell constCellComp)

variable {a b : Cat.{v, u}} {f g : a ⟶ b} (I : Inserter f g)

/-- The comparison functor from an inserter in `CAT` to the concrete inserter category. -/
def insTo : (I.pt : Type u) ⥤ Ins f.toFunctor g.toFunctor :=
  Ins.liftFunctor I.u.toFunctor I.φ.toNatTrans

/-- The 2-cell `constOne y ≫ f ⟶ constOne y ≫ g` given by a morphism `f y ⟶ g y`. -/
def constCell₂ {y : (a : Type u)} (φ : f.toFunctor.obj y ⟶ g.toFunctor.obj y) :
    constOne y ≫ f ⟶ constOne y ≫ g :=
  { toNatTrans :=
    { app := fun _ => φ
      naturality := fun p q h => by
        cases p; cases q
        -- The only morphism of the terminal category is an identity, sent to identities.
        exact (f.toFunctor.map_id y =≫ φ).trans ((Category.id_comp φ).trans
          ((Category.comp_id φ).symm.trans (φ ≫= (g.toFunctor.map_id y).symm))) } }

instance : (insTo I).Faithful where
  map_injective {p q} h₁ h₂ h := by
    have key : constCell h₁ = constCell h₂ := I.lift₂_uniq _ _ (by
      apply Cat.Hom₂.ext
      ext s
      cases s
      exact congr(($(h)).base))
    exact congr(($(key)).toNatTrans.app One.star)

instance : (insTo I).EssSurj where
  mem_essImage y := by
    refine ⟨(I.lift (constOne y.pt) (constCell₂ y.cell)).toFunctor.obj One.star, ⟨eqToIso ?_⟩⟩
    have hpt : ((insTo I).obj
        ((I.lift (constOne y.pt) (constCell₂ y.cell)).toFunctor.obj One.star)).pt = y.pt :=
      congr(($(I.lift_u (constOne y.pt) (constCell₂ y.cell))).toFunctor.obj One.star)
    refine Ins.obj_ext hpt ?_
    have := congr(($(I.lift_φ (constOne y.pt) (constCell₂ y.cell))).toNatTrans.app One.star)
    simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app] at this
    exact this

instance : (insTo I).Full where
  map_surjective {p q} m := by
    have hc : ((eqToHom (Category.assoc (constOne p) I.u f) ≫ (constOne p ◁ I.φ) ≫
        eqToHom (Category.assoc (constOne p) I.u g).symm) ≫ (constCellComp I.u m.base ▷ g)) =
        (constCellComp I.u m.base ▷ f) ≫ (eqToHom (Category.assoc (constOne q) I.u f) ≫
          (constOne q ◁ I.φ) ≫ eqToHom (Category.assoc (constOne q) I.u g).symm) := by
      apply Cat.Hom₂.ext
      ext s
      cases s
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact m.w
    refine ⟨(I.lift₂ (constCellComp I.u m.base) hc).toNatTrans.app One.star, ?_⟩
    ext
    exact congr(($(I.lift₂_u (constCellComp I.u m.base) hc)).toNatTrans.app One.star)

instance : (insTo I).IsEquivalence where

/-- Two natural transformations agreeing at an object agree at every isomorphic object. -/
lemma app_eq_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α β : F ⟶ G)
    {z z' : C} (i : z ≅ z') (h : α.app z = β.app z) : α.app z' = β.app z' := by
  rw [← cancel_epi (F.map i.hom), α.naturality, β.naturality, h]

section Equifier

open Paper

variable (B : BialgDatum (Obj := Cat.{v, u})) (E : Equifier B.α B.β)

/-- The inverse of the comparison equivalence of the inserter of `B`. -/
noncomputable abbrev insFrom : Ins B.f.toFunctor B.g.toFunctor ⥤ (B.ins.pt : Type u) :=
  (insTo B.ins).inv

/-- `insFrom` followed by `u` is the forgetful functor of `Ins f g`, up to the counit. -/
noncomputable def insFromU :
    insFrom B ⋙ B.ins.u.toFunctor ≅ Ins.forget B.f.toFunctor B.g.toFunctor :=
  Functor.isoWhiskerRight (insTo B.ins).asEquivalence.counitIso
    (Ins.forget B.f.toFunctor B.g.toFunctor) ≪≫ Functor.leftUnitor _

/-- An equation of `B`, transported to the concrete inserter category. -/
noncomputable def transport (γ : B.ins.u ≫ B.f' ⟶ B.ins.u ≫ B.g') :
    Ins.forget B.f.toFunctor B.g.toFunctor ⋙ B.f'.toFunctor ⟶
      Ins.forget B.f.toFunctor B.g.toFunctor ⋙ B.g'.toFunctor :=
  Functor.whiskerRight (insFromU B).inv B.f'.toFunctor ≫
    Functor.whiskerLeft (insFrom B) γ.toNatTrans ≫
      Functor.whiskerRight (insFromU B).hom B.g'.toFunctor

/-- The first equation of `B`, transported to the concrete inserter category. -/
noncomputable abbrev α₀ := transport B B.α

/-- The second equation of `B`, transported to the concrete inserter category. -/
noncomputable abbrev β₀ := transport B B.β

/-- The concrete category of bialgebras: an equifier category over `Ins f g`. -/
abbrev Q := Equif (α₀ B) (β₀ B)

/-- The transported 2-cells `α₀ B` and `β₀ B` agree at an object `y` of the inserter iff `B.α` and
`B.β` agree at its image `(insFrom B).obj y`. -/
lemma transport_app_eq_iff (y : Ins B.f.toFunctor B.g.toFunctor) :
    (α₀ B).app y = (β₀ B).app y ↔
      B.α.toNatTrans.app ((insFrom B).obj y) = B.β.toNatTrans.app ((insFrom B).obj y) := by
  simp only [transport, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  constructor
  · intro h
    simpa [← Functor.map_comp_assoc] using
      congrArg (fun t => B.f'.toFunctor.map ((insFromU B).hom.app y) ≫ t ≫
        B.g'.toFunctor.map ((insFromU B).inv.app y)) h
  · intro h
    rw [h]

/-- The comparison functor from the equifier to the concrete category of bialgebras. -/
noncomputable def equifTo : (E.pt : Type u) ⥤ Q B :=
  Equif.liftFunctor (E.e.toFunctor ⋙ insTo B.ins) (by
    ext x
    refine (transport_app_eq_iff B _).2 ?_
    refine app_eq_of_iso _ _ ((insTo B.ins).asEquivalence.unitIso.app (E.e.toFunctor.obj x)) ?_
    exact congr(($(E.cond)).toNatTrans.app x))

/-- `u_B` is the comparison functor followed by the concrete forgetful functor. -/
lemma uB_eq : (B.uB E).toFunctor =
    equifTo B E ⋙ (Equif.forget (α₀ B) (β₀ B) ⋙ Ins.forget _ _) := rfl

instance : (equifTo B E).Faithful where
  map_injective {p q} h₁ h₂ h := by
    have h' : E.e.toFunctor.map h₁ = E.e.toFunctor.map h₂ :=
      (insTo B.ins).map_injective ((Equif.forget (α₀ B) (β₀ B)).congr_map h)
    have key : constCell h₁ = constCell h₂ := E.faithful _ _ (by
      apply Cat.Hom₂.ext
      ext s
      cases s
      exact h')
    exact congr(($(key)).toNatTrans.app One.star)

instance : (equifTo B E).Full where
  map_surjective {p q} m := by
    obtain ⟨n, hn⟩ := (insTo B.ins).map_surjective ((Equif.forget (α₀ B) (β₀ B)).map m)
    obtain ⟨a, ha⟩ := E.full (constCellComp E.e n)
    refine ⟨a.toNatTrans.app One.star, (Equif.forget (α₀ B) (β₀ B)).map_injective ?_⟩
    change (insTo B.ins).map (E.e.toFunctor.map _) = _
    rw [← hn]
    congr 1
    exact congr(($(ha)).toNatTrans.app One.star)

instance : (equifTo B E).EssSurj where
  mem_essImage y := by
    have hz : B.α.toNatTrans.app ((insFrom B).obj y.obj) =
        B.β.toNatTrans.app ((insFrom B).obj y.obj) := (transport_app_eq_iff B _).1 y.property
    have hc : constOne ((insFrom B).obj y.obj) ◁ B.α =
        constOne ((insFrom B).obj y.obj) ◁ B.β := by
      apply Cat.Hom₂.ext
      ext s
      cases s
      exact hz
    let w := (E.lift _ hc).toFunctor.obj One.star
    have hw : E.e.toFunctor.obj w = (insFrom B).obj y.obj :=
      congr(($(E.lift_e _ hc)).toFunctor.obj One.star)
    refine ⟨w, ⟨(Equif.forget (α₀ B) (β₀ B)).preimageIso ?_⟩⟩
    exact (insTo B.ins).mapIso (eqToIso hw) ≪≫ (insTo B.ins).asEquivalence.counitIso.app y.obj

instance : (equifTo B E).IsEquivalence where

end Equifier

end UlmerBialgebras.CatBridge
