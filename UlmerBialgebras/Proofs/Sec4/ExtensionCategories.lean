module

public import UlmerBialgebras.Paper.Sec4DefsExt

/-!
# Categories of extensions over products, inserters and equifiers

Proofs of Remark 4.5 and Lemma 4.6.

## Main results

* `UlmerBialgebras.LeftExt.toUnder`: transposition along an initial left extension `L₀ = (l, η)`, an
  isomorphism of categories `LE(d, k) ≅ l \ K(X, c)` over `K(X, c)`
  (`LeftExt.toUnder_obj_bijective`, with inverse on objects `LeftExt.ofUnder`). Conversely,
  `LeftExt.exists_isInitial_of_equivalence_under`.
* `UlmerBialgebras.Inserter.leftExtToIns_obj_bijective`: the comparison `LE(d, k) ⥤ Ins(f_*, g_*)`
  is bijective on objects. Its inverse `Inserter.leftExtOfIns` lifts `(l', η')` with its cell
  `γ : f_*(l', η') ⟶ g_*(l', η')` to `(lift l' γ, lift₂ η')`, adapting
  `Inserter.exists_lift` (`UlmerBialgebras/Kan/KanInserter.lean`), where the cell came from
  an initial object.
* `UlmerBialgebras.Equifier.leftExtToEquif_obj_bijective`: the comparison `LE(d, k) ⥤ Eq(η_*, θ_*)`
  is bijective on objects, with inverse `Equifier.leftExtOfEquif`. Fullness and faithfulness come
  from `Equifier.push_full` and `Equifier.push_faithful` (`UlmerBialgebras/Kan/KanEquifier.lean`).

Product decompositions (Lemma 4.6 (1)) are `Product.kanFunctorLeft`
(`UlmerBialgebras/Kan/KanProduct.lean`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Remark 4.5 and Lemma 4.6
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w u₁ v₁

namespace UlmerBialgebras

open CategoryTheory Limits

namespace LeftExt

/-- For the unique morphism `σ : L₀ ⟶ L`, the unit of `L` is `η₀ ≫ (k ◁ σ)`. -/
lemma unit_comp_whiskerLeft_to {Obj : Type u} [Bicategory.{w, v} Obj]
    [Bicategory.Strict Obj] {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L₀ : LeftExt k d}
    (h : IsInitial L₀) (L : LeftExt k d) : L₀.unit ≫ (k ◁ (LeftExt.homCell (h.to L))) = L.unit :=
  (LeftExt.w (h.to L))

end LeftExt

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Three transported identities around a loop cancel after any preceding morphism. -/
private lemma comp_eqToHom_loop {C : Type*} [Category C] {A B B' B'' : C}
    (f : A ⟶ B) (p : B = B') (q : B' = B'') (r : B'' = B) :
    ((f ≫ eqToHom p) ≫ eqToHom q) ≫ eqToHom r = f := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

namespace LeftExt

/-- The underlying 2-cell of an `eqToHom` between left extensions. -/
lemma homCell_eqToHom {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' : LeftExt k d} (h : L = L') :
    LeftExt.homCell (eqToHom h) = eqToHom (congrArg LeftExt.ext h) := by
  subst h; rfl
/-- The underlying 2-cell of a composite of morphisms of left extensions is the composite. -/
@[simp] lemma comp_val {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L₁ L₂ L₃ : LeftExt k d}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) : LeftExt.homCell (α ≫ β) = LeftExt.homCell α ≫ LeftExt.homCell β :=
        rfl


/-! ## Remark 4.5: the coslice form of `LE(d, k)` -/

section Coslice

variable {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L₀ : LeftExt k d} (h : IsInitial L₀)

/-- Transposition along an initial left extension `L₀ = (l, η)`: `(l', η') ↦ (l', σ)`, where
`σ : L₀ ⟶ (l', η')` is the unique morphism. -/
@[simps]
noncomputable def toUnder : LeftExt k d ⥤ Under L₀.ext where
  obj L := Under.mk (LeftExt.homCell (h.to L))
  map {L L'} α :=
      Under.homMk (LeftExt.homCell α) (congr(LeftExt.homCell $(h.hom_ext (h.to L ≫ α) (h.to L'))))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (L₀) in
/-- The inverse of transposition on objects: `(l', σ) ↦ (l', (σ k) • η)`. -/
def ofUnder (U : Under L₀.ext) : LeftExt k d := LeftExt.mk U.right (L₀.unit ≫ (k ◁ U.hom))

/-- `ofUnder` is a left inverse of transposition `toUnder` on objects. -/
lemma ofUnder_toUnder_obj (L : LeftExt k d) : ofUnder L₀ ((toUnder h).obj L) = L := by
  rw [ofUnder, toUnder_obj]
  simp only [Under.mk_right, Under.mk_hom]
  rw [unit_comp_whiskerLeft_to h L]
  rfl

/-- `ofUnder` is a right inverse of transposition `toUnder` on objects. -/
lemma toUnder_obj_ofUnder (U : Under L₀.ext) : (toUnder h).obj (ofUnder L₀ U) = U := by
  have hσ : (LeftExt.homCell (h.to (ofUnder L₀ U))) = U.hom :=
    congr(LeftExt.homCell $(h.hom_ext (h.to (ofUnder L₀ U)) (LeftExt.homMk U.hom rfl)))
  rw [toUnder_obj, hσ]
  rfl

/-- Remark 4.5 of [forsman2026syntactic] on objects: transposition `LE(d, k) ⥤ l \ K(X, c)` along an
initial `L₀ = (l, η)` is bijective on objects, with inverse `ofUnder`. -/
lemma toUnder_obj_bijective : Function.Bijective (toUnder h).obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ofUnder L₀, ofUnder_toUnder_obj h, toUnder_obj_ofUnder h⟩

/-- Transposition `LE(d, k) ⥤ l \ K(X, c)` along an initial `L₀` is faithful. -/
instance : (toUnder h).Faithful where
  map_injective {_ _} _ _ H := by
    have H' := congr(CommaMorphism.right $(H))
    exact LeftExt.hom_ext H'

/-- Transposition `LE(d, k) ⥤ l \ K(X, c)` along an initial `L₀` is full. -/
instance : (toUnder h).Full where
  map_surjective {L L'} m := by
    have hw : (LeftExt.homCell (h.to L)) ≫ m.right = (LeftExt.homCell (h.to L')) := Under.w m
    refine ⟨LeftExt.homMk m.right ?_, rfl⟩
    let γ : L.ext ⟶ L'.ext := m.right
    have hw' : (LeftExt.homCell (h.to L)) ≫ γ = (LeftExt.homCell (h.to L')) := hw
    calc
      L.unit ≫ (k ◁ γ) = (L₀.unit ≫ (k ◁ (LeftExt.homCell (h.to L)))) ≫ (k ◁ γ) :=
        (unit_comp_whiskerLeft_to h L =≫ (k ◁ γ)).symm
      _ = L₀.unit ≫ ((k ◁ (LeftExt.homCell (h.to L))) ≫ (k ◁ γ)) := Category.assoc _ _ _
      _ = L₀.unit ≫ (k ◁ (LeftExt.homCell (h.to L'))) := by rw [← Bicategory.whiskerLeft_comp, hw']
      _ = L'.unit := unit_comp_whiskerLeft_to h L'

end Coslice

/-- A category of left extensions equivalent to a coslice category has an initial object. -/
lemma exists_isInitial_of_equivalence_under {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c}
    {C : Type u₁} [Category.{v₁} C] (x : C) (e : LeftExt k d ≌ Under x) :
    ∃ L : LeftExt k d, Nonempty (IsInitial L) :=
  ⟨e.inverse.obj (Under.mk (𝟙 x)), ⟨Under.mkIdInitial.isInitialObj e.inverse⟩⟩

end LeftExt

/-! ## Lemma 4.6 (2): extensions into an inserter -/

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b} (J : Inserter f g) {I X : Obj} (k : I ⟶ X)
  (d : I ⟶ J.pt)

/-- Reassociation: the extension `k ≫ x.pt.ext` factors through the inserter projection `J.u` via
the lift of `x.pt.ext` along `J`. -/
lemma comp_lift_comp_u (x : Ins (LeftExt.push k (d ≫ J.u) f) (J.twistedPush k d)) :
    k ≫ x.pt.ext = (k ≫ J.lift x.pt.ext (LeftExt.homCell x.cell)) ≫ J.u := by
  exact ((k ≫= J.lift_u x.pt.ext (LeftExt.homCell x.cell)).symm).trans
    (Category.assoc k _ J.u).symm

/-- The 2-dimensional universal property of the inserter applies to the unit of an object of
`Ins(f_*, g_*)`, transported to the lifted 1-cell. -/
lemma lift₂_condition (x : Ins (LeftExt.push k (d ≫ J.u) f) (J.twistedPush k d)) :
    strCell J d ≫ ((x.pt.unit ≫ eqToHom (comp_lift_comp_u J k d x)) ▷ g)
      = ((x.pt.unit ≫ eqToHom (comp_lift_comp_u J k d x)) ▷ f) ≫
        strCell J (k ≫ J.lift x.pt.ext (LeftExt.homCell x.cell)) := by
  set η : x.pt.ext ≫ f ⟶ x.pt.ext ≫ g := (LeftExt.homCell x.cell) with hη
  have hmor : ((x.pt.unit ▷ f) ≫ eqToHom (Category.assoc k x.pt.ext f)) ≫ (k ◁ η)
      = strCell J d ≫ (x.pt.unit ▷ g) ≫ eqToHom (Category.assoc k x.pt.ext g) :=
    (LeftExt.w x.cell)
  set l := J.lift x.pt.ext η with hl
  have hu : l ≫ J.u = x.pt.ext := J.lift_u x.pt.ext η
  have hstr : strCell J l = eqToHom (by rw [hu]) ≫ η ≫ eqToHom (by rw [hu]) := by
    rw [strCell_eq_transCell J hu, transCell_lift]
  have hmor' : (x.pt.unit ▷ f) ≫ eqToHom (Category.assoc k x.pt.ext f) ≫ (k ◁ η)
      = strCell J d ≫ (x.pt.unit ▷ g) ≫ eqToHom (Category.assoc k x.pt.ext g) := by
    simp only [← hmor, Category.assoc]
  rw [strCell_whiskerLeft, hstr]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  slice_rhs 1 3 => rw [hmor']
  simp

/-- The inverse of `Inserter.leftExtToIns` on objects: `((l', η'), γ) ↦ (lift l' γ, lift₂ η')`. -/
noncomputable def leftExtOfIns (x : Ins (LeftExt.push k (d ≫ J.u) f) (J.twistedPush k d)) :
    LeftExt k d :=
  LeftExt.mk (J.lift x.pt.ext (LeftExt.homCell x.cell)) (J.lift₂ _ (lift₂_condition J k d x))

/-- `leftExtOfIns` is a right inverse of the comparison `LE(d, k) ⥤ Ins(f_*, g_*)` on objects. -/
lemma leftExtToIns_obj_leftExtOfIns
    (x : Ins (LeftExt.push k (d ≫ J.u) f) (J.twistedPush k d)) :
    (J.leftExtToIns k d).obj (J.leftExtOfIns k d x) = x := by
  have hu : J.lift x.pt.ext (LeftExt.homCell x.cell) ≫ J.u = x.pt.ext :=
      J.lift_u x.pt.ext (LeftExt.homCell x.cell)
  have hpt : (LeftExt.push k d J.u).obj (J.leftExtOfIns k d x) = x.pt := by
    refine LeftExt.eq_of_ext_eq hu ?_
    simp only [leftExtOfIns, LeftExt.push_obj_unit, Category.assoc]
    have ht := J.lift₂_u (x.pt.unit ≫ eqToHom (comp_lift_comp_u J k d x))
      (lift₂_condition J k d x)
    exact (ht =≫ eqToHom _ ≫ eqToHom _).trans
      ((Category.assoc _ _ _).symm.trans (comp_eqToHom_loop x.pt.unit _ _ _))
  have hstr : strCell J (J.lift x.pt.ext (LeftExt.homCell x.cell)) =
      eqToHom (by rw [hu]; rfl) ≫ (LeftExt.homCell x.cell) ≫ eqToHom (by rw [hu]; rfl) := by
    exact (strCell_eq_transCell J hu).trans
      (_ ≫= transCell_lift J x.pt.ext (LeftExt.homCell x.cell) =≫ _)
  refine Ins.obj_ext hpt (LeftExt.hom_ext ?_)
  simp only [LeftExt.comp_val, LeftExt.homCell_eqToHom]
  exact hstr

/-- `leftExtOfIns` is a left inverse of the comparison `LE(d, k) ⥤ Ins(f_*, g_*)` on objects. -/
lemma leftExtOfIns_leftExtToIns_obj (L : LeftExt k d) :
    J.leftExtOfIns k d ((J.leftExtToIns k d).obj L) = L := by
  have hext : J.lift (L.ext ≫ J.u) (strCell J L.ext) = L.ext :=
    (J.lift_uniq L.ext _ _ rfl (by simp [strCell_def])).symm
  refine LeftExt.eq_of_ext_eq hext ?_
  refine J.lift₂_uniq _ _ ?_
  dsimp only [leftExtOfIns]
  rw [Bicategory.comp_whiskerRight]
  let x := (J.leftExtToIns k d).obj L
  have ht := J.lift₂_u (x.pt.unit ≫ eqToHom (comp_lift_comp_u J k d x))
    (lift₂_condition J k d x)
  refine (congrArg₂ (· ≫ ·) ht (Bicategory.eqToHom_whiskerRight _ J.u)).trans ?_
  exact comp_eqToHom_loop (L.unit ▷ J.u) _ _ _

/-- Lemma 4.6 (2) of [forsman2026syntactic] on objects: the comparison `LE(d, k) ⥤ Ins(f_*, g_*)` is
bijective on objects, with inverse `leftExtOfIns`. -/
lemma leftExtToIns_obj_bijective : Function.Bijective (J.leftExtToIns k d).obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨J.leftExtOfIns k d, J.leftExtOfIns_leftExtToIns_obj k d, J.leftExtToIns_obj_leftExtOfIns k d⟩

/-- The comparison `LE(d, k) ⥤ Ins(f_*, g_*)` is essentially surjective. -/
instance : (J.leftExtToIns k d).EssSurj where
  mem_essImage x := ⟨J.leftExtOfIns k d x, ⟨eqToIso (J.leftExtToIns_obj_leftExtOfIns k d x)⟩⟩

/-- The comparison `LE(d, k) ⥤ Ins(f_*, g_*)` followed by the forgetful functor is `u_*`, as in the
triangle of Lemma 4.6 (2) of [forsman2026syntactic]. -/
lemma leftExtToIns_comp_forget :
    J.leftExtToIns k d ⋙ Ins.forget (LeftExt.push k (d ≫ J.u) f) (J.twistedPush k d) =
      LeftExt.push k d J.u :=
  rfl

/-- The comparison `LE(d, k) ⥤ Ins(f_*, g_*)` is faithful. -/
instance : (J.leftExtToIns k d).Faithful where
  map_injective {_ _} _ _ H := (LeftExt.push k d J.u).map_injective (congr(Ins.Hom.base $(H)))

/-- The comparison `LE(d, k) ⥤ Ins(f_*, g_*)` is full. -/
instance : (J.leftExtToIns k d).Full where
  map_surjective {L T} m := by
    let m' : L.ext ≫ J.u ⟶ T.ext ≫ J.u := (LeftExt.homCell m.base)
    have cond : strCell J L.ext ≫ (m' ▷ g) = (m' ▷ f) ≫ strCell J T.ext :=
      congr(LeftExt.homCell $(m.w))
    have hb : ((L.unit ▷ J.u) ≫ eqToHom (Category.assoc k L.ext J.u)) ≫ (k ◁ m')
        = (T.unit ▷ J.u) ≫ eqToHom (Category.assoc k T.ext J.u) := (LeftExt.w m.base)
    refine ⟨LeftExt.homMk (J.lift₂ m' cond) ?_, Ins.hom_ext (LeftExt.hom_ext (J.lift₂_u _ _))⟩
    refine J.lift₂_uniq _ _ ?_
    rw [Bicategory.comp_whiskerRight, Bicategory.Strict.whisker_assoc']
    have hm := J.lift₂_u m' cond
    refine (congrArg (fun h => (L.unit ▷ J.u) ≫ eqToHom _ ≫ (k ◁ h) ≫ eqToHom _) hm).trans ?_
    rw [← Category.assoc, ← Category.assoc, hb]
    exact (Category.assoc _ _ _).trans
      (((T.unit ▷ J.u) ≫= eqToHom_trans _ _).trans (Category.comp_id _))

/-- Lemma 4.6 (2) of [forsman2026syntactic]: the comparison `LE(d, k) ⥤ Ins(f_*, g_*)` is an
equivalence (it is moreover bijective on objects, `leftExtToIns_obj_bijective`). -/
instance : (J.leftExtToIns k d).IsEquivalence where

end Inserter

/-! ## Lemma 4.6 (3): extensions into an equifier -/

namespace Equifier

variable {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ) {I X : Obj}
  (k : I ⟶ X) (d : I ⟶ E.pt)

/-- The extension `k ≫ y.obj.ext` is `(k ≫ E.lift y.obj.ext _) ≫ E.e`. -/
lemma comp_lift_comp_e (y : Equif (E.pushNat₁ k d) (E.pushNat₂ k d)) :
    k ≫ y.obj.ext = (k ≫ E.lift y.obj.ext (congrArg LeftExt.homCell y.property)) ≫ E.e := by
  exact ((k ≫= E.lift_e y.obj.ext (congr(LeftExt.homCell $(y.property)))).symm).trans
    (Category.assoc k _ E.e).symm

/-- The inverse of `Equifier.leftExtToEquif` on objects: an extension `(l', η')` of `e d` with
`η l' = θ l'` lifts to `(lift l', η)` with `e η = η'`. -/
noncomputable def leftExtOfEquif (y : Equif (E.pushNat₁ k d) (E.pushNat₂ k d)) : LeftExt k d :=
  LeftExt.mk (E.lift y.obj.ext (congrArg LeftExt.homCell y.property))
    (Classical.choose (E.full (y.obj.unit ≫ eqToHom (comp_lift_comp_e E k d y))))

/-- `leftExtOfEquif` is a right inverse of the comparison `LE(d, k) ⥤ Eq(η_*, θ_*)` on objects. -/
lemma leftExtToEquif_obj_leftExtOfEquif (y : Equif (E.pushNat₁ k d) (E.pushNat₂ k d)) :
    (E.leftExtToEquif k d).obj (E.leftExtOfEquif k d y) = y := by
  have hspec := Classical.choose_spec (E.full (y.obj.unit ≫ eqToHom (comp_lift_comp_e E k d y)))
  have hobj : (LeftExt.push k d E.e).obj (E.leftExtOfEquif k d y) = y.obj := by
    refine LeftExt.eq_of_ext_eq (E.lift_e _ _) ?_
    simp only [LeftExt.push_obj_unit, leftExtOfEquif, LeftExt.mk_unit]
    rw [hspec]
    exact comp_eqToHom_loop y.obj.unit _ _ _
  exact ObjectProperty.FullSubcategory.ext hobj

/-- Lemma 4.6 (3) of [forsman2026syntactic] on objects: the comparison `LE(d, k) ⥤ Eq(η_*, θ_*)` is
bijective on objects. -/
lemma leftExtToEquif_obj_bijective : Function.Bijective (E.leftExtToEquif k d).obj :=
  ⟨fun _ _ h => push_injective E k d (congr(ObjectProperty.FullSubcategory.obj $(h))),
    fun y => ⟨E.leftExtOfEquif k d y, E.leftExtToEquif_obj_leftExtOfEquif k d y⟩⟩

/-- The comparison `LE(d, k) ⥤ Eq(η_*, θ_*)` is faithful. -/
instance : (E.leftExtToEquif k d).Faithful where
  map_injective {_ _} _ _ H :=
    (LeftExt.push k d E.e).map_injective ((Equif.forget _ _).congr_map H)

/-- The comparison `LE(d, k) ⥤ Eq(η_*, θ_*)` is full. -/
instance : (E.leftExtToEquif k d).Full where
  map_surjective {_ _} m := by
    obtain ⟨α, hα⟩ := (LeftExt.push k d E.e).map_surjective m.hom
    exact ⟨α, InducedCategory.hom_ext hα⟩

end Equifier

end UlmerBialgebras
