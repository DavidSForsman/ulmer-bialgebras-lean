module

public import UlmerBialgebras.Paper.Sec6DefsGrp
public import UlmerBialgebras.Models.CatCells

/-!
# Evaluating the term graph of a `Σ_Cart`-signature

For a cartesian monoidal category `B`, viewed as the `Σ_Cart`-model `M = Cart.cartModel B`, and a
1-signature `σ` relative to `Σ_Cart` with symbols of size `s`, the arrows and derived paths of the
term graph of `σ` evaluate at an object `z` of `M^σ` to the corresponding cartesian morphisms:
the diagonal to `lift 𝟙 𝟙`, pairing to `lift`, the projections to `fst`, `snd`, the derived
associator to the associator of `B`. Here `B` has objects in `max s v w` and morphisms in
`max s v`, and the products of size `s` of `CAT` are `catOfSizeHom`.

## Main results

* `UlmerBialgebras.Paper.Cart.SigCalc.interpPath_liftPath`: pairing evaluates to `lift`.
* `UlmerBialgebras.Paper.Cart.SigCalc.interpPath_assocPath`: the derived associator evaluates to
  the associator.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 (`Σ_Cart`) and Definition 3.14
-/

@[expose] public section


universe s v w

namespace UlmerBialgebras.Paper.Cart.SigCalc

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

attribute [local instance] catOfSizeHom

variable {B : Type (max s v w)} [Category.{max s v} B] [CartesianMonoidalCategory B]
  {sg : OneSig.{0, 0, 0, s, s} sigCart}

section CatOfSize

variable {ι : Type s} {c : ι → Cat.{max s v, max s v w}} {A : Cat.{max s v, max s v w}}

/-- The components of a 2-cell induced into a product of size `s` in `CAT`. -/
@[simp] lemma catOfSize_lift₂_app
    {f g : A ⟶ (HasChosenProductsOfSize.prod (self := catOfSizeHom.{v, s, w}) c).pt}
    (γ : ∀ i, (f ≫ (HasChosenProductsOfSize.prod (self := catOfSizeHom.{v, s, w}) c).π i) ⟶
      (g ≫ (HasChosenProductsOfSize.prod (self := catOfSizeHom.{v, s, w}) c).π i)) (z : A) (i : ι) :
    ((HasChosenProductsOfSize.prod (self := catOfSizeHom.{v, s, w}) c).lift₂ γ).toNatTrans.app z i =
      (γ i).toNatTrans.app z :=
  rfl

end CatOfSize

variable (B sg) in
/-- The objects of `M^σ`. -/
abbrev SigObj : Type (max s v w) := ((cartModel B).sigObj sg : Type (max s v w))

/-- The structure map of `z ∈ M^σ` at a function symbol `f` is the cell `Ins.cell z f`. -/
@[simp] lemma sigIns_φ_app (z : SigObj B sg) (f : sg.Fn) :
    ((cartModel B).sigIns sg).φ.toNatTrans.app z f = Ins.cell z f := rfl

/-- The object interpreting a closed term at an object of `M^σ`. -/
abbrev interpTerm (z : SigObj B sg) (t : sg.CTrm ()) : B :=
  ((cartModel B).sigTm sg t).toFunctor.obj z

/-- The component at `z` of a 2-cell between term 1-cells. -/
abbrev interpArr {t t' : sg.CTrm ()}
    (α : (cartModel B).sigTm sg t ⟶ (cartModel B).sigTm sg t') (z : SigObj B sg) :
    interpTerm z t ⟶ interpTerm z t' := α.toNatTrans.app z

/-! ## Arrows of the term graph -/

/-- The 2-cell of an arrow transported along equalities of its source and target terms is the
2-cell of the arrow conjugated by `eqToHom`s. -/
lemma arrCell_transport {t₁ t₂ t₁' t₂' : sg.CTrm ()} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (g : sg.Arr t₁ t₂) :
    (cartModel B).arrCell sg (g.transport h₁ h₂) =
      eqToHom (by rw [h₁]) ≫ (cartModel B).arrCell sg g ≫ eqToHom (by rw [h₂]) := by
  subst h₁; subst h₂; simp [OneSig.Arr.transport]

omit [Category.{max s v} B] [CartesianMonoidalCategory B] in
/-- A morphism conjugated by `eqToHom`s is any morphism heterogeneously equal to it. -/
lemma eqToHom_comp_comp_eqToHom_of_heq {C : Type*} [Category C] {X Y X' Y' : C} (f : X ⟶ Y)
    (g : X' ⟶ Y') (h : X' = X) (h' : Y = Y') (hfg : HEq f g) :
    eqToHom h ≫ f ≫ eqToHom h' = g := by
  subst h; subst h'; simpa using eq_of_heq hfg

/-- The diagonal `δ_t` evaluates at `z` to `lift 𝟙 𝟙 : M(t) ⟶ M(t) ⊗ M(t)`. -/
lemma interpArr_diagArr (z : SigObj B sg) (t : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (diagArr t)) z = lift (𝟙 (interpTerm z t))
        (𝟙 (interpTerm z t)) := by
  rw [diagArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  exact eqToHom_comp_comp_eqToHom_of_heq (C := B) _ _ _ _ HEq.rfl

/-- The projection `p₁ : a □ b → a` evaluates at `z` to `fst`. -/
lemma interpArr_fstArr (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (fstArr a b)) z = fst (interpTerm z a)
        (interpTerm z b) := by
  rw [fstArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  exact eqToHom_comp_comp_eqToHom_of_heq (C := B) _ _ _ _ HEq.rfl

/-- The projection `p₂ : a □ b → b` evaluates at `z` to `snd`. -/
lemma interpArr_sndArr (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (sndArr a b)) z = snd (interpTerm z a)
        (interpTerm z b) := by
  rw [sndArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  exact eqToHom_comp_comp_eqToHom_of_heq (C := B) _ _ _ _ HEq.rfl

/-- The terminal map `! : t → I` evaluates at `z` to `toUnit`. -/
lemma interpArr_toUnitArr (z : SigObj B sg) (t : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (toUnitArr t)) z = toUnit (interpTerm z t) := by
  rw [toUnitArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  exact eqToHom_comp_comp_eqToHom_of_heq (C := B) _ _ _ _ HEq.rfl

/-- The arrow `g □ b` evaluates at `z` to the evaluation of `g` whiskered on the right by `M(b)`. -/
lemma interpArr_whiskerRightArr (z : SigObj B sg) {a a' : sg.CTrm ()}
    (b : sg.CTrm ())
    (g : sg.Arr a a') :
    interpArr ((cartModel B).arrCell sg (whiskerRightArr b g)) z =
      MonoidalCategory.whiskerRight (interpArr ((cartModel B).arrCell sg g) z) (interpTerm z b)
          := by
  have h := (cartModel B).arrCell_app sg CartFun.tens 0 ![a, b] ![a', b]
    (fun j hj => by fin_cases j <;> simp_all) g
  refine (congr(($h).toNatTrans.app z)).trans ?_
  rw [PreModel.appCell]
  simp only [interpArr, Cat.whiskerRight_app]
  change (_ ⊗ₘ _) = _
  refine Eq.trans ?_ (MonoidalCategory.tensorHom_id _ _)
  congr 1
  · refine (Cat.Hom₂.comp_app _ _ _).trans ?_
    simp only [Cat.Hom₂.comp_app, dite_true, cast_eq]
    exact eqToHom_comp_comp_eqToHom_of_heq _ _ (by rfl) (by rfl) HEq.rfl
  · refine (Cat.Hom₂.comp_app _ _ _).trans ?_
    rw [dite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
    simp only [Cat.eqToHom_app, eqToHom_trans]
    exact eqToHom_refl _ _

/-- The arrow `a □ g` evaluates at `z` to the evaluation of `g` whiskered on the left by `M(a)`. -/
lemma interpArr_whiskerLeftArr (z : SigObj B sg) (a : sg.CTrm ())
    {b b' : sg.CTrm ()}
    (g : sg.Arr b b') :
    interpArr ((cartModel B).arrCell sg (whiskerLeftArr a g)) z =
      MonoidalCategory.whiskerLeft (interpTerm z a) (interpArr ((cartModel B).arrCell sg g) z) := by
  have h := (cartModel B).arrCell_app sg CartFun.tens 1 ![a, b] ![a, b']
    (fun j hj => by fin_cases j <;> simp_all) g
  refine (congr(($h).toNatTrans.app z)).trans ?_
  rw [PreModel.appCell]
  simp only [interpArr, Cat.whiskerRight_app]
  change (_ ⊗ₘ _) = _
  refine Eq.trans ?_ (MonoidalCategory.id_tensorHom _ _)
  congr 1
  · refine (Cat.Hom₂.comp_app _ _ _).trans ?_
    rw [dite_eq_right (show (0 : Fin 2) ≠ 1 by decide)]
    simp only [Cat.eqToHom_app, eqToHom_trans]
    exact eqToHom_refl _ _
  · refine (Cat.Hom₂.comp_app _ _ _).trans ?_
    simp only [Cat.Hom₂.comp_app, dite_true, cast_eq]
    exact eqToHom_comp_comp_eqToHom_of_heq _ _ (by rfl) (by rfl) HEq.rfl

/-! ## Paths of the term graph -/

/-- The evaluation of a path at `z`. -/
abbrev interpPath {t t' : sg.CTrm ()} (p : sg.Path t t') (z : SigObj B sg) :
    interpTerm z t ⟶ interpTerm z t' := interpArr ((cartModel B).pathCell sg p) z

/-- The empty path evaluates to the identity. -/
lemma interpPath_nil (z : SigObj B sg) (t : sg.CTrm ()) :
    interpPath (.nil t) z = 𝟙 (interpTerm z t) := by
  rw [interpPath, interpArr, Model.pathCell_nil]; exact NatTrans.id_app _ _

/-- A path `g` followed by `p` evaluates to the composite of their evaluations. -/
lemma interpPath_cons (z : SigObj B sg) {t t' t'' : sg.CTrm ()} (g : sg.Arr t t')
    (p : sg.Path t' t'') :
    interpPath (.cons g p) z =
      interpArr ((cartModel B).arrCell sg g) z ≫ interpPath p z := by
  rw [interpPath, interpArr, Model.pathCell_cons]; exact NatTrans.comp_app _ _ _

/-- Path evaluation is functorial: `p` then `q` evaluates to the composite of the evaluations. -/
lemma interpPath_comp (z : SigObj B sg) {t t' t'' : sg.CTrm ()} (p : sg.Path t t')
    (q : sg.Path t' t'') : interpPath (OneSig.Path.comp p q) z = interpPath p z ≫ interpPath
        q z := by
  induction p with
  | nil t =>
    simp only [OneSig.Path.comp]
    rw [interpPath_nil, Category.id_comp]
  | cons g p ih =>
    simp only [OneSig.Path.comp]
    rw [interpPath_cons, interpPath_cons, ih, Category.assoc]

/-- A one-arrow path evaluates as the arrow. -/
lemma interpPath_arrPath (z : SigObj B sg) {t t' : sg.CTrm ()} (g : sg.Arr t t') :
    interpPath (arrPath g) z = interpArr ((cartModel B).arrCell sg g) z := by
  rw [arrPath, interpPath_cons, interpPath_nil, Category.comp_id]

/-- The path `p □ b` evaluates to the evaluation of `p` whiskered on the right by `M(b)`. -/
lemma interpPath_whiskerRightPath (z : SigObj B sg) (b : sg.CTrm ())
    {a t : sg.CTrm ()}
    (p : sg.Path a t) : interpPath (whiskerRightPath b p) z = MonoidalCategory.whiskerRight
        (interpPath p z) (interpTerm z b) := by
  induction p with
  | nil t =>
    rw [whiskerRightPath, interpPath_nil, interpPath_nil]
    exact (MonoidalCategory.id_whiskerRight _ _).symm
  | cons g p ih =>
    rw [whiskerRightPath, interpPath_cons, interpPath_cons, ih, interpArr_whiskerRightArr,
        MonoidalCategory.comp_whiskerRight]; rfl

/-- The path `a □ p` evaluates to the evaluation of `p` whiskered on the left by `M(a)`. -/
lemma interpPath_whiskerLeftPath (z : SigObj B sg) (a : sg.CTrm ())
    {b t : sg.CTrm ()}
    (p : sg.Path b t) :
    interpPath (whiskerLeftPath a p) z = MonoidalCategory.whiskerLeft (interpTerm z a) (interpPath
        p z) := by
  induction p with
  | nil t =>
    rw [whiskerLeftPath, interpPath_nil, interpPath_nil]
    exact (MonoidalCategory.whiskerLeft_id _ _).symm
  | cons g p ih =>
    rw [whiskerLeftPath, interpPath_cons, interpPath_cons, ih, interpArr_whiskerLeftArr,
        MonoidalCategory.whiskerLeft_comp]; rfl

/-- The pairing `⟨p, q⟩ = δ ; (p □ q)` evaluates to `lift` of the evaluations of `p` and `q`. -/
lemma interpPath_liftPath (z : SigObj B sg) {t a b : sg.CTrm ()} (p : sg.Path t a)
    (q : sg.Path t b) : interpPath (liftPath p q) z = lift (interpPath p z)
        (interpPath q z) := by
  rw [liftPath, interpPath_comp, diagPath, interpPath_arrPath, interpArr_diagArr, tensorPath,
      interpPath_comp, interpPath_whiskerRightPath,
    interpPath_whiskerLeftPath]
  exact (lift_whiskerRight_assoc _ _ _ _).trans ((lift_whiskerLeft _ _ _).trans
    (by rw [Category.id_comp, Category.id_comp]))

/-- The path `p₁` evaluates to `fst`. -/
lemma interpPath_fstPath (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpPath (fstPath a b) z = fst (interpTerm z a) (interpTerm z b) := by
  rw [fstPath, interpPath_arrPath, interpArr_fstArr]

/-- The path `p₂` evaluates to `snd`. -/
lemma interpPath_sndPath (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpPath (sndPath a b) z = snd (interpTerm z a) (interpTerm z b) := by
  rw [sndPath, interpPath_arrPath, interpArr_sndArr]

/-- The path `!` evaluates to `toUnit`. -/
lemma interpPath_toUnitPath (z : SigObj B sg) (t : sg.CTrm ()) :
    interpPath (toUnitPath t) z = toUnit (interpTerm z t) := by
  rw [toUnitPath, interpPath_arrPath, interpArr_toUnitArr]

/-- The derived associator `⟨p₁p₁, ⟨p₁p₂, p₂⟩⟩` evaluates to the associator `α` of `B`. -/
lemma interpPath_assocPath (z : SigObj B sg) (a b c : sg.CTrm ()) :
    interpPath (assocPath a b c) z =
      (α_ (interpTerm z a) (interpTerm z b) (interpTerm z c)).hom := by
  rw [assocPath, interpPath_liftPath, interpPath_comp, interpPath_fstPath, interpPath_fstPath,
      interpPath_liftPath, interpPath_comp, interpPath_fstPath, interpPath_sndPath,
    interpPath_sndPath]
  change lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _)) =
    (α_ (interpTerm z a) (interpTerm z b) (interpTerm z c)).hom
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

end UlmerBialgebras.Paper.Cart.SigCalc
