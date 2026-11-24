module

public import UlmerBialgebras.Proofs.Sec5.AlgTheoryCart
public import UlmerBialgebras.Proofs.Sec6.GrpModels

/-!
# The translated theory of groups is the `Σ_Cart`-theory of groups

For a cartesian monoidal category `B`, the category `B^{T'}` of models of the translation `T'` of
the equational theory of groups `grpEqTheory S` is isomorphic, over `B^S`, to the category of
models of the `Σ_Cart`-theory of groups `grpTheory S` of `UlmerBialgebras/Paper/Sec6DefsGrp.lean`.

* The 1-signatures `(grpLanguage S).toCartSig` and `grpSig S` agree symbol by symbol, so their
  objects of operations are strictly isomorphic (`toGrpSig`, `ofGrpSig`).
* The defining condition of `B^{T'}` is the group axioms in each sort (`model_iff_grpAxioms`),
  which is the defining condition of the models of `grpTheory S` (`GrpModels`).

## Main results

* `UlmerBialgebras.Paper.MSLanguage.GrpIso.cartThy_iso_grpModel`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11
-/

@[expose] public section

universe v w u₁

namespace UlmerBialgebras.Paper.MSLanguage.GrpIso

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Cart
  Cart.SigCalc CartIso Cart.GrpModels

attribute [local instance] catOfSizeHom
attribute [local implicit_reducible] toCartSig grpLanguage

variable {B : Type (max u₁ v w)} [Category.{max u₁ v} B] [CartesianMonoidalCategory B] {S : Type u₁}

/-- The objects of operations of the translated language of groups. -/
abbrev CartSigObj (B : Type (max u₁ v w)) [Category.{max u₁ v} B] [CartesianMonoidalCategory B]
    (S : Type u₁) :
    Type (max u₁ v w) :=
  SigObj.{u₁, v, w} B (grpLanguage S).toCartSig

/-! ## The two objects of operations -/

/-- The cells of an object of the translated signature, as cells of `grpSig S`. -/
def toGrpCell (x : S → B)
    (c : ∀ f : S × GrpFn, P.{u₁, v, w} x ((grpLanguage S).argSorts f) ⟶ x f.1) :
    ∀ f, ((cartModel B).domCell (grpSig S)).toFunctor.obj x f ⟶
        ((cartModel B).codCell (grpSig S)).toFunctor.obj x f
  | (s, .mul) => c (s, .mul)
  | (s, .one) => c (s, .one)
  | (s, .inv) => c (s, .inv)

/-- The cells of an object of `grpSig S`, as cells of the translated signature. -/
def ofGrpCell (x : S → B)
    (c : ∀ f, ((cartModel B).domCell (grpSig S)).toFunctor.obj x f ⟶
      ((cartModel B).codCell (grpSig S)).toFunctor.obj x f) :
    ∀ f : S × GrpFn, P.{u₁, v, w} x ((grpLanguage S).argSorts f) ⟶ x f.1
  | (s, .mul) => c (s, .mul)
  | (s, .one) => c (s, .one)
  | (s, .inv) => c (s, .inv)

/-- An object of the translated signature as an object of `grpSig S`. -/
def toGrpSig (z : CartSigObj B S) : SigModel B S :=
  ⟨base z, toGrpCell (base z) (cell z)⟩

/-- An object of `grpSig S` as an object of the translated signature. -/
def ofGrpSig (z : SigModel B S) : CartSigObj B S :=
  ⟨Ins.pt z, ofGrpCell (Ins.pt z) (Ins.cell z)⟩

/-! ## The defining condition -/

variable (z : CartSigObj B S)

/-- The equation `x * 1 = x` holds in `z` iff the right unit law holds. -/
lemma realize_mulOne (s : S) :
    (grpEquation S (s, .mulOne)).Realize (base z) ↔
      lift (𝟙 (carrier (toGrpSig z) s)) (toUnit _ ≫ one (toGrpSig z) s) ≫ mul (toGrpSig z) s =
        𝟙 _ := by
  rw [Equation.Realize, ← cancel_epi (cmp (base z) _).hom]
  dsimp only [grpEquation]
  simp only [cmp_hom_realize_func, cmp_hom_realize_var, prodLift, prodπ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rfl

/-- The equation `1 * x = x` holds in `z` iff the left unit law holds. -/
lemma realize_oneMul (s : S) :
    (grpEquation S (s, .oneMul)).Realize (base z) ↔
      lift (toUnit _ ≫ one (toGrpSig z) s) (𝟙 (carrier (toGrpSig z) s)) ≫ mul (toGrpSig z) s =
        𝟙 _ := by
  rw [Equation.Realize, ← cancel_epi (cmp (base z) _).hom]
  dsimp only [grpEquation]
  simp only [cmp_hom_realize_func, cmp_hom_realize_var, prodLift, prodπ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rfl

/-- The equation `x⁻¹ * x = 1` holds in `z` iff the left inverse law holds. -/
lemma realize_invMul (s : S) :
    (grpEquation S (s, .invMul)).Realize (base z) ↔
      lift (inv (toGrpSig z) s) (𝟙 (carrier (toGrpSig z) s)) ≫ mul (toGrpSig z) s =
        toUnit _ ≫ one (toGrpSig z) s := by
  rw [Equation.Realize, ← cancel_epi (cmp (base z) _).hom]
  dsimp only [grpEquation]
  simp only [cmp_hom_realize_func, cmp_hom_realize_var, prodLift, prodπ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Category.id_comp]
  rfl

/-- The equation `x * x⁻¹ = 1` holds in `z` iff the right inverse law holds. -/
lemma realize_mulInv (s : S) :
    (grpEquation S (s, .mulInv)).Realize (base z) ↔
      lift (𝟙 (carrier (toGrpSig z) s)) (inv (toGrpSig z) s) ≫ mul (toGrpSig z) s =
        toUnit _ ≫ one (toGrpSig z) s := by
  rw [Equation.Realize, ← cancel_epi (cmp (base z) _).hom]
  dsimp only [grpEquation]
  simp only [cmp_hom_realize_func, cmp_hom_realize_var, prodLift, prodπ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Category.id_comp]
  rfl

section Assoc

variable {D : Type*} [Category D] [CartesianMonoidalCategory D] {X : D} (m : X ⊗ X ⟶ X)

/-- The left side of associativity on `X ⊗ (X ⊗ X)`, transported along the associator. -/
lemma assoc_lhs :
    (α_ X X X).hom ≫ lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ m) (snd _ _ ≫ snd _ _) ≫ m =
      m ▷ X ≫ m := by
  have h : (α_ X X X).hom ≫ lift (fst _ _) (snd _ _ ≫ fst _ _) = fst _ _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, ← Category.assoc, h, whiskerRight_fst]
  · simp

/-- The right side of associativity on `X ⊗ (X ⊗ X)`. -/
lemma assoc_rhs :
    lift (fst _ _) (lift (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) ≫ m) ≫ m = X ◁ m ≫ m := by
  have h : lift (snd X (X ⊗ X) ≫ fst _ _) (snd _ _ ≫ snd _ _) = snd _ _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

end Assoc

/-- The associativity law of `GrpAxioms` at a sort. -/
def AssocLaw (z' : SigModel B S) (s : S) : Prop :=
  MonoidalCategory.whiskerRight (mul z' s) (carrier z' s) ≫ mul z' s =
    (α_ (carrier z' s) (carrier z' s) (carrier z' s)).hom ≫
      MonoidalCategory.whiskerLeft (carrier z' s) (mul z' s) ≫ mul z' s

/-- The equation `(x * y) * z = x * (y * z)` holds in `z` iff associativity holds. -/
lemma realize_assoc (s : S) :
    (grpEquation S (s, .assoc)).Realize (base z) ↔
      AssocLaw (toGrpSig z) s := by
  rw [Equation.Realize, ← cancel_epi (cmp (base z) _).hom]
  dsimp only [grpEquation]
  simp only [cmp_hom_realize_func, cmp_hom_realize_var, prodLift, prodπ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  let X := base z s
  let m : X ⊗ X ⟶ X := cell z (s, .mul)
  change (lift (lift (fst X (X ⊗ X)) (snd X (X ⊗ X) ≫ fst X X) ≫ m)
      (snd X (X ⊗ X) ≫ snd X X ≫ 𝟙 X) ≫ m =
    lift (fst X (X ⊗ X)) (lift (snd X (X ⊗ X) ≫ fst X X)
      (snd X (X ⊗ X) ≫ snd X X ≫ 𝟙 X) ≫ m) ≫ m) ↔ _
  simp only [Category.comp_id]
  refine (cancel_epi (α_ (base z s) (base z s) (base z s)).hom).symm.trans
    (Iff.of_eq (congrArg₂ Eq (assoc_lhs m) ?_))
  exact ((α_ (base z s) (base z s) (base z s)).hom ≫= (assoc_rhs m))

/-- **The defining condition of `B^{T'}` is the group axioms**: the induced structure of `z` is a
model of the equational theory of groups iff `z` satisfies the group axioms in each sort. -/
lemma model_iff_grpAxioms : base z ⊨ grpEqTheory S ↔ ∀ s, GrpAxioms (toGrpSig z) s := by
  refine ⟨fun h s => ?_, fun h => ⟨?_⟩⟩
  · have r := fun e => h.realize_of_mem (grpEquation S (s, e)) ⟨(s, e), rfl⟩
    exact ⟨(realize_assoc z s).1 (r _), (realize_mulOne z s).1 (r _),
      (realize_oneMul z s).1 (r _), (realize_invMul z s).1 (r _), (realize_mulInv z s).1 (r _)⟩
  · rintro φ ⟨⟨s, e⟩, rfl⟩
    cases e
    exacts [(realize_assoc z s).2 (h s).assoc, (realize_mulOne z s).2 (h s).mulOne,
      (realize_oneMul z s).2 (h s).oneMul, (realize_invMul z s).2 (h s).invMul,
      (realize_mulInv z s).2 (h s).mulInv]

/-! ## The isomorphism -/

variable (B S)

/-- From models of the translated theory of groups to models of `grpTheory S`. -/
noncomputable def toGrpModel : (grpEqTheory S).cartThy.{v, w, u₁} B ⥤ GrpModel B S where
  obj t := ⟨toGrpSig t.obj, (lhsCell_eq_rhsCell_iff _).2
    ((model_iff_grpAxioms t.obj).1 ((equifProp_iff.{u₁, v, w} t.obj).1 t.property))⟩
  map g := ObjectProperty.homMk
    { base := g.hom.base
      w := funext fun f => by
        obtain ⟨s, _ | _ | _⟩ := f
        all_goals exact funext_iff.1 g.hom.w _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- From models of `grpTheory S` to models of the translated theory of groups. -/
noncomputable def ofGrpModel : GrpModel B S ⥤ (grpEqTheory S).cartThy.{v, w, u₁} B where
  obj t := ⟨ofGrpSig t.obj, (equifProp_iff.{u₁, v, w} _).2
    ((model_iff_grpAxioms _).2 (fun s =>
      have h := grpAxioms_of_grpModel t s
      ⟨h.assoc, h.mulOne, h.oneMul, h.invMul, h.mulInv⟩))⟩
  map g := ObjectProperty.homMk
    { base := g.hom.base
      w := funext fun f => by
        obtain ⟨s, _ | _ | _⟩ := f
        all_goals exact funext_iff.1 g.hom.w _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The translated theory of groups has the models of `grpTheory S`**, over `B^S`. -/
theorem cartThy_iso_grpModel :
    ∃ (F : (grpEqTheory S).cartThy.{v, w, u₁} B ⥤ GrpModel B S)
      (G : GrpModel B S ⥤ (grpEqTheory S).cartThy.{v, w, u₁} B),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ ((cartModel B).e (grpSig S) (grpTheory S) ≫ (cartModel B).u (grpSig S)).toFunctor =
          (grpEqTheory S).cartThyForget.{v, w, u₁} B := by
  refine ⟨toGrpModel B S, ofGrpModel B S, ?_, ?_, ?_⟩
  · refine CategoryTheory.Functor.ext (fun t => ?_) (fun t t' g => ?_)
    · obtain ⟨⟨x, c⟩, hp⟩ := t
      refine ObjectProperty.FullSubcategory.ext (Ins.obj_ext rfl ?_)
      refine Eq.trans ?_ ((Category.id_comp _).trans (Category.comp_id _)).symm
      funext ⟨s, e⟩
      cases e
      all_goals rfl
    · obtain ⟨⟨x, c⟩, hp⟩ := t
      obtain ⟨⟨x', c'⟩, hp'⟩ := t'
      refine ObjectProperty.hom_ext _ (Ins.hom_ext ?_)
      refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (fullSubcategory_eqToHom_hom_base _).symm
        ((_ ≫= (fullSubcategory_eqToHom_hom_base _)).symm))
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  · refine CategoryTheory.Functor.ext (fun t => ?_) (fun t t' g => ?_)
    · obtain ⟨⟨x, c⟩, hp⟩ := t
      refine ObjectProperty.FullSubcategory.ext (Ins.obj_ext rfl ?_)
      refine Eq.trans ?_ ((Category.id_comp _).trans (Category.comp_id _)).symm
      funext ⟨s, e⟩
      cases e
      all_goals rfl
    · obtain ⟨⟨x, c⟩, hp⟩ := t
      obtain ⟨⟨x', c'⟩, hp'⟩ := t'
      refine ObjectProperty.hom_ext _ (Ins.hom_ext ?_)
      refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (fullSubcategory_eqToHom_hom_base _).symm
        ((_ ≫= (fullSubcategory_eqToHom_hom_base _)).symm))
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  · exact CategoryTheory.Functor.ext (fun _ => rfl)
      (fun _ _ _ => ((Category.id_comp _).trans (Category.comp_id _)).symm)

end UlmerBialgebras.Paper.MSLanguage.GrpIso
