module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import UlmerBialgebras.Paper.Sec6DefsGrp
public import UlmerBialgebras.Proofs.Sec5.CartSigCalc

/-!
# Models of the theory of groups in a cartesian category

For a cartesian monoidal category `B`, viewed as a `Σ_Cart`-model `M = Cart.cartModel B`, and a
set of sorts `S`, the category `M^T` of models of the multi-sorted theory of groups
`T = Cart.grpTheory S` is equivalent to the category `S → Grp B` of `S`-indexed families of
internal groups of `B`.

* An object of `M^σ` is a family `x : S → B` with operations `m_s : x_s ⊗ x_s → x_s`,
  `e_s : 𝟙 → x_s` and `i_s : x_s → x_s` (`carrier`, `mul`, `one`, `inv`).
* The arrows and derived paths of the term graph evaluate to the corresponding cartesian
  morphisms: the diagonal to `lift 𝟙 𝟙`, pairing to `lift`, the derived associator to the
  associator of `B`.
* So the defining condition of `M^T` is exactly the group axioms in each sort
  (`lhsCell_eq_rhsCell_iff`), in the form of Mathlib's `GrpObj`.

## Main results

* `UlmerBialgebras.Paper.Cart.GrpModels.lhsCell_eq_rhsCell_iff`: an object of `M^σ` satisfies the
  defining condition of `M^T` iff it satisfies the group axioms in each sort.
* `UlmerBialgebras.Paper.Cart.GrpModels.toFamily`: the comparison functor `M^T ⥤ (S → Grp B)`.
* `UlmerBialgebras.Paper.Cart.GrpModels.grpModelEquiv`: an equivalence `M^T ≌ (S → Grp B)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 (`Σ_Cart`), Definition 3.14 and Corollary 6.11
-/

@[expose] public section

universe v w u₁

namespace UlmerBialgebras.Paper.Cart.GrpModels

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

attribute [local instance] catOfSizeHom

variable {B : Type (max u₁ v w)} [Category.{max u₁ v} B] [CartesianMonoidalCategory B] {S : Type u₁}

/-- The objects of `M^σ`. -/
abbrev SigModel (B : Type (max u₁ v w)) [Category.{max u₁ v} B] [CartesianMonoidalCategory B]
    (S : Type u₁) :
    Type (max u₁ v w) :=
  ((cartModel B).sigObj (grpSig S) : Type (max u₁ v w))

/-- The object of a sort. -/
def carrier (z : SigModel B S) (s : S) : B := Ins.pt z s

/-- The multiplication of a sort. -/
def mul (z : SigModel B S) (s : S) : carrier z s ⊗ carrier z s ⟶ carrier z s := Ins.cell z (s, .mul)

/-- The unit of a sort. -/
def one (z : SigModel B S) (s : S) : 𝟙_ B ⟶ carrier z s := Ins.cell z (s, .one)

/-- The inverse of a sort. -/
def inv (z : SigModel B S) (s : S) : carrier z s ⟶ carrier z s := Ins.cell z (s, .inv)

/-- The structure map of `z ∈ M^σ` at a function symbol `f` is the cell `Ins.cell z f`. -/
@[simp] lemma sigIns_φ_app (z : SigModel B S) (f : (grpSig S).Fn) :
    ((cartModel B).sigIns (grpSig S)).φ.toNatTrans.app z f = Ins.cell z f := rfl

/-- The object interpreting a closed term at an object of `M^σ`. -/
abbrev interpTerm (z : SigModel B S) (t : (grpSig S).CTrm ()) : B :=
  ((cartModel B).sigTm (grpSig S) t).toFunctor.obj z

/-- The component at `z` of a 2-cell between term 1-cells. -/
abbrev interpArr {t t' : (grpSig S).CTrm ()}
    (α : (cartModel B).sigTm (grpSig S) t ⟶ (cartModel B).sigTm (grpSig S) t') (z : SigModel B S) :
    interpTerm z t ⟶ interpTerm z t' := α.toNatTrans.app z

/-! ## Arrows of the term graph -/

/-- The arrow of the multiplication symbol `m_s` evaluates at `z` to `mul z s`. -/
lemma interpArr_fn_mul (z : SigModel B S) (s : S) :
    interpArr ((cartModel B).arrCell (grpSig S) (OneSig.Arr.fn (sg := grpSig S) (s, .mul))) z =
      mul z s := by
  dsimp only [grpSig, interpArr]
  rw [Model.arrCell_fn]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerRight_toNatTrans]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the unit symbol `e_s` evaluates at `z` to `one z s`. -/
lemma interpArr_fn_one (z : SigModel B S) (s : S) :
    interpArr ((cartModel B).arrCell (grpSig S) (OneSig.Arr.fn (sg := grpSig S) (s, .one))) z =
      one z s := by
  dsimp only [grpSig, interpArr]
  rw [Model.arrCell_fn]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerRight_toNatTrans]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the inverse symbol `i_s` evaluates at `z` to `inv z s`. -/
lemma interpArr_fn_inv (z : SigModel B S) (s : S) :
    interpArr ((cartModel B).arrCell (grpSig S) (OneSig.Arr.fn (sg := grpSig S) (s, .inv))) z =
      inv z s := by
  dsimp only [grpSig, interpArr]
  rw [Model.arrCell_fn]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerRight_toNatTrans]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-! ## Paths of the term graph -/

/-- The evaluation of a path at `z`. -/
abbrev interpPath {t t' : (grpSig S).CTrm ()} (p : (grpSig S).Path t t') (z : SigModel B S) :
    interpTerm z t ⟶ interpTerm z t' := interpArr ((cartModel B).pathCell (grpSig S) p) z

/-- The empty path evaluates to the identity. -/
lemma interpPath_nil (z : SigModel B S) (t : (grpSig S).CTrm ()) :
    interpPath (.nil t) z = 𝟙 (interpTerm z t) := by
  apply SigCalc.interpPath_nil.{u₁, v, w}

/-- Path evaluation is functorial: `p` then `q` evaluates to the composite of the evaluations. -/
lemma interpPath_comp (z : SigModel B S) {t t' t'' : (grpSig S).CTrm ()} (p : (grpSig S).Path t t')
    (q : (grpSig S).Path t' t'') : interpPath (OneSig.Path.comp p q) z = interpPath p z ≫ interpPath
        q z := by
  apply SigCalc.interpPath_comp.{u₁, v, w}

/-- A one-arrow path evaluates as the arrow. -/
lemma interpPath_arrPath (z : SigModel B S) {t t' : (grpSig S).CTrm ()} (g : (grpSig S).Arr t t') :
    interpPath (arrPath g) z = interpArr ((cartModel B).arrCell (grpSig S) g) z := by
  apply SigCalc.interpPath_arrPath.{u₁, v, w}

/-- The path `p □ b` evaluates to the evaluation of `p` whiskered on the right by `M(b)`. -/
lemma interpPath_whiskerRightPath (z : SigModel B S) (b : (grpSig S).CTrm ())
    {a t : (grpSig S).CTrm ()}
    (p : (grpSig S).Path a t) : interpPath (whiskerRightPath b p) z = MonoidalCategory.whiskerRight
        (interpPath p z) (interpTerm z b) := by
  apply SigCalc.interpPath_whiskerRightPath.{u₁, v, w}

/-- The path `a □ p` evaluates to the evaluation of `p` whiskered on the left by `M(a)`. -/
lemma interpPath_whiskerLeftPath (z : SigModel B S) (a : (grpSig S).CTrm ())
    {b t : (grpSig S).CTrm ()}
    (p : (grpSig S).Path b t) :
    interpPath (whiskerLeftPath a p) z = MonoidalCategory.whiskerLeft (interpTerm z a) (interpPath
        p z) := by
  apply SigCalc.interpPath_whiskerLeftPath.{u₁, v, w}

/-- The pairing `⟨p, q⟩ = δ ; (p □ q)` evaluates to `lift` of the evaluations of `p` and `q`. -/
lemma interpPath_liftPath (z : SigModel B S) {t a b : (grpSig S).CTrm ()} (p : (grpSig S).Path t a)
    (q : (grpSig S).Path t b) : interpPath (liftPath p q) z = lift (interpPath p z)
        (interpPath q z) := by
  apply SigCalc.interpPath_liftPath.{u₁, v, w}

/-- The path `!` evaluates to `toUnit`. -/
lemma interpPath_toUnitPath (z : SigModel B S) (t : (grpSig S).CTrm ()) :
    interpPath (toUnitPath t) z = toUnit (interpTerm z t) := by
  apply SigCalc.interpPath_toUnitPath.{u₁, v, w}

/-- The derived associator `⟨p₁p₁, ⟨p₁p₂, p₂⟩⟩` evaluates to the associator `α` of `B`. -/
lemma interpPath_assocPath (z : SigModel B S) (a b c : (grpSig S).CTrm ()) :
    interpPath (assocPath a b c) z =
      (α_ (interpTerm z a) (interpTerm z b) (interpTerm z c)).hom := by
  apply SigCalc.interpPath_assocPath.{u₁, v, w}

/-- The path `m_s` evaluates to `mul z s`. -/
lemma interpPath_mulPath (z : SigModel B S) (s : S) : interpPath (mulPath s) z = mul z s := by
  exact (interpPath_arrPath z (OneSig.Arr.fn (sg := grpSig S) (s, .mul))).trans
      (interpArr_fn_mul z s)

/-- The path `e_s` evaluates to `one z s`. -/
lemma interpPath_onePath (z : SigModel B S) (s : S) : interpPath (onePath s) z = one z s := by
  exact (interpPath_arrPath z (OneSig.Arr.fn (sg := grpSig S) (s, .one))).trans
      (interpArr_fn_one z s)

/-- The path `i_s` evaluates to `inv z s`. -/
lemma interpPath_invPath (z : SigModel B S) (s : S) : interpPath (invPath s) z = inv z s := by
  exact (interpPath_arrPath z (OneSig.Arr.fn (sg := grpSig S) (s, .inv))).trans
      (interpArr_fn_inv z s)

/-- The path `! ; e_s` evaluates to `toUnit ≫ one z s`. -/
lemma interpPath_constOnePath (z : SigModel B S) (s : S) : interpPath (constOnePath s) z = toUnit
    (carrier z s) ≫ one z s := by
  rw [constOnePath, interpPath_comp, interpPath_toUnitPath, interpPath_onePath]; rfl

/-! ## The defining condition of `M^T` -/

/-- The group axioms at a sort, in the form of Mathlib's `GrpObj`. -/
structure GrpAxioms (z : SigModel B S) (s : S) : Prop where
  assoc : MonoidalCategory.whiskerRight (mul z s) (carrier z s) ≫ mul z s =
    (α_ (carrier z s) (carrier z s) (carrier z s)).hom ≫ MonoidalCategory.whiskerLeft (carrier z s)
        (mul z s) ≫ mul z s
  mulOne : lift (𝟙 (carrier z s)) (toUnit (carrier z s) ≫ one z s) ≫ mul z s = 𝟙 (carrier z s)
  oneMul : lift (toUnit (carrier z s) ≫ one z s) (𝟙 (carrier z s)) ≫ mul z s = 𝟙 (carrier z s)
  invMul : lift (inv z s) (𝟙 (carrier z s)) ≫ mul z s = toUnit (carrier z s) ≫ one z s
  mulInv : lift (𝟙 (carrier z s)) (inv z s) ≫ mul z s = toUnit (carrier z s) ≫ one z s

/-- The component at `z` and equation `r` of the left-hand cell of `M^T` evaluates the path
`lhs r` at `z`. -/
lemma lhsCell_app (z : SigModel B S) (r : S × GrpEqn) :
    ((cartModel B).lhsCell (grpSig S) (grpTheory S)).toNatTrans.app z r =
      interpPath ((grpTheory S).lhs r) z := by
  rw [Model.lhsCell]
  dsimp only [grpTheory, Model.Peq]
  simp only [Cart.SigCalc.catOfSize_lift₂_app.{u₁, v, w}, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The component at `z` and equation `r` of the right-hand cell of `M^T` evaluates the path
`rhs r` at `z`. -/
lemma rhsCell_app (z : SigModel B S) (r : S × GrpEqn) :
    ((cartModel B).rhsCell (grpSig S) (grpTheory S)).toNatTrans.app z r =
      interpPath ((grpTheory S).rhs r) z := by
  rw [Model.rhsCell]
  dsimp only [grpTheory, Model.Peq]
  simp only [Cart.SigCalc.catOfSize_lift₂_app.{u₁, v, w}, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The left side of associativity evaluates to `(m ▷ x) ≫ m`. -/
lemma interpPath_grpEqnLhs_assoc (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).lhs (s, .assoc)) z = MonoidalCategory.whiskerRight (mul z s) (carrier
        z s) ≫ mul z s := by
  refine (interpPath_comp z (whiskerRightPath (sortTerm s) (mulPath s)) (mulPath s)).trans ?_
  rw [interpPath_whiskerRightPath, interpPath_mulPath]; rfl

/-- The right side of associativity evaluates to `α ≫ (x ◁ m) ≫ m`. -/
lemma interpPath_grpEqnRhs_assoc (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).rhs (s, .assoc)) z =
      (α_ (carrier z s) (carrier z s) (carrier z s)).hom ≫ MonoidalCategory.whiskerLeft (carrier z
          s) (mul z s) ≫ mul z s := by
  refine (interpPath_comp z (assocPath (sortTerm s) (sortTerm s) (sortTerm s))
    (OneSig.Path.comp (whiskerLeftPath (sortTerm s) (mulPath s)) (mulPath s))).trans ?_
  rw [interpPath_comp, interpPath_assocPath, interpPath_whiskerLeftPath, interpPath_mulPath]; rfl

/-- The left side of the right unit law evaluates to `lift 𝟙 (! ≫ e) ≫ m`. -/
lemma interpPath_grpEqnLhs_mulOne (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).lhs (s, .mulOne)) z =
      lift (𝟙 (carrier z s)) (toUnit (carrier z s) ≫ one z s) ≫ mul z s := by
  refine (interpPath_comp z (liftPath (.nil (sortTerm s)) (constOnePath s)) (mulPath s)).trans ?_
  rw [interpPath_liftPath, interpPath_nil, interpPath_constOnePath,
      interpPath_mulPath]; rfl

/-- The left side of the left unit law evaluates to `lift (! ≫ e) 𝟙 ≫ m`. -/
lemma interpPath_grpEqnLhs_oneMul (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).lhs (s, .oneMul)) z =
      lift (toUnit (carrier z s) ≫ one z s) (𝟙 (carrier z s)) ≫ mul z s := by
  refine (interpPath_comp z (liftPath (constOnePath s) (.nil (sortTerm s))) (mulPath s)).trans ?_
  rw [interpPath_liftPath, interpPath_nil, interpPath_constOnePath,
      interpPath_mulPath]; rfl

/-- The left side of the left inverse law evaluates to `lift i 𝟙 ≫ m`. -/
lemma interpPath_grpEqnLhs_invMul (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).lhs (s, .invMul)) z = lift (inv z s) (𝟙 (carrier z s)) ≫ mul z s := by
  refine (interpPath_comp z (liftPath (invPath s) (.nil (sortTerm s))) (mulPath s)).trans ?_
  rw [interpPath_liftPath, interpPath_nil, interpPath_invPath, interpPath_mulPath];
      rfl

/-- The left side of the right inverse law evaluates to `lift 𝟙 i ≫ m`. -/
lemma interpPath_grpEqnLhs_mulInv (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).lhs (s, .mulInv)) z = lift (𝟙 (carrier z s)) (inv z s) ≫ mul z s := by
  refine (interpPath_comp z (liftPath (.nil (sortTerm s)) (invPath s)) (mulPath s)).trans ?_
  rw [interpPath_liftPath, interpPath_nil, interpPath_invPath, interpPath_mulPath];
      rfl

/-- The right side of the right unit law evaluates to `𝟙`. -/
lemma interpPath_grpEqnRhs_mulOne (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).rhs (s, .mulOne)) z = 𝟙 (carrier z s) := interpPath_nil z (sortTerm s)

/-- The right side of the left unit law evaluates to `𝟙`. -/
lemma interpPath_grpEqnRhs_oneMul (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).rhs (s, .oneMul)) z = 𝟙 (carrier z s) := interpPath_nil z (sortTerm s)

/-- The right side of the left inverse law evaluates to `! ≫ e`. -/
lemma interpPath_grpEqnRhs_invMul (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).rhs (s, .invMul)) z = toUnit (carrier z s) ≫ one z s :=
        interpPath_constOnePath z s

/-- The right side of the right inverse law evaluates to `! ≫ e`. -/
lemma interpPath_grpEqnRhs_mulInv (z : SigModel B S) (s : S) :
    interpPath ((grpTheory S).rhs (s, .mulInv)) z = toUnit (carrier z s) ≫ one z s :=
        interpPath_constOnePath z s

/-- **The defining condition of `M^T`**: an object of `M^σ` is a model of the theory of groups
exactly when it satisfies the group axioms in each sort. -/
lemma lhsCell_eq_rhsCell_iff (z : SigModel B S) :
    ((cartModel B).lhsCell (grpSig S) (grpTheory S)).toNatTrans.app z =
        ((cartModel B).rhsCell (grpSig S) (grpTheory S)).toNatTrans.app z ↔ ∀ s, GrpAxioms z s := by
  refine funext_iff.trans ?_
  constructor
  · intro h s
    have hassoc := h (s, .assoc)
    have hmulOne := h (s, .mulOne)
    have honeMul := h (s, .oneMul)
    have hinvMul := h (s, .invMul)
    have hmulInv := h (s, .mulInv)
    rw [lhsCell_app, rhsCell_app] at hassoc hmulOne honeMul hinvMul hmulInv
    exact ⟨by rw [← interpPath_grpEqnLhs_assoc, ← interpPath_grpEqnRhs_assoc]; exact hassoc,
      by rw [← interpPath_grpEqnLhs_mulOne, ← interpPath_grpEqnRhs_mulOne]; exact hmulOne,
      by rw [← interpPath_grpEqnLhs_oneMul, ← interpPath_grpEqnRhs_oneMul]; exact honeMul,
      by rw [← interpPath_grpEqnLhs_invMul, ← interpPath_grpEqnRhs_invMul]; exact hinvMul,
      by rw [← interpPath_grpEqnLhs_mulInv, ← interpPath_grpEqnRhs_mulInv]; exact hmulInv⟩
  · rintro h ⟨s, e⟩
    rw [lhsCell_app, rhsCell_app]
    cases e
    · rw [interpPath_grpEqnLhs_assoc, interpPath_grpEqnRhs_assoc]; exact (h s).assoc
    · rw [interpPath_grpEqnLhs_mulOne, interpPath_grpEqnRhs_mulOne]; exact (h s).mulOne
    · rw [interpPath_grpEqnLhs_oneMul, interpPath_grpEqnRhs_oneMul]; exact (h s).oneMul
    · rw [interpPath_grpEqnLhs_invMul, interpPath_grpEqnRhs_invMul]; exact (h s).invMul
    · rw [interpPath_grpEqnLhs_mulInv, interpPath_grpEqnRhs_mulInv]; exact (h s).mulInv

/-! ## The unit laws in two forms -/

section Conv

variable {D : Type*} [Category D] [CartesianMonoidalCategory D] {X : D} (e : 𝟙_ D ⟶ X)

/-- In a cartesian category, `e ▷ X = λ ≫ lift (! ≫ e) 𝟙` for `e : 𝟙 ⟶ X`. -/
lemma whiskerRight_unit_eq : e ▷ X = (λ_ X).hom ≫ lift (toUnit X ≫ e) (𝟙 X) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [whiskerRight_fst, Category.assoc, lift_fst, leftUnitor_hom]
    rw [← Category.assoc]; congr 1; exact toUnit_unique _ _
  · simp [leftUnitor_hom]

/-- In a cartesian category, `X ◁ e = ρ ≫ lift 𝟙 (! ≫ e)` for `e : 𝟙 ⟶ X`. -/
lemma whiskerLeft_unit_eq : X ◁ e = (ρ_ X).hom ≫ lift (𝟙 X) (toUnit X ≫ e) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [rightUnitor_hom]
  · simp only [whiskerLeft_snd, Category.assoc, lift_snd, rightUnitor_hom]
    rw [← Category.assoc]; congr 1; exact toUnit_unique _ _

end Conv

/-- The group structure of a sort of a model of the theory of groups. -/
@[instance_reducible]
def grpObjOfGrpAxioms (z : SigModel B S) (s : S) (h : GrpAxioms z s) : GrpObj (carrier z s) where
  one := one z s
  mul := mul z s
  one_mul := by rw [whiskerRight_unit_eq, Category.assoc, h.oneMul, Category.comp_id]
  mul_one := by rw [whiskerLeft_unit_eq, Category.assoc, h.mulOne, Category.comp_id]
  mul_assoc := h.assoc
  inv := inv z s
  left_inv := h.invMul
  right_inv := h.mulInv

/-- A family of group objects, as an object of `M^σ`. -/
def sigModelOfGrp (G : S → Grp B) : SigModel B S where
  pt := fun s => (G s).X
  cell := fun f => match f with
    | (s, .mul) => (MonObj.mul : (G s).X ⊗ (G s).X ⟶ (G s).X)
    | (s, .one) => (MonObj.one : 𝟙_ B ⟶ (G s).X)
    | (s, .inv) => (GrpObj.inv : (G s).X ⟶ (G s).X)

/-- The object of `M^σ` built from a family of internal groups satisfies the group axioms in each
sort. -/
lemma grpAxioms_sigModelOfGrp (G : S → Grp B) (s : S) : GrpAxioms (sigModelOfGrp G) s where
  assoc := MonObj.mul_assoc (G s).X
  mulOne := by
    have h := MonObj.mul_one (G s).X
    rw [whiskerLeft_unit_eq, Category.assoc] at h
    exact (cancel_epi (ρ_ (G s).X).hom).1 (h.trans (Category.comp_id _).symm)
  oneMul := by
    have h := MonObj.one_mul (G s).X
    rw [whiskerRight_unit_eq, Category.assoc] at h
    exact (cancel_epi (λ_ (G s).X).hom).1 (h.trans (Category.comp_id _).symm)
  invMul := GrpObj.left_inv (G s).X
  mulInv := GrpObj.right_inv (G s).X

/-! ## The equivalence -/

/-- The category `M^T` of models of the theory of groups. -/
abbrev GrpModel (B : Type (max u₁ v w)) [Category.{max u₁ v} B] [CartesianMonoidalCategory B]
    (S : Type u₁) :
    Type (max u₁ v w) :=
  ((cartModel B).thyObj (grpSig S) (grpTheory S) : Type (max u₁ v w))

/-- An object of `M^T` satisfies the group axioms in each sort (by `lhsCell_eq_rhsCell_iff`). -/
lemma grpAxioms_of_grpModel (t : GrpModel B S) (s : S) : GrpAxioms t.obj s :=
    (lhsCell_eq_rhsCell_iff t.obj).1 t.property s

/-- The group object of a sort of a model. -/
def toGrp (t : GrpModel B S) (s : S) : Grp B := @Grp.mk B _ _ (carrier t.obj s)
    (grpObjOfGrpAxioms t.obj s (grpAxioms_of_grpModel t s))

/-- The component of a morphism of `M^σ` at a sort. -/
def baseHom {z z' : SigModel B S} (f : z ⟶ z') (s : S) : carrier z s ⟶ carrier z' s := f.base s

/-- A morphism of `M^σ` commutes with the multiplications. -/
lemma baseHom_mul {z z' : SigModel B S} (f : z ⟶ z') (s : S) :
    mul z s ≫ baseHom f s = (baseHom f s ⊗ₘ baseHom f s) ≫ mul z' s := funext_iff.1 f.w (s, .mul)

/-- A morphism of `M^σ` preserves the units. -/
lemma baseHom_one {z z' : SigModel B S} (f : z ⟶ z') (s : S) :
    one z s ≫ baseHom f s = one z' s := by
  have h : one z s ≫ baseHom f s = 𝟙 (𝟙_ B) ≫ one z' s := funext_iff.1 f.w (s, .one)
  simpa using h

/-- **The comparison functor** from models of the theory of groups to families of internal
groups. -/
def toFamily (B : Type (max u₁ v w)) [Category.{max u₁ v} B] [CartesianMonoidalCategory B]
    (S : Type u₁) :
    GrpModel B S ⥤ (S → Grp B) where
  obj t s := toGrp t s
  map f s := Grp.homMk'' (A := toGrp _ s) (B := toGrp _ s) (baseHom f.hom s)
    (baseHom_one f.hom s) (baseHom_mul f.hom s)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A morphism of `M^σ` built from a family of morphisms compatible with the operations. -/
def grpModelHomMk {z z' : SigModel B S} (g : ∀ s, carrier z s ⟶ carrier z' s)
    (hm : ∀ s, mul z s ≫ g s = (g s ⊗ₘ g s) ≫ mul z' s) (he : ∀ s, one z s ≫ g s = one z' s)
    (hi : ∀ s, inv z s ≫ g s = g s ≫ inv z' s) : z ⟶ z' where
  base := g
  w := by
    funext f
    rcases f with ⟨s, _ | _ | _⟩
    · exact hm s
    · exact (he s).trans (Category.id_comp _).symm
    · exact hi s

/-- A family of internal groups, as a model of the theory of groups. -/
def ofFamily (G : S → Grp B) : GrpModel B S :=
  ⟨sigModelOfGrp G, (lhsCell_eq_rhsCell_iff (sigModelOfGrp G)).2 (grpAxioms_sigModelOfGrp G)⟩

/-- The comparison `toFamily : M^T ⥤ (S → Grp B)` is faithful. -/
instance : (toFamily B S).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply Ins.hom_ext
    funext s
    exact congr(($(funext_iff.1 h s)).hom.hom)

/-- The comparison `toFamily : M^T ⥤ (S → Grp B)` is full. -/
instance : (toFamily B S).Full where
  map_surjective {t t'} g := by
    refine ⟨ObjectProperty.homMk (grpModelHomMk (fun s => (g s).hom.hom)
      (fun s => IsMonHom.mul_hom (g s).hom.hom) (fun s => IsMonHom.one_hom (g s).hom.hom)
      (fun s => ?_)), ?_⟩
    · exact @GrpObj.inv_hom B _ _ (carrier t.obj s) (carrier t'.obj s)
        (grpObjOfGrpAxioms t.obj s (grpAxioms_of_grpModel t s))
        (grpObjOfGrpAxioms t'.obj s (grpAxioms_of_grpModel t' s)) (g s).hom.hom
            (g s).hom.isMonHom_hom
    · rfl

/-- The comparison `toFamily : M^T ⥤ (S → Grp B)` is essentially surjective (via `ofFamily`). -/
instance : (toFamily B S).EssSurj where
  mem_essImage G := ⟨ofFamily G, ⟨Pi.isoMk fun s => Grp.mkIso (Iso.refl _)
    (Category.comp_id _) (by
    change MonObj.mul ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ MonObj.mul; simp; rfl)⟩⟩

/-- The comparison `toFamily : M^T ⥤ (S → Grp B)` is an equivalence. -/
instance : (toFamily B S).IsEquivalence where

/-- **Models of the theory of groups in `B` are `S`-indexed families of internal groups.** -/
noncomputable def grpModelEquiv (B : Type (max u₁ v w)) [Category.{max u₁ v} B]
    [CartesianMonoidalCategory B] (S : Type u₁) :
    GrpModel B S ≌ (S → Grp B) :=
  (toFamily B S).asEquivalence

end UlmerBialgebras.Paper.Cart.GrpModels
