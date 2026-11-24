module

public import Mathlib.Data.ZMod.Defs
public import UlmerBialgebras.Examples.FieldModel
public import UlmerBialgebras.Models.CatCells

/-!
# Computing `M^σ` and `M^T` for the theory of fields

For the model `M = (Set, ×, 1, (−) + 1)` of `FieldModel.lean`, this file computes the object
of operations `M^σ` and the defining condition of `M^T` for the theory `T_Field` of
Examples 3.20 (3):

* an object of `M^σ` is a set `X` (`UlmerBialgebras.FieldEx.ob`) together with operations
  `m : X × X → X`, `i : X → X`, `e : 1 → X` and `m₁, m₂ : (X+1) × (X+1) → X + 1`,
  `ν : X + 1 → X + 1`, `ι : 1 → X + 1` (`UlmerBialgebras.FieldEx.mul`, `inv`, `one`, `add`, `rmul`,
  `neg`, `zero`), a morphism being a function commuting with all of them
  (`UlmerBialgebras.FieldEx.bs`, `UlmerBialgebras.FieldEx.homMk`);
* every arrow and every derived path of the term graph occurring in `T_Field` is evaluated
  at such an object (`UlmerBialgebras.FieldEx.mulP`, `addP`, `assocP`, `swapP`, `etaSP`, …);
* consequently the defining condition of `M^T` is exactly the conjunction of the thirteen
  field axioms `UlmerBialgebras.FieldEx.Axioms` (`UlmerBialgebras.FieldEx.mem_thy_iff`).

Objects of `M^σ` are also built from raw data by `UlmerBialgebras.FieldEx.ofData`.

## Main results

* `UlmerBialgebras.FieldEx.Axioms`: the field axioms for the operations of an object of `M^σ`.
* `UlmerBialgebras.FieldEx.mem_thy_iff`: an object of `M^σ` satisfies the defining condition of
  `M^T` (Definition 3.14) iff it satisfies `UlmerBialgebras.FieldEx.Axioms`.
* `UlmerBialgebras.FieldEx.homMk`: a function commuting with the operations is a morphism of `M^σ`.
* `UlmerBialgebras.FieldEx.ofData`: the object of `M^σ` built from a set and seven operations.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 3.13 and 3.14, Examples 3.20 (3)
-/

@[expose] public section


universe u

namespace UlmerBialgebras

namespace FieldEx

open CategoryTheory Limits

/-- The objects of `M^σ`. -/
abbrev SigObj : Type (u + 1) := ((model.{u}).sigObj oneSig : Type (u + 1))

/-- A morphism of `Type u`, as a function. -/
abbrev ev {A B : Type u} (f : A ⟶ B) (a : A) : B := f a

/-- The underlying set. -/
def ob (z : SigObj.{u}) : Type u := Ins.pt z ()

/-- The multiplication. -/
def mul (z : SigObj.{u}) (x y : ob z) : ob z := ev (Ins.cell z FnSym.mul) (x, y)

/-- The inverse. -/
def inv (z : SigObj.{u}) (x : ob z) : ob z := ev (Ins.cell z FnSym.inv) x

/-- The unit. -/
def one (z : SigObj.{u}) : ob z := ev (Ins.cell z FnSym.one) PUnit.unit

/-- The addition on `Ss`. -/
def add (z : SigObj.{u}) (x y : Option (ob z)) : Option (ob z) :=
  ev (Ins.cell z FnSym.add) (x, y)

/-- The ring multiplication on `Ss`. -/
def rmul (z : SigObj.{u}) (x y : Option (ob z)) : Option (ob z) :=
  ev (Ins.cell z FnSym.rmul) (x, y)

/-- The negation on `Ss`. -/
def neg (z : SigObj.{u}) (x : Option (ob z)) : Option (ob z) :=
  ev (Ins.cell z FnSym.neg) x

/-- The zero of `Ss`. -/
def zero (z : SigObj.{u}) : Option (ob z) := ev (Ins.cell z FnSym.zero) PUnit.unit

/-- The underlying map of a morphism of `M^σ`. -/
def bs {z z' : SigObj.{u}} (f : z ⟶ z') : ob z → ob z' := ev (f.base ())

/-! ## Term interpretations on objects -/

/-- The term `s` is interpreted at `z` by the underlying set `X`. -/
@[simp] lemma sigTm_obj_sTm (z : SigObj.{u}) :
    ((model.{u}).sigTm oneSig sTm).toFunctor.obj z = ob z := rfl

/-- The term `a □ b` is interpreted at `z` by the product of the interpretations. -/
@[simp] lemma sigTm_obj_tn (a b : CTm) (z : SigObj.{u}) :
    ((model.{u}).sigTm oneSig (tn a b)).toFunctor.obj z =
      (((model.{u}).sigTm oneSig a).toFunctor.obj z × ((model.{u}).sigTm oneSig b).toFunctor.obj z)
          := rfl

/-- The term `S a` is interpreted at `z` by `Option` of the interpretation of `a`. -/
@[simp] lemma sigTm_obj_sc (a : CTm) (z : SigObj.{u}) :
    ((model.{u}).sigTm oneSig (sc a)).toFunctor.obj z = Option (((model.{u}).sigTm oneSig
        a).toFunctor.obj z) := rfl

/-- The term `I` is interpreted at `z` by the one-point set. -/
@[simp] lemma sigTm_obj_un (z : SigObj.{u}) :
    ((model.{u}).sigTm oneSig (un : CTm)).toFunctor.obj z = PUnit := rfl

/-! ## The underlying function of a 2-cell -/

/-- The set interpreting a closed term at an object of `M^σ`. -/
abbrev tmS (z : SigObj.{u}) (t : CTm) : Type u := ((model.{u}).sigTm oneSig t).toFunctor.obj z

/-- The function underlying the component at `z` of a 2-cell between term 1-cells. -/
noncomputable def fnOf {t t' : CTm}
    (α : (model.{u}).sigTm oneSig t ⟶ (model.{u}).sigTm oneSig t') (z : SigObj.{u}) :
    tmS z t → tmS z t' := ev (α.toNatTrans.app z)
/-- The function underlying a vertical composite of 2-cells is the composite of the functions. -/
@[simp] lemma fnOf_comp {t t' t'' : CTm}
    (α : (model.{u}).sigTm oneSig t ⟶ (model.{u}).sigTm oneSig t')
    (β : (model.{u}).sigTm oneSig t' ⟶ (model.{u}).sigTm oneSig t'') (z : SigObj.{u}) (x : tmS z t)
        :
    fnOf (α ≫ β) z x = fnOf β z (fnOf α z x) := rfl

/-- The function underlying an identity 2-cell is the identity. -/
@[simp] lemma fnOf_id {t : CTm} (z : SigObj.{u}) (x : tmS z t) :
    fnOf (𝟙 ((model.{u}).sigTm oneSig t)) z x = x := rfl


/-- The function underlying the evaluation of a path. -/
noncomputable abbrev pathFn {t t' : CTm} (p : oneSig.Path t t') (z : SigObj.{u}) : tmS z t → tmS z
    t' :=
  fnOf ((model.{u}).pathCell oneSig p) z

/-- The empty path is evaluated by the identity function. -/
@[simp] lemma pathFn_nil (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    pathFn (OneSig.Path.nil t) z x = x := by
  simp [pathFn]

/-- The path `cons g p` is evaluated by first applying the arrow `g`, then the path `p`. -/
@[simp] lemma pathFn_cons {t t' t'' : CTm} (g : oneSig.Arr t t') (p : oneSig.Path t' t'')
    (z : SigObj.{u}) (x : tmS z t) :
    pathFn (OneSig.Path.cons g p) z x = pathFn p z (fnOf ((model.{u}).arrCell oneSig g) z x) := by
  simp [pathFn]

/-! ## Arrows of the term graph on objects -/

/-- The arrow of the multiplication symbol is interpreted at `z` by the structure map `mul`. -/
lemma arrCell_fn_mul_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.mul)).toNatTrans.app z = Ins.cell z FnSym.mul := rfl

/-- The arrow of the multiplication symbol is evaluated at `z` by `mul z`. -/
@[simp] lemma fnOf_mul (z : SigObj.{u}) (x : tmS z (tn sTm sTm)) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.mul)) z x = mul z x.1 x.2 := rfl

/-- The evaluation of a transported arrow. -/
lemma arrCell_transport {c : Unit} {t₁ t₂ t₁' t₂' : oneSig.CTrm c} (h₁ : t₁ = t₁')
    (h₂ : t₂ = t₂') (g : oneSig.Arr t₁ t₂) :
    (model.{u}).arrCell oneSig (g.transport h₁ h₂) =
      eqToHom (by rw [h₁]) ≫ (model.{u}).arrCell oneSig g ≫ eqToHom (by rw [h₂]) := by
  subst h₁; subst h₂; simp [OneSig.Arr.transport]

/-- The arrow of the inverse symbol is interpreted at `z` by the structure map `inv`. -/
lemma arrCell_fn_inv_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.inv)).toNatTrans.app z = Ins.cell z FnSym.inv := rfl

/-- The arrow of the inverse symbol is evaluated at `z` by `inv z`. -/
@[simp] lemma fnOf_inv (z : SigObj.{u}) (x : tmS z sTm) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.inv)) z x = inv z x := rfl

/-- The arrow of the unit symbol is interpreted at `z` by the structure map `one`. -/
lemma arrCell_fn_one_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.one)).toNatTrans.app z = Ins.cell z FnSym.one := rfl

/-- The arrow of the unit symbol is evaluated at `z` by the constant `one z`. -/
@[simp] lemma fnOf_one (z : SigObj.{u}) (x : tmS z un) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.one)) z x = one z := rfl

/-- The arrow of the addition symbol is interpreted at `z` by the structure map `add`. -/
lemma arrCell_fn_add_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.add)).toNatTrans.app z = Ins.cell z FnSym.add := rfl

/-- The arrow of the addition symbol is evaluated at `z` by `add z`. -/
@[simp] lemma fnOf_add (z : SigObj.{u}) (x : tmS z (tn ssTm ssTm)) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.add)) z x = add z x.1 x.2 := rfl

/-- The arrow of the ring multiplication symbol is interpreted at `z` by the structure map
`rmul`. -/
lemma arrCell_fn_rmul_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.rmul)).toNatTrans.app z = Ins.cell z FnSym.rmul := rfl

/-- The arrow of the ring multiplication symbol is evaluated at `z` by `rmul z`. -/
@[simp] lemma fnOf_rmul (z : SigObj.{u}) (x : tmS z (tn ssTm ssTm)) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.rmul)) z x = rmul z x.1 x.2 := rfl

/-- The arrow of the negation symbol is interpreted at `z` by the structure map `neg`. -/
lemma arrCell_fn_neg_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.neg)).toNatTrans.app z = Ins.cell z FnSym.neg := rfl

/-- The arrow of the negation symbol is evaluated at `z` by `neg z`. -/
@[simp] lemma fnOf_neg (z : SigObj.{u}) (x : tmS z ssTm) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.neg)) z x = neg z x := rfl

/-- The arrow of the zero symbol is interpreted at `z` by the structure map `zero`. -/
lemma arrCell_fn_zero_app (z : SigObj.{u}) :
    ((model.{u}).arrCell oneSig (fnArr FnSym.zero)).toNatTrans.app z = Ins.cell z FnSym.zero := rfl

/-- The arrow of the zero symbol is evaluated at `z` by the constant `zero z`. -/
@[simp] lemma fnOf_zero (z : SigObj.{u}) (x : tmS z un) :
    fnOf ((model.{u}).arrCell oneSig (fnArr FnSym.zero)) z x = zero z := rfl

/-! ### Instances of the transformation symbols -/

/-- The diagonal `δ_t` is evaluated by `x ↦ (x, x)`. -/
@[simp] lemma fnOf_diag (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    fnOf ((model.{u}).arrCell oneSig (diagArr t)) z x = (x, x) := by
  rw [fnOf, diagArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp [model, diagCell]; rfl

/-- The first projection arrow is evaluated by `x ↦ x.1`. -/
@[simp] lemma fnOf_proj₁ (a b : CTm) (z : SigObj.{u}) (x : tmS z (tn a b)) :
    fnOf ((model.{u}).arrCell oneSig (proj₁Arr a b)) z x = x.1 := by
  rw [fnOf, proj₁Arr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp [model, proj₁Cell]; rfl

/-- The second projection arrow is evaluated by `x ↦ x.2`. -/
@[simp] lemma fnOf_proj₂ (a b : CTm) (z : SigObj.{u}) (x : tmS z (tn a b)) :
    fnOf ((model.{u}).arrCell oneSig (proj₂Arr a b)) z x = x.2 := by
  rw [fnOf, proj₂Arr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp [model, proj₂Cell]; rfl

/-- The arrow `!_t : t → I` is evaluated by the constant map to `PUnit.unit`. -/
@[simp] lemma fnOf_term (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    fnOf ((model.{u}).arrCell oneSig (termArr t)) z x = PUnit.unit := by
  rw [fnOf, termArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp [model, termCell]; rfl

/-- The unit `η_t : t → S t` is evaluated by `some`. -/
@[simp] lemma fnOf_eta (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    fnOf ((model.{u}).arrCell oneSig (etaArr t)) z x = some x := by
  rw [fnOf, etaArr, arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp [model, etaCell]; rfl

/-! ### Functorial images -/

/-- The arrow `g □ b` is evaluated by applying the evaluation of `g` to the first component. -/
@[simp] lemma fnOf_leftArr {a a' : CTm} (b : CTm) (g : oneSig.Arr a a') (z : SigObj.{u})
    (x : tmS z (tn a b)) :
    fnOf ((model.{u}).arrCell oneSig (leftArr b g)) z x =
      (fnOf ((model.{u}).arrCell oneSig g) z x.1, x.2) := rfl

/-- The arrow `a □ g` is evaluated by applying the evaluation of `g` to the second component. -/
@[simp] lemma fnOf_rightArr (a : CTm) {b b' : CTm} (g : oneSig.Arr b b') (z : SigObj.{u})
    (x : tmS z (tn a b)) :
    fnOf ((model.{u}).arrCell oneSig (rightArr a g)) z x =
      (x.1, fnOf ((model.{u}).arrCell oneSig g) z x.2) := rfl

/-! ## Paths -/

/-- The concatenation of two paths is evaluated by the composite of their evaluations. -/
@[simp] lemma pathFn_comp {t t' t'' : CTm} (p : oneSig.Path t t') (q : oneSig.Path t' t'')
    (z : SigObj.{u}) (x : tmS z t) :
    pathFn (OneSig.Path.comp p q) z x = pathFn q z (pathFn p z x) := by
  induction p with
  | nil t => simp [OneSig.Path.comp]
  | cons g p ih => simp [OneSig.Path.comp, ih]

/-- A single arrow, as a path, is evaluated as the arrow. -/
@[simp] lemma pathFn_arrPath {t t' : CTm} (g : oneSig.Arr t t') (z : SigObj.{u}) (x : tmS z t) :
    pathFn (arrPath g) z x = fnOf ((model.{u}).arrCell oneSig g) z x := by
  simp [arrPath]

/-- The path `p □ b` is evaluated by applying the evaluation of `p` to the first component. -/
@[simp] lemma pathFn_leftPath {a t : CTm} (b : CTm) (p : oneSig.Path a t) (z : SigObj.{u})
    (x : tmS z (tn a b)) :
    pathFn (leftPath b p) z x = (pathFn p z x.1, x.2) := by
  induction p with
  | nil t =>
    simp only [leftPath, pathFn_nil, Fin.isValue, cat_finProd_lift_obj, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact Prod.ext rfl rfl
  | cons g p ih => simpa [leftPath] using ih _

/-- The path `a □ p` is evaluated by applying the evaluation of `p` to the second component. -/
@[simp] lemma pathFn_rightPath (a : CTm) {b t : CTm} (p : oneSig.Path b t) (z : SigObj.{u})
    (x : tmS z (tn a b)) :
    pathFn (rightPath a p) z x = (x.1, pathFn p z x.2) := by
  induction p with
  | nil t =>
    simp only [rightPath, pathFn_nil, Fin.isValue, cat_finProd_lift_obj, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact Prod.ext rfl rfl
  | cons g p ih => simpa [rightPath] using ih _

/-- The path `p □ q` is evaluated componentwise by the evaluations of `p` and `q`. -/
@[simp] lemma pathFn_tensPath {a a' b b' : CTm} (p : oneSig.Path a a') (q : oneSig.Path b b')
    (z : SigObj.{u}) (x : tmS z (tn a b)) :
    pathFn (tensPath p q) z x = (pathFn p z x.1, pathFn q z x.2) := by
  simp only [tensPath, pathFn_comp, pathFn_leftPath, Fin.isValue, cat_finProd_lift_obj,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  exact pathFn_rightPath a' q z (pathFn p z x.1, x.2)

/-- The diagonal path is evaluated by `x ↦ (x, x)`. -/
@[simp] lemma pathFn_diagP (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    pathFn (diagP t) z x = (x, x) := by simp [diagP]; rfl

/-- The first projection path is evaluated by `x ↦ x.1`. -/
@[simp] lemma pathFn_fstP (a b : CTm) (z : SigObj.{u}) (x : tmS z (tn a b)) :
    pathFn (fstP a b) z x = x.1 := by simp [fstP]

/-- The second projection path is evaluated by `x ↦ x.2`. -/
@[simp] lemma pathFn_sndP (a b : CTm) (z : SigObj.{u}) (x : tmS z (tn a b)) :
    pathFn (sndP a b) z x = x.2 := by simp [sndP]

/-- The path `bangP t` to `I` is evaluated by the constant map to `PUnit.unit`. -/
@[simp] lemma pathFn_bangP (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    pathFn (bangP t) z x = PUnit.unit := by simp [bangP]; rfl

/-- The unit path `etaP t` is evaluated by `some`. -/
@[simp] lemma pathFn_etaP (t : CTm) (z : SigObj.{u}) (x : tmS z t) :
    pathFn (etaP t) z x = some x := by simp [etaP]; rfl

/-- The pairing `⟨p, q⟩` is evaluated by `x ↦ (pathFn p z x, pathFn q z x)`. -/
@[simp] lemma pathFn_pairP {t a b : CTm} (p : oneSig.Path t a) (q : oneSig.Path t b)
    (z : SigObj.{u}) (x : tmS z t) :
    pathFn (pairP p q) z x = (pathFn p z x, pathFn q z x) := by
  simp only [pairP, pathFn_comp, pathFn_diagP]
  exact pathFn_tensPath p q z (x, x)

/-- The derived associator is evaluated by `((x, y), w) ↦ (x, (y, w))`. -/
@[simp] lemma pathFn_assocP (a b c : CTm) (z : SigObj.{u}) (x : tmS z (tn (tn a b) c)) :
    pathFn (assocP a b c) z x = (x.1.1, (x.1.2, x.2)) := by
  simp [assocP]; rfl

/-- The derived symmetry is evaluated by `(x, y) ↦ (y, x)`. -/
@[simp] lemma pathFn_swapP (a b : CTm) (z : SigObj.{u}) (x : tmS z (tn a b)) :
    pathFn (swapP a b) z x = (x.2, x.1) := by
  simp [swapP]; rfl

/-! ### The paths attached to the function symbols -/

/-- The path `mulP` is evaluated at `z` by `mul z`. -/
@[simp] lemma pathFn_mulP (z : SigObj.{u}) (x : tmS z (tn sTm sTm)) :
    pathFn mulP z x = mul z x.1 x.2 := by simp [mulP]

/-- The path `invP` is evaluated at `z` by `inv z`. -/
@[simp] lemma pathFn_invP (z : SigObj.{u}) (x : tmS z sTm) :
    pathFn invP z x = inv z x := by simp [invP]

/-- The path `oneP` is evaluated at `z` by the constant `one z`. -/
@[simp] lemma pathFn_oneP (z : SigObj.{u}) (x : tmS z un) :
    pathFn oneP z x = one z := by simp [oneP]

/-- The path `addP` is evaluated at `z` by `add z`. -/
@[simp] lemma pathFn_addP (z : SigObj.{u}) (x : tmS z (tn ssTm ssTm)) :
    pathFn addP z x = add z x.1 x.2 := by simp [addP]

/-- The path `rmulP` is evaluated at `z` by `rmul z`. -/
@[simp] lemma pathFn_rmulP (z : SigObj.{u}) (x : tmS z (tn ssTm ssTm)) :
    pathFn rmulP z x = rmul z x.1 x.2 := by simp [rmulP]

/-- The path `negP` is evaluated at `z` by `neg z`. -/
@[simp] lemma pathFn_negP (z : SigObj.{u}) (x : tmS z ssTm) :
    pathFn negP z x = neg z x := by simp [negP]

/-- The path `zeroP` is evaluated at `z` by the constant `zero z`. -/
@[simp] lemma pathFn_zeroP (z : SigObj.{u}) (x : tmS z un) :
    pathFn zeroP z x = zero z := by simp [zeroP]

/-! ## The defining condition of `M^T` -/

/-- **The field axioms**, written out for the operations of an object of `M^σ`: `(X, m, i, u)`
is a commutative group, `(Option X, m₁, ν, ι, m₂, some u)` is a commutative ring, and `some`
is a morphism of magmas from `(X, m)` to `(Option X, m₂)`. -/
structure Axioms (z : SigObj.{u}) : Prop where
  /-- `m` is associative. -/
  mulAssoc : ∀ x y w : ob z, mul z (mul z x y) w = mul z x (mul z y w)
  /-- `m` is commutative. -/
  mulComm : ∀ x y : ob z, mul z x y = mul z y x
  /-- `u` is a unit for `m`. -/
  mulUnit : ∀ x : ob z, mul z (one z) x = x
  /-- `i` is an inverse for `m`. -/
  mulInv : ∀ x : ob z, mul z (inv z x) x = one z
  /-- `m₁` is associative. -/
  addAssoc : ∀ x y w : Option (ob z), add z (add z x y) w = add z x (add z y w)
  /-- `m₁` is commutative. -/
  addComm : ∀ x y : Option (ob z), add z x y = add z y x
  /-- `ι` is a unit for `m₁`. -/
  addUnit : ∀ x : Option (ob z), add z (zero z) x = x
  /-- `ν` is an inverse for `m₁`. -/
  addInv : ∀ x : Option (ob z), add z (neg z x) x = zero z
  /-- `m₂` is associative. -/
  rmulAssoc : ∀ x y w : Option (ob z), rmul z (rmul z x y) w = rmul z x (rmul z y w)
  /-- `m₂` is commutative. -/
  rmulComm : ∀ x y : Option (ob z), rmul z x y = rmul z y x
  /-- `ηs ∘ u` is a unit for `m₂`. -/
  rmulUnit : ∀ x : Option (ob z), rmul z (some (one z)) x = x
  /-- `m₂` distributes over `m₁`. -/
  distrib : ∀ x y w : Option (ob z), rmul z x (add z y w) = add z (rmul z x y) (rmul z x w)
  /-- `ηs` is a morphism of magmas. -/
  etaMul : ∀ x y : ob z, rmul z (some x) (some y) = some (mul z x y)

/-- The left-hand 2-cell of the theory at `z` and equation `r` is the interpretation of
the path `theory.lhs r`. -/
lemma lhsCell_app (z : SigObj.{u}) (r : EqnSym) :
    ((model.{u}).lhsCell oneSig theory).toNatTrans.app z r =
      ((model.{u}).pathCell oneSig (theory.lhs r)).toNatTrans.app z := rfl

/-- The right-hand 2-cell of the theory at `z` and equation `r` is the interpretation of
the path `theory.rhs r`. -/
lemma rhsCell_app (z : SigObj.{u}) (r : EqnSym) :
    ((model.{u}).rhsCell oneSig theory).toNatTrans.app z r =
      ((model.{u}).pathCell oneSig (theory.rhs r)).toNatTrans.app z := rfl

/-- Two 2-cells between term 1-cells agree at `z` exactly when the underlying functions do. -/
lemma app_eq_iff {t t' : CTm}
    (α β : (model.{u}).sigTm oneSig t ⟶ (model.{u}).sigTm oneSig t') (z : SigObj.{u}) :
    α.toNatTrans.app z = β.toNatTrans.app z ↔ ∀ x, fnOf α z x = fnOf β z x :=
  ⟨fun h x => by rw [fnOf, fnOf, h], fun h => ConcreteCategory.hom_ext (C := Type u) _ _ h⟩

private lemma pathFn_assocLHS_eq {a : CTm} (op : oneSig.Path (tn a a) a) (z : SigObj.{u})
    (fn : tmS z a → tmS z a → tmS z a) (hop : ∀ p, pathFn op z p = fn p.1 p.2)
    (x : tmS z (tn (tn a a) a)) :
    pathFn (assocLHS a op) z x = fn (fn x.1.1 x.1.2) x.2 := by
  rw [assocLHS, pathFn_comp, pathFn_leftPath]
  exact (hop _).trans congr(fn $(hop x.1) x.2)

private lemma pathFn_assocRHS_eq {a : CTm} (op : oneSig.Path (tn a a) a) (z : SigObj.{u})
    (fn : tmS z a → tmS z a → tmS z a) (hop : ∀ p, pathFn op z p = fn p.1 p.2)
    (x : tmS z (tn (tn a a) a)) :
    pathFn (assocRHS a op) z x = fn x.1.1 (fn x.1.2 x.2) := by
  rw [assocRHS, pathFn_comp, pathFn_assocP]
  refine (pathFn_comp _ _ z _).trans ?_
  exact congr(pathFn op z $(pathFn_rightPath a op z _)).trans
    ((hop _).trans congr(fn x.1.1 $(hop (x.1.2, x.2))))

private lemma pathFn_commRHS_eq {a : CTm} (op : oneSig.Path (tn a a) a) (z : SigObj.{u})
    (fn : tmS z a → tmS z a → tmS z a) (hop : ∀ p, pathFn op z p = fn p.1 p.2)
    (x : tmS z (tn a a)) :
    pathFn (commRHS a op) z x = fn x.2 x.1 := by
  rw [commRHS, pathFn_comp, pathFn_swapP]
  exact hop _

private lemma pathFn_unitLHS_eq {a : CTm} (op : oneSig.Path (tn a a) a) (c : oneSig.Path un a)
    (z : SigObj.{u}) (fn : tmS z a → tmS z a → tmS z a) (hop : ∀ p, pathFn op z p = fn p.1 p.2)
    (x : tmS z a) :
    pathFn (unitLHS a op c) z x = fn (pathFn c z PUnit.unit) x := by
  rw [unitLHS, pathFn_comp, pathFn_pairP]
  refine (hop _).trans ?_
  rw [pathFn_comp, pathFn_bangP, pathFn_nil]

private lemma pathFn_invLHS_eq {a : CTm} (op : oneSig.Path (tn a a) a) (iv : oneSig.Path a a)
    (z : SigObj.{u}) (fn : tmS z a → tmS z a → tmS z a) (hop : ∀ p, pathFn op z p = fn p.1 p.2)
    (x : tmS z a) :
    pathFn (invLHS a op iv) z x = fn (pathFn iv z x) x := by
  rw [invLHS, pathFn_comp, pathFn_pairP]
  refine (hop _).trans ?_
  rw [pathFn_nil]

private lemma pathFn_invRHS_eq (a : CTm) (c : oneSig.Path un a) (z : SigObj.{u}) (x : tmS z a) :
    pathFn (invRHS a c) z x = pathFn c z PUnit.unit := by
  rw [invRHS, pathFn_comp, pathFn_bangP]

private lemma pathFn_distribLHS_eq (z : SigObj.{u}) (x : tmS z (tn ssTm (tn ssTm ssTm))) :
    pathFn distribLHS z x = rmul z x.1 (add z x.2.1 x.2.2) := by
  rw [distribLHS, pathFn_comp, pathFn_rightPath]
  refine (pathFn_rmulP z _).trans ?_
  exact congr(rmul z x.1 $(pathFn_addP z x.2))

private lemma pathFn_distribRHS_eq (z : SigObj.{u}) (x : tmS z (tn ssTm (tn ssTm ssTm))) :
    pathFn distribRHS z x = add z (rmul z x.1 x.2.1) (rmul z x.1 x.2.2) := by
  rw [distribRHS, pathFn_comp, pathFn_pairP]
  refine (pathFn_addP z _).trans ?_
  -- Each summand is `rmul` of the first component with a component of the second.
  dsimp only
  congr 1
  · rw [pathFn_comp, pathFn_pairP]
    refine (pathFn_rmulP z _).trans ?_
    dsimp only
    rw [pathFn_fstP, pathFn_comp, pathFn_sndP ssTm (tn ssTm ssTm)]
    exact congr(rmul z x.1 $(pathFn_fstP ssTm ssTm z x.2))
  · rw [pathFn_comp, pathFn_pairP]
    refine (pathFn_rmulP z _).trans ?_
    dsimp only
    rw [pathFn_fstP, pathFn_comp, pathFn_sndP ssTm (tn ssTm ssTm)]
    exact congr(rmul z x.1 $(pathFn_sndP ssTm ssTm z x.2))

private lemma pathFn_etaMulLHS_eq (z : SigObj.{u}) (x : tmS z (tn sTm sTm)) :
    pathFn ((tensPath etaSP etaSP).comp rmulP) z x = rmul z (some x.1) (some x.2) := by
  rw [pathFn_comp, pathFn_tensPath]
  exact (pathFn_rmulP z _).trans congr(rmul z $(pathFn_etaP sTm z x.1) $(pathFn_etaP sTm z x.2))

private lemma pathFn_etaMulRHS_eq (z : SigObj.{u}) (x : tmS z (tn sTm sTm)) :
    pathFn (mulP.comp etaSP) z x = some (mul z x.1 x.2) := by
  rw [pathFn_comp]
  exact congr(pathFn etaSP z $(pathFn_mulP z x)).trans (pathFn_etaP sTm z _)

private lemma eqn_pathFn (z : SigObj.{u})
    (h : ((model.{u}).lhsCell oneSig theory).toNatTrans.app z =
      ((model.{u}).rhsCell oneSig theory).toNatTrans.app z)
    (r : EqnSym) (x : tmS z (theory.dom r)) :
    pathFn (theory.lhs r) z x = pathFn (theory.rhs r) z x :=
  (app_eq_iff _ _ z).1 ((lhsCell_app z r).symm.trans
    (congr($h r).trans (rhsCell_app z r))) x

/-- Forward direction of `mem_thy_iff`: equality of `lhsCell` and `rhsCell` on `z` implies
all field axioms. -/
private lemma axioms_of_lhsCell_eq_rhsCell (z : SigObj.{u})
    (h : ((model.{u}).lhsCell oneSig theory).toNatTrans.app z =
      ((model.{u}).rhsCell oneSig theory).toNatTrans.app z) :
    Axioms z := by
  -- Each axiom is the equation `h` at its symbol `r`, evaluated at a point `p` and read through
  -- the computations of `pathFn` above.
  have hm := fun p => pathFn_mulP z p
  have ha := fun p => pathFn_addP z p
  have hr := fun p => pathFn_rmulP z p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y w; let p : tmS z (tn (tn sTm sTm) sTm) := ((x, y), w)
    have e := eqn_pathFn z h .mulAssoc p; dsimp only [theory] at e
    rw [pathFn_assocLHS_eq mulP z _ hm, pathFn_assocRHS_eq mulP z _ hm] at e; exact e
  · intro x y; let p : tmS z (tn sTm sTm) := (x, y)
    have e := eqn_pathFn z h .mulComm p; dsimp only [theory] at e
    rw [hm, pathFn_commRHS_eq mulP z _ hm] at e; exact e
  · intro x; let p : tmS z sTm := x
    have e := eqn_pathFn z h .mulUnit p; dsimp only [theory] at e
    rw [pathFn_unitLHS_eq mulP oneP z _ hm, pathFn_oneP z (PUnit.unit : tmS z un), pathFn_nil] at e
    exact e
  · intro x; let p : tmS z sTm := x
    have e := eqn_pathFn z h .mulInv p; dsimp only [theory] at e
    rw [pathFn_invLHS_eq mulP invP z _ hm, pathFn_invP, pathFn_invRHS_eq,
      pathFn_oneP z (PUnit.unit : tmS z un)] at e; exact e
  · intro x y w; let p : tmS z (tn (tn ssTm ssTm) ssTm) := ((x, y), w)
    have e := eqn_pathFn z h .addAssoc p; dsimp only [theory] at e
    rw [pathFn_assocLHS_eq addP z _ ha, pathFn_assocRHS_eq addP z _ ha] at e; exact e
  · intro x y; let p : tmS z (tn ssTm ssTm) := (x, y)
    have e := eqn_pathFn z h .addComm p; dsimp only [theory] at e
    rw [ha, pathFn_commRHS_eq addP z _ ha] at e; exact e
  · intro x; let p : tmS z ssTm := x
    have e := eqn_pathFn z h .addUnit p; dsimp only [theory] at e
    rw [pathFn_unitLHS_eq addP zeroP z _ ha, pathFn_zeroP z (PUnit.unit : tmS z un),
      pathFn_nil] at e
    exact e
  · intro x; let p : tmS z ssTm := x
    have e := eqn_pathFn z h .addInv p; dsimp only [theory] at e
    rw [pathFn_invLHS_eq addP negP z _ ha, pathFn_negP, pathFn_invRHS_eq,
      pathFn_zeroP z (PUnit.unit : tmS z un)] at e; exact e
  · intro x y w; let p : tmS z (tn (tn ssTm ssTm) ssTm) := ((x, y), w)
    have e := eqn_pathFn z h .rmulAssoc p; dsimp only [theory] at e
    rw [pathFn_assocLHS_eq rmulP z _ hr, pathFn_assocRHS_eq rmulP z _ hr] at e; exact e
  · intro x y; let p : tmS z (tn ssTm ssTm) := (x, y)
    have e := eqn_pathFn z h .rmulComm p; dsimp only [theory] at e
    rw [hr, pathFn_commRHS_eq rmulP z _ hr] at e; exact e
  · intro x; let p : tmS z ssTm := x
    have e := eqn_pathFn z h .rmulUnit p; dsimp only [theory] at e
    rw [pathFn_unitLHS_eq rmulP rmulUnitP z _ hr, pathFn_nil, rmulUnitP,
      pathFn_comp oneP etaSP z PUnit.unit, pathFn_oneP z (PUnit.unit : tmS z un), etaSP,
      pathFn_etaP sTm z (one z : tmS z sTm)] at e; exact e
  · intro x y w; let p : tmS z (tn ssTm (tn ssTm ssTm)) := (x, (y, w))
    have e := eqn_pathFn z h .distrib p; dsimp only [theory] at e
    rw [pathFn_distribLHS_eq, pathFn_distribRHS_eq] at e; exact e
  · intro x y; let p : tmS z (tn sTm sTm) := (x, y)
    have e := eqn_pathFn z h .etaMul p; dsimp only [theory] at e
    rw [pathFn_etaMulLHS_eq, pathFn_etaMulRHS_eq] at e; exact e

/-- Backward direction of `mem_thy_iff`: the field axioms imply equality of `lhsCell` and
`rhsCell` on `z`. -/
private lemma lhsCell_eq_rhsCell_of_axioms (z : SigObj.{u}) (hx : Axioms z) :
    ((model.{u}).lhsCell oneSig theory).toNatTrans.app z =
      ((model.{u}).rhsCell oneSig theory).toNatTrans.app z := by
  -- At each symbol `r`, both sides compute, through `pathFn`, to the two sides of an axiom.
  funext (r : EqnSym)
  rw [lhsCell_app, rhsCell_app]
  change ((model.{u}).pathCell oneSig (theory.lhs r)).toNatTrans.app z =
    ((model.{u}).pathCell oneSig (theory.rhs r)).toNatTrans.app z
  have hm := fun p => pathFn_mulP z p
  have ha := fun p => pathFn_addP z p
  have hr := fun p => pathFn_rmulP z p
  cases r <;> dsimp only [theory] <;> rw [app_eq_iff] <;> intro x <;>
    change pathFn _ z x = pathFn _ z x
  · rw [pathFn_assocLHS_eq mulP z _ hm, pathFn_assocRHS_eq mulP z _ hm]
    exact hx.mulAssoc x.1.1 x.1.2 x.2
  · rw [hm, pathFn_commRHS_eq mulP z _ hm]; exact hx.mulComm x.1 x.2
  · rw [pathFn_unitLHS_eq mulP oneP z _ hm, pathFn_oneP z PUnit.unit, pathFn_nil]
    exact hx.mulUnit x
  · rw [pathFn_invLHS_eq mulP invP z _ hm, pathFn_invP, pathFn_invRHS_eq,
      pathFn_oneP z (PUnit.unit : tmS z un)]; exact hx.mulInv x
  · rw [pathFn_assocLHS_eq addP z _ ha, pathFn_assocRHS_eq addP z _ ha]
    exact hx.addAssoc x.1.1 x.1.2 x.2
  · rw [ha, pathFn_commRHS_eq addP z _ ha]; exact hx.addComm x.1 x.2
  · rw [pathFn_unitLHS_eq addP zeroP z _ ha, pathFn_zeroP z PUnit.unit, pathFn_nil]
    exact hx.addUnit x
  · rw [pathFn_invLHS_eq addP negP z _ ha, pathFn_negP, pathFn_invRHS_eq,
      pathFn_zeroP z (PUnit.unit : tmS z un)]; exact hx.addInv x
  · rw [pathFn_assocLHS_eq rmulP z _ hr, pathFn_assocRHS_eq rmulP z _ hr]
    exact hx.rmulAssoc x.1.1 x.1.2 x.2
  · rw [hr, pathFn_commRHS_eq rmulP z _ hr]; exact hx.rmulComm x.1 x.2
  · rw [pathFn_unitLHS_eq rmulP rmulUnitP z _ hr, pathFn_nil, rmulUnitP,
      pathFn_comp oneP etaSP z PUnit.unit, pathFn_oneP z (PUnit.unit : tmS z un), etaSP,
      pathFn_etaP sTm z (one z : tmS z sTm)]
    exact hx.rmulUnit x
  · rw [pathFn_distribLHS_eq, pathFn_distribRHS_eq]; exact hx.distrib x.1 x.2.1 x.2.2
  · rw [pathFn_etaMulLHS_eq, pathFn_etaMulRHS_eq]; exact hx.etaMul x.1 x.2

/-- **The defining condition of `M^T`**: an object of `M^σ` is a `T_Field`-bialgebra exactly
when its operations satisfy the field axioms. -/
lemma mem_thy_iff (z : SigObj.{u}) :
    ((model.{u}).lhsCell oneSig theory).toNatTrans.app z = ((model.{u}).rhsCell oneSig
        theory).toNatTrans.app z ↔
      Axioms z :=
  ⟨axioms_of_lhsCell_eq_rhsCell z, lhsCell_eq_rhsCell_of_axioms z⟩

/-! ## Morphisms of `M^σ` -/

section Morphisms

variable {z z' : SigObj.{u}}

/-- The underlying map of the identity is the identity. -/
@[simp] lemma bs_id (z : SigObj.{u}) : bs (𝟙 z) = id := rfl

/-- The underlying map of a composite is the composite of the underlying maps. -/
@[simp] lemma bs_comp {z'' : SigObj.{u}} (f : z ⟶ z') (g : z' ⟶ z'') :
    bs (f ≫ g) = bs g ∘ bs f := rfl

/-- A morphism of `M^σ` is determined by its underlying map. -/
lemma bs_injective {f g : z ⟶ z'} (h : bs f = bs g) : f = g := by
  apply Ins.hom_ext
  funext s
  cases s
  exact ConcreteCategory.hom_ext (C := Type u) _ _ (funext_iff.mp h)

/-- The square of a morphism of `M^σ` at a function symbol, as an equality of functions. -/
lemma w_at (f : z ⟶ z') (s : FnSym) (x) :
    ev ((Ins.cell z s) ≫ ((model.{u}).codCell oneSig).toFunctor.map f.base s) x =
      ev (((model.{u}).domCell oneSig).toFunctor.map f.base s ≫ (Ins.cell z' s)) x := by
  exact congr(ev ($(f.w) s) x)

/-- The underlying map of a morphism of `M^σ` preserves the unit. -/
lemma bs_one (f : z ⟶ z') : bs f (one z) = one z' :=
  w_at f FnSym.one PUnit.unit

/-- The underlying map of a morphism, extended to `Option`, preserves the addition. -/
lemma bs_add (f : z ⟶ z') (x y : Option (ob z)) :
    Option.map (bs f) (add z x y) = add z' (Option.map (bs f) x) (Option.map (bs f) y) :=
  w_at f FnSym.add (x, y)

/-- The underlying map of a morphism, extended to `Option`, preserves the ring multiplication. -/
lemma bs_rmul (f : z ⟶ z') (x y : Option (ob z)) :
    Option.map (bs f) (rmul z x y) = rmul z' (Option.map (bs f) x) (Option.map (bs f) y) :=
  w_at f FnSym.rmul (x, y)

/-- The underlying map of a morphism, extended to `Option`, preserves the zero. -/
lemma bs_zero (f : z ⟶ z') : Option.map (bs f) (zero z) = zero z' :=
  w_at f FnSym.zero PUnit.unit

/-- A morphism of `M^σ`, built from a function compatible with the seven operations. -/
noncomputable def homMk (g : ob z → ob z')
    (hmul : ∀ x y, g (mul z x y) = mul z' (g x) (g y))
    (hinv : ∀ x, g (inv z x) = inv z' (g x))
    (hone : g (one z) = one z')
    (hadd : ∀ x y, Option.map g (add z x y) = add z' (Option.map g x) (Option.map g y))
    (hrmul : ∀ x y, Option.map g (rmul z x y) = rmul z' (Option.map g x) (Option.map g y))
    (hneg : ∀ x, Option.map g (neg z x) = neg z' (Option.map g x))
    (hzero : Option.map g (zero z) = zero z') : z ⟶ z' where
  base := fun _ => TypeCat.ofHom g
  w := by
    funext s
    refine ConcreteCategory.hom_ext (C := Type u) _ _ fun x => ?_
    cases s
    · exact hmul x.1 x.2
    · exact hinv x
    · exact hone
    · exact hadd x.1 x.2
    · exact hrmul x.1 x.2
    · exact hneg x
    · exact hzero

/-- The underlying map of `homMk g …` is `g`. -/
@[simp] lemma bs_homMk (g : ob z → ob z') (hmul hinv hone hadd hrmul hneg hzero) :
    bs (homMk (z := z) (z' := z') g hmul hinv hone hadd hrmul hneg hzero) = g := rfl

end Morphisms

/-! ## Objects of `M^σ` from raw data -/

/-- An object of `M^σ` built from a set and the seven operations. -/
noncomputable def ofData (X : Type u) (m : X → X → X) (i : X → X) (e : X)
    (a : Option X → Option X → Option X) (r : Option X → Option X → Option X)
    (n : Option X → Option X) (o : Option X) : SigObj.{u} where
  pt := fun _ => X
  cell := fun s => match s with
    | FnSym.mul => TypeCat.ofHom fun (p : X × X) => m p.1 p.2
    | FnSym.inv => TypeCat.ofHom i
    | FnSym.one => TypeCat.ofHom fun (_ : PUnit) => e
    | FnSym.add => TypeCat.ofHom fun (p : Option X × Option X) => a p.1 p.2
    | FnSym.rmul => TypeCat.ofHom fun (p : Option X × Option X) => r p.1 p.2
    | FnSym.neg => TypeCat.ofHom n
    | FnSym.zero => TypeCat.ofHom fun (_ : PUnit) => o

variable (X : Type u) (m : X → X → X) (i : X → X) (e : X)
  (a : Option X → Option X → Option X) (r : Option X → Option X → Option X)
  (n : Option X → Option X) (o : Option X)

/-- The underlying set of `ofData X …` is `X`. -/
@[simp] lemma ob_ofData : ob (ofData X m i e a r n o) = X := rfl

/-- The multiplication of `ofData X m …` is `m`. -/
@[simp] lemma mul_ofData (x y : X) : mul (ofData X m i e a r n o) x y = m x y := rfl

/-- The inverse of `ofData X m i …` is `i`. -/
@[simp] lemma inv_ofData (x : X) : inv (ofData X m i e a r n o) x = i x := rfl

/-- The unit of `ofData X m i e …` is `e`. -/
@[simp] lemma one_ofData : one (ofData X m i e a r n o) = e := rfl

/-- The addition of `ofData X m i e a …` is `a`. -/
@[simp] lemma add_ofData (x y : Option X) : add (ofData X m i e a r n o) x y = a x y := rfl

/-- The ring multiplication of `ofData X m i e a r …` is `r`. -/
@[simp] lemma rmul_ofData (x y : Option X) : rmul (ofData X m i e a r n o) x y = r x y := rfl

/-- The negation of `ofData X m i e a r n o` is `n`. -/
@[simp] lemma neg_ofData (x : Option X) : neg (ofData X m i e a r n o) x = n x := rfl

/-- The zero of `ofData X m i e a r n o` is `o`. -/
@[simp] lemma zero_ofData : zero (ofData X m i e a r n o) = o := rfl

end FieldEx

end UlmerBialgebras
