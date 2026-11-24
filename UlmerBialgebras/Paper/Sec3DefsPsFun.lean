module

public import UlmerBialgebras.Models.LaxCell
public import UlmerBialgebras.Models.OplaxCell
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Modification.Lax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The 2-signature of a bicategory and the model of a pseudofunctor

Examples 3.4 and 3.9 of *A Syntactic Approach to Ulmer's Bialgebras* [forsman2026syntactic], for
an arbitrary bicategory `A` and a pseudofunctor (Mathlib's `Pseudofunctor`).

* `UlmerBialgebras.Paper.PsFun.sigOf A` (Example 3.4): the 2-signature `Σ_A` of a bicategory `A`.
  Its category symbols are the objects of `A`, its functor symbols the 1-cells, and its
  transformation symbols are the 2-cells `η^{x_a} : f(x_a) → g(x_a)`, the composition symbols
  `α_{g,f}^{x_a} : (gf)(x_a) → g(f(x_a))` and the unit symbols `β_a^{x_a} : id_a(x_a) → x_a`.
  The associators and unitors of `A` are 2-cells, so they are transformation symbols too.
* `UlmerBialgebras.Paper.PsFun.model F` (Example 3.9): the `Σ_A`-model `M_F` of a pseudofunctor
  `F : A → K`. The composition and unit symbols are interpreted by the structure isomorphisms
  `F (f ≫ g) ≅ F f ≫ F g` and `F (𝟙 a) ≅ 𝟙` of `F`.

This generalizes `UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`, where `A` is a strict 2-category and
`F` a strict
2-functor; those definitions are kept unchanged for the statements that use them.

Conventions. The library composes 1-cells in diagrammatic order, `f ≫ g` for the paper's `gf`.
The 2-category `K` is strict with chosen finite products, so that the existing definition of a
`Σ`-model applies; the construction uses only the unary products `∏_{i : Fin 1} F a`. A functor
symbol has a one-element arity, so `M_F(f)` is `F f` precomposed with the projection out of the
chosen unary product, and the transformation cells of `M_F` are `F η`, `F(gf) ≅ Fg ∘ Ff` and
`F(id) ≅ id` up to this identification (`eqToHom`).

## Main definitions

* `UlmerBialgebras.Paper.PsFun.sigOf`: the 2-signature `Σ_A` of a bicategory `A` (Example 3.4).
* `UlmerBialgebras.Paper.PsFun.model`: the `Σ_A`-model `M_F` of a pseudofunctor (Example 3.9).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.4, 3.9, 3.12
-/

universe u v w ua va wa

namespace UlmerBialgebras.Paper.PsFun

open CategoryTheory

variable (A : Type ua) [Bicategory.{wa, va} A]

/-- The functor symbols of `Σ_A`: the 1-cells of `A`. -/
abbrev SigFun : Type (max ua va) := Σ (a b : A), (a ⟶ b)

/-- The transformation symbols of `Σ_A` (Example 3.4). -/
inductive SigTr : Type (max ua va wa)
  /-- `η^{x_a} : f(x_a) → g(x_a)` for a 2-cell `η : f ⇒ g : a → b`. -/
  | cell {a b : A} {f g : a ⟶ b} (η : f ⟶ g)
  /-- `α_{g,f}^{x_a} : (gf)(x_a) → g(f(x_a))` for composable `a --f--> b --g--> c`. -/
  | comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
  /-- `β_a^{x_a} : id_a(x_a) → x_a`. -/
  | unit (a : A)

variable {A}

/-- The type of the variable of a transformation symbol of `Σ_A`. -/
@[reducible] def SigTr.src : SigTr A → A
  | .cell (a := a) _ => a
  | .comp (a := a) _ _ => a
  | .unit a => a

/-- The type of the terms of a transformation symbol of `Σ_A`. -/
@[reducible] def SigTr.tgt : SigTr A → A
  | .cell (b := b) _ => b
  | .comp (c := c) _ _ => c
  | .unit a => a

variable (A)

/-- The category and functor symbols of `Σ_A`. -/
@[reducible] def funSigOf : FunSig where
  Cat := A
  Fun := SigFun A
  arn := fun _ => 1
  art := fun B _ => B.1
  fcod := fun B => B.2.1

/-- The unary term `f(t)` of `Σ_A`. -/
@[reducible] def app1 {V : Type} {vty : V → A} {a b : A} (f : a ⟶ b)
    (t : Trm (funSigOf A) vty a) : Trm (funSigOf A) vty b :=
  Trm.app (S := funSigOf A) ⟨a, b, f⟩ (fun _ => t)

/-- The source term of a transformation symbol of `Σ_A`. -/
def sigTrSrc : ∀ τ : SigTr A, Trm (funSigOf A) (fun _ : Fin 1 => τ.src) τ.tgt
  | .cell (f := f) _ => app1 A f (.var 0)
  | .comp f g => app1 A (f ≫ g) (.var 0)
  | .unit a => app1 A (𝟙 a) (.var 0)

/-- The target term of a transformation symbol of `Σ_A`. -/
def sigTrTgt : ∀ τ : SigTr A, Trm (funSigOf A) (fun _ : Fin 1 => τ.src) τ.tgt
  | .cell (g := g) _ => app1 A g (.var 0)
  | .comp f g => app1 A g (app1 A f (.var 0))
  | .unit _ => .var 0

/-- **Example 3.4** ([forsman2026syntactic]): the 2-signature `Σ_A` of a bicategory `A`. -/
@[reducible] def sigOf : TwoSig.{ua, max ua va, max ua va wa} where
  toFunSig := funSigOf A
  Tr := SigTr A
  trn := fun _ => 1
  trt := fun τ _ => τ.src
  trty := fun τ => τ.tgt
  trsrc := sigTrSrc A
  trtgt := sigTrTgt A

variable {A}
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K]
  [HasChosenFinProducts.{u, v, w} K] (F : Pseudofunctor A K)

/-- The interpretation of the category and functor symbols of `Σ_A` given by a pseudofunctor `F`:
`M_F(a) = F a` and `M_F(f) = F f` (precomposed with the unary product projection). -/
@[reducible] def preModel : PreModel (sigOf A) K where
  obj := F.obj
  fn := fun B => (HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj B.1)).π 0 ≫ F.map B.2.2

/-- The interpretation of a unary term `f(x)` at the generic environment of a transformation
symbol is the projection followed by `F f`. -/
lemma preModel_interp_app1_var (τ : SigTr A) {b : A} (f : τ.src ⟶ b) :
    (preModel F).interp ((preModel F).Pctx τ).π
        (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => τ.src) 0)) =
      ((preModel F).Pctx τ).π 0 ≫ F.map f :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ F.map f) (Product.lift_π _ _ 0))

/-- The interpretation of the composition symbols of `Σ_A` given by `F`: `F (f ≫ g) ≅ F f ≫ F g`,
whiskered by the projection. -/
def trCellComp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (preModel F).interp ((preModel F).Pctx (SigTr.comp f g)).π ((sigOf A).trsrc (.comp f g)) ⟶
      (preModel F).interp ((preModel F).Pctx (SigTr.comp f g)).π ((sigOf A).trtgt (.comp f g)) :=
  eqToHom (preModel_interp_app1_var F (.comp f g) (f ≫ g)) ≫
    (((preModel F).Pctx (SigTr.comp f g)).π 0 ◁ (F.mapComp f g).hom) ≫
    eqToHom (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ F.map g) (preModel_interp_app1_var F (.comp f g) f).symm)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ F.map g) (Product.lift_π _ _ 0))).symm)

/-- The interpretation of the unit symbols of `Σ_A` given by `F`: `F (𝟙 a) ≅ 𝟙`, whiskered by the
projection. -/
def trCellUnit (a : A) :
    (preModel F).interp ((preModel F).Pctx (SigTr.unit a)).π ((sigOf A).trsrc (.unit a)) ⟶
      (preModel F).interp ((preModel F).Pctx (SigTr.unit a)).π ((sigOf A).trtgt (.unit a)) :=
  eqToHom (preModel_interp_app1_var F (.unit a) (𝟙 a)) ≫
    (((preModel F).Pctx (SigTr.unit a)).π 0 ◁ (F.mapId a).hom) ≫
    eqToHom (Category.comp_id _)

/-- The interpretation of the transformation symbols of `Σ_A` given by `F`. -/
def trCell : ∀ τ : SigTr A,
    (preModel F).interp ((preModel F).Pctx τ).π ((sigOf A).trsrc τ) ⟶
      (preModel F).interp ((preModel F).Pctx τ).π ((sigOf A).trtgt τ)
  | .cell η => _ ◁ (_ ◁ F.map₂ η)
  | .comp f g => trCellComp F f g
  | .unit a => trCellUnit F a

/-- **Example 3.9** ([forsman2026syntactic]): the `Σ_A`-model `M_F` induced by a pseudofunctor
`F : A → K`. -/
@[reducible] def model : Model (sigOf A) K where
  toPreModel := preModel F
  tr := trCell F

end UlmerBialgebras.Paper.PsFun
