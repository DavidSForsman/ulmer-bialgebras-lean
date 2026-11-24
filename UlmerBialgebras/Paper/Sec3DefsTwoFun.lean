module

public import UlmerBialgebras.Models.LaxCell
public import UlmerBialgebras.Models.OplaxCell

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The 2-signature of a 2-category, the model of a 2-functor, and natural transformations

Examples 3.4, 3.9 and 3.12 of *A Syntactic Approach to Ulmer's Bialgebras*
[forsman2026syntactic].

* `UlmerBialgebras.Paper.TwoFun.sigOf A` (Example 3.4): the 2-signature `Σ_A` of a 2-category
  `A`. Its category symbols are the objects of `A`, its functor symbols the 1-cells, and its
  transformation symbols are the 2-cells `η^{x_a} : f(x_a) → g(x_a)`, the composition symbols
  `α_{g,f}^{x_a} : (gf)(x_a) → g(f(x_a))` and the unit symbols `β_a^{x_a} : id_a(x_a) → x_a`.
* `UlmerBialgebras.Paper.TwoFun.StrictTwoFunctor A K`: strict 2-functors.
* `UlmerBialgebras.Paper.TwoFun.StrictTwoFunctor.model F` (Example 3.9): the `Σ_A`-model `M_F`.
* `LaxNat`, `OplaxNat`, `LaxModif`, `OplaxModif` (Example 3.12): lax and oplax natural
  transformations between strict 2-functors and their modifications; pseudo and strict
  transformations are the lax ones whose naturality 2-cells are invertible, resp. identities.

Conventions. The library composes 1-cells in diagrammatic order, `f ≫ g` for the paper's
`gf`. A functor symbol of `Σ_A` has a one-element arity, so `M_F(f)` is `F f` precomposed with
the projection out of the chosen unary product `∏_{i : Fin 1} F a`; the transformation cells
of `M_F` are the paper's `Fη`, `id_{F(gf)}` and `id_{id_{Fa}}` up to this identification and
the equalities `F(gf) = Fg ∘ Ff`, `F(id) = id` (`eqToHom`).

The direction of the naturality 2-cells follows the paper's lax morphisms of models
(Definition 3.10): a lax transformation `σ : F ⇒ G` has `σ_f : G f ∘ σ_a ⇒ σ_b ∘ F f`, written
`σ_a ≫ G f ⟶ F f ≫ σ_b` here; an oplax one has the reverse 2-cells.

## Main results

* `UlmerBialgebras.Paper.TwoFun.sigOf`: the 2-signature `Σ_A` of a 2-category `A`
  (Example 3.4).
* `UlmerBialgebras.Paper.TwoFun.StrictTwoFunctor`,
  `UlmerBialgebras.Paper.TwoFun.StrictTwoFunctor.model`: strict 2-functors and the `Σ_A`-model `M_F`
  of a strict 2-functor (Example 3.9).
* `UlmerBialgebras.Paper.TwoFun.LaxNat`, `UlmerBialgebras.Paper.TwoFun.OplaxNat`,
  `UlmerBialgebras.Paper.TwoFun.LaxModif`, `UlmerBialgebras.Paper.TwoFun.OplaxModif`: lax and oplax
  transformations and their modifications (Example 3.12).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.4, 3.9, 3.12, Definition 3.10
-/

universe u v w ua va wa

namespace UlmerBialgebras.Paper.TwoFun

open CategoryTheory

variable (A : Type ua) [Bicategory.{wa, va} A] [Bicategory.Strict A]

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

/-- **Example 3.4** ([forsman2026syntactic]): the 2-signature `Σ_A` of a 2-category `A`. -/
@[reducible] def sigOf : TwoSig.{ua, max ua va, max ua va wa} where
  toFunSig := funSigOf A
  Tr := SigTr A
  trn := fun _ => 1
  trt := fun τ _ => τ.src
  trty := fun τ => τ.tgt
  trsrc := sigTrSrc A
  trtgt := sigTrTgt A

variable {A}
variable (K : Type u) [Bicategory.{w, v} K] [Bicategory.Strict K]

/-- A strict 2-functor `F : A → K`. -/
structure StrictTwoFunctor (A : Type ua) [Bicategory.{wa, va} A] [Bicategory.Strict A] where
  /-- The action on objects. -/
  obj : A → K
  /-- The action on 1-cells. -/
  map : ∀ {a b : A}, (a ⟶ b) → (obj a ⟶ obj b)
  /-- The action on 2-cells. -/
  map₂ : ∀ {a b : A} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g)
  map_id : ∀ a : A, map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g
  map₂_id : ∀ {a b : A} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)
  map₂_comp : ∀ {a b : A} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ
  map₂_whiskerLeft : ∀ {a b c : A} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
    map₂ (f ◁ η) = eqToHom (map_comp f g) ≫ (map f ◁ map₂ η) ≫ eqToHom (map_comp f h).symm
  map₂_whiskerRight : ∀ {a b c : A} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
    map₂ (η ▷ h) = eqToHom (map_comp f h) ≫ (map₂ η ▷ map h) ≫ eqToHom (map_comp g h).symm

variable {K}

namespace StrictTwoFunctor

variable [HasChosenFinProducts.{u, v, w} K] (F : StrictTwoFunctor K A)

/-- The interpretation of the category and functor symbols of `Σ_A` given by `F`:
`M_F(a) = F a` and `M_F(f) = F f` (precomposed with the unary product projection). -/
@[reducible] def preModel : PreModel (sigOf A) K where
  obj := F.obj
  fn := fun B => (HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj B.1)).π 0 ≫ F.map B.2.2

/-- The interpretation of the transformation symbols of `Σ_A` given by `F`. -/
def trCell : ∀ τ : SigTr A,
    F.preModel.interp (F.preModel.Pctx τ).π ((sigOf A).trsrc τ) ⟶
      F.preModel.interp (F.preModel.Pctx τ).π ((sigOf A).trtgt τ)
  | .cell η => _ ◁ (_ ◁ F.map₂ η)
  | .comp f g => eqToHom <|
      show F.preModel.interp (F.preModel.Pctx (.comp f g)).π ((sigOf A).trsrc (.comp f g)) =
        F.preModel.interp (F.preModel.Pctx (.comp f g)).π ((sigOf A).trtgt (.comp f g)) from
      (Product.lift_const_π_assoc _ _ 0 _).trans <|
      (whisker_eq _ (F.map_comp f g)).trans <| (Category.assoc _ _ _).symm.trans <|
      (eq_whisker (Product.lift_const_π_assoc _ _ 0 _).symm (F.map g)).trans
      (Product.lift_const_π_assoc _ _ 0 _).symm
  | .unit a => eqToHom <|
      show F.preModel.interp (F.preModel.Pctx (.unit a)).π ((sigOf A).trsrc (.unit a)) =
        F.preModel.interp (F.preModel.Pctx (.unit a)).π ((sigOf A).trtgt (.unit a)) from
      (Product.lift_const_π_assoc _ _ 0 _).trans <|
      (whisker_eq _ (F.map_id a)).trans (Category.comp_id _)

/-- **Example 3.9** ([forsman2026syntactic]): the `Σ_A`-model `M_F` induced by a strict 2-functor
`F : A → K`. -/
@[reducible] def model : Model (sigOf A) K where
  toPreModel := F.preModel
  tr := F.trCell

end StrictTwoFunctor

variable (F G : StrictTwoFunctor K A)

/-- A lax natural transformation `σ : F ⇒ G` between strict 2-functors, with naturality
2-cells `σ_f : G f ∘ σ_a ⇒ σ_b ∘ F f` (Example 3.12 of [forsman2026syntactic]). -/
structure LaxNat where
  /-- The component 1-cells. -/
  app : ∀ a : A, F.obj a ⟶ G.obj a
  /-- The naturality 2-cells. -/
  nat : ∀ {a b : A} (f : a ⟶ b), app a ≫ G.map f ⟶ F.map f ≫ app b
  /-- Naturality in 2-cells. -/
  nat_cell : ∀ {a b : A} {f g : a ⟶ b} (η : f ⟶ g),
    (app a ◁ G.map₂ η) ≫ nat g = nat f ≫ (F.map₂ η ▷ app b)
  /-- Compatibility with composition of 1-cells. -/
  nat_comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
    nat (f ≫ g) =
      eqToHom ((whisker_eq (app a) (G.map_comp f g)).trans (Category.assoc _ _ _).symm) ≫
        (nat f ▷ G.map g) ≫ eqToHom (Category.assoc _ _ _) ≫ (F.map f ◁ nat g) ≫
        eqToHom ((eq_whisker (F.map_comp f g) (app c)).trans (Category.assoc _ _ _)).symm
  /-- Compatibility with identity 1-cells. -/
  nat_id : ∀ a : A, nat (𝟙 a) =
    eqToHom (((whisker_eq (app a) (G.map_id a)).trans (Category.comp_id _)).trans
      ((eq_whisker (F.map_id a) (app a)).trans (Category.id_comp _)).symm)

/-- A lax transformation is *pseudo* if its naturality 2-cells are invertible. -/
def LaxNat.IsPseudo {F G : StrictTwoFunctor K A} (σ : LaxNat F G) : Prop :=
  ∀ {a b : A} (f : a ⟶ b), IsIso (σ.nat f)

/-- A lax transformation is *strict* (2-natural) if its naturality 2-cells are identities. -/
def LaxNat.IsStrict {F G : StrictTwoFunctor K A} (σ : LaxNat F G) : Prop :=
  ∀ {a b : A} (f : a ⟶ b), ∃ h : σ.app a ≫ G.map f = F.map f ≫ σ.app b,
    σ.nat f = eqToHom h

/-- A modification between lax natural transformations. -/
structure LaxModif {F G : StrictTwoFunctor K A} (σ τ : LaxNat F G) where
  /-- The component 2-cells. -/
  app : ∀ a : A, σ.app a ⟶ τ.app a
  /-- Compatibility with the naturality 2-cells. -/
  naturality : ∀ {a b : A} (f : a ⟶ b),
    (app a ▷ G.map f) ≫ τ.nat f = σ.nat f ≫ (F.map f ◁ app b)

/-- An oplax natural transformation `σ : F ⇒ G` between strict 2-functors, with naturality
2-cells `σ_f : σ_b ∘ F f ⇒ G f ∘ σ_a` (Example 3.12 of [forsman2026syntactic]). -/
structure OplaxNat where
  /-- The component 1-cells. -/
  app : ∀ a : A, F.obj a ⟶ G.obj a
  /-- The naturality 2-cells. -/
  nat : ∀ {a b : A} (f : a ⟶ b), F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality in 2-cells. -/
  nat_cell : ∀ {a b : A} {f g : a ⟶ b} (η : f ⟶ g),
    (F.map₂ η ▷ app b) ≫ nat g = nat f ≫ (app a ◁ G.map₂ η)
  /-- Compatibility with composition of 1-cells. -/
  nat_comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
    nat (f ≫ g) =
      eqToHom ((eq_whisker (F.map_comp f g) (app c)).trans (Category.assoc _ _ _)) ≫
        (F.map f ◁ nat g) ≫ eqToHom (Category.assoc _ _ _).symm ≫ (nat f ▷ G.map g) ≫
        eqToHom ((whisker_eq (app a) (G.map_comp f g)).trans (Category.assoc _ _ _).symm).symm
  /-- Compatibility with identity 1-cells. -/
  nat_id : ∀ a : A, nat (𝟙 a) =
    eqToHom (((eq_whisker (F.map_id a) (app a)).trans (Category.id_comp _)).trans
      ((whisker_eq (app a) (G.map_id a)).trans (Category.comp_id _)).symm)

/-- A modification between oplax natural transformations. -/
structure OplaxModif {F G : StrictTwoFunctor K A} (σ τ : OplaxNat F G) where
  /-- The component 2-cells. -/
  app : ∀ a : A, σ.app a ⟶ τ.app a
  /-- Compatibility with the naturality 2-cells. -/
  naturality : ∀ {a b : A} (f : a ⟶ b),
    (F.map f ◁ app b) ≫ τ.nat f = σ.nat f ≫ (app a ▷ G.map f)

end UlmerBialgebras.Paper.TwoFun
