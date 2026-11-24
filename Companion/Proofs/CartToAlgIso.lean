module

public import Companion.Statements.DefsAlgTranslations
public import UlmerBialgebras.Proofs.Sec5.CartSigCalc
public import UlmerBialgebras.Proofs.Sec5.AlgTheoryCart

/-!
# `Σ_Cart`-theories as equational theories (proofs)

For a cartesian monoidal category `B` (objects in `max s v w`, morphisms in `max s v`, above the
size `s`), a 1-signature `sg` relative to `Σ_Cart` and a `sg`-theory `T`, the models of the
equational theory `T' = toMSTheory T` in `B` form a category isomorphic, over `B^S`, to the
category `B^T` of Definition 3.14. This is the converse of
`MSLanguage.CartIso.modelCat_iso_cartThy`.

* `cmpT x t`: the object of a closed term `t` at a family `x` is the product of the `x` at the
  factors of `t` (`piOne`, `piZero` and `piAppend` for a variable, `I` and `□`).
* `msStruc z`: the structure of `z ∈ M^σ`, the operation `(B, j)` being the cell of `B` followed
  by the `j`-th projection.
* `tupHom x τ`: a tuple of terms read as a morphism between the objects of terms.
* `interpArr_eq`, `interpPath_eq`: an arrow or path of the term graph evaluates to the morphism
  of its tuple. The raw arrows `δ, p₁, p₂, !, □` are first moved to the derived forms of
  `UlmerBialgebras/Proofs/Sec5/CartSigCalc.lean`.
* `equifProp_iff`: `z` lies in `M^T` iff its structure is a model of `T'`.

## Main results

* `UlmerBialgebras.Paper.CartToAlg.modelCat_iso_thyCat`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 and Definition 3.14
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe s v w

namespace UlmerBialgebras.Paper.CartToAlg

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Cart

/-! ## Products over `Fin 1`, `Fin 0` and `Fin.append` -/

section Products

variable {B : Type*} [Category B]

/-- Moving the endpoints of a morphism along equalities of objects. -/
lemma eqToHom_conj {X X₁ X₂ Y Y₁ Y₂ : B} (p : X = X₁) (q : Y₁ = Y) (r : X = X₂) (r' : Y = Y₂)
    {M : X₁ ⟶ Y₁} {M' : X₂ ⟶ Y₂}
    (hM : M = eqToHom (p.symm.trans r) ≫ M' ≫ eqToHom (q.trans r').symm) :
    eqToHom p ≫ M ≫ eqToHom q = eqToHom r ≫ M' ≫ eqToHom r'.symm := by
  subst hM; simp

/-- Solving `eqToHom p ≫ M ≫ eqToHom q = L` for `M`. -/
lemma eq_conj_of {X X₁ Y Y₁ : B} (p : X = X₁) (q : Y₁ = Y) {M : X₁ ⟶ Y₁} {L : X ⟶ Y}
    (h : eqToHom p ≫ M ≫ eqToHom q = L) : M = eqToHom p.symm ≫ L ≫ eqToHom q.symm := by
  subst p q; simpa using h

variable [CartesianMonoidalCategory B]

/-- An object is its product over `Fin 1`. -/
noncomputable def piOne (X : B) : (∏ᶜ fun _ : Fin 1 => X) ≅ X where
  hom := Pi.π _ 0
  inv := Pi.lift fun _ => 𝟙 X
  hom_inv_id := Pi.hom_ext _ _ fun j => by fin_cases j; simp
  inv_hom_id := by simp

/-- The unit is the product over `Fin 0`. -/
noncomputable def piZero {X : Fin 0 → B} : 𝟙_ B ≅ ∏ᶜ X where
  hom := Pi.lift fun j => j.elim0
  inv := toUnit _
  hom_inv_id := toUnit_unique _ _
  inv_hom_id := Pi.hom_ext _ _ fun j => j.elim0

/-- The diagonal `lift (𝟙 X) (𝟙 X)` moved along an equality of objects `X = X'` is the diagonal of
`X'`. -/
lemma lift_conj {X X' : B} (e : X = X') (e' : X' ⊗ X' = X ⊗ X) :
    lift (𝟙 X) (𝟙 X) = eqToHom e ≫ lift (𝟙 X') (𝟙 X') ≫ eqToHom e' := by
  subst e; simp

/-- The first projection `fst X Y` moved along equalities of objects is the first projection of the
new objects. -/
lemma fst_conj {X Y X' Y' : B} (e₁ : X = X') (e₂ : Y = Y') (e : X ⊗ Y = X' ⊗ Y') (e' : X' = X) :
    fst X Y = eqToHom e ≫ fst X' Y' ≫ eqToHom e' := by
  subst e₁ e₂; simp

/-- The second projection `snd X Y` moved along equalities of objects is the second projection of
the new objects. -/
lemma snd_conj {X Y X' Y' : B} (e₁ : X = X') (e₂ : Y = Y') (e : X ⊗ Y = X' ⊗ Y') (e' : Y' = Y) :
    snd X Y = eqToHom e ≫ snd X' Y' ≫ eqToHom e' := by
  subst e₁ e₂; simp

/-- The morphism `toUnit X` moved along an equality of objects `X = X'` is `toUnit X'`. -/
lemma toUnit_conj {X X' : B} (e : X = X') (e' : 𝟙_ B = 𝟙_ B) :
    toUnit X = eqToHom e ≫ toUnit X' ≫ eqToHom e' :=
  toUnit_unique _ _

/-- Right whiskering commutes with moving a morphism along equalities of objects. -/
lemma whiskerRight_conj {X Y Z X' Y' Z' : B} (e₁ : X = X') (e₂ : Y = Y') (e₃ : Z = Z')
    (M : X' ⟶ Y') (e : X ⊗ Z = X' ⊗ Z') (e' : Y' ⊗ Z' = Y ⊗ Z) :
    (eqToHom e₁ ≫ M ≫ eqToHom e₂.symm) ▷ Z = eqToHom e ≫ (M ▷ Z') ≫ eqToHom e' := by
  subst e₁ e₂ e₃; simp

/-- Left whiskering commutes with moving a morphism along equalities of objects. -/
lemma whiskerLeft_conj {X Y Z X' Y' Z' : B} (e₁ : X = X') (e₂ : Y = Y') (e₃ : Z = Z')
    (M : X' ⟶ Y') (e : Z ⊗ X = Z' ⊗ X') (e' : Z' ⊗ Y' = Z ⊗ Y) :
    Z ◁ (eqToHom e₁ ≫ M ≫ eqToHom e₂.symm) = eqToHom e ≫ (Z' ◁ M) ≫ eqToHom e' := by
  subst e₁ e₂ e₃; simp

variable {S : Type*} (X : S → B) {m n : ℕ} (a : Fin m → S) (b : Fin n → S)

/-- The map `∏ᶜ (X ∘ a) ⊗ ∏ᶜ (X ∘ b) ⟶ ∏ᶜ (X ∘ Fin.append a b)`. -/
noncomputable def appendHom :
    (∏ᶜ fun i => X (a i)) ⊗ (∏ᶜ fun i => X (b i)) ⟶ ∏ᶜ fun k => X (Fin.append a b k) :=
  Pi.lift fun k => Fin.addCases
    (motive := fun k => (∏ᶜ fun i => X (a i)) ⊗ (∏ᶜ fun i => X (b i)) ⟶ X (Fin.append a b k))
    (fun i => fst _ _ ≫ Pi.π _ i ≫ eqToHom (congrArg X (Fin.append_left a b i)).symm)
    (fun i => snd _ _ ≫ Pi.π _ i ≫ eqToHom (congrArg X (Fin.append_right a b i)).symm) k

/-- The map `∏ᶜ (X ∘ Fin.append a b) ⟶ ∏ᶜ (X ∘ a) ⊗ ∏ᶜ (X ∘ b)`. -/
noncomputable def appendInv :
    (∏ᶜ fun k => X (Fin.append a b k)) ⟶ (∏ᶜ fun i => X (a i)) ⊗ (∏ᶜ fun i => X (b i)) :=
  lift (Pi.lift fun i => Pi.π _ (Fin.castAdd n i) ≫ eqToHom (congrArg X (Fin.append_left a b i)))
    (Pi.lift fun i => Pi.π _ (Fin.natAdd m i) ≫ eqToHom (congrArg X (Fin.append_right a b i)))

/-- The projection of `appendHom` at an index `Fin.castAdd n i` of the left block is the first
projection followed by the `i`-th projection. -/
@[reassoc]
lemma appendHom_π_left (i : Fin m) :
    appendHom X a b ≫ Pi.π _ (Fin.castAdd n i) =
      fst _ _ ≫ Pi.π _ i ≫ eqToHom (congrArg X (Fin.append_left a b i)).symm := by
  rw [appendHom, Pi.lift_comp_π, Fin.addCases_left]

/-- The projection of `appendHom` at an index `Fin.natAdd m i` of the right block is the second
projection followed by the `i`-th projection. -/
@[reassoc]
lemma appendHom_π_right (i : Fin n) :
    appendHom X a b ≫ Pi.π _ (Fin.natAdd m i) =
      snd _ _ ≫ Pi.π _ i ≫ eqToHom (congrArg X (Fin.append_right a b i)).symm := by
  rw [appendHom, Pi.lift_comp_π, Fin.addCases_right]

/-- `appendHom` is natural. -/
lemma map_appendHom {Y : S → B} (h : ∀ s, X s ⟶ Y s) :
    (Limits.Pi.map (fun i => h (a i)) ⊗ₘ Limits.Pi.map (fun i => h (b i))) ≫ appendHom Y a b =
      appendHom X a b ≫ Limits.Pi.map (fun k => h (Fin.append a b k)) := by
  refine Pi.hom_ext _ _ fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Category.assoc, appendHom_π_left, Category.assoc, Limits.Pi.map_π,
      appendHom_π_left_assoc, tensorHom_fst_assoc, Limits.Pi.map_π_assoc]
    congr 2
    rw [eqToHom_naturality _ (Fin.append_left a b i).symm]
  · rw [Category.assoc, appendHom_π_right, Category.assoc, Limits.Pi.map_π,
      appendHom_π_right_assoc, tensorHom_snd_assoc, Limits.Pi.map_π_assoc]
    congr 2
    rw [eqToHom_naturality _ (Fin.append_right a b i).symm]

/-- `∏ᶜ (X ∘ a) ⊗ ∏ᶜ (X ∘ b) ≅ ∏ᶜ (X ∘ Fin.append a b)`. -/
noncomputable def piAppend :
    (∏ᶜ fun i => X (a i)) ⊗ (∏ᶜ fun i => X (b i)) ≅ ∏ᶜ fun k => X (Fin.append a b k) where
  hom := appendHom X a b
  inv := appendInv X a b
  hom_inv_id := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine Pi.hom_ext _ _ fun i => ?_
      simp only [appendInv, Category.assoc, lift_fst, Pi.lift_comp_π, Category.id_comp]
      rw [← Category.assoc, appendHom_π_left]
      simp
    · refine Pi.hom_ext _ _ fun i => ?_
      simp only [appendInv, Category.assoc, lift_snd, Pi.lift_comp_π, Category.id_comp]
      rw [← Category.assoc, appendHom_π_right]
      simp
  inv_hom_id := by
    refine Pi.hom_ext _ _ fun k => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Category.assoc, appendHom_π_left, ← Category.assoc, ← Category.assoc, appendInv,
        lift_fst, Pi.lift_comp_π]
      simp
    · rw [Category.assoc, appendHom_π_right, ← Category.assoc, ← Category.assoc, appendInv,
        lift_snd, Pi.lift_comp_π]
      simp

/-- `appendHom` followed by `appendInv` is the identity. -/
@[reassoc (attr := simp)]
lemma appendHom_appendInv : appendHom X a b ≫ appendInv X a b = 𝟙 _ := (piAppend X a b).hom_inv_id

end Products

/-! ## Terms of `Σ_Cart` as products of their factors -/

section Cmp

open Cart.SigCalc

attribute [local instance] catOfSizeHom
attribute [local implicit_reducible] factors toMSLanguage

variable {B : Type (max s v w)} [Category.{max s v} B] [CartesianMonoidalCategory B]
  {sg : OneSig.{0, 0, 0, s, s} sigCart}

/-- The object of a closed term at a family `x` of objects (the evaluation `M(t)` of
Definition 3.13 at `x`). -/
abbrev tObj (x : sg.Srt → B) {c : Unit} (t : sg.CTrm c) : B :=
  ((cartModel B).tm sg t).toFunctor.obj x

/-- **The object of a closed term is the product of its factors.** -/
noncomputable def cmpT (x : sg.Srt → B) :
    ∀ {c : Unit} (t : sg.CTrm c), tObj x t ≅ ∏ᶜ fun i => x ((factors t).2 i)
  | _, .var y => (piOne (x y)).symm
  | _, .app CartFun.tens args =>
      tensorIso (cmpT x (args 0)) (cmpT x (args 1)) ≪≫ piAppend x _ _
  | _, .app CartFun.unit _ => piZero

/-- The family of objects of `z ∈ M^σ`. -/
abbrev base (z : SigObj B sg) : sg.Srt → B := Ins.pt z

/-- The object of a closed term at `z ∈ M^σ` is its object at the family of `z`. -/
lemma hzT (z : SigObj B sg) (t : sg.CTrm ()) : interpTerm z t = tObj (base z) t :=
  congr(($((cartModel B).sigTm_eq sg t)).toFunctor.obj z)

/-- The `σ'`-structure on the family of `z ∈ M^σ`: the operation `(B, j)` is the cell of `B`
followed by the `j`-th projection, between the products of factors. -/
@[implicit_reducible]
noncomputable def msStruc (z : SigObj B sg) : (toMSLanguage sg).Structure (C := B) (base z) where
  funMap f := (cmpT (base z) (sg.fndom f.1)).inv ≫ Ins.cell z f.1 ≫
    (cmpT (base z) (sg.fncod f.1)).hom ≫ Pi.π _ f.2

/-- The operation `(B, j)` of `msStruc z` is the cell of `B` between the products of factors,
followed by the `j`-th projection. -/
lemma msStruc_funMap (z : SigObj B sg) (f : (toMSLanguage sg).Functions) :
    (msStruc z).funMap f = (cmpT (base z) (sg.fndom f.1)).inv ≫ Ins.cell z f.1 ≫
      (cmpT (base z) (sg.fncod f.1)).hom ≫ Pi.π _ f.2 := rfl

/-- The morphism `M(t)(x) ⟶ M(t)(y)` induced by a family of morphisms. -/
abbrev tMap {x y : sg.Srt → B} (h : ∀ a, x a ⟶ y a) {c : Unit} (t : sg.CTrm c) :
    tObj x t ⟶ tObj y t :=
  ((cartModel B).tm sg t).toFunctor.map (X := x) (Y := y) h

/-- `cmpT` is natural. -/
lemma tMap_cmpT {x y : sg.Srt → B} (h : ∀ a, x a ⟶ y a) :
    ∀ {c : Unit} (t : sg.CTrm c),
      tMap h t ≫ (cmpT y t).hom = (cmpT x t).hom ≫ Limits.Pi.map (fun _ => h _)
  | _, .var a => Pi.hom_ext _ _ fun j =>
      (Category.assoc _ _ _).trans ((tMap h (.var a) ≫=
        (Pi.lift_comp_π (fun _ : Fin 1 => 𝟙 (y a)) j)).trans ((Category.comp_id _).trans
        ((Category.id_comp _).symm.trans ((((Pi.lift_comp_π (fun _ : Fin 1 => 𝟙 (x a)) j).symm =≫
          h a)).trans ((Category.assoc _ _ _).trans
          ((_ ≫= (Limits.Pi.map_π (fun i => h ((factors (.var a)).2 i)) j).symm).trans
            (Category.assoc _ _ _).symm))))))
  | _, .app CartFun.tens args => by
      exact (Category.assoc _ _ _).symm.trans <|
          ((tensorHom_comp_tensorHom _ _ _ _).trans
        (congr($(tMap_cmpT h (args 0)) ⊗ₘ $(tMap_cmpT h (args 1)))) =≫ appendHom y _ _).trans
        (((tensorHom_comp_tensorHom _ _ _ _).symm =≫ appendHom y _ _).trans
          ((Category.assoc _ _ _).trans ((_ ≫= map_appendHom x _ _ h).trans
            (Category.assoc _ _ _).symm)))
  | _, .app CartFun.unit _ => Pi.hom_ext _ _ fun j => j.elim0

/-- `cmpT⁻¹` is natural. -/
lemma cmpT_inv_tMap {x y : sg.Srt → B} (h : ∀ a, x a ⟶ y a) {c : Unit} (t : sg.CTrm c) :
    (cmpT x t).inv ≫ tMap h t = Limits.Pi.map (fun _ => h _) ≫ (cmpT y t).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← tMap_cmpT, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- A morphism of cells commuting with `tMap` gives, between products of factors, one commuting
with `Pi.map`. -/
lemma comm_aux {x y : sg.Srt → B} (h : ∀ a, x a ⟶ y a) {t₁ t₂ : sg.CTrm ()}
    (c : tObj x t₁ ⟶ tObj x t₂) (c' : tObj y t₁ ⟶ tObj y t₂)
    (hw : c ≫ tMap h t₂ = tMap h t₁ ≫ c') (j : Fin (factors t₂).1) :
    ((cmpT x t₁).inv ≫ c ≫ (cmpT x t₂).hom ≫ Pi.π _ j) ≫ h _ =
      Limits.Pi.map (fun i => h ((factors t₁).2 i)) ≫ (cmpT y t₁).inv ≫ c' ≫
        (cmpT y t₂).hom ≫ Pi.π _ j := by
  have e₁ : (cmpT x t₂).hom ≫ Pi.π _ j ≫ h ((factors t₂).2 j) =
      tMap h t₂ ≫ (cmpT y t₂).hom ≫ Pi.π _ j :=
    ((cmpT x t₂).hom ≫= (Limits.Pi.map_π (fun i => h ((factors t₂).2 i)) j).symm).trans
      ((Category.assoc _ _ _).symm.trans (((tMap_cmpT h t₂).symm =≫ Pi.π _ j).trans
        (Category.assoc _ _ _)))
  rw [Category.assoc, Category.assoc, Category.assoc, e₁, ← Category.assoc c, hw, Category.assoc,
    ← Category.assoc _ (tMap h t₁), cmpT_inv_tMap, Category.assoc]

/-! ## Tuples as morphisms -/

variable (x : sg.Srt → B) [(toMSLanguage sg).Structure x]

/-- **The morphism of a tuple** `τ : t → t'`: the tuple of the realizations of its terms, read
between the objects of `t` and `t'` along `cmpT`. -/
noncomputable def tupHom {c : Unit} {t t' : sg.CTrm c} (τ : Tuple t t') : tObj x t ⟶ tObj x t' :=
  (cmpT x t).hom ≫ Pi.lift (fun j => (τ j).realize x) ≫ (cmpT x t').inv

/-- A term moved along an equality of sorts realizes to the realization followed by `eqToHom`. -/
lemma realize_castSort {n : ℕ} {Γ : Fin n → sg.Srt} {a b : sg.Srt} (h : a = b)
    (u : (toMSLanguage sg).Term Γ a) :
    (castSort h u).realize x = u.realize x ≫ eqToHom (congrArg x h) := by
  subst h; exact (Category.comp_id _).symm

/-- The tuple of the variables realizes to the identity. -/
lemma lift_realize_var {n : ℕ} (Γ : Fin n → sg.Srt) :
    Pi.lift (fun i => ((MSLanguage.Term.var i : (toMSLanguage sg).Term Γ (Γ i))).realize x) =
      𝟙 _ :=
  Pi.hom_ext _ _ fun j => (Pi.lift_comp_π _ j).trans (Category.id_comp _).symm

/-- The identity tuple realizes to the identity. -/
lemma lift_realize_id {c : Unit} (t : sg.CTrm c) :
    Pi.lift (fun j => (Tuple.id t j).realize x) = 𝟙 _ :=
  Pi.hom_ext _ _ fun j => (Pi.lift_comp_π _ j).trans (Category.id_comp _).symm

/-- The morphism of the identity tuple is the identity. -/
lemma tupHom_id {c : Unit} (t : sg.CTrm c) : tupHom x (Tuple.id t) = 𝟙 _ := by
  rw [tupHom, lift_realize_id, Category.id_comp, Iso.hom_inv_id]

/-- The morphism of a composite of tuples is the composite of their morphisms. -/
lemma tupHom_comp {c : Unit} {t₁ t₂ t₃ : sg.CTrm c} (p : Tuple t₁ t₂) (q : Tuple t₂ t₃) :
    tupHom x (p.comp q) = tupHom x p ≫ tupHom x q := by
  have h : Pi.lift (fun j => ((p.comp q) j).realize x) =
      Pi.lift (fun j => (p j).realize x) ≫ Pi.lift (fun j => (q j).realize x) :=
    Pi.hom_ext _ _ fun j =>
        (Pi.lift_comp_π _ j).trans ((MSLanguage.Term.realize_subst x p (q j)).trans
      (_ ≫= (Pi.lift_comp_π (fun j => (q j).realize x) j).symm) |>.trans
          (Category.assoc _ _ _).symm)
  rw [tupHom, tupHom, tupHom, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {x} in
/-- The tuple of a pairing is the pair of the tuples followed by `appendHom`. -/
lemma lift_realize_pairTerms {k m n : ℕ} {Γ : Fin k → sg.Srt} {a : Fin m → sg.Srt}
    {b : Fin n → sg.Srt} (p : ∀ i, (toMSLanguage sg).Term Γ (a i))
    (q : ∀ i, (toMSLanguage sg).Term Γ (b i)) :
    Pi.lift (fun j => (pairTerms p q j).realize x) =
      lift (Pi.lift fun i => (p i).realize x) (Pi.lift fun i => (q i).realize x) ≫
        appendHom x a b := by
  refine Pi.hom_ext _ _ fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Pi.lift_comp_π, Category.assoc, appendHom_π_left, lift_fst_assoc, Pi.lift_comp_π_assoc,
      pairTerms, Fin.addCases_left, realize_castSort]
  · rw [Pi.lift_comp_π, Category.assoc, appendHom_π_right, lift_snd_assoc, Pi.lift_comp_π_assoc,
      pairTerms, Fin.addCases_right, realize_castSort]

/-- The tuple of left variables is `appendInv ≫ fst`. -/
lemma lift_realize_projL {m n : ℕ} (a : Fin m → sg.Srt) (b : Fin n → sg.Srt) :
    Pi.lift (fun i => (projL a b i).realize x) = appendInv x a b ≫ fst _ _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Pi.lift_comp_π, projL, realize_castSort, appendInv, lift_fst, Pi.lift_comp_π]
  rfl

/-- The tuple of right variables is `appendInv ≫ snd`. -/
lemma lift_realize_projR {m n : ℕ} (a : Fin m → sg.Srt) (b : Fin n → sg.Srt) :
    Pi.lift (fun i => (projR a b i).realize x) = appendInv x a b ≫ snd _ _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Pi.lift_comp_π, projR, realize_castSort, appendInv, lift_snd, Pi.lift_comp_π]
  rfl

/-- The tuple of a substitution instance is the composite of the tuples. -/
lemma lift_realize_subst {c : Unit} {t₁ t₂ : sg.CTrm c} {k : ℕ} {Γ : Fin k → sg.Srt}
    (σ : ∀ i, (toMSLanguage sg).Term Γ ((factors t₁).2 i)) (u : Tuple t₁ t₂) :
    Pi.lift (fun j => ((u j).subst σ).realize x) =
      Pi.lift (fun i => (σ i).realize x) ≫ Pi.lift (fun j => (u j).realize x) :=
  Pi.hom_ext _ _ fun j =>
      (Pi.lift_comp_π _ j).trans ((MSLanguage.Term.realize_subst x σ (u j)).trans
    (_ ≫= (Pi.lift_comp_π (fun j => (u j).realize x) j).symm) |>.trans
      (Category.assoc _ _ _).symm)

/-! ## The tuples of the arrows of `Σ_Cart` -/

/-- The morphism of the tuple of the diagonal arrow `δ` at `a` is the diagonal
`lift (𝟙 _) (𝟙 _)`. -/
lemma tupHom_diag (a : sg.CTrm ()) :
    (tupHom x (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.diag ![a])) :
      tObj x a ⟶ tObj x a ⊗ tObj x a) = lift (𝟙 _) (𝟙 _) := by
  change (cmpT x a).hom ≫ Pi.lift (fun j => (pairTerms (fun i => .var i) (fun i => .var i) j :
      (toMSLanguage sg).Term _ _).realize x) ≫
    (appendInv x _ _ ≫ ((cmpT x a).inv ⊗ₘ (cmpT x a).inv)) = lift (𝟙 (tObj x a)) (𝟙 (tObj x a))
  rw [lift_realize_pairTerms, lift_realize_var, Category.assoc, appendHom_appendInv_assoc, lift_map,
    comp_lift, Category.id_comp, Iso.hom_inv_id]

/-- The morphism of the tuple of the first projection arrow `p₁` at `a, b` is `fst`. -/
lemma tupHom_proj₁ (a b : sg.CTrm ()) :
    (tupHom x (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.proj₁ ![a, b])) :
      tObj x a ⊗ tObj x b ⟶ tObj x a) = fst _ _ := by
  change (((cmpT x a).hom ⊗ₘ (cmpT x b).hom) ≫ appendHom x _ _) ≫
    Pi.lift (fun i => (projL (factors a).2 (factors b).2 i).realize x) ≫ (cmpT x a).inv =
      fst (tObj x a) (tObj x b)
  rw [lift_realize_projL, Category.assoc, Category.assoc, appendHom_appendInv_assoc,
      tensorHom_fst_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The morphism of the tuple of the second projection arrow `p₂` at `a, b` is `snd`. -/
lemma tupHom_proj₂ (a b : sg.CTrm ()) :
    (tupHom x (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.proj₂ ![a, b])) :
      tObj x a ⊗ tObj x b ⟶ tObj x b) = snd _ _ := by
  change (((cmpT x a).hom ⊗ₘ (cmpT x b).hom) ≫ appendHom x _ _) ≫
    Pi.lift (fun i => (projR (factors a).2 (factors b).2 i).realize x) ≫ (cmpT x b).inv =
      snd (tObj x a) (tObj x b)
  rw [lift_realize_projR, Category.assoc, Category.assoc, appendHom_appendInv_assoc,
      tensorHom_snd_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The morphism of the tuple of the terminal arrow `!` at `a` is `toUnit`. -/
lemma tupHom_term (a : sg.CTrm ()) :
    (tupHom x (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.term ![a])) :
      tObj x a ⟶ 𝟙_ B) = toUnit _ :=
  toUnit_unique _ _

/-- The morphism of the tuple of the right whiskering of an arrow `g` by `b` is the right whiskering
of the morphism of `g` by the object of `b`. -/
lemma tupHom_whiskerRight {a a' : sg.CTrm ()} (b : sg.CTrm ()) (g : sg.Arr a a') :
    (tupHom x (arrTuple (whiskerRightArr b g)) : tObj x a ⊗ tObj x b ⟶ tObj x a' ⊗ tObj x b) =
      tupHom x (arrTuple g) ▷ tObj x b := by
  change (((cmpT x a).hom ⊗ₘ (cmpT x b).hom) ≫ appendHom x _ _) ≫
    Pi.lift (fun j => (pairTerms (fun j => (arrTuple g j).subst (projL _ _))
      (fun j => (Tuple.id b j).subst (projR _ _)) j).realize x) ≫
    (appendInv x _ _ ≫ ((cmpT x a').inv ⊗ₘ (cmpT x b).inv)) = _
  rw [lift_realize_pairTerms, lift_realize_subst, lift_realize_subst, lift_realize_projL,
    lift_realize_projR, lift_realize_id, Category.comp_id]
  simp only [Category.assoc, ← comp_lift, appendHom_appendInv_assoc]
  rw [tupHom]
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- The morphism of the tuple of the left whiskering of an arrow `g` by `a` is the left whiskering
of the morphism of `g` by the object of `a`. -/
lemma tupHom_whiskerLeft (a : sg.CTrm ()) {b b' : sg.CTrm ()} (g : sg.Arr b b') :
    (tupHom x (arrTuple (whiskerLeftArr a g)) : tObj x a ⊗ tObj x b ⟶ tObj x a ⊗ tObj x b') =
      tObj x a ◁ tupHom x (arrTuple g) := by
  change (((cmpT x a).hom ⊗ₘ (cmpT x b).hom) ≫ appendHom x _ _) ≫
    Pi.lift (fun j => (pairTerms (fun j => (Tuple.id a j).subst (projL _ _))
      (fun j => (arrTuple g j).subst (projR _ _)) j).realize x) ≫
    (appendInv x _ _ ≫ ((cmpT x a).inv ⊗ₘ (cmpT x b').inv)) = _
  rw [lift_realize_pairTerms, lift_realize_subst, lift_realize_subst, lift_realize_projL,
    lift_realize_projR, lift_realize_id, Category.comp_id]
  simp only [Category.assoc, ← comp_lift, appendHom_appendInv_assoc]
  rw [tupHom]
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- The tuple of a function symbol `B` is the tuple of the operations `(B, j)`. -/
lemma tupHom_fn (f : sg.Fn) :
    tupHom x (arrTuple (OneSig.Arr.fn (sg := sg) f)) =
      (cmpT x (sg.fndom f)).hom ≫
        Pi.lift (fun j => MSLanguage.funMap (L := toMSLanguage sg) (M := x) ⟨f, j⟩) ≫
          (cmpT x (sg.fncod f)).inv := by
  refine (_ ≫= (congrArg Pi.lift (funext fun j => ?_)) =≫ _)
  exact (lift_realize_var x _ =≫ _).trans (Category.id_comp _)

/-- At `z ∈ M^σ` with its structure `msStruc z`, the tuple of a function symbol is its cell. -/
lemma tupHom_fn_msStruc (z : SigObj B sg) (f : sg.Fn) :
    @tupHom _ _ _ _ (base z) (msStruc z) _ _ _ (arrTuple (OneSig.Arr.fn (sg := sg) f)) =
      Ins.cell z f := by
  let := msStruc z
  have h : Pi.lift (fun j => MSLanguage.funMap (L := toMSLanguage sg) (M := base z) ⟨f, j⟩) =
      (cmpT (base z) (sg.fndom f)).inv ≫ Ins.cell z f ≫ (cmpT (base z) (sg.fncod f)).hom :=
    Pi.hom_ext _ _ fun j => (Pi.lift_comp_π _ j).trans
      ((Category.assoc _ _ _).trans (_ ≫= Category.assoc _ _ _)).symm
  exact (tupHom_fn (base z) f).trans (((_ ≫= h =≫ _)).trans
    ((_ ≫= Category.assoc _ _ _).trans ((Iso.hom_inv_id_assoc _ _).trans
      ((Category.assoc _ _ _).trans ((_ ≫= Iso.hom_inv_id _).trans
        (Category.comp_id _))))))

/-! ## The evaluation of arrows and paths -/

attribute [local instance] msStruc

/-- The evaluation of the arrow of a function symbol at `z ∈ M^σ` is its tuple morphism, up to
`hzT`. -/
lemma interpArr_fn' (z : SigObj B sg) (f : sg.Fn) :
    interpArr ((cartModel B).arrCell sg (OneSig.Arr.fn (sg := sg) f)) z =
      eqToHom (hzT z (sg.fndom f)) ≫ tupHom (base z) (arrTuple (OneSig.Arr.fn (sg := sg) f)) ≫
        eqToHom (hzT z (sg.fncod f)).symm := by
  rw [tupHom_fn_msStruc, Model.arrCell_fn]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app]
  rfl

/-- The evaluation of the diagonal arrow `δ` at `z ∈ M^σ` is its tuple morphism, up to `hzT`. -/
lemma interpArr_eq_diag (z : SigObj B sg) (a : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (OneSig.Arr.tr (sg := sg) CartTr.diag ![a])) z =
      eqToHom (hzT z a) ≫ tupHom (base z) (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.diag ![a])) ≫
        eqToHom (hzT z (tensTerm a a)).symm := by
  have h := interpArr_diagArr z a
  rw [diagArr, arrCell_transport] at h
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app] at h
  refine (eq_conj_of _ _ h).trans (eqToHom_conj _ _ (hzT z a) (hzT z (tensTerm a a)) ?_)
  exact (lift_conj (hzT z a) (hzT z (tensTerm a a)).symm).trans
    ((eqToHom (hzT z a) ≫= (tupHom_diag (base z) a).symm =≫ eqToHom (hzT z (tensTerm a a)).symm))

/-- The evaluation of the first projection arrow `p₁` at `z ∈ M^σ` is its tuple morphism, up to
`hzT`. -/
lemma interpArr_eq_proj₁ (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (OneSig.Arr.tr (sg := sg) CartTr.proj₁ ![a, b])) z =
      eqToHom (hzT z ((sigCart.trsrc CartTr.proj₁).subst ![a, b])) ≫
        tupHom (base z) (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.proj₁ ![a, b])) ≫
          eqToHom (hzT z a).symm := by
  have h := interpArr_fstArr z a b
  rw [fstArr, arrCell_transport] at h
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app] at h
  refine (eq_conj_of _ _ h).trans (eqToHom_conj _ _ (hzT z (tensTerm a b)) (hzT z a) ?_)
  exact (fst_conj (hzT z a) (hzT z b) (hzT z (tensTerm a b)) (hzT z a).symm).trans
    ((eqToHom (hzT z (tensTerm a b)) ≫= (tupHom_proj₁ (base z) a b).symm =≫ eqToHom (hzT z a).symm))

/-- The evaluation of the second projection arrow `p₂` at `z ∈ M^σ` is its tuple morphism, up to
`hzT`. -/
lemma interpArr_eq_proj₂ (z : SigObj B sg) (a b : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (OneSig.Arr.tr (sg := sg) CartTr.proj₂ ![a, b])) z =
      eqToHom (hzT z ((sigCart.trsrc CartTr.proj₂).subst ![a, b])) ≫
        tupHom (base z) (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.proj₂ ![a, b])) ≫
          eqToHom (hzT z b).symm := by
  have h := interpArr_sndArr z a b
  rw [sndArr, arrCell_transport] at h
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app] at h
  refine (eq_conj_of _ _ h).trans (eqToHom_conj _ _ (hzT z (tensTerm a b)) (hzT z b) ?_)
  exact (snd_conj (hzT z a) (hzT z b) (hzT z (tensTerm a b)) (hzT z b).symm).trans
    ((eqToHom (hzT z (tensTerm a b)) ≫= (tupHom_proj₂ (base z) a b).symm =≫ eqToHom (hzT z b).symm))

/-- The evaluation of the terminal arrow `!` at `z ∈ M^σ` is its tuple morphism, up to `hzT`. -/
lemma interpArr_eq_term (z : SigObj B sg) (a : sg.CTrm ()) :
    interpArr ((cartModel B).arrCell sg (OneSig.Arr.tr (sg := sg) CartTr.term ![a])) z =
      eqToHom (hzT z a) ≫ tupHom (base z) (arrTuple (OneSig.Arr.tr (sg := sg) CartTr.term ![a])) ≫
        eqToHom (hzT z unitTerm).symm := by
  have h := interpArr_toUnitArr z a
  rw [toUnitArr, arrCell_transport] at h
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app] at h
  refine (eq_conj_of _ _ h).trans (eqToHom_conj _ _ (hzT z a) (hzT z unitTerm) ?_)
  exact (toUnit_conj (hzT z a) (hzT z unitTerm).symm).trans
    ((eqToHom (hzT z a) ≫= (tupHom_term (base z) a).symm =≫ eqToHom (hzT z unitTerm).symm))

/-- If the evaluation of an arrow `g` is its tuple morphism up to `hzT`, then so is the evaluation
of its right whiskering by `b`. -/
lemma interpArr_eq_whiskerRight (z : SigObj B sg) {a a' : sg.CTrm ()} (b : sg.CTrm ())
    (g : sg.Arr a a')
    (ih : interpArr ((cartModel B).arrCell sg g) z =
      eqToHom (hzT z a) ≫ tupHom (base z) (arrTuple g) ≫ eqToHom (hzT z a').symm) :
    interpArr ((cartModel B).arrCell sg (whiskerRightArr b g)) z =
      eqToHom (hzT z (tensTerm a b)) ≫ tupHom (base z) (arrTuple (whiskerRightArr b g)) ≫
        eqToHom (hzT z (tensTerm a' b)).symm := by
  rw [interpArr_whiskerRightArr, ih]
  exact ((whiskerRight_conj (hzT z a) (hzT z a') (hzT z b) _ (hzT z (tensTerm a b))
      (hzT z (tensTerm a' b)).symm).trans
      ((eqToHom (hzT z (tensTerm a b)) ≫= (tupHom_whiskerRight (base z) b g).symm =≫
        eqToHom (hzT z (tensTerm a' b)).symm)))

/-- If the evaluation of an arrow `g` is its tuple morphism up to `hzT`, then so is the evaluation
of its left whiskering by `a`. -/
lemma interpArr_eq_whiskerLeft (z : SigObj B sg) (a : sg.CTrm ()) {b b' : sg.CTrm ()}
    (g : sg.Arr b b')
    (ih : interpArr ((cartModel B).arrCell sg g) z =
      eqToHom (hzT z b) ≫ tupHom (base z) (arrTuple g) ≫ eqToHom (hzT z b').symm) :
    interpArr ((cartModel B).arrCell sg (whiskerLeftArr a g)) z =
      eqToHom (hzT z (tensTerm a b)) ≫ tupHom (base z) (arrTuple (whiskerLeftArr a g)) ≫
        eqToHom (hzT z (tensTerm a b')).symm := by
  rw [interpArr_whiskerLeftArr, ih]
  exact ((whiskerLeft_conj (hzT z b) (hzT z b') (hzT z a) _ (hzT z (tensTerm a b))
      (hzT z (tensTerm a b')).symm).trans
      ((eqToHom (hzT z (tensTerm a b)) ≫= (tupHom_whiskerLeft (base z) a g).symm =≫
        eqToHom (hzT z (tensTerm a b')).symm)))

/-- **The evaluation of an arrow is its tuple**, up to `hzT` (`interpArr_eq`). -/
lemma interpArr_eq (z : SigObj B sg) : ∀ {t t' : sg.CTrm ()} (g : sg.Arr t t'),
    interpArr ((cartModel B).arrCell sg g) z =
      eqToHom (hzT z t) ≫ tupHom (base z) (arrTuple g) ≫ eqToHom (hzT z t').symm
  | _, _, .fn f => interpArr_fn' z f
  | _, _, .tr CartTr.diag sub => by
      obtain ⟨a, rfl⟩ : ∃ a, sub = ![a] := ⟨sub 0, funext fun i => by fin_cases i; rfl⟩
      exact interpArr_eq_diag z a
  | _, _, .tr CartTr.proj₁ sub => by
      obtain ⟨a, b, rfl⟩ : ∃ a b, sub = ![a, b] :=
        ⟨sub 0, sub 1, funext fun i => by fin_cases i <;> rfl⟩
      exact interpArr_eq_proj₁ z a b
  | _, _, .tr CartTr.proj₂ sub => by
      obtain ⟨a, b, rfl⟩ : ∃ a b, sub = ![a, b] :=
        ⟨sub 0, sub 1, funext fun i => by fin_cases i <;> rfl⟩
      exact interpArr_eq_proj₂ z a b
  | _, _, .tr CartTr.term sub => by
      obtain ⟨a, rfl⟩ : ∃ a, sub = ![a] := ⟨sub 0, funext fun i => by fin_cases i; rfl⟩
      exact interpArr_eq_term z a
  | _, _, .app CartFun.tens ⟨0, _⟩ args args' hne g => by
      have ih := interpArr_eq z g
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = ![a, b] :=
        ⟨args 0, args 1, funext fun i => by fin_cases i <;> rfl⟩
      obtain ⟨a', b', rfl⟩ : ∃ a b, args' = ![a, b] :=
        ⟨args' 0, args' 1, funext fun i => by fin_cases i <;> rfl⟩
      obtain rfl : b = b' := hne 1 (Fin.ne_of_val_ne Nat.one_ne_zero)
      exact interpArr_eq_whiskerRight z b g ih
  | _, _, .app CartFun.tens ⟨1, _⟩ args args' hne g => by
      have ih := interpArr_eq z g
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = ![a, b] :=
        ⟨args 0, args 1, funext fun i => by fin_cases i <;> rfl⟩
      obtain ⟨a', b', rfl⟩ : ∃ a b, args' = ![a, b] :=
        ⟨args' 0, args' 1, funext fun i => by fin_cases i <;> rfl⟩
      obtain rfl : a = a' := hne 0 (Fin.ne_of_val_ne Nat.zero_ne_one)
      exact interpArr_eq_whiskerLeft z a g ih
  | _, _, .app CartFun.unit i _ _ _ _ => i.elim0

/-- **The evaluation of a path is its tuple**, up to `hzT`. -/
lemma interpPath_eq (z : SigObj B sg) : ∀ {t t' : sg.CTrm ()} (p : sg.Path t t'),
    interpPath p z =
      eqToHom (hzT z t) ≫ tupHom (base z) (pathTuple p) ≫ eqToHom (hzT z t').symm
  | _, _, .nil t => by
      rw [interpPath_nil, pathTuple, tupHom_id]
      simp
  | _, _, .cons g p => by
      rw [interpPath_cons, interpArr_eq, interpPath_eq z p, pathTuple, tupHom_comp]
      simp

variable {x} in
/-- Two tuples have the same morphism iff their terms have the same realizations. -/
lemma tupHom_eq_iff {c : Unit} {t t' : sg.CTrm c} (τ σ : Tuple t t') :
    tupHom x τ = tupHom x σ ↔ ∀ j, (τ j).realize x = (σ j).realize x := by
  refine ⟨fun h j => ?_, fun h => ?_⟩
  · have h' : Pi.lift (fun j => (τ j).realize x) = Pi.lift (fun j => (σ j).realize x) := by
      have := ((cmpT x t).inv ≫= h =≫ (cmpT x t').hom)
      simpa [tupHom] using this
    simpa using (h' =≫ Pi.π _ j)
  · rw [tupHom, tupHom, funext h]

/-! ## The defining condition of `C^T` -/

variable {T : Theory.{0, 0, 0, s, s, s} sg}

/-- The component at `z` and `r` of the left-hand cell of `M^T` evaluates the left path of
`r`. -/
lemma lhsCell_app (z : SigObj B sg) (r : T.Eqn) :
    ((cartModel B).lhsCell sg T).toNatTrans.app z r = interpPath (T.lhs r) z := by
  rw [Model.lhsCell]
  simp only [catOfSize_lift₂_app, Cat.Hom.comp_toFunctor, Cat.Hom.toNatTrans_comp,
      Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The component at `z` and `r` of the right-hand cell of `M^T` evaluates the right path of
`r`. -/
lemma rhsCell_app (z : SigObj B sg) (r : T.Eqn) :
    ((cartModel B).rhsCell sg T).toNatTrans.app z r = interpPath (T.rhs r) z := by
  rw [Model.rhsCell]
  simp only [catOfSize_lift₂_app, Cat.Hom.comp_toFunctor, Cat.Hom.toNatTrans_comp,
      Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **The defining condition of `M^T`**: `z ∈ M^σ` lies in `M^T` iff its structure is a model of
`T' = toMSTheory T`. -/
lemma equifProp_iff (z : SigObj B sg) :
    ((cartModel B).lhsCell sg T).toNatTrans.app z =
        ((cartModel B).rhsCell sg T).toNatTrans.app z ↔
      MSLanguage.Theory.Model (base z) (toMSTheory T) := by
  have key : ∀ r : T.Eqn, ((cartModel B).lhsCell sg T).toNatTrans.app z r =
      ((cartModel B).rhsCell sg T).toNatTrans.app z r ↔
        ∀ j, (pathTuple (T.lhs r) j).realize (base z) =
            (pathTuple (T.rhs r) j).realize (base z) := by
    intro r
    rw [lhsCell_app, rhsCell_app, interpPath_eq, interpPath_eq, ← tupHom_eq_iff]
    constructor
    · intro h
      simpa using (eqToHom (hzT z _).symm ≫= h =≫ eqToHom (hzT z _))
    · intro h; rw [h]
  refine funext_iff.trans ⟨fun h => ⟨?_⟩, fun h r => (key r).2 fun j => ?_⟩
  · rintro _ ⟨⟨r, j⟩, rfl⟩
    exact (key r).1 (h r) j
  · exact h.realize_of_mem _ ⟨⟨r, j⟩, rfl⟩

/-! ## The isomorphism -/

/-- The structure of the `σ`-object with the cells `tupHom` of the function symbols is the given
structure. -/
lemma msStruc_mk (y : sg.Srt → B) (S : (toMSLanguage sg).Structure y) :
    msStruc (⟨y, fun f => @tupHom _ _ _ _ y S _ _ _ (arrTuple (OneSig.Arr.fn (sg := sg) f))⟩ :
      SigObj B sg) = S := by
  obtain ⟨g⟩ := S
  refine congrArg MSLanguage.Structure.mk (funext fun ⟨f, j⟩ => ?_)
  let : (toMSLanguage sg).Structure y := ⟨g⟩
  change (cmpT y _).inv ≫ tupHom y _ ≫ (cmpT y _).hom ≫ Pi.π _ j = g ⟨f, j⟩
  rw [tupHom_fn]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  exact Pi.lift_comp_π _ j

/-- Homomorphisms commute with the morphisms of tuples. -/
lemma tupHom_natural {y y' : sg.Srt → B} [(toMSLanguage sg).Structure y]
    [(toMSLanguage sg).Structure y'] (g : (toMSLanguage sg).Hom y y') {c : Unit}
    {t t' : sg.CTrm c} (τ : Tuple t t') :
    tupHom y τ ≫ tMap g.toFun t' = tMap g.toFun t ≫ tupHom y' τ := by
  have h₁ := cmpT_inv_tMap g.toFun t'
  have h₂ : Pi.lift (fun j => (τ j).realize y) ≫ Limits.Pi.map (fun _ => g.toFun _) =
      Limits.Pi.map (fun _ => g.toFun _) ≫ Pi.lift (fun j => (τ j).realize y') :=
    Pi.hom_ext _ _ fun j => by
      rw [Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc, Category.assoc, Pi.lift_comp_π,
        MSLanguage.LangMorphism.realize_comp_hom]
  rw [tupHom, tupHom, Category.assoc, Category.assoc, h₁, ← Category.assoc _ (Limits.Pi.map _),
    h₂, ← Category.assoc, ← Category.assoc, ← tMap_cmpT, Category.assoc, Category.assoc]

variable (B T)

/-- The `T`-model of a model of `T'`: the family with the cells `tupHom` of the function
symbols. -/
noncomputable def toCartObj (A : (toMSTheory T).ModelCat B) : thyCat B sg T where
  obj := ⟨A.Carrier, fun f => tupHom A.Carrier (arrTuple (OneSig.Arr.fn (sg := sg) f))⟩
  property := (equifProp_iff _).2 ((congrArg
    (fun S => @MSLanguage.Theory.Model _ B _ _ A.Carrier S (toMSTheory T))
    (msStruc_mk A.Carrier A.struc)).mpr A.is_model)

/-- **From models of `T'` to models of `T`.** -/
noncomputable def toCart : (toMSTheory T).ModelCat B ⥤ thyCat B sg T where
  obj := toCartObj B T
  map g := ObjectProperty.homMk
    { base := fun a => g.toFun a
      w := funext fun _ => tupHom_natural g _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **From models of `T` to models of `T'`.** -/
noncomputable def ofCart : thyCat B sg T ⥤ (toMSTheory T).ModelCat B where
  obj t := @MSLanguage.Theory.ModelCat.mk _ B _ _ _ (base t.obj) (msStruc t.obj)
    ((equifProp_iff t.obj).1 t.property)
  map {t t'} g :=
    { toFun := fun a => g.hom.base a
      map_fun' := fun ⟨f, j⟩ => by
        have hw : Ins.cell t.obj f ≫ tMap (fun a => g.hom.base a) (sg.fncod f) =
            tMap (fun a => g.hom.base a) (sg.fndom f) ≫ Ins.cell t'.obj f :=
          congr($(g.hom.w) f)
        exact comm_aux (x := base t.obj) (y := base t'.obj) (t₁ := sg.fndom f) (t₂ := sg.fncod f)
          (fun a => g.hom.base a) (Ins.cell t.obj f) (Ins.cell t'.obj f) hw j }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ofCart` is a left inverse of `toCart`. -/
lemma toCart_ofCart : toCart B T ⋙ ofCart B T = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) (fun A A' g => ?_)
  · obtain @⟨M, S, hM⟩ := A
    exact MSLanguage.modelCat_eq _ _
      (fun f => congrArg (fun S' => @MSLanguage.funMap _ _ _ _ _ S' f) (msStruc_mk M S))
  · refine MSLanguage.Hom.ext (funext fun a => ?_)
    rw [MSLanguage.comp_toFun, MSLanguage.comp_toFun]
    refine Eq.trans ?_ (congr($((MSLanguage.eqToHom_toFun _ a).symm) ≫
      $(_ ≫= (MSLanguage.eqToHom_toFun _ a).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- `ofCart` is a right inverse of `toCart`. -/
lemma ofCart_toCart : ofCart B T ⋙ toCart B T = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun t t' g => ?_)
  · obtain ⟨⟨x, c⟩, hp⟩ := t
    refine ObjectProperty.FullSubcategory.ext (Ins.obj_ext rfl ?_)
    exact (funext fun f => tupHom_fn_msStruc ⟨x, c⟩ f).trans
      ((Category.id_comp _).trans (Category.comp_id _)).symm
  · obtain ⟨⟨x, c⟩, hp⟩ := t
    obtain ⟨⟨x', c'⟩, hp'⟩ := t'
    refine ObjectProperty.hom_ext _ (Ins.hom_ext ?_)
    refine Eq.trans ?_ (congr($((MSLanguage.CartIso.fullSubcategory_eqToHom_hom_base _).symm) ≫
      $(_ ≫= (MSLanguage.CartIso.fullSubcategory_eqToHom_hom_base _).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- `toCart` lies over the forgetful functors to `B^S`. -/
lemma toCart_forget :
    toCart B T ⋙ thyCatForget B sg T = MSLanguage.Theory.ModelCat.forget B (toMSTheory T) :=
  CategoryTheory.Functor.ext (fun _ => rfl)
    (fun _ _ _ => ((Category.id_comp _).trans (Category.comp_id _)).symm)

/-- **Models of `T'` in `B` are the `T`-models in the `Σ_Cart`-model `B`**, over `B^S`. -/
theorem modelCat_iso_thyCat :
    ∃ (F : (toMSTheory T).ModelCat B ⥤ thyCat B sg T)
        (G : thyCat B sg T ⥤ (toMSTheory T).ModelCat B),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ thyCatForget B sg T = MSLanguage.Theory.ModelCat.forget B (toMSTheory T) :=
  ⟨toCart B T, ofCart B T, toCart_ofCart B T, ofCart_toCart B T, toCart_forget B T⟩

end Cmp

end UlmerBialgebras.Paper.CartToAlg
