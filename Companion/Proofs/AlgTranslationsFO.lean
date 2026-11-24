module

public import Companion.Statements.DefsAlgTranslations
public import Mathlib.ModelTheory.Semantics
public import Companion.Proofs.ExtrasTheoryMorphism

/-!
# Single-sorted equational theories as first-order theories (proofs)

Helpers for `modelCat_type_iso_foModelCat` in `Companion/Proofs/ExtrasAlgTranslations.lean`. For a
language with one sort (`Unique L.Sorts`), a model in `Type u` is a family of types indexed by the
one sort; its value at the sort carries the Mathlib structure of `toFOLanguage L`. Sorts other
than `default` are reached by the casts `tr`.

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapter 1
-/

@[expose] public section

universe u u₄ u₅

namespace UlmerBialgebras.Paper.AlgFO

open CategoryTheory Limits MSLanguage FirstOrder

variable {L : MSLanguage.{u₄, u₅}}

section Terms

/-- A function symbol of `L` as a function symbol of `toFOLanguage L`. -/
def fsym (f : L.Functions) : (toFOLanguage L).Functions (L.arity f) := ⟨f, rfl⟩

/-- The first-order form of a variable is the variable `Sum.inr i`. -/
lemma toFO_var {n : ℕ} {Γ : Fin n → L.Sorts} (i : Fin n) :
    (Term.var (L := L) (Γ := Γ) i).toFO = .var (Sum.inr i) := rfl

/-- The first-order form of an application is the application of the first-order symbol to the
first-order forms of the arguments. -/
lemma toFO_func {n : ℕ} {Γ : Fin n → L.Sorts} (f : L.Functions)
    (ts : ∀ i, L.Term Γ (L.argSorts f i)) :
    (Term.func f ts).toFO = .func (fsym f) (fun i => (ts i).toFO) := rfl

end Terms

section Basic

variable [Unique L.Sorts]

/-- Every sort is the sort `default`. -/
lemma hd (s : L.Sorts) : s = default := Subsingleton.elim _ _

/-- A family at a sort is the family at `default`. -/
def tr (M : L.Sorts → Type u) (s : L.Sorts) : M s ≃ M default :=
  Equiv.cast (congrArg M (hd s))

/-- The tuple in `∏ᶜ` with given components. -/
noncomputable def tup {n : ℕ} (F : Fin n → Type u) (x : ∀ i, F i) : ∏ᶜ F :=
  (Types.productIso.{0, u} F).inv x

/-- The components of `tup F x` are the `x i`. -/
lemma π_tup {n : ℕ} (F : Fin n → Type u) (x : ∀ i, F i) (i : Fin n) :
    Pi.π F i (tup F x) = x i :=
  ConcreteCategory.congr_hom (Types.productIso_inv_comp_π F i) x

/-- The tuple of the values at `y` of a family of maps is the value at `y` of their `Pi.lift`. -/
lemma tup_lift {Y : Type u} {n : ℕ} (F : Fin n → Type u) (g : ∀ i, Y ⟶ F i) (y : Y) :
    tup F (fun i => g i y) = Pi.lift g y := by
  have h1 : (Types.productIso.{0, u} F).hom (tup F (fun i => g i y)) = fun i => g i y :=
    Iso.inv_hom_id_apply _ _
  have h2 : (Types.productIso.{0, u} F).hom (Pi.lift g y) = fun i => g i y :=
    funext fun i => ConcreteCategory.congr_hom (Pi.lift_comp_π g i) y
  exact (Types.productIso.{0, u} F).toEquiv.injective (h1.trans h2.symm)

/-! ## Models to first-order structures -/

end Basic

section ToFO

variable [Unique L.Sorts]

variable (M : L.Sorts → Type u) [L.Structure (C := Type u) M]

/-- The Mathlib structure of `toFOLanguage L` on the value at `default` of a model. -/
@[implicit_reducible]
noncomputable def foStructure : (toFOLanguage L).Structure (M default) where
  funMap f x := tr M _ (funMap (M := M) f.1
    (tup _ fun i => (tr M _).symm (x (Fin.cast f.2 i))))
  RelMap r := Empty.elim r

attribute [local instance] foStructure

/-- The function symbols of `foStructure M` are those of `M`, read through `tr M` and `tup`. -/
lemma foStructure_funMap {n : ℕ} (f : (toFOLanguage L).Functions n) (x : Fin n → M default) :
    FirstOrder.Language.Structure.funMap f x =
      tr M _ (funMap (M := M) f.1 (tup _ fun i => (tr M _).symm (x (Fin.cast f.2 i)))) := rfl

/-- The first-order realization of a term at `xs` is the realization of the term at the tuple of
`xs`, moved to `default`. -/
lemma realize_toFO {n : ℕ} {Γ : Fin n → L.Sorts} (xs : Fin n → M default) :
    ∀ {s : L.Sorts} (t : L.Term Γ s),
      t.toFO.realize (Sum.elim Empty.elim xs) =
        tr M s (t.realize M (tup _ fun i => (tr M _).symm (xs i)))
  | _, .var i => by
    rw [toFO_var, Language.Term.realize_var, Sum.elim_inr, MSLanguage.Term.realize_var, π_tup,
      Equiv.apply_symm_apply]
  | _, .func f ts => by
    rw [toFO_func, Language.Term.realize_func, foStructure_funMap, MSLanguage.Term.realize_func,
      types_comp_apply]
    congr 2
    rw [← tup_lift]
    congr 1
    funext i
    exact congr((tr M _).symm $(realize_toFO xs (ts i))).trans (Equiv.symm_apply_apply _ _)

/-- A model of `T` is a Mathlib model of `T.toFO`. -/
lemma foStructure_model {T : L.Theory} [M ⊨ T] : (M default) ⊨ T.toFO := by
  refine ⟨fun ψ hψ => ?_⟩
  obtain ⟨φ, hφ, rfl⟩ := hψ
  simp only [Equation.toFOSentence, Language.Sentence.Realize,
    Language.BoundedFormula.realize_alls, Language.BoundedFormula.realize_bdEqual]
  intro xs
  have : (default : Empty → M default) = Empty.elim := funext fun e => e.elim
  rw [this, realize_toFO, realize_toFO]
  rw [ConcreteCategory.congr_hom (Theory.Model.realize_of_mem (M := M) φ hφ) _]

end ToFO

/-! ## First-order structures to models -/

section OfFO

variable (N : Type u) [(toFOLanguage L).Structure N]

/-- An `L`-structure on the constant family at a Mathlib `toFOLanguage L`-structure. -/
@[implicit_reducible]
noncomputable def msStructure : L.Structure (C := Type u) fun _ : L.Sorts => N where
  funMap f := TypeCat.ofHom fun p => Language.Structure.funMap
    (L := toFOLanguage L) (fsym f)
    ((Types.productIso.{0, u} _).hom p)

attribute [local instance] msStructure

/-- Realizing a term in the constant family is realizing its first-order form. -/
lemma realize_msStructure {n : ℕ} {Γ : Fin n → L.Sorts}
    (p : ∏ᶜ fun i => (fun _ : L.Sorts => N) (Γ i)) :
    ∀ {s : L.Sorts} (t : L.Term Γ s),
      t.realize (fun _ : L.Sorts => N) p =
        t.toFO.realize (Sum.elim Empty.elim ((Types.productIso.{0, u} _).hom p))
  | _, .var _ => rfl
  | _, .func f ts => by
    rw [Term.realize, types_comp_apply]
    exact congrArg (Language.Structure.funMap (L := toFOLanguage L)
      (fsym f)) (funext fun i =>
        (ConcreteCategory.congr_hom
          (Pi.lift_comp_π (fun j => (ts j).realize (fun _ : L.Sorts => N)) i) p).trans
          (realize_msStructure p (ts i)))

/-- A Mathlib model of `T.toFO` is a model of `T`. -/
lemma msStructure_model {T : L.Theory} [N ⊨ T.toFO] : (fun _ : L.Sorts => N) ⊨ T := by
  refine ⟨fun φ hφ => ConcreteCategory.hom_ext _ _ fun p => ?_⟩
  rw [realize_msStructure, realize_msStructure]
  have h := Language.Theory.realize_sentence_of_mem (M := N) T.toFO ⟨φ, hφ, rfl⟩
  simp only [Equation.toFOSentence, Language.Sentence.Realize,
    Language.BoundedFormula.realize_alls, Language.BoundedFormula.realize_bdEqual] at h
  have e : (default : Empty → N) = Empty.elim := funext fun e => e.elim
  rw [e] at h
  exact h _

end OfFO

/-! ## The functors -/

section Functors

variable (T : L.Theory)

attribute [local instance] foStructure msStructure

/-- Mathlib homomorphisms commute with the interpretation of `msStructure`. -/
lemma ofFO_map_fun {N N' : Type u} [(toFOLanguage L).Structure N]
    [(toFOLanguage L).Structure N'] (h : (toFOLanguage L).Hom N N') (f : L.Functions)
    (p : ∏ᶜ fun _ : Fin (L.arity f) => N) :
    h (Language.Structure.funMap (L := toFOLanguage L)
        (fsym f) ((Types.productIso.{0, u} _).hom p)) =
      Language.Structure.funMap (L := toFOLanguage L)
        (fsym f)
        ((Types.productIso.{0, u} _).hom
          (Limits.Pi.map (C := Type u) (f := fun _ : Fin (L.arity f) => N)
            (g := fun _ : Fin (L.arity f) => N') (fun _ => TypeCat.ofHom h) p)) := by
  rw [Language.Hom.map_fun]
  congr 1
  funext i
  exact (ConcreteCategory.congr_hom
    (Limits.Pi.map_π (C := Type u) (f := fun _ : Fin (L.arity f) => N)
      (g := fun _ : Fin (L.arity f) => N') (fun _ => TypeCat.ofHom h) i) p).symm


variable [Unique L.Sorts]

/-- Homomorphisms commute with the casts to `default`. -/
lemma hom_tr {M M' : L.Sorts → Type u} (g : ∀ s, M s ⟶ M' s) (s : L.Sorts) (y : M s) :
    g default (tr M s y) = tr M' s (g s y) := by
  obtain rfl := hd s
  rfl

/-- Homomorphisms commute with the inverse casts from `default`. -/
lemma hom_tr_symm {M M' : L.Sorts → Type u} (g : ∀ s, M s ⟶ M' s) (s : L.Sorts)
    (y : M default) : g s ((tr M s).symm y) = (tr M' s).symm (g default y) := by
  obtain rfl := hd s
  rfl

/-- A product of maps applied to a tuple is the tuple of the images of its components. -/
lemma tup_map {n : ℕ} {F F' : Fin n → Type u} (g : ∀ i, F i ⟶ F' i) (x : ∀ i, F i) :
    Limits.Pi.map g (tup F x) = tup F' fun i => g i (x i) := by
  have h1 : ∀ i, Pi.π F' i (Limits.Pi.map g (tup F x)) = g i (x i) := fun i =>
    (ConcreteCategory.congr_hom (Limits.Pi.map_π g i) (tup F x)).trans
      congr(g i $(π_tup F x i))
  exact (Types.productIso.{0, u} F').toEquiv.injective
    (funext fun i => (h1 i).trans (π_tup F' (fun i => g i (x i)) i).symm)

/-- Models of `T` in `Type u` to Mathlib models of `T.toFO`. -/
noncomputable def toFO : T.ModelCat (Type u) ⥤ FOModelCat.{u} (toFOLanguage L) T.toFO where
  obj A :=
    haveI := foStructure_model A.Carrier (T := T)
    ⟨A.Carrier default⟩
  map {A B} g :=
    { toFun := g.toFun default
      map_fun' := fun {n} f x => by
        rw [foStructure_funMap, foStructure_funMap, hom_tr,
          ← types_comp_apply (funMap f.1) (g.toFun _), g.map_fun', types_comp_apply, tup_map]
        congr 3
        funext i
        exact hom_tr_symm g.toFun _ _
      map_rel' := fun r => Empty.elim r }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Mathlib models of `T.toFO` to models of `T` in `Type u`. -/
noncomputable def ofFO : FOModelCat.{u} (toFOLanguage L) T.toFO ⥤ T.ModelCat (Type u) where
  obj N :=
    haveI := msStructure_model N.Carrier (T := T)
    ⟨fun _ : L.Sorts => N.Carrier⟩
  map {N N'} h :=
    { toFun := fun _ => TypeCat.ofHom (show (toFOLanguage L).Hom N.Carrier N'.Carrier from h)
      map_fun' := fun f => ConcreteCategory.hom_ext _ _ fun p =>
        ofFO_map_fun (show (toFOLanguage L).Hom N.Carrier N'.Carrier from h) f p }
  map_id _ := rfl
  map_comp _ _ := rfl

end Functors

/-! ## The inverse laws -/

section Laws

variable (T : L.Theory)

variable [Unique L.Sorts]

attribute [local instance] foStructure msStructure

/-- On a model whose family is constant, `toFO T` followed by `ofFO T` gives back the model. -/
lemma ofFO_toFO_const (X : Type u) [L.Structure (C := Type u) fun _ : L.Sorts => X]
    [(fun _ : L.Sorts => X) ⊨ T] :
    (ofFO T).obj ((toFO T).obj ⟨fun _ : L.Sorts => X⟩) = ⟨fun _ : L.Sorts => X⟩ :=
  MSLanguage.modelCat_mk_eq _ _ (fun f => ConcreteCategory.hom_ext _ _ fun p => by
    exact congrArg _ (Iso.hom_inv_id_apply _ _)) _ _

/-- On objects, `toFO T` followed by `ofFO T` is the identity. -/
lemma ofFO_toFO_obj (A : T.ModelCat (Type u)) : (ofFO T).obj ((toFO T).obj A) = A := by
  obtain ⟨M⟩ := A
  rename_i s hm
  have hM : M = fun _ => M default := funext fun x => congr(M $(hd x))
  revert s hm
  rw [hM]
  intro s hm
  exact ofFO_toFO_const T (M default)

/-- `toFO T` followed by `ofFO T` is the identity functor. -/
lemma toFO_ofFO : toFO T ⋙ ofFO T = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun A => ofFO_toFO_obj T A)
  (fun A B g => MSLanguage.Hom.ext (funext fun s => by
    obtain rfl := hd s
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ _).symm
    refine Eq.trans ?_ ((MSLanguage.modelCat_eqToHom_toFun _ _).symm =≫ _)
    refine Eq.trans ?_ (_ ≫= (MSLanguage.comp_toFun _ _ _).symm)
    refine Eq.trans ?_ ((_ ≫= _ ≫= (MSLanguage.modelCat_eqToHom_toFun _ _).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

/-- On objects, `ofFO T` followed by `toFO T` is the identity. -/
lemma toFO_ofFO_obj (N : FOModelCat.{u} (toFOLanguage L) T.toFO) :
    (toFO T).obj ((ofFO T).obj N) = N := by
  obtain ⟨X⟩ := N
  rename_i s hm
  refine FOModelCat.mk_eq _ _ ?_ _ _
  obtain ⟨F, R⟩ := s
  refine FirstOrder.Language.Structure.ext ?_ ?_
  · funext n f x
    obtain ⟨f, rfl⟩ := f
    exact congrArg (F (fsym f))
      (Iso.inv_hom_id_apply (Types.productIso.{0, u} fun _ : Fin (L.arity f) => X) x)
  · funext n r
    exact Empty.elim r

/-- `ofFO T` followed by `toFO T` is the identity functor. -/
lemma ofFO_toFO : ofFO T ⋙ toFO T = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun N => toFO_ofFO_obj T N)
  (fun N N' h => FOModelCat.app_ext fun x => by
    rw [FOModelCat.app_comp, FOModelCat.app_comp, FOModelCat.app_eqToHom, FOModelCat.app_eqToHom]
    rfl)

end Laws

end UlmerBialgebras.Paper.AlgFO
