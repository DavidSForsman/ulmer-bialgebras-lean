module

public import UlmerBialgebras.Models.Bialgebra
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Subterminal

/-!
# Internal limits: Kan extensions and their lifting along PIE limits

This file formalizes the basic definitions of Section 4 of *A Syntactic Approach to Ulmer's
Bialgebras*, Definitions 4.1--4.4:

* `UlmerBialgebras.QuotientInitial`, `UlmerBialgebras.Subterminal` — Definition 4.1;
* `UlmerBialgebras.LeftExt`, `UlmerBialgebras.RightExt` — Definition 4.2, the categories of left
  resp. right extensions of `d` along `k` in a strict 2-category, together with the post-composition
  functors `UlmerBialgebras.LeftExt.push` and `UlmerBialgebras.RightExt.push` induced by a 1-cell
  `f`;
* `UlmerBialgebras.PreservesInitial`, `UlmerBialgebras.StrictlyCreatesInitial`,
  `UlmerBialgebras.JointlyStrictlyCreatesInitial` (and their duals) — Definition 4.3;
* `UlmerBialgebras.PreservesLeftKan`, `UlmerBialgebras.StrictlyCreatesLeftKan` (and their duals) —
  Definition 4.4.

Theorem 4.7 (lifting of Kan extensions along products, inserters and equifiers) is proved
in `KanProduct.lean`, `KanInserter.lean` and `KanEquifier.lean`; Corollary 4.8 is in
`KanBialgebra.lean`, and the supports (Definition 3.16) and Corollaries 4.11--4.12 are in
`KanModel.lean`.

## Main results

* `UlmerBialgebras.QuotientInitial`, `UlmerBialgebras.Subterminal`: Definition 4.1.
* `UlmerBialgebras.LeftExt`, `UlmerBialgebras.RightExt`: the categories of left and right extensions
  (Definition 4.2), Mathlib's `Bicategory.LeftExtension` and `Bicategory.RightExtension`.
* `UlmerBialgebras.PreservesInitial`, `UlmerBialgebras.StrictlyCreatesInitial`,
  `UlmerBialgebras.JointlyStrictlyCreatesInitial`: Definition 4.3.
* `UlmerBialgebras.preservesInitial_of_strictlyCreatesInitial`: a functor strictly creating initial
  objects preserves them.
* `UlmerBialgebras.PreservesLeftKan`, `UlmerBialgebras.StrictlyCreatesLeftKan`: Definition 4.4.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.1–4.4
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-! ## Definition 4.1 -/

/-- An object is **quotient initial** if there is at most one morphism out of it. -/
def QuotientInitial {A : Type*} [Category A] (a : A) : Prop := ∀ b : A, Subsingleton (a ⟶ b)

/-- An object is **subterminal** if there is at most one morphism into it: Mathlib's
`CategoryTheory.IsSubterminal`. -/
abbrev Subterminal {A : Type*} [Category A] (a : A) : Prop := IsSubterminal a

/-! ## Reflection of initial and terminal objects along fully faithful functors -/

/-- A fully faithful functor reflects initial objects. -/
noncomputable def isInitialOfFullyFaithful {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X : C} (h : Limits.IsInitial (F.obj X)) :
    Limits.IsInitial X :=
  Limits.IsInitial.ofUniqueHom (fun Y => F.preimage (h.to (F.obj Y)))
    (fun _ _ => F.map_injective (by simp only [Functor.map_preimage]; exact h.hom_ext _ _))

/-- A fully faithful functor which is surjective on objects preserves initial objects. -/
noncomputable def isInitialObjOfFullyFaithful {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] (hsurj : ∀ b : D, ∃ a : C, F.obj a = b) {X : C}
    (h : Limits.IsInitial X) : Limits.IsInitial (F.obj X) := by
  refine Limits.IsInitial.ofUniqueHom
    (fun b => F.map (h.to (hsurj b).choose) ≫ eqToHom (hsurj b).choose_spec) ?_
  intro b m
  have hm : m ≫ eqToHom (hsurj b).choose_spec.symm = F.map (h.to (hsurj b).choose) := by
    rw [← F.map_preimage (m ≫ eqToHom (hsurj b).choose_spec.symm)]
    exact F.congr_map (h.hom_ext _ _)
  rw [← hm]
  simp

/-! ## Initial and terminal objects in a product of categories -/

/-- A componentwise initial family is initial in the product category. -/
noncomputable def isInitialPi {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)] {b : ∀ i, B i}
    (h : ∀ i, Limits.IsInitial (b i)) : Limits.IsInitial b :=
  Limits.IsInitial.ofUniqueHom (fun x i => (h i).to (x i))
    (fun _ _ => funext fun i => (h i).hom_ext _ _)

/-- A componentwise terminal family is terminal in the product category. -/
noncomputable def isTerminalPi {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)] {b : ∀ i, B i}
    (h : ∀ i, Limits.IsTerminal (b i)) : Limits.IsTerminal b :=
  Limits.IsTerminal.ofUniqueHom (fun x i => (h i).from (x i))
    (fun _ _ => funext fun i => (h i).hom_ext _ _)

/-- Each component of an initial object of a product category is initial. -/
noncomputable def isInitialPiApply {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    {b : ∀ i, B i} (h : Limits.IsInitial b) (i : ι) : Limits.IsInitial (b i) := by
  classical
  refine Limits.IsInitial.ofUniqueHom
    (fun x => (h.to (Function.update b i x)) i ≫ eqToHom (Function.update_self i x b)) ?_
  intro x m
  have key : h.to (Function.update b i x) = (fun j =>
      if hj : j = i then (by subst hj; exact m ≫ eqToHom (Function.update_self j x b).symm)
      else eqToHom (Function.update_of_ne hj x b).symm) := h.hom_ext _ _
  have h2 := funext_iff.mp key i
  simp only [dite_eq_left] at h2
  rw [h2]; simp

/-- Each component of a terminal object of a product category is terminal. -/
noncomputable def isTerminalPiApply {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    {b : ∀ i, B i} (h : Limits.IsTerminal b) (i : ι) : Limits.IsTerminal (b i) := by
  classical
  refine Limits.IsTerminal.ofUniqueHom
    (fun x => eqToHom (Function.update_self i x b).symm ≫ (h.from (Function.update b i x)) i) ?_
  intro x m
  have key : h.from (Function.update b i x) = (fun j =>
      if hj : j = i then (by subst hj; exact eqToHom (Function.update_self j x b) ≫ m)
      else eqToHom (Function.update_of_ne hj x b)) := h.hom_ext _ _
  have h2 := funext_iff.mp key i
  simp only [dite_eq_left] at h2
  rw [h2]; simp

/-! ## Definition 4.3 -/

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor preserves initial objects. -/
def PreservesInitial (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsInitial a) → Nonempty (Limits.IsInitial (F.obj a))

/-- A functor preserves terminal objects. -/
def PreservesTerminal (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsTerminal a) → Nonempty (Limits.IsTerminal (F.obj a))

/-- A functor **strictly creates initial objects**: every initial object of the target has
a unique preimage, and that preimage is initial. -/
def StrictlyCreatesInitial (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsInitial b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsInitial a)

/-- A functor **strictly creates terminal objects**. -/
def StrictlyCreatesTerminal (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsTerminal b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsTerminal a)

/-- A functor strictly creating initial objects preserves them, as soon as the target has an
initial object. -/
lemma preservesInitial_of_strictlyCreatesInitial (F : A ⥤ B) (h : StrictlyCreatesInitial F)
    {b₀ : B} (hb₀ : Nonempty (Limits.IsInitial b₀)) : PreservesInitial F := by
  intro a ha
  obtain ⟨⟨a₀, ha₀, -⟩, hinit⟩ := h b₀ hb₀
  have i : a ≅ a₀ := ha.some.uniqueUpToIso (hinit a₀ ha₀).some
  exact ⟨Limits.IsInitial.ofIso hb₀.some ((eqToIso ha₀).symm ≪≫ (F.mapIso i).symm)⟩

/-- A family of functors **jointly strictly creates initial objects**. -/
def JointlyStrictlyCreatesInitial {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, Nonempty (Limits.IsInitial b) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧
      ∀ a : A, (∀ i, (F i).obj a = b i) → Nonempty (Limits.IsInitial a)

/-- A family of functors **jointly strictly creates terminal objects**. -/
def JointlyStrictlyCreatesTerminal {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, Nonempty (Limits.IsTerminal b) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧
      ∀ a : A, (∀ i, (F i).obj a = b i) → Nonempty (Limits.IsTerminal a)

/-- A family of functors **jointly strictly creates quotient initial objects**: every family of
quotient initial objects has a unique lift, and every lift of it is quotient initial. -/
def JointlyStrictlyCreatesQuotientInitial {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, (∀ i, QuotientInitial (b i)) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧ ∀ a : A, (∀ i, (F i).obj a = b i) → QuotientInitial a

/-- A family of functors **jointly strictly creates subterminal objects**: every family of
subterminal objects has a unique lift, and every lift of it is subterminal. -/
def JointlyStrictlyCreatesSubterminal {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, (∀ i, Subterminal (b i)) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧ ∀ a : A, (∀ i, (F i).obj a = b i) → Subterminal a

/-! ### Definition 4.3 (2) and (4): reflection and creation -/

/-- A functor **reflects initial objects** (Definition 4.3 (2)): "an object `c` in `C` is an
initial object whenever `Fc` is". -/
def ReflectsInitial (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsInitial (F.obj a)) → Nonempty (Limits.IsInitial a)

/-- A functor **reflects terminal objects**: the dual of `ReflectsInitial`. -/
def ReflectsTerminal (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsTerminal (F.obj a)) → Nonempty (Limits.IsTerminal a)

/-- A functor **creates initial objects** (Definition 4.3 (4)): "whenever `D` has an initial
object, then `C` has one and `F` preserves and reflects initial objects". -/
def CreatesInitial (F : A ⥤ B) : Prop :=
  (∃ b : B, Nonempty (Limits.IsInitial b)) →
    (∃ a : A, Nonempty (Limits.IsInitial a)) ∧ PreservesInitial F ∧ ReflectsInitial F

/-- A functor **creates terminal objects**: the dual of `CreatesInitial`. -/
def CreatesTerminal (F : A ⥤ B) : Prop :=
  (∃ b : B, Nonempty (Limits.IsTerminal b)) →
    (∃ a : A, Nonempty (Limits.IsTerminal a)) ∧ PreservesTerminal F ∧ ReflectsTerminal F

/-! The joint forms. Definition 4.3 identifies a family `(F_i : C → D_i)_i` with the induced
functor `C → ∏_i D_i`, which is `Functor.pi' F`. -/

section Jointly

variable {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]

/-- A family of functors **jointly preserves initial objects** (Definition 4.3 (1)). -/
def JointlyPreservesInitial (F : ∀ i, A ⥤ B i) : Prop := PreservesInitial (Functor.pi' F)

/-- A family of functors **jointly preserves terminal objects**. -/
def JointlyPreservesTerminal (F : ∀ i, A ⥤ B i) : Prop := PreservesTerminal (Functor.pi' F)

/-- A family of functors **jointly reflects initial objects** (Definition 4.3 (2)). -/
def JointlyReflectsInitial (F : ∀ i, A ⥤ B i) : Prop := ReflectsInitial (Functor.pi' F)

/-- A family of functors **jointly reflects terminal objects**. -/
def JointlyReflectsTerminal (F : ∀ i, A ⥤ B i) : Prop := ReflectsTerminal (Functor.pi' F)

/-- A family of functors **jointly creates initial objects** (Definition 4.3 (4)). -/
def JointlyCreatesInitial (F : ∀ i, A ⥤ B i) : Prop := CreatesInitial (Functor.pi' F)

/-- A family of functors **jointly creates terminal objects**. -/
def JointlyCreatesTerminal (F : ∀ i, A ⥤ B i) : Prop := CreatesTerminal (Functor.pi' F)

end Jointly

/-! ### Sanity lemmas for Definition 4.3 -/

/-- A functor strictly creating terminal objects preserves them, as soon as the target has a
terminal object. -/
lemma preservesTerminal_of_strictlyCreatesTerminal (F : A ⥤ B) (h : StrictlyCreatesTerminal F)
    {b₀ : B} (hb₀ : Nonempty (Limits.IsTerminal b₀)) : PreservesTerminal F := by
  intro a ha
  obtain ⟨⟨a₀, ha₀, -⟩, hterm⟩ := h b₀ hb₀
  have i : a ≅ a₀ := ha.some.uniqueUpToIso (hterm a₀ ha₀).some
  exact ⟨Limits.IsTerminal.ofIso hb₀.some ((eqToIso ha₀).symm ≪≫ (F.mapIso i).symm)⟩

/-- Strict creation of initial objects implies creation. -/
lemma createsInitial_of_strictlyCreatesInitial (F : A ⥤ B) (h : StrictlyCreatesInitial F) :
    CreatesInitial F := by
  rintro ⟨b₀, hb₀⟩
  obtain ⟨⟨a₀, ha₀, -⟩, hinit⟩ := h b₀ hb₀
  exact ⟨⟨a₀, hinit a₀ ha₀⟩, preservesInitial_of_strictlyCreatesInitial F h hb₀,
    fun a ha => (h (F.obj a) ha).2 a rfl⟩

/-- Strict creation of terminal objects implies creation. -/
lemma createsTerminal_of_strictlyCreatesTerminal (F : A ⥤ B) (h : StrictlyCreatesTerminal F) :
    CreatesTerminal F := by
  rintro ⟨b₀, hb₀⟩
  obtain ⟨⟨a₀, ha₀, -⟩, hterm⟩ := h b₀ hb₀
  exact ⟨⟨a₀, hterm a₀ ha₀⟩, preservesTerminal_of_strictlyCreatesTerminal F h hb₀,
    fun a ha => (h (F.obj a) ha).2 a rfl⟩

/-- A functor creating initial objects preserves them, as soon as the target has one. -/
lemma preservesInitial_of_createsInitial (F : A ⥤ B) (h : CreatesInitial F) {b₀ : B}
    (hb₀ : Nonempty (Limits.IsInitial b₀)) : PreservesInitial F :=
  (h ⟨b₀, hb₀⟩).2.1

/-- A functor creating initial objects reflects them, as soon as the target has one. -/
lemma reflectsInitial_of_createsInitial (F : A ⥤ B) (h : CreatesInitial F) {b₀ : B}
    (hb₀ : Nonempty (Limits.IsInitial b₀)) : ReflectsInitial F :=
  (h ⟨b₀, hb₀⟩).2.2

/-- A functor creating terminal objects preserves them, as soon as the target has one. -/
lemma preservesTerminal_of_createsTerminal (F : A ⥤ B) (h : CreatesTerminal F) {b₀ : B}
    (hb₀ : Nonempty (Limits.IsTerminal b₀)) : PreservesTerminal F :=
  (h ⟨b₀, hb₀⟩).2.1

/-- A functor creating terminal objects reflects them, as soon as the target has one. -/
lemma reflectsTerminal_of_createsTerminal (F : A ⥤ B) (h : CreatesTerminal F) {b₀ : B}
    (hb₀ : Nonempty (Limits.IsTerminal b₀)) : ReflectsTerminal F :=
  (h ⟨b₀, hb₀⟩).2.2

section Jointly

variable {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]

/-- Joint strict creation of initial objects is strict creation by the induced functor. -/
lemma strictlyCreatesInitial_pi' {F : ∀ i, A ⥤ B i} (h : JointlyStrictlyCreatesInitial F) :
    StrictlyCreatesInitial (Functor.pi' F) := by
  intro b hb
  obtain ⟨⟨a, ha, hu⟩, hi⟩ := h b hb
  exact ⟨⟨a, funext ha, fun a' h' => hu a' fun i => funext_iff.mp h' i⟩,
    fun a' h' => hi a' fun i => funext_iff.mp h' i⟩

/-- Joint strict creation of terminal objects is strict creation by the induced functor. -/
lemma strictlyCreatesTerminal_pi' {F : ∀ i, A ⥤ B i} (h : JointlyStrictlyCreatesTerminal F) :
    StrictlyCreatesTerminal (Functor.pi' F) := by
  intro b hb
  obtain ⟨⟨a, ha, hu⟩, hi⟩ := h b hb
  exact ⟨⟨a, funext ha, fun a' h' => hu a' fun i => funext_iff.mp h' i⟩,
    fun a' h' => hi a' fun i => funext_iff.mp h' i⟩

/-- Joint strict creation of initial objects implies joint creation. -/
lemma jointlyCreatesInitial_of_jointlyStrictlyCreatesInitial {F : ∀ i, A ⥤ B i}
    (h : JointlyStrictlyCreatesInitial F) : JointlyCreatesInitial F :=
  createsInitial_of_strictlyCreatesInitial _ (strictlyCreatesInitial_pi' h)

/-- Joint strict creation of terminal objects implies joint creation. -/
lemma jointlyCreatesTerminal_of_jointlyStrictlyCreatesTerminal {F : ∀ i, A ⥤ B i}
    (h : JointlyStrictlyCreatesTerminal F) : JointlyCreatesTerminal F :=
  createsTerminal_of_strictlyCreatesTerminal _ (strictlyCreatesTerminal_pi' h)

end Jointly

section Extensions

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ## Definition 4.2: categories of extensions -/

/-- A left extension of `d` along `k`: a 1-cell `l` together with a 2-cell `d ⟹ k l`; Mathlib's
`Bicategory.LeftExtension k d`. -/
abbrev LeftExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.LeftExtension k d

/-- A right extension of `d` along `k`: a 1-cell `l` together with a 2-cell `k l ⟹ d`; Mathlib's
`Bicategory.RightExtension k d`. -/
abbrev RightExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.RightExtension k d

/-- The left extension given by a 1-cell `l` and a 2-cell `d ⟹ k l`. -/
abbrev LeftExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (unit : d ⟶ k ≫ ext) :
    LeftExt k d := Bicategory.LeftExtension.mk ext unit

/-- The right extension given by a 1-cell `l` and a 2-cell `k l ⟹ d`. -/
abbrev RightExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (counit : k ≫ ext ⟶ d) :
    RightExt k d := Bicategory.RightExtension.mk ext counit

/-- The extending 1-cell of a left extension. -/
abbrev LeftExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : X ⟶ c :=
  Bicategory.LeftExtension.extension L

/-- The extending 1-cell of a right extension. -/
abbrev RightExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) : X ⟶ c :=
  Bicategory.RightExtension.extension L

/-- The comparison 2-cell of a left extension. -/
abbrev LeftExt.unit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : d ⟶ k ≫ L.ext :=
  Bicategory.LeftExtension.unit L

/-- The comparison 2-cell of a right extension. -/
abbrev RightExt.counit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) :
    k ≫ L.ext ⟶ d :=
  Bicategory.RightExtension.counit L

/-! ### The interface of morphisms of extensions

The category of left extensions is Mathlib's `StructuredArrow d (precomp _ k)`, and that of right
extensions is `CostructuredArrow (precomp _ k) d`. The library uses them only through the 2-cell of
a morphism, its compatibility with the comparison 2-cells, the morphism given by a compatible
2-cell, and extensionality. -/

namespace LeftExt

variable {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' L'' : LeftExt k d}

/-- The 2-cell `L.ext ⟶ L'.ext` of a morphism of left extensions. -/
abbrev homCell (α : L ⟶ L') : L.ext ⟶ L'.ext := α.right

/-- A morphism of left extensions is compatible with the comparison 2-cells. -/
lemma w (α : L ⟶ L') : L.unit ≫ k ◁ homCell α = L'.unit := Bicategory.LeftExtension.w α

/-- The morphism of left extensions given by a compatible 2-cell. -/
abbrev homMk (η : L.ext ⟶ L'.ext) (w : L.unit ≫ k ◁ η = L'.unit) : L ⟶ L' :=
  Bicategory.LeftExtension.homMk η w

/-- The 2-cell of `homMk η w` is `η`. -/
@[simp] lemma homCell_homMk (η : L.ext ⟶ L'.ext) (w : L.unit ≫ k ◁ η = L'.unit) :
    homCell (homMk η w) = η := rfl

/-- The 2-cell of the identity is the identity. -/
@[simp] lemma homCell_id (L : LeftExt k d) : homCell (𝟙 L) = 𝟙 L.ext := rfl

/-- The 2-cell of a composite is the composite of the 2-cells. -/
@[simp] lemma homCell_comp (α : L ⟶ L') (β : L' ⟶ L'') :
    homCell (α ≫ β) = homCell α ≫ homCell β := rfl

/-- Morphisms of left extensions are equal when their 2-cells are. -/
@[ext] lemma hom_ext {α β : L ⟶ L'} (h : homCell α = homCell β) : α = β :=
  StructuredArrow.hom_ext α β h

end LeftExt

namespace RightExt

variable {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' L'' : RightExt k d}

/-- The 2-cell `L.ext ⟶ L'.ext` of a morphism of right extensions. -/
abbrev homCell (α : L ⟶ L') : L.ext ⟶ L'.ext := α.left

/-- A morphism of right extensions is compatible with the comparison 2-cells. -/
lemma w (α : L ⟶ L') : k ◁ homCell α ≫ L'.counit = L.counit := Bicategory.RightExtension.w α

/-- The morphism of right extensions given by a compatible 2-cell. -/
abbrev homMk (η : L.ext ⟶ L'.ext) (w : k ◁ η ≫ L'.counit = L.counit) : L ⟶ L' :=
  Bicategory.RightExtension.homMk η w

/-- The 2-cell of `homMk η w` is `η`. -/
@[simp] lemma homCell_homMk (η : L.ext ⟶ L'.ext) (w : k ◁ η ≫ L'.counit = L.counit) :
    homCell (homMk η w) = η := rfl

/-- The 2-cell of the identity is the identity. -/
@[simp] lemma homCell_id (L : RightExt k d) : homCell (𝟙 L) = 𝟙 L.ext := rfl

/-- The 2-cell of a composite is the composite of the 2-cells. -/
@[simp] lemma homCell_comp (α : L ⟶ L') (β : L' ⟶ L'') :
    homCell (α ≫ β) = homCell α ≫ homCell β := rfl

/-- Morphisms of right extensions are equal when their 2-cells are. -/
@[ext] lemma hom_ext {α β : L ⟶ L'} (h : homCell α = homCell β) : α = β :=
  CostructuredArrow.hom_ext α β h

end RightExt

/-- Two left extensions with the same underlying 1-cell and the same (transported)
comparison 2-cell are equal. -/
lemma LeftExt.eq_of_ext_eq {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' : LeftExt k d}
    (h : L.ext = L'.ext) (h2 : L.unit ≫ eqToHom (by rw [h]) = L'.unit) : L = L' := by
  obtain ⟨⟨⟨⟩⟩, e, u⟩ := L
  obtain ⟨⟨⟨⟩⟩, e', u'⟩ := L'
  cases h
  have h3 : u = u' := (Category.comp_id u).symm.trans h2
  subst h3
  rfl

/-- Two right extensions with the same underlying 1-cell and the same (transported)
comparison 2-cell are equal. -/
lemma RightExt.eq_of_ext_eq {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' : RightExt k d}
    (h : L.ext = L'.ext) (h2 : eqToHom (by rw [h]) ≫ L'.counit = L.counit) : L = L' := by
  obtain ⟨e, ⟨⟨⟩⟩, u⟩ := L
  obtain ⟨e', ⟨⟨⟩⟩, u'⟩ := L'
  cases h
  have h3 : u = u' := h2.symm.trans (Category.id_comp u')
  subst h3
  rfl

/-- The extending 1-cell of `LeftExt.mk e u` is `e`. -/
@[simp] lemma LeftExt.mk_ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (e : X ⟶ c) (u : d ⟶ k ≫ e) :
    (LeftExt.mk e u).ext = e := rfl

/-- The comparison 2-cell of `LeftExt.mk e u` is `u`. -/
@[simp] lemma LeftExt.mk_unit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (e : X ⟶ c) (u : d ⟶ k ≫ e) :
    (LeftExt.mk e u).unit = u := rfl

/-- A left extension is `LeftExt.mk` of its 1-cell and its comparison 2-cell. -/
lemma LeftExt.mk_eta {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) :
    LeftExt.mk L.ext L.unit = L := rfl

/-- The extending 1-cell of `RightExt.mk e u` is `e`. -/
@[simp] lemma RightExt.mk_ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (e : X ⟶ c) (u : k ≫ e ⟶ d) :
    (RightExt.mk e u).ext = e := rfl

/-- The comparison 2-cell of `RightExt.mk e u` is `u`. -/
@[simp] lemma RightExt.mk_counit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (e : X ⟶ c) (u : k ≫ e ⟶ d) :
    (RightExt.mk e u).counit = u := rfl

/-- The comparison 2-cells of equal left extensions agree. -/
lemma LeftExt.unit_congr {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' : LeftExt k d}
    (h : L = L') : L.unit ≫ eqToHom (by rw [h]) = L'.unit := by
  subst h; simp

end Extensions

section TwoCat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Post-composing a morphism of left extensions with `f` is compatible with the comparison
2-cells of the post-composed extensions. -/
lemma LeftExt.push_w {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') {L L' : LeftExt k d}
    (a : L ⟶ L') :
    ((L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f)) ≫ k ◁ (LeftExt.homCell a ▷ f) =
      (L'.unit ▷ f) ≫ eqToHom (Category.assoc k L'.ext f) := by
  rw [Bicategory.Strict.whisker_assoc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (obj := _ ⟶ _), ← Bicategory.comp_whiskerRight, LeftExt.w a]

/-- Post-composition with a 1-cell `f : c ⟶ c'`, as a functor between categories of left
extensions.  This is the functor `f∗` of Definition 4.4. -/
@[implicit_reducible]
def LeftExt.push {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    LeftExt k d ⥤ LeftExt k (d ≫ f) where
  obj L := LeftExt.mk (L.ext ≫ f) ((L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f))
  map a := LeftExt.homMk (LeftExt.homCell a ▷ f) (LeftExt.push_w k d f a)
  map_id L := LeftExt.hom_ext (Bicategory.id_whiskerRight L.ext f)
  map_comp _ _ := LeftExt.hom_ext (Bicategory.comp_whiskerRight _ _ f)

/-- The extending 1-cell of `f_* L` is `L.ext ≫ f`. -/
@[simp] lemma LeftExt.push_obj_ext {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    (L : LeftExt k d) : ((LeftExt.push k d f).obj L).ext = L.ext ≫ f := rfl

/-- The comparison 2-cell of `f_* L` is `L.unit ▷ f`, up to associativity. -/
@[simp] lemma LeftExt.push_obj_unit {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    (L : LeftExt k d) :
    ((LeftExt.push k d f).obj L).unit = (L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f) := rfl

/-- The 2-cell of `f_* a` is `a ▷ f`. -/
@[simp] lemma LeftExt.push_map_homCell {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    {L L' : LeftExt k d} (a : L ⟶ L') :
    LeftExt.homCell ((LeftExt.push k d f).map a) = LeftExt.homCell a ▷ f := rfl

/-- Whiskering a 2-cell `γ : f ⟹ g` by the extending 1-cell of a left extension `L` commutes
with the comparison 2-cells of `f_* L` and of `g_* L` twisted by `d ◁ γ`. -/
lemma LeftExt.unit_whiskerLeft_whiskerLeft {I X c c' : Obj} (k : I ⟶ X) {d : I ⟶ c}
    {f g : c ⟶ c'} (γ : f ⟶ g) (L : LeftExt k d) :
    ((L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f)) ≫ (k ◁ (L.ext ◁ γ))
      = d ◁ γ ≫ (L.unit ▷ g) ≫ eqToHom (Category.assoc k L.ext g) := by
  rw [Category.assoc, Bicategory.Strict.comp_whiskerLeft']
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc, ← Bicategory.whisker_exchange]

/-- Post-composing a morphism of right extensions with `f` is compatible with the comparison
2-cells of the post-composed extensions. -/
lemma RightExt.push_w {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') {L L' : RightExt k d}
    (a : L ⟶ L') :
    k ◁ (RightExt.homCell a ▷ f) ≫ (eqToHom (Category.assoc k L'.ext f).symm ≫ (L'.counit ▷ f)) =
      eqToHom (Category.assoc k L.ext f).symm ≫ (L.counit ▷ f) := by
  rw [Bicategory.Strict.whisker_assoc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Bicategory.comp_whiskerRight, RightExt.w a]

/-- Post-composition with a 1-cell `f : c ⟶ c'`, as a functor between categories of right
extensions. -/
@[implicit_reducible]
def RightExt.push {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    RightExt k d ⥤ RightExt k (d ≫ f) where
  obj L := RightExt.mk (L.ext ≫ f) (eqToHom (Category.assoc k L.ext f).symm ≫ (L.counit ▷ f))
  map a := RightExt.homMk (RightExt.homCell a ▷ f) (RightExt.push_w k d f a)
  map_id L := RightExt.hom_ext (Bicategory.id_whiskerRight L.ext f)
  map_comp _ _ := RightExt.hom_ext (Bicategory.comp_whiskerRight _ _ f)

/-- The extending 1-cell of `f_* L` is `L.ext ≫ f`. -/
@[simp] lemma RightExt.push_obj_ext {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    (L : RightExt k d) : ((RightExt.push k d f).obj L).ext = L.ext ≫ f := rfl

/-- The comparison 2-cell of `f_* L` is `L.counit ▷ f`, up to associativity. -/
@[simp] lemma RightExt.push_obj_counit {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    (L : RightExt k d) :
    ((RightExt.push k d f).obj L).counit =
      eqToHom (Category.assoc k L.ext f).symm ≫ (L.counit ▷ f) := rfl

/-- The 2-cell of `f_* a` is `a ▷ f`. -/
@[simp] lemma RightExt.push_map_homCell {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    {L L' : RightExt k d} (a : L ⟶ L') :
    RightExt.homCell ((RightExt.push k d f).map a) = RightExt.homCell a ▷ f := rfl

/-! ## Definition 4.4 -/

variable {I X c c' : Obj}

/-- `f` preserves the left Kan extension of `d` along `k`. -/
def PreservesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  PreservesInitial (LeftExt.push k d f)

/-- `f` preserves the right Kan extension of `d` along `k`. -/
def PreservesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  PreservesTerminal (RightExt.push k d f)

/-- `f` strictly creates the left Kan extensions of `d` along `k`. -/
def StrictlyCreatesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  StrictlyCreatesInitial (LeftExt.push k d f)

/-- `f` strictly creates the right Kan extensions of `d` along `k`. -/
def StrictlyCreatesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  StrictlyCreatesTerminal (RightExt.push k d f)

/-- `f` reflects the left Kan extension of `d` along `k` (Definition 4.4): `f_*` reflects
initial objects. -/
def ReflectsLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  ReflectsInitial (LeftExt.push k d f)

/-- `f` reflects the right Kan extension of `d` along `k`. -/
def ReflectsRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  ReflectsTerminal (RightExt.push k d f)

/-- `f` creates the left Kan extension of `d` along `k` (Definition 4.4): `f_*` creates initial
objects. -/
def CreatesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  CreatesInitial (LeftExt.push k d f)

/-- `f` creates the right Kan extension of `d` along `k`. -/
def CreatesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  CreatesTerminal (RightExt.push k d f)

/-! ### Sanity lemmas for Definition 4.4 -/

/-- Strict creation of a left Kan extension implies its creation. -/
lemma createsLeftKan_of_strictlyCreatesLeftKan {k : I ⟶ X} {d : I ⟶ c} {f : c ⟶ c'}
    (h : StrictlyCreatesLeftKan k d f) : CreatesLeftKan k d f :=
  createsInitial_of_strictlyCreatesInitial _ h

/-- Strict creation of a right Kan extension implies its creation. -/
lemma createsRightKan_of_strictlyCreatesRightKan {k : I ⟶ X} {d : I ⟶ c} {f : c ⟶ c'}
    (h : StrictlyCreatesRightKan k d f) : CreatesRightKan k d f :=
  createsTerminal_of_strictlyCreatesTerminal _ h

/-- If `f` creates the left Kan extension of `d` along `k` and `d ≫ f` has one, then `f`
preserves and reflects the left Kan extension of `d` along `k`. -/
lemma preservesLeftKan_and_reflectsLeftKan_of_createsLeftKan {k : I ⟶ X} {d : I ⟶ c}
    {f : c ⟶ c'} (h : CreatesLeftKan k d f) {L : LeftExt k (d ≫ f)}
    (hL : Nonempty (Limits.IsInitial L)) : PreservesLeftKan k d f ∧ ReflectsLeftKan k d f :=
  ⟨preservesInitial_of_createsInitial _ h hL, reflectsInitial_of_createsInitial _ h hL⟩

/-- If `f` creates the right Kan extension of `d` along `k` and `d ≫ f` has one, then `f`
preserves and reflects the right Kan extension of `d` along `k`. -/
lemma preservesRightKan_and_reflectsRightKan_of_createsRightKan {k : I ⟶ X} {d : I ⟶ c}
    {f : c ⟶ c'} (h : CreatesRightKan k d f) {R : RightExt k (d ≫ f)}
    (hR : Nonempty (Limits.IsTerminal R)) : PreservesRightKan k d f ∧ ReflectsRightKan k d f :=
  ⟨preservesTerminal_of_createsTerminal _ h hR, reflectsTerminal_of_createsTerminal _ h hR⟩

end TwoCat

end UlmerBialgebras
