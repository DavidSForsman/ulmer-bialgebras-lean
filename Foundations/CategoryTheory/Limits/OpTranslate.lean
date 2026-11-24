module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Foundations.CategoryTheory.Limits.PiLimits
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# Opposite-category translations

Regular monomorphisms are regular epimorphisms in the opposite category. Opposite
categories commute with products of categories, compatibly with evaluation and insertion
of a single component. These translations let the primal preservation theorems supply
their dual forms.

## Main results

* `UlmerBialgebras.OpTranslate.isRegularMono_iff_op`: `f` is a regular monomorphism iff `f.op` is a
  regular epimorphism;
* `UlmerBialgebras.OpTranslate.preservesLimitsOfShape_iff_op`: `F` preserves limits of shape `J` iff
  `F.op` preserves colimits of shape `Jᵒᵖ`;
* `UlmerBialgebras.OpTranslate.isRegularMono_map`: equalizer-preserving functors preserve regular
  monomorphisms;
* `UlmerBialgebras.OpTranslate.piOpEquiv`: taking opposites commutes with products of categories;
* `UlmerBialgebras.constPreservesLimitsOfShape`, `UlmerBialgebras.pi'PreservesLimitsOfShape`,
  `UlmerBialgebras.piEvalPreservesLimitsOfShape'`: constant functors preserve connected limits, a
  product-valued functor preserves the limits preserved by every component, and product
  evaluations preserve limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.18, Theorem 4.19, Example 4.20 (2)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.OpTranslate

open CategoryTheory Limits Opposite

/-- Regular monomorphisms are regular epimorphisms in the opposite category. -/
lemma isRegularMono_iff_op {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    IsRegularMono f ↔ IsRegularEpi f.op :=
  (isRegularEpi_op_iff_isRegularMono f).symm

/-- Coreflexive pairs become reflexive pairs under reversal of arrows. -/
lemma isCoreflexivePair_iff_op {C : Type u} [Category.{v} C] {X Y : C} (f g : X ⟶ Y) :
    IsCoreflexivePair f g ↔ IsReflexivePair f.op g.op := by
  constructor
  · intro h
    let := h
    obtain ⟨r, hf, hg⟩ := IsCoreflexivePair.common_retraction f g
    exact IsReflexivePair.mk' r.op (by simpa using congr(($(hf)).op))
      (by simpa using congr(($(hg)).op))
  · intro h
    let := h
    obtain ⟨r, hf, hg⟩ := IsReflexivePair.common_section f.op g.op
    exact IsCoreflexivePair.mk' r.unop (by simpa using congr(($(hf)).unop))
      (by simpa using congr(($(hg)).unop))

section Preservation

variable {A B J : Type*} [Category A] [Category B] [Category J]

/-- Limit preservation is colimit preservation for the opposite diagram and functor. -/
lemma preservesLimit_iff_op (D : J ⥤ A) (F : A ⥤ B) :
    PreservesLimit D F ↔ PreservesColimit D.op F.op := by
  constructor
  · intro h
    let := h
    have : PreservesLimit ((CategoryTheory.opOpEquivalence J).functor ⋙ D) F := inferInstance
    have : PreservesLimit D.op.leftOp F :=
      inferInstanceAs (PreservesLimit ((CategoryTheory.opOpEquivalence J).functor ⋙ D) F)
    exact preservesColimit_op _ _
  · intro h
    let := h
    exact preservesLimit_of_op _ _

/-- Shape-wise limit preservation is shape-wise colimit preservation in opposite categories. -/
lemma preservesLimitsOfShape_iff_op (J : Type*) [Category J] (F : A ⥤ B) :
    PreservesLimitsOfShape J F ↔ PreservesColimitsOfShape Jᵒᵖ F.op := by
  constructor
  · intro h
    let := h
    have : PreservesLimitsOfShape Jᵒᵖᵒᵖ F :=
      preservesLimitsOfShape_of_equiv (CategoryTheory.opOpEquivalence J).symm F
    exact preservesColimitsOfShape_op Jᵒᵖ F
  · intro h
    let := h
    exact preservesLimitsOfShape_of_op J F

/-- A functor preserving coequalizers preserves regular epimorphisms. -/
lemma isRegularEpi_map (F : A ⥤ B) [PreservesColimitsOfShape WalkingParallelPair F]
    {X Y : A} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularEpi (F.map f) := by
  let r := IsRegularEpi.getStruct f
  exact ⟨⟨Cofork.IsColimit.regularEpi ((isColimitMapCoconeCoforkEquiv F r.w)
    (isColimitOfPreserves F r.isColimit))⟩⟩

/-- Equalizer-preserving functors preserve regular monomorphisms, by regular-epi duality. -/
lemma isRegularMono_map (F : A ⥤ B) [PreservesLimitsOfShape WalkingParallelPair F]
    {X Y : A} (f : X ⟶ Y) [IsRegularMono f] : IsRegularMono (F.map f) := by
  have : PreservesColimitsOfShape WalkingParallelPairᵒᵖ F.op :=
    (preservesLimitsOfShape_iff_op WalkingParallelPair F).1 inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair F.op :=
    preservesColimitsOfShape_of_equiv walkingParallelPairOpEquiv.symm F.op
  exact (isRegularEpi_op_iff_isRegularMono (F.map f)).1 (isRegularEpi_map F.op f.op)

end Preservation

variable {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]

/-- Send the opposite of a family to the family of its opposites. -/
@[simps]
def piOpTo : (∀ i, C i)ᵒᵖ ⥤ (∀ i, (C i)ᵒᵖ) where
  obj x i := Opposite.op (x.unop i)
  map f i := (f.unop i).op

/-- Assemble a family of opposite objects into the opposite of a family. -/
@[simps]
def piOpFrom : (∀ i, (C i)ᵒᵖ) ⥤ (∀ i, C i)ᵒᵖ where
  obj x := Opposite.op (fun i => (x i).unop)
  map f := Quiver.Hom.op (fun i => (f i).unop)

/-- Taking opposites commutes with products of categories. -/
def piOpEquiv : (∀ i, C i)ᵒᵖ ≌ (∀ i, (C i)ᵒᵖ) where
  functor := piOpTo C
  inverse := piOpFrom C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [piOpTo, piOpFrom])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [piOpTo, piOpFrom])
  functor_unitIso_comp x := by
    change 𝟙 ((piOpTo C).obj x) ≫ 𝟙 ((piOpTo C).obj x) = 𝟙 ((piOpTo C).obj x)
    simp

/-- The functor `piOpTo C` is an equivalence. -/
instance : (piOpTo C).IsEquivalence := (piOpEquiv C).isEquivalence_functor
/-- The functor `piOpFrom C` is an equivalence. -/
instance : (piOpFrom C).IsEquivalence := (piOpEquiv C).isEquivalence_inverse

/-- Evaluation commutes with the opposite/product equivalence. -/
lemma piOpTo_comp_eval (i : ι) :
    piOpTo C ⋙ Pi.eval (fun j => (C j)ᵒᵖ) i = (Pi.eval C i).op := rfl

/-- The product/opposite functors are strict inverses. -/
@[simp] lemma piOpTo_comp_piOpFrom : piOpTo C ⋙ piOpFrom C = 𝟭 _ := rfl

/-- The composite `piOpFrom C ⋙ piOpTo C` is the identity functor. -/
@[simp] lemma piOpFrom_comp_piOpTo : piOpFrom C ⋙ piOpTo C = 𝟭 _ := rfl

/-- Opposite products of functors are computed componentwise. -/
lemma pi'_op_comp_piOpTo {A : Type*} [Category A] (F : ∀ i, A ⥤ C i) :
    (Functor.pi' F).op ⋙ piOpTo C = Functor.pi' (fun i => (F i).op) := rfl

/-- Inserting one component commutes with taking opposites. -/
lemma update_op_comp_piOpTo [DecidableEq ι] (x : ∀ i, C i) (i : ι) :
    (updateFunctor x i).op ⋙ piOpTo C = updateFunctor (fun j => Opposite.op (x j)) i := by
  unfold updateFunctor
  rw [pi'_op_comp_piOpTo]
  congr 1
  funext j
  split_ifs with h <;> subst_vars <;> rfl

/-- Insertion compatibility with the inverse product/opposite functor. -/
lemma update_op_comp_piOpFrom [DecidableEq ι] (x : ∀ i, C i) (i : ι) :
    updateFunctor (fun j => Opposite.op (x j)) i ⋙ piOpFrom C = (updateFunctor x i).op := by
  have h := congrArg (fun F => F ⋙ piOpFrom C) (update_op_comp_piOpTo C x i)
  simpa only [Functor.assoc, piOpTo_comp_piOpFrom, Functor.comp_id] using h.symm

/-- Product-valued limit preservation is the product-valued colimit result in opposites. -/
lemma pi'_preservesLimitsOfShape (J : Type*) [Category J] {A : Type*} [Category A]
    (F : ∀ i, A ⥤ C i) [∀ i, PreservesLimitsOfShape J (F i)] :
    PreservesLimitsOfShape J (Functor.pi' F) := by
  have : ∀ i, PreservesColimitsOfShape Jᵒᵖ (F i).op :=
    fun i => (preservesLimitsOfShape_iff_op J (F i)).1 inferInstance
  have : PreservesColimitsOfShape Jᵒᵖ (Functor.pi' (fun i => (F i).op)) := inferInstance
  have : PreservesColimitsOfShape Jᵒᵖ ((Functor.pi' F).op ⋙ piOpTo C) := by
    rw [pi'_op_comp_piOpTo]
    infer_instance
  have : PreservesColimitsOfShape Jᵒᵖ (Functor.pi' F).op :=
    preservesColimitsOfShape_of_reflects_of_preserves _ (piOpTo C)
  exact (preservesLimitsOfShape_iff_op J (Functor.pi' F)).2 inferInstance

/-- Product evaluation preserves limits by its colimit counterpart in opposite categories. -/
lemma piEval_preservesLimitsOfShape (J : Type*) [Category J] (i : ι) :
    PreservesLimitsOfShape J (Pi.eval C i) := by
  classical
  have : PreservesColimitsOfShape Jᵒᵖ (Pi.eval (fun j => (C j)ᵒᵖ) i) := inferInstance
  have : PreservesColimitsOfShape Jᵒᵖ (piOpTo C ⋙ Pi.eval (fun j => (C j)ᵒᵖ) i) :=
    inferInstance
  have : PreservesColimitsOfShape Jᵒᵖ (Pi.eval C i).op := by
    rw [← piOpTo_comp_eval C i]
    infer_instance
  exact (preservesLimitsOfShape_iff_op J (Pi.eval C i)).2 inferInstance

/-- Constant limit preservation is dual to constant colimit preservation. -/
lemma const_preservesLimitsOfShape (J : Type*) [Category J] [IsConnected J]
    {A B : Type*} [Category A] [Category B] (x : B) :
    PreservesLimitsOfShape J ((Functor.const A).obj x) := by
  have : PreservesColimitsOfShape Jᵒᵖ (((Functor.const A).obj x).op) :=
    inferInstanceAs (PreservesColimitsOfShape Jᵒᵖ ((Functor.const Aᵒᵖ).obj (Opposite.op x)))
  exact (preservesLimitsOfShape_iff_op J ((Functor.const A).obj x)).2 inferInstance

end UlmerBialgebras.OpTranslate

/-! ## Product-limit instances derived from the colimit instances -/

namespace UlmerBialgebras

open CategoryTheory Limits

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {J : Type*} [Category J]

/-- A constant functor preserves limits of connected shapes, by duality. -/
instance constPreservesLimitsOfShape [IsConnected J] {A : Type*} [Category A] {E : Type*}
    [Category E] (x : E) : PreservesLimitsOfShape J ((Functor.const A).obj x) :=
  OpTranslate.const_preservesLimitsOfShape J x

/-- A product-valued functor preserves limits preserved by every component, by duality. -/
noncomputable instance pi'PreservesLimitsOfShape {A : Type*} [Category A] (f : ∀ j, A ⥤ C j)
    [∀ j, PreservesLimitsOfShape J (f j)] : PreservesLimitsOfShape J (Functor.pi' f) :=
  OpTranslate.pi'_preservesLimitsOfShape C J f

/-- Product evaluations preserve limits, by duality. -/
noncomputable instance piEvalPreservesLimitsOfShape' (i : ι) :
    PreservesLimitsOfShape J (Pi.eval C i) := OpTranslate.piEval_preservesLimitsOfShape C J i

end UlmerBialgebras
