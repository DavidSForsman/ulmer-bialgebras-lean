module

public import InternalGroups.GrpObjSubgroupCorrespondenceCocomm
public import InternalGroups.GrpStabilizerCoset
public import InternalGroups.GrpKernelImage
public import Foundations.CategoryTheory.Monoidal.CommComonReflexive
public import Foundations.CategoryTheory.Limits.MapRegularEpi
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Module maps of cocommutative comonoids: quotients, descent and kernels

The lemmas behind the bi-ideal correspondence of
`InternalGroups.GrpObjSubgroupCorrespondenceBiIdeal`, for an abelian symmetric monoidal category `A`
and an internal group or monoid `h` of `CommComon A`:

* comonoid structures on quotients by epimorphisms (`InternalGroups.comonObjOfEpi`), by lifting
  in squares with an epimorphism on the left and a monomorphism on the right;
* consequences of the exactness of the tensor product;
* the underlying morphisms in `A` of module maps (`InternalGroups.modHomA`);
* descent of module maps along epimorphisms of `A`, and the comparison of quotients by their
  kernels in `A`.

## Main results

* `InternalGroups.exists_hom_of_epi`: for module maps `p : N ⟶ P` and `f : N ⟶ M` with `p` an
  epimorphism of `A`, a morphism `g` of `A` with `p ≫ g = f` underlies a module map.
* `InternalGroups.exists_comp_eq_iff_kernelSubobject_le`: `f` factors through `p` iff the kernel
  of `p` in `A` is contained in that of `f`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj ComonObj

namespace InternalGroups

/-! ## Comonoid structures on quotients -/

section ComonObjOfEpi

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A quotient of a comonoid object through which the counit and the comultiplication descend is
itself a comonoid object.  Dual to `InternalGroups.monObjOfMono`. -/
@[instance_reducible, simps counit comul]
def comonObjOfEpi {m n : C} [ComonObj m] (p : m ⟶ n) [Epi p]
    (counit : n ⟶ 𝟙_ C) (comul : n ⟶ n ⊗ n)
    (hcounit : p ≫ counit = ε[m]) (hcomul : p ≫ comul = Δ[m] ≫ (p ⊗ₘ p)) : ComonObj n where
  counit := counit
  comul := comul
  counit_comul := by
    rw [← cancel_epi p, reassoc_of% hcomul, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id, hcounit, tensorHom_def, ComonObj.counit_comul_assoc,
      leftUnitor_inv_naturality]
  comul_counit := by
    rw [← cancel_epi p, reassoc_of% hcomul, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, hcounit, tensorHom_def', ComonObj.comul_counit_assoc,
      rightUnitor_inv_naturality]
  comul_assoc := by
    rw [← cancel_epi p, reassoc_of% hcomul, reassoc_of% hcomul]
    have hl : (p ⊗ₘ p) ≫ (comul ▷ n) = (Δ[m] ▷ m) ≫ ((p ⊗ₘ p) ⊗ₘ p) := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hcomul, Category.comp_id, Category.id_comp]
    have hr : (p ⊗ₘ p) ≫ (n ◁ comul) = (m ◁ Δ[m]) ≫ (p ⊗ₘ p ⊗ₘ p) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hcomul, Category.comp_id, Category.id_comp]
    rw [reassoc_of% hl, hr, associator_naturality, ComonObj.comul_assoc_assoc]

/-- The quotient map of `InternalGroups.comonObjOfEpi` is a morphism of comonoid objects. -/
lemma isComonHom_comonObjOfEpi {m n : C} [ComonObj m] (p : m ⟶ n) [Epi p]
    (counit : n ⟶ 𝟙_ C) (comul : n ⟶ n ⊗ n)
    (hcounit : p ≫ counit = ε[m]) (hcomul : p ≫ comul = Δ[m] ≫ (p ⊗ₘ p)) :
    letI := comonObjOfEpi p counit comul hcounit hcomul
    IsComonHom p :=
  letI := comonObjOfEpi p counit comul hcounit hcomul
  { hom_counit := hcounit, hom_comul := hcomul }

/-- A quotient of a cocommutative comonoid object is cocommutative. -/
lemma isCommComonObj_comonObjOfEpi [BraidedCategory C] {m n : C} [ComonObj m]
    [IsCommComonObj m] (p : m ⟶ n) [Epi p] (counit : n ⟶ 𝟙_ C) (comul : n ⟶ n ⊗ n)
    (hcounit : p ≫ counit = ε[m]) (hcomul : p ≫ comul = Δ[m] ≫ (p ⊗ₘ p)) :
    letI := comonObjOfEpi p counit comul hcounit hcomul
    IsCommComonObj n :=
  letI := comonObjOfEpi p counit comul hcounit hcomul
  ⟨by
    change comul ≫ (β_ n n).hom = comul
    rw [← cancel_epi p, reassoc_of% hcomul, hcomul, BraidedCategory.braiding_naturality,
      IsCommComonObj.comul_comm_assoc]⟩

/-- **Comonoid morphisms descend along epimorphic comonoid morphisms.**  If `p ≫ k` is a morphism
of comonoid objects and `p` is an epimorphic morphism of comonoid objects, then so is `k`. -/
lemma isComonHom_of_epi_comp {X Y Z : C} [ComonObj X] [ComonObj Y] [ComonObj Z]
    (p : X ⟶ Y) [Epi p] [IsComonHom p] (g : X ⟶ Z) [IsComonHom g] (k : Y ⟶ Z)
    (hk : p ≫ k = g) : IsComonHom k where
  hom_counit := by
    rw [← cancel_epi p, reassoc_of% hk, IsComonHom.hom_counit, IsComonHom.hom_counit]
  hom_comul := by
    rw [← cancel_epi p, reassoc_of% hk, IsComonHom.hom_comul, IsComonHom.hom_comul_assoc,
      tensorHom_comp_tensorHom, hk]

end ComonObjOfEpi

/-! ## Consequences of exactness of the tensor product -/

section ExactTensor

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A]

/-- By symmetry, tensoring on the right preserves finite limits. -/
lemma preservesFiniteLimits_tensorRight_of_left [BraidedCategory A]
    [∀ X : A, PreservesFiniteLimits (tensorLeft X)] (X : A) :
    PreservesFiniteLimits (tensorRight X) :=
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- By symmetry, tensoring on the right preserves finite colimits. -/
lemma preservesFiniteColimits_tensorRight_of_left [BraidedCategory A]
    [∀ X : A, PreservesFiniteColimits (tensorLeft X)] (X : A) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- A tensor product which is left exact in each variable preserves coreflexive equalizers in
each variable. -/
lemma tensorPreservesCoreflexiveEqualizers_of_preservesFiniteLimits
    [∀ X : A, PreservesFiniteLimits (tensorLeft X)]
    [∀ X : A, PreservesFiniteLimits (tensorRight X)] :
    UlmerBialgebras.TensorPreservesCoreflexiveEqualizers A where
  preserves_left _ := ⟨fun _ _ _ _ _ => inferInstance⟩
  preserves_right _ := ⟨fun _ _ _ _ _ => inferInstance⟩

/-- A right exact tensor product preserves reflexive coequalizers. -/
lemma preservesReflexiveCoeq_tensorLeft_of_preservesFiniteColimits
    [∀ X : A, PreservesFiniteColimits (tensorLeft X)] (Z : A) :
    PreservesReflexiveCoeq (tensorLeft Z) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- A tensor product which preserves monomorphisms in each variable preserves them jointly. -/
lemma mono_tensorHom_of_preservesMonomorphisms [∀ X : A, (tensorLeft X).PreservesMonomorphisms]
    [∀ X : A, (tensorRight X).PreservesMonomorphisms] {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y')
    [Mono f] [Mono g] : Mono (f ⊗ₘ g) := by
  rw [tensorHom_def]
  have : Mono (f ▷ X') := (tensorRight X').map_mono f
  have : Mono (Y ◁ g) := (tensorLeft Y).map_mono g
  exact mono_comp _ _

end ExactTensor

/-! ## Underlying morphisms of `A` -/


section Underlying

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [SymmetricCategory A]

/-- The morphism of `A` underlying a morphism of cocommutative comonoids, with the underlying
objects `X.X` and `Y.X` as source and target. -/
def homA {X Y : CommComon A} (f : X ⟶ Y) : X.X ⟶ Y.X := f.hom.hom

/-- `homA` sends a composite to the composite of the underlying morphisms. -/
@[simp]
lemma homA_comp {X Y Z : CommComon A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homA (f ≫ g) = homA f ≫ homA g := rfl

/-- `homA` sends an identity to the identity. -/
@[simp]
lemma homA_id (X : CommComon A) : homA (𝟙 X) = 𝟙 X.X := rfl

/-- A morphism of cocommutative comonoids is determined by its underlying morphism. -/
lemma homA_injective {X Y : CommComon A} : Function.Injective (homA (X := X) (Y := Y)) :=
  fun f g hfg => CommComon.hom_ext f g hfg

/-- The underlying morphism of `CommComon.homMk f` is `f`. -/
@[simp]
lemma homA_homMk {X Y : CommComon A} (f : X.X ⟶ Y.X) [IsComonHom f] :
    homA (UlmerBialgebras.CommComon.homMk f) = f := rfl

instance isComonHom_homA {X Y : CommComon A} (f : X ⟶ Y) : IsComonHom (homA f) :=
  UlmerBialgebras.CommComon.isComonHom_hom_hom f

/-- **Whiskering in `CommComon A` is whiskering in `A`.**  The product of Fox's theorem has the
tensor product of `A` as underlying object (definitionally), and a whiskered morphism has the
whiskered morphism of `A` as underlying morphism. -/
lemma homA_whiskerLeft (X : CommComon A) {Y Y' : CommComon A} (f : Y ⟶ Y') :
    homA (X ◁ f) = X.X ◁ homA f := by
  have h : X ◁ f = UlmerBialgebras.CommComon.tensorObjWhiskerLeft X f := by
    refine BinaryFan.IsLimit.hom_ext (UlmerBialgebras.CommComon.binaryFanIsLimit X Y') ?_ ?_
    · rw [UlmerBialgebras.CommComon.tensorObjWhiskerLeft_fst]
      exact CartesianMonoidalCategory.whiskerLeft_fst X f
    · rw [UlmerBialgebras.CommComon.tensorObjWhiskerLeft_snd]
      exact CartesianMonoidalCategory.whiskerLeft_snd X f
  rw [h]
  rfl

/-- A morphism of cocommutative comonoids whose underlying morphism is an epimorphism is an
epimorphism. -/
lemma epi_of_epi_homA {Y Y' : CommComon A} (f : Y ⟶ Y') [Epi (homA f)] : Epi f :=
  (UlmerBialgebras.CommComon.forgetV A).epi_of_epi_map (inferInstanceAs (Epi (homA f)))

/-- Whiskering preserves morphisms of cocommutative comonoids with epimorphic underlying
morphism, as soon as tensoring in `A` preserves epimorphisms. -/
instance epi_homA_whiskerLeft [∀ Z : A, (tensorLeft Z).PreservesEpimorphisms]
    (X : CommComon A) {Y Y' : CommComon A} (f : Y ⟶ Y') [Epi (homA f)] :
    Epi (homA (X ◁ f)) := by
  rw [homA_whiskerLeft]
  exact (tensorLeft X.X).map_epi (homA f)

variable {h : CommComon A} [MonObj h]

/-- The morphism of `A` underlying a morphism of `h`-modules in `CommComon A`. -/
def modHomA {N M : Mod (CommComon A) h} (f : N ⟶ M) : N.X.X ⟶ M.X.X := homA f.hom

/-- `modHomA` sends a composite of module maps to the composite in `A`. -/
@[simp]
lemma modHomA_comp {N M P : Mod (CommComon A) h} (f : N ⟶ M) (g : M ⟶ P) :
    modHomA (f ≫ g) = modHomA f ≫ modHomA g := rfl

/-- A module map is determined by its underlying morphism in `A`. -/
lemma modHomA_injective {N M : Mod (CommComon A) h} :
    Function.Injective (modHomA (N := N) (M := M)) :=
  fun _ _ hfg => Mod.hom_ext _ _ (homA_injective hfg)

instance isComonHom_modHomA {N M : Mod (CommComon A) h} (f : N ⟶ M) : IsComonHom (modHomA f) :=
  isComonHom_homA f.hom

/-- A morphism of `h`-modules in `CommComon A` whose underlying morphism of `A` is an
epimorphism is an epimorphism of `h`-modules. -/
lemma epi_of_epi_modHomA {N P : Mod (CommComon A) h} (p : N ⟶ P) [Epi (modHomA p)] : Epi p :=
  ⟨fun {_} _ _ huv => modHomA_injective
    ((cancel_epi (modHomA p)).1 (congrArg modHomA huv))⟩

end Underlying

/-! ## Descent of module maps along epimorphisms -/

section Descent

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ Z : A, (tensorLeft Z).PreservesEpimorphisms]
variable {h : CommComon A} [MonObj h]

/-- **Descent of module maps along epimorphisms of `A`.**  Let `p : N ⟶ P` and `f : N ⟶ M` be
morphisms of `h`-modules in `CommComon A` with `p` an epimorphism of `A`.  A morphism `g` of `A`
with `p ≫ g = f` underlies a morphism of `h`-modules. -/
theorem exists_hom_of_epi {N P M : Mod (CommComon A) h} (p : N ⟶ P) [Epi (modHomA p)]
    (f : N ⟶ M) (g : P.X.X ⟶ M.X.X) (hg : modHomA p ≫ g = modHomA f) :
    ∃ u : P ⟶ M, p ≫ u = f ∧ modHomA u = g := by
  have : IsComonHom g := isComonHom_of_epi_comp (modHomA p) (modHomA f) g hg
  let g' : P.X ⟶ M.X := UlmerBialgebras.CommComon.homMk g
  have hpg : p.hom ≫ g' = f.hom := homA_injective hg
  have : Epi (homA p.hom) := inferInstanceAs (Epi (modHomA p))
  have : Epi (h ◁ p.hom) := epi_of_epi_homA _
  have hp : (h ◁ p.hom) ≫ γ[h, P.X] = γ[h, N.X] ≫ p.hom :=
    (IsModHom.smul_hom (A := h) (f := p.hom)).symm
  have hf : γ[h, N.X] ≫ f.hom = (h ◁ f.hom) ≫ γ[h, M.X] :=
    IsModHom.smul_hom (A := h) (f := f.hom)
  have hsmul : γ[h, P.X] ≫ g' = (h ◁ g') ≫ γ[h, M.X] := by
    rw [← cancel_epi (h ◁ p.hom), reassoc_of% hp, hpg, hf, ← hpg,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact ⟨Mod.Hom.mk' g' hsmul, Mod.hom_ext _ _ hpg, rfl⟩

end Descent

/-! ## Comparing quotients by their kernels -/

section Kernels

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ Z : A, (tensorLeft Z).PreservesEpimorphisms]
variable {h : CommComon A} [MonObj h]

/-- **Quotients are compared by their kernels in `A`.**  For morphisms `p : N ⟶ P` and
`f : N ⟶ M` of `h`-modules in `CommComon A` with `p` an epimorphism of `A`, `f` factors through
`p` iff the kernel of `p` in `A` is contained in that of `f`. -/
theorem exists_comp_eq_iff_kernelSubobject_le {N P M : Mod (CommComon A) h} (p : N ⟶ P)
    [Epi (modHomA p)] (f : N ⟶ M) :
    (∃ u : P ⟶ M, p ≫ u = f) ↔ kernelSubobject (modHomA p) ≤ kernelSubobject (modHomA f) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact kernelSubobject_comp_le _ (modHomA u)
  · intro hle
    have hz : kernel.ι (modHomA p) ≫ modHomA f = 0 := by
      rw [← kernelSubobject_arrow', Category.assoc, ← Subobject.ofLE_arrow hle, Category.assoc,
        kernelSubobject_arrow_comp, comp_zero, comp_zero]
    obtain ⟨u, hu, -⟩ := exists_hom_of_epi p f (Abelian.epiDesc (modHomA p) (modHomA f) hz)
      (Abelian.comp_epiDesc (modHomA p) (modHomA f) hz)
    exact ⟨u, hu⟩

/-- **Quotient modules with `A`-epimorphic quotient maps are compared by their kernels in
`A`.** -/
theorem quot_le_iff_kernelSubobject_le (q q' : QuotMod h) [Epi (modHomA q.p)] :
    q ≤ q' ↔ kernelSubobject (modHomA q.p) ≤ kernelSubobject (modHomA q'.p) :=
  exists_comp_eq_iff_kernelSubobject_le q.p q'.p

/-- Two quotient modules with `A`-epimorphic quotient maps and the same kernel in `A` are
isomorphic as quotients, so one is a regular epimorphism iff the other is. -/
theorem isRegularEpi_of_kernelSubobject_eq {q q' : QuotMod h} [Epi (modHomA q.p)]
    [Epi (modHomA q'.p)]
    (hk : kernelSubobject (modHomA q.p) = kernelSubobject (modHomA q'.p))
    (hq : IsRegularEpi q.p) : IsRegularEpi q'.p := by
  obtain ⟨u, hu⟩ := (quot_le_iff_kernelSubobject_le q q').2 hk.le
  obtain ⟨v, hv⟩ := (quot_le_iff_kernelSubobject_le q' q).2 hk.ge
  have hvu : v ≫ u = 𝟙 q'.V := by
    refine (cancel_epi q'.p).1 ?_
    rw [Category.comp_id, ← Category.assoc, hv, hu]
  have huv : u ≫ v = 𝟙 q.V := by
    refine (cancel_epi q.p).1 ?_
    rw [Category.comp_id, ← Category.assoc, hu, hv]
  let e : Arrow.mk q.p ≅ Arrow.mk q'.p :=
    Arrow.isoMk (Iso.refl _) { hom := u, inv := v, hom_inv_id := huv, inv_hom_id := hvu }
      (by simp only [Iso.refl_hom, Category.id_comp]; exact hu.symm)
  exact ⟨⟨RegularEpi.ofArrowIso e hq.regularEpi.some⟩⟩

end Kernels

end InternalGroups
