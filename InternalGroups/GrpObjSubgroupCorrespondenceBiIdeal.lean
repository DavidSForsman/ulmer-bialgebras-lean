module

public import InternalGroups.GrpObjSubgroupCorrespondenceCocomm
public import InternalGroups.GrpStabilizerCoset
public import InternalGroups.GrpKernelImage
public import Foundations.CategoryTheory.Monoidal.CommComonReflexive
public import Foundations.CategoryTheory.Limits.MapRegularEpi
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import InternalGroups.CommComonModQuotient

/-!
# Newman's correspondence with bi-ideals

Let `A` be an abelian symmetric monoidal category whose tensor product is exact in each variable:
`[∀ X, PreservesFiniteLimits (tensorLeft X)]` and `[∀ X, PreservesFiniteColimits (tensorLeft X)]`
(the right-hand versions follow by symmetry).  Let `C = CommComon A` be its category of
cocommutative comonoids, cartesian monoidal by Fox's theorem, and let `h` be an internal group of
`C`, that is, a cocommutative Hopf monoid of `A`.

* A **sub-Hopf monoid** of `h` is a subgroup object `s : SubGrp h` of `h` in `C`.
* A **bi-ideal** of `h` is a subobject `I` of `h` in `A` which is the kernel, in `A`, of some
  morphism `h ⟶ M` of `h`-modules in `C` (`InternalGroups.IsBiIdeal`).

Newman's correspondence sends a subgroup object `s` to the kernel in `A` of its coset quotient
`h ⟶ h / s` (`InternalGroups.SubGrp.biIdeal`).  Conversely, a bi-ideal `I` is sent to the
stabilizer (pseudo-kernel) of the cokernel `h ⟶ h / I` of `I` in `A`
(`InternalGroups.BiIdeal.stab`).  Here the cokernel carries the structure of an `h`-module in `C`
for which `h ⟶ h / I` is a morphism of `h`-modules (`InternalGroups.BiIdeal.quot`,
`InternalGroups.BiIdeal.isColimitCokernelCofork`).  The two maps form a Galois connection
(`InternalGroups.galoisConnection_biIdeal_stab`).

## Main results

* `InternalGroups.biIdealMap_injective_iff_grpIsStabilizer`: the correspondence is injective on
  isomorphism classes of subgroup objects iff every subgroup object of `h` is a stabilizer.
  `InternalGroups.biIdealMap_injective_iff_mono` is the same statement for all monomorphisms of
  internal groups into `h`, and `InternalGroups.biIdealMap_injective_iff` the form
  `stab (h / s) ≤ s`.
* `InternalGroups.biIdealMap_surjective_iff`: the correspondence is surjective iff the quotient
  `h ⟶ h / I` by every bi-ideal `I` is a regular epimorphism of `h`-modules.
  `InternalGroups.biIdealMap_surjective_iff_epi` is the same statement for all quotient modules
  whose quotient map is an epimorphism of `A`.
* `InternalGroups.biIdealMap_bijective_iff`: both together.

## Method

Everything reduces to one comparison lemma,
`InternalGroups.exists_comp_eq_iff_kernelSubobject_le`.  Let `p : N ⟶ P` and `f : N ⟶ M` be
morphisms of `h`-modules in `C`, with `p` an epimorphism of `A`.  Then `f` factors through `p` iff
the kernel of `p` in `A` is contained in that of `f`.  The factorization exists in `A` because `A`
is abelian.  It is a morphism of `h`-modules in `C` by descent along `p`
(`InternalGroups.exists_hom_of_epi`), which uses that tensoring preserves epimorphisms.

The quotient `h / I` is the coimage in `A` of a module map witnessing `I`
(`InternalGroups.coimMod`).  Its comonoid structure and its action are obtained by lifting in
squares whose left side is an epimorphism and whose right side is a monomorphism of `A`.  This
uses that tensoring preserves monomorphisms.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj ComonObj

namespace InternalGroups

/-! ## The coimage of a module map -/

section Coimage

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
variable {h : CommComon A} [MonObj h] {N M : Mod (CommComon A) h} (f : N ⟶ M)

attribute [local instance] mono_tensorHom_of_preservesMonomorphisms

/-- The coimage, in `A`, of the morphism of `A` underlying a morphism of `h`-modules. -/
noncomputable abbrev coimObj : A := Abelian.coimage (modHomA f)

/-- The quotient map onto the coimage. -/
noncomputable abbrev coimπ : N.X.X ⟶ coimObj f := Abelian.coimage.π (modHomA f)

/-- The monomorphism from the coimage. -/
noncomputable abbrev coimι : coimObj f ⟶ M.X.X := Abelian.factorThruCoimage (modHomA f)

/-- The coimage factors `modHomA f` as `coimπ f ≫ coimι f`. -/
lemma coimπ_coimι : coimπ f ≫ coimι f = modHomA f := Abelian.coimage.fac _

/-- The counit of the coimage, restricted from `M`. -/
noncomputable def coimCounit : coimObj f ⟶ 𝟙_ A := coimι f ≫ ε[M.X.X]

/-- The counit of the coimage restricts along `coimπ f` to the counit of `N`. -/
lemma coimπ_coimCounit : coimπ f ≫ coimCounit f = ε[N.X.X] := by
  rw [coimCounit, ← Category.assoc, coimπ_coimι, IsComonHom.hom_counit]

/-- The square defining the comultiplication of the coimage. -/
lemma coimComulSq :
    CommSq (Δ[N.X.X] ≫ (coimπ f ⊗ₘ coimπ f)) (coimπ f) (coimι f ⊗ₘ coimι f)
      (coimι f ≫ Δ[M.X.X]) where
  w := by
    rw [Category.assoc, tensorHom_comp_tensorHom, coimπ_coimι, ← Category.assoc, coimπ_coimι,
      IsComonHom.hom_comul]

variable [∀ Z : A, (tensorLeft Z).PreservesMonomorphisms]
  [∀ Z : A, (tensorRight Z).PreservesMonomorphisms]

/-- The comultiplication of the coimage. -/
noncomputable def coimComul : coimObj f ⟶ coimObj f ⊗ coimObj f :=
  have : StrongEpi (coimπ f) := strongEpi_of_epi _
  (coimComulSq f).lift

/-- `coimπ f` is compatible with the comultiplications of `N` and of the coimage. -/
lemma coimπ_coimComul : coimπ f ≫ coimComul f = Δ[N.X.X] ≫ (coimπ f ⊗ₘ coimπ f) :=
  have : StrongEpi (coimπ f) := strongEpi_of_epi _
  (coimComulSq f).fac_left

/-- The comonoid structure of the coimage. -/
@[instance_reducible]
noncomputable def coimComonObj : ComonObj (coimObj f) :=
  comonObjOfEpi (coimπ f) (coimCounit f) (coimComul f) (coimπ_coimCounit f) (coimπ_coimComul f)

/-- The coimage as a cocommutative comonoid. -/
noncomputable def coimCommComon : CommComon A :=
  letI := coimComonObj f
  letI := isCommComonObj_comonObjOfEpi (coimπ f) (coimCounit f) (coimComul f)
    (coimπ_coimCounit f) (coimπ_coimComul f)
  ⟨coimObj f⟩

/-- The quotient map onto the coimage, as a morphism of cocommutative comonoids. -/
noncomputable def coimπC : N.X ⟶ coimCommComon f :=
  have : IsComonHom (M := N.X.X) (N := (coimCommComon f).X) (coimπ f) :=
    isComonHom_comonObjOfEpi (coimπ f) (coimCounit f) (coimComul f) (coimπ_coimCounit f)
      (coimπ_coimComul f)
  UlmerBialgebras.CommComon.homMk (A := N.X) (B := coimCommComon f) (coimπ f)

/-- The monomorphism from the coimage, as a morphism of cocommutative comonoids. -/
noncomputable def coimιC : coimCommComon f ⟶ M.X :=
  have : IsComonHom (M := N.X.X) (N := (coimCommComon f).X) (coimπ f) :=
    isComonHom_comonObjOfEpi (coimπ f) (coimCounit f) (coimComul f) (coimπ_coimCounit f)
      (coimπ_coimComul f)
  have : Epi (X := N.X.X) (Y := (coimCommComon f).X) (coimπ f) :=
    inferInstanceAs (Epi (coimπ f))
  have : IsComonHom (M := (coimCommComon f).X) (N := M.X.X) (coimι f) :=
    isComonHom_of_epi_comp (Y := (coimCommComon f).X) (coimπ f) (modHomA f) (coimι f)
      (coimπ_coimι f)
  UlmerBialgebras.CommComon.homMk (A := coimCommComon f) (B := M.X) (coimι f)

/-- The comonoid maps `coimπC f` and `coimιC f` compose to `f.hom`. -/
lemma coimπC_coimιC : coimπC f ≫ coimιC f = f.hom :=
  homA_injective (coimπ_coimι f)

instance : Epi (homA (coimπC f)) := inferInstanceAs (Epi (coimπ f))

instance : Mono (homA (coimιC f)) := inferInstanceAs (Mono (coimι f))

/-- The square defining the action of `h` on the coimage. -/
lemma coimActSq :
    CommSq (homA γ[h, N.X] ≫ homA (coimπC f)) (homA (h ◁ coimπC f)) (homA (coimιC f))
      (homA ((h ◁ coimιC f) ≫ γ[h, M.X])) where
  w := by
    have hC : γ[h, N.X] ≫ coimπC f ≫ coimιC f
        = (h ◁ coimπC f) ≫ (h ◁ coimιC f) ≫ γ[h, M.X] := by
      rw [coimπC_coimιC, ← MonoidalCategory.whiskerLeft_comp_assoc, coimπC_coimιC]
      exact IsModHom.smul_hom (A := h) (f := f.hom)
    simpa only [homA_comp, Category.assoc] using congr(homA $hC)

variable [∀ Z : A, (tensorLeft Z).PreservesEpimorphisms]

/-- The underlying morphism of `A` of the action of `h` on the coimage. -/
noncomputable def coimAct₀ : (h ⊗ coimCommComon f).X ⟶ (coimCommComon f).X :=
  have : StrongEpi (homA (h ◁ coimπC f)) := strongEpi_of_epi _
  (coimActSq f).lift

/-- `coimπ f` intertwines the action of `h` on `N` with the action `coimAct₀ f`. -/
lemma homA_whiskerLeft_coimπC_coimAct₀ :
    homA (h ◁ coimπC f) ≫ coimAct₀ f = homA γ[h, N.X] ≫ homA (coimπC f) :=
  have : StrongEpi (homA (h ◁ coimπC f)) := strongEpi_of_epi _
  (coimActSq f).fac_left

/-- `coimι f` intertwines the action `coimAct₀ f` with the action of `h` on `M`. -/
lemma coimAct₀_homA_coimιC :
    coimAct₀ f ≫ homA (coimιC f) = homA ((h ◁ coimιC f) ≫ γ[h, M.X]) :=
  have : StrongEpi (homA (h ◁ coimπC f)) := strongEpi_of_epi _
  (coimActSq f).fac_right

/-- The action of `h` on the coimage, as a morphism of cocommutative comonoids. -/
noncomputable def coimActC : h ⊗ coimCommComon f ⟶ coimCommComon f :=
  have : IsComonHom (coimAct₀ f) :=
    isComonHom_of_epi_comp (homA (h ◁ coimπC f)) (homA (γ[h, N.X] ≫ coimπC f)) (coimAct₀ f)
      (homA_whiskerLeft_coimπC_coimAct₀ f)
  UlmerBialgebras.CommComon.homMk (coimAct₀ f)

/-- `coimπC f` intertwines the action of `h` on `N` with the action `coimActC f`. -/
lemma whiskerLeft_coimπC_coimActC :
    (h ◁ coimπC f) ≫ coimActC f = γ[h, N.X] ≫ coimπC f :=
  homA_injective (homA_whiskerLeft_coimπC_coimAct₀ f)

/-- `coimιC f` intertwines the action `coimActC f` with the action of `h` on `M`. -/
lemma coimActC_coimιC :
    coimActC f ≫ coimιC f = (h ◁ coimιC f) ≫ γ[h, M.X] :=
  homA_injective (coimAct₀_homA_coimιC f)

/-- The `h`-module structure of the coimage. -/
@[instance_reducible]
noncomputable def coimModObj : ModObj h (coimCommComon f) where
  smul := coimActC f
  one_smul := by
    change η[h] ▷ coimCommComon f ≫ coimActC f = (λ_ (coimCommComon f)).hom
    have : Epi (𝟙_ (CommComon A) ◁ coimπC f) := epi_of_epi_homA _
    rw [← cancel_epi (𝟙_ (CommComon A) ◁ coimπC f), whisker_exchange_assoc,
      whiskerLeft_coimπC_coimActC, ModObj.one_smul_self_assoc, leftUnitor_naturality]
  mul_smul := by
    change μ[h] ▷ coimCommComon f ≫ coimActC f =
      (α_ h h (coimCommComon f)).hom ≫ h ◁ coimActC f ≫ coimActC f
    have : Epi ((h ⊗ h) ◁ coimπC f) := epi_of_epi_homA _
    rw [← cancel_epi ((h ⊗ h) ◁ coimπC f), whisker_exchange_assoc, whiskerLeft_coimπC_coimActC,
      ModObj.mul_smul_self_assoc, associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_coimπC_coimActC,
      MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_coimπC_coimActC]

/-- **The coimage of a module map, as an `h`-module.**  Its underlying object of `A` is the
coimage `coimage f` of the underlying morphism of `A`. -/
noncomputable def coimMod : Mod (CommComon A) h :=
  letI := coimModObj f
  ⟨coimCommComon f⟩

/-- The quotient map onto the coimage, as a morphism of `h`-modules. -/
noncomputable def coimModπ : N ⟶ coimMod f :=
  letI := coimModObj f
  Mod.Hom.mk' (M := N) (N := coimMod f) (coimπC f) (whiskerLeft_coimπC_coimActC f).symm

/-- The monomorphism from the coimage, as a morphism of `h`-modules. -/
noncomputable def coimModι : coimMod f ⟶ M :=
  letI := coimModObj f
  Mod.Hom.mk' (M := coimMod f) (N := M) (coimιC f) (coimActC_coimιC f)

/-- **Image factorization of a module map.** -/
lemma coimModπ_coimModι : coimModπ f ≫ coimModι f = f :=
  modHomA_injective (coimπ_coimι f)

instance : Epi (modHomA (coimModπ f)) := inferInstanceAs (Epi (coimπ f))

instance : Mono (modHomA (coimModι f)) := inferInstanceAs (Mono (coimι f))

/-- The kernel in `A` of the quotient map onto the coimage is the kernel of the module map. -/
lemma kernelSubobject_coimModπ :
    kernelSubobject (modHomA (coimModπ f)) = kernelSubobject (modHomA f) := by
  rw [← kernelSubobject_comp_mono (modHomA (coimModπ f)) (modHomA (coimModι f))]
  congr 1
  exact (modHomA_comp _ _).symm.trans congr(modHomA $(coimModπ_coimModι f))

end Coimage

/-! ## Kernel subobjects of epimorphisms -/

section KernelSubobject

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The arrow of the kernel subobject of a morphism is a kernel of it. -/
noncomputable def isLimitKernelForkKernelSubobject {X Y : A} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelSubobject f).arrow (kernelSubobject_arrow_comp f)) :=
  KernelFork.IsLimit.ofι _ _ (fun g hg => factorThruKernelSubobject f g hg)
    (fun g hg => factorThruKernelSubobject_comp_arrow f g hg)
    (fun g hg m hm => by
      rw [← cancel_mono (kernelSubobject f).arrow, hm, factorThruKernelSubobject_comp_arrow])

/-- In an abelian category, an epimorphism is a cokernel of any subobject equal to its kernel. -/
noncomputable def isColimitCokernelCoforkOfKernelSubobjectEq {X Y : A} (f : X ⟶ Y) [Epi f]
    (S : Subobject X) (hS : kernelSubobject f = S) :
    IsColimit (CokernelCofork.ofπ (f := S.arrow) f
      (by subst hS; exact kernelSubobject_arrow_comp f)) := by
  subst hS
  exact Abelian.epiIsCokernelOfKernel _ (isLimitKernelForkKernelSubobject f)

end KernelSubobject

/-! ## Bi-ideals and their quotients -/

section BiIdeals

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
variable {h : CommComon A} [MonObj h]

variable (h) in
/-- A **bi-ideal** of an internal monoid `h` of `CommComon A` (for an internal group: a
cocommutative Hopf monoid of `A`): a subobject of `h` in `A` which is the kernel, in `A`, of a
morphism `h ⟶ M` of `h`-modules in `CommComon A`. -/
def IsBiIdeal (I : Subobject h.X) : Prop :=
  ∃ (M : Mod (CommComon A) h) (f : selfMod h ⟶ M), kernelSubobject (modHomA f) = I

variable (h) in
/-- The **bi-ideals** of `h`, ordered by inclusion. -/
abbrev BiIdeal := {I : Subobject h.X // IsBiIdeal h I}

namespace BiIdeal

/-- The target of a chosen module map witnessing a bi-ideal. -/
noncomputable def mod (I : BiIdeal h) : Mod (CommComon A) h := I.2.choose

/-- A chosen module map out of `h` whose kernel in `A` is the bi-ideal. -/
noncomputable def map (I : BiIdeal h) : selfMod h ⟶ I.mod := I.2.choose_spec.choose

/-- A bi-ideal is the kernel in `A` of its chosen witnessing module map `I.map`. -/
lemma kernelSubobject_map (I : BiIdeal h) : kernelSubobject (modHomA I.map) = I.1 :=
  I.2.choose_spec.choose_spec

variable [∀ Z : A, (tensorLeft Z).PreservesEpimorphisms]
  [∀ Z : A, (tensorLeft Z).PreservesMonomorphisms] [∀ Z : A, (tensorRight Z).PreservesMonomorphisms]

/-- **The quotient of `h` by a bi-ideal** `I`, as a quotient `h`-module in `CommComon A`.  Its
underlying morphism of `A` is the cokernel of `I` in `A`
(`InternalGroups.BiIdeal.isColimitCokernelCofork`); the structure of an `h`-module in
`CommComon A` is induced from that of any module map witnessing `I`. -/
noncomputable def quot (I : BiIdeal h) : QuotMod h where
  V := coimMod I.map
  p := coimModπ I.map
  epi_p := epi_of_epi_modHomA _

instance (I : BiIdeal h) : Epi (modHomA I.quot.p) :=
  inferInstanceAs (Epi (modHomA (coimModπ I.map)))

/-- The kernel in `A` of the quotient by a bi-ideal is the bi-ideal. -/
lemma kernelSubobject_quot (I : BiIdeal h) : kernelSubobject (modHomA I.quot.p) = I.1 :=
  (kernelSubobject_coimModπ I.map).trans I.kernelSubobject_map

/-- **The quotient by a bi-ideal is the cokernel in `A` of the bi-ideal.** -/
noncomputable def isColimitCokernelCofork (I : BiIdeal h) :
    IsColimit (CokernelCofork.ofπ (f := I.1.arrow) (modHomA I.quot.p)
      (by rw [← I.kernelSubobject_quot]; exact kernelSubobject_arrow_comp _)) :=
  isColimitCokernelCoforkOfKernelSubobjectEq _ _ I.kernelSubobject_quot

end BiIdeal

end BiIdeals

/-! ## Newman's correspondence with bi-ideals -/

section Correspondence

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ X : A, PreservesFiniteLimits (tensorLeft X)] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

attribute [local instance] preservesFiniteLimits_tensorRight_of_left
  preservesFiniteColimits_tensorRight_of_left
  tensorPreservesCoreflexiveEqualizers_of_preservesFiniteLimits
  preservesReflexiveCoeq_tensorLeft_of_preservesFiniteColimits

variable {h : CommComon A} [GrpObj h]

/-- The coset quotient of a subgroup object is an epimorphism of `A`: it is a reflexive
coequalizer of `CommComon A`, and the forgetful functor to `A` preserves those. -/
instance epi_modHomA_quot_p (s : SubGrp h) : Epi (modHomA s.quot.p) := by
  have : IsRegularEpi s.quot.p.hom := isRegularEpi_quot_p_hom s
  have : IsRegularEpi ((UlmerBialgebras.CommComon.forgetV A).map s.quot.p.hom) :=
    isRegularEpi_map_of_preservesReflexiveCoeq _ s.quot.p.hom
  exact inferInstanceAs (Epi ((UlmerBialgebras.CommComon.forgetV A).map s.quot.p.hom))

/-- **The stabilizer of a bi-ideal** `I`: the stabilizer (pseudo-kernel) of the base point of the
quotient `h ⟶ h / I`, a subgroup object of `h`. -/
noncomputable def BiIdeal.stab (I : BiIdeal h) : SubGrp h := InternalGroups.stab I.quot

/-- **The bi-ideal of a subgroup object** `s` of `h`: the kernel, in `A`, of the coset quotient
`h ⟶ h / s`. -/
noncomputable def SubGrp.biIdeal (s : SubGrp h) : BiIdeal h :=
  ⟨kernelSubobject (modHomA s.quot.p), _, s.quot.p, rfl⟩

/-- **The bi-ideal correspondence is a Galois connection**: `biIdeal s ≤ I ↔ s ≤ stab I`. -/
theorem SubGrp.biIdeal_le_iff (s : SubGrp h) (I : BiIdeal h) : s.biIdeal ≤ I ↔ s ≤ I.stab :=
  calc s.biIdeal ≤ I
      ↔ kernelSubobject (modHomA s.quot.p) ≤ kernelSubobject (modHomA I.quot.p) := by
        rw [BiIdeal.kernelSubobject_quot]; rfl
    _ ↔ s.quot ≤ I.quot := (quot_le_iff_kernelSubobject_le s.quot I.quot).symm
    _ ↔ s ≤ I.stab := galoisConnection_quot_stab.le_iff_le

/-- The bi-ideal map and the stabilizer of bi-ideals form a Galois connection. -/
theorem galoisConnection_biIdeal_stab :
    GaloisConnection (fun s : SubGrp h => s.biIdeal) (fun I : BiIdeal h => I.stab) :=
  fun s I => s.biIdeal_le_iff I

variable (h) in
/-- **Newman's bi-ideal map** on isomorphism classes of subgroup objects: the class of `s` is
sent to the kernel, in `A`, of the coset quotient `h ⟶ h / s`. -/
noncomputable def biIdealMap : Antisymmetrization (SubGrp h) (· ≤ ·) → BiIdeal h :=
  Quotient.lift (fun s : SubGrp h => s.biIdeal) fun _ _ hst =>
    le_antisymm (galoisConnection_biIdeal_stab.monotone_l hst.1)
      (galoisConnection_biIdeal_stab.monotone_l hst.2)

/-- The bi-ideal map sends the class of `s` to the kernel of the coset quotient `h ⟶ h / s`. -/
lemma biIdealMap_mk_val (s : SubGrp h) :
    (biIdealMap h (Quotient.mk _ s)).1 = kernelSubobject (modHomA s.quot.p) := rfl

/-! ### Injectivity: every subgroup object is a stabilizer -/

/-- **Injectivity of the bi-ideal correspondence is coset injectivity**: the bi-ideal map is
injective iff every subgroup object `s` of `h` is recovered from its coset quotient,
`stab (h / s) ≤ s`. -/
theorem biIdealMap_injective_iff :
    Function.Injective (biIdealMap h) ↔ ∀ s : SubGrp h, stab s.quot ≤ s := by
  constructor
  · intro hinj s
    have h₂ : s.quot ≤ (stab s.quot).quot :=
      galoisConnection_quot_stab.monotone_l (le_stab_quot s)
    have h₃ : (stab s.quot).quot ≤ s.quot := quot_stab_le s.quot
    have heq : s.biIdeal = (stab s.quot).biIdeal :=
      Subtype.ext (le_antisymm ((quot_le_iff_kernelSubobject_le _ _).1 h₂)
        ((quot_le_iff_kernelSubobject_le _ _).1 h₃))
    exact (Quotient.exact (hinj (a₁ := Quotient.mk _ s) (a₂ := Quotient.mk _ (stab s.quot))
      heq)).2
  · intro hstab
    refine Quotient.ind₂ fun s t hst => Quotient.sound ?_
    have hk : kernelSubobject (modHomA s.quot.p) = kernelSubobject (modHomA t.quot.p) :=
      Subtype.ext_iff.1 (show s.biIdeal = t.biIdeal from hst)
    have hst' : s.quot ≤ t.quot := (quot_le_iff_kernelSubobject_le _ _).2 hk.le
    have hts' : t.quot ≤ s.quot := (quot_le_iff_kernelSubobject_le _ _).2 hk.ge
    exact ⟨(le_stab_quot s).trans ((galoisConnection_quot_stab.monotone_u hst').trans (hstab t)),
      (le_stab_quot t).trans ((galoisConnection_quot_stab.monotone_u hts').trans (hstab s))⟩

/-- **Every subgroup object is a stabilizer iff every subgroup object is recovered from its coset
quotient.** -/
theorem forall_grpIsStabilizer_iff :
    (∀ s : SubGrp h, GrpIsStabilizer s.inclGrp) ↔ ∀ s : SubGrp h, stab s.quot ≤ s := by
  constructor
  · intro H s
    exact stab_quot_le_of_grpIsStabilizer s (H s)
  · intro H s
    exact (isGrpStabilizer_stab (G := Grp.mk h) s.quot).of_iso
      (SubGrp.isoOfLe (le_stab_quot s) (H s)) (SubGrp.isoOfLe_hom_inclGrp _ _)

/-- **Injectivity of Newman's bi-ideal correspondence is the property that every subgroup
object (sub-Hopf monoid) of `h` is a stabilizer.** -/
theorem biIdealMap_injective_iff_grpIsStabilizer :
    Function.Injective (biIdealMap h) ↔ ∀ s : SubGrp h, GrpIsStabilizer s.inclGrp :=
  biIdealMap_injective_iff.trans forall_grpIsStabilizer_iff.symm

omit [∀ X : A, PreservesFiniteColimits (tensorLeft X)] in
/-- **Every monomorphism of internal groups into `h` is a stabilizer iff every subgroup object of
`h` is.** -/
theorem forall_mono_grpIsStabilizer_iff :
    (∀ (X : Grp (CommComon A)) (m : X ⟶ Grp.mk h), Mono m → GrpIsStabilizer m) ↔
      ∀ s : SubGrp h, GrpIsStabilizer s.inclGrp := by
  constructor
  · intro H s
    exact H _ _ ((Grp.forget _).mono_of_mono_map s.mono_i)
  · intro H X m hm
    have : Mono m.hom.hom := mono_hom_of_mono m
    let s : SubGrp h := ⟨X.X, m.hom.hom⟩
    have hs : s.inclGrp = m := rfl
    exact (H s).of_iso (Iso.refl X) ((Category.id_comp s.inclGrp).trans hs)

/-- **Injectivity of Newman's bi-ideal correspondence is the property that every monomorphism of
internal groups into `h` is a stabilizer.** -/
theorem biIdealMap_injective_iff_mono :
    Function.Injective (biIdealMap h) ↔
      ∀ (X : Grp (CommComon A)) (m : X ⟶ Grp.mk h), Mono m → GrpIsStabilizer m :=
  biIdealMap_injective_iff_grpIsStabilizer.trans forall_mono_grpIsStabilizer_iff.symm

/-! ### Surjectivity: the bi-ideal quotients are regular -/

/-- **Surjectivity of Newman's bi-ideal correspondence is the property that the quotient of `h`
by every bi-ideal is a regular epimorphism of `h`-modules.** -/
theorem biIdealMap_surjective_iff :
    Function.Surjective (biIdealMap h) ↔ ∀ I : BiIdeal h, IsRegularEpi I.quot.p := by
  constructor
  · intro hsur I
    obtain ⟨x, hx⟩ := hsur I
    obtain ⟨s, rfl⟩ := Quotient.exists_rep x
    have hk : kernelSubobject (modHomA s.quot.p) = kernelSubobject (modHomA I.quot.p) := by
      rw [BiIdeal.kernelSubobject_quot]
      exact Subtype.ext_iff.1 (show s.biIdeal = I from hx)
    exact isRegularEpi_of_kernelSubobject_eq hk ⟨⟨SubGrp.regularEpiQuot s⟩⟩
  · intro hreg I
    refine ⟨Quotient.mk _ I.stab, Subtype.ext ?_⟩
    rw [biIdealMap_mk_val]
    rw [← BiIdeal.kernelSubobject_quot]
    exact le_antisymm ((quot_le_iff_kernelSubobject_le _ _).1 (quot_stab_le I.quot))
      ((quot_le_iff_kernelSubobject_le _ _).1 (le_quot_stab I.quot (hreg I).regularEpi.some))

/-- The bi-ideal quotients are, up to isomorphism, exactly the quotient modules whose quotient map
is an epimorphism of `A`; so they are all regular iff every such quotient is regular. -/
theorem forall_isRegularEpi_quot_iff :
    (∀ I : BiIdeal h, IsRegularEpi I.quot.p) ↔
      ∀ q : QuotMod h, Epi (modHomA q.p) → IsRegularEpi q.p := by
  constructor
  · intro H q hq
    let I : BiIdeal h := ⟨kernelSubobject (modHomA q.p), _, q.p, rfl⟩
    exact isRegularEpi_of_kernelSubobject_eq (I.kernelSubobject_quot) (H I)
  · intro H I
    exact H I.quot inferInstance

/-- **Surjectivity of Newman's bi-ideal correspondence is the property that every quotient module
of `h` whose quotient map is an epimorphism of `A` is a regular epimorphism of `h`-modules.** -/
theorem biIdealMap_surjective_iff_epi :
    Function.Surjective (biIdealMap h) ↔
      ∀ q : QuotMod h, Epi (modHomA q.p) → IsRegularEpi q.p :=
  biIdealMap_surjective_iff.trans forall_isRegularEpi_quot_iff

/-- **Newman's bi-ideal correspondence is bijective iff every subgroup object of `h` is a
stabilizer and the quotient of `h` by every bi-ideal is a regular epimorphism.** -/
theorem biIdealMap_bijective_iff :
    Function.Bijective (biIdealMap h) ↔
      (∀ s : SubGrp h, GrpIsStabilizer s.inclGrp) ∧ ∀ I : BiIdeal h, IsRegularEpi I.quot.p :=
  and_congr biIdealMap_injective_iff_grpIsStabilizer biIdealMap_surjective_iff

end Correspondence


end InternalGroups
