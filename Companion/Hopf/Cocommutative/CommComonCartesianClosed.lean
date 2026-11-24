module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Isomorphisms
public import Companion.Foundations.CategoryTheory.Monoidal.CommComonClosed
public import Hopf.Basic.CoalgebraLocallyFinite
public import Hopf.Cocommutative.Subcoalgebra
public import Hopf.Mathlib.CocommEquivalence
public import InternalGroups.GrpObjSubgroupCorrespondenceBiIdeal

/-!
# Cocommutative coalgebras over a field form a cartesian closed category

Let `k` be a field.  The category `CommComon (ModuleCat k)` of cocommutative `k`-coalgebras is
cartesian monoidal, its product being the tensor product of coalgebras.  This file proves that
it is cartesian closed, by the special adjoint functor theorem
(`UlmerBialgebras.CommComon.monoidalClosed`).  The two hypotheses that are particular to
`ModuleCat k` are discharged here.

* **Co-well-poweredness.**  An epimorphism of cocommutative coalgebras is surjective, since the
  forgetful functor preserves pushouts.  Two epimorphisms out of `X` with the same kernel differ
  by a linear isomorphism, which is a coalgebra isomorphism because comonoid morphisms descend
  along epimorphic ones (`InternalGroups.isComonHom_of_epi_comp`).  So a quotient of `X` is
  determined by its kernel, a submodule of `X`.
* **A small separating family.**  By the fundamental theorem of coalgebras
  (`Coalgebra.LocallyFinite.exists_fg_subcoalgebra`), every element of a cocommutative coalgebra
  lies in a finite-dimensional subcoalgebra, which is again cocommutative.  A finite-dimensional
  coalgebra is isomorphic to one carried by some `Fin n → k`, and the cocommutative coalgebra
  structures on these modules form a small family.

## Main results

* `UlmerBialgebras.CommComon.wellPowered_op_moduleCat` — `CommComon (ModuleCat k)` is
  co-well-powered;
* `UlmerBialgebras.CommComon.exists_finiteDimensional_hom` — every element of a cocommutative
  coalgebra is in the image of a finite-dimensional cocommutative coalgebra;
* `UlmerBialgebras.CommComon.isSeparating_finFamily` — the cocommutative coalgebras carried by
  the modules `Fin n → k` form a small separating family;
* `UlmerBialgebras.CommComon.monoidalClosed_moduleCat` — `CommComon (ModuleCat k)` is cartesian
  closed.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory Limits

namespace CommComon

variable {k : Type u} [Field k]

/-! ## Co-well-poweredness -/

/-- An epimorphism of cocommutative coalgebras is surjective. -/
lemma surjective_of_epi {X Y : CategoryTheory.CommComon (ModuleCat.{u} k)} (f : X ⟶ Y)
    [Epi f] : Function.Surjective ((forgetV _).map f).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- Two epimorphisms of cocommutative coalgebras out of `X` with the same kernel differ by an
isomorphism. -/
lemma exists_iso_of_ker_eq {X S T : CategoryTheory.CommComon (ModuleCat.{u} k)}
    (p : X ⟶ S) (q : X ⟶ T) [Epi p] [Epi q]
    (h : LinearMap.ker ((forgetV _).map p).hom = LinearMap.ker ((forgetV _).map q).hom) :
    ∃ e : T ≅ S, q ≫ e.hom = p := by
  let p' := ((forgetV _).map p).hom
  let q' := ((forgetV _).map q).hom
  have hp : Function.Surjective p' := surjective_of_epi p
  have hq : Function.Surjective q' := surjective_of_epi q
  let e : T.X ≃ₗ[k] S.X := (q'.quotKerEquivOfSurjective hq).symm.trans
      ((Submodule.quotEquivOfEq _ _ h.symm).trans (p'.quotKerEquivOfSurjective hp))
  have he : ∀ x, e (q' x) = p' x := fun x => by
    have : (q'.quotKerEquivOfSurjective hq).symm (q' x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 (q'.quotKerEquivOfSurjective_apply_mk hq x).symm
    change p'.quotKerEquivOfSurjective hp (Submodule.quotEquivOfEq _ _ h.symm
      ((q'.quotKerEquivOfSurjective hq).symm (q' x))) = p' x
    rw [this]
    rfl
  let f : T.X ⟶ S.X := ModuleCat.ofHom e.toLinearMap
  let g : S.X ⟶ T.X := ModuleCat.ofHom e.symm.toLinearMap
  let p₀ : X.X ⟶ S.X := (forgetV _).map p
  let q₀ : X.X ⟶ T.X := (forgetV _).map q
  have hf : q₀ ≫ f = p₀ := by ext x; exact he x
  have hg : p₀ ≫ g = q₀ := by
    ext x; exact (LinearEquiv.symm_apply_eq _).2 (he x).symm
  have : Epi q₀ := inferInstanceAs (Epi ((forgetV _).map q))
  have : Epi p₀ := inferInstanceAs (Epi ((forgetV _).map p))
  have : IsComonHom q₀ := inferInstanceAs (IsComonHom q.hom.hom)
  have : IsComonHom p₀ := inferInstanceAs (IsComonHom p.hom.hom)
  have : IsComonHom f := InternalGroups.isComonHom_of_epi_comp q₀ p₀ f hf
  have : IsComonHom g := InternalGroups.isComonHom_of_epi_comp p₀ q₀ g hg
  refine ⟨⟨homMk f, homMk g, ?_, ?_⟩, ?_⟩
  · ext x; exact e.symm_apply_apply x
  · ext x; exact e.apply_symm_apply x
  · ext x; exact he x

/-- **`CommComon (ModuleCat k)` is co-well-powered**: a quotient of a cocommutative coalgebra is
determined by its kernel. -/
instance wellPowered_op_moduleCat :
    WellPowered.{u} (CategoryTheory.CommComon (ModuleCat.{u} k))ᵒᵖ where
  subobject_small X := by
    let φ : Subobject X → Submodule k X.unop.X := fun s =>
      LinearMap.ker ((forgetV _).map s.arrow.unop).hom
    refine small_of_injective (f := φ) fun s t h => ?_
    obtain ⟨e, he⟩ := exists_iso_of_ker_eq s.arrow.unop t.arrow.unop h
    exact Subobject.eq_of_comm e.op (Quiver.Hom.unop_inj he)

/-! ## A small separating family -/

/-- **Every element of a cocommutative coalgebra is in the image of a finite-dimensional
cocommutative coalgebra**, by the fundamental theorem of coalgebras. -/
lemma exists_finiteDimensional_hom (X : CategoryTheory.CommComon (ModuleCat.{u} k)) (x : X.X) :
    ∃ (G : CategoryTheory.CommComon (ModuleCat.{u} k)) (_ : FiniteDimensional k G.X) (h : G ⟶ X),
      x ∈ LinearMap.range ((forgetV _).map h).hom := by
  let C : CoalgCat.{u} k := (CoalgCat.ofComon k).obj X.toComon
  have : Coalgebra.IsCocomm k C := (CoalgCat.ofComon_isCocomm_iff X.toComon).2 X.comm
  obtain ⟨E, hxE, hfg, hE⟩ := Coalgebra.LocallyFinite.exists_fg_subcoalgebra (k := k) (C := C) x
  let := Subcoalg.subCoalgebra hE
  have : Coalgebra.IsCocomm k E := ⟨Subcoalg.subComul_comm hE⟩
  let ι : E →ₗc[k] C :=
    { E.subtype with
      counit_comp := rfl
      map_comp_comul := Subcoalg.map_subtype_comp_subComul hE }
  let G := CoalgCat.toCommComonObj (CoalgCat.of k E)
  have : IsComonHom (C := ModuleCat.{u} k) (M := G.X) (N := X.X) (ModuleCat.ofHom E.subtype) :=
    ((CoalgCat.toComon k).map (CoalgCat.ofHom ι)).isComonHom_hom
  exact ⟨G, Module.Finite.iff_fg.2 hfg, homMk (ModuleCat.ofHom E.subtype), ⟨x, hxE⟩, rfl⟩

variable (k) in
/-- The index type of the separating family: a natural number `n` and a cocommutative comonoid
structure on `Fin n → k`. -/
abbrev FinIndex : Type u :=
  Σ' (n : ℕ) (c : ComonObj (ModuleCat.of k (Fin n → k))),
    @IsCommComonObj _ _ _ _ (ModuleCat.of k (Fin n → k)) c

variable (k) in
/-- The cocommutative coalgebra carried by `Fin n → k` with a given structure. -/
def finFamily (i : FinIndex k) : CategoryTheory.CommComon (ModuleCat.{u} k) :=
  letI := i.2.1
  letI := i.2.2
  ⟨ModuleCat.of k (Fin i.1 → k)⟩

variable (k) in
/-- **The cocommutative coalgebras carried by the modules `Fin n → k` form a separating
family.** -/
theorem isSeparating_finFamily : (ObjectProperty.ofObj (finFamily k)).IsSeparating := by
  intro X Y f g H
  ext x
  obtain ⟨G, hG, h, y, rfl⟩ := exists_finiteDimensional_hom X x
  let e : G.X ≅ ModuleCat.of k (Fin (Module.finrank k G.X) → k) :=
    (Module.finBasis k G.X).equivFun.toModuleIso
  have hmem : ObjectProperty.ofObj (finFamily k) (ofIso G e) :=
    ObjectProperty.ofObj.mk (X := finFamily k)
      ⟨_, ComonObj.ofIso e, ComonObj.isCommComonObj_ofIso e⟩
  have := H _ hmem ((isoOfIso G e).inv ≫ h)
  rw [Category.assoc, Category.assoc, cancel_epi] at this
  exact congr(($this).hom.hom.hom y)

/-! ## Cartesian closedness -/

/-- **The category of cocommutative coalgebras over a field is cartesian closed.** -/
noncomputable instance monoidalClosed_moduleCat :
    MonoidalClosed (CategoryTheory.CommComon (ModuleCat.{u} k)) :=
  monoidalClosed (isSeparating_finFamily k)

end CommComon

end UlmerBialgebras
