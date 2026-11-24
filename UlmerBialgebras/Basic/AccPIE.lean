module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import UlmerBialgebras.Basic.AccPi
public import UlmerBialgebras.Basic.AccInsEq

/-!
# `Acc` and the PIE limits of `CAT`

This file assembles the results of `AccPi.lean` and `AccInsEq.lean` about the closure of
accessible categories under the three PIE limits of `CAT` (products, inserters, equifiers).

For a fixed regular cardinal `κ`:

* **Products** (fully proved, `UlmerBialgebras.Pi.isCardinalAccessibleCategory`): if
  `HasCardinalLT ι κ` and each `C i` is `κ`-accessible, then `∀ i, C i` is `κ`-accessible;
  the projections and the induced functors are `κ`-accessible.

* **Inserters and equifiers**: the inserter `Ins F G` and the equifier `Equif η θ` of
  `κ`-accessible functors have `κ`-filtered colimits, created by the forgetful functors,
  which are themselves `κ`-accessible, as are the induced functors; moreover the candidate
  generating families
  `UlmerBialgebras.Ins.gen F G κ` (objects `⟨x, ψ⟩` with `x` and `F x` `κ`-presentable) and
  `UlmerBialgebras.Equif.gen η θ κ` (objects that are `κ`-presentable in `C`) consist of
  `κ`-presentable objects and are essentially small.  Consequently accessibility of the
  inserter and of the equifier is reduced to the *generation* step, i.e. to the statement
  that every object is a `κ`-filtered colimit of objects of the generating family
  (`UlmerBialgebras.Ins.isCardinalAccessibleCategory`,
  `UlmerBialgebras.Equif.isCardinalAccessibleCategory`).

The generation step is the part of the classical Makkai–Paré limit theorem that genuinely
needs a *second* cardinal `λ` with `λ ⊲ κ` (sharply less) and a closure argument inside a
`λ`-directed diagram; it is carried out in `AccessibleInserter.lean` and
`AccessibleEquifier.lean`, and the resulting unconditional statements are assembled in
`AccClosure.lean`.

## Main results

* `UlmerBialgebras.Ins.gen`, `UlmerBialgebras.Equif.gen`: the candidate generating families of the
  inserter and of the equifier.
* `UlmerBialgebras.Ins.isCardinalAccessibleCategory`: if every object of the inserter of two
  `κ`-accessible functors is a `κ`-filtered colimit of objects of `UlmerBialgebras.Ins.gen F G κ`,
  then the inserter is a `κ`-accessible category.
* `UlmerBialgebras.Equif.isCardinalAccessibleCategory`: the same for the equifier and
  `UlmerBialgebras.Equif.gen η θ κ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 2.3 and Theorem 5.11
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC],
  2.72 Theorem, 2.76 Lemma
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}

/-! ## Inserters -/

namespace Ins

/-- The candidate generating family of the inserter: objects `⟨x, ψ⟩` such that `x` is
`κ`-presentable in `C` and `F x` is `κ`-presentable in `D`. -/
def gen (F G : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] : ObjectProperty (Ins F G) :=
  fun x => IsCardinalPresentable x.pt κ ∧ IsCardinalPresentable (F.obj x.pt) κ

/-- Transport of an inserter object along an isomorphism of the underlying object. -/
@[simps]
def transportIso {x : Ins F G} {y : C} (e : x.pt ≅ y) : Ins F G :=
  ⟨y, F.map e.inv ≫ x.cell ≫ G.map e.hom⟩

/-- An inserter object is isomorphic to its transport along an isomorphism. -/
noncomputable def isoTransportIso {x : Ins F G} {y : C} (e : x.pt ≅ y) : x ≅ transportIso e := by
  have hw : x.cell ≫ G.map (e.hom : x.pt ⟶ (transportIso e).pt) =
      F.map (e.hom : x.pt ⟶ (transportIso e).pt) ≫ (transportIso e).cell := by
    simp
  let f : x ⟶ transportIso e := ⟨e.hom, hw⟩
  have h1 : IsIso ((forget F G).map f) := by rw [forget_map]; exact inferInstanceAs (IsIso e.hom)
  have : IsIso f := isIso_of_reflects_iso _ (forget F G)
  exact asIso f

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The candidate generating family of the inserter is essentially small. -/
instance gen_essentiallySmall [LocallySmall.{w} D]
    [ObjectProperty.EssentiallySmall.{w} (CategoryTheory.isCardinalPresentable C κ)] :
    ObjectProperty.EssentiallySmall.{w} (gen F G κ) := by
  obtain ⟨Q₀, _, -, hle⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le.{w}
      (CategoryTheory.isCardinalPresentable C κ)
  refine ⟨fun z => Q₀ z.pt, ?_, ?_⟩
  · have : Small.{w} (Σ (x : Subtype Q₀), (F.obj x.1 ⟶ G.obj x.1)) := inferInstance
    exact small_of_injective
      (f := fun (z : Subtype (fun z : Ins F G => Q₀ z.pt)) =>
        (⟨⟨z.1.pt, z.2⟩, z.1.cell⟩ : Σ (x : Subtype Q₀), (F.obj x.1 ⟶ G.obj x.1)))
      (by rintro ⟨⟨a, ca⟩, ha⟩ ⟨⟨b, cb⟩, hb⟩ h
          simp only [Sigma.mk.injEq, Subtype.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          simp_all)
  · rintro x ⟨hx, -⟩
    obtain ⟨y, hy, ⟨e⟩⟩ := hle x.pt hx
    exact ⟨transportIso e, hy, ⟨isoTransportIso e⟩⟩

/-- **Accessibility of the inserter, reduced to the generation step.**  If every object of
the inserter of two `κ`-accessible functors is a `κ`-filtered colimit of objects of
`UlmerBialgebras.Ins.gen F G κ`, then the inserter is a `κ`-accessible category. -/
theorem isCardinalAccessibleCategory [IsCardinalAccessibleCategory.{w} C κ]
    [LocallySmall.{w} D] [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    (hgen : ∀ x : Ins F G, ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      (gen F G κ).colimitsOfShape J x) :
    IsCardinalAccessibleCategory.{w} (Ins F G) κ := by
  have hg : (gen F G κ).IsCardinalFilteredGenerator κ :=
    { le_isCardinalPresentable := by
        rintro x ⟨h₁, h₂⟩
        exact Ins.isCardinalPresentable x
      exists_colimitsOfShape := hgen }
  exact
    { toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator
      toHasCardinalFilteredColimits := inferInstance }

end Ins

/-! ## Equifiers -/

namespace Equif

variable {η θ : F ⟶ G}

/-- The candidate generating family of the equifier: the objects that are `κ`-presentable
in the ambient category. -/
def gen (η θ : F ⟶ G) (κ : Cardinal.{w}) [Fact κ.IsRegular] : ObjectProperty (Equif η θ) :=
  fun x => IsCardinalPresentable x.obj κ

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The equifier is closed under isomorphisms in `C`. -/
lemma equifProp_of_iso {x : C} (hx : equifProp η θ x) {y : C} (e : x ≅ y) :
    equifProp η θ y := by
  have h1 := η.naturality e.hom
  have h2 := θ.naturality e.hom
  -- (membership in `equifProp η θ` is the equation `η.app y = θ.app y`)
  refine (cancel_epi (F.map e.hom)).mp ?_
  rw [h1, h2, hx]

/-- The candidate generating family of the equifier is essentially small. -/
instance gen_essentiallySmall
    [ObjectProperty.EssentiallySmall.{w} (CategoryTheory.isCardinalPresentable C κ)] :
    ObjectProperty.EssentiallySmall.{w} (gen η θ κ) := by
  obtain ⟨Q₀, _, -, hle⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le.{w}
      (CategoryTheory.isCardinalPresentable C κ)
  refine ⟨fun z => Q₀ z.obj, ?_, ?_⟩
  · exact small_of_injective
      (f := fun (z : Subtype (fun z : Equif η θ => Q₀ z.obj)) => (⟨z.1.obj, z.2⟩ : Subtype Q₀))
      (by rintro ⟨⟨a, ha'⟩, ha⟩ ⟨⟨b, hb'⟩, hb⟩ h
          simp only [Subtype.mk.injEq] at h
          subst h
          rfl)
  · intro x hx
    obtain ⟨y, hy, ⟨e⟩⟩ := hle x.obj hx
    refine ⟨⟨y, equifProp_of_iso x.property e⟩, hy, ⟨?_⟩⟩
    exact (ObjectProperty.ι _).preimageIso e

/-- **Accessibility of the equifier, reduced to the generation step.**  If every object of
the equifier of two natural transformations between `κ`-accessible functors is a
`κ`-filtered colimit of objects of `UlmerBialgebras.Equif.gen η θ κ`, then the equifier is a
`κ`-accessible category. -/
theorem isCardinalAccessibleCategory [IsCardinalAccessibleCategory.{w} C κ]
    [F.IsCardinalAccessible κ]
    (hgen : ∀ x : Equif η θ, ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      (gen η θ κ).colimitsOfShape J x) :
    IsCardinalAccessibleCategory.{w} (Equif η θ) κ := by
  have hg : (gen η θ κ).IsCardinalFilteredGenerator κ :=
    { le_isCardinalPresentable := by
        intro x hx
        have : IsCardinalPresentable x.obj κ := hx
        exact Equif.isCardinalPresentable x
      exists_colimitsOfShape := hgen }
  exact
    { toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator
      toHasCardinalFilteredColimits := inferInstance }

end Equif

end UlmerBialgebras
