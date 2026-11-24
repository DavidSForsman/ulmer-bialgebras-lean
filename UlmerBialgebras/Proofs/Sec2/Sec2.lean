module

public import UlmerBialgebras.Kan.KanBialgebra
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Proofs.Sec3.TransposedDatum
public import UlmerBialgebras.Proofs.Sec3.MonModelCalc
public import UlmerBialgebras.Proofs.Sec3.MonoidalLaxInduced
public import UlmerBialgebras.Models.CoMor
public import UlmerBialgebras.Models.CoBialgebra
public import UlmerBialgebras.Models.CoInduced

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Solution: Sections 2 and 3

Proofs of the numbered results of Sections 2 and 3, restating the theorems of
`UlmerBialgebras/Paper/Sec2.lean`.

## Main results

* `UlmerBialgebras.Paper.ex_2_3_1`: Example 2.3 (1), `CAT` has all PIE limits.
* `UlmerBialgebras.Paper.prop_3_15`: Proposition 3.15, `M^σ` is the object of pre-bialgebras and
  `M^T` the object of bialgebras of `B_{M,T}`.
* `UlmerBialgebras.Paper.thm_3_22`: Theorem 3.22, the induced functor of algebras.
* `UlmerBialgebras.Paper.cor_3_24`: Corollary 3.24, a lax monoidal functor induces a functor between
  the categories of internal monoids, lying over it.
* `UlmerBialgebras.Paper.ex_3_20_3`: Examples 3.20 (3), `M^{T_Field}` is equivalent to the category
  of fields.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 2 and 3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
* [S. Lack, G. Tendas, *Virtual concepts in the theory of accessible categories*][LACK2023107196],
  Theorem 5.5, Theorem 5.9
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras]
-/

universe u v w u' v' u'' v'' u₁ u₂ u₃ s₁ s₂ s₃ uᵥ u𝓌

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 2 -/

/-- **Example 2.3 (1)** ([forsman2026syntactic]): the 2-category `CAT` has all PIE limits. A family
of categories indexed by a type in `Type w` has a strict product, in `Cat.{max w v, max w u}`
(for `w = 0` this stays in `Cat.{v, u}`), and `Cat.{v, max u v}` has strict inserters and
equifiers. -/
theorem ex_2_3_1 :
    Nonempty (HasChosenProductsOfSize.{w} Cat.{max w v, max w u}) ∧
      Nonempty (HasChosenInserters Cat.{v, max u v}) ∧
      Nonempty (HasChosenEquifiers Cat.{v, max u v}) :=
  ⟨⟨⟨fun c => catProduct c⟩⟩, ⟨⟨fun F G => catInserter F G⟩⟩, ⟨⟨fun η θ => catEquifier η θ⟩⟩⟩

/-- **Remark 2.2** ([forsman2026syntactic]), inserters: in `CAT`, the inserter of `F, G : C ⥤ D` is
the category of pairs `(c, Fc ⟶ Gc)` with its forgetful functor and the tautological
transformation. -/
theorem rem_2_2_ins {C D : Cat.{v, max u v}} (F G : C ⟶ D) :
    ∃ I : Inserter F G, I.pt = Cat.of (Ins F.toFunctor G.toFunctor) ∧ HEq I.u ((Ins.forget
        F.toFunctor G.toFunctor).toCatHom) ∧
      HEq I.φ ((Ins.cellNat F.toFunctor G.toFunctor).toCatHom₂) :=
  ⟨catInserter F G, rfl, HEq.rfl, HEq.rfl⟩

/-- **Remark 2.2** ([forsman2026syntactic]), equifiers: in `CAT`, the equifier of `η, θ : F ⟹ G` is
the full subcategory of objects `c` with `η_c = θ_c`. -/
theorem rem_2_2_equif {C D : Cat.{v, max u v}} {F G : C ⟶ D} (η θ : F ⟶ G) :
    ∃ E : Equifier η θ, E.pt = Cat.of (Equif η.toNatTrans θ.toNatTrans) ∧ HEq E.e ((Equif.forget
        η.toNatTrans θ.toNatTrans).toCatHom) :=
  ⟨catEquifier η θ, rfl, HEq.rfl⟩

section Representables

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Helper: an equality in the inserter category determines its structure morphism up to
isomorphism on the base. -/
lemma ins_obj_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} {x₁ x₂ : C} {c₁ : F.obj x₁ ⟶ G.obj x₁} {c₂ : F.obj x₂ ⟶ G.obj x₂}
    (h : (⟨x₁, c₁⟩ : Ins F G) = ⟨x₂, c₂⟩) :
    c₁ = eqToHom congr(F.obj ($h).pt) ≫ c₂ ≫ eqToHom congr(G.obj ($h).pt).symm := by
  cases h
  simp

end Representables

section AccPIE

/-- **Example 2.3 (2)** ([forsman2026syntactic]), products: a small product of accessible categories
is accessible, and the projections are accessible functors. -/
theorem ex_2_3_2_prod {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, IsAccessibleCategory.{w} (C i)] :
    IsAccessibleCategory.{w} (∀ i, C i) ∧
      ∀ i, Functor.IsAccessible.{w} (Pi.eval C i) :=
  ⟨Pi.isAccessibleCategory, fun i => Pi.eval_isAccessible i⟩

/-- **Example 2.3 (2)** ([forsman2026syntactic]), products, universal property in `ACC`: the functor
into a product induced by accessible functors is accessible. -/
theorem ex_2_3_2_prod_lift {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, IsAccessibleCategory.{w} (C i)] {X : Type u''} [Category.{v''} X]
    [IsAccessibleCategory.{w} X] (g : ∀ i, X ⥤ C i) [∀ i, Functor.IsAccessible.{w} (g i)] :
    Functor.IsAccessible.{w} (Functor.pi' g) :=
  Pi.pi'_isAccessible g

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Example 2.3 (2)** ([forsman2026syntactic]), inserters: the inserter of two accessible functors
between accessible categories is accessible, its forgetful functor is accessible, and the functor
into it induced by an accessible functor is accessible. -/
theorem ex_2_3_2_ins [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F G : C ⥤ D) [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] :
    IsAccessibleCategory.{w} (Ins F G) ∧ Functor.IsAccessible.{w} (Ins.forget F G) ∧
      ∀ {X : Type u''} [Category.{v''} X] [IsAccessibleCategory.{w} X] (h : X ⥤ C)
        (α : h ⋙ F ⟶ h ⋙ G), Functor.IsAccessible.{w} h →
          Functor.IsAccessible.{w} (Ins.liftFunctor h α) :=
  ⟨Ins.isAccessibleCategory, Ins.forget_isAccessible,
    fun h α hh => by have := hh; exact Ins.liftFunctor_isAccessible h α⟩

/-- **Example 2.3 (2)** ([forsman2026syntactic]), equifiers. -/
theorem ex_2_3_2_equif [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    {F G : C ⥤ D} [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] (η θ : F ⟶ G) :
    IsAccessibleCategory.{w} (Equif η θ) ∧ Functor.IsAccessible.{w} (Equif.forget η θ) ∧
      ∀ {X : Type u''} [Category.{v''} X] [IsAccessibleCategory.{w} X] (h : X ⥤ C)
        (H : Functor.whiskerLeft h η = Functor.whiskerLeft h θ), Functor.IsAccessible.{w} h →
          Functor.IsAccessible.{w} (Equif.liftFunctor h H) :=
  ⟨Equif.isAccessibleCategory, Equif.forget_isAccessible,
    fun h H hh => by have := hh; exact Equif.liftFunctor_isAccessible h H⟩

end AccPIE

end UlmerBialgebras.Paper
