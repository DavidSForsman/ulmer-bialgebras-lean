module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec3DefsMonModel
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Models.OplaxInduced
public import UlmerBialgebras.Paper.Sec3DefsTransposedDatum

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Challenge: Sections 2 and 3

Statements of the numbered results of Sections 2 and 3, with proofs left as `sorry`.
Numbers refer to version 2 of the paper.

## Main results

* `UlmerBialgebras.Paper.ex_2_3_1`: `CAT` has products of every size, inserters and equifiers
  (Example 2.3 (1)).
* `UlmerBialgebras.Paper.prop_3_11_lax`: the composite of two lax morphisms of models is a lax
  morphism (Proposition 3.11).
* `UlmerBialgebras.Paper.prop_3_15`: `M^σ` is the inserter and `M^T` an equifier of the bialgebraic
  datum `B_{M,T}` (Proposition 3.15).
* `UlmerBialgebras.Paper.thm_3_22`: if `η_t` is invertible on the function coarity terms and the
  equational coarity components are monic, there is a unique 1-cell `M^T → N^T` over
  `F^σ` (Theorem 3.22).
* `UlmerBialgebras.Paper.cor_3_24`: a lax monoidal functor `F : C ⥤ D` induces a functor
  `Mon C ⥤ Mon D` over `F` (Corollary 3.24).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 2, 3
  (Remark 2.2, Example 2.3, Remark 3.2, Propositions 3.11, 3.15, Lemmas 3.18, 3.21,
  Theorem 3.22, Corollaries 3.23, 3.24, Examples 3.20)
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model theory*]
  [MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
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
      Nonempty (HasChosenEquifiers Cat.{v, max u v}) := sorry

/-- **Remark 2.2** ([forsman2026syntactic]), inserters: in `CAT`, the inserter of `F, G : C ⥤ D` is
the category of pairs `(c, Fc ⟶ Gc)` with its forgetful functor and the tautological transformation.
-/
theorem rem_2_2_ins {C D : Cat.{v, max u v}} (F G : C ⟶ D) :
    ∃ I : Inserter F G, I.pt = Cat.of (Ins F.toFunctor G.toFunctor) ∧ HEq I.u ((Ins.forget
        F.toFunctor G.toFunctor).toCatHom) ∧
      HEq I.φ ((Ins.cellNat F.toFunctor G.toFunctor).toCatHom₂) := sorry

/-- **Remark 2.2** ([forsman2026syntactic]), equifiers: in `CAT`, the equifier of `η, θ : F ⟹ G` is
the full subcategory of objects `c` with `η_c = θ_c`. -/
theorem rem_2_2_equif {C D : Cat.{v, max u v}} {F G : C ⟶ D} (η θ : F ⟶ G) :
    ∃ E : Equifier η θ, E.pt = Cat.of (Equif η.toNatTrans θ.toNatTrans) ∧ HEq E.e ((Equif.forget
        η.toNatTrans θ.toNatTrans).toCatHom) := sorry

section Representables

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

end Representables

section AccPIE

/-- **Example 2.3 (2)** ([forsman2026syntactic]; [MakkaiPare1989AccessibleCategories], [LPC]),
products: a small product of accessible categories is accessible, and the projections are accessible
functors.

**Reading.**
* "accessible functor" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w}` plus `IsAccessibleCategory.{w}` on its domain and codomain;
  Mathlib's predicate does not include the latter.
-/
theorem ex_2_3_2_prod {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, IsAccessibleCategory.{w} (C i)] :
    IsAccessibleCategory.{w} (∀ i, C i) ∧
      ∀ i, Functor.IsAccessible.{w} (Pi.eval C i) := sorry

/-- **Example 2.3 (2)** ([forsman2026syntactic]; [MakkaiPare1989AccessibleCategories], [LPC]),
products, universal property in `ACC`: the functor into a product induced by accessible functors is
accessible.

**Reading.**
* "accessible functor" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w}` plus `IsAccessibleCategory.{w}` on its domain and codomain;
  Mathlib's predicate does not include the latter.
-/
theorem ex_2_3_2_prod_lift {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, IsAccessibleCategory.{w} (C i)] {X : Type u''} [Category.{v''} X]
    [IsAccessibleCategory.{w} X] (g : ∀ i, X ⥤ C i) [∀ i, Functor.IsAccessible.{w} (g i)] :
    Functor.IsAccessible.{w} (Functor.pi' g) := sorry

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Example 2.3 (2)** ([forsman2026syntactic]; [MakkaiPare1989AccessibleCategories], [LPC]),
inserters: the inserter of two accessible functors between accessible categories is accessible, its
forgetful functor is accessible, and the functor into it induced by an accessible functor is
accessible.

**Reading.**
* "accessible functor" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w}` plus `IsAccessibleCategory.{w}` on its domain and codomain;
  Mathlib's predicate does not include the latter.
-/
theorem ex_2_3_2_ins [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F G : C ⥤ D) [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] :
    IsAccessibleCategory.{w} (Ins F G) ∧ Functor.IsAccessible.{w} (Ins.forget F G) ∧
      ∀ {X : Type u''} [Category.{v''} X] [IsAccessibleCategory.{w} X] (h : X ⥤ C)
        (α : h ⋙ F ⟶ h ⋙ G), Functor.IsAccessible.{w} h →
          Functor.IsAccessible.{w} (Ins.liftFunctor h α) := sorry

/-- **Example 2.3 (2)** ([forsman2026syntactic]; [MakkaiPare1989AccessibleCategories], [LPC]),
equifiers.

**Reading.**
* "accessible functor" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w}` plus `IsAccessibleCategory.{w}` on its domain and codomain;
  Mathlib's predicate does not include the latter.
-/
theorem ex_2_3_2_equif [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    {F G : C ⥤ D} [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] (η θ : F ⟶ G) :
    IsAccessibleCategory.{w} (Equif η θ) ∧ Functor.IsAccessible.{w} (Equif.forget η θ) ∧
      ∀ {X : Type u''} [Category.{v''} X] [IsAccessibleCategory.{w} X] (h : X ⥤ C)
        (H : Functor.whiskerLeft h η = Functor.whiskerLeft h θ), Functor.IsAccessible.{w} h →
          Functor.IsAccessible.{w} (Equif.liftFunctor h H) := sorry

end AccPIE

end UlmerBialgebras.Paper
