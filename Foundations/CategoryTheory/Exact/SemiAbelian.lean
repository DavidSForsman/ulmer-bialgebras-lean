module

public import Mathlib.CategoryTheory.RegularCategory.Basic

/-!
# Semi-abelian and co-semi-abelian categories

We formalise Definition 2.1 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

A category is *semi-abelian* when it is pointed, protomodular, Barr-exact and has binary
coproducts; it is *co-semi-abelian* when its opposite is semi-abelian.

Mathlib already provides `CategoryTheory.Regular` (regular categories, item 2 of the
definition), `CategoryTheory.Limits.HasZeroObject` (item 1) and
`CategoryTheory.IsKernelPair`, so here we add the missing notions: jointly extremal
epimorphic pairs, protomodularity, internal equivalence relations and Barr exactness. The
(co-)semi-abelian categories themselves are not defined here.

## Main results

* `CategoryTheory.JointlyExtremalEpiPair`: jointly extremal epimorphic pairs of morphisms;
* `CategoryTheory.Protomodular`: protomodular categories (Definition 2.1 (4) of
  [forsman2026semiabeliannessaffinegroupschemes]);
* `CategoryTheory.IsInternalEquivalenceRelation`: internal equivalence relations, i.e. jointly monic
  pairs which are reflexive, symmetric and transitive;
* `CategoryTheory.IsBarrExact`: Barr-exact categories, regular categories in which every internal
  equivalence relation is a kernel pair (Definition 2.1 (3) of
  [forsman2026semiabeliannessaffinegroupschemes]; cf. Definition 6.4 of [forsman2026syntactic]).

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Definition 2.1
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4
* [G. Janelidze, L. Márki, W. Tholen, *Semi-abelian categories*][JANELIDZE2002367]
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [M. Barr, *Exact categories*][Ba]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian categories*]
  [BorceuxBourn2004]
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory Limits

universe v u

variable (C : Type u) [Category.{v} C]

/-- A pair of morphisms with common codomain is *jointly extremal epimorphic* if, whenever both
factor through a fixed monomorphism `m`, that monomorphism is an isomorphism. -/
def JointlyExtremalEpiPair {c₁ c₂ d : C} (f₁ : c₁ ⟶ d) (f₂ : c₂ ⟶ d) : Prop :=
  ∀ ⦃z : C⦄ (m : z ⟶ d), Mono m → ∀ (g₁ : c₁ ⟶ z) (g₂ : c₂ ⟶ z),
    g₁ ≫ m = f₁ → g₂ ≫ m = f₂ → IsIso m

/-- A family of morphisms with common codomain is *jointly extremal epimorphic* if, whenever all
members factor through a fixed monomorphism `m`, that monomorphism is an isomorphism. -/
def JointlyExtremalEpiFamily {L : Type*} {K : L → C} {G : C}
    (f : ∀ i : L, K i ⟶ G) : Prop :=
  ∀ ⦃Z : C⦄ (m : Z ⟶ G), Mono m → (∀ i : L, ∃ g : K i ⟶ Z, g ≫ m = f i) → IsIso m

/-- A pair `(f₁, f₂)` is jointly extremal epimorphic iff the `Bool`-indexed family
`if b then f₁ else f₂` is jointly extremal epimorphic. -/
lemma jointlyExtremalEpiPair_iff_family {c₁ c₂ d : C} (f₁ : c₁ ⟶ d) (f₂ : c₂ ⟶ d) :
    JointlyExtremalEpiPair C f₁ f₂ ↔
      JointlyExtremalEpiFamily C (K := fun b : Bool => if b then c₁ else c₂)
        (fun b : Bool => match b with | true => f₁ | false => f₂) := by
  constructor
  · intro h Z m hm hg
    obtain ⟨g₁, hg₁⟩ := hg true
    obtain ⟨g₂, hg₂⟩ := hg false
    exact h m hm g₁ g₂ hg₁ hg₂
  · intro h Z m hm g₁ g₂ hg₁ hg₂
    refine h m hm (fun b => ?_)
    cases b
    · exact ⟨g₂, hg₂⟩
    · exact ⟨g₁, hg₁⟩

/-- **Definition 2.1 (4)**: a category is *protomodular* if pullbacks along retractions exist
and, for every retraction `r : x ⟶ y` with section `s` and every pullback `k : a ⟶ x` of a
morphism along `r`, the pair `(s, k)` is jointly extremal epimorphic. -/
class Protomodular : Prop where
  /-- Pullbacks along retractions exist. -/
  hasPullback_of_isSplitEpi : ∀ {x y z : C} (r : x ⟶ y) (_ : IsSplitEpi r) (g : z ⟶ y),
    HasPullback g r
  /-- The section and the pullback projection are jointly extremal epimorphic. -/
  jointlyExtremalEpiPair : ∀ {x y a b : C} {r : x ⟶ y} {s : y ⟶ x}, s ≫ r = 𝟙 y →
    ∀ {k : a ⟶ x} {t : a ⟶ b} {u : b ⟶ y}, IsPullback t k u r →
      JointlyExtremalEpiPair C s k

variable {C}

/-- An internal equivalence relation on `X`: a jointly monic pair `r₁, r₂ : R ⟶ X` which is
reflexive, symmetric and transitive (the latter two expressed on generalized elements). -/
structure IsInternalEquivalenceRelation {R X : C} (r₁ r₂ : R ⟶ X) : Prop where
  /-- `(r₁, r₂)` is a jointly monic pair, i.e. `R` really is a relation. -/
  jointly_mono : ∀ ⦃T : C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b
  /-- Reflexivity. -/
  refl : ∃ d : X ⟶ R, d ≫ r₁ = 𝟙 X ∧ d ≫ r₂ = 𝟙 X
  /-- Symmetry. -/
  symm : ∃ σ : R ⟶ R, σ ≫ r₁ = r₂ ∧ σ ≫ r₂ = r₁
  /-- Transitivity. -/
  trans : ∀ ⦃T : C⦄ (a b : T ⟶ R), a ≫ r₂ = b ≫ r₁ →
    ∃ c : T ⟶ R, c ≫ r₁ = a ≫ r₁ ∧ c ≫ r₂ = b ≫ r₂

variable (C)

/-- **Definition 2.1 (3)**: a category is *(Barr-)exact* if it is regular and every internal
equivalence relation is a kernel pair. -/
class IsBarrExact extends Regular C where
  /-- Every internal equivalence relation is the kernel pair of some morphism. -/
  isKernelPair_of_isInternalEquivalenceRelation : ∀ {R X : C} {r₁ r₂ : R ⟶ X},
    IsInternalEquivalenceRelation r₁ r₂ → ∃ (Y : C) (f : X ⟶ Y), IsKernelPair f r₁ r₂

end CategoryTheory
