module

public import Foundations.CategoryTheory.Factorization.OFS
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Orthogonality and Mathlib's lifting properties

Orthogonality `e ⊥ m` (`UlmerBialgebras.Orthogonal`) asks for a *unique* diagonal filler of every
commutative square; Mathlib's `HasLiftingProperty e m` asks for one. This file relates the two
notions, and the orthogonal classes of a class `A` to Mathlib's `A.rlp` and `A.llp`. Mathlib has
lifting properties and weak factorization systems, but neither orthogonality nor orthogonal
factorization systems, so these stay local.

## Main results

* `UlmerBialgebras.orthogonal_iff_hasLiftingProperty`: `e ⊥ m` if and only if `e` has the left
  lifting property against `m` and the lifts are unique
  (`UlmerBialgebras.Orthogonal.hasLiftingProperty` is the forward half);
* `UlmerBialgebras.rightOrth_le_rlp`, `UlmerBialgebras.leftOrth_le_llp`: `A⊥ ⊆ A.rlp` and
  `⊥A ⊆ A.llp`.

## References

* [E. Riehl, *Categorical Homotopy Theory*][Riehl2014CategoricalHomotopyTheory], Chapter 11
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Orthogonality is the unique lifting property.** `e ⊥ m` if and only if every commutative
square from `e` to `m` has a lift (Mathlib's `HasLiftingProperty e m`) and any two lifts of the
same square are equal. -/
theorem orthogonal_iff_hasLiftingProperty {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) :
    Orthogonal e m ↔ HasLiftingProperty e m ∧
      ∀ (f : a ⟶ c) (g : b ⟶ d) (h h' : b ⟶ c), e ≫ h = f → h ≫ m = g → e ≫ h' = f →
        h' ≫ m = g → h = h' := by
  constructor
  · intro ho
    refine ⟨⟨fun {f g} sq => ?_⟩, fun f g h h' h₁ h₂ h₁' h₂' => ?_⟩
    · obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := ho f g sq.w
      exact ⟨⟨{ l := l, fac_left := hl₁, fac_right := hl₂ }⟩⟩
    · have w : f ≫ m = e ≫ g := by rw [← h₁, ← h₂, Category.assoc]
      exact (ho f g w).unique ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩
  · rintro ⟨hl, hu⟩ f g w
    have sq : CommSq f e m g := ⟨w⟩
    exact ⟨sq.lift, ⟨sq.fac_left, sq.fac_right⟩,
      fun h ⟨h₁, h₂⟩ => hu f g h sq.lift h₁ h₂ sq.fac_left sq.fac_right⟩

/-- A morphism orthogonal to `m` has the left lifting property against `m`. -/
theorem Orthogonal.hasLiftingProperty {a b c d : C} {e : a ⟶ b} {m : c ⟶ d}
    (h : Orthogonal e m) : HasLiftingProperty e m :=
  ((orthogonal_iff_hasLiftingProperty e m).1 h).1

/-- The right orthogonal class `A⊥` is contained in Mathlib's right lifting class `A.rlp`. -/
theorem rightOrth_le_rlp (A : MorphismProperty C) : rightOrth A ≤ A.rlp :=
  fun _ _ _ hm _ _ e he => (hm e he).hasLiftingProperty

/-- The left orthogonal class `⊥A` is contained in Mathlib's left lifting class `A.llp`. -/
theorem leftOrth_le_llp (A : MorphismProperty C) : leftOrth A ≤ A.llp :=
  fun _ _ _ he _ _ m hm => (he m hm).hasLiftingProperty

end UlmerBialgebras
