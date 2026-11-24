module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Two facts about left Kan extensions

## Main results

* `UlmerBialgebras.hasLeftKanExtension_pi`: a diagram in a product of categories has a left Kan
  extension as soon as each of its components does.
* `UlmerBialgebras.hasLeftKanExtension_comp_leftAdjoint`: post-composition with a left adjoint
  preserves the existence of left Kan extensions.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 5.8
-/

@[expose] public section

namespace UlmerBialgebras

open CategoryTheory Limits Functor

section Pi

variable {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)] {I K : Type*} [Category I]
  [Category K] (k : I ⥤ K) (X : I ⥤ ∀ i, C i)

/-- A diagram `X : I ⥤ ∏ᵢ Cᵢ` has a left Kan extension along `k` as soon as each component
    `X ⋙ evalᵢ` does; it is built componentwise. -/
theorem hasLeftKanExtension_pi [h : ∀ i, k.HasLeftKanExtension (X ⋙ Pi.eval C i)] :
    k.HasLeftKanExtension X := by
  -- Componentwise left Kan extensions, assembled into a functor to the product.
  let Ei := fun i => k.leftKanExtension (X ⋙ Pi.eval C i)
  let αi := fun i => k.leftKanExtensionUnit (X ⋙ Pi.eval C i)
  let E : K ⥤ ∀ i, C i := Functor.pi' Ei
  let α : X ⟶ k ⋙ E :=
    { app := fun j i => (αi i).app j
      naturality := fun j j' g => by
        funext i
        exact (αi i).naturality g }
  let desc : ∀ T : LeftExtension k X, ∀ i, Ei i ⟶ T.right ⋙ Pi.eval C i := fun T i =>
    (Ei i).descOfIsLeftKanExtension (αi i) (T.right ⋙ Pi.eval C i)
      (Functor.whiskerRight T.hom (Pi.eval C i))
  -- The assembled extension is a left Kan extension: check componentwise.
  have : E.IsLeftKanExtension α := by
    refine ⟨⟨IsInitial.ofUniqueHom (fun T => StructuredArrow.homMk
      { app := fun x i => (desc T i).app x
        naturality := fun x y f => by
          funext i
          exact (desc T i).naturality f } ?_) ?_⟩⟩
    · ext j i
      exact (Ei i).descOfIsLeftKanExtension_fac_app (αi i) (T.right ⋙ Pi.eval C i)
        (Functor.whiskerRight T.hom (Pi.eval C i)) j
    · intro T m
      apply StructuredArrow.ext
      ext x i
      let γ : Ei i ⟶ T.right ⋙ Pi.eval C i :=
        { app := fun x => m.right.app x i
          naturality := fun x y f => congr($(m.right.naturality f) i) }
      have hγ : γ = desc T i := by
        apply (Ei i).hom_ext_of_isLeftKanExtension (αi i)
        rw [(Ei i).descOfIsLeftKanExtension_fac]
        ext j
        exact congr($(congr_app (StructuredArrow.w m) j) i)
      exact congr_app hγ x
  exact HasLeftKanExtension.mk E α

end Pi

section Adj

variable {A B : Type*} [Category A] [Category B] {L' : A ⥤ B}
  {I K : Type*} [Category I] [Category K] (k : I ⥤ K) (X : I ⥤ A)

/-- If `X` has a left Kan extension `E` along `k` and `L' ⊣ R`, then `X ⋙ L'` has a left Kan
    extension along `k`, namely `E ⋙ L'`. -/
theorem hasLeftKanExtension_comp_leftAdjoint {R : B ⥤ A} (adj : L' ⊣ R)
    [k.HasLeftKanExtension X] :
    k.HasLeftKanExtension (X ⋙ L') := by
  -- Whisker the Kan extension of `X` by `L'`; transpose extensions of `X ⋙ L'` along `L' ⊣ R`.
  let E := k.leftKanExtension X
  let α := k.leftKanExtensionUnit X
  let α' : X ⋙ L' ⟶ k ⋙ (E ⋙ L') := Functor.whiskerRight α L'
  let flat : ∀ T : LeftExtension k (X ⋙ L'), X ⟶ k ⋙ (T.right ⋙ R) := fun T =>
    { app := fun j => adj.homEquiv _ _ (T.hom.app j)
      naturality := fun j j' g => by
        have := T.hom.naturality g
        dsimp at this ⊢
        rw [← adj.homEquiv_naturality_left, this, adj.homEquiv_naturality_right] }
  let γ₀ : ∀ T : LeftExtension k (X ⋙ L'), E ⟶ T.right ⋙ R := fun T =>
    E.descOfIsLeftKanExtension α (T.right ⋙ R) (flat T)
  -- Universality follows from that of `E` through the adjunction.
  have : (E ⋙ L').IsLeftKanExtension α' := by
    refine ⟨⟨IsInitial.ofUniqueHom (fun T => StructuredArrow.homMk
      { app := fun x => (adj.homEquiv _ _).symm ((γ₀ T).app x)
        naturality := fun x y f => by
          have := (γ₀ T).naturality f
          dsimp at this ⊢
          rw [← adj.homEquiv_naturality_left_symm, this,
            adj.homEquiv_naturality_right_symm] } ?_) ?_⟩⟩
    · ext j
      have h := E.descOfIsLeftKanExtension_fac_app α (T.right ⋙ R) (flat T) j
      dsimp [α', γ₀] at h ⊢
      rw [← adj.homEquiv_naturality_left_symm, h]
      simp [flat]
    · intro T m
      apply StructuredArrow.ext
      let msharp : E ⟶ T.right ⋙ R :=
        { app := fun x => adj.homEquiv _ _ (m.right.app x)
          naturality := fun x y f => by
            have := m.right.naturality f
            dsimp at this ⊢
            rw [← adj.homEquiv_naturality_left, this, adj.homEquiv_naturality_right] }
      have hm : msharp = γ₀ T := by
        apply E.hom_ext_of_isLeftKanExtension α
        rw [E.descOfIsLeftKanExtension_fac]
        ext j
        have hw := congr_app (StructuredArrow.w m) j
        dsimp [α', msharp, flat] at hw ⊢
        rw [← adj.homEquiv_naturality_left, hw]
      ext x
      have := congr_app hm x
      dsimp [msharp] at this ⊢
      rw [← this, Equiv.symm_apply_apply]
  exact HasLeftKanExtension.mk (E ⋙ L') α'

end Adj

end UlmerBialgebras
