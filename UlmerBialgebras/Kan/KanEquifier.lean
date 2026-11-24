module

public import UlmerBialgebras.Kan.Kan
public import UlmerBialgebras.Basic.HomCat

/-!
# Theorem 4.7 (3): lifting Kan extensions along an equifier

This file proves part (3) of Theorem 4.7 of *A Syntactic Approach to Ulmer's Bialgebras*:
the canonical 1-cell `e : Eq(η, θ) → a` out of an equifier of `η, θ : f ⟹ g : a → b`
strictly creates those left Kan extensions whose quotient initiality is preserved by `f`.

The proof is organized around the fact that post-composition with `e`,
`LeftExt.push k d E.e`, is a **fully faithful** functor (`UlmerBialgebras.Equifier.push_full`,
`UlmerBialgebras.Equifier.push_faithful`), so that it reflects initial objects; the only real work
is to show that an initial left extension of `d ≫ e` along `k` equifies `η` and `θ` and hence
lifts through the equifier.

The right Kan case is the left Kan case in `K^co` (`UlmerBialgebras/Kan/CoKan.lean`); it is derived
in
`UlmerBialgebras/Proofs/Sec4/Sec4.lean`.

## Main results

* `UlmerBialgebras.Equifier.push_full`, `UlmerBialgebras.Equifier.push_faithful`: post-composition
  with the canonical 1-cell `e` of an equifier is fully faithful on left extensions.
* `UlmerBialgebras.Equifier.strictlyCreates_leftKan`: `e` strictly creates those left Kan extensions
  whose quotient initiality `f` preserves (Theorem 4.7 (3)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.6 (3) and Theorem 4.7 (3)
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Equifier

variable {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ) {I X : Obj}

/-- Whiskering `E.cond` with a 1-cell into the equifier. -/
lemma cond_comp {x : Obj} (h : x ⟶ E.pt) : (h ≫ E.e) ◁ η = (h ≫ E.e) ◁ θ := by
  rw [Bicategory.Strict.comp_whiskerLeft h E.e η, Bicategory.Strict.comp_whiskerLeft h E.e θ,
    E.cond]

/-- 1-cells into an equifier are determined by their composite with `e`. -/
lemma hom_ext {x : Obj} {k₁ k₂ : x ⟶ E.pt} (h : k₁ ≫ E.e = k₂ ≫ E.e) : k₁ = k₂ := by
  rw [E.lift_uniq k₁ (k₁ ≫ E.e) (cond_comp E k₁) rfl,
    E.lift_uniq k₂ (k₁ ≫ E.e) (cond_comp E k₁) h.symm]

section Left

variable (k : I ⟶ X) (d : I ⟶ E.pt)

/-- Post-composition with the equifier 1-cell `e`, `LeftExt.push k d E.e`, is faithful. -/
instance push_faithful : (LeftExt.push k d E.e).Faithful where
  map_injective h := LeftExt.hom_ext (E.faithful _ _ (LeftExt.hom_ext_iff.mp h))

/-- Post-composition with the equifier 1-cell `e`, `LeftExt.push k d E.e`, is full. -/
instance push_full : (LeftExt.push k d E.e).Full where
  map_surjective {L L'} β := by
    obtain ⟨α, hα⟩ := E.full (LeftExt.homCell β)
    have hβ : ((L.unit ▷ E.e) ≫ eqToHom (Category.assoc k L.ext E.e)) ≫ (k ◁ LeftExt.homCell β)
        = (L'.unit ▷ E.e) ≫ eqToHom (Category.assoc k L'.ext E.e) := LeftExt.w β
    refine ⟨LeftExt.homMk α (E.faithful _ _ ?_), LeftExt.hom_ext hα⟩
    rw [Bicategory.comp_whiskerRight, Bicategory.Strict.whisker_assoc', hα]
    rw [← Category.assoc (obj := _ ⟶ _), ← Category.assoc (obj := _ ⟶ _), hβ]
    simp

/-- `LeftExt.push k d E.e` is injective on objects: a left extension of `d` along `k` is
determined by its image under post-composition with `e`. -/
lemma push_injective {L₁ L₂ : LeftExt k d}
    (h : (LeftExt.push k d E.e).obj L₁ = (LeftExt.push k d E.e).obj L₂) : L₁ = L₂ := by
  have he : L₁.ext = L₂.ext := hom_ext E (congr(LeftExt.ext $h))
  refine LeftExt.eq_of_ext_eq he ?_
  refine E.faithful _ _ ?_
  have h2 := LeftExt.unit_congr h
  simp only [LeftExt.push_obj_unit, Category.assoc, eqToHom_trans] at h2
  rw [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  refine (cancel_mono (eqToHom (Category.assoc k L₂.ext E.e))).mp ?_
  simp only [Category.assoc, eqToHom_trans]
  exact h2

/-- The underlying 1-cell of an initial left extension of `d ≫ e` equifies `η` and `θ`,
provided `f` preserves its quotient initiality. -/
lemma ext_equifies
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (Limits.IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L))
    (L' : LeftExt k (d ≫ E.e)) (hL' : Nonempty (Limits.IsInitial L')) :
    L'.ext ◁ η = L'.ext ◁ θ := by
  have key : ∀ β : f ⟶ g, (d ≫ E.e) ◁ β = (d ≫ E.e) ◁ η →
      ((L'.unit ▷ f) ≫ eqToHom (Category.assoc k L'.ext f)) ≫ (k ◁ (L'.ext ◁ β))
        = ((d ≫ E.e) ◁ η) ≫ (L'.unit ▷ g) ≫ eqToHom (Category.assoc k L'.ext g) := by
    intro β hβ
    have hw : eqToHom (Category.assoc k L'.ext f) ≫ (k ◁ (L'.ext ◁ β))
        = ((k ≫ L'.ext) ◁ β) ≫ eqToHom (Category.assoc k L'.ext g) := by
      rw [Bicategory.Strict.comp_whiskerLeft k L'.ext β]; simp
    rw [Category.assoc (obj := _ ⟶ _), hw, ← Category.assoc (obj := _ ⟶ _),
        Eq.symm <| Bicategory.whisker_exchange L'.unit β, hβ, Category.assoc (obj := _ ⟶ _)]
  set Y : LeftExt k ((d ≫ E.e) ≫ f) :=
    LeftExt.mk (L'.ext ≫ g)
      (((d ≫ E.e) ◁ η) ≫ (L'.unit ▷ g) ≫ eqToHom (Category.assoc k L'.ext g))
  exact LeftExt.hom_ext_iff.mp (@Subsingleton.elim _ (hf L' hL' Y)
    (LeftExt.homMk (L'.ext ◁ η) (key η rfl) : (LeftExt.push k (d ≫ E.e) f).obj L' ⟶ Y)
    (LeftExt.homMk (L'.ext ◁ θ) (key θ (cond_comp E d).symm)))

/-- **Theorem 4.7 (3)** ([forsman2026syntactic]): the canonical 1-cell out of an equifier
strictly creates those left Kan extensions whose quotient initiality is preserved by `f`. -/
theorem strictlyCreates_leftKan
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (Limits.IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L)) :
    StrictlyCreatesLeftKan k d E.e := by
  intro L' hL'
  have hcond : L'.ext ◁ η = L'.ext ◁ θ := ext_equifies E k d hf L' hL'
  have hle : E.lift L'.ext hcond ≫ E.e = L'.ext := E.lift_e L'.ext hcond
  obtain ⟨ε, hε⟩ := E.full (k₁ := d) (k₂ := k ≫ E.lift L'.ext hcond)
    (L'.unit ≫ eqToHom (by rw [Category.assoc, hle]))
  have hpush : (LeftExt.push k d E.e).obj (LeftExt.mk (E.lift L'.ext hcond) ε) = L' := by
    refine LeftExt.eq_of_ext_eq hle ?_
    simp only [LeftExt.push_obj_unit]
    rw [LeftExt.mk_unit]
    simp only [hε, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine ⟨⟨LeftExt.mk (E.lift L'.ext hcond) ε, hpush, fun L₁ h => push_injective E k d
    (h.trans hpush.symm)⟩, ?_⟩
  intro L₁ h
  subst h
  obtain ⟨hi⟩ := hL'
  exact ⟨isInitialOfFullyFaithful (LeftExt.push k d E.e) hi⟩

end Left


end Equifier

end UlmerBialgebras
