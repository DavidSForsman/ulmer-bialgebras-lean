module

public import UlmerBialgebras.Paper.Sec6DefsAlgTheory

/-!
# Single-sorted languages: the Mathlib bridge

For a single-sorted Mathlib language `L'`, the one-sorted language `ofLanguage L'` has the same
models and homomorphisms in `Type w` as Mathlib's first-order semantics: a term realizes, at a
point of `∏ᶜ`, as its Mathlib form at the corresponding assignment (`realize_toFOTerm`).

## Main results

* `UlmerBialgebras.Paper.realize_toSentence_iff`: an equation holds in the sense of
  `MSLanguage` iff its Mathlib sentence holds (used for `ofLanguage_model_iff`).
* `UlmerBialgebras.Paper.funMap_comm_iff`: commuting with a function symbol agrees with Mathlib
  (used for `ofLanguage_isHom_iff`).

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe w uF uR

namespace UlmerBialgebras.Paper

open CategoryTheory Limits MSLanguage FirstOrder

variable {L' : FirstOrder.Language.{uF, uR}} {M : Type w} [L'.Structure M]

/-- Realizing a term in the one-sorted family `M` is realizing its Mathlib form. -/
lemma realize_toFOTerm {n : ℕ} {Γ : Fin n → Unit}
    (x : ∏ᶜ fun i => (fun _ : Unit => M) (Γ i)) :
    ∀ {s : Unit} (t : (ofLanguage L').Term Γ s),
      (t.realize (fun _ : Unit => M)) x =
        t.toFOTerm.realize (Sum.elim Empty.elim ((Types.productIso _).hom x))
  | _, .var i => by simp [Term.realize, Term.toFOTerm]
  | _, .func f ts => by
    simp only [Term.realize, Term.toFOTerm, Structure.funMap, Language.Term.realize]
    change Language.Structure.funMap f.2
      ((Types.productIso _).hom ((Pi.lift fun i => Term.realize (fun _ : Unit => M) (ts i)) x)) = _
    congr 1
    funext i
    exact (Types.pi_lift_π_apply _ _ i x).trans (realize_toFOTerm x (ts i))

/-- An equation is realized in the one-sorted family `M` iff its Mathlib form holds for every
assignment of the variables. -/
lemma equation_realize_iff (φ : (ofLanguage L').Equation) :
    φ.Realize (fun _ : Unit => M) ↔ ∀ xs : Fin φ.ctxLen → M,
      φ.lhs.toFOTerm.realize (Sum.elim Empty.elim xs) =
        φ.rhs.toFOTerm.realize (Sum.elim Empty.elim xs) := by
  constructor
  · intro h xs
    have h1 := realize_toFOTerm ((Types.productIso _).inv xs) φ.lhs
    have h2 := realize_toFOTerm ((Types.productIso _).inv xs) φ.rhs
    simp only [Iso.inv_hom_id_apply] at h1 h2
    exact h1.symm.trans ((ConcreteCategory.congr_hom h ((Types.productIso _).inv xs)).trans h2)
  · intro h
    exact ConcreteCategory.hom_ext _ _ fun x =>
      (realize_toFOTerm x φ.lhs).trans ((h _).trans (realize_toFOTerm x φ.rhs).symm)

/-- The Mathlib sentence of an equation holds in `M` iff the equation is realized. -/
lemma realize_toSentence_iff (φ : (ofLanguage L').Equation) :
    M ⊨ φ.toSentence ↔ φ.Realize (fun _ : Unit => M) := by
  rw [equation_realize_iff]
  simp only [Equation.toSentence, Language.Sentence.Realize,
    Language.BoundedFormula.realize_alls, Language.BoundedFormula.realize_bdEqual]
  refine forall_congr' fun xs => ?_
  have : (default : Empty → M) = Empty.elim := funext fun e => e.elim
  rw [this]

variable {N : Type w} [L'.Structure N]

/-- The product map `∏ᶜ g` corresponds under `∏ᶜ ≅ (∀ j, M)` to composition with `g`. -/
lemma productIso_hom_piMap {J : Type} (g : M → N) (y : ∏ᶜ fun _ : J => M) :
    (Types.productIso.{0, w} fun _ : J => N).hom
        ((Limits.Pi.map fun _ => TypeCat.ofHom g) y) =
      g ∘ (Types.productIso.{0, w} fun _ : J => M).hom y := by
  funext j
  exact Types.pi_map_π_apply _ j y

/-- A function commutes with the interpretation of a function symbol of `ofLanguage L'` iff it
commutes with Mathlib's interpretation. -/
lemma funMap_comm_iff (f : (ofLanguage L').Functions) (g : M → N) :
    funMap (M := fun _ : Unit => M) f ≫ TypeCat.ofHom g =
        Limits.Pi.map (fun _ => TypeCat.ofHom g) ≫ funMap (M := fun _ : Unit => N) f ↔
      ∀ x : Fin f.1 → M, g (Language.Structure.funMap f.2 x) =
        Language.Structure.funMap f.2 (g ∘ x) := by
  constructor
  · intro h x
    have := ConcreteCategory.congr_hom h ((Types.productIso _).inv x)
    calc g (Language.Structure.funMap f.2 x)
        = g (Language.Structure.funMap f.2
            ((Types.productIso _).hom ((Types.productIso _).inv x))) := by
          rw [Iso.inv_hom_id_apply]
      _ = Language.Structure.funMap f.2 ((Types.productIso _).hom
            ((Limits.Pi.map fun _ => TypeCat.ofHom g) ((Types.productIso _).inv x))) := this
      _ = Language.Structure.funMap f.2 (g ∘ x) := by
          rw [productIso_hom_piMap, Iso.inv_hom_id_apply]
  · intro h
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact (h _).trans (congrArg (Language.Structure.funMap f.2) (productIso_hom_piMap g y).symm)

end UlmerBialgebras.Paper

