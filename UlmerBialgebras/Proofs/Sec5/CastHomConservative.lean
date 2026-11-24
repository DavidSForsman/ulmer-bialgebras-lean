module

public import UlmerBialgebras.Proofs.Sec5.BiDense

/-!
# Conservativity along an equality of base objects

This supplies the cast-hom conservativity input for Corollary 5.3. Both comonadic forms
of the corollary are derived from the monadic forms in
`UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean`, via `K^co`.

## Main results

* `UlmerBialgebras.Paper.postcomp_castHom_reflectsIsomorphisms`: for an equality `h : a = b` of
  objects, `K(x, castHom h)` reflects isomorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 5.3
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- For an equality `h : a = b` of objects, `K(x, castHom h)` reflects isomorphisms (it is
`K(x, 𝟙 a)` after `subst`); input for Corollary 5.3 of [forsman2026syntactic]. -/
lemma postcomp_castHom_reflectsIsomorphisms {a b : Obj} (h : a = b) (x : Obj) :
    (postcomp x (castHom h)).ReflectsIsomorphisms := by
  subst h
  change (postcomp x (𝟙 a)).ReflectsIsomorphisms
  rw [postcomp_id₁]
  infer_instance

end UlmerBialgebras.Paper
