module

public import UlmerBialgebras.Appendix.VCat

/-!
# Conjugating hom-objects by two isomorphisms

One can conjugate the hom-objects of a `V`-category by a family of isomorphisms `k e ≅ e`
indexed by the objects themselves.  The reconstruction of a `V`-functor from a
pseudonatural family on the small probes (`VCatHomDense.lean`) needs the same operation in a
slightly more flexible form: the two isomorphisms at the source and at the target are
unrelated.

* `UlmerBialgebras.eHomConj₂ p q : (a' ⟶[V] b') ⟶ (a ⟶[V] b)` for `p : a ≅ a'` and `q : b ≅ b'`;
* `UlmerBialgebras.eComp_eHomConj₂` — compatibility with the enriched composition;
* `UlmerBialgebras.eHomEquiv_comp_eHomConj₂` — the effect on names of morphisms;
* `UlmerBialgebras.eHomConj₂_trans` — compatibility with composition of the isomorphisms.

## Main results

* `UlmerBialgebras.eHomConj₂`: conjugation `(a' ⟶[V] b') ⟶ (a ⟶[V] b)` of a hom-object by
  isomorphisms `a ≅ a'` and `b ≅ b'`.
* `UlmerBialgebras.eComp_eHomConj₂`: conjugation is compatible with the enriched composition.
* `UlmerBialgebras.eHomConj₂_trans`: conjugation is compatible with composition of the isomorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Appendix A
  (proof of Theorem A.5)
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
variable {E : Type u} [Category.{w} E] [EnrichedOrdinaryCategory V E]

/-- Conjugation of a hom-object by an isomorphism at the source and one at the target. -/
def eHomConj₂ {a a' b b' : E} (p : a ≅ a') (q : b ≅ b') :
    (a' ⟶[V] b') ⟶ (a ⟶[V] b) :=
  eHomWhiskerRight V p.hom b' ≫ eHomWhiskerLeft V a q.inv

/-- **Conjugation is compatible with the enriched composition.** -/
lemma eComp_eHomConj₂ {a a' b b' c c' : E} (p : a ≅ a') (q : b ≅ b') (r : c ≅ c') :
    eComp V a' b' c' ≫ eHomConj₂ p r
      = (eHomConj₂ p q ⊗ₘ eHomConj₂ q r) ≫ eComp V a b c := by
  have hb : eComp V a b' c
      = (eHomWhiskerLeft V a q.inv ⊗ₘ eHomWhiskerRight V q.hom c) ≫ eComp V a b c := by
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
    exact (eHom_whisker_cancel V (X := a) (Z := c) q.symm).symm
  dsimp only [eHomConj₂]
  rw [← Category.assoc, eComp_eHomWhiskerRight, Category.assoc, eComp_eHomWhiskerLeft,
    ← Category.assoc, ← MonoidalCategory.tensorHom_def, hb, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, eHom_whisker_exchange]

/-- The name of a morphism conjugated by two isomorphisms. -/
lemma eHomEquiv_comp_eHomConj₂ {a a' b b' : E} (p : a ≅ a') (q : b ≅ b') (f : a' ⟶ b') :
    eHomEquiv V f ≫ eHomConj₂ p q = eHomEquiv V (p.hom ≫ f ≫ q.inv) := by
  dsimp only [eHomConj₂]
  rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerRight, eHomEquiv_comp_eHomWhiskerLeft,
    Category.assoc]

/-- Conjugation by a composite of isomorphisms. -/
lemma eHomConj₂_trans {a a' a'' b b' b'' : E} (p : a ≅ a') (p' : a' ≅ a'') (q : b ≅ b')
    (q' : b' ≅ b'') :
    eHomConj₂ (V := V) p' q' ≫ eHomConj₂ p q = eHomConj₂ (p ≪≫ p') (q ≪≫ q') := by
  dsimp only [eHomConj₂]
  rw [Category.assoc, reassoc_of% (eHom_whisker_exchange V p.hom q'.inv), ← Category.assoc,
    ← eHomWhiskerRight_comp]
  simp [← eHomWhiskerLeft_comp]

end UlmerBialgebras
