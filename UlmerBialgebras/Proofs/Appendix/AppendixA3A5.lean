module

public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3
public import UlmerBialgebras.Proofs.Appendix.AppendixReverse
public import UlmerBialgebras.Proofs.Appendix.AppendixForest
public import UlmerBialgebras.Proofs.Appendix.AppendixLinear
public import UlmerBialgebras.Proofs.Appendix.AppendixLinearDensity

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Checked statements that are not numbered results of the paper

Proofs of the checked theorems that the paper uses without a number of their own:

* Section 2.2: the representables `K(x, -)` preserve and jointly reflect products, inserters and
  equifiers (`rep_preserves_prod`, …, `rep_reflects_equif`);
* Appendix A: the point, arrow and three-object probes (`appendix_unit_classification`,
  `appendix_arrow_classification`, `appendix_arrow_transformations`,
  `appendix_three_classification`), the fully faithful part of Theorem A.5
  (`appendix_local_density`) and two related density results (`appendix_tiny_biDense`,
  `appendix_small_biDense`).

## Main results

* `UlmerBialgebras.Paper.rep_preserves_prod`: the representable `K(x, -)` sends a product to a
  product (Section 2.2).
* `UlmerBialgebras.Paper.rep_reflects_prod`: the representables `K(x, -)` jointly reflect products.
* `UlmerBialgebras.Paper.rep_preserves_ins`: `K(x, -)` sends an inserter to an inserter.
* `UlmerBialgebras.Paper.rep_reflects_ins`: the representables `K(x, -)` jointly reflect inserters.
* `UlmerBialgebras.Paper.rep_preserves_equif`: `K(x, -)` sends an equifier to an equifier.
* `UlmerBialgebras.Paper.rep_reflects_equif`: the representables `K(x, -)` jointly reflect
  equifiers.
* `UlmerBialgebras.Paper.appendix_three_classification`: Lemma A.3 for a two-edge linear forest, the
  universal property of the three-object probe of Definition A.4.
* `UlmerBialgebras.Paper.appendix_local_density`: the fully faithful part of Theorem A.5.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2.2 and
  Appendix A
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
-/

namespace UlmerBialgebras.Paper

section Appendix

universe w v u

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Lemma A.3** ([forsman2026syntactic]) for the one-edge forest: the arrow probe is free on its
label. -/
theorem appendix_arrow_classification (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) :
    Function.Bijective (fun F : arrowVCat.{w, v, u} Z x ⟶ C =>
      (⟨F.obj .src, F.obj .tgt, F.emap .src .tgt⟩ :
        Σ c : C.carrier, Σ c' : C.carrier, x ⟶ (c ⟶[V] c'))) := by
  exact (Appendix.arrowFunctorDataEquiv Z x C).bijective

/-- The fully faithful part of Theorem A.5 ([forsman2026syntactic]): the exact linear class of
probes (point, arrow and three-object categories `𝟑_{x,y}` included) is cell-dense in `CAT_V`,
sufficing for reconstruction and uniqueness of enriched natural transformations. -/
theorem appendix_local_density (Z : MonoidalInitial V) :
    IsACellDense (Obj := Appendix.PaperVCat.{w, v, u} V)
      (Appendix.IsPaperLinearProbe.{w, v, u} Z) := by
  exact isACellDense_of_probes (Appendix.reverseInitial Z) _ (Or.inl rfl)
    (fun x => Or.inr (Or.inl ⟨x, rfl⟩))

/-- **Lemma A.3** ([forsman2026syntactic]) for a two-edge linear forest, in the paper's tensor
order. This is the universal property of the three-object probe of Definition A.4. -/
theorem appendix_three_classification (Z : MonoidalInitial V) (x y : V)
    (C : Appendix.PaperVCat.{w, v, u} V) :
    Function.Bijective (fun F : Appendix.paperThreeVCat.{w, v, u} Z x y ⟶ C =>
      (⟨F.obj .zero, F.obj .one, F.obj .two,
        (F.emap .zero .one).unmop, (F.emap .one .two).unmop⟩ :
        Σ c₀ : C.carrier, Σ c₁ : C.carrier, Σ c₂ : C.carrier,
          (x ⟶ MonoidalOpposite.unmop (c₀ ⟶[Vᴹᵒᵖ] c₁)) ×
            (y ⟶ MonoidalOpposite.unmop (c₁ ⟶[Vᴹᵒᵖ] c₂)))) := by
  exact (Appendix.paperThreeFunctorDataEquiv Z x y C).bijective

end Appendix

end UlmerBialgebras.Paper
