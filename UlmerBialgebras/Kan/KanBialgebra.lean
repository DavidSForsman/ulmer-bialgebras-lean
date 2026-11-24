module

public import UlmerBialgebras.Kan.CoKan
public import UlmerBialgebras.Kan.KanComp
public import UlmerBialgebras.Kan.KanInserter
public import UlmerBialgebras.Kan.KanEquifier

/-!
# Creation of Kan extensions by bialgebraic objects

Corollary 4.8 combines creation by an inserter and an equifier. This common proof is stated
using the PIE data alone, so both model-level and paper-level corollaries can use it
without an import cycle. The right case is the left case in `K^co`.

## Main results

* `UlmerBialgebras.Inserter.strictlyCreates_leftKan_equifier`: the canonical 1-cell out of an
  equifier over an inserter strictly creates those left Kan extensions that `f` preserves and whose
  quotient initiality `f'` preserves (Corollary 4.8).
* `UlmerBialgebras.Inserter.strictlyCreates_rightKan_equifier`: the dual statement for right Kan
  extensions (Corollary 4.8).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.8
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3 and 3.4
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Inserter

/-- **Corollary 4.8** ([forsman2026syntactic]) for an inserter followed by an equifier. -/
theorem strictlyCreates_leftKan_equifier {c x y : Obj} {f g : c ⟶ x}
    (Ins : Inserter f g) {f' g' : c ⟶ y} {α β : Ins.u ≫ f' ⟶ Ins.u ≫ g'}
    (E : Equifier α β) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : PreservesLeftKan k (d ≫ (E.e ≫ Ins.u)) f)
    (hf' : ∀ L : LeftExt k (d ≫ (E.e ≫ Ins.u)), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ (E.e ≫ Ins.u)) f').obj L)) :
    StrictlyCreatesLeftKan k d (E.e ≫ Ins.u) := by
  have hins : StrictlyCreatesLeftKan k (d ≫ E.e) Ins.u :=
    Inserter.strictlyCreates_leftKan Ins k (d ≫ E.e)
      (preservesLeftKan_congr (Category.assoc d E.e Ins.u).symm rfl hf)
  refine strictlyCreatesLeftKan_comp k d E.e Ins.u hins ?_
  intro b hb
  obtain ⟨⟨a₀, ha₀, -⟩, hinit⟩ :=
    hins _ (isInitial_reindex k (Category.assoc d E.e Ins.u).symm hb)
  refine Equifier.strictlyCreates_leftKan E k d ?_
  intro L hL
  refine quotientInitial_of_reindex k (Category.assoc (d ≫ E.e) Ins.u f').symm ?_
  rw [← LeftExt.push_push_obj]
  have hiso : (LeftExt.push k (d ≫ E.e) Ins.u).obj L ≅
      (LeftExt.reindex k (Category.assoc d E.e Ins.u).symm).obj b :=
    (LeftExt.push k (d ≫ E.e) Ins.u).mapIso
      (IsInitial.uniqueUpToIso hL.some (hinit a₀ ha₀).some) ≪≫ eqToIso ha₀
  refine QuotientInitial.of_iso
    ((LeftExt.push k ((d ≫ E.e) ≫ Ins.u) f').mapIso hiso).symm ?_
  rw [LeftExt.push_reindex_obj]
  exact quotientInitial_reindex _ _ (hf' b hb)

/-- The right half of Corollary 4.8 is the left half applied in `K^co`. -/
theorem strictlyCreates_rightKan_equifier {c x y : Obj} {f g : c ⟶ x}
    (Ins : Inserter f g) {f' g' : c ⟶ y} {α β : Ins.u ≫ f' ⟶ Ins.u ≫ g'}
    (E : Equifier α β) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : PreservesRightKan k (d ≫ (E.e ≫ Ins.u)) g)
    (hg' : ∀ R : RightExt k (d ≫ (E.e ≫ Ins.u)), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ (E.e ≫ Ins.u)) g').obj R)) :
    StrictlyCreatesRightKan k d (E.e ≫ Ins.u) := by
  refine (Co.strictlyCreatesLeftKan_iff k d (E.e ≫ Ins.u)).1 ?_
  refine strictlyCreates_leftKan_equifier (Co.inserter Ins) (Co.equifier E)
    (Co.hom k) (Co.hom d)
    ((Co.preservesLeftKan_iff k (d ≫ (E.e ≫ Ins.u)) g).2 hg) ?_
  intro L hL
  rw [Co.quotientInitial_iff]
  exact (congrArg Subterminal (Co.toRight_push k (d ≫ (E.e ≫ Ins.u)) g' L)).mpr
    (hg' _ ((Co.isInitial_iff L).1 hL))

end Inserter

namespace Paper

/-- An equifier of `η, θ` is an equifier of `η, θ` conjugated by identity 2-cells
`eqToHom`. -/
def Equifier.conj {a b : Obj} {f g f' g' : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    (h₁ : f' = f) (h₂ : g = g') :
    Equifier (eqToHom h₁ ≫ η ≫ eqToHom h₂) (eqToHom h₁ ≫ θ ≫ eqToHom h₂) where
  pt := E.pt
  e := E.e
  cond := by subst h₁; subst h₂; simpa using E.cond
  lift h H := E.lift h (by subst h₁; subst h₂; simpa using H)
  lift_e h _ := E.lift_e h _
  lift_uniq k h _ hk := E.lift_uniq k h _ hk
  full β := E.full β
  faithful α β := E.faithful α β

end Paper

end UlmerBialgebras
