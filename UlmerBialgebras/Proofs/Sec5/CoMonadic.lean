module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Monadicity.CoAdj
public import UlmerBialgebras.Monadicity.CoPairs
public import UlmerBialgebras.Monadicity.CoLimits
public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Monad.Comonadicity

/-!
# Monadicity and comonadicity under reversal of 2-cells

Beck's criteria identify monadicity with creation of split coequalizers and comonadicity
with creation of cosplit equalizers. The hom-category translations for `K^co` exchange
these criteria, while `Co.adj` exchanges the adjoints.

## Main results

* `UlmerBialgebras.Paper.isComonadic2_iff_monadic_co`: a 1-cell `g` is comonadic in `K` if and only
  if `Co.hom g` is monadic in `K^co`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 5.1 and Lemma 5.2
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Comonadicity in `K` is monadicity in `K^co`. -/
theorem isComonadic2_iff_monadic_co {a b : Obj} (g : a ⟶ b) :
    IsComonadic2 g ↔ IsMonadic2 (Obj := Co Obj) (Co.hom g) := by
  constructor
  · rintro ⟨h, A, heq⟩
    refine ⟨Co.hom h, Co.adj A, fun x => ?_⟩
    let : ComonadicLeftAdjoint (postcomp (Co.unop x) g) :=
      ⟨postcomp (Co.unop x) h, A.postcompAdj (Co.unop x), heq (Co.unop x)⟩
    let : Monad.CreatesColimitOfIsSplitPair
        (postcomp (Obj := Co Obj) x (Co.hom g)) := by
      refine ⟨fun {f f'} α β hsp => ?_⟩
      let α' := Co.uncell (Obj := Obj) α
      let β' := Co.uncell (Obj := Obj) β
      haveI := (Co.postcomp_isSplitPair_iff (Co.unop x) g α' β').1 hsp
      letI : CreatesLimit (parallelPair (C := (Co.unop x ⟶ a)) α' β') (postcomp (Co.unop x) g) :=
        Comonad.createsFSplitEqualizersOfComonadic (F := postcomp (Co.unop x) g) α' β'
      exact Co.postcompCreatesCoequalizer (Co.unop x) g α' β'
    exact (Monad.monadicOfCreatesGSplitCoequalizers ((Co.adj A).postcompAdj x)).eqv
  · rintro ⟨h, A, heq⟩
    refine ⟨h, Co.unadj (Obj := Obj) (f := g) (g := h) A, fun x => ?_⟩
    let : MonadicRightAdjoint (postcomp (Obj := Co Obj) (Co.op x) (Co.hom g)) :=
      ⟨postcomp (Obj := Co Obj) (Co.op x) h, A.postcompAdj (Co.op x), heq (Co.op x)⟩
    let : Comonad.CreatesLimitOfIsCosplitPair (postcomp x g) := by
      refine ⟨fun {f f'} α β hsp => ?_⟩
      haveI := (Co.postcomp_isSplitPair_iff x g α β).2 hsp
      letI : CreatesColimit (parallelPair (Co.cell α) (Co.cell β))
          (postcomp (Obj := Co Obj) (Co.op x) (Co.hom g)) :=
        Monad.createsGSplitCoequalizersOfMonadic _ (Co.cell α) (Co.cell β)
      exact Co.postcompCreatesEqualizer x g α β
    exact (Comonad.comonadicOfCreatesFSplitEqualizers
      ((Co.unadj (Obj := Obj) (f := g) (g := h) A).postcompAdj x)).eqv

end UlmerBialgebras.Paper
