module

public import UlmerBialgebras.Models.CoHom
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-!
# Split pairs in `K^co`

A pair is split for post-composition in `K^co` exactly when the corresponding pair in `K`
is cosplit. The same splitting maps witness both statements, with their roles exchanged.

## Main results

* `UlmerBialgebras.Co.postcomp_isSplitPair_iff`: a pair is split for post-composition in `K^co` iff
  the corresponding pair is cosplit for post-composition in `K`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.2 and Corollary 5.3
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Co

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Split pairs in the dual hom-category are cosplit pairs in the original hom-category. -/
lemma postcomp_isSplitPair_iff (x : Obj) {a b : Obj} (v : a ⟶ b)
    {f g : x ⟶ a} (α β : g ⟶ f) :
    (postcomp (Obj := Co Obj) (Co.op x) (hom v)).IsSplitPair (cell α) (cell β) ↔
      (postcomp x v).IsCosplitPair α β := by
  constructor
  · intro h
    obtain ⟨Z, π, ⟨q⟩⟩ := h.splittable
    refine ⟨⟨Z, π, ⟨{
      leftRetraction := q.rightSection
      rightRetraction := q.leftSection
      condition := ?_
      ι_leftRetraction := ?_
      bottom_rightRetraction := ?_
      top_rightRetraction := ?_ }⟩⟩⟩
    · exact q.condition
    · exact q.rightSection_π
    · exact q.leftSection_bottom
    · exact q.leftSection_top
  · intro h
    obtain ⟨Z, ι, ⟨q⟩⟩ := h.splittable
    refine ⟨⟨Z, ι, ⟨{
      rightSection := q.leftRetraction
      leftSection := q.rightRetraction
      condition := ?_
      rightSection_π := ?_
      leftSection_bottom := ?_
      leftSection_top := ?_ }⟩⟩⟩
    · exact q.condition
    · exact q.ι_leftRetraction
    · exact q.bottom_rightRetraction
    · exact q.top_rightRetraction

end UlmerBialgebras.Co
