module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Foundations.CategoryTheory.Factorization.RegularTools
public import Foundations.CategoryTheory.Factorization.ExactCriterion

/-!
# Transfer of regularity and exactness along pullback-preserving functors

Helper results for Lemma 6.5 (`lem_6_5` in `UlmerBialgebras/Proofs/Sec6/Sec6Factorization.lean`).
The development's
transfer lemma `isRegularCat_of_faithful` asks the functor to preserve finite limits; the
paper's Lemma 6.5 only asks it to preserve pullbacks. The results here work under that weaker
hypothesis.

## Main results

* `UlmerBialgebras.Paper.extremalEpi_of_regularEpi'`: a regular epimorphism is left orthogonal to
  all monos.
* `UlmerBialgebras.Paper.IsEquivRel.map_of_preservesPullbacks`: a pullback-preserving functor out of
  a finitely complete category preserves internal equivalence relations.
* `UlmerBialgebras.Paper.extremalEpi_of_map_extremalEpi`: a conservative pullback-preserving functor
  reflects the left orthogonality to monos.
* `UlmerBialgebras.Paper.mono_map_of_isKernelPair`: in a regular category, the second factor of the
  canonical factorization through the coequalizer of a kernel pair becomes a mono.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.5
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [T. Wißmann, *Minimality notions via factorization systems and examples*][Wissmann2022Minimality]
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section General

variable {C : Type u} [Category.{v} C]

/-- A regular epimorphism is left orthogonal to every monomorphism. -/
lemma extremalEpi_of_regularEpi' {X Y : C} {f : X ⟶ Y} (h : RegularEpi f) : extremalEpi C f := by
  intro c d m hm u v huv
  have : Mono m := hm
  have : IsRegularEpi f := isRegularEpi_of_regularEpi h
  have : StrongEpi f := inferInstance
  have : Epi f := h.epi
  have sq : CommSq u f m v := ⟨huv⟩
  refine ⟨sq.lift, ⟨sq.fac_left, sq.fac_right⟩, ?_⟩
  rintro k ⟨hk1, -⟩
  exact (cancel_epi f).1 (hk1.trans sq.fac_left.symm)

end General

section Transfer

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A pullback-preserving functor out of a finitely complete category preserves internal
equivalence relations. (Joint monicity is preserved because `x × x` is the pullback of `x`
and `x` over the terminal object.) -/
theorem IsEquivRel.map_of_preservesPullbacks [HasFiniteLimits D] (U : D ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U] {R c : D} {r s : R ⟶ c} (h : IsEquivRel r s) :
    IsEquivRel (U.map r) (U.map s) := by
  -- `R → c × c` (as the pullback over `⊤`) is monic, and `U` keeps the pullback squares; the
  -- four axioms then transport along `U`.
  obtain ⟨d, hd1, hd2⟩ := h.diagonal
  obtain ⟨t, ht1, ht2⟩ := h.involution
  let τ : c ⟶ ⊤_ D := terminal.from c
  let ι : R ⟶ pullback τ τ := pullback.lift r s (terminal.hom_ext _ _)
  have hι : Mono ι := by
    constructor
    intro Z a b hab
    refine h.jointly_mono a b ?_ ?_
    · simpa [ι] using hab =≫ pullback.fst τ τ
    · simpa [ι] using hab =≫ pullback.snd τ τ
  have hpb := (IsPullback.of_hasPullback τ τ).map U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x a b ha hb
    refine (cancel_mono (U.map ι)).1 (hpb.hom_ext ?_ ?_)
    · simp only [Category.assoc, ← U.map_comp, ι, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, ← U.map_comp, ι, pullback.lift_snd]
      exact hb
  · intro x f
    refine ⟨f ≫ U.map d, ?_, ?_⟩
    · rw [Category.assoc, ← U.map_comp, hd1, U.map_id, Category.comp_id]
    · rw [Category.assoc, ← U.map_comp, hd2, U.map_id, Category.comp_id]
  · intro x e
    refine ⟨e ≫ U.map t, ?_, ?_⟩
    · rw [Category.assoc, ← U.map_comp, ht1]
    · rw [Category.assoc, ← U.map_comp, ht2]
  · intro x a b hab
    have hpb' : IsPullback (pullback.fst s r) (pullback.snd s r) s r :=
      IsPullback.of_hasPullback s r
    have hpbU := hpb'.map U
    obtain ⟨g, hg1, hg2⟩ := h.trans (pullback.fst s r) (pullback.snd s r) pullback.condition
    refine ⟨hpbU.lift a b hab ≫ U.map g, ?_, ?_⟩
    · rw [Category.assoc, ← U.map_comp, hg1, U.map_comp, ← Category.assoc, hpbU.lift_fst]
    · rw [Category.assoc, ← U.map_comp, hg2, U.map_comp, ← Category.assoc, hpbU.lift_snd]

/-- A conservative pullback-preserving functor reflects the left orthogonality to all
monomorphisms. -/
lemma extremalEpi_of_map_extremalEpi [HasPullbacks D] (U : D ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U] [U.ReflectsIsomorphisms] {a b : D} {e : a ⟶ b}
    (he : extremalEpi C (U.map e)) : extremalEpi D e := by
  intro c d n hn u v huv
  have : Mono n := hn
  let w : a ⟶ pullback n v := pullback.lift u e huv
  have hUn : MorphismProperty.monomorphisms C (U.map (pullback.snd n v)) := by
    rw [MorphismProperty.monomorphisms.iff]; infer_instance
  obtain ⟨k, ⟨-, hk2⟩, -⟩ := he _ hUn (U.map w) (𝟙 _)
    (by rw [← U.map_comp, pullback.lift_snd, Category.comp_id])
  have : IsSplitEpi (U.map (pullback.snd n v)) := ⟨⟨⟨k, hk2⟩⟩⟩
  have : IsIso (U.map (pullback.snd n v)) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (pullback.snd n v) := isIso_of_reflects_iso _ U
  refine ⟨inv (pullback.snd n v) ≫ pullback.fst n v, ⟨?_, ?_⟩, ?_⟩
  · have : e = w ≫ pullback.snd n v := (pullback.lift_snd u e huv).symm
    rw [this, Category.assoc, IsIso.hom_inv_id_assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · rintro k' ⟨-, hk'2⟩
    rw [← cancel_mono n, hk'2, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- In a regular category `C`: let `(U a, U b)` be a kernel pair of `U f`, let `e` coequalize
`(a, b)` with `U e` left orthogonal to monos, and let `e ≫ m = f`. Then `U m` is a mono. -/
lemma mono_map_of_isKernelPair (hC : IsRegularCat C) (U : D ⥤ C) {R x y Q : D} {f : x ⟶ y}
    {a b : R ⟶ x} (hk : IsKernelPair (U.map f) (U.map a) (U.map b)) {e : x ⟶ Q} {m : Q ⟶ y}
    (hw : a ≫ e = b ≫ e) (hfac : e ≫ m = f) (he : extremalEpi C (U.map e)) :
    Mono (U.map m) := by
  have := hC.hasFiniteLimits
  constructor
  intro Z g h hgh
  obtain ⟨Z1, p1, g1, hp1, hg1⟩ := hC.exists_cover he g
  obtain ⟨Z2, p2, h2, hp2, hh2⟩ := hC.exists_cover he (p1 ≫ h)
  have hsame : (p2 ≫ g1) ≫ U.map f = h2 ≫ U.map f := by
    rw [← hfac, U.map_comp, Category.assoc, ← Category.assoc g1, hg1, ← Category.assoc h2, hh2]
    simp only [Category.assoc]
    rw [hgh]
  have hw' : U.map a ≫ U.map e = U.map b ≫ U.map e := by rw [← U.map_comp, hw, U.map_comp]
  have key : (p2 ≫ p1) ≫ g = (p2 ≫ p1) ≫ h := by
    calc (p2 ≫ p1) ≫ g = (p2 ≫ g1) ≫ U.map e := by simp only [Category.assoc, hg1]
      _ = (hk.lift _ _ hsame ≫ U.map a) ≫ U.map e := by rw [hk.lift_fst]
      _ = (hk.lift _ _ hsame ≫ U.map b) ≫ U.map e := by rw [Category.assoc, hw', ← Category.assoc]
      _ = h2 ≫ U.map e := by rw [hk.lift_snd]
      _ = (p2 ≫ p1) ≫ h := by rw [hh2, Category.assoc]
  have : Epi (p2 ≫ p1) := extremalEpi_epi (extremalEpi_comp hp2 hp1)
  exact (cancel_epi _).1 key

end Transfer

end UlmerBialgebras.Paper
