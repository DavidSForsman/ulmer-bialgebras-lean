module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Foundations.CategoryTheory.Factorization.OFS

/-!
# Regularity and exactness

Definition 6.4 of *A Syntactic Approach to Ulmer's Bialgebras*, together with the general
machinery used to lift these notions along PIE limits (cf. Lemma 6.5 and Theorem 6.6).

A category is **regular** if it has finite limits and a stable orthogonal factorization
system whose right class is the class of monomorphisms; it is **exact** if moreover every
internal equivalence relation is a kernel pair.

Since the right class of an orthogonal factorization system determines the left one
(`UlmerBialgebras.OFS.E_eq`), the left class of a regular category is necessarily the class
`UlmerBialgebras.extremalEpi` of morphisms left orthogonal to all monomorphisms (the extremal
epimorphisms).  In a regular category this class coincides with the class of regular
epimorphisms; accordingly, the hypotheses "`F` preserves regular epimorphisms" of
Lemma 6.5 and Theorem 6.6 are formalized as "`F` preserves the left class `extremalEpi`",
which is exactly what the proofs use.

Similarly, effectiveness of an equivalence relation `r, s : R ⇉ c` is formalized as: `r, s`
is the kernel pair of a morphism `f` *of which it is also the coequalizer*.  In a regular
category the coequalizer of a kernel pair always exists (as the paper recalls, extremal
epimorphisms are regular epimorphisms there), so this is the usual notion of a Barr-exact
category; spelling it out this way keeps the development independent of that classical
result.

## Main results

* `UlmerBialgebras.IsRegularCat`, `UlmerBialgebras.IsExactCat`: regular and exact categories
  (Definition 6.4);
* `UlmerBialgebras.IsEquivRel.map` — an internal equivalence relation is preserved by any functor
  preserving finite limits;
* `UlmerBialgebras.isRegularCat_of_faithful` — a criterion for regularity of a category equipped
  with a faithful, finite-limit-preserving functor to a regular category and a compatible
  orthogonal factorization system;
* `UlmerBialgebras.isKernelPair_of_map` — reflection of kernel pairs.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4, Lemma 6.5, Theorem 6.6
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The left class of the (extremal epi, mono) factorization: the morphisms left orthogonal
to all monomorphisms. -/
def extremalEpi (C : Type u) [Category.{v} C] : MorphismProperty C :=
  leftOrth (MorphismProperty.monomorphisms C)

/-- The left class of an orthogonal factorization system whose right class consists of the
monomorphisms is the class of extremal epimorphisms. -/
lemma OFS.e_eq_extremalEpi (S : OFS C) (h : S.M = MorphismProperty.monomorphisms C) :
    S.E = extremalEpi C := by
  rw [S.E_eq, h, extremalEpi]

/-- **Definition 6.4**: a regular category. -/
structure IsRegularCat (C : Type u) [Category.{v} C] : Prop where
  /-- A regular category has finite limits. -/
  hasFiniteLimits : HasFiniteLimits C
  /-- A regular category carries an orthogonal factorization system whose right class is
  the class of monomorphisms. -/
  exists_ofs : ∃ S : OFS C, S.M = MorphismProperty.monomorphisms C
  /-- The left class is stable under pullback. -/
  stable : (extremalEpi C).IsStableUnderBaseChange

/-- An internal equivalence relation: a jointly monomorphic pair `r, s : R ⇉ c` which is
reflexive, symmetric and transitive on each `Hom (x, c)`. -/
structure IsEquivRel {R c : C} (r s : R ⟶ c) : Prop where
  /-- `(r, s)` is a jointly monomorphic pair. -/
  jointly_mono : ∀ {x : C} (a b : x ⟶ R), a ≫ r = b ≫ r → a ≫ s = b ≫ s → a = b
  /-- Reflexivity. -/
  refl : ∀ {x : C} (f : x ⟶ c), ∃ d : x ⟶ R, d ≫ r = f ∧ d ≫ s = f
  /-- Symmetry. -/
  symm : ∀ {x : C} (d : x ⟶ R), ∃ d' : x ⟶ R, d' ≫ r = d ≫ s ∧ d' ≫ s = d ≫ r
  /-- Transitivity. -/
  trans : ∀ {x : C} (d e : x ⟶ R), d ≫ s = e ≫ r → ∃ g : x ⟶ R, g ≫ r = d ≫ r ∧ g ≫ s = e ≫ s

namespace IsEquivRel

variable {A : Type*} [Category A] {R c : A} {r s : R ⟶ c}

/-- The diagonal of an internal equivalence relation. -/
lemma diagonal (h : IsEquivRel r s) : ∃ d : c ⟶ R, d ≫ r = 𝟙 c ∧ d ≫ s = 𝟙 c :=
  h.refl (𝟙 c)

/-- The symmetry involution of an internal equivalence relation. -/
lemma involution (h : IsEquivRel r s) : ∃ t : R ⟶ R, t ≫ r = s ∧ t ≫ s = r := by
  obtain ⟨t, h1, h2⟩ := h.symm (𝟙 R)
  exact ⟨t, by simpa using h1, by simpa using h2⟩

/-- Joint monicity of `(r, s)` says exactly that `⟨r, s⟩ : R ⟶ c × c` is a monomorphism. -/
lemma mono_lift [HasBinaryProduct c c] (h : IsEquivRel r s) : Mono (prod.lift r s) := by
  constructor
  intro Z g₁ g₂ hg
  refine h.jointly_mono g₁ g₂ ?_ ?_
  · have := hg =≫ (prod.fst : c ⨯ c ⟶ c)
    simpa using this
  · have := hg =≫ (prod.snd : c ⨯ c ⟶ c)
    simpa using this

/-- An internal equivalence relation is preserved by any functor preserving finite
limits. -/
theorem map [HasFiniteLimits A] (U : A ⥤ C) [PreservesFiniteLimits U] (h : IsEquivRel r s) :
    IsEquivRel (U.map r) (U.map s) := by
  obtain ⟨d, hd1, hd2⟩ := h.diagonal
  obtain ⟨t, ht1, ht2⟩ := h.involution
  have hmono : Mono (prod.lift r s) := h.mono_lift
  have hUmono : Mono (U.map (prod.lift r s)) := inferInstance
  have hfan : IsLimit (BinaryFan.mk (U.map (prod.fst : c ⨯ c ⟶ c))
      (U.map (prod.snd : c ⨯ c ⟶ c))) :=
    isLimitMapConeBinaryFanEquiv U _ _ (isLimitOfPreserves U (prodIsProd c c))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x a b ha hb
    refine (cancel_mono (U.map (prod.lift r s))).1 ?_
    refine BinaryFan.IsLimit.hom_ext hfan ?_ ?_
    · simp only [BinaryFan.mk_fst, Category.assoc, ← U.map_comp, prod.lift_fst]
      exact ha
    · simp only [BinaryFan.mk_snd, Category.assoc, ← U.map_comp, prod.lift_snd]
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
    have hpb : IsPullback (pullback.fst s r) (pullback.snd s r) s r := IsPullback.of_hasPullback s r
    have hpbU := hpb.map U
    obtain ⟨g, hg1, hg2⟩ := h.trans (pullback.fst s r) (pullback.snd s r) pullback.condition
    refine ⟨hpbU.lift a b hab ≫ U.map g, ?_, ?_⟩
    · rw [Category.assoc, ← U.map_comp, hg1, U.map_comp, ← Category.assoc, hpbU.lift_fst]
    · rw [Category.assoc, ← U.map_comp, hg2, U.map_comp, ← Category.assoc, hpbU.lift_snd]

end IsEquivRel

/-- A kernel pair is an internal equivalence relation. -/
theorem IsKernelPair.isEquivRel {A : Type*} [Category A] {R c d : A} {f : c ⟶ d} {r s : R ⟶ c}
    (h : IsKernelPair f r s) : IsEquivRel r s where
  jointly_mono _ _ ha hb := h.hom_ext ha hb
  refl g := ⟨h.lift g g rfl, h.lift_fst _ _ _, h.lift_snd _ _ _⟩
  symm d := ⟨h.lift (d ≫ s) (d ≫ r) (by
      rw [Category.assoc, Category.assoc, ← h.w]), h.lift_fst _ _ _, h.lift_snd _ _ _⟩
  trans d e hde := ⟨h.lift (d ≫ r) (e ≫ s) (by
      rw [Category.assoc, Category.assoc, h.w, ← Category.assoc, hde, Category.assoc,
        ← h.w]), h.lift_fst _ _ _, h.lift_snd _ _ _⟩

/-- **Definition 6.4**: an exact category is a regular category in which every internal
equivalence relation is the kernel pair of its coequalizer. -/
structure IsExactCat (C : Type u) [Category.{v} C] : Prop where
  /-- An exact category is regular. -/
  regular : IsRegularCat C
  /-- Every internal equivalence relation is effective. -/
  effective : ∀ {R c : C} (r s : R ⟶ c), IsEquivRel r s →
    ∃ (d : C) (f : c ⟶ d) (hk : IsKernelPair f r s),
      Nonempty (IsColimit (Cofork.ofπ f hk.w))

/-- A functor preserves the coequalizers of kernel pairs. -/
def PreservesCoequalizersOfKernelPairs (F : C ⥤ D) : Prop :=
  ∀ ⦃R x y : C⦄ (r s : R ⟶ x) (f : x ⟶ y) (hk : IsKernelPair f r s)
    (_ : IsColimit (Cofork.ofπ f hk.w)),
    Nonempty (IsColimit (F.mapCocone (Cofork.ofπ f hk.w)))

/-! ## General criteria -/

section Criteria

variable {A : Type*} [Category A]

/-- A functor reflecting pullbacks reflects kernel pairs. -/
lemma isKernelPair_of_map (U : A ⥤ C) [ReflectsLimitsOfShape WalkingCospan U] {R x y : A}
    {f : x ⟶ y} {r s : R ⟶ x} (w : r ≫ f = s ≫ f)
    (h : IsKernelPair (U.map f) (U.map r) (U.map s)) : IsKernelPair f r s := by
  refine ⟨⟨w⟩, ⟨?_⟩⟩
  exact isLimitOfReflects U ((isLimitMapConePullbackConeEquiv U w).symm h.isLimit)

/-- **Regularity criterion.** If `U : A ⥤ C` is faithful and preserves finite limits, `A`
has finite limits, `C` is regular, and `S` is an orthogonal factorization system on `A`
whose right class consists of the morphisms sent by `U` to monomorphisms and whose left
class consists of the morphisms sent by `U` to extremal epimorphisms, then `A` is
regular. -/
theorem isRegularCat_of_faithful (U : A ⥤ C) [U.Faithful] [HasFiniteLimits A]
    [PreservesFiniteLimits U] (hC : IsRegularCat C) (S : OFS A)
    (hM : ∀ ⦃x y : A⦄ (f : x ⟶ y), S.M f ↔ Mono (U.map f))
    (hE : ∀ ⦃x y : A⦄ (f : x ⟶ y), S.E f ↔ extremalEpi C (U.map f)) :
    IsRegularCat A := by
  have hMmono : S.M = MorphismProperty.monomorphisms A := by
    ext x y f
    rw [hM f]
    constructor
    · intro h; exact U.mono_of_mono_map h
    · intro h
      have : Mono f := h
      infer_instance
  have hSE : S.E = extremalEpi A := S.e_eq_extremalEpi hMmono
  refine ⟨inferInstance, ⟨S, hMmono⟩, ⟨?_⟩⟩
  intro X Y Y' Z f g f' g' sq hg
  rw [← hSE] at hg ⊢
  rw [hE] at hg ⊢
  exact hC.stable.of_isPullback (sq.map U) hg

end Criteria

end UlmerBialgebras
