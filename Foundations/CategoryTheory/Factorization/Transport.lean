module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Foundations.CategoryTheory.Factorization.RegularExact

/-!
# Transport of factorization systems, regularity and exactness along an equivalence

This development deduces representable (hom-category-wise) versions of the results of
Section 6 of *A Syntactic Approach to Ulmer's Bialgebras* (Theorem 6.3, Theorem 6.6) from the
1-categorical ones by comparing the hom-category of a PIE limit with the corresponding PIE
limit of hom-categories.  (An earlier version of the paper stated these representable
versions; the current one states the results in `CAT`.)  The comparison is an equivalence of
categories, so we first record that all the notions of Section 6 are invariant under
equivalences.

## Main results

* `UlmerBialgebras.OFS.transport` — an orthogonal factorization system transports along an
  equivalence (its two classes are the inverse images along `e.inverse`);
* `UlmerBialgebras.IsRegularCat.of_equivalence`, `UlmerBialgebras.IsExactCat.of_equivalence` —
  regularity and exactness are invariant under equivalences of categories.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.1,
  Definition 6.4, Theorem 6.3, Theorem 6.6
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

namespace OFS

variable (S : OFS A) (e : A ≌ B)

/-- `S.E (e.inverse.map (e.functor.map a))` holds iff `S.E a` holds. -/
lemma e_inverse_functor_map {X Y : A} (a : X ⟶ Y) :
    S.E (e.inverse.map (e.functor.map a)) ↔ S.E a := by
  rw [Equivalence.inv_fun_map]
  exact S.e_conj_iff _ _ _

/-- `S.M (e.inverse.map (e.functor.map a))` holds iff `S.M a` holds. -/
lemma m_inverse_functor_map {X Y : A} (a : X ⟶ Y) :
    S.M (e.inverse.map (e.functor.map a)) ↔ S.M a := by
  rw [Equivalence.inv_fun_map]
  exact S.m_conj_iff _ _ _

/-- Transport of an orthogonal factorization system along an equivalence of categories. -/
def transport : OFS B :=
  OFS.mk' (S.E.inverseImage e.inverse) (S.M.inverseImage e.inverse)
    (by
      intro X Y f
      obtain ⟨Z, a, b, ha, hb, hab⟩ := S.fact (e.inverse.map f)
      refine ⟨e.functor.obj Z, (e.counitIso.app X).inv ≫ e.functor.map a,
        e.functor.map b ≫ (e.counitIso.app Y).hom, ?_, ?_, ?_⟩
      · rw [MorphismProperty.inverseImage_iff, e.inverse.map_comp]
        exact S.e_comp (S.e_of_isIso _) ((S.e_inverse_functor_map e a).2 ha)
      · rw [MorphismProperty.inverseImage_iff, e.inverse.map_comp]
        exact S.m_comp ((S.m_inverse_functor_map e b).2 hb) (S.m_of_isIso _)
      · rw [Category.assoc, ← Category.assoc (e.functor.map a), ← e.functor.map_comp, hab]
        simp)
    (by
      intro X Y Z W e₁ m he hm f g hsq
      have hsq' : e.inverse.map f ≫ e.inverse.map m = e.inverse.map e₁ ≫ e.inverse.map g := by
        rw [← e.inverse.map_comp, ← e.inverse.map_comp, hsq]
      obtain ⟨θ, ⟨h1, h2⟩, huniq⟩ := S.orth he hm _ _ hsq'
      refine ⟨e.inverse.preimage θ, ⟨?_, ?_⟩, ?_⟩
      · apply e.inverse.map_injective
        rw [e.inverse.map_comp, e.inverse.map_preimage, h1]
      · apply e.inverse.map_injective
        rw [e.inverse.map_comp, e.inverse.map_preimage, h2]
      · rintro k ⟨k1, k2⟩
        apply e.inverse.map_injective
        rw [e.inverse.map_preimage]
        refine huniq _ ⟨?_, ?_⟩
        · rw [← e.inverse.map_comp, k1]
        · rw [← e.inverse.map_comp, k2])
    (by
      have := S.e_isStableUnderRetracts
      infer_instance)
    (by
      have := S.m_isStableUnderRetracts
      infer_instance)

/-- The left class of `S.transport e` is the inverse image of `S.E` along `e.inverse`. -/
@[simp]
lemma transport_E {X Y : B} (f : X ⟶ Y) : (S.transport e).E f ↔ S.E (e.inverse.map f) := Iff.rfl

/-- The right class of `S.transport e` is the inverse image of `S.M` along `e.inverse`. -/
@[simp]
lemma transport_M {X Y : B} (f : X ⟶ Y) : (S.transport e).M f ↔ S.M (e.inverse.map f) := Iff.rfl

end OFS

/-- Regularity is invariant under equivalences of categories. -/
theorem IsRegularCat.of_equivalence (h : IsRegularCat A) (e : A ≌ B) : IsRegularCat B := by
  have := h.hasFiniteLimits
  have : HasFiniteLimits B := ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  obtain ⟨S, hS⟩ := h.exists_ofs
  have hSE := S.e_eq_extremalEpi hS
  refine isRegularCat_of_faithful e.inverse h (S.transport e) ?_ ?_
  · intro X Y f
    rw [OFS.transport_M, hS, MorphismProperty.monomorphisms.iff]
  · intro X Y f
    rw [OFS.transport_E, hSE]

/-- Exactness is invariant under equivalences of categories. -/
theorem IsExactCat.of_equivalence (h : IsExactCat A) (e : A ≌ B) : IsExactCat B := by
  have := h.regular.hasFiniteLimits
  have : HasFiniteLimits B := ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  refine ⟨h.regular.of_equivalence e, ?_⟩
  intro R c r s hrs
  have hbase : IsEquivRel (e.inverse.map r) (e.inverse.map s) := hrs.map e.inverse
  obtain ⟨d, f, hk, ⟨hcolim⟩⟩ := h.effective _ _ hbase
  refine ⟨e.functor.obj d, (e.counitIso.app c).inv ≫ e.functor.map f, ?_, ?_⟩
  · -- the transported morphism has the same kernel pair
    refine isKernelPair_of_map e.inverse ?_ ?_
    · rw [← Category.assoc, ← Category.assoc]
      have h1 : r ≫ (e.counitIso.app c).inv = (e.counitIso.app _).inv ≫
          e.functor.map (e.inverse.map r) := by simp
      have h2 : s ≫ (e.counitIso.app c).inv = (e.counitIso.app _).inv ≫
          e.functor.map (e.inverse.map s) := by simp
      rw [h1, h2, Category.assoc, Category.assoc, ← e.functor.map_comp, ← e.functor.map_comp, hk.w]
    · have hmap : e.inverse.map ((e.counitIso.app c).inv ≫ e.functor.map f)
          = f ≫ e.unit.app d := by
        simp
      rw [hmap]
      exact hk.comp_of_mono
  · refine ⟨isColimitOfReflects e.inverse ((isColimitMapCoconeCoforkEquiv e.inverse _).symm ?_)⟩
    exact IsColimit.ofIsoColimit hcolim (Cofork.ext (e.unitIso.app d) (by simp))

end UlmerBialgebras
