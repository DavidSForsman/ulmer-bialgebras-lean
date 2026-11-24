module

public import UlmerBialgebras.Proofs.Sec5.LeftExtColim
public import UlmerBialgebras.Proofs.Sec4.ExtensionCategories

/-!
# Lemma 5.6: extensions into `Ins(f, id)` as algebras of the pushout endofunctor

Let `N` be an inserter of `f : c ⟶ c` and `𝟙 c`, let `X ←k— I —d→ N.pt` be a span, and let
`e₁ = (l₁, η₁)` and `e₂ = (l₂, η₂)` be initial extensions of `A = u d` and of `f A` along `k`.
For `H = LeftExt.pushoutStep k (φ d) e₁ e₂`, the composite

  `LE(d, k) ≅ Ins(f_*, id_*) ≅ Ins(f_*, α^*) ≅ Alg(H)`

is an isomorphism of categories over `LE(A, k)`
(`UlmerBialgebras.Paper.AbsKan.exists_leftExt_iso_algebra_pushoutStep`):

* the first factor is Lemma 4.6 (2), `Inserter.leftExtToIns`;
* the second replaces `id_* = Inserter.twistedPush` by the isomorphic `α^* = LeftExt.pull k (φ d)`
  (`Internal.twistedPushIsoPull`, `Internal.insCongrRight`);
* the third transposes the structure maps along the relative adjunction `H ⊣_{f_*} α^*`
  (`AbsKan.stepRel`, `Internal.insToAlgebra`).

As a relative left adjoint, `H` preserves the colimits that `f_*` preserves, among them the
connected colimits that exist in `K(X, c)` and are preserved by `K(X, f)`.

## Main results

* `UlmerBialgebras.Paper.AbsKan.exists_leftExt_iso_algebra_pushoutStep`: Lemma 5.6, a functor
  `LE(d, k) ⥤ Alg(H)` that is bijective on objects, full and faithful and lies over `LE(u d, k)`,
  and `H` preserves the connected colimits whose underlying colimits exist and are preserved by
  `postcomp X f`.
* `UlmerBialgebras.Paper.AbsKan.Internal.insToAlgebra`: for an `F`-relative left adjoint `L` of `G`,
  the functor `Ins F G ⥤ Alg(L)` transposing the structure maps.
* `UlmerBialgebras.Paper.AbsKan.Internal.twistedPushIsoPull`: an isomorphism `id_* ≅ α^*`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.6 (2) and Lemma 5.6
* [G. M. Kelly, *A unified treatment of transfinite constructions for free algebras, free
  monoids, colimits, associated sheaves, and so on*][kellyUnifiedTreatmentTransfinite1980]
-/

@[expose] public section

universe u v w u' v'

open scoped CategoryTheory.Bicategory

namespace UlmerBialgebras.Paper.AbsKan

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Internal

section Generic

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G G' : C ⥤ D}

/-- A natural isomorphism `θ : G ≅ G'` induces an isomorphism of categories
`Ins(F, G) ≅ Ins(F, G')` over `C`, `(x, a) ↦ (x, θ_x • a)`. -/
@[simps, reducible]
def insCongrRight (θ : G ≅ G') : Ins F G ⥤ Ins F G' where
  obj x := ⟨x.pt, x.cell ≫ θ.hom.app x.pt⟩
  map {x y} g := ⟨g.base, by
    rw [Category.assoc, ← θ.hom.naturality, ← Category.assoc, g.w, Category.assoc]⟩

/-- `insCongrRight θ : Ins(F, G) ⥤ Ins(F, G')` is bijective on objects, with inverse
`(x, a) ↦ (x, θ⁻¹_x • a)`. -/
lemma insCongrRight_obj_bijective (θ : G ≅ G') :
    Function.Bijective (insCongrRight (F := F) θ).obj :=
  Function.bijective_iff_has_inverse.mpr ⟨fun y => ⟨y.pt, y.cell ≫ θ.inv.app y.pt⟩,
    fun x => by simp, fun ⟨p, a⟩ => by
      simp⟩

/-- `insCongrRight θ : Ins(F, G) ⥤ Ins(F, G')` is faithful. -/
instance (θ : G ≅ G') : (insCongrRight (F := F) θ).Faithful where
  map_injective h := Ins.hom_ext (congr(Ins.Hom.base $(h)) :)

/-- `insCongrRight θ : Ins(F, G) ⥤ Ins(F, G')` is full. -/
instance (θ : G ≅ G') : (insCongrRight (F := F) θ).Full where
  map_surjective {x y} g := ⟨⟨g.base, by
    have hw : (x.cell ≫ θ.hom.app x.pt) ≫ G'.map g.base =
        F.map g.base ≫ y.cell ≫ θ.hom.app y.pt := g.w
    rw [← cancel_mono (θ.hom.app y.pt), Category.assoc, θ.hom.naturality, ← Category.assoc, hw,
      Category.assoc]⟩, rfl⟩

variable {L : C ⥤ C} (ra : RelLeftAdjoint F G L)

/-- Transposing the structure maps along an `F`-relative left adjoint `L` of `G`: the
isomorphism of categories `Ins(F, G) ≅ Alg(L)` over `C`. -/
@[simps, reducible]
def insToAlgebra : Ins F G ⥤ Endofunctor.Algebra L where
  obj x := ⟨x.pt, (ra.homEquiv x.pt x.pt).symm x.cell⟩
  map {x y} g := ⟨g.base, by
    rw [← ra.homEquiv_symm_naturality_left, ← ra.homEquiv_symm_naturality_right, g.w]⟩

/-- `insToAlgebra : Ins(F, G) ⥤ Alg(L)` is bijective on objects; the inverse transposes back
along the relative adjunction. -/
lemma insToAlgebra_obj_bijective : Function.Bijective (insToAlgebra ra).obj :=
  Function.bijective_iff_has_inverse.mpr ⟨fun A => ⟨A.a, ra.homEquiv A.a A.a A.str⟩,
    fun x => by simp, fun ⟨a, s⟩ => by
      simp⟩

/-- `insToAlgebra : Ins(F, G) ⥤ Alg(L)` is faithful. -/
instance : (insToAlgebra ra).Faithful where
  map_injective h := Ins.hom_ext (congr(Endofunctor.Algebra.Hom.f $(h)))

/-- `insToAlgebra : Ins(F, G) ⥤ Alg(L)` is full. -/
instance : (insToAlgebra ra).Full where
  map_surjective {_ _} g := ⟨⟨g.f, ra.isHom_of_cellT g.f g.h.symm⟩, rfl⟩

end Generic

section TwistedPush

variable {c : Obj} {f : c ⟶ c} (N : Inserter f (𝟙 c)) {I X : Obj} (k : I ⟶ X)
  (d : I ⟶ N.pt)

/-- `id_* ≅ α^*`: the functor `id_*` of Lemma 4.6 (2) for the inserter of `f` and `𝟙 c` is
isomorphic to pulling back along `φ d`, by the identities `l ≫ 𝟙 c = l`. -/
def twistedPushIsoPull : N.twistedPush k d ≅ LeftExt.pull k (N.phiAtId d) :=
  NatIso.ofComponents (fun x => eqToIso (LeftExt.eq_of_ext_eq (Category.comp_id x.ext) (by
      -- the inserter cell `strCell N d` is `N.phiAt d` by definition
      change (N.phiAt d ≫ (x.unit ▷ 𝟙 c) ≫ eqToHom (Category.assoc k x.ext (𝟙 c))) ≫
          eqToHom (k ≫= Category.comp_id x.ext) =
        (N.phiAt d ≫ eqToHom (Category.comp_id _)) ≫ x.unit
      rw [Bicategory.Strict.whiskerRight_id]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])))
    (fun g => LeftExt.hom_ext (by
      simp only [LeftExt.comp_val, eqToIso.hom, LeftExt.homCell_eqToHom]
      change (LeftExt.homCell g ▷ 𝟙 c) ≫ eqToHom (Category.comp_id _) =
        eqToHom (Category.comp_id _) ≫ LeftExt.homCell g
      rw [Bicategory.Strict.whiskerRight_id]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]))

end TwistedPush

end Internal

open Internal

/-- **Lemma 5.6** ([forsman2026syntactic]), the isomorphism `LE(d, k) ≅ Alg(H)` over `LE(u d, k)`
and the preservation of connected colimits by `H`. -/
theorem exists_leftExt_iso_algebra_pushoutStep {c : Obj} (f : c ⟶ c) (Ins : Inserter f (𝟙 c))
    {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) [HasPushouts (X ⟶ c)]
    (e₁ : LeftExt k (d ≫ Ins.u)) (he₁ : IsInitial e₁)
    (e₂ : LeftExt k ((d ≫ Ins.u) ≫ f)) (he₂ : IsInitial e₂) :
    (∃ F : LeftExt k d ⥤ Endofunctor.Algebra (LeftExt.pushoutStep k (Ins.phiAtId d) e₁ he₂),
      Function.Bijective F.obj ∧ F.Full ∧ F.Faithful ∧
        F ⋙ Endofunctor.Algebra.forget _ = LeftExt.push k d Ins.u) ∧
    ∀ {J : Type u'} [Category.{v'} J] [IsConnected J] (W : J ⥤ LeftExt k (d ≫ Ins.u)),
      HasColimit (W ⋙ LeftExt.forget k (d ≫ Ins.u)) →
        PreservesColimit (W ⋙ LeftExt.forget k (d ≫ Ins.u)) (postcomp X f) →
          PreservesColimit W (LeftExt.pushoutStep k (Ins.phiAtId d) e₁ he₂) := by
  let ra := stepRel k (Ins.phiAtId d) e₁ he₁ he₂
  refine ⟨⟨Inserter.leftExtToIns Ins k d ⋙ insCongrRight (twistedPushIsoPull Ins k d) ⋙
    insToAlgebra ra, (insToAlgebra_obj_bijective ra).comp ((insCongrRight_obj_bijective _).comp
      (Inserter.leftExtToIns_obj_bijective Ins k d)), inferInstance, inferInstance, rfl⟩, ?_⟩
  intro J _ _ W hW hf
  have := push_preservesColimit k W f
  exact ra.preservesColimit W

end UlmerBialgebras.Paper.AbsKan
