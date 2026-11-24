module

public import UlmerBialgebras.Density.ADense
public import UlmerBialgebras.Appendix.VCatArrow
public import UlmerBialgebras.Appendix.VCatUnit
public import UlmerBialgebras.Appendix.RepVAcc

/-!
# Small `V`-categories are locally dense in `CAT_V`

`ADense.lean` isolates the adequacy condition needed for the `A`-accessible adjoint functor
theorem: the class `A` must be **dense** in the ambient 2-category.  This file verifies the
local half of that condition — `UlmerBialgebras.IsACellDense` — in the motivating example, `CAT_V`
with `A` the small `V`-categories:

* `UlmerBialgebras.isACellDense_isSmallVCat` — a compatible family of 2-cells on the representables
  `CAT_V(a, -)`, `a` small, is induced by a unique `V`-natural transformation.

Only two small probes are used:

* the **unit** `V`-category `1`, whose `V`-functors into `C` are the objects of `C`
  (`VCatUnit.lean`): the family at `1` gives the components of the `V`-natural
  transformation, and compatibility with pre-composition shows that *every* component of the
  family is determined by them;
* the **free `V`-category on an arrow** `2_x` (`VCatArrow.lean`) for `x = (c ⟶[V] c')`,
  applied to the generic arrow `𝟙 (c ⟶[V] c')`: the single `V`-naturality square of the
  family at that probe is exactly the `V`-naturality square of the components.

The only standing assumption on the base is that `V` has an absorbing initial object
(`UlmerBialgebras.MonoidalInitial`), which is what makes the arrow probe exist; this holds for any
braided monoidal closed `V` with an initial object, in particular for any complete and
cocomplete symmetric monoidal closed `V`.

## Main results

* `UlmerBialgebras.isACellDense_of_probes`: for `V` with an absorbing initial object, every class of
  `V`-categories containing the unit `V`-category and all arrow `V`-categories `2_x` satisfies
  `UlmerBialgebras.IsACellDense`.
* `UlmerBialgebras.isACellDense_isSmallVCat`: the small `V`-categories satisfy
  `UlmerBialgebras.IsACellDense` in `CAT_V`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-! ## The two probes are small -/

/-- The unit `V`-category is a small `V`-category. -/
lemma isSmallVCat_unitVCat : IsSmallVCat.{w, v, u} V (unitVCat.{w, v, max u w} V) :=
  inferInstanceAs (Small.{w} _)

/-- The free `V`-category on an arrow is a small `V`-category. -/
lemma isSmallVCat_arrowVCat (Z : MonoidalInitial V) (x : V) :
    IsSmallVCat.{w, v, u} V (arrowVCat.{w, v, max u w} Z x) :=
  inferInstanceAs (Small.{w} _)

/-! ## Pre-composing the object probe -/

/-- Pre-composing the `V`-functor picking out an object `a` of `X` with a `V`-functor
`k : X ⟶ C` picks out the object `k a` of `C`. -/
lemma const_comp₁ {X C : VCat.{w, v, u} V} (a : X.carrier) (k : X ⟶ C) :
    ((UnitVCat.const a : unitVCat.{w, v, u} V ⟶ X) ≫ k : unitVCat.{w, v, u} V ⟶ C)
      = UnitVCat.const (k.obj a) := by
  refine VFunctor.ext' ?_ ?_
  · refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ t => ?_)
    -- the two transports are along `rfl` equations of objects
    refine Eq.trans ?_ ((whisker_eq _ ((whisker_eq _ (eqToHom_refl _ _)).trans
      (Category.comp_id _))).trans ((eq_whisker (eqToHom_refl _ _) _).trans
        (Category.id_comp _))).symm
    apply (eHomEquiv V).injective
    refine (k.emap_hom ((UnitVCat.const a).toFunctor.map t)).symm.trans ?_
    -- `(UnitVCat.const a).map t` is `(eHomEquiv V).symm (toEnd t ≫ eId V a)`
    exact (eq_whisker (Equiv.apply_symm_apply _ _) _).trans ((Category.assoc _ _ _).trans
      ((whisker_eq _ (k.emap_id a)).trans (Equiv.apply_symm_apply _ _).symm))
  · intro _ _
    simp only [vCat_comp₁_eq, VFunctor.comp_emap, UnitVCat.const_emap]
    exact (whisker_eq _ (eqToHom_refl _ _)).trans ((Category.comp_id _).trans (k.emap_id a))

/-! ## Local density -/

/-- **Two probes suffice for local density.**  A class `A` of `V`-categories containing the
unit `V`-category and the free `V`-category on an arrow `x`, for every object `x` of `V`, is
locally dense in `CAT_V`: a compatible family of 2-cells on the representables `CAT_V(a, -)`,
`a ∈ A`, comes from a unique `V`-natural transformation.

This is the sharp form of `isACellDense_isSmallVCat`: for local density, it replaces the class
of *all* small `V`-categories by a `w`-small family of probes. `VCatEssSmall.lean` records that the
essential-smallness statements built on this are not formalized. -/
theorem isACellDense_of_probes (Z : MonoidalInitial V)
    (A : VCat.{w, v, u} V → Prop) (h1 : A (unitVCat.{w, v, u} V))
    (harr : ∀ x : V, A (arrowVCat.{w, v, u} Z x)) :
    IsACellDense (Obj := VCat.{w, v, u} V) A := by
  intro C D p q Φ
  -- the candidate components, read off the unit probe
  let cpt : ∀ c : C.carrier, p.obj c ⟶ q.obj c := fun c =>
    ((Φ.app h1).app (UnitVCat.const c)).app (UnitVCat.star V)
  -- every component of the family is one of these
  have key : ∀ (X : VCat.{w, v, u} V) (hX : A X) (k : X ⟶ C)
      (a : X.carrier), ((Φ.app hX).app k).app a = cpt (k.obj a) := by
    intro X hX k a
    have hnat := Φ.naturality h1 hX (UnitVCat.const a) k
    have h := congr(VNatTrans.app $hnat (UnitVCat.star V))
    simp only [vCat_whiskerLeft_app, vCat_vcomp_app, VNatTrans.eqToHom_app,
      UnitVCat.const_obj] at h
    have h2 : HEq (((Φ.app h1).app ((UnitVCat.const a : unitVCat.{w, v, u} V ⟶ X) ≫ k)).app
          (UnitVCat.star V))
        (((Φ.app h1).app (UnitVCat.const (k.obj a) :
            unitVCat.{w, v, u} V ⟶ C)).app (UnitVCat.star V)) := by
      rw [const_comp₁ a k]
    rw [h, eq_of_heq h2]
    -- the two transports are along `rfl` equations of objects
    exact (whisker_eq _ ((whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _))).trans
      ((eq_whisker (eqToHom_refl _ _) _).trans (Category.id_comp _))
  -- the `V`-natural transformation
  refine ⟨{ app := cpt, vnaturality := ?_ }, ?_, ?_⟩
  · intro c c'
    have hA := harr (c ⟶[V] c')
    have hsq := ((Φ.app hA).app
      (arrowVFunctor Z (c ⟶[V] c') c c' (𝟙 _))).vnaturality (ArrowObj.src) (ArrowObj.tgt)
    -- transport `hsq` along `key` at the two vertices of the arrow
    have hsq' : (𝟙 (c ⟶[V] c') ≫ p.emap c c') ≫ eHomWhiskerLeft V (VFunctor.obj p c) (cpt c') =
        (𝟙 (c ⟶[V] c') ≫ q.emap c c') ≫ eHomWhiskerRight V (cpt c) (VFunctor.obj q c') :=
      (congrArg₂ (fun (x : p.obj c ⟶ q.obj c) (y : p.obj c' ⟶ q.obj c') =>
          (𝟙 (c ⟶[V] c') ≫ p.emap c c') ≫ eHomWhiskerLeft V (VFunctor.obj p c) y =
            (𝟙 (c ⟶[V] c') ≫ q.emap c c') ≫ eHomWhiskerRight V x (VFunctor.obj q c'))
        (key _ hA _ ArrowObj.src) (key _ hA _ ArrowObj.tgt)).mp hsq
    rw [Category.id_comp, Category.id_comp] at hsq'
    exact hsq'
  · intro X hX
    refine NatTrans.ext (funext fun k => VNatTrans.ext (funext fun a => ?_))
    exact (key X hX k a).symm
  · intro β hβ
    refine VNatTrans.ext (funext fun c => ?_)
    exact congr(VNatTrans.app $(NatTrans.congr_app (hβ h1) (UnitVCat.const c)) (UnitVCat.star V))

/-- **Small `V`-categories are locally dense in `CAT_V`**: a compatible family of 2-cells on
the representables `CAT_V(a, -)`, `a` a small `V`-category, comes from a unique `V`-natural
transformation. -/
theorem isACellDense_isSmallVCat (Z : MonoidalInitial V) :
    IsACellDense (Obj := VCat.{w, v, max u w} V) (IsSmallVCat.{w, v, u} V) :=
  isACellDense_of_probes Z _ isSmallVCat_unitVCat
    (fun x => isSmallVCat_arrowVCat.{w, v, u} Z x)

end UlmerBialgebras
