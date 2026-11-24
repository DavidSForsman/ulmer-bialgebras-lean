module

public import UlmerBialgebras.Appendix.VCatHomDenseFunctor
public import UlmerBialgebras.Appendix.VCatCellDense

/-!
# The reconstructed `V`-functor induces the family

`VCatHomDenseFunctor.lean` builds, out of a pseudonatural family `Φ` of functors on the
representables of the small `V`-categories, a `V`-functor `UlmerBialgebras.AHomFamily.toVFunctor Φ`.
This file compares post-composition with it to the family itself.

* `UlmerBialgebras.AHomFamily.vProbeFactor k : x ⟶ vProbe k.obj` — the factorisation of a 1-cell
  through the probe on the family of its values, with
  `UlmerBialgebras.AHomFamily.vProbeFactor_comp_incl`;
* `UlmerBialgebras.AHomFamily.probeFactorIso` — the comparison isomorphisms of the probe assemble
  into an isomorphism `k ≫ toVFunctor Φ ≅ vProbeFactor k ≫ probeVal Φ k.obj` of `V`-functors;
* `UlmerBialgebras.AHomFamily.homIso Φ hx k : k ≫ toVFunctor Φ ≅ (Φ.fn hx).obj k` — composing it
  with the pseudonaturality isomorphism along `vProbeFactor k`;
* `UlmerBialgebras.AHomFamily.homIso_nat` — `homIso` is compatible with the pseudonaturality
  isomorphisms of the family;
* `UlmerBialgebras.AHomFamily.homIso_naturality` — `homIso` is natural in `k`.

The last two are what make `homIso` a *representation* of the family in the sense of
`ADense.lean`; naturality in `k` is where the free `V`-categories on an arrow are used, and
hence where an absorbing initial object of `V` is assumed (`VCatHomDenseUnit.lean`).

## Main results

* `UlmerBialgebras.AHomFamily.vProbeFactor`: the factorisation `x ⟶ vProbe k.obj` of a 1-cell `k`
  through the probe on the family of its values.
* `UlmerBialgebras.AHomFamily.probeFactorIso`: the isomorphism
  `k ≫ toVFunctor Φ ≅ vProbeFactor k ≫ probeVal Φ k.obj` of `V`-functors.
* `UlmerBialgebras.AHomFamily.homIso`: the isomorphism `k ≫ toVFunctor Φ ≅ (Φ.fn hx).obj k`.

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
variable {D C : VCat.{w, v, max u w} V}

namespace AHomFamily

variable {P : VCat.{w, v, max u w} V → Prop}
variable (Φ : AHomFamily P D C)

/-! ## Factoring a 1-cell through the probe on its values -/

/-- The factorisation of a 1-cell `k : X ⟶ D` through the probe on the family of its
values: it is the identity on objects and `k` on hom-objects. -/
def vProbeFactor {X : VCat.{w, v, max u w} V} (k : X ⟶ D) : X ⟶ vProbe (k.obj) where
  toFunctor :=
    { obj := fun a => a
      map := fun {_ _} f => k.map f
      map_id := fun a => k.toFunctor.map_id a
      map_comp := fun f g => k.toFunctor.map_comp f g }
  emap a b := k.emap a b
  emap_comp a b c := k.emap_comp a b c
  emap_hom f := k.emap_hom f

/-- The factorisation `vProbeFactor k` is the identity on objects. -/
@[simp] lemma vProbeFactor_obj {X : VCat.{w, v, max u w} V} (k : X ⟶ D) (a : X.carrier) :
    (vProbeFactor k).obj a = vProbeObj _ a := rfl

/-- The factorisation `vProbeFactor k` acts on hom-objects by `k`. -/
@[simp] lemma vProbeFactor_emap {X : VCat.{w, v, max u w} V} (k : X ⟶ D) (a b : X.carrier) :
    (vProbeFactor k).emap a b = k.emap a b := rfl

/-- The factorisation composed with the inclusion of the probe is the original 1-cell. -/
lemma vProbeFactor_comp_incl {X : VCat.{w, v, max u w} V} (k : X ⟶ D) :
    vProbeFactor k ≫ vProbeIncl (k.obj) = k := by
  refine VFunctor.ext' ?_ ?_
  · exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      ((Category.id_comp _).trans (Category.comp_id _)).symm)
  · intro a b
    exact (Category.comp_id _).trans (Category.comp_id _)

/-! ## The comparison isomorphism -/

section

variable {x : VCat.{w, v, max u w} V} [hx : IsVProbeIndex.{w, v, u} P x.carrier]

/-- The pseudonaturality isomorphism along the factorisation of `k`. -/
noncomputable def natFactorIso (k : x ⟶ D) :
    (Φ.fn (IsVProbeIndex.mem_self P x)).obj k ≅ vProbeFactor k ≫ probeVal Φ (k.obj) :=
  eqToIso (congrArg (fun m : x ⟶ D => (Φ.fn (IsVProbeIndex.mem_self P x)).obj m)
      (vProbeFactor_comp_incl k).symm) ≪≫
    (Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem (k.obj))
      (vProbeFactor k)).app (vProbeIncl (k.obj))

/-- The components of `natFactorIso Φ k`: a transport along `vProbeFactor_comp_incl`, then the
component of the pseudonaturality isomorphism along the factorisation of `k`. -/
lemma natFactorIso_hom_app (k : x ⟶ D) (a : x.carrier) :
    (natFactorIso Φ k).hom.app a =
      eqToHom congr(((Φ.fn (IsVProbeIndex.mem_self P x)).obj
        $((vProbeFactor_comp_incl k).symm)).obj a) ≫
      ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem (k.obj))
        (vProbeFactor k)).hom.app (vProbeIncl (k.obj))).app a :=
  VNatTrans.eqToHom_app congr((Φ.fn (IsVProbeIndex.mem_self P x)).obj
    $((vProbeFactor_comp_incl k).symm)) a =≫ _

variable [VProbeSystem.{w, v, u} P]

/-- The comparison isomorphisms at the indices of the probe on the values of `k` assemble
into an isomorphism of `V`-functors. -/
def probeFactorCell (k : x ⟶ D) :
    (k ≫ toVFunctor Φ : x ⟶ C) ⟶ vProbeFactor k ≫ probeVal Φ (k.obj) where
  app a := (probeIso Φ (k.obj) a).hom
  vnaturality a a' := by
    -- `gEmap` is read off any probe (`probeEmap_eq`), here the one on the values of `k`, where
    -- it is `probeVal` conjugated by the comparison isomorphisms.
    simp only [vCat_comp₁_eq, VFunctor.comp_emap, VFunctor.comp_obj, vProbeFactor_emap,
      vProbeFactor_obj, toVFunctor_emap, toVFunctor_obj, ← probeEmap_eq, probeEmap, eHomConj₂]
    -- What is left is `inv ≫ hom = 𝟙` on the target, after reassociation.
    have hc : eHomWhiskerLeft V (objMap Φ (k.obj a)) (probeIso Φ (k.obj) a').inv ≫
        eHomWhiskerLeft V (objMap Φ (k.obj a)) (probeIso Φ (k.obj) a').hom = 𝟙 _ := by
      rw [← eHomWhiskerLeft_comp, Iso.inv_hom_id, eHomWhiskerLeft_id]
    exact (Category.assoc _ _ _).trans (_ ≫= ((Category.assoc _ _ _).trans
      (_ ≫= ((Category.assoc _ _ _).trans ((_ ≫= hc).trans (Category.comp_id _)))))) |>.trans
        (Category.assoc _ _ _).symm

/-- The comparison 2-cell `probeFactorCell Φ k` is invertible, since all its components are. -/
instance (k : x ⟶ D) : IsIso (probeFactorCell Φ k) :=
  VNatTrans.isIso_of_app _ (fun a => (probeIso Φ (k.obj) a).isIso_hom)

/-- The comparison isomorphisms at the indices of the probe on the values of `k` assemble
into an isomorphism of `V`-functors. -/
noncomputable def probeFactorIso (k : x ⟶ D) :
    k ≫ toVFunctor Φ ≅ vProbeFactor k ≫ probeVal Φ (k.obj) :=
  asIso (probeFactorCell Φ k)

/-- **Post-composing with the reconstructed `V`-functor computes the family**, at each
1-cell out of a small `V`-category. -/
noncomputable def homIso (k : x ⟶ D) :
    k ≫ toVFunctor Φ ≅ (Φ.fn (IsVProbeIndex.mem_self P x)).obj k :=
  probeFactorIso Φ k ≪≫ (natFactorIso Φ k).symm

end

/-! ## The unit probe -/

/-- The 1-cell of `CAT_V` out of the unit `V`-category attached to an object. -/
def unitPt {X : VCat.{w, v, max u w} V} (a : X.carrier) : unitVCat.{w, v, max u w} V ⟶ X :=
  UnitVCat.const a

/-- The point `unitPt a` sends the unique object to `a`. -/
@[simp] lemma unitPt_obj {X : VCat.{w, v, max u w} V} (a : X.carrier)
    (Y : (unitVCat.{w, v, max u w} V).carrier) : (unitPt a).obj Y = a := rfl

/-- Pre-composing the point `a` with a 1-cell `k` is the point `k a`. -/
lemma unitPt_comp₁ {X Y : VCat.{w, v, max u w} V} (a : X.carrier) (k : X ⟶ Y) :
    unitPt a ≫ k = unitPt (k.obj a) :=
  const_comp₁ a k

/-- The 2-cell of `CAT_V` out of the unit `V`-category attached to a morphism. -/
def unitCell {X : VCat.{w, v, max u w} V} {a b : X.carrier} (f : a ⟶ b) :
    unitPt a ⟶ unitPt (X := X) b where
  app _ := f
  vnaturality _ _ := eId_eHomWhiskerLeft f

/-- The component of the 2-cell `unitCell f` at the unique object is `f`. -/
@[simp] lemma unitCell_app {X : VCat.{w, v, max u w} V} {a b : X.carrier} (f : a ⟶ b)
    (Y : (unitVCat.{w, v, max u w} V).carrier) : (unitCell (X := X) f).app Y = f := rfl

end AHomFamily

end UlmerBialgebras
