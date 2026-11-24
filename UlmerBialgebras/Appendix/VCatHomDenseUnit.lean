module

public import UlmerBialgebras.Appendix.VCatHomDenseNatIso

/-!
# Naturality of the comparison isomorphism at the unit probe

The comparison isomorphism `UlmerBialgebras.AHomFamily.homIso` of `VCatHomDenseIso.lean` has to be
natural in the 1-cell `k`.  Since a pseudonatural family carries no axiom relating its action
on 2-cells at different probes, that action has to be *computed*, and everything reduces to
the unit probe, where a 1-cell is a point of `D` and a 2-cell a morphism of `D`:

* `UlmerBialgebras.unitVFunctor_eq_const` — a `V`-functor out of the unit `V`-category is the point
  at its value;
* `UlmerBialgebras.AHomFamily.UnitNat Φ δ` — the naturality statement for a 2-cell `δ` out of the
  unit `V`-category, with `UlmerBialgebras.AHomFamily.unitNat_eqToHom` and
  `UlmerBialgebras.AHomFamily.unitNat_congr`;
* `UlmerBialgebras.AHomFamily.homIso_component_iff` — naturality of `homIso` at a 2-cell of an
  arbitrary small probe, componentwise at an object `a`, *is* `UnitNat` for the 2-cell
  restricted along the point `a`;
* `UlmerBialgebras.AHomFamily.homIso_naturality_const` — `UnitNat` holds for the 2-cell `unitCell f`
  attached to a morphism `f : d ⟶ d'` of `D`.

The last statement is the one with mathematical content, and the free `V`-category on an
arrow is what proves it; this is where an absorbing initial object
`UlmerBialgebras.MonoidalInitial V` of the base is assumed.

## Main results

* `UlmerBialgebras.unitVFunctor_eq_const`: a `V`-functor out of the unit `V`-category is the point
  at its value.
* `UlmerBialgebras.AHomFamily.homIso_component_iff`: naturality of `homIso` at a 2-cell, at an
  object `a`, is equivalent to `UnitNat` for the 2-cell restricted along the point `a`.
* `UlmerBialgebras.AHomFamily.homIso_naturality_const`: for `V` with an absorbing initial object,
  `UnitNat` holds for the 2-cell `unitCell f` attached to a morphism `f : d ⟶ d'` of `D`.
* `UlmerBialgebras.AHomFamily.homIso_naturality_unit`: under the same hypotheses, `UnitNat` holds
  for every 2-cell out of the unit `V`-category.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **A `V`-functor out of the unit `V`-category is the point at its value.** -/
lemma unitVFunctor_eq_const {C : Type u} [Category.{w} C] [EnrichedOrdinaryCategory V C]
    (F : VFunctor V (UnitVCat.{w, v, u} V) C) :
    F = UnitVCat.const (F.obj (UnitVCat.star V)) := by
  have hobj : F.toFunctor = (UnitVCat.const (F.obj (UnitVCat.star V))).toFunctor := by
    refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y t => ?_)
    · obtain rfl : X = UnitVCat.star V := rfl
      rfl
    · obtain rfl : X = UnitVCat.star V := rfl
      obtain rfl : Y = UnitVCat.star V := rfl
      apply (eHomEquiv V).injective
      rw [← F.emap_hom t, UnitVCat.vFunctor_emap F _ _]
      simp [UnitVCat.const]
  refine VFunctor.extHEq hobj (fun X Y => ?_)
  obtain rfl : X = UnitVCat.star V := rfl
  obtain rfl : Y = UnitVCat.star V := rfl
  rw [UnitVCat.vFunctor_emap F _ _]
  dsimp [UnitVCat.const]
  rfl

variable {D C : VCat.{w, v, max u w} V}

namespace AHomFamily
/-- The identity morphism gives the identity 2-cell out of the unit `V`-category. -/
@[simp] lemma unitCell_id {X : VCat.{w, v, max u w} V} (a : X.carrier) :
    unitCell (X := X) (𝟙 a) = 𝟙 (unitPt a) :=
  VNatTrans.ext (funext fun _ => rfl)


variable {P : VCat.{w, v, max u w} V → Prop} [VProbeSystem.{w, v, u} P]
variable (Φ : AHomFamily P D C)

/-! ## Naturality at the unit probe -/

/-- The naturality statement for the comparison isomorphism at a 2-cell out of the unit
`V`-category. -/
def UnitNat {m m' : unitVCat.{w, v, max u w} V ⟶ D} (δ : m ⟶ m') : Prop :=
  gMap Φ (δ.app (UnitVCat.star V)) ≫ (homIso Φ m').hom.app (UnitVCat.star V)
    = (homIso Φ m).hom.app (UnitVCat.star V)
      ≫ ((Φ.fn (VProbeSystem.unit (V := V) (P := P))).map δ).app (UnitVCat.star V)

/-- Naturality holds for the 2-cells coming from equalities of 1-cells. -/
lemma unitNat_eqToHom {m m' : unitVCat.{w, v, max u w} V ⟶ D} (h : m = m') :
    UnitNat Φ (eqToHom h) := by
  subst h
  simp only [UnitNat, unitVCat_carrier, eqToHom_refl, vCat_id₂_app, gMap_id, vCat_comp₁_eq,
    CategoryTheory.Functor.map_id, Category.comp_id]
  -- (the identity is at `objMap Φ (m.obj _)`, the source of `homIso` only up to unfolding)
  exact Category.id_comp _

/-- Naturality is invariant under transporting a 2-cell along equalities of its source and
target. -/
lemma unitNat_congr {m₁ m₁' m₂ m₂' : unitVCat.{w, v, max u w} V ⟶ D} (h : m₁ = m₂)
    (h' : m₁' = m₂') {δ : m₁ ⟶ m₁'} (hd : UnitNat Φ δ) :
    UnitNat Φ (eqToHom h.symm ≫ δ ≫ eqToHom h' : m₂ ⟶ m₂') := by
  subst h; subst h'
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hd

/-! ## Reduction of naturality to the unit probe -/

section

variable {x : VCat.{w, v, max u w} V} [hx : IsVProbeIndex.{w, v, u} P x.carrier]

/-- Restricting the comparison isomorphism along a point of `x`. -/
lemma homIso_unitPt (k : x ⟶ D) (a : x.carrier) :
    (homIso Φ (unitPt a ≫ k)).hom.app (UnitVCat.star V)
        ≫ ((Φ.nat (VProbeSystem.unit (V := V) (P := P))
            (IsVProbeIndex.mem_self P x) (unitPt a)).hom.app k).app (UnitVCat.star V)
      = (homIso Φ k).hom.app a := by
  have h := congr(VNatTrans.app $(homIso_nat Φ (unitPt a) k) (UnitVCat.star V))
  simp only [vCat_vcomp_app, vCat_whiskerLeft_app, VNatTrans.eqToHom_app] at h
  exact h.trans (Category.id_comp _)

/-- **Naturality of the comparison isomorphism at a 2-cell, componentwise, is naturality at
the unit probe** for the restriction of the 2-cell along the corresponding point. -/
lemma homIso_component_iff {k k' : x ⟶ D} (β : k ⟶ k') (a : x.carrier) :
    (gMap Φ (β.app a) ≫ (homIso Φ k').hom.app a
        = (homIso Φ k).hom.app a ≫ ((Φ.fn (IsVProbeIndex.mem_self P x)).map β).app a)
      ↔ UnitNat Φ (unitPt a ◁ β) := by
  have F4 := congr(VNatTrans.app $((Φ.nat (VProbeSystem.unit (V := V) (P := P))
      (IsVProbeIndex.mem_self P x) (unitPt a)).hom.naturality β) (UnitVCat.star V))
  simp only [Functor.comp_map, precomp_map, vCat_vcomp_app, vCat_whiskerLeft_app,
    unitPt_obj] at F4
  let N := ((Φ.nat (VProbeSystem.unit (V := V) (P := P))
      (IsVProbeIndex.mem_self P x) (unitPt a)).hom.app k').app (UnitVCat.star V)
  have : IsIso N :=
    (vNatIsoApp ((Φ.nat (VProbeSystem.unit (V := V) (P := P))
      (IsVProbeIndex.mem_self P x) (unitPt a)).app k') (UnitVCat.star V)).isIso_hom
  have h_lhs : (gMap Φ (β.app a) ≫ (homIso Φ (unitPt a ≫ k')).hom.app (UnitVCat.star V)) ≫ N
      = gMap Φ (β.app a) ≫ (homIso Φ k').hom.app a :=
    (Category.assoc _ _ _).trans (gMap Φ (β.app a) ≫= homIso_unitPt Φ k' a)
  have h_rhs : ((homIso Φ (unitPt a ≫ k)).hom.app (UnitVCat.star V) ≫
        ((Φ.fn (VProbeSystem.unit (V := V) (P := P))).map (unitPt a ◁ β)).app
          (UnitVCat.star V)) ≫ N
      = (homIso Φ k).hom.app a ≫ ((Φ.fn (IsVProbeIndex.mem_self P x)).map β).app a :=
    (Category.assoc _ _ _).trans
      ((homIso Φ (unitPt a ≫ k)).hom.app (UnitVCat.star V) ≫= F4 |>.trans
        ((Category.assoc _ _ _).symm.trans
          (homIso_unitPt Φ k a =≫ ((Φ.fn (IsVProbeIndex.mem_self P x)).map β).app a)))
  constructor
  · intro h
    simp only [UnitNat, vCat_whiskerLeft_app, unitPt_obj]
    refine (cancel_mono N).mp ?_
    exact h_lhs.trans (h.trans h_rhs.symm)
  · intro h
    simp only [UnitNat, vCat_whiskerLeft_app, unitPt_obj] at h
    exact h_lhs.symm.trans (h =≫ N |>.trans h_rhs)

end

/-! ## The arrow probe -/

/-- The square that makes `(𝟙 d, f)` a 2-cell from the arrow 1-cell named by `𝟙` to the one
named by `d ◁ f`. -/
private lemma arrow_sq (Z : MonoidalInitial V) {d d' : D.carrier} (f : d ⟶ d') :
    (arrowVFunctor Z (d ⟶[V] d) d d (𝟙 _)).emap .src .tgt ≫ eHomWhiskerLeft V d f
      = (arrowVFunctor Z (d ⟶[V] d) d d' (eHomWhiskerLeft V d f)).emap .src .tgt
        ≫ eHomWhiskerRight V (𝟙 d) d' := by
  change 𝟙 _ ≫ eHomWhiskerLeft V d f = eHomWhiskerLeft V d f ≫ eHomWhiskerRight V (𝟙 d) d'
  rw [eHomWhiskerRight_id, Category.id_comp, Category.comp_id]

/-- At the source of the generic arrow `arrowVCat`, the conjugated 2-cell `δ` has identity
component because `γ.app a0 = 𝟙 d`. -/
private lemma arrowVNatTrans_delta_src_id (Z : MonoidalInitial V)
    {d d' : D.carrier} (f : d ⟶ d')
    (hsm : IsVProbeIndex.{w, v, u} P (arrowVCat.{w, v, max u w} Z (d ⟶[V] d)).carrier) :
    let y : V := (d ⟶[V] d)
    let A : VCat.{w, v, max u w} V := arrowVCat.{w, v, max u w} Z y
    let m : A ⟶ D := arrowVFunctor Z y d d (𝟙 y)
    let m' : A ⟶ D := arrowVFunctor Z y d d' (eHomWhiskerLeft V d f)
    let γ : m ⟶ m' := arrowVNatTrans Z y (𝟙 d) f (arrow_sq Z f)
    let Θ := (Φ.fn (IsVProbeIndex.mem_self P A)).map γ
    let δ : (m ≫ toVFunctor Φ) ⟶ (m' ≫ toVFunctor Φ) := (homIso Φ m).hom ≫ Θ ≫ (homIso Φ m').inv
    δ.app (arrowSrc.{w, v, max u w} Z y) =
      𝟙 ((m ≫ toVFunctor Φ).obj (arrowSrc.{w, v, max u w} Z y)) := by
  intro y A m m' γ Θ δ
  set a0 := arrowSrc.{w, v, max u w} Z y
  have hsrc0 : gMap Φ (γ.app a0) ≫ (homIso Φ m').hom.app a0 =
      (homIso Φ m).hom.app a0 ≫ Θ.app a0 := by
    refine (homIso_component_iff Φ γ a0).mpr ?_
    have h : (unitPt a0 ≫ m : unitVCat.{w, v, max u w} V ⟶ D) = unitPt a0 ≫ m' :=
      (unitPt_comp₁ a0 m).trans (unitPt_comp₁ a0 m').symm
    have he : (unitPt a0 ◁ γ) = eqToHom h := by
      refine VNatTrans.ext (funext fun _ => ?_)
      rw [VNatTrans.eqToHom_app]
      rfl
    rw [he]; exact unitNat_eqToHom Φ h
  have hid : gMap Φ (γ.app a0) ≫ (homIso Φ m').hom.app a0 = (homIso Φ m').hom.app a0 := by
    rw [show gMap Φ (γ.app a0) = 𝟙 (objMap Φ d) from gMap_id Φ d]
    exact Category.id_comp _
  have hsrc1 : (homIso Φ m).hom.app a0 ≫ Θ.app a0 = (homIso Φ m').hom.app a0 :=
    hsrc0.symm.trans hid
  simp only [δ, vCat_vcomp_app]
  rw [← Category.assoc, hsrc1]
  exact (vNatIsoApp (homIso Φ m') a0).hom_inv_id

/-- At the target of the generic arrow `arrowVCat`, `V`-naturality of `δ` together with
`δ.app a0 = 𝟙` identifies `δ.app a1` with `gMap Φ f`. -/
private lemma arrowVNatTrans_delta_tgt_eq (Z : MonoidalInitial V)
    {d d' : D.carrier} (f : d ⟶ d')
    (hsm : IsVProbeIndex.{w, v, u} P (arrowVCat.{w, v, max u w} Z (d ⟶[V] d)).carrier)
    (hδsrc :
      let y : V := (d ⟶[V] d)
      let A : VCat.{w, v, max u w} V := arrowVCat.{w, v, max u w} Z y
      let m : A ⟶ D := arrowVFunctor Z y d d (𝟙 y)
      let m' : A ⟶ D := arrowVFunctor Z y d d' (eHomWhiskerLeft V d f)
      let γ : m ⟶ m' := arrowVNatTrans Z y (𝟙 d) f (arrow_sq Z f)
      let Θ := (Φ.fn (IsVProbeIndex.mem_self P A)).map γ
      let δ : (m ≫ toVFunctor Φ) ⟶ (m' ≫ toVFunctor Φ) := (homIso Φ m).hom ≫ Θ ≫ (homIso Φ m').inv
      δ.app (arrowSrc.{w, v, max u w} Z y) =
        𝟙 ((m ≫ toVFunctor Φ).obj (arrowSrc.{w, v, max u w} Z y))) :
    let y : V := (d ⟶[V] d)
    let A : VCat.{w, v, max u w} V := arrowVCat.{w, v, max u w} Z y
    let m : A ⟶ D := arrowVFunctor Z y d d (𝟙 y)
    let m' : A ⟶ D := arrowVFunctor Z y d d' (eHomWhiskerLeft V d f)
    let γ : m ⟶ m' := arrowVNatTrans Z y (𝟙 d) f (arrow_sq Z f)
    let Θ := (Φ.fn (IsVProbeIndex.mem_self P A)).map γ
    let δ : (m ≫ toVFunctor Φ) ⟶ (m' ≫ toVFunctor Φ) := (homIso Φ m).hom ≫ Θ ≫ (homIso Φ m').inv
    δ.app (arrowTgt.{w, v, max u w} Z y) = gMap Φ f := by
  intro y A m m' γ Θ δ
  set a0 := arrowSrc.{w, v, max u w} Z y
  set a1 := arrowTgt.{w, v, max u w} Z y
  have hnat := δ.vnaturality a0 a1
  have hWR : eHomWhiskerRight V (δ.app a0) ((m' ≫ toVFunctor Φ).obj a1) = 𝟙 _ := by
    rw [hδsrc]; exact eHomWhiskerRight_id (V := V) _ _
  replace hnat := hnat.trans ((_ ≫= hWR).trans (Category.comp_id _))
  have h1 : (m ≫ toVFunctor Φ).emap a0 a1 = gEmap Φ d d := Category.id_comp _
  have h2 : (m' ≫ toVFunctor Φ).emap a0 a1 = eHomWhiskerLeft V d f ≫ gEmap Φ d d' := rfl
  rw [h1, h2] at hnat
  let δ1 : objMap Φ d ⟶ objMap Φ d' := δ.app a1
  have hL : eHomEquiv V (𝟙 d) ≫ gEmap Φ d d ≫ eHomWhiskerLeft V (objMap Φ d) δ1 =
      eHomEquiv V δ1 := by
    rw [← Category.assoc, gEmap_hom, gMap_id, eHomEquiv_comp_eHomWhiskerLeft, Category.id_comp]
  have hR : eHomEquiv V (𝟙 d) ≫ eHomWhiskerLeft V d f ≫ gEmap Φ d d' =
      eHomEquiv V (gMap Φ f) := by
    rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerLeft, Category.id_comp, gEmap_hom]
  exact (eHomEquiv V).injective
    (hL.symm.trans ((eHomEquiv V (𝟙 d) ≫= hnat).trans hR))

/-- **Naturality of the comparison isomorphism at the unit probe**: the action of the family
on the 2-cell `unitCell f` attached to a morphism `f : d ⟶ d'` of `D` is the reconstructed
action `gMap Φ f`, conjugated by the comparison isomorphisms. -/
lemma homIso_naturality_const (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x)) {d d' : D.carrier} (f : d ⟶ d') :
    UnitNat Φ (unitCell f) := by
  set y : V := (d ⟶[V] d)
  set A : VCat.{w, v, max u w} V := arrowVCat.{w, v, max u w} Z y
  set m : A ⟶ D := arrowVFunctor Z y d d (𝟙 y)
  set m' : A ⟶ D := arrowVFunctor Z y d d' (eHomWhiskerLeft V d f)
  set a1 : A.carrier := arrowTgt.{w, v, max u w} Z y
  set γ : m ⟶ m' := arrowVNatTrans Z y (𝟙 d) f (arrow_sq Z f)
  have hsm : IsVProbeIndex.{w, v, u} P A.carrier :=
    VProbeSystem.isVProbeIndex_carrier (harr y)
  set Θ := (Φ.fn (IsVProbeIndex.mem_self P A)).map γ
  set δ : (m ≫ toVFunctor Φ) ⟶ (m' ≫ toVFunctor Φ) := (homIso Φ m).hom ≫ Θ ≫ (homIso Φ m').inv
  have hδsrc := arrowVNatTrans_delta_src_id Φ Z f hsm
  have hkey : δ.app a1 = gMap Φ f :=
    arrowVNatTrans_delta_tgt_eq Φ Z f hsm hδsrc
  -- (`γ.app a1` is `f`.)
  have hcomp : gMap Φ f ≫ (homIso Φ m').hom.app a1 = (homIso Φ m).hom.app a1 ≫ Θ.app a1 := by
    have hinv : (homIso Φ m').inv.app a1 ≫ (homIso Φ m').hom.app a1 = 𝟙 _ :=
      (vNatIsoApp (homIso Φ m') a1).inv_hom_id
    rw [← hkey]
    -- `δ.app a1` is the composite of the components; cancel `inv ≫ hom`.
    exact (Category.assoc _ _ _).trans
      (_ ≫= ((Category.assoc _ _ _).trans ((_ ≫= hinv).trans (Category.comp_id _))))
  have hcell : UnitNat Φ (unitPt a1 ◁ γ) := (homIso_component_iff Φ γ a1).mp hcomp
  have h : (unitPt a1 ≫ m : unitVCat.{w, v, max u w} V ⟶ D) = unitPt d := unitPt_comp₁ a1 m
  have h' : (unitPt a1 ≫ m' : unitVCat.{w, v, max u w} V ⟶ D) = unitPt d' := unitPt_comp₁ a1 m'
  have hEq : unitCell f = (eqToHom h.symm ≫ (unitPt a1 ◁ γ) ≫ eqToHom h' :
      unitPt d ⟶ unitPt (X := D) d') := by
    refine VNatTrans.ext (funext fun _ => ?_)
    rw [vCat_vcomp_app, vCat_vcomp_app, VNatTrans.eqToHom_app, VNatTrans.eqToHom_app]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  rw [hEq]
  exact unitNat_congr Φ h h' hcell

/-- Naturality of the comparison isomorphism at the unit probe, for an arbitrary 2-cell. -/
lemma homIso_naturality_unit (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    {m m' : unitVCat.{w, v, max u w} V ⟶ D} (δ : m ⟶ m') : UnitNat Φ δ := by
  obtain ⟨d, rfl⟩ : ∃ d : D.carrier, m = unitPt d := ⟨_, unitVFunctor_eq_const m⟩
  obtain ⟨d', rfl⟩ : ∃ d' : D.carrier, m' = unitPt d' := ⟨_, unitVFunctor_eq_const m'⟩
  have hd : δ = unitCell (δ.app (UnitVCat.star V)) := VNatTrans.ext (funext fun _ => rfl)
  refine (homIso_naturality_const Φ Z harr (δ.app (UnitVCat.star V))).trans ?_
  exact (homIso Φ (unitPt d)).hom.app (UnitVCat.star V) ≫=
    congr(((Φ.fn (VProbeSystem.unit (V := V) (P := P))).map $hd.symm).app (UnitVCat.star V))

end AHomFamily

end UlmerBialgebras
