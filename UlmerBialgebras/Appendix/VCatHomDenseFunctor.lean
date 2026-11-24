module

public import UlmerBialgebras.Appendix.VCatHomDense
public import UlmerBialgebras.Appendix.VCatConj

/-!
# The `V`-functor reconstructed from a pseudonatural family on the small probes

`VCatHomDense.lean` evaluates a pseudonatural family `Φ` of functors on the representables of
the small `V`-categories at the *induced probes* of `VCatProbe.lean`, and produces

* the object map `UlmerBialgebras.AHomFamily.objMap`, read off the one-point probes, and
* the comparison isomorphisms `UlmerBialgebras.AHomFamily.probeIso` at the indices of an arbitrary
  probe.

This file turns that data into a genuine `V`-functor `D ⟶ C`:

* `UlmerBialgebras.AHomFamily.probeEmap`, `UlmerBialgebras.AHomFamily.probeMap` — the action on
  hom-objects and on morphisms read off a probe, conjugated by the comparison isomorphisms;
* `UlmerBialgebras.AHomFamily.probeEmap_reindex`, `UlmerBialgebras.AHomFamily.probeMap_reindex` —
  these do not change under reindexing of the probe;
* `UlmerBialgebras.AHomFamily.probeEmap_eq`, `UlmerBialgebras.AHomFamily.probeMap_eq` — hence they
  only depend on the objects of `D` involved, and agree with the values read off the canonical
  two-point probe;
* `UlmerBialgebras.AHomFamily.toVFunctor : D ⟶ C` — the reconstructed `V`-functor.  Its
  functoriality and its compatibility with the enriched composition come from the corresponding
  properties of the `V`-functors `UlmerBialgebras.AHomFamily.probeVal` on the three-point probes.

No hypothesis on the monoidal base is needed here: the induced probes exist for any `V`.

## Main results

* `UlmerBialgebras.AHomFamily.probeEmap_reindex`, `UlmerBialgebras.AHomFamily.probeMap_reindex`: the
  actions on hom-objects and on morphisms read off a probe do not change under reindexing of the
  probe.
* `UlmerBialgebras.AHomFamily.probeEmap_eq`, `UlmerBialgebras.AHomFamily.probeMap_eq`: these actions
  agree with the values read off the canonical two-point probe.
* `UlmerBialgebras.AHomFamily.toVFunctor`: the `V`-functor `D ⟶ C` reconstructed from a
  pseudonatural family on the probes.

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

/-! ## The data read off a probe -/

/-- The comparison isomorphism attached to a reindexing, at an index. -/
def probeCmpIso {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S] [IsVProbeIndex.{w, v, u} P T]
    (κ : T → D.carrier)
    (r : S → T) (s : S) :
    (probeVal Φ (fun x => κ (r x))).obj (vProbeObj _ s) ≅ (probeVal Φ κ).obj (vProbeObj κ (r s)) :=
  vNatIsoApp (probeCmp Φ κ r) (vProbeObj _ s)

/-- The forward map of `probeCmpIso` is the component at `s` of `probeCmp Φ κ r`. -/
@[simp] lemma probeCmpIso_hom {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier) (r : S → T) (s : S) :
    (probeCmpIso Φ κ r s).hom = (probeCmp Φ κ r).hom.app (vProbeObj _ s) := rfl

/-- The inverse map of `probeCmpIso` is the component at `s` of the inverse of `probeCmp Φ κ r`. -/
@[simp] lemma probeCmpIso_inv {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier) (r : S → T) (s : S) :
    (probeCmpIso Φ κ r s).inv = (probeCmp Φ κ r).inv.app (vProbeObj _ s) := rfl

/-- Naturality of `probeCmpIso` on hom-objects: the `V`-naturality of the probe comparison, at
the objects of the probe. -/
lemma probeCmpIso_hom_vnaturality {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier) (r : S → T) (s s' : S) :
    (probeVal Φ (fun x => κ (r x))).emap (vProbeObj _ s) (vProbeObj _ s') ≫
        eHomWhiskerLeft V ((probeVal Φ (fun x => κ (r x))).obj (vProbeObj _ s))
          (probeCmpIso Φ κ r s').hom
      = (probeVal Φ κ).emap (vProbeObj κ (r s)) (vProbeObj κ (r s')) ≫
        eHomWhiskerRight V (probeCmpIso Φ κ r s).hom
          ((probeVal Φ κ).obj (vProbeObj κ (r s'))) :=
  by simpa only [vCat_comp₁_eq, VFunctor.comp_emap, VFunctor.comp_obj, vProbeReindex_obj,
    vProbeReindex_emap, Category.id_comp, probeCmpIso_hom] using
    (probeCmp Φ κ r).hom.vnaturality (vProbeObj _ s) (vProbeObj _ s')

/-- Naturality of `probeCmpIso` on morphisms: the naturality of the probe comparison, at the
objects of the probe. -/
lemma probeCmpIso_hom_naturality {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier) (r : S → T) {s s' : S}
    (f : κ (r s) ⟶ κ (r s')) :
    (probeVal Φ (fun x => κ (r x))).toFunctor.map (X := vProbeObj _ s) (Y := vProbeObj _ s') f ≫
        (probeCmpIso Φ κ r s').hom
      = (probeCmpIso Φ κ r s).hom ≫
        (probeVal Φ κ).toFunctor.map (X := vProbeObj κ (r s)) (Y := vProbeObj κ (r s')) f :=
  (probeCmp Φ κ r).hom.naturality (X := vProbeObj _ s) (Y := vProbeObj _ s') f

variable [VProbeSystem.{w, v, u} P]

/-- The action on hom-objects read off a probe, conjugated by the comparison isomorphisms. -/
def probeEmap {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) (s s' : S) :
    (ι s ⟶[V] ι s') ⟶ (objMap Φ (ι s) ⟶[V] objMap Φ (ι s')) :=
  (probeVal Φ ι).emap (vProbeObj ι s) (vProbeObj ι s') ≫
    eHomConj₂ (probeIso Φ ι s) (probeIso Φ ι s')

/-- The action on morphisms read off a probe, conjugated by the comparison isomorphisms. -/
def probeMap {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) {s s' : S}
    (f : ι s ⟶ ι s') : objMap Φ (ι s) ⟶ objMap Φ (ι s') :=
  (probeIso Φ ι s).hom ≫
    (probeVal Φ ι).toFunctor.map (X := vProbeObj ι s) (Y := vProbeObj ι s') f ≫
    (probeIso Φ ι s').inv

/-- The comparison isomorphisms of the probes are compatible with reindexing. -/
lemma probeIso_trans_probeCmpIso {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T]
    (κ : T → D.carrier) (r : S → T) (s : S) :
    probeIso Φ (fun x => κ (r x)) s ≪≫ probeCmpIso Φ κ r s = probeIso Φ κ (r s) :=
  Iso.ext (probeIso_reindex Φ κ r s)

/-! ## Independence of the probe -/

/-- The action on hom-objects does not change under reindexing of the probe. -/
lemma probeEmap_reindex {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier)
    (r : S → T) (s s' : S) :
    probeEmap Φ (fun x => κ (r x)) s s' = probeEmap Φ κ (r s) (r s') := by
  -- On hom-objects, the probe along `κ ∘ r` is the probe along `κ` conjugated by the
  -- comparison isomorphisms of the reindexing (their `V`-naturality, whiskered by the inverse)
  have hstep : (probeVal Φ (fun x => κ (r x))).emap (vProbeObj _ s) (vProbeObj _ s')
      = (probeVal Φ κ).emap (vProbeObj κ (r s)) (vProbeObj κ (r s'))
        ≫ eHomConj₂ (probeCmpIso Φ κ r s) (probeCmpIso Φ κ r s') := by
    rw [eHomConj₂, ← Category.assoc, ← probeCmpIso_hom_vnaturality, Category.assoc,
      ← eHomWhiskerLeft_comp, Iso.hom_inv_id, eHomWhiskerLeft_id, Category.comp_id]
  -- and these compose with the comparison isomorphisms of `κ ∘ r` to those of `κ`.
  rw [probeEmap, probeEmap, hstep, Category.assoc, eHomConj₂_trans, probeIso_trans_probeCmpIso,
    probeIso_trans_probeCmpIso]

/-- The action on morphisms does not change under reindexing of the probe. -/
lemma probeMap_reindex {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T] (κ : T → D.carrier)
    (r : S → T) {s s' : S} (f : κ (r s) ⟶ κ (r s')) :
    probeMap Φ (fun x => κ (r x)) (s := s) (s' := s') f = probeMap Φ κ f := by
  -- The probe along `κ ∘ r` acts by the probe along `κ`, conjugated by the comparison
  -- isomorphisms of the reindexing; these compose with those of `κ ∘ r` to those of `κ`.
  have hstep := (Iso.eq_comp_inv (probeCmpIso Φ κ r s')).mpr (probeCmpIso_hom_naturality Φ κ r f)
  rw [probeMap, probeMap, hstep, ← probeIso_trans_probeCmpIso Φ κ r s,
    ← probeIso_trans_probeCmpIso Φ κ r s']
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-! ## The canonical two- and three-point probes -/

/-- The two-point probe on a pair of objects of `D`. -/
def pair2 (d d' : D.carrier) : ULift.{max u w} Bool → D.carrier :=
  fun b => bif b.down then d' else d

/-- The three-point probe on a triple of objects of `D`. -/
def triple3 (d₁ d₂ d₃ : D.carrier) : Option (ULift.{max u w} Bool) → D.carrier
  | none => d₁
  | some ⟨false⟩ => d₂
  | some ⟨true⟩ => d₃

/-- Probes with the same index map give the same action on hom-objects. -/
lemma probeEmap_congr {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] {ι ι' : S → D.carrier}
    (h : ι = ι')
    (s s' : S) : HEq (probeEmap Φ ι s s') (probeEmap Φ ι' s s') := by
  subst h; rfl

/-- Probes with the same index map give the same action on morphisms. -/
lemma probeMap_congr {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] {ι ι' : S → D.carrier}
    (h : ι = ι')
    {s s' : S} (f : ι s ⟶ ι s') (f' : ι' s ⟶ ι' s') (hf : f ≍ f') :
    probeMap Φ ι f ≍ probeMap Φ ι' f' := by
  subst h
  obtain rfl : f = f' := eq_of_heq hf
  rfl

/-! ## The reconstructed `V`-functor -/

/-- The action on hom-objects of the reconstructed `V`-functor: the one read off the
canonical two-point probe. -/
def gEmap (d d' : D.carrier) : (d ⟶[V] d') ⟶ (objMap Φ d ⟶[V] objMap Φ d') :=
  probeEmap Φ (pair2 d d') ⟨false⟩ ⟨true⟩

/-- The action on morphisms of the reconstructed `V`-functor: the one read off the canonical
two-point probe. -/
def gMap {d d' : D.carrier} (f : d ⟶ d') : objMap Φ d ⟶ objMap Φ d' :=
  probeMap Φ (pair2 d d') (s := ⟨false⟩) (s' := ⟨true⟩) f

/-- **Every probe computes the action on hom-objects.** -/
lemma probeEmap_eq {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) (s s' : S) :
    probeEmap Φ ι s s' = gEmap Φ (ι s) (ι s') := by
  have hfun : (fun b : ULift.{max u w} Bool => ι (bif b.down then s' else s))
      = pair2 (ι s) (ι s') := by
    funext b
    rcases b with ⟨(_ | _)⟩ <;> rfl
  exact ((probeEmap_reindex Φ ι (fun b : ULift.{max u w} Bool => bif b.down then s' else s)
      ⟨false⟩ ⟨true⟩).symm.trans (eq_of_heq (probeEmap_congr Φ hfun ⟨false⟩ ⟨true⟩)))

/-- **Every probe computes the action on morphisms.** -/
lemma probeMap_eq {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) (s s' : S)
    (f : ι s ⟶ ι s') : probeMap Φ ι f = gMap Φ f := by
  have hfun : (fun b : ULift.{max u w} Bool => ι (bif b.down then s' else s))
      = pair2 (ι s) (ι s') := by
    funext b
    rcases b with ⟨(_ | _)⟩ <;> rfl
  exact ((probeMap_reindex Φ ι (fun b : ULift.{max u w} Bool => bif b.down then s' else s)
      (s := ⟨false⟩) (s' := ⟨true⟩) f).symm.trans
    (eq_of_heq (probeMap_congr Φ hfun (s := ⟨false⟩) (s' := ⟨true⟩) f _ HEq.rfl)))

/-- The reconstructed action on morphisms `gMap` preserves identities. -/
lemma gMap_id (d : D.carrier) : gMap Φ (𝟙 d) = 𝟙 (objMap Φ d) := by
  -- On the one-point probe, `𝟙 d` is the identity of its object.
  refine (probeMap_eq Φ (pt d) PUnit.unit PUnit.unit (𝟙 d)).symm.trans ?_
  exact (_ ≫= (((probeVal Φ (pt d)).toFunctor.map_id (vProbeObj _ PUnit.unit) =≫ _).trans
    (Category.id_comp _))).trans (Iso.hom_inv_id _)

/-- Regroup `u ≫ (f ≫ g) ≫ v` by inserting `i.inv ≫ i.hom` between `f` and `g`. -/
lemma cancel_iso_comp {X Y Z W U M : C.carrier}
    (u : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ W) (v : W ⟶ U) (i : M ≅ Z) :
    u ≫ (f ≫ g) ≫ v = (u ≫ f ≫ i.inv) ≫ (i.hom ≫ g ≫ v) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The reconstructed action on morphisms `gMap` preserves composition. -/
lemma gMap_comp {d₁ d₂ d₃ : D.carrier} (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    gMap Φ (f ≫ g) = gMap Φ f ≫ gMap Φ g := by
  have h₁ : probeMap Φ (triple3 d₁ d₂ d₃) (s := none) (s' := some ⟨false⟩) f = gMap Φ f :=
    probeMap_eq Φ (triple3 d₁ d₂ d₃) none (some ⟨false⟩) f
  have h₂ : probeMap Φ (triple3 d₁ d₂ d₃) (s := some ⟨false⟩) (s' := some ⟨true⟩) g = gMap Φ g :=
    probeMap_eq Φ (triple3 d₁ d₂ d₃) (some ⟨false⟩) (some ⟨true⟩) g
  have h₃ : probeMap Φ (triple3 d₁ d₂ d₃) (s := none) (s' := some ⟨true⟩) (f ≫ g)
      = gMap Φ (f ≫ g) :=
    probeMap_eq Φ (triple3 d₁ d₂ d₃) none (some ⟨true⟩) (f ≫ g)
  rw [← h₁, ← h₂, ← h₃]
  dsimp only [probeMap]
  have hmc := (probeVal Φ (triple3 d₁ d₂ d₃)).toFunctor.map_comp
    (X := none) (Y := some ⟨false⟩) (Z := some (⟨true⟩ : ULift.{max u w} Bool)) f g
  have e1 := (probeIso Φ (triple3 d₁ d₂ d₃) none).hom ≫=
    (hmc =≫ (probeIso Φ (triple3 d₁ d₂ d₃) (some ⟨true⟩)).inv)
  have e2 := cancel_iso_comp ((probeIso Φ (triple3 d₁ d₂ d₃) none).hom)
    ((probeVal Φ (triple3 d₁ d₂ d₃)).toFunctor.map (X := none) (Y := some ⟨false⟩) f)
    ((probeVal Φ (triple3 d₁ d₂ d₃)).toFunctor.map (X := some ⟨false⟩) (Y := some ⟨true⟩) g)
    ((probeIso Φ (triple3 d₁ d₂ d₃) (some ⟨true⟩)).inv)
    (probeIso Φ (triple3 d₁ d₂ d₃) (some ⟨false⟩))
  exact e1.trans e2

/-- The reconstructed action on hom-objects `gEmap` is compatible with composition
`eComp`. -/
lemma gEmap_comp (d₁ d₂ d₃ : D.carrier) :
    eComp V d₁ d₂ d₃ ≫ gEmap Φ d₁ d₃
      = (gEmap Φ d₁ d₂ ⊗ₘ gEmap Φ d₂ d₃)
        ≫ eComp V (objMap Φ d₁) (objMap Φ d₂) (objMap Φ d₃) := by
  -- Read the three actions off the three-point probe on `d₁, d₂, d₃` (`probeEmap_eq`).
  have h₁ : probeEmap Φ (triple3 d₁ d₂ d₃) none (some ⟨false⟩) = gEmap Φ d₁ d₂ :=
    probeEmap_eq Φ (triple3 d₁ d₂ d₃) none (some ⟨false⟩)
  have h₂ : probeEmap Φ (triple3 d₁ d₂ d₃) (some ⟨false⟩) (some ⟨true⟩) = gEmap Φ d₂ d₃ :=
    probeEmap_eq Φ (triple3 d₁ d₂ d₃) (some ⟨false⟩) (some ⟨true⟩)
  have h₃ : probeEmap Φ (triple3 d₁ d₂ d₃) none (some ⟨true⟩) = gEmap Φ d₁ d₃ :=
    probeEmap_eq Φ (triple3 d₁ d₂ d₃) none (some ⟨true⟩)
  rw [← h₁, ← h₂, ← h₃]
  -- On that probe, `probeVal` is a `V`-functor, so it is compatible with `eComp` ...
  dsimp only [probeEmap]
  have hcomp : eComp V d₁ d₂ d₃ ≫ (probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨true⟩)
      = ((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ⊗ₘ
          (probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩))
        ≫ eComp V ((probeVal Φ (triple3 d₁ d₂ d₃)).obj none)
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨false⟩))
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨true⟩)) :=
    (probeVal Φ (triple3 d₁ d₂ d₃)).emap_comp none (some ⟨false⟩) (some ⟨true⟩)
  let p0 := probeIso Φ (triple3 d₁ d₂ d₃) none
  let p1 := probeIso Φ (triple3 d₁ d₂ d₃) (some (⟨false⟩ : ULift.{max u w} Bool))
  let p2 := probeIso Φ (triple3 d₁ d₂ d₃) (some (⟨true⟩ : ULift.{max u w} Bool))
  -- ... and conjugation by the comparison isomorphisms commutes with `eComp`
  -- (`eComp_eHomConj₂`); the rest is reassociation and the interchange law of `⊗ₘ`.
  have e1 : eComp V d₁ d₂ d₃ ≫
        (probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨true⟩) ≫ eHomConj₂ p0 p2
      = (eComp V d₁ d₂ d₃ ≫ (probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨true⟩)) ≫
        eHomConj₂ p0 p2 :=
    (Category.assoc _ _ _).symm
  have e2 := hcomp =≫ eHomConj₂ p0 p2
  have e_comp := eComp_eHomConj₂ (V := V) p0 p1 p2
  have e3_assoc : (((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ⊗ₘ
          (probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩))
        ≫ eComp V ((probeVal Φ (triple3 d₁ d₂ d₃)).obj none)
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨false⟩))
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨true⟩))) ≫ eHomConj₂ p0 p2
      = ((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ⊗ₘ
          (probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩))
        ≫ (eComp V ((probeVal Φ (triple3 d₁ d₂ d₃)).obj none)
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨false⟩))
            ((probeVal Φ (triple3 d₁ d₂ d₃)).obj (some ⟨true⟩)) ≫ eHomConj₂ p0 p2) :=
    Category.assoc _ _ _
  have e3_step := ((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ⊗ₘ
          (probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩)) ≫= e_comp
  have e3 := e3_assoc.trans e3_step
  have e4 : ((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ⊗ₘ
          (probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩))
        ≫ ((eHomConj₂ p0 p1 ⊗ₘ eHomConj₂ p1 p2)
        ≫ eComp V (objMap Φ (triple3 d₁ d₂ d₃ none))
            (objMap Φ (triple3 d₁ d₂ d₃ (some ⟨false⟩)))
            (objMap Φ (triple3 d₁ d₂ d₃ (some ⟨true⟩))))
      = (((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩) ≫ eHomConj₂ p0 p1) ⊗ₘ
         ((probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩) ≫ eHomConj₂ p1 p2))
        ≫ eComp V (objMap Φ d₁) (objMap Φ d₂) (objMap Φ d₃) :=
    (Category.assoc _ _ _).symm.trans
      (MonoidalCategory.tensorHom_comp_tensorHom
          ((probeVal Φ (triple3 d₁ d₂ d₃)).emap none (some ⟨false⟩))
          ((probeVal Φ (triple3 d₁ d₂ d₃)).emap (some ⟨false⟩) (some ⟨true⟩))
          (eHomConj₂ p0 p1)
          (eHomConj₂ p1 p2) =≫ eComp V (objMap Φ d₁) (objMap Φ d₂) (objMap Φ d₃))
  exact e1.trans (e2.trans (e3.trans e4))

/-- Compatibility of the reconstructed hom-object action `gEmap` with the underlying
morphism action `gMap`, via `eHomEquiv`. -/
lemma gEmap_hom {d d' : D.carrier} (f : d ⟶ d') :
    eHomEquiv V f ≫ gEmap Φ d d' = eHomEquiv V (gMap Φ f) := by
  let p0 := probeIso Φ (pair2 d d') (⟨false⟩ : ULift.{max u w} Bool)
  let p1 := probeIso Φ (pair2 d d') (⟨true⟩ : ULift.{max u w} Bool)
  have e_assoc : eHomEquiv V f ≫ (probeVal Φ (pair2 d d')).emap ⟨false⟩ ⟨true⟩ ≫ eHomConj₂ p0 p1
      = (eHomEquiv V f ≫ (probeVal Φ (pair2 d d')).emap ⟨false⟩ ⟨true⟩) ≫ eHomConj₂ p0 p1 :=
    (Category.assoc _ _ _).symm
  have ehom := (probeVal Φ (pair2 d d')).emap_hom
    (X := (⟨false⟩ : ULift.{max u w} Bool)) (Y := ⟨true⟩) f
  have e_step := ehom =≫ eHomConj₂ p0 p1
  have e_conj := eHomEquiv_comp_eHomConj₂ (V := V) p0 p1
    ((probeVal Φ (pair2 d d')).toFunctor.map
      (X := (⟨false⟩ : ULift.{max u w} Bool)) (Y := ⟨true⟩) f)
  exact e_assoc.trans (e_step.trans e_conj)

/-- **The `V`-functor reconstructed from a pseudonatural family on the small probes.** -/
def toVFunctor : D ⟶ C where
  toFunctor :=
    { obj := objMap Φ
      map := fun {_ _} f => gMap Φ f
      map_id := gMap_id Φ
      map_comp := fun f g => gMap_comp Φ f g }
  emap := gEmap Φ
  emap_comp := gEmap_comp Φ
  emap_hom := fun {_ _} f => gEmap_hom Φ f

/-- The `V`-functor `toVFunctor Φ` acts on objects by `objMap Φ`. -/
@[simp] lemma toVFunctor_obj (d : D.carrier) : (toVFunctor Φ).obj d = objMap Φ d := rfl
/-- The `V`-functor `toVFunctor Φ` acts on morphisms by `gMap Φ`. -/
@[simp] lemma toVFunctor_map {d d' : D.carrier} (f : d ⟶ d') :
    (toVFunctor Φ).toFunctor.map f = gMap Φ f := rfl
/-- The `V`-functor `toVFunctor Φ` acts on hom-objects by `gEmap Φ`. -/
@[simp] lemma toVFunctor_emap (d d' : D.carrier) : (toVFunctor Φ).emap d d' = gEmap Φ d d' := rfl

end AHomFamily

end UlmerBialgebras
