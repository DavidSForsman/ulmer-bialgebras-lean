module

public import UlmerBialgebras.Appendix.VProbeSystem
public import UlmerBialgebras.Density.ADense

/-!
# Reconstructing a `V`-functor from a pseudonatural family on the small probes

`VCatCellDense.lean` proves the *local* half of the density of the small `V`-categories in
`CAT_V`.  This file is about the 1-cell half: a pseudonatural family of functors
`CAT_V(a, D) ⥤ CAT_V(a, C)`, `a` small, is induced by a `V`-functor `D ⟶ C`.

The probes used are the *induced* ones of `VCatProbe.lean`: for a `w`-small family
`ι : S → D` of objects of `D`, the `V`-category `vProbe ι` with objects `S` and hom-objects
those of `D`.  Evaluating the family at the inclusion `vProbe ι ⟶ D` gives a `V`-functor
`Ψ ι : vProbe ι ⟶ C` (`UlmerBialgebras.AHomFamily.probeVal`), and reindexing along `r : S' → S`
gives comparison isomorphisms `Ψ (ι ∘ r) ≅ vProbeReindex ι r ≫ Ψ ι`
(`UlmerBialgebras.AHomFamily.probeCmp`).  Everything is then a consequence of the cocycle
axiom `nat_comp` of a pseudonatural family, through the single lemma
`UlmerBialgebras.AHomFamily.probeIso_reindex`.

## Main results

* `UlmerBialgebras.AHomFamily.probeVal`: the `V`-functor `vProbe ι ⟶ C` obtained by evaluating the
  family at the inclusion of an induced probe.
* `UlmerBialgebras.AHomFamily.objMap`: the object map of the reconstructed `V`-functor, the value of
  the family on the one-point probe.
* `UlmerBialgebras.AHomFamily.probeIso`: the comparison isomorphism
  `objMap Φ (ι s) ≅ (probeVal Φ ι).obj s`.
* `UlmerBialgebras.AHomFamily.probeIso_reindex`: the comparison isomorphisms are compatible with
  reindexing of probes.

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

/-- Two `eqToHom`s with equal sources are heterogeneously equal. -/
lemma heq_eqToHom_eqToHom {X : Type*} [Category X] {a b a' b' : X} (h : a = b) (h' : a' = b')
    (ha : a = a') : eqToHom h ≍ eqToHom h' := by
  subst ha; cases h; cases h'; rfl

namespace AHomFamily

variable {P : VCat.{w, v, max u w} V → Prop}
variable (Φ : AHomFamily P D C)

/-! ## Values of the family on the induced probes -/

/-- The `V`-functor obtained by evaluating the family at the inclusion of an induced probe. -/
def probeVal {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) : vProbe ι ⟶ C :=
  (Φ.fn (IsVProbeIndex.mem ι)).obj (vProbeIncl ι)

/-- The comparison isomorphism attached to a reindexing of probes. -/
def probeCmp {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S] [IsVProbeIndex.{w, v, u} P T]
    (κ : T → D.carrier)
    (r : S → T) : probeVal Φ (fun x => κ (r x)) ≅ vProbeReindex κ r ≫ probeVal Φ κ :=
  eqToIso (congrArg (Φ.fn (IsVProbeIndex.mem (fun x => κ (r x)))).obj
      (vProbeReindex_comp_incl κ r).symm) ≪≫
    (Φ.nat (IsVProbeIndex.mem (fun x => κ (r x))) (IsVProbeIndex.mem κ)
      (vProbeReindex κ r)).app (vProbeIncl κ)

/-- Componentwise form of the composition law of `Φ.nat`: at a composite `u ≫ p`, the component
is the composite of the components at `u` and at `p`, up to `eqToHom`. -/
lemma nat_comp_app {x y z : VCat.{w, v, max u w} V} (hx : P x) (hy : P y) (hz : P z)
    (u : x ⟶ y) (p : y ⟶ z) (m : z ⟶ D) (a : x.carrier) :
    ((Φ.nat hx hz (u ≫ p)).hom.app m).app a
      = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.assoc])
          ≫ ((Φ.nat hx hy u).hom.app (p ≫ m)).app a
          ≫ ((Φ.nat hy hz p).hom.app m).app (u.obj a) := by
  have h := congr(VNatTrans.app $(Φ.nat_comp hx hy hz u p m) a)
  simp only [vCat_vcomp_app, VNatTrans.eqToHom_app, vCat_whiskerLeft_app] at h
  -- the last transport of `h` is along a definitional equality of objects
  rw [h]
  congr 2
  exact Category.comp_id _

/-- Componentwise congruence of `Φ.nat` in the 1-cell `q`, up to `eqToHom`. -/
lemma nat_congr_app {x z : VCat.{w, v, max u w} V} (hx : P x) (hz : P z) {q q' : x ⟶ z}
    (h : q = q') (m : z ⟶ D)
    (a : x.carrier) :
    ((Φ.nat hx hz q).hom.app m).app a
      = eqToHom (by rw [h]) ≫ ((Φ.nat hx hz q').hom.app m).app a ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Componentwise congruence of `Φ.nat` in the object `m`, up to `eqToHom`. -/
lemma nat_app_congr_app {x z : VCat.{w, v, max u w} V} (hx : P x) (hz : P z) (q : x ⟶ z)
    {m m' : z ⟶ D} (h : m = m')
    (a : x.carrier) :
    ((Φ.nat hx hz q).hom.app m).app a
      = eqToHom (by rw [h]) ≫ ((Φ.nat hx hz q).hom.app m').app a ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- The components of the probe comparison `probeCmp Φ κ r`, unfolded. -/
lemma probeCmp_hom_app {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T]
    (κ : T → D.carrier) (r : S → T) (X : (vProbe (fun x => κ (r x))).carrier) :
    (probeCmp Φ κ r).hom.app X
      = (eqToHom congr((Φ.fn (IsVProbeIndex.mem (fun x => κ (r x)))).obj
          $((vProbeReindex_comp_incl κ r).symm))).app X
        ≫ ((Φ.nat (IsVProbeIndex.mem (fun x => κ (r x))) (IsVProbeIndex.mem κ)
            (vProbeReindex κ r)).hom.app (vProbeIncl κ)).app X :=
  rfl

/-! ## The comparison isomorphisms -/

variable [VProbeSystem.{w, v, u} P]

/-- The one-point family of objects. -/
def pt (d : D.carrier) : PUnit.{max u w + 1} → D.carrier := fun _ => d

/-- **The object map of the reconstructed `V`-functor**: the value of the family on the
one-point probe at `d`. -/
def objMap (d : D.carrier) : C.carrier := (probeVal Φ (pt d)).obj (vProbeObj _ PUnit.unit)

/-- **The comparison isomorphism at an index of a probe.** -/
def probeIso {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) (s : S) :
    objMap Φ (ι s) ≅ (probeVal Φ ι).obj (vProbeObj ι s) :=
  vNatIsoApp (probeCmp Φ ι (fun _ : PUnit.{max u w + 1} => s)) (vProbeObj _ PUnit.unit)

/-- The comparison isomorphism at an index is the component of the probe comparison for the
reindexing along that index. -/
lemma probeIso_hom {S : Type max u w} [IsVProbeIndex.{w, v, u} P S] (ι : S → D.carrier) (s : S) :
    (probeIso Φ ι s).hom
      = (probeCmp Φ ι (fun _ : PUnit.{max u w + 1} => s)).hom.app (vProbeObj _ PUnit.unit) :=
  rfl

/-- Reassociating and merging the `eqToHom`s in `eqToHom ≫ f ≫ eqToHom ≫ g`. -/
private lemma eqToHom_comp_comp_eqToHom_comp {X : Type*} [Category X] {a a₁ a₂ b c d e : X}
    (p : a = b) (p₁ : a = a₁) (p₂ : a₁ = a₂) (p₃ : a₂ = b) (f : b ⟶ c) (q q' : c = d)
    (g : d ⟶ e) :
    eqToHom p ≫ f ≫ eqToHom q ≫ g
      = eqToHom p₁ ≫ eqToHom p₂ ≫ (eqToHom p₃ ≫ f ≫ eqToHom q') ≫ g := by
  simp

/-- **The key coherence lemma**: the comparison isomorphisms at the indices of a probe are
compatible with reindexing. -/
lemma probeIso_reindex {S T : Type max u w} [IsVProbeIndex.{w, v, u} P S]
    [IsVProbeIndex.{w, v, u} P T]
    (κ : T → D.carrier) (r : S → T) (s : S) :
    (probeIso Φ (fun x => κ (r x)) s).hom
        ≫ (probeCmp Φ κ r).hom.app (vProbeObj (fun x => κ (r x)) s)
      = (probeIso Φ κ (r s)).hom := by
  let pt0 := vProbeObj (fun _ : PUnit.{max u w + 1} => κ (r s)) PUnit.unit
  -- `E`: the cocycle law of `Φ.nat` for the reindexings `PUnit → S → T`, at the point, with the
  -- composite reindexing replaced by the reindexing along `r s`.
  have hcomp : vProbeReindex (fun x => κ (r x)) (fun _ : PUnit.{max u w + 1} => s)
        ≫ vProbeReindex κ r
      = vProbeReindex κ (fun _ : PUnit.{max u w + 1} => r s) :=
    vProbeReindex_comp κ r _
  have h1 := nat_comp_app Φ (IsVProbeIndex.mem
      (fun _ : PUnit.{max u w + 1} => κ (r s)))
      (IsVProbeIndex.mem (fun x => κ (r x))) (IsVProbeIndex.mem κ)
      (vProbeReindex (fun x => κ (r x)) (fun _ : PUnit.{max u w + 1} => s)) (vProbeReindex κ r)
      (vProbeIncl κ) pt0
  have h2 := nat_congr_app Φ (IsVProbeIndex.mem
      (fun _ : PUnit.{max u w + 1} => κ (r s)))
      (IsVProbeIndex.mem κ) hcomp (vProbeIncl κ) pt0
  have h3 := nat_app_congr_app Φ (IsVProbeIndex.mem
      (fun _ : PUnit.{max u w + 1} => κ (r s)))
      (IsVProbeIndex.mem (fun x => κ (r x)))
      (vProbeReindex (fun x => κ (r x)) (fun _ : PUnit.{max u w + 1} => s))
      (vProbeReindex_comp_incl κ r) pt0
  have E := h1.symm.trans h2
  rw [h3] at E
  replace E := E.trans (eqToHom _ ≫= Category.comp_id _)
  -- The three comparison isomorphisms are components of `Φ.nat`, after a transport.
  rw [probeIso_hom, probeIso_hom, probeCmp_hom_app, probeCmp_hom_app, probeCmp_hom_app]
  refine (Category.assoc _ _ _).trans ?_
  -- Both sides are `E`, up to merging the transports along equalities of objects.
  have hcell :
      (vProbeReindex (fun x => κ (r x)) (fun _ : PUnit.{max u w + 1} => s) ≫ vProbeReindex κ r) ≫
        vProbeIncl κ = vProbeIncl (fun _ : PUnit.{max u w + 1} => κ (r s)) := by
    rw [Category.assoc, vProbeReindex_comp_incl, vProbeReindex_comp_incl]
  refine Eq.trans ?_ (Eq.trans (eqToHom congr(((Φ.fn (IsVProbeIndex.mem
      (fun _ : PUnit.{max u w + 1} => κ (r s)))).obj $hcell.symm).obj pt0) ≫= E) ?_)
  · rw [VNatTrans.eqToHom_app, VNatTrans.eqToHom_app]
    exact eqToHom_comp_comp_eqToHom_comp _ _ _ _ _ _ _ _
  · rw [VNatTrans.eqToHom_app]
    exact eqToHom_trans_assoc _ _ _

end AHomFamily

end UlmerBialgebras
