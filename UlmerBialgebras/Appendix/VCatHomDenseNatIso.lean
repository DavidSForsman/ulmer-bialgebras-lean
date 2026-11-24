module

public import UlmerBialgebras.Appendix.VCatHomDenseIso

/-!
# The comparison isomorphism is compatible with pseudonaturality

`VCatHomDenseIso.lean` produces, for a pseudonatural family `Φ` of functors on the
representables of the small `V`-categories, an isomorphism
`UlmerBialgebras.AHomFamily.homIso Φ k : k ≫ toVFunctor Φ ≅ (Φ.fn hx).obj k`.

This file proves the first of the two conditions making it a representation of `Φ`:

* `UlmerBialgebras.AHomFamily.homIso_nat` — `homIso` intertwines the pseudonaturality isomorphisms
  of `Φ` with the associativity constraints of `CAT_V`.

No hypothesis on the monoidal base is needed.

## Main results

* `UlmerBialgebras.AHomFamily.homIso_nat`: the comparison isomorphism `homIso` is compatible with
  the pseudonaturality isomorphisms of the family and the associativity of `CAT_V`.

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
variable {D C : VCat.{w, v, max u w} V}

namespace AHomFamily

variable {P : VCat.{w, v, max u w} V → Prop}
variable (Φ : AHomFamily P D C)

/-- The factorisations through the probes are compatible with pre-composition. The target of
`vProbeFactor (u ≫ k)` is written as `vProbe (fun x => k.obj (u.obj x))`. -/
lemma vProbeFactor_comp_reindex {x y : VCat.{w, v, max u w} V} (u : x ⟶ y) (k : y ⟶ D) :
    (vProbeFactor (u ≫ k) : x ⟶ vProbe (fun x => k.obj (u.obj x))) ≫ vProbeReindex (k.obj) (u.obj)
      = u ≫ vProbeFactor k := by
  refine VFunctor.ext' ?_ ?_
  · exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      ((Category.id_comp _).trans (Category.comp_id _)).symm)
  · intro a b
    exact (Category.comp_id _).trans (Category.comp_id _)

/-! ## Componentwise forms of the coherence axioms -/

section

variable {x y : VCat.{w, v, max u w} V} [hx : IsVProbeIndex.{w, v, u} P x.carrier]
  [hy : IsVProbeIndex.{w, v, u} P y.carrier]

/-- Reassociating and merging the `eqToHom`s in `(eqToHom ≫ f) ≫ eqToHom ≫ g`. -/
private lemma eqToHom_comp_comp_eqToHom_comp' {X : Type*} [Category X] {a a₁ a₂ b c d e : X}
    (p : a = b) (p₁ : a = a₁) (p₂ : a₁ = a₂) (p₃ : a₂ = b) (f : b ⟶ c) (q q' : c = d)
    (g : d ⟶ e) :
    (eqToHom p ≫ f) ≫ eqToHom q ≫ g
      = eqToHom p₁ ≫ eqToHom p₂ ≫ (eqToHom p₃ ≫ f ≫ eqToHom q') ≫ g := by
  simp

/-- Cancelling a loop of `eqToHom`s in front of `f ≫ eqToHom ≫ g`. -/
private lemma eqToHom_comp_eqToHom_comp_cancel {X : Type*} [Category X] {a a₁ a₂ a₃ b c d : X}
    (p₁ : a = a₁) (p₂ : a₁ = a₂) (p₃ : a₂ = a₃) (p₄ : a₃ = a) (f : a ⟶ b) (q q' : b = c)
    (g : c ⟶ d) :
    eqToHom p₁ ≫ eqToHom p₂ ≫ eqToHom p₃ ≫ (eqToHom p₄ ≫ f ≫ eqToHom q) ≫ g
      = f ≫ eqToHom q' ≫ g := by
  simp

/-- The componentwise form of the cocycle identity relating the pseudonaturality
isomorphism along `u`, the ones along the two factorisations through probes, and the
comparison isomorphism of the reindexing of probes. -/
lemma natFactorIso_cocycle (u : x ⟶ y) (k : y ⟶ D) (a : x.carrier) :
    (natFactorIso Φ (u ≫ k)).hom.app a ≫ (probeCmp Φ (k.obj) (u.obj)).hom.app (vProbeObj _ a)
      = ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y) u).hom.app
            k).app a
          ≫ (natFactorIso Φ k).hom.app (u.obj a) := by
  -- The cocycle law of `Φ.nat` for `x → vProbe (k ∘ u) → vProbe k → D` and for
  -- `x → y → vProbe k → D`, with the transports along the factorisations through the probes.
  have h1 := nat_comp_app Φ (IsVProbeIndex.mem_self P x)
    (IsVProbeIndex.mem (fun x => k.obj (u.obj x))) (IsVProbeIndex.mem (k.obj))
    (vProbeFactor (u ≫ k) : x ⟶ vProbe (fun x => k.obj (u.obj x)))
    (vProbeReindex (k.obj) (u.obj)) (vProbeIncl (k.obj)) a
  have hA := nat_app_congr_app Φ (IsVProbeIndex.mem_self P x)
    (IsVProbeIndex.mem (fun x => k.obj (u.obj x)))
    (vProbeFactor (u ≫ k) : x ⟶ vProbe (fun x => k.obj (u.obj x)))
    (vProbeReindex_comp_incl (k.obj) (u.obj)) a
  have h2 := nat_comp_app Φ (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y)
    (IsVProbeIndex.mem (k.obj)) u (vProbeFactor k) (vProbeIncl (k.obj)) a
  have hB := nat_app_congr_app Φ (IsVProbeIndex.mem_self P x)
    (IsVProbeIndex.mem_self P y) u (vProbeFactor_comp_incl k) a
  -- The two composites `x → vProbe k` are equal (`vProbeFactor_comp_reindex`), so the two
  -- laws compare.
  have h3 := nat_congr_app Φ (IsVProbeIndex.mem_self P x)
    (IsVProbeIndex.mem (k.obj)) (vProbeFactor_comp_reindex u k) (vProbeIncl (k.obj)) a
  rw [hA] at h1
  rw [hB] at h2
  replace h3 := h1.symm.trans (h3.trans (eqToHom _ ≫= (h2 =≫ eqToHom _)))
  replace h3 := h3.trans (eqToHom _ ≫= Category.comp_id _)
  have hcell : ((vProbeFactor (u ≫ k) : x ⟶ vProbe (fun x => k.obj (u.obj x))) ≫
      vProbeReindex (k.obj) (u.obj)) ≫ vProbeIncl (k.obj) = u ≫ k := by
    rw [vProbeFactor_comp_reindex, Category.assoc, vProbeFactor_comp_incl]
  have E := eqToHom congr(((Φ.fn (IsVProbeIndex.mem_self P x)).obj $hcell.symm).obj a) ≫= h3
  -- Unfold the three isomorphisms of the statement to components of `Φ.nat`; what is left is
  -- merging transports.
  rw [natFactorIso_hom_app, probeCmp_hom_app, VNatTrans.eqToHom_app,
    natFactorIso_hom_app]
  refine Eq.trans ?_ (Eq.trans E ?_)
  · exact eqToHom_comp_comp_eqToHom_comp' _ _ _ _ _ _ _ _
  · exact eqToHom_comp_eqToHom_comp_cancel _ _ _ _ _ _ _ _

variable [VProbeSystem.{w, v, u} P]

/-- **The comparison isomorphism is compatible with the pseudonaturality isomorphisms** of
the family. -/
lemma homIso_nat (u : x ⟶ y) (k : y ⟶ D) :
    (homIso Φ (u ≫ k)).hom ≫ (Φ.nat (IsVProbeIndex.mem_self P x)
        (IsVProbeIndex.mem_self P y) u).hom.app k
      = eqToHom (Category.assoc u k (toVFunctor Φ)) ≫ (u ◁ (homIso Φ k).hom) := by
  refine VNatTrans.ext (funext fun a => ?_)
  -- Componentwise, this is the cocycle identity `natFactorIso_cocycle` ...
  have hkey := natFactorIso_cocycle Φ u k a
  simp only [vCat_vcomp_app, vCat_whiskerLeft_app, VNatTrans.eqToHom_app, homIso,
    Iso.trans_hom, Iso.symm_hom]
  have hstep : (natFactorIso Φ (u ≫ k)).inv.app a
        ≫ ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y) u).hom.app
            k).app a
      = (probeCmp Φ (k.obj) (u.obj)).hom.app (vProbeObj _ a)
        ≫ (natFactorIso Φ k).inv.app (u.obj a) := by
    refine (Iso.eq_comp_inv (vNatIsoApp (natFactorIso Φ k) (u.obj a))).mpr ?_
    refine (Category.assoc _ _ _).trans ?_
    rw [vNatIsoApp_hom]
    exact (_ ≫= hkey.symm).trans ((vNatIsoApp (natFactorIso Φ (u ≫ k)) a).inv_hom_id_assoc _)
  -- ... combined with the compatibility of the comparison isomorphisms with reindexing.
  have hcmp : (probeFactorIso Φ (u ≫ k)).hom.app a
        ≫ (probeCmp Φ (k.obj) (u.obj)).hom.app (vProbeObj _ a)
      = (probeFactorIso Φ k).hom.app (u.obj a) :=
    probeIso_reindex Φ (k.obj) (u.obj) a
  have h_assoc1 : ((probeFactorIso Φ (u ≫ k)).hom.app a ≫ (natFactorIso Φ (u ≫ k)).inv.app a)
      ≫ ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y) u).hom.app k).app a
    = (probeFactorIso Φ (u ≫ k)).hom.app a ≫
      ((natFactorIso Φ (u ≫ k)).inv.app a ≫
        ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y) u).hom.app k).app a) :=
    Category.assoc _ _ _
  have h_assoc2 : (probeFactorIso Φ (u ≫ k)).hom.app a ≫
      ((probeCmp Φ (k.obj) (u.obj)).hom.app (vProbeObj _ a) ≫
        (natFactorIso Φ k).inv.app (u.obj a))
    = ((probeFactorIso Φ (u ≫ k)).hom.app a ≫
        (probeCmp Φ (k.obj) (u.obj)).hom.app (vProbeObj _ a)) ≫
      (natFactorIso Φ k).inv.app (u.obj a) :=
    (Category.assoc _ _ _).symm
  have hchain : ((probeFactorIso Φ (u ≫ k)).hom.app a ≫ (natFactorIso Φ (u ≫ k)).inv.app a)
      ≫ ((Φ.nat (IsVProbeIndex.mem_self P x) (IsVProbeIndex.mem_self P y) u).hom.app k).app a
    = (probeFactorIso Φ k).hom.app (u.obj a) ≫ (natFactorIso Φ k).inv.app (u.obj a) :=
    h_assoc1.trans ((probeFactorIso Φ (u ≫ k)).hom.app a ≫= hstep
      |>.trans (h_assoc2.trans (hcmp =≫ (natFactorIso Φ k).inv.app (u.obj a))))
  exact hchain.trans (Category.id_comp _).symm

end

end AHomFamily

end UlmerBialgebras
