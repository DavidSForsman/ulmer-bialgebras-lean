module

public import UlmerBialgebras.Appendix.VCatEssSmall

/-!
# Induced probes in `CAT_V`

`VCatEssSmall.lean` equips a type `S` with the `V`-category structure induced along a map
`ι : S → C` into a `V`-category (`UlmerBialgebras.vcatInduced`).  When `S` is `w`-small this is a
**small** `V`-category, and it comes with a canonical `V`-functor into `C`.  These are the
probes used in `VCatHomDense.lean` to reconstruct a `V`-functor `D ⟶ C` out of a
pseudonatural family of functors on the representables of the small `V`-categories.

* `UlmerBialgebras.vInducedInclAux`, `UlmerBialgebras.vProbeIncl` — the inclusion
  `vcatInduced C ι ⟶ C`, the identity on hom-objects;
* `UlmerBialgebras.vInducedReindexAux`, `UlmerBialgebras.vProbeReindex` — reindexing along
  `r : S → T`, a `V`-functor `vcatInduced C (κ ∘ r) ⟶ vcatInduced C κ` over `C`.

The compatibilities are *strict* equalities of `V`-functors, which is what makes the probes
convenient: `vProbeReindex κ r ≫ vProbeIncl κ = vProbeIncl (κ ∘ r)`
(`UlmerBialgebras.vProbeReindex_comp_incl`) and the functoriality of reindexing
(`UlmerBialgebras.vProbeReindex_comp`).  The restriction of a `V`-functor to induced probes and the
smallness of probes on `w`-small index types are not formalized in this file.

## Main results

* `UlmerBialgebras.vProbe`, `UlmerBialgebras.vProbeIncl`, `UlmerBialgebras.vProbeReindex`: the probe
  on a family of objects of `C`, its inclusion into `C`, and reindexing between probes.
* `UlmerBialgebras.vProbeReindex_comp_incl`:
  `vProbeReindex κ r ≫ vProbeIncl κ = vProbeIncl (κ ∘ r)`.
* `UlmerBialgebras.vProbeReindex_comp`: reindexing along `r'` then `r` is reindexing along `r ∘ r'`.
* `UlmerBialgebras.vProbeObj`: the object of a probe at an index, with its type, and its simp
  lemmas for the inclusion and reindexing.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u u₁ u₂ u₃

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-! ## The inclusion of an induced probe -/

section

variable {C : Type u₁} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The inclusion of an induced `V`-category: it is the identity on hom-objects. -/
@[reducible] def vInducedInclAux {S : Type u₂} (ι : S → C) : VFunctor V (VInduced ι) C where
  toFunctor :=
    { obj := ι
      map := fun {_ _} f => f
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  emap _ _ := 𝟙 _
  emap_comp _ _ _ := by
    simp only [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl
  emap_hom _ := by
    simp only [Category.comp_id]
    rfl

/-- The inclusion `vInducedInclAux ι` sends `s` to `ι s`. -/
@[simp] lemma vInducedInclAux_obj {S : Type u₂} (ι : S → C) (s : VInduced ι) :
    (vInducedInclAux (V := V) ι).obj s = ι s := rfl

/-- The inclusion `vInducedInclAux ι` acts on hom-objects by identities. -/
@[simp] lemma vInducedInclAux_emap {S : Type u₂} (ι : S → C) (a b : VInduced ι) :
    (vInducedInclAux (V := V) ι).emap a b = 𝟙 _ := rfl

/-- Reindexing an induced `V`-category along a map of index types. -/
@[reducible] def vInducedReindexAux {S : Type u₂} {T : Type u₃} (κ : T → C) (r : S → T) :
    VFunctor V (VInduced (fun x => κ (r x))) (VInduced κ) where
  toFunctor :=
    { obj := r
      map := fun {_ _} f => f
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  emap _ _ := 𝟙 _
  emap_comp _ _ _ := by
    simp only [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl
  emap_hom _ := by
    simp only [Category.comp_id]
    rfl

/-- Reindexing along `r` acts on objects by `r`. -/
@[simp] lemma vInducedReindexAux_obj {S : Type u₂} {T : Type u₃} (κ : T → C) (r : S → T)
    (s : VInduced (fun x => κ (r x))) : (vInducedReindexAux (V := V) κ r).obj s = r s := rfl

/-- Reindexing acts by the identity on hom-objects. -/
@[simp] lemma vInducedReindexAux_emap {S : Type u₂} {T : Type u₃} (κ : T → C) (r : S → T)
    (a b : VInduced (fun x => κ (r x))) :
    (vInducedReindexAux (V := V) κ r).emap a b = 𝟙 _ := rfl

/-- Reindexing composes. -/
lemma vInducedReindexAux_comp {S : Type u₂} {T : Type u₃} {U : Type u₁} (κ : U → C)
    (r : T → U) (r' : S → T) :
    (vInducedReindexAux (V := V) (fun x => κ (r x)) r').comp (vInducedReindexAux κ r)
      = vInducedReindexAux κ (fun x => r (r' x)) := by
  refine VFunctor.ext' rfl ?_
  intro a b
  dsimp [VFunctor.comp, vInducedReindexAux]
  rw [Category.id_comp]
  exact (whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _)

/-- Reindexing is a map over `C`. -/
lemma vInducedReindexAux_comp_incl {S : Type u₂} {T : Type u₃} (κ : T → C) (r : S → T) :
    (vInducedReindexAux (V := V) κ r).comp (vInducedInclAux κ)
      = vInducedInclAux (fun x => κ (r x)) := by
  refine VFunctor.ext' rfl ?_
  intro a b
  dsimp [VFunctor.comp, vInducedReindexAux, vInducedInclAux]
  rw [Category.id_comp]
  exact (whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _)

end

/-! ## Probes as objects and 1-cells of `CAT_V` -/

section

variable {C : VCat.{w, v, max u w} V}

/-- The probe attached to a family of objects of `C`, as an object of `CAT_V`. -/
abbrev vProbe {S : Type max u w} (ι : S → C.carrier) : VCat.{w, v, max u w} V :=
  vcatInduced C ι

/-- The inclusion 1-cell of a probe. -/
abbrev vProbeIncl {S : Type max u w} (ι : S → C.carrier) : vProbe ι ⟶ C :=
  vInducedInclAux ι

/-- The reindexing 1-cell between probes. -/
abbrev vProbeReindex {S T : Type max u w} (κ : T → C.carrier) (r : S → T) :
    vProbe (fun x => κ (r x)) ⟶ vProbe κ :=
  vInducedReindexAux κ r

/-- Reindexing a probe along `r` followed by the inclusion of the probe on `κ` is the
inclusion of the probe on `κ ∘ r`. -/
lemma vProbeReindex_comp_incl {S T : Type max u w} (κ : T → C.carrier) (r : S → T) :
    vProbeReindex κ r ≫ vProbeIncl κ = vProbeIncl (fun x => κ (r x)) :=
  vInducedReindexAux_comp_incl κ r

/-- Reindexing of probes composes: reindexing along `r'` then `r` is reindexing along `r ∘ r'`. -/
lemma vProbeReindex_comp {S T U : Type max u w} (κ : U → C.carrier) (r : T → U) (r' : S → T) :
    vProbeReindex (fun x => κ (r x)) r' ≫ vProbeReindex κ r
      = vProbeReindex κ (fun x => r (r' x)) :=
  vInducedReindexAux_comp κ r r'

/-! ### The objects of a probe

An object of `vProbe ι` is an index `s : S`, but only up to unfolding `VCat.of` and `VInduced`.
`vProbeObj ι s` is that object with its type, so that terms built from it are type-correct at
every transparency and `rw` and `simp` can work under them. -/

/-- The object of the probe `vProbe ι` at the index `s`. -/
abbrev vProbeObj {S : Type max u w} (ι : S → C.carrier) (s : S) : (vProbe ι).carrier := s

/-- The index of an object of the probe `vProbe ι`. -/
def vProbeObj.idx {S : Type max u w} {ι : S → C.carrier} (a : (vProbe ι).carrier) : S := a

/-- Every object of a probe is the object at its index. -/
@[simp] lemma vProbeObj_idx {S : Type max u w} (ι : S → C.carrier) (a : (vProbe ι).carrier) :
    vProbeObj ι (vProbeObj.idx a) = a := rfl

/-- The index of the object at `s` is `s`. -/
@[simp] lemma vProbeObj.idx_vProbeObj {S : Type max u w} (ι : S → C.carrier) (s : S) :
    vProbeObj.idx (vProbeObj ι s) = s := rfl

/-- The inclusion of a probe sends the object at `s` to `ι s`. -/
@[simp] lemma vProbeIncl_obj {S : Type max u w} (ι : S → C.carrier) (s : S) :
    (vProbeIncl ι).obj (vProbeObj ι s) = ι s := rfl

/-- The inclusion of a probe acts on hom-objects by identities. -/
@[simp] lemma vProbeIncl_emap {S : Type max u w} (ι : S → C.carrier) (a b : (vProbe ι).carrier) :
    (vProbeIncl ι).emap a b = 𝟙 _ := rfl

/-- Reindexing along `r` sends the object at `s` to the object at `r s`. -/
@[simp] lemma vProbeReindex_obj {S T : Type max u w} (κ : T → C.carrier) (r : S → T) (s : S) :
    (vProbeReindex κ r).obj (vProbeObj (fun x => κ (r x)) s) = vProbeObj κ (r s) := rfl

/-- Reindexing acts on hom-objects by identities. -/
@[simp] lemma vProbeReindex_emap {S T : Type max u w} (κ : T → C.carrier) (r : S → T)
    (a b : (vProbe (fun x => κ (r x))).carrier) : (vProbeReindex κ r).emap a b = 𝟙 _ := rfl

end

end UlmerBialgebras
