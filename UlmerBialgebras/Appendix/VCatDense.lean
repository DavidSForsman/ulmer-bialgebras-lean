module

public import UlmerBialgebras.Appendix.VCatHomDenseNat

/-!
# Small `V`-categories are dense in `CAT_V`

`VCatCellDense.lean` proved the local half of density (`UlmerBialgebras.IsACellDense`) for the class
of small `V`-categories inside `CAT_V`.  This file assembles the work of
`VCatHomDense.lean`, `VCatHomDenseFunctor.lean`, `VCatHomDenseIso.lean`,
`VCatHomDenseNatIso.lean` and `VCatHomDenseUnit.lean` into the remaining half and hence into
density itself:

* `UlmerBialgebras.AHomFamily.representation` — a pseudonatural family of functors on the
  representables of the small `V`-categories is induced by the reconstructed `V`-functor
  `UlmerBialgebras.AHomFamily.toVFunctor`;
* `UlmerBialgebras.isAHomDense_isSmallVCat` — the 1-cell half of density;
* `UlmerBialgebras.isADense_isSmallVCat` — **small `V`-categories are dense in `CAT_V`**, a variant
  of Theorem A.5 for the larger class of all small `V`-categories.

The only hypothesis on the monoidal base `V` is that it has an *absorbing initial object*
(`UlmerBialgebras.MonoidalInitial`), i.e. an initial object `0` with `0 ⊗ y` and `y ⊗ 0` initial.
 This holds for any braided monoidal closed `V` with an initial object, in particular for any
complete and cocomplete symmetric monoidal closed base.
No completeness of `V` is required.

## Main results

* `UlmerBialgebras.AHomFamily.representation`: a pseudonatural family of functors on the
  representables of a system of probes containing the arrow `V`-categories is represented by the
  reconstructed `V`-functor.
* `UlmerBialgebras.isADense_of_vProbeSystem`: for `V` with an absorbing initial object, every system
  of probes containing the arrow `V`-categories is dense in `CAT_V`.
* `UlmerBialgebras.isAHomDense_isSmallVCat`: the 1-cell half of density for the small
  `V`-categories.
* `UlmerBialgebras.isADense_isSmallVCat`: the small `V`-categories are dense in `CAT_V`, a variant
  of Theorem A.5.

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

variable {P : VCat.{w, v, max u w} V → Prop} [VProbeSystem.{w, v, u} P]
variable (Φ : AHomFamily P D C)

/-- **The reconstructed `V`-functor represents the family.** -/
noncomputable def representation (Z : MonoidalInitial V)
    (harr : ∀ y : V, P (arrowVCat.{w, v, max u w} Z y)) : Φ.Representation where
  g := toVFunctor Φ
  iso := fun x hx => by
    have : IsVProbeIndex.{w, v, u} P x.carrier := VProbeSystem.isVProbeIndex_carrier hx
    exact NatIso.ofComponents (fun k => homIso Φ k) (fun β => homIso_naturality Φ Z harr β)
  iso_nat := fun x y hx hy u k => by
    have : IsVProbeIndex.{w, v, u} P x.carrier := VProbeSystem.isVProbeIndex_carrier hx
    have : IsVProbeIndex.{w, v, u} P y.carrier := VProbeSystem.isVProbeIndex_carrier hy
    exact homIso_nat Φ u k

end AHomFamily

/-- **The 1-cell half of density for any system of probes containing the arrow
`V`-categories**: every pseudonatural family of functors on the `P`-representables is induced
by a `V`-functor. -/
theorem isAHomDense_of_vProbeSystem (Z : MonoidalInitial V)
    (P : VCat.{w, v, max u w} V → Prop) [VProbeSystem.{w, v, u} P]
    (harr : ∀ y : V, P (arrowVCat.{w, v, max u w} Z y)) :
    IsAHomDense (Obj := VCat.{w, v, max u w} V) P :=
  fun _ _ Φ => ⟨Φ.representation Z harr⟩

/-- **Density for any system of probes containing the arrow `V`-categories.**  This is the
axiomatised form of `UlmerBialgebras.isADense_isSmallVCat`: the reconstruction of a `V`-functor from
a pseudonatural family only uses the point, two-point and three-point probes, the probes on the
object type of a member of the class, and the arrow `V`-categories. -/
theorem isADense_of_vProbeSystem (Z : MonoidalInitial V)
    (P : VCat.{w, v, max u w} V → Prop) [VProbeSystem.{w, v, u} P]
    (harr : ∀ y : V, P (arrowVCat.{w, v, max u w} Z y)) :
    IsADense (Obj := VCat.{w, v, max u w} V) P where
  cell := isACellDense_of_probes Z P (VProbeSystem.unit (V := V)) harr
  hom := isAHomDense_of_vProbeSystem Z P harr

/-- **The 1-cell half of density**: every pseudonatural family of functors on the
representables of the small `V`-categories is induced by a `V`-functor. -/
theorem isAHomDense_isSmallVCat (Z : MonoidalInitial V) :
    IsAHomDense (Obj := VCat.{w, v, max u w} V) (IsSmallVCat.{w, v, u} V) :=
  isAHomDense_of_vProbeSystem Z _ (fun y => isSmallVCat_arrowVCat.{w, v, u} Z y)

/-- **Small `V`-categories are dense in `CAT_V`**, for any monoidal base `V` with an
absorbing initial object: a variant of **Theorem A.5** ([forsman2026syntactic]) for the class of
all small `V`-categories, following Hofstra–Karvonen [hofstraInnerAutoequivalencesGeneral2024],
Lemma 7.1. -/
theorem isADense_isSmallVCat (Z : MonoidalInitial V) :
    IsADense (Obj := VCat.{w, v, max u w} V) (IsSmallVCat.{w, v, u} V) where
  cell := isACellDense_isSmallVCat.{w, v, u} Z
  hom := isAHomDense_isSmallVCat.{w, v, u} Z

end UlmerBialgebras
