module

public import UlmerBialgebras.Paper.Sec7DefsSec7Variant
public import UlmerBialgebras.Proofs.Sec7.BiDenseBridge

/-!
# Solution: Definition 7.1 as a variant of Hofstra–Karvonen bi-density

The paper's Definition 7.1 says that a class `A` of objects of a strict 2-category `K` is
bi-dense if `c ↦ K(-, c)|_{A^op}` is bi-fully faithful, and calls this "a variation of the
bicategorical notion of density introduced in [HK, Definition 6.2]". Hofstra–Karvonen define
bi-density for a pseudofunctor `F : 𝒞 → 𝒟`: the functors
`𝒟(c, d) → [𝒞^op, Cat](𝒟(F-, c), 𝒟(F-, d))` are equivalences. We show that `A` is bi-dense in
the paper's sense iff the inclusion of the full sub-2-category spanned by `A` is bi-dense in
Hofstra–Karvonen's sense.

The proof translates both ways between the componentwise structures of Definition 7.1 and
modifications and strong transformations between the restricted representables (see
`UlmerBialgebras/Proofs/Sec7/BiDenseBridge.lean`): families of 2-cells are modifications between
induced
transformations, pseudonatural families of functors are strong transformations, and
representations are invertible modifications. Full faithfulness of the restricted Yoneda
functor is then `UlmerBialgebras.IsACellDense`, and its essential surjectivity is the 1-cell half of
Definition 7.1.

## Main results

* `UlmerBialgebras.Paper.isBiDense_iff_isBiDense_fullSubBicatι`: a class `A` of objects is bi-dense
  in the sense of Definition 7.1 iff the inclusion pseudofunctor of the full sub-2-category spanned
  by `A` is bi-dense in the sense of Hofstra–Karvonen.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Pseudofunctor.StrongTrans

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 7.1 versus Hofstra–Karvonen** ([forsman2026syntactic], Definition 7.1;
[hofstraInnerAutoequivalencesGeneral2024], Definition 6.2): a class `A` of objects of a strict
2-category `K` is bi-dense in the sense of Definition 7.1 iff the inclusion pseudofunctor of the
full sub-2-category spanned by `A` is bi-dense in the sense of Hofstra–Karvonen. -/
theorem isBiDense_iff_isBiDense_fullSubBicatι (A : ObjectProperty Obj) :
    IsBiDense A ↔ (fullSubBicatι A).IsBiDense := by
  -- Both say that the restriction functors `Φ A c d` are equivalences: Definition 7.1 gives a
  -- unique cell for each family (`Φ` full and faithful) and a representation of each strong
  -- transformation (`Φ` essentially surjective), and conversely.
  constructor
  · intro hA
    refine ⟨fun c d => ?_⟩
    have hfull : (BiDenseBridge.Φ A c d).Full := ⟨fun {p q} Γ => by
      obtain ⟨α, hα, -⟩ := hA.cell (BiDenseBridge.cellFamily Γ)
      refine ⟨α, ?_⟩
      ext X k
      exact congr(NatTrans.app $(hα X.unop.2) k)⟩
    have hfaith : (BiDenseBridge.Φ A c d).Faithful := ⟨fun {p q α β} h =>
      hA.cell.cell_ext (fun x hx =>
        congr((($h).as.app (Opposite.op (BiDenseBridge.ob x hx))).toNatTrans))⟩
    have hess : (BiDenseBridge.Φ A c d).EssSurj := ⟨fun η => by
      obtain ⟨r⟩ := hA.hom (BiDenseBridge.ofStrongTrans η)
      exact ⟨r.g, ⟨BiDenseBridge.isoOfRepresentation η r⟩⟩⟩
    exact Functor.IsEquivalence.mk
  · intro h
    refine ⟨fun c₀ d₀ p q Ψ => ?_, fun d₀ c₀ G => ?_⟩
    · let c : AsBicat.{u, v, w} Obj := c₀
      let d : AsBicat.{u, v, w} Obj := d₀
      have := h.isEquivalence c d
      refine ⟨(BiDenseBridge.Φ A c d).preimage (BiDenseBridge.homOfCellFamily (c := c) (d := d) Ψ),
        fun x hx => ?_, ?_⟩
      · exact congr((($((BiDenseBridge.Φ A c d).map_preimage
          (BiDenseBridge.homOfCellFamily Ψ))).as.app
            (Opposite.op (BiDenseBridge.ob x hx))).toNatTrans)
      · intro β hβ
        apply (BiDenseBridge.Φ A c d).map_injective
        refine Eq.trans ?_ (Functor.map_preimage _ _).symm
        ext X k
        exact congr(NatTrans.app $(hβ X.unop.2) k)
    · let c : AsBicat.{u, v, w} Obj := c₀
      let d : AsBicat.{u, v, w} Obj := d₀
      have := h.isEquivalence d c
      obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := BiDenseBridge.Φ A d c)
        (BiDenseBridge.toStrongTrans (c := d) (d := c) G)
      exact ⟨BiDenseBridge.representationOfIso G g e⟩

end UlmerBialgebras.Paper
