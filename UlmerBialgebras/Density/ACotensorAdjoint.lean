module

public import UlmerBialgebras.Density.CotensorHomEquiv
public import UlmerBialgebras.Density.ALeftAdjoint
public import UlmerBialgebras.Density.AComplete

/-!
# The synthetic adjoint functor theorem: cotensors produce a left adjoint in `K`

Let `K` be a strict 2-category and `A` a class of objects of `K`.  For a 1-cell
`g : d ⟶ c` the *representable* halves of the adjoint functor theorem are easy: if the
objects are `A`-complete and `g` is `A`-accessible and `A`-continuous, then each
`K(x, g) : K(x, d) ⥤ K(x, c)`, `x ∈ A`, has a left adjoint `L_x`
(by the adjoint functor theorem for locally presentable categories; in this file the `L_x`
are a hypothesis).  What is *not* automatic is that the family `(L_x)_{x ∈ A}` be
**pseudonatural**, which is what density needs in order to glue the `L_x` into a 1-cell of
`K`.

This file proves that the **cotensors** supply exactly that.  If `d` is `A`-cotensored (every
restriction functor `K(r, d)` has a right adjoint, `ACotensor.lean`) and `g` respects the
`A`-cotensors, then the mates

```
  L_x (r ≫ k) ⟶ r ≫ L_y k       (r : x ⟶ y in A)
```

are invertible. The proof follows the paper's four hom-set bijections: the right Kan
extension in `d`, the local adjunction at `y`, preservation by `g`, and the local adjunction
at `x`. `leftMateHomEquiv_apply` checks that their composite is precomposition with the
canonical oplax comparison, which is therefore invertible. Thus the family is pseudonatural:

* `UlmerBialgebras.leftMateApp` — the mate, with its characterisation through the units
  (`UlmerBialgebras.leftMateApp_unit`, `UlmerBialgebras.leftMateApp_uniq`);
* `UlmerBialgebras.isIso_leftMateApp` — the mate is invertible when `d` is `A`-cotensored and `g`
  respects the `A`-cotensors;
* `UlmerBialgebras.leftMateIso` — the resulting invertible comparisons.

The coherence of the mates (pseudonaturality of the family) is not proved here. It is the
coherence of the lax transformation that `laxNat_adjunction` lifts from the local adjunctions
(`UlmerBialgebras/Proofs/Sec5/ThmSevenFourRoute.lean`), which assembles the
`UlmerBialgebras.ALeftAdjointFamily`.

## Main results

* `UlmerBialgebras.leftMateApp`: the mate `L_x (r ≫ k) ⟶ r ≫ L_y k` of a family of left adjoints
  of the representables of `g`.
* `UlmerBialgebras.leftMateHomEquiv`: the composite of the four hom-set equivalences.
* `UlmerBialgebras.leftMateHomEquiv_apply`: the composite is precomposition with the mate.
* `UlmerBialgebras.isIso_leftMateApp`: if `d` is `A`-cotensored and `g` respects the `A`-cotensors,
  the mate is an isomorphism (the main step of the proof of Theorem 7.4).
* `UlmerBialgebras.leftMateIso`: under the same hypotheses, if every `K(x, g)`, `x ∈ A`, is a
  right adjoint, the comparisons of the chosen left adjoints are isomorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 7.4 and Corollary 7.5
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## The mate of a family of left adjoints -/

section Mate

variable {c d x y : Obj} {g : d ⟶ c} {r : x ⟶ y}
  {Lx : (x ⟶ c) ⥤ (x ⟶ d)} {Ly : (y ⟶ c) ⥤ (y ⟶ d)}

/-- The 2-cell `r ≫ k ⟶ (r ≫ L_y k) ≫ g` obtained from the unit of `L_y ⊣ K(y, g)`. -/
def leftMateAux (adjy : Ly ⊣ postcomp y g) (r : x ⟶ y) (k : y ⟶ c) :
    r ≫ k ⟶ (r ≫ Ly.obj k) ≫ g :=
  (r ◁ adjy.unit.app k) ≫ eqToHom (Category.assoc r (Ly.obj k) g).symm

/-- **The mate** of the identity square relating the restrictions along `r` with
post-composition by `g`: the comparison `L_x (r ≫ k) ⟶ r ≫ L_y k`. -/
noncomputable def leftMateApp (adjx : Lx ⊣ postcomp x g) (adjy : Ly ⊣ postcomp y g)
    (r : x ⟶ y) (k : y ⟶ c) : Lx.obj (r ≫ k) ⟶ r ≫ Ly.obj k :=
  (adjx.homEquiv (r ≫ k) (r ≫ Ly.obj k)).symm (leftMateAux adjy r k)

variable (adjx : Lx ⊣ postcomp x g) (adjy : Ly ⊣ postcomp y g)

/-- The defining property of the mate: it is the 2-cell whose adjunct is the unit of the
family at `y`, restricted along `r`. -/
lemma leftMateApp_unit (k : y ⟶ c) :
    adjx.unit.app (r ≫ k) ≫ (leftMateApp adjx adjy r k ▷ g) = leftMateAux adjy r k := by
  have h := (adjx.homEquiv (r ≫ k) (r ≫ Ly.obj k)).apply_symm_apply (leftMateAux adjy r k)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The mate is the unique 2-cell with that property. -/
lemma leftMateApp_uniq (k : y ⟶ c) (σ : Lx.obj (r ≫ k) ⟶ r ≫ Ly.obj k)
    (hσ : adjx.unit.app (r ≫ k) ≫ (σ ▷ g) = leftMateAux adjy r k) :
    σ = leftMateApp adjx adjy r k := by
  refine (adjx.homEquiv (r ≫ k) (r ≫ Ly.obj k)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simpa only [postcomp_map] using hσ.trans (leftMateApp_unit adjx adjy k).symm

/-- The mates are natural in `k`. -/
lemma leftMateApp_naturality {k k' : y ⟶ c} (α : k ⟶ k') :
    Lx.map (r ◁ α) ≫ leftMateApp adjx adjy r k' = leftMateApp adjx adjy r k ≫ (r ◁ Ly.map α) := by
  have hnatx : adjx.unit.app (r ≫ k) ≫ (postcomp x g).map (Lx.map (r ◁ α))
      = (r ◁ α) ≫ adjx.unit.app (r ≫ k') := (adjx.unit.naturality (r ◁ α)).symm
  have hnaty : adjy.unit.app k ≫ (Ly.map α ▷ g) = α ≫ adjy.unit.app k' := by
    simpa only [Functor.id_map, Functor.comp_map, postcomp_map] using
      (adjy.unit.naturality α).symm
  have hR : adjx.unit.app (r ≫ k) ≫ ((leftMateApp adjx adjy r k ≫ (r ◁ Ly.map α)) ▷ g)
      = (r ◁ (adjy.unit.app k ≫ (Ly.map α ▷ g))) ≫ eqToHom (Category.assoc r (Ly.obj k') g).symm :=
        by
    rw [Bicategory.comp_whiskerRight, ← Category.assoc (obj := _ ⟶ _), leftMateApp_unit adjx adjy k,
        leftMateAux,
      Bicategory.Strict.whisker_assoc' r (Ly.map α) g, Bicategory.whiskerLeft_comp]
    simp
  have hL : adjx.unit.app (r ≫ k) ≫ ((Lx.map (r ◁ α) ≫ leftMateApp adjx adjy r k') ▷ g)
      = (r ◁ (α ≫ adjy.unit.app k')) ≫ eqToHom (Category.assoc r (Ly.obj k') g).symm := by
    rw [Bicategory.comp_whiskerRight, ← Category.assoc (obj := _ ⟶ _),
        ← postcomp_map x g (Lx.map (r ◁ α)), hnatx,
      ]
    simp only [Category.assoc, leftMateApp_unit adjx adjy k', leftMateAux,
      Bicategory.whiskerLeft_comp]
  refine (adjx.homEquiv (r ≫ k) (r ≫ Ly.obj k')).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [postcomp_map]
  rw [hL, hR, hnaty]

/-- The mates, as a natural transformation. -/
noncomputable def leftMate (adjx : Lx ⊣ postcomp x g) (adjy : Ly ⊣ postcomp y g)
    (r : x ⟶ y) : precomp r c ⋙ Lx ⟶ Ly ⋙ precomp r d where
  app k := leftMateApp adjx adjy r k
  naturality _ _ α := leftMateApp_naturality adjx adjy α

end Mate

/-! ## Invertibility of the mate -/

/-- The adjunct of `μ ≫ (r ◁ β) ≫ ε`, computed through the cotensor `ε`: this is the
calculation that turns the invertibility of the mate into the universal property of the
cotensors. -/
lemma leftMateApp_homEquiv {c d x y : Obj} {g : d ⟶ c} {r : x ⟶ y}
    {Lx : (x ⟶ c) ⥤ (x ⟶ d)} {Ly : (y ⟶ c) ⥤ (y ⟶ d)} (adjx : Lx ⊣ postcomp x g)
    (adjy : Ly ⊣ postcomp y g) (k : y ⟶ c) {n : x ⟶ d} {t : y ⟶ d} (ε : r ≫ t ⟶ n)
    (β : Ly.obj k ⟶ t) :
    adjx.homEquiv (r ≫ k) n (leftMateApp adjx adjy r k ≫ ((r ◁ β) ≫ ε))
      = (r ◁ (adjy.homEquiv k t β)) ≫ cotensorWhisker r ε g := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [postcomp_map, Bicategory.comp_whiskerRight]
  rw [← Category.assoc (obj := _ ⟶ _), ← Category.assoc (obj := _ ⟶ _),
      leftMateApp_unit adjx adjy k, leftMateAux,
    Bicategory.Strict.whisker_assoc' r β g, cotensorWhisker, Bicategory.whiskerLeft_comp]
  simp

/-- The four hom-set bijections in the proof of Theorem 7.4: right Kan extension in `d`,
the adjunction at `y`, preservation of the right Kan extension, and the adjunction at `x`.
They identify morphisms out of `r ≫ Ly(k)` with morphisms out of `Lx(r ≫ k)`. -/
noncomputable def leftMateHomEquiv {c d x y : Obj} {g : d ⟶ c} {r : x ⟶ y}
    {Lx : (x ⟶ c) ⥤ (x ⟶ d)} {Ly : (y ⟶ c) ⥤ (y ⟶ d)} (adjx : Lx ⊣ postcomp x g)
    (adjy : Ly ⊣ postcomp y g) (k : y ⟶ c) {n : x ⟶ d} {t : y ⟶ d} (ε : r ≫ t ⟶ n)
    (hε : IsCotensorUniv r ε) (hgε : IsCotensorUniv r (cotensorWhisker r ε g)) :
    (r ≫ Ly.obj k ⟶ n) ≃ (Lx.obj (r ≫ k) ⟶ n) :=
  ((hε.homEquiv (Ly.obj k)).trans (adjy.homEquiv k t)).trans
    ((hgε.homEquiv k).symm.trans (adjx.homEquiv (r ≫ k) n).symm)

/-- Following the hom-set bijections of Theorem 7.4 is precomposition with the canonical
oplax comparison. Thus the comparison, rather than just some isomorphism, is invertible. -/
lemma leftMateHomEquiv_apply {c d x y : Obj} {g : d ⟶ c} {r : x ⟶ y}
    {Lx : (x ⟶ c) ⥤ (x ⟶ d)} {Ly : (y ⟶ c) ⥤ (y ⟶ d)} (adjx : Lx ⊣ postcomp x g)
    (adjy : Ly ⊣ postcomp y g) (k : y ⟶ c) {n : x ⟶ d} {t : y ⟶ d} (ε : r ≫ t ⟶ n)
    (hε : IsCotensorUniv r ε) (hgε : IsCotensorUniv r (cotensorWhisker r ε g))
    (φ : r ≫ Ly.obj k ⟶ n) :
    leftMateHomEquiv adjx adjy k ε hε hgε φ = leftMateApp adjx adjy r k ≫ φ := by
  apply (adjx.homEquiv (r ≫ k) n).injective
  simp only [leftMateHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (r ◁ adjy.homEquiv k t (hε.lift φ)) ≫ cotensorWhisker r ε g = _
  have h := leftMateApp_homEquiv adjx adjy k ε (hε.lift φ)
  rw [hε.fac φ] at h
  exact h.symm

/-- **The canonical oplax comparison is invertible.** The paper's hom-set argument identifies
precomposition with it as a composite of four equivalences. -/
lemma isIso_leftMateApp {A : ObjectProperty Obj} {c d x y : Obj} {g : d ⟶ c} {r : x ⟶ y}
    {Lx : (x ⟶ c) ⥤ (x ⟶ d)} {Ly : (y ⟶ c) ⥤ (y ⟶ d)} (adjx : Lx ⊣ postcomp x g)
    (adjy : Ly ⊣ postcomp y g) (hx : A x) (hy : A y) (hd : IsACotensored A d)
    (hg : RespectsACotensors A g) (k : y ⟶ c) : IsIso (leftMateApp adjx adjy r k) := by
  refine isIso_of_coyoneda_map_bijective _ fun n => ?_
  obtain ⟨t, ε, hε⟩ := hd hx hy r n
  have hgε := hg hx hy r ε hε
  have he := (leftMateHomEquiv adjx adjy k ε hε hgε).bijective
  have hfun : ⇑(leftMateHomEquiv adjx adjy k ε hε hgε) =
      (fun φ => leftMateApp adjx adjy r k ≫ φ) :=
    funext (leftMateHomEquiv_apply adjx adjy k ε hε hgε)
  rw [hfun] at he
  exact he

/-! ## The compatible family of left adjoints -/

section Family

variable {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}

/-- The chosen left adjoint of the representable `K(x, g)`. -/
noncomputable def repLeftAdjoint (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)
    ⦃x : Obj⦄ (hx : A x) : (x ⟶ c) ⥤ (x ⟶ d) :=
  letI := hrep hx
  (postcomp x g).leftAdjoint

/-- The chosen adjunction `L_x ⊣ K(x, g)`. -/
noncomputable def repLeftAdjunction (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)
    ⦃x : Obj⦄ (hx : A x) : repLeftAdjoint hrep hx ⊣ postcomp x g :=
  letI := hrep hx
  Adjunction.ofIsRightAdjoint (postcomp x g)

/-- The pseudonaturality isomorphism of the family of left adjoints: the mate, invertible
because `d` is `A`-cotensored and `g` respects the `A`-cotensors. -/
noncomputable def leftMateIso (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)
    (hd : IsACotensored A d) (hg : RespectsACotensors A g) ⦃x y : Obj⦄ (hx : A x) (hy : A y)
    (r : x ⟶ y) :
    precomp r c ⋙ repLeftAdjoint hrep hx ≅ repLeftAdjoint hrep hy ⋙ precomp r d := by
  haveI : ∀ k, IsIso
      ((leftMate (repLeftAdjunction hrep hx) (repLeftAdjunction hrep hy) r).app k) :=
    fun k => isIso_leftMateApp _ _ hx hy hd hg k
  haveI := NatIso.isIso_of_isIso_app
    (leftMate (repLeftAdjunction hrep hx) (repLeftAdjunction hrep hy) r)
  exact asIso (leftMate (repLeftAdjunction hrep hx) (repLeftAdjunction hrep hy) r)

/-- The component at `k` of the forward map of `leftMateIso` is
`leftMateApp` of the chosen adjunctions at `r` and `k`. -/
@[simp] lemma leftMateIso_hom_app
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint) (hd : IsACotensored A d)
    (hg : RespectsACotensors A g) ⦃x y : Obj⦄ (hx : A x) (hy : A y) (r : x ⟶ y)
    (k : y ⟶ c) :
    (leftMateIso hrep hd hg hx hy r).hom.app k
      = leftMateApp (repLeftAdjunction hrep hx) (repLeftAdjunction hrep hy) r k := rfl

end Family

end UlmerBialgebras
