module

public import UlmerBialgebras.Density.ATensor
public import UlmerBialgebras.Density.AAdjoint
public import UlmerBialgebras.Density.ALocPres

/-!
# The synthetic adjoint functor theorem: tensors produce a right adjoint in `K`

This file is the exact dual of `ACotensorAdjoint.lean`.  Let `K` be a strict 2-category and
`A` a class of objects of `K`.  For a 1-cell `f : c ⟶ d` the *representable* halves of the
adjoint functor theorem are easy: if `c` is `A`-locally presentable and `f` is
`A`-cocontinuous, then each `K(x, f) : K(x, c) ⥤ K(x, d)`, `x ∈ A`, has a right adjoint
`R_x` (by the adjoint functor theorem for locally presentable categories; in this file the
`R_x` are a hypothesis).  What is *not* automatic is that the family `(R_x)_{x ∈ A}` be
**pseudonatural**, which is what density needs in order to glue the `R_x` into a 1-cell
of `K`.

This file proves that the **tensors** supply exactly that.  If `c` is `A`-tensored (every
restriction functor `K(r, c)` has a left adjoint, `ATensor.lean`) and `f` respects the
`A`-tensors, then the mates

```
  r ≫ R_y k ⟶ R_x (r ≫ k)       (r : x ⟶ y in A)
```

are invertible and the family is pseudonatural:

* `UlmerBialgebras.rightMateApp` — the mate, with its characterisation through the counits
  (`UlmerBialgebras.rightMateApp_counit`, `UlmerBialgebras.rightMateApp_uniq`);
* `UlmerBialgebras.isIso_rightMateApp` — the mate is invertible when `c` is `A`-tensored and `f`
  respects the `A`-tensors;
* `UlmerBialgebras.aRightAdjointFamilyOfTensors` — the resulting compatible family of right
  adjoints (`UlmerBialgebras.ARightAdjointFamily`), the input of the `A`-accessible adjoint functor
  theorem of `AAdjoint.lean`.

## Main results

* `UlmerBialgebras.rightMateApp`: the mate `r ≫ R_y k ⟶ R_x (r ≫ k)` of a family of right adjoints
  of the representables of `f`.
* `UlmerBialgebras.isIso_rightMateApp`: if `c` is `A`-tensored and `f` respects the `A`-tensors, the
  mate is an isomorphism (the dual of the main step of the proof of Theorem 7.4).
* `UlmerBialgebras.aRightAdjointFamilyOfTensors`: under the same hypotheses, if every
  `K(x, f)`, `x ∈ A`, is a left adjoint, the right adjoints form an
  `UlmerBialgebras.ARightAdjointFamily`.

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

/-! ## The mate of a family of right adjoints -/

section Mate

variable {c d x y : Obj} {f : c ⟶ d} {r : x ⟶ y}
  {Rx : (x ⟶ d) ⥤ (x ⟶ c)} {Ry : (y ⟶ d) ⥤ (y ⟶ c)}

/-- The 2-cell `(r ≫ R_y k) ≫ f ⟶ r ≫ k` obtained from the counit of `K(y, f) ⊣ R_y`. -/
def rightMateAux (adjy : postcomp y f ⊣ Ry) (r : x ⟶ y) (k : y ⟶ d) :
    (r ≫ Ry.obj k) ≫ f ⟶ r ≫ k :=
  eqToHom (Category.assoc r (Ry.obj k) f) ≫ (r ◁ adjy.counit.app k)

/-- **The mate** of the identity square relating the restrictions along `r` with
post-composition by `f`: the comparison `r ≫ R_y k ⟶ R_x (r ≫ k)`. -/
noncomputable def rightMateApp (adjx : postcomp x f ⊣ Rx) (adjy : postcomp y f ⊣ Ry)
    (r : x ⟶ y) (k : y ⟶ d) : r ≫ Ry.obj k ⟶ Rx.obj (r ≫ k) :=
  adjx.homEquiv (r ≫ Ry.obj k) (r ≫ k) (rightMateAux adjy r k)

variable (adjx : postcomp x f ⊣ Rx) (adjy : postcomp y f ⊣ Ry)

/-- The defining property of the mate: its adjunct is the counit of the family at `y`,
restricted along `r`. -/
lemma rightMateApp_counit (k : y ⟶ d) :
    (rightMateApp adjx adjy r k ▷ f) ≫ adjx.counit.app (r ≫ k) = rightMateAux adjy r k := by
  have h := (adjx.homEquiv (r ≫ Ry.obj k) (r ≫ k)).symm_apply_apply
    (rightMateAux adjy r k)
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- The mate is the unique 2-cell with that property. -/
lemma rightMateApp_uniq (k : y ⟶ d) (σ : r ≫ Ry.obj k ⟶ Rx.obj (r ≫ k))
    (hσ : (σ ▷ f) ≫ adjx.counit.app (r ≫ k) = rightMateAux adjy r k) :
    σ = rightMateApp adjx adjy r k := by
  refine (adjx.homEquiv (r ≫ Ry.obj k) (r ≫ k)).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simpa only [postcomp_map] using hσ.trans (rightMateApp_counit adjx adjy k).symm

/-- Naturality of the counit of a representable adjunction, written with whiskering. -/
lemma counit_naturality_whisker {a : Obj} {Ra : (a ⟶ d) ⥤ (a ⟶ c)}
    (adja : postcomp a f ⊣ Ra) {k k' : a ⟶ d} (α : k ⟶ k') :
    (Ra.map α ▷ f) ≫ adja.counit.app k' = adja.counit.app k ≫ α := by
  simpa only [Functor.comp_map, Functor.id_map, postcomp_map] using adja.counit.naturality α

/-- The mates are natural in `k`. -/
lemma rightMateApp_naturality {k k' : y ⟶ d} (α : k ⟶ k') :
    (r ◁ Ry.map α) ≫ rightMateApp adjx adjy r k'
      = rightMateApp adjx adjy r k ≫ Rx.map (r ◁ α) := by
  refine (adjx.homEquiv (r ≫ Ry.obj k) (r ≫ k')).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [postcomp_map, Bicategory.comp_whiskerRight, Category.assoc]
  rw [rightMateApp_counit adjx adjy k', counit_naturality_whisker adjx (r ◁ α),
    ← Category.assoc, rightMateApp_counit adjx adjy k, rightMateAux, rightMateAux,
    Bicategory.Strict.whisker_assoc' r (Ry.map α) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Bicategory.whiskerLeft_comp, counit_naturality_whisker adjy α, Bicategory.whiskerLeft_comp]

end Mate

/-! ## The unit and cocycle coherence of the mates -/

section Coherence

variable {c d x y z : Obj} {f : c ⟶ d}
  {Rx : (x ⟶ d) ⥤ (x ⟶ c)} {Ry : (y ⟶ d) ⥤ (y ⟶ c)} {Rz : (z ⟶ d) ⥤ (z ⟶ c)}

/-- The mate along an identity 1-cell is the canonical isomorphism. -/
lemma rightMateApp_id (adjx : postcomp x f ⊣ Rx) (k : x ⟶ d) :
    rightMateApp adjx adjx (𝟙 x) k = eqToHom (by simp only [Category.id_comp]) := by
  refine (rightMateApp_uniq adjx adjx k _ ?_).symm
  have hnat : (eqToHom (congrArg Rx.obj (Category.id_comp k).symm) ▷ f) ≫
        adjx.counit.app (𝟙 x ≫ k)
      = adjx.counit.app k ≫ eqToHom (Category.id_comp k).symm := by
    simpa only [eqToHom_map] using
      counit_naturality_whisker adjx (eqToHom (Category.id_comp k).symm)
  simp only [rightMateAux, Bicategory.Strict.id_whiskerLeft,
    show (eqToHom (by simp only [Category.id_comp]) : 𝟙 x ≫ Rx.obj k ⟶ Rx.obj (𝟙 x ≫ k))
      = eqToHom (Category.id_comp (Rx.obj k)) ≫ eqToHom (congrArg Rx.obj (Category.id_comp k).symm)
        from
      (eqToHom_trans _ _).symm,
    Bicategory.comp_whiskerRight, Category.assoc, hnat]
  simp

/-- The mates compose. -/
lemma rightMateApp_comp (adjx : postcomp x f ⊣ Rx) (adjy : postcomp y f ⊣ Ry)
    (adjz : postcomp z f ⊣ Rz) (u : x ⟶ y) (v : y ⟶ z) (k : z ⟶ d) :
    rightMateApp adjx adjz (u ≫ v) k
      = eqToHom (Category.assoc u v (Rz.obj k)) ≫ (u ◁ rightMateApp adjy adjz v k) ≫
          rightMateApp adjx adjy u (v ≫ k) ≫ eqToHom (by simp only [Category.assoc]) := by
  refine (rightMateApp_uniq adjx adjz k _ ?_).symm
  have hnat : (eqToHom (congrArg Rx.obj (Category.assoc u v k).symm) ▷ f) ≫
        adjx.counit.app ((u ≫ v) ≫ k)
      = adjx.counit.app (u ≫ (v ≫ k)) ≫ eqToHom (Category.assoc u v k).symm := by
    simpa only [eqToHom_map] using
      counit_naturality_whisker adjx (eqToHom (Category.assoc u v k).symm)
  simp only [Bicategory.comp_whiskerRight, Category.assoc]
  rw [hnat, ← Category.assoc (rightMateApp adjx adjy u (v ≫ k) ▷ f),
    rightMateApp_counit adjx adjy (v ≫ k), rightMateAux, rightMateAux,
    Bicategory.Strict.whisker_assoc' u (rightMateApp adjy adjz v k) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (u ◁ (rightMateApp adjy adjz v k ▷ f)), ← Bicategory.whiskerLeft_comp,
    rightMateApp_counit adjy adjz k, rightMateAux, Bicategory.whiskerLeft_comp,
    Bicategory.Strict.comp_whiskerLeft' u v (adjz.counit.app k)]
  simp

end Coherence

/-! ## Invertibility of the mate -/

/-- The adjunct of `(η ≫ (r ◁ β)) ≫ μ`, computed through the tensor `η`: this is the
calculation that turns the invertibility of the mate into the universal property of the
tensors. -/
lemma rightMateApp_counit_comp {c d x y : Obj} {f : c ⟶ d} {r : x ⟶ y}
    {Rx : (x ⟶ d) ⥤ (x ⟶ c)} {Ry : (y ⟶ d) ⥤ (y ⟶ c)} (adjx : postcomp x f ⊣ Rx)
    (adjy : postcomp y f ⊣ Ry) (k : y ⟶ d) {n : x ⟶ c} {t : y ⟶ c} (η : n ⟶ r ≫ t)
    (β : t ⟶ Ry.obj k) :
    (((η ≫ (r ◁ β)) ≫ rightMateApp adjx adjy r k) ▷ f) ≫ adjx.counit.app (r ≫ k)
      = tensorWhisker r η f ≫ (r ◁ ((β ▷ f) ≫ adjy.counit.app k)) := by
  simp only [Bicategory.comp_whiskerRight, Category.assoc]
  rw [rightMateApp_counit adjx adjy k, rightMateAux, tensorWhisker,
    Bicategory.Strict.whisker_assoc' r β f, Bicategory.whiskerLeft_comp]
  simp

/-- **The tensors make the mate invertible.**  If `c` is `A`-tensored and `f` respects the
`A`-tensors, then the comparison `r ≫ R_y k ⟶ R_x (r ≫ k)` is an isomorphism. -/
lemma isIso_rightMateApp {A : ObjectProperty Obj} {c d x y : Obj} {f : c ⟶ d} {r : x ⟶ y}
    {Rx : (x ⟶ d) ⥤ (x ⟶ c)} {Ry : (y ⟶ d) ⥤ (y ⟶ c)} (adjx : postcomp x f ⊣ Rx)
    (adjy : postcomp y f ⊣ Ry) (hx : A x) (hy : A y) (hc : IsATensored A c)
    (hf : RespectsATensors A f) (k : y ⟶ d) : IsIso (rightMateApp adjx adjy r k) := by
  refine isIso_of_yoneda_map_bijective _ fun n => ?_
  obtain ⟨t, η, hη⟩ := hc hx hy r n
  have htw : IsTensorUniv r (tensorWhisker r η f) := hf hx hy r η hη
  constructor
  · intro φ₁ φ₂ h
    have hcomp : φ₁ ≫ rightMateApp adjx adjy r k = φ₂ ≫ rightMateApp adjx adjy r k := h
    have hfac : ∀ φ : n ⟶ r ≫ Ry.obj k, η ≫ (r ◁ hη.desc φ) = φ := fun φ => hη.fac φ
    have h' : (((η ≫ (r ◁ hη.desc φ₁)) ≫ rightMateApp adjx adjy r k) ▷ f) ≫
          adjx.counit.app (r ≫ k)
        = (((η ≫ (r ◁ hη.desc φ₂)) ≫ rightMateApp adjx adjy r k) ▷ f) ≫
          adjx.counit.app (r ≫ k) := by
      rw [hfac φ₁, hfac φ₂, hcomp]
    rw [rightMateApp_counit_comp adjx adjy k η, rightMateApp_counit_comp adjx adjy k η] at h'
    have hβ : hη.desc φ₁ = hη.desc φ₂ :=
      (adjy.homEquiv t k).symm.injective (by
        simpa only [Adjunction.homEquiv_counit, postcomp_map] using htw.hom_ext h')
    rw [← hfac φ₁, ← hfac φ₂, hβ]
  · intro ψ
    obtain ⟨γ, hγ, -⟩ := htw k ((adjx.homEquiv n (r ≫ k)).symm ψ)
    have hγ' : tensorWhisker r η f ≫ (r ◁ γ) = (ψ ▷ f) ≫ adjx.counit.app (r ≫ k) := by
      simpa only [Adjunction.homEquiv_counit, postcomp_map] using hγ
    have hβγ : (((adjy.homEquiv t k) γ) ▷ f) ≫ adjy.counit.app k = γ := by
      simpa only [Adjunction.homEquiv_counit, postcomp_map] using
        (adjy.homEquiv t k).symm_apply_apply γ
    refine ⟨η ≫ (r ◁ (adjy.homEquiv t k) γ), ?_⟩
    refine (adjx.homEquiv n (r ≫ k)).symm.injective ?_
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [postcomp_map]
    rw [rightMateApp_counit_comp adjx adjy k η, hβγ]
    exact hγ'

/-! ## The compatible family of right adjoints -/

section Family

/-- A two-sided-inverse argument: two right inverses of the same 2-cell agree. -/
private lemma eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} {nu : X ⟶ Y} {h g : Y ⟶ X}
    (h2 : h ≫ nu = 𝟙 Y) (h3 : nu ≫ g = 𝟙 X) : h = g := by
  calc h = h ≫ nu ≫ g := by rw [h3, Category.comp_id]
    _ = (h ≫ nu) ≫ g := (Category.assoc _ _ _).symm
    _ = g := by rw [h2, Category.id_comp]

variable {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}

/-- The chosen right adjoint of the representable `K(x, f)`. -/
noncomputable def repRightAdjoint (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint)
    ⦃x : Obj⦄ (hx : A x) : (x ⟶ d) ⥤ (x ⟶ c) :=
  letI := hrep hx
  (postcomp x f).rightAdjoint

/-- The chosen adjunction `K(x, f) ⊣ R_x`. -/
noncomputable def repRightAdjunction (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint)
    ⦃x : Obj⦄ (hx : A x) : postcomp x f ⊣ repRightAdjoint hrep hx :=
  letI := hrep hx
  Adjunction.ofIsLeftAdjoint (postcomp x f)

/-- The pseudonaturality isomorphism of the family of right adjoints: the inverse of the
mate, which is invertible because `c` is `A`-tensored and `f` respects the `A`-tensors. -/
noncomputable def rightMateIso (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint)
    (hc : IsATensored A c) (hf : RespectsATensors A f) ⦃x y : Obj⦄ (hx : A x) (hy : A y)
    (r : x ⟶ y) :
    precomp r d ⋙ repRightAdjoint hrep hx ≅ repRightAdjoint hrep hy ⋙ precomp r c := by
  haveI : ∀ k : y ⟶ d,
      IsIso (rightMateApp (repRightAdjunction hrep hx) (repRightAdjunction hrep hy) r k) :=
    fun k => isIso_rightMateApp _ _ hx hy hc hf k
  exact NatIso.ofComponents
    (fun k => (asIso (rightMateApp (repRightAdjunction hrep hx)
      (repRightAdjunction hrep hy) r k)).symm) (by
        intro k k' α
        simp only [Iso.symm_hom, asIso_inv, Functor.comp_map, precomp_map]
        rw [IsIso.eq_inv_comp, ← Category.assoc (obj := _ ⟶ _), IsIso.comp_inv_eq]
        exact (rightMateApp_naturality (repRightAdjunction hrep hx)
          (repRightAdjunction hrep hy) α).symm)

/-- The component at `k` of the inverse of `rightMateIso` is
`rightMateApp` of the chosen adjunctions at `r` and `k`. -/
@[simp] lemma rightMateIso_inv_app
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint) (hc : IsATensored A c)
    (hf : RespectsATensors A f) ⦃x y : Obj⦄ (hx : A x) (hy : A y) (r : x ⟶ y)
    (k : y ⟶ d) :
    (rightMateIso hrep hc hf hx hy r).inv.app k
      = rightMateApp (repRightAdjunction hrep hx) (repRightAdjunction hrep hy) r k := rfl

/-- The mate is inverse to the pseudonaturality isomorphism. -/
lemma rightMateApp_comp_rightMateIso_hom
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint) (hc : IsATensored A c)
    (hf : RespectsATensors A f) ⦃x y : Obj⦄ (hx : A x) (hy : A y) (r : x ⟶ y)
    (k : y ⟶ d) :
    rightMateApp (repRightAdjunction hrep hx) (repRightAdjunction hrep hy) r k ≫
        (rightMateIso hrep hc hf hx hy r).hom.app k = 𝟙 _ :=
  (rightMateIso hrep hc hf hx hy r).inv_hom_id_app k

/-- **The family of right adjoints of the representables of `f` is pseudonatural** when `c`
is `A`-tensored and `f` respects the `A`-tensors. -/
noncomputable def aRightAdjointFamilyOfTensors
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x f).IsLeftAdjoint) (hc : IsATensored A c)
    (hf : RespectsATensors A f) : ARightAdjointFamily A f where
  fn := repRightAdjoint hrep
  nat := fun _ _ hx hy r => rightMateIso hrep hc hf hx hy r
  nat_id := by
    intro x hx k
    refine eq_of_comp_eq_id ((rightMateIso hrep hc hf hx hx (𝟙 x)).hom_inv_id_app k) ?_
    rw [rightMateIso_inv_app, rightMateApp_id]
    simp
  nat_comp := by
    intro x y z hx hy hz u v k
    refine eq_of_comp_eq_id ((rightMateIso hrep hc hf hx hz (u ≫ v)).hom_inv_id_app k) ?_
    rw [rightMateIso_inv_app,
      rightMateApp_comp (repRightAdjunction hrep hx) (repRightAdjunction hrep hy)
        (repRightAdjunction hrep hz) u v k]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (rightMateApp (repRightAdjunction hrep hx)
        (repRightAdjunction hrep hy) u (v ≫ k)),
      rightMateApp_comp_rightMateIso_hom hrep hc hf hx hy u (v ≫ k), Category.id_comp,
      ← Category.assoc (u ◁ rightMateApp (repRightAdjunction hrep hy)
        (repRightAdjunction hrep hz) v k), ← Bicategory.whiskerLeft_comp,
      rightMateApp_comp_rightMateIso_hom hrep hc hf hy hz v k]
    simp
  adj := fun _ hx => repRightAdjunction hrep hx
  counit_nat := by
    intro x y hx hy u k
    rw [rightMateIso_inv_app]
    exact rightMateApp_counit (repRightAdjunction hrep hx) (repRightAdjunction hrep hy) k

end Family

end UlmerBialgebras
