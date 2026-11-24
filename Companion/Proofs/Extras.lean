module

public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3
public import UlmerBialgebras.Proofs.Appendix.AppendixReverse
public import UlmerBialgebras.Proofs.Appendix.AppendixForest
public import UlmerBialgebras.Proofs.Appendix.AppendixLinear
public import UlmerBialgebras.Proofs.Appendix.AppendixLinearDensity

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Checked statements that are not numbered results of the paper

Proofs of the checked theorems that the paper uses without a number of their own:

* Section 2.2: the representables `K(x, -)` preserve and jointly reflect products, inserters and
  equifiers (`rep_preserves_prod`, …, `rep_reflects_equif`);
* Appendix A: the point, arrow and three-object probes (`appendix_unit_classification`,
  `appendix_arrow_classification`, `appendix_arrow_transformations`,
  `appendix_three_classification`), the fully faithful part of Theorem A.5
  (`appendix_local_density`) and two related density results (`appendix_tiny_biDense`,
  `appendix_small_biDense`).

## Main results

* `UlmerBialgebras.Paper.rep_preserves_prod`: the representable `K(x, -)` sends a product to a
  product (Section 2.2).
* `UlmerBialgebras.Paper.rep_reflects_prod`: the representables `K(x, -)` jointly reflect products.
* `UlmerBialgebras.Paper.rep_preserves_ins`: `K(x, -)` sends an inserter to an inserter.
* `UlmerBialgebras.Paper.rep_reflects_ins`: the representables `K(x, -)` jointly reflect inserters.
* `UlmerBialgebras.Paper.rep_preserves_equif`: `K(x, -)` sends an equifier to an equifier.
* `UlmerBialgebras.Paper.rep_reflects_equif`: the representables `K(x, -)` jointly reflect
  equifiers.
* `UlmerBialgebras.Paper.appendix_three_classification`: Lemma A.3 for a two-edge linear forest, the
  universal property of the three-object probe of Definition A.4.
* `UlmerBialgebras.Paper.appendix_local_density`: the fully faithful part of Theorem A.5.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2.2 and
  Appendix A
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
-/

namespace UlmerBialgebras.Paper

section Representables

universe u v w s

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Section 2.2** ([forsman2026syntactic]): the representable `K(x, -)` sends a product to a
product: the comparison `K(x, ∏ cᵢ) → ∏ K(x, cᵢ)` is an isomorphism of categories. -/
theorem rep_preserves_prod {ι : Type s} {c : ι → Obj} (P : Product c) (x : Obj) :
    Function.Bijective (P.homFunctor x).obj ∧ (P.homFunctor x).Full ∧
      (P.homFunctor x).Faithful := by
  refine ⟨⟨fun h h' e => ?_, fun k => ⟨P.lift k, funext fun i => P.lift_π k i⟩⟩,
    inferInstance, inferInstance⟩
  rw [← P.lift_uniq h, ← P.lift_uniq h']
  exact congr(P.lift $e)

/-- **Section 2.2** ([forsman2026syntactic]): the representables `K(x, -)` jointly reflect
products. -/
theorem rep_reflects_prod {ι : Type s} {c : ι → Obj} (pt : Obj) (π : ∀ i, pt ⟶ c i)
    (h : ∀ x : Obj, Function.Bijective (Product.candHomFunctor pt π x).obj ∧
      (Product.candHomFunctor pt π x).Full ∧ (Product.candHomFunctor pt π x).Faithful) :
    ∃ P : Product c, P.pt = pt ∧ HEq P.π π := by
  let P : Product c := {
    pt := pt
    π := π
    lift := fun {x} g => ((h x).1.2 g).choose
    lift_π := fun {x} g i => by
      have hg := ((h x).1.2 g).choose_spec
      exact funext_iff.1 hg i
    lift_uniq := fun {x} k => by
      apply (h x).1.1
      exact ((h x).1.2 (fun i => k ≫ π i)).choose_spec
    lift₂ := fun {x} {f g} α => by
      exact ((h x).2.1.map_surjective α).choose
    lift₂_π := fun {x} {f g} α i => by
      have hα := ((h x).2.1.map_surjective α).choose_spec
      exact funext_iff.1 hα i
    lift₂_uniq := fun {x} {f g} β => by
      have := (h x).2.2
      have hβ := ((h x).2.1.map_surjective (fun i => β ▷ π i)).choose_spec
      apply (Product.candHomFunctor pt π x).map_injective
      exact hβ
  }
  exact ⟨P, rfl, HEq.rfl⟩

/-- **Section 2.2** ([forsman2026syntactic]): the representable `K(x, -)` sends an inserter to an
inserter: the comparison `K(x, Ins(f, g)) → Ins(K(x, f), K(x, g))` is an isomorphism of
categories. -/
theorem rep_preserves_ins {a b : Obj} {f g : a ⟶ b} (I : Inserter f g) (x : Obj) :
    Function.Bijective (I.homFunctor x).obj ∧ (I.homFunctor x).Full ∧
      (I.homFunctor x).Faithful := by
  have hk : ∀ k : x ⟶ I.pt, k = I.lift (k ≫ I.u) (Inserter.homCell I x k) := fun k =>
    I.lift_uniq k (k ≫ I.u) (Inserter.homCell I x k) rfl (by simp [Inserter.homCell])
  refine ⟨⟨fun k k' e => ?_, fun y => ⟨I.lift y.pt y.cell, ?_⟩⟩, inferInstance, inferInstance⟩
  · have := congrArg (fun y : Ins (postcomp x f) (postcomp x g) => I.lift y.pt y.cell) e
    exact (hk k).trans (this.trans (hk k').symm)
  · refine Ins.obj_ext (I.lift_u y.pt y.cell) ?_
    change Inserter.homCell I x (I.lift y.pt y.cell) = _
    rw [Inserter.homCell, I.lift_φ y.pt y.cell]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    congr 1

/-- If the candidate comparison functor sends `k` to `⟨h, α⟩` (with `k ≫ u = h`), then `k ◁ φ`
is `α` up to the associativity identifications. -/
lemma candHomFunctor_obj_eq_whisker {a b : Obj} {f g : a ⟶ b} {pt : Obj} {u : pt ⟶ a}
    {φ : u ≫ f ⟶ u ≫ g} {x : Obj} {k : x ⟶ pt} {h : x ⟶ a} {α : h ≫ f ⟶ h ≫ g}
    (hk : (Inserter.candHomFunctor pt u φ x).obj k = ⟨h, α⟩) (hu : k ≫ u = h) :
    k ◁ φ = eqToHom (by rw [← Category.assoc, hu]) ≫ α ≫
      eqToHom (by rw [← Category.assoc, hu]) := by
  have hcell := ins_obj_eq hk
  dsimp [Inserter.candHomCell] at hcell
  have h_eq : k ◁ φ =
      eqToHom (Category.assoc k u f).symm ≫
      (eqToHom (Category.assoc k u f) ≫ k ◁ φ ≫ eqToHom (Category.assoc k u g).symm) ≫
      eqToHom (Category.assoc k u g) := by
    simp
  rw [h_eq, hcell]
  simp

/-- Conversely, if `k ≫ u = h` and `k ◁ φ` is `α` up to associativity, the candidate comparison
functor sends `k` to `⟨h, α⟩`. -/
lemma candHomFunctor_obj_eq_of_whisker {a b : Obj} {f g : a ⟶ b} {pt : Obj} {u : pt ⟶ a}
    {φ : u ≫ f ⟶ u ≫ g} {x : Obj} {k : x ⟶ pt} {h : x ⟶ a} {α : h ≫ f ⟶ h ≫ g}
    (hu : k ≫ u = h)
    (hφ : k ◁ φ = eqToHom (by rw [← Category.assoc, hu]) ≫ α ≫
      eqToHom (by rw [← Category.assoc, hu])) :
    (Inserter.candHomFunctor pt u φ x).obj k = ⟨h, α⟩ := by
  refine Ins.obj_ext hu ?_
  change eqToHom (Category.assoc k u f) ≫ (k ◁ φ) ≫ eqToHom (Category.assoc k u g).symm = _
  rw [hφ]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  congr 1

/-- The compatibility condition of the 2-dimensional universal property of an inserter, restated as
the condition for `α` to be a morphism of the inserter category `Ins(f ∘ -, g ∘ -)`. -/
lemma candHomCell_comp_map_eq {a b : Obj} {f g : a ⟶ b} {pt : Obj} {u : pt ⟶ a}
    {φ : u ≫ f ⟶ u ≫ g} {x : Obj} {k₁ k₂ : x ⟶ pt} (α : k₁ ≫ u ⟶ k₂ ≫ u)
    (hα : (eqToHom (Category.assoc k₁ u f) ≫ (k₁ ◁ φ) ≫ eqToHom (Category.assoc k₁ u g).symm) ≫
        (α ▷ g) = (α ▷ f) ≫ (eqToHom (Category.assoc k₂ u f) ≫ (k₂ ◁ φ) ≫
          eqToHom (Category.assoc k₂ u g).symm)) :
    Inserter.candHomCell u φ x k₁ ≫ (postcomp x g).map α
      = (postcomp x f).map α ≫ Inserter.candHomCell u φ x k₂ := by
  dsimp [Inserter.candHomCell, postcomp]
  exact hα

/-- **Section 2.2** ([forsman2026syntactic]): the representables `K(x, -)` jointly reflect
inserters. -/
theorem rep_reflects_ins {a b : Obj} {f g : a ⟶ b} (pt : Obj) (u : pt ⟶ a)
    (φ : u ≫ f ⟶ u ≫ g)
    (h : ∀ x : Obj, Function.Bijective (Inserter.candHomFunctor pt u φ x).obj ∧
      (Inserter.candHomFunctor pt u φ x).Full ∧ (Inserter.candHomFunctor pt u φ x).Faithful) :
    ∃ I : Inserter f g, I.pt = pt ∧ HEq I.u u ∧ HEq I.φ φ := by
  let liftObj {x : Obj} (h' : x ⟶ a) (α : h' ≫ f ⟶ h' ≫ g) : x ⟶ pt :=
    ((h x).1.2 ⟨h', α⟩).choose
  have liftObj_spec {x : Obj} (h' : x ⟶ a) (α : h' ≫ f ⟶ h' ≫ g) :
      (Inserter.candHomFunctor pt u φ x).obj (liftObj h' α) = ⟨h', α⟩ :=
    ((h x).1.2 ⟨h', α⟩).choose_spec
  have lift_u : ∀ {x : Obj} (h' : x ⟶ a) (α : h' ≫ f ⟶ h' ≫ g),
      liftObj h' α ≫ u = h' := fun h' α =>
    congr(($(liftObj_spec h' α)).pt)
  let I : Inserter f g := {
    pt := pt
    u := u
    φ := φ
    lift := liftObj
    lift_u := lift_u
    lift_φ := fun h' α => candHomFunctor_obj_eq_whisker (liftObj_spec h' α) (lift_u h' α)
    lift_uniq := fun {x} k h' α hu hφ =>
      (h x).1.1 ((candHomFunctor_obj_eq_of_whisker hu hφ).trans (liftObj_spec h' α).symm)
    lift₂ := fun {x} {_ _} α hα =>
      ((h x).2.1.map_surjective ⟨α, candHomCell_comp_map_eq α hα⟩).choose
    lift₂_u := fun {x} {_ _} α hα =>
      congr(($(Exists.choose_spec
        ((h x).2.1.map_surjective ⟨α, candHomCell_comp_map_eq α hα⟩))).base)
    lift₂_uniq := fun {x} {k₁ k₂} β γ hβγ => by
      have := (h x).2.2
      apply (Inserter.candHomFunctor pt u φ x).map_injective
      ext
      exact hβγ
  }
  exact ⟨I, rfl, HEq.rfl, HEq.rfl⟩

/-- **Section 2.2** ([forsman2026syntactic]): the representable `K(x, -)` sends an equifier to an
equifier. -/
theorem rep_preserves_equif {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    (x : Obj) :
    Function.Bijective (E.homFunctor x).obj ∧ (E.homFunctor x).Full ∧
      (E.homFunctor x).Faithful := by
  refine ⟨⟨fun k k' e => ?_, fun y => ⟨E.lift y.obj y.property,
    ObjectProperty.FullSubcategory.ext (E.lift_e y.obj y.property)⟩⟩, inferInstance, inferInstance⟩
  have h1 : k ≫ E.e = k' ≫ E.e := congr(($e).obj)
  have H : (k' ≫ E.e) ◁ η = (k' ≫ E.e) ◁ θ := Equifier.homProp E x k'
  exact (E.lift_uniq k _ H h1).trans (E.lift_uniq k' _ H rfl).symm

/-- **Section 2.2** ([forsman2026syntactic]): the representables `K(x, -)` jointly reflect
equifiers. -/
theorem rep_reflects_equif {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (pt : Obj) (e : pt ⟶ a)
    (hcond : e ◁ η = e ◁ θ)
    (h : ∀ x : Obj, Function.Bijective (Equifier.candHomFunctor pt e hcond x).obj ∧
      (Equifier.candHomFunctor pt e hcond x).Full ∧ (Equifier.candHomFunctor pt e hcond x).Faithful)
          :
    ∃ E : Equifier η θ, E.pt = pt ∧ HEq E.e e := by
  let E : Equifier η θ := {
    pt := pt
    e := e
    cond := hcond
    lift := fun {x} h' H => ((h x).1.2 ⟨h', H⟩).choose
    lift_e := fun {x} h' H => by
      have hobj := ((h x).1.2 ⟨h', H⟩).choose_spec
      exact congr(($hobj).obj)
    lift_uniq := fun {x} k h' H hk => by
      apply (h x).1.1
      have hobj := ((h x).1.2 ⟨h', H⟩).choose_spec
      rw [hobj]
      exact ObjectProperty.FullSubcategory.ext hk
    full := fun {x} {k₁ k₂} β => by
      let mor : (Equifier.candHomFunctor pt e hcond x).obj k₁ ⟶
                (Equifier.candHomFunctor pt e hcond x).obj k₂ := ObjectProperty.homMk β
      obtain ⟨α, hα⟩ := (h x).2.1.map_surjective mor
      refine ⟨α, ?_⟩
      have := (Equif.forget (postcompNat x η) (postcompNat x θ)).congr_map hα
      exact this
    faithful := fun {x} {k₁ k₂} α β hαβ => by
      have := (h x).2.2
      apply (Equifier.candHomFunctor pt e hcond x).map_injective
      ext
      exact hαβ
  }
  exact ⟨E, rfl, HEq.rfl⟩

end Representables

section Appendix

universe w v u

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Definition A.4** ([forsman2026syntactic]), point probe: enriched functors out of `1` classify
objects. -/
theorem appendix_unit_classification (C : VCat.{w, v, u} V) :
    (unitVCatEval C).IsEquivalence ∧ Function.Bijective (unitVCatEval C).obj := by
  exact ⟨inferInstance, (Appendix.unitFunctorDataEquiv C).bijective⟩

/-- Transformations from the arrow probe are exactly the two endpoint components
satisfying one enriched naturality square. -/
theorem appendix_arrow_transformations (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) (F G : arrowVCat.{w, v, u} Z x ⟶ C) :
    Function.Bijective (fun α : F ⟶ G =>
      (⟨(α.app .src, α.app .tgt), α.vnaturality .src .tgt⟩ :
        { p : (F.obj .src ⟶ G.obj .src) × (F.obj .tgt ⟶ G.obj .tgt) //
          F.emap .src .tgt ≫ eHomWhiskerLeft V (F.obj .src) p.2 =
            G.emap .src .tgt ≫ eHomWhiskerRight V p.1 (G.obj .tgt) })) := by
  exact (Appendix.arrowTransformationEquiv Z x C F G).bijective

/-- Related density result (auxiliary, not a result of the paper): all enriched categories
with at most three objects are bi-dense. This is a larger class than the linear probes in A.5. -/
theorem appendix_tiny_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := VCat.{w, v, max u w} V) (IsTinyVCat.{w, v, u} (V := V)) := by
  have h := isADense_isTinyVCat.{w, v, u} Z
  refine ⟨h.cell, ?_⟩
  intro D C G
  exact h.hom G.toAHomFamily

/-- Related density result (auxiliary, not a result of the paper): small enriched categories
are bi-dense. -/
theorem appendix_small_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := VCat.{w, v, max u w} V) (IsSmallVCat.{w, v, u} V) := by
  have h := isADense_isSmallVCat.{w, v, u} Z
  refine ⟨h.cell, ?_⟩
  intro D C G
  exact h.hom G.toAHomFamily

end Appendix

end UlmerBialgebras.Paper
