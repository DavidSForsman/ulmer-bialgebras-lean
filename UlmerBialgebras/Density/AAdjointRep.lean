module

public import UlmerBialgebras.Density.AAdjoint

/-!
# Representable adjunctions induced by an adjunction in `K`

`AAdjoint.lean` shows that a compatible family of right adjoints for the representables of a
1-cell `f`, together with density of `A`, produces a right adjoint for `f` in the 2-category
`K`.  This file records the first step of the converse:

* `UlmerBialgebras.TwoAdj.postcompAdj` — an adjunction `f ⊣ g` in `K` induces, for every object `x`,
  an adjunction `K(x, f) ⊣ K(x, g)` between the hom-categories.

That the induced family is a `UlmerBialgebras.ARightAdjointFamily`, and the resulting
characterisation of right adjoints in `K` for a dense class `A`, are not formalized in this file.

## Main results

* `UlmerBialgebras.TwoAdj.postcompAdj`: an adjunction `f ⊣ g` in `K` induces, for every object `x`,
  an adjunction `K(x, f) ⊣ K(x, g)` of post-composition functors.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 7.1 and Theorem 7.4
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace TwoAdj

variable {c d : Obj} {f : c ⟶ d} {g : d ⟶ c} (Adj : TwoAdj f g)

/-- Naturality of the unit `k ↦ k ◁ η` of the adjunction induced on the hom-categories out of
`x` (`postcompUnit`), up to the `eqToHom`s of the strict unit and associativity laws. -/
theorem postcompUnit_naturality (x : Obj) {k k' : x ⟶ c} (α : k ⟶ k') :
    α ≫ (eqToHom (Category.comp_id k').symm ≫ (k' ◁ Adj.unit') ≫
        eqToHom (Category.assoc k' f g).symm) =
      (eqToHom (Category.comp_id k).symm ≫ (k ◁ Adj.unit') ≫
        eqToHom (Category.assoc k f g).symm) ≫ (α ▷ f) ▷ g := by
  have hex := Eq.symm <| Bicategory.whisker_exchange α Adj.unit'
  rw [Bicategory.Strict.whiskerRight_id α, Bicategory.Strict.whiskerRight_comp α f g] at hex
  simp only [Category.assoc] at hex
  rw [eqToHom_comp_iff] at hex
  have h2 := hex =≫ eqToHom (Category.assoc k' f g).symm
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h2
  rw [Category.assoc (obj := _ ⟶ _), Category.assoc (obj := _ ⟶ _)]
  exact h2

/-- The unit of the adjunction induced on the hom-categories out of `x`. -/
@[simps]
def postcompUnit (x : Obj) : 𝟭 (x ⟶ c) ⟶ postcomp x f ⋙ postcomp x g where
  app k := eqToHom (Category.comp_id k).symm ≫ (k ◁ Adj.unit') ≫ eqToHom (Category.assoc k f g).symm
  -- `id` gives the proof the field's own statement as its type, so the fingerprints, which
  -- erase proofs but keep their types, are those of the inline proof it replaces
  naturality _ _ α := id (Adj.postcompUnit_naturality x α)

/-- Naturality of the counit `k ↦ k ◁ ε` of the adjunction induced on the hom-categories out
of `x` (`postcompCounit`), up to the `eqToHom`s of the strict unit and associativity laws. -/
theorem postcompCounit_naturality (x : Obj) {k k' : x ⟶ d} (α : k ⟶ k') :
    (α ▷ g) ▷ f ≫ (eqToHom (Category.assoc k' g f) ≫ (k' ◁ Adj.counit') ≫
        eqToHom (Category.comp_id k')) =
      (eqToHom (Category.assoc k g f) ≫ (k ◁ Adj.counit') ≫ eqToHom (Category.comp_id k)) ≫
        α := by
  have hex := Eq.symm <| Bicategory.whisker_exchange α Adj.counit'
  rw [Bicategory.Strict.whiskerRight_id α, Bicategory.Strict.whiskerRight_comp α g f] at hex
  simp only [Category.assoc] at hex
  rw [eqToHom_comp_iff] at hex
  have h2 := hex =≫ eqToHom (Category.comp_id k')
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h2
  rw [Category.assoc (obj := _ ⟶ _), Category.assoc (obj := _ ⟶ _)]
  exact h2

/-- The counit of the adjunction induced on the hom-categories out of `x`. -/
@[simps]
def postcompCounit (x : Obj) : postcomp x g ⋙ postcomp x f ⟶ 𝟭 (x ⟶ d) where
  app k := eqToHom (Category.assoc k g f) ≫ (k ◁ Adj.counit') ≫ eqToHom (Category.comp_id k)
  naturality _ _ α := id (Adj.postcompCounit_naturality x α)

/-- The left triangle identity of the adjunction `K(x, f) ⊣ K(x, g)` induced by `f ⊣ g`
(`postcompAdj`): for `k : x ⟶ c`, whiskering the unit at `k` by `f` and then applying the
counit at `k ≫ f` is the identity of `k ≫ f`. -/
theorem postcompAdj_left_triangle (x : Obj) (k : x ⟶ c) :
    (postcomp x f).map ((Adj.postcompUnit x).app k) ≫
        (Adj.postcompCounit x).app ((postcomp x f).obj k) = 𝟙 ((postcomp x f).obj k) := by
  have h := congr(eqToHom (show k ≫ f = k ≫ (𝟙 c ≫ f) by rw [Category.id_comp]) ≫
    (k ◁ $(Adj.left_triangle')) ≫
      eqToHom (show k ≫ (f ≫ 𝟙 d) = k ≫ f by rw [Category.comp_id]))
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc] at h
  rw [Bicategory.Strict.whisker_assoc k Adj.unit' f,
    Bicategory.Strict.comp_whiskerLeft' k f Adj.counit'] at h
  simp only [postcompUnit_app, postcompCounit_app, postcomp_map, postcomp_obj,
    Functor.comp_obj, Functor.id_obj, Bicategory.comp_whiskerRight,
      Bicategory.eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc] at h ⊢
  simpa only [Bicategory.Strict.associator_eqToIso,
    Bicategory.Strict.comp_whiskerLeft, Bicategory.Strict.whisker_assoc,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
        Category.comp_id] using h

/-- The right triangle identity of the adjunction `K(x, f) ⊣ K(x, g)` induced by `f ⊣ g`
(`postcompAdj`): for `k : x ⟶ d`, the unit at `k ≫ g` followed by the counit at `k` whiskered
by `g` is the identity of `k ≫ g`. -/
theorem postcompAdj_right_triangle (x : Obj) (k : x ⟶ d) :
    (Adj.postcompUnit x).app ((postcomp x g).obj k) ≫
        (postcomp x g).map ((Adj.postcompCounit x).app k) = 𝟙 ((postcomp x g).obj k) := by
  have h := congr(eqToHom (show k ≫ g = k ≫ (g ≫ 𝟙 c) by rw [Category.comp_id]) ≫
    (k ◁ $(Adj.right_triangle')) ≫
      eqToHom (show k ≫ (𝟙 d ≫ g) = k ≫ g by rw [Category.id_comp]))
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc] at h
  rw [Bicategory.Strict.comp_whiskerLeft' k g Adj.unit',
    Bicategory.Strict.whisker_assoc k Adj.counit' g] at h
  simp only [postcompUnit_app, postcompCounit_app, postcomp_map, postcomp_obj,
    Functor.comp_obj, Functor.id_obj, Bicategory.comp_whiskerRight,
      Bicategory.eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc] at h ⊢
  simpa only [Bicategory.Strict.associator_eqToIso,
    Bicategory.Strict.comp_whiskerLeft, Bicategory.Strict.whisker_assoc,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
        Category.comp_id] using h

/-- **A 2-adjunction is detected representably**: an adjunction `f ⊣ g` in a strict
2-category induces an adjunction `K(x, f) ⊣ K(x, g)` between the hom-categories out of any
object `x`. -/
def postcompAdj (x : Obj) : postcomp x f ⊣ postcomp x g where
  unit := Adj.postcompUnit x
  counit := Adj.postcompCounit x
  left_triangle_components k := id (Adj.postcompAdj_left_triangle x k)
  right_triangle_components k := id (Adj.postcompAdj_right_triangle x k)

section Rel

variable {c x : Obj} {l : x ⟶ c} {g : c ⟶ x} (A : TwoAdj l g) (f : c ⟶ x)

/-- The bijection `(p (f l) ⟶ q) ≃ (p f ⟶ q g)` on 2-cells induced by an adjunction `l ⊣ g`, for
1-cells `p, q : z ⟶ c` and `f : c ⟶ x`: it exhibits `f l` as an `f`-relative left adjoint of `g`
(the first case of Remark 3.2 of [forsman2026syntactic]). -/
def relEquiv {z : Obj} (p q : z ⟶ c) : (p ≫ (f ≫ l) ⟶ q) ≃ (p ≫ f ⟶ q ≫ g) where
  toFun γ := (A.postcompAdj z).homEquiv (p ≫ f) q (eqToHom (Category.assoc p f l) ≫ γ)
  invFun δ := eqToHom (Category.assoc p f l).symm ≫
    ((A.postcompAdj z).homEquiv (p ≫ f) q).symm δ
  left_inv γ := by simp
  right_inv δ := by
    show _ = δ
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact Equiv.apply_symm_apply _ _

/-- `relEquiv` is natural in the first variable. -/
lemma relEquiv_nat_left {z : Obj} {p p' q : z ⟶ c} (σ : p' ⟶ p) (γ : p ≫ (f ≫ l) ⟶ q) :
    A.relEquiv f p' q ((σ ▷ (f ≫ l)) ≫ γ) = (σ ▷ f) ≫ A.relEquiv f p q γ := by
  dsimp only [relEquiv, Equiv.coe_fn_mk]
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [Bicategory.Strict.whiskerRight_comp σ f l]
  simp

/-- `relEquiv` is natural in the second variable. -/
lemma relEquiv_nat_right {z : Obj} {p q q' : z ⟶ c} (γ : p ≫ (f ≫ l) ⟶ q) (τ : q ⟶ q') :
    A.relEquiv f p q' (γ ≫ τ) = A.relEquiv f p q γ ≫ (τ ▷ g) := by
  dsimp only [relEquiv, Equiv.coe_fn_mk]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

/-- `relEquiv` is natural in the object `z`. -/
lemma relEquiv_nat_z {z z' : Obj} (h : z' ⟶ z) {p q : z ⟶ c} (γ : p ≫ (f ≫ l) ⟶ q) :
    A.relEquiv f (h ≫ p) (h ≫ q) (eqToHom (Category.assoc h p (f ≫ l)) ≫ (h ◁ γ)) =
      eqToHom (Category.assoc h p f) ≫ (h ◁ A.relEquiv f p q γ) ≫
        eqToHom (Category.assoc h q g).symm := by
  dsimp only [relEquiv, Equiv.coe_fn_mk]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  dsimp only [TwoAdj.postcompAdj]
  simp only [TwoAdj.postcompUnit_app, postcomp_map, postcomp_obj, Functor.comp_obj,
    Functor.id_obj, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans_assoc]
  rw [Bicategory.whiskerLeft_congr' (Category.assoc h p f) A.unit',
    Bicategory.Strict.comp_whiskerLeft h (p ≫ f) A.unit',
    Bicategory.Strict.whisker_assoc' h γ g]
  simp

end Rel

end TwoAdj

namespace ARightAdjointFamily

variable {c d : Obj} {f : c ⟶ d} {g : d ⟶ c}

end ARightAdjointFamily

end UlmerBialgebras
