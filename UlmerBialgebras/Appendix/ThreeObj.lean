module

public import UlmerBialgebras.Appendix.VCatTinyDense

/-!
# The carrier of the linear three-object enriched category

The `V`-category structure on three objects `0, 1, 2` with hom-objects `I`, `x`, `y`, `x ⊗ y` and
an initial object for the backward pairs, and the hom-maps of a `V`-functor out of it. The
`V`-category `threeVCat` and the `V`-functor `threeVFunctor` of Definition A.4 and Lemma A.3 are
defined in `UlmerBialgebras/Paper/AppendixDefsThree.lean` from these; the laws are proved here.

Composition follows the library convention `Hom(0,1) ⊗ Hom(1,2) → Hom(0,2)`.

## Main definitions

* `UlmerBialgebras.Paper.Appendix.ThreeObj`: the three objects, with their `EnrichedCategory`
  instance (`ThreeObj.hom`, `ThreeObj.eid`, `ThreeObj.ecomp`).
* `UlmerBialgebras.Paper.Appendix.threeObjMap`, `UlmerBialgebras.Paper.Appendix.threeEmap`: the
  object and hom-maps of the `V`-functor determined by `f : x → C(c₀,c₁)` and `g : y → C(c₁,c₂)`,
  with `threeEmap_id` and `threeEmap_comp`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma A.3, Definition A.4 (the linear `V`-category `𝟑_{x,y}`)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The three vertices of a labelled linear graph. -/
inductive ThreeObj (Z : MonoidalInitial V) (x y : V) : Type u where
  | zero | one | two

namespace ThreeObj

variable (Z : MonoidalInitial V) (x y : V)

/-- Hom-objects of `𝟑_{x,y}`: `I` on the diagonal, `x` for `0 → 1`, `y` for `1 → 2`,
`x ⊗ y` for `0 → 2`, and the initial object `Z.zero` for the backward pairs. -/
def hom : ThreeObj.{w, v, u} Z x y → ThreeObj.{w, v, u} Z x y → V
  | .zero, .zero => 𝟙_ V
  | .zero, .one => x
  | .zero, .two => x ⊗ y
  | .one, .zero => Z.zero
  | .one, .one => 𝟙_ V
  | .one, .two => y
  | .two, .zero => Z.zero
  | .two, .one => Z.zero
  | .two, .two => 𝟙_ V

/-- Identities of `𝟑_{x,y}`: the identity of `I` at each object. -/
def eid : ∀ a : ThreeObj.{w, v, u} Z x y, 𝟙_ V ⟶ hom Z x y a a
  | .zero => 𝟙 _
  | .one => 𝟙 _
  | .two => 𝟙 _

/-- Composition `Hom(a,b) ⊗ Hom(b,c) → Hom(a,c)` of `𝟑_{x,y}`: unitors where one factor is
`I`, the identity `x ⊗ y → x ⊗ y` for `0 → 1 → 2`, and the unique map out of an initial tensor
otherwise. -/
def ecomp : ∀ a b c : ThreeObj.{w, v, u} Z x y,
    hom Z x y a b ⊗ hom Z x y b c ⟶ hom Z x y a c
  | .zero, .zero, .zero => (λ_ (𝟙_ V)).hom
  | .zero, .zero, .one => (λ_ x).hom
  | .zero, .zero, .two => (λ_ (x ⊗ y)).hom
  | .zero, .one, .one => (ρ_ x).hom
  | .zero, .one, .two => 𝟙 _
  | .zero, .two, .two => (ρ_ (x ⊗ y)).hom
  | .one, .one, .one => (λ_ (𝟙_ V)).hom
  | .one, .one, .two => (λ_ y).hom
  | .one, .two, .two => (ρ_ y).hom
  | .two, .two, .two => (λ_ (𝟙_ V)).hom
  | .one, .zero, _ => (Z.zeroTensor _).to _
  | .two, .zero, _ => (Z.zeroTensor _).to _
  | .two, .one, _ => (Z.zeroTensor _).to _
  | _, .one, .zero => (Z.tensorZero _).to _
  | _, .two, .zero => (Z.tensorZero _).to _
  | _, .two, .one => (Z.tensorZero _).to _

/-- The left unit law of `ecomp Z x y`: the `V`-category axiom `id_comp`. -/
theorem ecomp_id_comp (a b : ThreeObj.{w, v, u} Z x y) :
    (λ_ (hom Z x y a b)).inv ≫ eid Z x y a ▷ hom Z x y a b ≫ ecomp Z x y a a b = 𝟙 _ := by
  cases a <;> cases b <;>
    first
      | exact Z.isInitial.hom_ext _ _
      | (show (λ_ _).inv ≫ _ ≫ _ = _; simp [eid, ecomp, hom])

/-- The right unit law of `ecomp Z x y`: the `V`-category axiom `comp_id`. -/
theorem ecomp_comp_id (a b : ThreeObj.{w, v, u} Z x y) :
    (ρ_ (hom Z x y a b)).inv ≫ hom Z x y a b ◁ eid Z x y b ≫ ecomp Z x y a b b = 𝟙 _ := by
  cases a <;> cases b <;>
    first
      | exact Z.isInitial.hom_ext _ _
      | (show (ρ_ _).inv ≫ _ ≫ _ = _; simp [eid, ecomp, hom, unitors_equal])

/-- The associativity of `ecomp Z x y`: the `V`-category axiom `assoc`. -/
theorem ecomp_assoc (a b c d : ThreeObj.{w, v, u} Z x y) :
    (α_ (hom Z x y a b) (hom Z x y b c) (hom Z x y c d)).inv ≫ ecomp Z x y a b c ▷ hom Z x y c d ≫
        ecomp Z x y a c d =
      hom Z x y a b ◁ ecomp Z x y b c d ≫ ecomp Z x y a b d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
      | exact (Z.zeroTensor _).hom_ext _ _
      | exact (Z.tensorLeftInitial _ (Z.zeroTensor _)).hom_ext _ _
      | exact (Z.tensorLeftInitial _ (Z.tensorZero _)).hom_ext _ _
      | (show (α_ _ _ _).inv ≫ _ ≫ _ = _ ≫ _;
          simp only [hom, ecomp, whiskerRight_id, Category.assoc, id_whiskerLeft, Iso.hom_inv_id,
            Category.comp_id, leftUnitor_whiskerRight, Iso.inv_hom_id_assoc, whiskerRight_tensor,
            comp_whiskerRight, pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id,
            whiskerLeft_rightUnitor, whiskerLeft_id, Category.id_comp, triangle_assoc_comp_right,
            tensor_whiskerLeft]; first | done | monoidal)

/-- The `V`-category structure on `ThreeObj Z x y` given by `hom`, `eid` and `ecomp`. -/
instance : EnrichedCategory V (ThreeObj.{w, v, u} Z x y) where
  Hom := hom Z x y
  id := eid Z x y
  comp := ecomp Z x y
  id_comp := ecomp_id_comp Z x y
  comp_id := ecomp_comp_id Z x y
  assoc := ecomp_assoc Z x y

end ThreeObj

section Functor

variable (Z : MonoidalInitial V) (x y : V)
    {C : Type u} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The object map `0 ↦ c₀`, `1 ↦ c₁`, `2 ↦ c₂` of a `V`-functor out of `𝟑_{x,y}`. -/
def threeObjMap (c₀ c₁ c₂ : C) : ThreeObj.{w, v, u} Z x y → C
  | .zero => c₀
  | .one => c₁
  | .two => c₂

/-- The hom-maps of the `V`-functor out of `𝟑_{x,y}` determined by `f : x → C(c₀,c₁)` and
`g : y → C(c₁,c₂)`: `f`, `g`, their composite `(f ⊗ g) ≫ comp` on `x ⊗ y`, identities on the
diagonal, and the maps out of `Z.zero` on the backward pairs. -/
def threeEmap (c₀ c₁ c₂ : C) (f : x ⟶ (c₀ ⟶[V] c₁)) (g : y ⟶ (c₁ ⟶[V] c₂)) :
    ∀ a b : ThreeObj.{w, v, u} Z x y,
      (a ⟶[V] b) ⟶ (threeObjMap Z x y c₀ c₁ c₂ a ⟶[V] threeObjMap Z x y c₀ c₁ c₂ b)
  | .zero, .zero => eId V c₀
  | .zero, .one => f
  | .zero, .two => (f ⊗ₘ g) ≫ eComp V c₀ c₁ c₂
  | .one, .zero => Z.isInitial.to _
  | .one, .one => eId V c₁
  | .one, .two => g
  | .two, .zero => Z.isInitial.to _
  | .two, .one => Z.isInitial.to _
  | .two, .two => eId V c₂

/-- The hom-maps `threeEmap` preserve the enriched identities. -/
lemma threeEmap_id (c₀ c₁ c₂ : C) (f : x ⟶ (c₀ ⟶[V] c₁)) (g : y ⟶ (c₁ ⟶[V] c₂)) :
    ∀ X : ThreeObj.{w, v, u} Z x y,
      eId V X ≫ threeEmap Z x y c₀ c₁ c₂ f g X X = eId V (threeObjMap Z x y c₀ c₁ c₂ X) := by
  rintro (_ | _ | _) <;> exact Category.id_comp _

/-- The hom-maps `threeEmap` preserve the enriched composition. -/
lemma threeEmap_comp (c₀ c₁ c₂ : C) (f : x ⟶ (c₀ ⟶[V] c₁)) (g : y ⟶ (c₁ ⟶[V] c₂)) :
    ∀ X Y W : ThreeObj.{w, v, u} Z x y,
      eComp V X Y W ≫ threeEmap Z x y c₀ c₁ c₂ f g X W =
        (threeEmap Z x y c₀ c₁ c₂ f g X Y ⊗ₘ threeEmap Z x y c₀ c₁ c₂ f g Y W) ≫
          eComp V (threeObjMap Z x y c₀ c₁ c₂ X) (threeObjMap Z x y c₀ c₁ c₂ Y)
            (threeObjMap Z x y c₀ c₁ c₂ W) := by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    first
      | exact leftUnitor_comp_eId _
      | exact rightUnitor_comp_eId _
      | exact (Z.zeroTensor _).hom_ext _ _
      | exact (Z.tensorZero _).hom_ext _ _
      | exact Category.id_comp _

end Functor

end UlmerBialgebras.Paper.Appendix
