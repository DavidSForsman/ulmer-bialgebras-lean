module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Maps between pushouts along a common first leg

For pushouts of a fixed `a : A ⟶ B` against varying `b : A ⟶ C`, a morphism `t : C ⟶ C'` with
`b ≫ t = b'` induces `pushout.desc (pushout.inl a b') (t ≫ pushout.inr a b')`. These maps are
functorial in `t`.

## Main results

* `CategoryTheory.Limits.pushout_condition_of_comp`: the compatibility needed to define the map.
* `CategoryTheory.Limits.pushout_desc_inl_id`: the map induced by the identity is the identity.
* `CategoryTheory.Limits.pushout_desc_inl_comp`: the map induced by a composite is the composite.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], III.3 (pushouts)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] {A B : D} (a : A ⟶ B)

/-- If `b ≫ t = b'`, then `a ≫ inl = b ≫ t ≫ inr` for the pushout of `a` and `b'`, so that
`inl` and `t ≫ inr` induce a map out of the pushout of `a` and `b`. -/
lemma pushout_condition_of_comp {C C' : D} (b : A ⟶ C) (b' : A ⟶ C') [HasPushout a b']
    (t : C ⟶ C') (h : b ≫ t = b') :
    a ≫ pushout.inl a b' = b ≫ t ≫ pushout.inr a b' := by
  rw [pushout.condition, ← Category.assoc, h]

/-- The map between pushouts along `a` induced by an identity is the identity. -/
lemma pushout_desc_inl_id {C : D} (b : A ⟶ C) [HasPushout a b] {t : C ⟶ C} (ht : t = 𝟙 C)
    (w : a ≫ pushout.inl a b = b ≫ t ≫ pushout.inr a b) :
    pushout.desc (pushout.inl a b) (t ≫ pushout.inr a b) w = 𝟙 _ := by
  subst ht
  apply pushout.hom_ext <;> simp

/-- The map between pushouts along `a` induced by a composite is the composite of the maps. -/
lemma pushout_desc_inl_comp {C₁ C₂ C₃ : D} (b₁ : A ⟶ C₁) (b₂ : A ⟶ C₂) (b₃ : A ⟶ C₃)
    [HasPushout a b₁] [HasPushout a b₂] [HasPushout a b₃] (t₁ : C₁ ⟶ C₂) (t₂ : C₂ ⟶ C₃)
    {t : C₁ ⟶ C₃} (ht : t = t₁ ≫ t₂)
    (w : a ≫ pushout.inl a b₃ = b₁ ≫ t ≫ pushout.inr a b₃)
    (w₁ : a ≫ pushout.inl a b₂ = b₁ ≫ t₁ ≫ pushout.inr a b₂)
    (w₂ : a ≫ pushout.inl a b₃ = b₂ ≫ t₂ ≫ pushout.inr a b₃) :
    pushout.desc (pushout.inl a b₃) (t ≫ pushout.inr a b₃) w =
      pushout.desc (pushout.inl a b₂) (t₁ ≫ pushout.inr a b₂) w₁ ≫
        pushout.desc (pushout.inl a b₃) (t₂ ≫ pushout.inr a b₃) w₂ := by
  subst ht
  apply pushout.hom_ext <;> simp

end CategoryTheory.Limits
