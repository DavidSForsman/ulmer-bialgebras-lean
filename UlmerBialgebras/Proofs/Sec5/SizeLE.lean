module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Proofs.Sec5.ChainCofinality

/-!
# Consequences of `HasColimitsOfSizeLE κ`

Colimits of size at most an infinite `κ` include the colimits of `μ`-chains for `μ ≤ κ` and all
finite colimits.

## Main results

* `UlmerBialgebras.Paper.hasChainColimitsUpTo_of_sizeLE`: colimits of size at most `κ` give colimits
  of `μ`-chains for infinite `μ ≤ κ`.
* `UlmerBialgebras.Paper.hasChainColimitsLE_of_sizeLE`: colimits of size at most `κ` give colimits
  of nonempty well-ordered chains of cardinality at most `κ`.
* `UlmerBialgebras.Paper.hasFiniteColimits_of_sizeLE`: for infinite `κ`, a category with colimits of
  size at most `κ` has finite colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.7
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cardinal

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}}

/-- Colimits of size at most `κ` include the colimits of `μ`-chains for infinite `μ ≤ κ`. -/
theorem hasChainColimitsUpTo_of_sizeLE (hC : HasColimitsOfSizeLE κ C) :
    HasChainColimitsUpTo κ C := by
  intro μ hμ hμκ
  refine hC _ ?_
  have h1 : Cardinal.mk (Σ X Y : μ.ord.ToType, X ⟶ Y) ≤ Cardinal.mk (μ.ord.ToType × μ.ord.ToType) :=
    Cardinal.mk_le_of_injective (f := fun p => (p.1, p.2.1)) (by
      rintro ⟨a, b, f⟩ ⟨a', b', f'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Subsingleton.elim f f'])
  have h2 : Cardinal.mk (μ.ord.ToType × μ.ord.ToType) = μ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_toType, Cardinal.card_ord,
      Cardinal.mul_eq_self hμ]
  exact h1.trans (h2.le.trans hμκ)

/-- Colimits of size at most `κ` give colimits of all nonempty well-ordered chains of cardinality at
most `κ` (via `hasChainColimitsUpTo_of_sizeLE` and `hasChainColimitsLE_of_upTo`). -/
theorem hasChainColimitsLE_of_sizeLE (hC : HasColimitsOfSizeLE κ C) :
    UlmerBialgebras.HasChainColimitsLE κ C :=
  hasChainColimitsLE_of_upTo (hasChainColimitsUpTo_of_sizeLE hC)

/-- Colimits of size at most an infinite `κ` include the colimits of finite shapes. -/
theorem hasColimitsOfShape_of_sizeLE_of_fin (hκ : Cardinal.aleph0 ≤ κ)
    (hC : HasColimitsOfSizeLE κ C) (J : Type) [SmallCategory J] [FinCategory J] :
    HasColimitsOfShape J C := by
  have : HasColimitsOfShape (AsSmall.{w} J) C := by
    refine hC _ ?_
    refine le_trans (le_of_lt ?_) hκ
    have : Finite (AsSmall.{w} J) := Finite.of_equiv J
      { toFun := fun j => AsSmall.up.obj j
        invFun := fun j => AsSmall.down.obj j
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have : ∀ X Y : AsSmall.{w} J, Finite (X ⟶ Y) := fun X Y =>
      Finite.of_equiv (AsSmall.down.obj X ⟶ AsSmall.down.obj Y)
        { toFun := fun f => AsSmall.up.map f
          invFun := fun f => AsSmall.down.map f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    exact Cardinal.lt_aleph0_of_finite _
  exact hasColimitsOfShape_of_equivalence AsSmall.equiv.symm

/-- For infinite `κ`, a category with colimits of size at most `κ` has all finite colimits. -/
theorem hasFiniteColimits_of_sizeLE (hκ : Cardinal.aleph0 ≤ κ) (hC : HasColimitsOfSizeLE κ C) :
    HasFiniteColimits C :=
  ⟨fun J _ _ => hasColimitsOfShape_of_sizeLE_of_fin hκ hC J⟩

end UlmerBialgebras.Paper
