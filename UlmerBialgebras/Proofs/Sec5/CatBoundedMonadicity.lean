module

public import UlmerBialgebras.Proofs.Sec5.CatAccessibleMonadicity

/-!
# Relative left adjoints of functors as relative adjoints in CAT

The pointwise transposition of a relative left adjoint of functors gives a relative left
adjoint in the strict 2-category `CAT`. These comparison maps are used by the fixed-cardinal
monadicity results in `UlmerBialgebras/Proofs/Sec5/CatCardinalMonadicity.lean`.

## Main results

* `UlmerBialgebras.Paper.CatTwo.relTranspose`, `relTransposeInv`: pointwise transposition of
  natural transformations;
* `UlmerBialgebras.Paper.CatTwo.relLeftAdj2OfRelLeftAdjoint`: the relative adjoint in `CAT`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.2
  and Section 7
-/

@[expose] public section

universe v u w

namespace UlmerBialgebras.Paper.CatTwo

open CategoryTheory UlmerBialgebras Limits

/-! ## Relative left adjoints in `CAT` -/

section Rel

variable {c x : Cat.{v, u}} {f g : c ⟶ x} {L : c ⟶ c}

/-- The pointwise transposition of a relative left adjoint of functors, on natural
transformations `p ⋙ L ⟶ q`. -/
@[simps]
def relTranspose (ra : RelLeftAdjoint f.toFunctor g.toFunctor L.toFunctor) {z : Cat.{v, u}} (p q :
    z ⟶ c)
    (γ : p ≫ L ⟶ q) : p ≫ f ⟶ q ≫ g where
  toNatTrans := {
    app t := ra.homEquiv _ _ (γ.toNatTrans.app t)
    naturality t t' m := by
      have h := γ.toNatTrans.naturality m
      simp only [Cat.Hom.comp_map] at h ⊢
      rw [← ra.homEquiv_naturality_left, ← ra.homEquiv_naturality_right, h] }

/-- The pointwise inverse transposition of a relative left adjoint of functors. -/
@[simps]
def relTransposeInv (ra : RelLeftAdjoint f.toFunctor g.toFunctor L.toFunctor) {z : Cat.{v, u}} (p q
    : z ⟶ c)
    (δ : p ≫ f ⟶ q ≫ g) : p ≫ L ⟶ q where
  toNatTrans := {
    app t := (ra.homEquiv _ _).symm (δ.toNatTrans.app t)
    naturality t t' m := by
      have h := δ.toNatTrans.naturality m
      simp only [Cat.Hom.comp_map] at h ⊢
      rw [← ra.homEquiv_symm_naturality_left, ← ra.homEquiv_symm_naturality_right, h] }

/-- An `f`-relative left adjoint `L` of `g`, as functors, is an `f`-relative left adjoint of `g`
in the 2-category `CAT` (Remark 3.2 of [forsman2026syntactic]). -/
def relLeftAdj2OfRelLeftAdjoint (ra : RelLeftAdjoint f.toFunctor g.toFunctor L.toFunctor) :
    RelLeftAdj2 (Obj := Cat.{v, u}) f g L where
  equiv p q :=
    { toFun := relTranspose ra p q
      invFun := relTransposeInv ra p q
      left_inv γ := catVU_cell_ext fun t => by simp
      right_inv δ := catVU_cell_ext fun t => by simp }
  nat_left σ γ := catVU_cell_ext fun t => by
    simp [ra.homEquiv_naturality_left]
  nat_right γ τ := catVU_cell_ext fun t => by
    simp [ra.homEquiv_naturality_right]
  nat_z := by
    intros
    exact catVU_cell_ext fun t => by simp

end Rel

end UlmerBialgebras.Paper.CatTwo
