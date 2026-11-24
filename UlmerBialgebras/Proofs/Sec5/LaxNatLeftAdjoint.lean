module

public import UlmerBialgebras.Proofs.Sec5.HomTwoFunctor
public import UlmerBialgebras.Proofs.Sec5.MateNat
public import UlmerBialgebras.Density.ACotensorAdjoint
public import UlmerBialgebras.Models.CatTwoAdj

/-!
# The left adjoints of the representables of `g`, as local data of a lax transformation

For `g : d ⟶ c` such that every `K(x, g)`, `x ∈ A`, is a right adjoint, the chosen left adjoints
`L_x ⊣ K(x, g)` are adjunctions in `Cat` between the components of the hom 2-functors on `𝒜ᵒᵖ`.
The mates of the (identity) naturality cells of `K(−, g)` are the comparisons
`leftMateApp : L_y (u ≫ k) ⟶ u ≫ L_x k`.

## Main results

* `UlmerBialgebras.Paper.homAdj`: the adjunction `L_x ⊣ K(x, g)` in `Cat`.
* `UlmerBialgebras.Paper.mate_postcompLaxNat_app`: the components of the mates of `K(−, g)` are
  `leftMateApp`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory Bicategory TwoFun

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}
variable (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)

omit [Bicategory.Strict Obj] in
/-- The object `x` of `𝒜ᵒᵖ` lies in `A`. -/
lemma FullSubOp.prop (x : FullSubOp A) : A (FullSubOp.pt x) :=
  (show {x : Obj // A x} from x.unop).2

/-- The chosen left adjoint `L_x` of `K(x, g)`, as a 1-cell of `Cat`. -/
noncomputable abbrev homLeftAdj (x : FullSubOp A) :
    (homTwoFunctor A c).obj x ⟶ (homTwoFunctor A d).obj x :=
  (repLeftAdjoint hrep (FullSubOp.prop x)).toCatHom

/-- The adjunction `L_x ⊣ K(x, g)` in `Cat`. -/
noncomputable def homAdj (x : FullSubOp A) :
    TwoAdj (homLeftAdj hrep x) ((postcompLaxNat A g).app x) :=
  Adjunction.toTwoAdj (repLeftAdjunction hrep (FullSubOp.prop x))

/-- **The mates of `K(−, g)` are the comparisons of the left adjoints**: the component at `k` of
the mate of the naturality cell of `K(−, g)` at `f : x ⟶ y` is `leftMateApp`. -/
lemma mate_postcompLaxNat_app {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c) :
    ((Bicategory.mateEquiv (homAdj hrep x) (homAdj hrep y)).symm
        ((postcompLaxNat A g).nat f)).toNatTrans.app k =
      leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k := by
  apply leftMateApp_uniq
  have h := congr(($(unit_mateEquiv_symm (homAdj hrep x) (homAdj hrep y)
    ((postcompLaxNat A g).nat f))).toNatTrans.app k)
  simp only [AsBicat.leftUnitor_inv, AsBicat.rightUnitor_inv, AsBicat.associator_hom,
    AsBicat.associator_inv, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  have h₂ : FullSubOp.hom f ◁ (repLeftAdjunction hrep (FullSubOp.prop x)).unit.app k ≫
      (eqToHom (postcomp_naturality g f)).toNatTrans.app
        ((repLeftAdjoint hrep (FullSubOp.prop x)).obj k) =
      (repLeftAdjunction hrep (FullSubOp.prop y)).unit.app (FullSubOp.hom f ≫ k) ≫
        ((Bicategory.mateEquiv (homAdj hrep x) (homAdj hrep y)).symm
          ((postcompLaxNat A g).nat f)).toNatTrans.app k ▷ g := h
  rw [leftMateAux]
  exact h₂.symm.trans (congrArg _ (Cat.eqToHom_app _ _ _ _))

end UlmerBialgebras.Paper
