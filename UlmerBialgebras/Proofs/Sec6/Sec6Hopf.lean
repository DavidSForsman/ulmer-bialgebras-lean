module

public import UlmerBialgebras.Proofs.Sec6.HopfExactness
public import UlmerBialgebras.Proofs.Sec6.HopfCocExactness
public import UlmerBialgebras.Proofs.Sec6.ExactnessBridge

/-!
# Corollary 6.11

* `grpExt_barrExact_reduction`: Fox's products and the created coreflexive equalizers give
  `Comon_A^coc` finite limits, and the reflexive coequalizers of `A` lift to it with the product
  preserving them (`Cor611.cocomm_*`, `ComonDescent.cocomm_standing`). The abstract core
  `Cart.isExactCat_grpExtTheory` then applies: the dictionary `M^{T_Grp} ≌ (S → Grp B)` and
  Corollary 6.9. The statements use Barr-exactness `CategoryTheory.BarrExact`; the bridges
  `CategoryTheory.isBarrExact_iff_barrExact` and `UlmerBialgebras.isExactCat_iff_barrExact`
  (`UlmerBialgebras/Proofs/Sec6/ExactnessBridge.lean`) connect it with the notions used in the
  proofs.
* `grpExt_barrExact`: `Mod_R` and `Mod_R^op` satisfy the hypotheses of the reduction when `R` is von
  Neumann regular (`UlmerBialgebras/Proofs/Sec6/HopfExactness.lean`). `Hopf^coc_{Mod_R^op}` is
  Barr-exact because
  it is the category of affine group schemes (`Loc.isBarrExact_grp_commComon_op`).
  `Hopf^coc_{Mod_R}` is Barr-exact by descent along the localizations from the field case
  (`Loc.isBarrExact_grp_commComon_of_field`).

## Main results

* `UlmerBialgebras.Paper.grpExt_barrExact_reduction`: the reduction step of the proof of
  Corollary 6.11 (not a numbered result), in its `Σ_Cart` form: for a symmetric monoidal `A`
  with coreflexive equalizers and reflexive coequalizers, both preserved by the tensor product in
  each variable, if `Hopf_A^coc = Grp(Comon_A^coc)` is Barr-exact, then `(Comon_A^coc)^T` is
  Barr-exact for every algebraic theory `T` extending the theory of groups in each sort.
* `UlmerBialgebras.Paper.grpExt_barrExact`: Corollary 6.11 in its `Σ_Cart` form: for a commutative
  von Neumann regular ring `R`, `(Comon_A^coc)^T` is Barr-exact for `A = Mod_R^op` and for
  `A = Mod_R`. The checked statements of Corollary 6.11 (`UniversalAlgebra.modelCat_barrExact` and
  its variants, `UlmerBialgebras/Proofs/Sec6/UniversalAlgebra/Exactness.lean`) do not use it: they
  are proved by
  `modelCat_barrExact_reduction` → `isExactCat_modelCat` → `isExactCat_cartThy_of_grp` →
  `isExactCat_thyObj_of_restrict` (Corollary 6.9).
* `UlmerBialgebras.Paper.grpExt_barrExact_moduleCat`: the same for `Mod_R = ModuleCat.{u} R`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollaries 6.9
  and 6.11
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.Paper

open CategoryTheory Limits MonoidalCategory Cart Loc

/-- **Corollary 6.11, reduction to groups** ([forsman2026syntactic]) (auxiliary: the step of the
paper's proof, factorization.tex ~line 193, stated on its own; not a numbered result). Let `A` be a
symmetric monoidal category with coreflexive equalizers and reflexive coequalizers, both preserved
by the tensor product in each variable. If `Hopf_A^coc = Grp(Comon_A^coc)` is Barr-exact, then
`(Comon_A^coc)^T` is exact for every multi-sorted theory `T` of universal algebra extending the
theory of groups in each sort. -/
theorem grpExt_barrExact_reduction (A : Type u) [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A] [HasCoreflexiveEqualizers A] [HasReflexiveCoequalizers A]
    [∀ Z : A, PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ Z : A, PreservesCoreflexiveEq (tensorRight Z)]
    [∀ Z : A, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    [∀ Z : A, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]
    [BarrExact (Grp (CategoryTheory.CommComon A))]
    (S Fn' : Type) (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ()) {E' : Type}
    (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
    (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))
    (halg : (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).IsAlgebraic) :
    BarrExact ((cartModel (CategoryTheory.CommComon A)).thyObj (grpExtSig S Fn' dom' cod')
      (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) : Type (max u v)) := by
  have := Cor611.cocomm_hasFiniteLimits A
  have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := A)
  have := fun X => (ComonDescent.cocomm_standing A X).1
  have := fun X => (ComonDescent.cocomm_standing A X).2
  exact isExactCat_iff_barrExact.1 (isExactCat_grpExtTheory_univ.{v, u}
    (CategoryTheory.isBarrExact_iff_barrExact.2 inferInstance) S Fn' dom' cod' edom ecod elhs erhs
        halg)

/-- **Corollary 6.11** ([forsman2026syntactic]): let `R` be a commutative von Neumann regular ring
and `T` a multi-sorted theory of universal algebra extending the theory of groups in each sort. Then
`(Comon_A^coc)^T` is exact for `A = Mod_R^op` (where `Comon_A^coc` is the category of affine
`R`-schemes) and for `A = Mod_R`. -/
theorem grpExt_barrExact (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (S Fn' : Type) (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ()) {E' : Type}
    (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
    (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))
    (halg : (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).IsAlgebraic) :
    BarrExact ((cartModel (CategoryTheory.CommComon (ModU R)ᵒᵖ)).thyObj (grpExtSig S Fn' dom' cod')
      (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) : Type (u + 1)) ∧
    BarrExact ((cartModel (CategoryTheory.CommComon (ModU R))).thyObj (grpExtSig S Fn' dom' cod')
      (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) : Type (u + 1)) := by
  refine ⟨?_, ?_⟩
  · have := fun Z => Loc.modUOp_preservesReflexiveCoeq_tensorLeft R hR Z
    have := fun Z => Loc.modUOp_preservesReflexiveCoeq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_op R hR).barrExact
    exact grpExt_barrExact_reduction (ModU R)ᵒᵖ S Fn' dom' cod' edom ecod elhs erhs halg
  · have := fun Z => Loc.modU_preservesCoreflexiveEq_tensorLeft R hR Z
    have := fun Z => Loc.modU_preservesCoreflexiveEq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_of_field R hR
      fun k _ hk => Loc.isBarrExact_grp_commComon_modU_of_isField k hk).barrExact
    exact grpExt_barrExact_reduction (ModU R) S Fn' dom' cod' edom ecod elhs erhs halg

/-- **Corollary 6.11, for `ModuleCat R`** ([forsman2026syntactic]): Corollary 6.11
(`grpExt_barrExact`) for the category of `R`-modules itself, `ModuleCat.{u} R`, with objects in
`Type (u + 1)` and morphisms in `Type u`, instead of the copy `ModU R` with hom-sets lifted to
`Type (u + 1)`: for a commutative von Neumann regular ring `R` and a multi-sorted theory `T` of
universal algebra extending the theory of groups in each sort, `(Comon_A^coc)^T` is exact for
`A = Mod_R^op` and for `A = Mod_R`.
-/
theorem grpExt_barrExact_moduleCat (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (S Fn' : Type) (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ()) {E' : Type}
    (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
    (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))
    (halg : (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).IsAlgebraic) :
    BarrExact ((cartModel (CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ)).thyObj
      (grpExtSig S Fn' dom' cod') (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) :
        Type (u + 1)) ∧
    BarrExact ((cartModel (CategoryTheory.CommComon (ModuleCat.{u} R))).thyObj
      (grpExtSig S Fn' dom' cod') (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) :
        Type (u + 1)) := by
  refine ⟨?_, ?_⟩
  · have := fun Z => Loc.moduleCatOp_preservesReflexiveCoeq_tensorLeft R hR Z
    have := fun Z => Loc.moduleCatOp_preservesReflexiveCoeq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_moduleCat_op R hR).barrExact
    exact grpExt_barrExact_reduction (ModuleCat.{u} R)ᵒᵖ S Fn' dom' cod' edom ecod elhs erhs halg
  · have := fun Z => Loc.moduleCat_preservesCoreflexiveEq_tensorLeft R hR Z
    have := fun Z => Loc.moduleCat_preservesCoreflexiveEq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_moduleCat R hR
      fun k _ hk => Loc.isBarrExact_grp_commComon_modU_of_isField k hk).barrExact
    exact grpExt_barrExact_reduction (ModuleCat.{u} R) S Fn' dom' cod' edom ecod elhs erhs halg

end UlmerBialgebras.Paper
