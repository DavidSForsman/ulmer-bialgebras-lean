module

public import UlmerBialgebras.Proofs.Sec6.GrpModels
public import UlmerBialgebras.Proofs.Sec5.Sec5_7
public import UlmerBialgebras.Proofs.Sec6.LocModel
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.PiLimits
public import Foundations.CategoryTheory.Exact.JointlyConservative
public import Foundations.CategoryTheory.Grp.GrpReflexiveCoeq
public import Foundations.CategoryTheory.Grp.GrpLimits
public import UlmerBialgebras.Proofs.Sec6.ExactBridge
public import Foundations.CategoryTheory.Grp.GrpTensorReflexive
public import UlmerBialgebras.Proofs.Sec6.GrpDescent
public import UlmerBialgebras.Proofs.Sec6.Support.CartTransport
public import Foundations.CategoryTheory.Exact.SemiAbelianEquiv

/-!
# The abstract core of Corollary 6.11

Let `B` be a cartesian category with finite limits and reflexive coequalizers, the binary product
preserving reflexive coequalizers in each variable. If `Grp B` is Barr-exact, then for every
multi-sorted theory `T` of universal algebra extending the theory of groups in each sort, the
category `B^T = (cartModel B)^T` is exact.

The models of the theory of groups form `S → Grp B` (`GrpModels.grpModelEquiv`), which is exact as a
product of exact categories. Corollary 6.9 then passes from the theory of groups to `T`.

## Main results

* `UlmerBialgebras.Paper.Cart.isExactCat_grpModel`: if `Grp B` is Barr-exact, the models of the
  theory of groups in `B` form an exact category.
* `UlmerBialgebras.Paper.Cart.isExactCat_grpExtTheory`: if `Grp B` is Barr-exact, `B^T` is exact for
  every algebraic theory `T` extending the theory of groups in each sort (the abstract core of
  Corollary 6.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollaries 6.9 and 6.11
-/

@[expose] public section

universe u u₁

namespace UlmerBialgebras.Paper.Cart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

section GrpModel

variable {B : Type (max u₁ u)} [Category.{max u₁ u} B] [CartesianMonoidalCategory B]
  [HasFiniteLimits B] [HasReflexiveCoequalizers B]
  [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]

include B in
/-- A power of the Barr-exact category `Grp B` is Barr-exact. -/
theorem isBarrExact_pi_grp (S : Type u₁) (h : CategoryTheory.IsBarrExact (Grp B)) :
    CategoryTheory.IsBarrExact (S → Grp B) := by
  -- The evaluations `S → Grp B ⥤ Grp B` are jointly conservative and preserve the relevant
  -- limits and coequalizers, which are computed sortwise; so exactness of `Grp B` transfers.
  classical
  have := h
  have : HasReflexiveCoequalizers (Grp B) :=
    CategoryTheory.GrpReflexiveCoeq.hasReflexiveCoequalizers_grp
      B
  have hrefl : ∀ {X Y : S → Grp B} (u v : X ⟶ Y), IsReflexivePair u v → HasCoequalizer u v := by
    intro X Y u v huv
    have : ∀ s, HasColimit (parallelPair u v ⋙ Pi.eval (fun _ : S => Grp B) s) := by
      intro s
      have hs : IsReflexivePair (u s) (v s) := by
        obtain ⟨r, hr₁, hr₂⟩ := huv.common_section
        exact IsReflexivePair.mk' (r s) (funext_iff.1 hr₁ s) (funext_iff.1 hr₂ s)
      have : HasColimit (parallelPair ((parallelPair u v ⋙ Pi.eval (fun _ : S => Grp B) s).map
          WalkingParallelPairHom.left) ((parallelPair u v ⋙ Pi.eval (fun _ : S => Grp B) s).map
            WalkingParallelPairHom.right)) := by
        have : IsReflexivePair ((parallelPair u v ⋙ Pi.eval (fun _ : S => Grp B) s).map
            WalkingParallelPairHom.left) ((parallelPair u v ⋙ Pi.eval (fun _ : S => Grp B) s).map
              WalkingParallelPairHom.right) := hs
        infer_instance
      exact hasColimit_of_iso (diagramIsoParallelPair _)
    exact ⟨⟨⟨piCoconeOfCocones (parallelPair u v) fun _ => colimit.cocone _,
      piIsColimitOfEval fun _ => colimit.isColimit _⟩⟩⟩
  -- the four hypotheses of the transfer: joint conservativity, preservation, and coequalizers
  -- of kernel pairs and of equivalence relations
  refine CategoryTheory.isBarrExact_of_jointlyConservative (D := fun _ : S => Grp B)
    (fun s => Pi.eval (fun _ : S => Grp B) s) ?_ ?_ ?_ ?_
  · refine ⟨?_⟩
    intro X Y f hf
    exact (isIso_pi_iff f).2 hf
  · exact fun _ => ⟨fun _ _ _ _ _ => inferInstance⟩
  · intro X Y Z f g₁ g₂ hk
    exact hrefl g₁ g₂ (UlmerBialgebras.Paper.GrpDescent.isReflexivePair_of_isKernelPair hk)
  · intro R X r₁ r₂ hr
    exact hrefl r₁ r₂ hr.isReflexivePair

include B in
/-- Models of the theory of groups in `B` form an exact category. -/
theorem isExactCat_grpModel (S : Type u₁) (h : CategoryTheory.IsBarrExact (Grp B)) :
    IsExactCat (GrpModels.GrpModel B S) := by
  have := isBarrExact_pi_grp S h
  exact (CategoryTheory.isExactCat_of_isBarrExact (C := S → Grp B)).of_equivalence
    (GrpModels.grpModelEquiv B S).symm

end GrpModel

section Ext

variable {B : Type u} [Category.{u} B] [CartesianMonoidalCategory B] [HasFiniteLimits B]
  [HasReflexiveCoequalizers B] [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]

omit [HasFiniteLimits B] [HasReflexiveCoequalizers B] in
include B in
/-- The functor symbols of `Σ_Cart` preserve reflexive coequalizers componentwise in the
cartesian model of `B`. -/
theorem cartModel_preservesReflexiveCoeqComponentwise :
    ∀ F : sigCart.Fun,
      PreservesColimitsComponentwise (cartModel B) WalkingReflexivePair F := by
  intro F
  cases F with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, B),
        PreservesColimitsOfShape WalkingReflexivePair
          (updateFunctor x i ⋙ MonEx.tensFunctor B) := by
      intro i x
      fin_cases i
      · have := preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq
          (tensorRight (x 1))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · have := preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq
          (tensorLeft (x 0))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

include B in
/-- **The abstract core of Corollary 6.11** ([forsman2026syntactic]). If `Grp B` is Barr-exact,
then `B^T` is exact for every multi-sorted theory `T` extending the theory of groups in each
sort. -/
theorem isExactCat_grpExtTheory (h : CategoryTheory.IsBarrExact (Grp B)) (S : Type) (Fn' : Type)
    (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ()) {E' : Type}
    (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
    (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))
    (halg : (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).IsAlgebraic) :
    IsExactCat ((cartModel B).thyObj (grpExtSig S Fn' dom' cod')
      (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) : Type u) :=
  isExactCat_thyObj_of_restrict.{u, u, _, _, _, _, _, _} (cartModel B)
    (grpExtSig S Fn' dom' cod') Sum.inl
    (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) Sum.inl (fun r => grpEqnLhs r)
    (fun r => grpEqnRhs r) (fun _ => rfl) (fun _ => rfl) halg
    (fun _ => (inferInstance : HasFiniteLimits B))
    (fun _ => (inferInstance : HasReflexiveCoequalizers B))
    cartModel_preservesReflexiveCoeqComponentwise
    (isExactCat_grpModel.{u, 0} S h)

section Univ

open UlmerBialgebras.UnivChange UnivChange.Model

universe vB uB

/-- **The abstract core of Corollary 6.11, at independent universes.** For a cartesian category
`B` with objects in `Type (max uB vB)` and morphisms in `Type vB`: if `Grp B` is Barr-exact, then
`B^T` is exact for every algebraic theory `T` extending the theory of groups in each sort. It
follows from `isExactCat_grpExtTheory` for `CartU B` (the hom-sets lifted to `Type (max uB vB)`),
whose cartesian model is the change of universe of that of `B` (`cartModel_cartU`). -/
theorem isExactCat_grpExtTheory_univ {B : Type (max uB vB)} [Category.{vB} B]
    [CartesianMonoidalCategory B] [HasFiniteLimits B] [HasReflexiveCoequalizers B]
    [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]
    (h : CategoryTheory.IsBarrExact (Grp B)) (S : Type) (Fn' : Type)
    (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ()) {E' : Type}
    (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
    (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))
    (halg : (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).IsAlgebraic) :
    IsExactCat ((cartModel B).thyObj (grpExtSig S Fn' dom' cod')
      (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs) : Type (max uB vB)) := by
  let e := cartUEquiv.{vB, uB} B
  have : HasFiniteLimits (CartU.{vB, uB} B) := hasFiniteLimits_of_equivalence e.symm
  have : HasReflexiveCoequalizers (CartU.{vB, uB} B) := by
    have := (hasReflexiveCoequalizers_iff (C := B)).2 inferInstance
    exact hasReflexiveCoequalizers_iff.1
      (Adjunction.hasColimitsOfShape_of_equivalence e.inverse)
  have : CategoryTheory.PreservesReflexiveCoeq e.inverse := ⟨fun _ _ _ _ _ => inferInstance⟩
  have : CategoryTheory.PreservesReflexiveCoeq e.functor := ⟨fun _ _ _ _ _ => inferInstance⟩
  have : ∀ Z : CartU.{vB, uB} B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z) :=
    fun Z => inferInstanceAs (CategoryTheory.PreservesReflexiveCoeq
      (e.inverse ⋙ tensorLeft (e.inverse.obj Z) ⋙ e.functor))
  have : ∀ Z : CartU.{vB, uB} B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z) :=
    fun Z => inferInstanceAs (CategoryTheory.PreservesReflexiveCoeq
      (e.inverse ⋙ tensorRight (e.inverse.obj Z) ⋙ e.functor))
  have h' : CategoryTheory.IsBarrExact (Grp (CartU.{vB, uB} B)) :=
    isBarrExact_of_equivalence e.mapGrp.symm
  have hU := isExactCat_grpExtTheory (B := CartU.{vB, uB} B) h' S Fn' dom' cod' edom ecod elhs
    erhs halg
  rw [cartModel_cartU] at hU
  exact hU.of_equivalence ((thyEquiv _).trans (upEquiv _).symm)

end Univ

end Ext

end UlmerBialgebras.Paper.Cart
