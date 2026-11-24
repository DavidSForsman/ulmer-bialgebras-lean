module

public import Hopf.Cocommutative.Correspondence.Main
public import Hopf.Cocommutative.GrpHomDictionary
public import Hopf.Cocommutative.DescentFreeBasis
public import Hopf.Cocommutative.CoinvSubcoalgebra
public import Hopf.Cocommutative.CommComonTensor
public import InternalGroups.SubgroupCorrespondence
public import Mathlib.Tactic.Group
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Foundations.CategoryTheory.Monoidal.ComonColimits
public import Hopf.Cocommutative.CocommFiniteLimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import InternalGroups.CosetKernel
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import UlmerBialgebras.Monadicity.LPAdjoint
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import UlmerBialgebras.Kan.Sifted
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Monadicity.ComonPresentable
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Basic.InsEqCat
public import UlmerBialgebras.Monadicity.AccCompleteIff
public import Foundations.CategoryTheory.Grp.GrpLimits
public import Foundations.CategoryTheory.Presentable.LPComplete
public import InternalGroups.CosetEffective

/-!
# Newman's correspondence for `Comon_k^coc`, unconditionally

Let `k` be a field. A group object `H` of `Comon_k^coc = CommComon (ModuleCat k)` is a
cocommutative Hopf algebra (`Hopf/Cocommutative/GrpCocommHopf.lean`). This file proves that
every coset relation of `H` is effective:

* `InternalGroups.SubGrpObj.isEffectiveCoset_of_field`: the coset pair `H ⊗ S ⇉ H` of a subgroup
  object `S` is the kernel pair of the coset quotient `q : H ⟶ H/S`.

It is used by Newman's bi-ideal correspondence for `Comon_k^coc`
(`UlmerBialgebras/Proofs/Sec6/SubgroupCorrespondenceBiIdeal.lean`), and is the input on coset
relations of the
exactness criterion of the development repository's `Solution/HopfCocStablyEpiMono.lean`.

The proof reduces the categorical statement to Newman's two closure identities for cocommutative
Hopf algebras, `μ (τ K) = K` (`HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq`) and
`τ (μ I) = I` (`HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq`), where `τ K = H K⁺` and
`μ I = {h | Δ h − h ⊗ 1 ∈ H ⊗ I}`. Write `n` for the inclusion of `S` and `K` for its image.

1. `InternalGroups.SubGrpObj.isSubHopf_rangeSubalgebra`: `K` is a sub-Hopf algebra of `H`.
2. `InternalGroups.SubGrpObj.ker_quotπLinearMap_le_tau`: `ker q ≤ H K⁺` (over any commutative
   ring), since the forgetful functor to `ModuleCat k` preserves the coset coequalizer; the same
   holds for any coequalizer of the coset pair (`InternalGroups.SubGrpObj.ker_le_tau_of_isColimit`).
3. `InternalGroups.SubGrpObj.range_le_of_comp_quotπ`: a generalized element `x : T ⟶ H` with
   `x ≫ q = 1 ≫ q` takes values in `μ (ker q) ≤ μ (H K⁺) = K`.
4. `InternalGroups.SubGrpObj.injective_inclLinearMap`: `n` is injective. Its kernel `J` is a left
   bi-ideal (`isLeftBiIdeal_ker_linearMap_incl`), and `μ J` consists of scalars
   (`exists_eq_smul_one_of_mem_coinv_ker`): `μ J` is the equalizer of the coreflexive pair
   `(id, n), (id, 1) : S ⟶ S ⊗ H`, whose inclusion `ι` satisfies `ι ≫ n = 1 ≫ n`, so `ι = 1` since
   `n` is a monomorphism. Hence `J = τ (μ J) = 0`.
5. `InternalGroups.SubGrpObj.mem_of_range_le`: a generalized element with values in `K` factors
   through `S`, since `n⁻¹ ∘ x` is a coalgebra map (`n ⊗ n` is injective over a field).
6. `InternalGroups.SubGrpObj.kernelSub_quot_equiv`: by 3 and 5, the kernel of `q` is `S` again,
   which is equivalent to the effectiveness of the coset relation
   (`InternalGroups.SubGrpObj.isEffectiveCoset_of_kernelSub_quot_equiv`).

The structure maps `S.one'`, `S.mul'` and `S.inv'` of `S` as a group object
(`InternalGroups/SubGrpObjAsGrp.lean`) are read through Fox's product, so that the
underlying linear maps can be computed elementwise.

## Main results

* `InternalGroups.SubGrpObj.isEffectiveCoset_of_field`: over a field `k`, the coset relation of a
  subgroup object `S` of a group object of `CommComon (ModuleCat k)` is effective.
* `InternalGroups.SubGrpObj.injective_inclLinearMap`: over a field, the inclusion of a subgroup
  object is injective on underlying modules.
* `InternalGroups.SubGrpObj.kernelSub_quot_equiv`: over a field, the kernel of the coset quotient
  `H ⟶ H/S` is equivalent to `S`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10 and
  Corollary 6.11
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory TensorProduct
open scoped MonObj ComonObj HopfAlgebra.Cocommutative.GrpDict

namespace InternalGroups.SubGrpObj

open UlmerBialgebras

open HopfAlgebra.Cocommutative.GrpDict

section CommRing

variable {k : Type u} [CommRing k] {H : Grp (CommComon (ModuleCat.{u} k))} (S : SubGrpObj H)

/-- The inclusion of a subgroup object, as a linear map of the underlying modules. -/
abbrev inclLinearMap : (S.N.X : ModuleCat.{u} k) →ₗ[k] (H.X.X : ModuleCat.{u} k) :=
  S.n.hom.hom.hom

/-- The unit `1` of `H` lies in the image of the inclusion `K ↪ H` of the subgroup object. -/
lemma one_mem_range_inclLinearMap : (1 : (H.X.X : ModuleCat.{u} k)) ∈
    LinearMap.range S.inclLinearMap := by
  refine ⟨S.one'.hom.hom.hom (1 : k), ?_⟩
  have h := congr(($(S.one'_comp)).hom.hom.hom (1 : k))
  have hone : (oneMor H) = η[H.X] := by
    rw [oneMor, CategoryTheory.Hom.one_def]
    exact ((toUnit_unique _ (𝟙 _)) =≫ η[H.X]).trans (Category.id_comp _)
  simp only [CommComon.comp_hom, ModuleCat.hom_comp] at h
  rw [one_def, unitHom, hone]
  exact h

/-- The image of the inclusion `K ↪ H` is closed under multiplication. -/
lemma mul_mem_range_inclLinearMap {a b : (H.X.X : ModuleCat.{u} k)}
    (ha : a ∈ LinearMap.range S.inclLinearMap) (hb : b ∈ LinearMap.range S.inclLinearMap) :
    a * b ∈ LinearMap.range S.inclLinearMap := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  refine ⟨S.mul'.hom.hom.hom (s ⊗ₜ[k] t), ?_⟩
  have h := congr(($(S.mul'_comp)).hom.hom.hom (s ⊗ₜ[k] t))
  simp only [CommComon.comp_hom, ModuleCat.hom_comp,
    tensorHom_hom_hom] at h
  rw [mul_def, mulHom_eq]
  exact h

/-- The image of the inclusion `K ↪ H` is closed under the antipode. -/
lemma antipode_mem_range_inclLinearMap {a : (H.X.X : ModuleCat.{u} k)}
    (ha : a ∈ LinearMap.range S.inclLinearMap) :
    HopfAlgebra.antipode k a ∈ LinearMap.range S.inclLinearMap := by
  obtain ⟨s, rfl⟩ := ha
  refine ⟨S.inv'.hom.hom.hom s, ?_⟩
  have h := congr(($(S.inv'_comp)).hom.hom.hom s)
  simp only [CommComon.comp_hom, ModuleCat.hom_comp] at h
  exact h

/-- The comultiplication of `H` sends the image `K` of `K ↪ H` into the image of `K ⊗ K → H ⊗ H`. -/
lemma comul_mem_range_inclLinearMap {a : (H.X.X : ModuleCat.{u} k)}
    (ha : a ∈ LinearMap.range S.inclLinearMap) :
    Coalgebra.comul (R := k) a ∈ LinearMap.range
      (TensorProduct.mapIncl (LinearMap.range S.inclLinearMap)
        (LinearMap.range S.inclLinearMap)) := by
  obtain ⟨s, rfl⟩ := ha
  have h : Coalgebra.comul (R := k) (S.inclLinearMap s) =
      TensorProduct.map S.inclLinearMap S.inclLinearMap (Coalgebra.comul (R := k) s) :=
    congr(($(IsComonHom.hom_comul (f := S.n.hom.hom))).hom s)
  refine ⟨TensorProduct.map S.inclLinearMap.rangeRestrict S.inclLinearMap.rangeRestrict
    (Coalgebra.comul (R := k) s), ?_⟩
  rw [h, TensorProduct.mapIncl, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

/-- The image of a subgroup object, as a subalgebra of the underlying Hopf algebra. -/
noncomputable def rangeSubalgebra : Subalgebra k (H.X.X : ModuleCat.{u} k) :=
  Submodule.toSubalgebra (LinearMap.range S.inclLinearMap) S.one_mem_range_inclLinearMap
    fun _ _ ha hb => S.mul_mem_range_inclLinearMap ha hb

/-- The underlying submodule of `S.rangeSubalgebra` is the range of the inclusion `K ↪ H`. -/
lemma toSubmodule_rangeSubalgebra :
    Subalgebra.toSubmodule S.rangeSubalgebra = LinearMap.range S.inclLinearMap :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- **The image of a subgroup object is a sub-Hopf algebra.** -/
theorem isSubHopf_rangeSubalgebra : HopfAlgebra.IsSubHopfAlgebra k S.rangeSubalgebra where
  comul_mem _ ha := S.comul_mem_range_inclLinearMap ha
  antipode_mem _ ha := S.antipode_mem_range_inclLinearMap ha

/-! ## The kernel of the coset quotient -/

/-- The underlying linear map of the coset quotient `H ⟶ H/S`. -/
noncomputable abbrev quotπLinearMap :
    (H.X.X : ModuleCat.{u} k) →ₗ[k] (S.quotObj.X : ModuleCat.{u} k) :=
  S.quotπ.hom.hom.hom

/-- The coset multiplication `H ⊗ K → H` sends `h ⊗ s` to `h * s`. -/
lemma cosetMul_tmul (h : (H.X.X : ModuleCat.{u} k)) (s : (S.N.X : ModuleCat.{u} k)) :
    S.cosetMul.hom.hom.hom (h ⊗ₜ[k] s) = h * S.inclLinearMap s := by
  have hw : (H.X ◁ S.n).hom.hom = 𝟙 H.X.X ⊗ₘ S.n.hom.hom := by
    rw [← id_tensorHom, tensorHom_hom_hom]
    rfl
  simp only [mul_def, mulHom_eq, cosetMul, CommComon.comp_hom, hw]
  rfl

/-- The first projection `H ⊗ K → H` of the cartesian structure sends `h ⊗ s` to `ε(s) • h`. -/
lemma fst_tmul (h : (H.X.X : ModuleCat.{u} k)) (s : (S.N.X : ModuleCat.{u} k)) :
    (fst H.X S.N).hom.hom.hom (h ⊗ₜ[k] s) = Coalgebra.counit (R := k) s • h :=
  rfl

/-- The two maps of the coset pair differ by an element of `H K⁺`. -/
lemma cosetMul_sub_fst_mem_tau (t : ((H.X ⊗ S.N).X : ModuleCat.{u} k)) :
    S.cosetMul.hom.hom.hom t - (fst H.X S.N).hom.hom.hom t ∈
      HopfAlgebra.Cocommutative.tau (LinearMap.range S.inclLinearMap) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    let m : (H.X.X : ModuleCat.{u} k) ⊗[k] (S.N.X : ModuleCat.{u} k) →ₗ[k]
        (H.X.X : ModuleCat.{u} k) := S.cosetMul.hom.hom.hom
    let p : (H.X.X : ModuleCat.{u} k) ⊗[k] (S.N.X : ModuleCat.{u} k) →ₗ[k]
        (H.X.X : ModuleCat.{u} k) := (fst H.X S.N).hom.hom.hom
    change m (x + y) - p (x + y) ∈ _
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hx hy
  | tmul h s =>
    rw [cosetMul_tmul, fst_tmul]
    have hcounit : Coalgebra.counit (R := k) (S.inclLinearMap s) = Coalgebra.counit (R := k) s :=
      congr(($(IsComonHom.hom_counit (f := S.n.hom.hom))).hom s)
    have hmem : S.inclLinearMap s - Coalgebra.counit (R := k) s • (1 : (H.X.X : ModuleCat.{u} k)) ∈
        HopfAlgebra.Cocommutative.augPart (LinearMap.range S.inclLinearMap) := by
      refine HopfAlgebra.Cocommutative.mem_augPart.mpr
        ⟨Submodule.sub_mem _ ⟨s, rfl⟩ (Submodule.smul_mem _ _ S.one_mem_range_inclLinearMap), ?_⟩
      rw [map_sub, map_smul, hcounit, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]
    have := HopfAlgebra.Cocommutative.mul_mem_tau h hmem
    rwa [mul_sub, mul_smul_comm, mul_one] at this

/-- **The kernel of a coequalizer of the coset pair lies in `H K⁺`**, where `K` is the image of
`S`: for any colimiting cofork `q : H ⟶ Q` of `H ⊗ S ⇉ H` in `Comon_k^coc`. The forgetful functor
to `ModuleCat k` preserves the coequalizer, and the quotient map `H ⟶ H ⧸ H K⁺` coequalizes the
coset pair, so it factors through `q`. -/
theorem ker_le_tau_of_isColimit {Q : CommComon (ModuleCat.{u} k)} (q : H.X ⟶ Q)
    (hq : S.cosetMul ≫ q = fst H.X S.N ≫ q) (hc : IsColimit (Cofork.ofπ q hq)) :
    LinearMap.ker q.hom.hom.hom ≤
      HopfAlgebra.Cocommutative.tau (LinearMap.range S.inclLinearMap) := by
  let F := CommComon.forgetV (ModuleCat.{u} k)
  have hcF : IsColimit (Cofork.ofπ (F.map q) (by simp only [← F.map_comp, hq]) :
      Cofork (F.map S.cosetMul) (F.map (fst H.X S.N))) :=
    (isColimitMapCoconeCoforkEquiv F hq) (isColimitOfPreserves F hc)
  let π₀ : F.obj H.X ⟶ ModuleCat.of k ((H.X.X : ModuleCat.{u} k) ⧸
      HopfAlgebra.Cocommutative.tau (LinearMap.range S.inclLinearMap)) :=
    ModuleCat.ofHom (HopfAlgebra.Cocommutative.tau (LinearMap.range S.inclLinearMap)).mkQ
  have hπ₀ : F.map S.cosetMul ≫ π₀ = F.map (fst H.X S.N) ≫ π₀ := by
    ext t
    exact Submodule.Quotient.eq _ |>.mpr (S.cosetMul_sub_fst_mem_tau t)
  obtain ⟨φ, hφ⟩ := Cofork.IsColimit.desc' hcF π₀ hπ₀
  intro y hy
  -- `y ↦ 0` under `q`, hence under `φ ∘ q = mkQ`.
  have h : φ.hom (q.hom.hom.hom y) = (HopfAlgebra.Cocommutative.tau
      (LinearMap.range S.inclLinearMap)).mkQ y := congr(($hφ).hom y)
  rw [LinearMap.mem_ker.mp hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero φ.hom))

/-- **The kernel of the coset quotient `H ⟶ H/S` lies in `H K⁺`**, where `K` is the image of `S`
(`ker_le_tau_of_isColimit`). -/
theorem ker_quotπLinearMap_le_tau :
    LinearMap.ker S.quotπLinearMap ≤
      HopfAlgebra.Cocommutative.tau (LinearMap.range S.inclLinearMap) :=
  S.ker_le_tau_of_isColimit S.quotπ S.quotπ_condition S.quotIsColimit

/-! ## Generalized elements with trivial class -/

/-- The underlying linear map of the constant unit sends `t` to `ε(t) • 1`. -/
private lemma elemLinearMap_one_apply {T : CommComon (ModuleCat.{u} k)}
    (t : (T.X : ModuleCat.{u} k)) :
    elemLinearMap (1 : T ⟶ H.X) t = Coalgebra.counit (R := k) t •
      (1 : (H.X.X : ModuleCat.{u} k)) := by
  have h := congr(($(one_hom_eq (H := H) (T := T))).hom t)
  refine h.trans ?_
  exact congr((unitHom H).hom $(mul_one (Coalgebra.counit (R := k) t))).symm.trans
    ((unitHom H).hom.map_smul _ _)

/-- If `x ≫ q = 1 ≫ q` for the coset quotient `q : H ⟶ H/S`, then `q (x t) = ε(t) q(1)`. -/
lemma quotπLinearMap_apply_of_comp_quotπ {T : CommComon (ModuleCat.{u} k)} (x : T ⟶ H.X)
    (hx : x ≫ S.quotπ = (1 : T ⟶ H.X) ≫ S.quotπ) (t : (T.X : ModuleCat.{u} k)) :
    S.quotπLinearMap (elemLinearMap x t) = Coalgebra.counit (R := k) t • S.quotπLinearMap 1 := by
  have h : S.quotπLinearMap (elemLinearMap x t) =
      S.quotπLinearMap ((1 : T ⟶ H.X).hom.hom.hom t) :=
    congr(($hx).hom.hom.hom t)
  exact h.trans (congr(S.quotπLinearMap $(elemLinearMap_one_apply t)).trans
    (S.quotπLinearMap.map_smul _ _))

/-- **A generalized element with trivial class takes values in the coinvariants of `ker q`.**
If `x ≫ q = 1 ≫ q` for the coset quotient `q : H ⟶ H/S`, then `(id ⊗ q) (Δ (x t)) = x t ⊗ q 1`,
and so `Δ (x t) - x t ⊗ 1` lies in `H ⊗ ker q`, the kernel of `id ⊗ q` (by flatness). -/
theorem mem_coinv_ker_of_comp_quotπ [IsAbsFlat k] {T : CommComon (ModuleCat.{u} k)}
    (x : T ⟶ H.X) (hx : x ≫ S.quotπ = (1 : T ⟶ H.X) ≫ S.quotπ) (t : (T.X : ModuleCat.{u} k)) :
    elemLinearMap x t ∈ HopfAlgebra.Cocommutative.coinv (LinearMap.ker S.quotπLinearMap) := by
  have hcomul : Coalgebra.comul (R := k) (elemLinearMap x t) =
      TensorProduct.map (elemLinearMap x) (elemLinearMap x) (Coalgebra.comul (R := k) t) :=
    congr(($(IsComonHom.hom_comul (f := x.hom.hom))).hom t)
  have hq : S.quotπLinearMap ∘ₗ elemLinearMap x =
      LinearMap.toSpanSingleton k _ (S.quotπLinearMap 1) ∘ₗ
        Coalgebra.counit (R := k) (A := (T.X : ModuleCat.{u} k)) := by
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    exact S.quotπLinearMap_apply_of_comp_quotπ x hx t
  rw [HopfAlgebra.Cocommutative.mem_coinv,
    ← HopfAlgebra.Cocommutative.ker_lTensor_eq_rightTensor, LinearMap.mem_ker, map_sub,
    LinearMap.lTensor_tmul, hcomul, LinearMap.lTensor_map, hq, ← LinearMap.map_lTensor,
    Coalgebra.lTensor_counit_comul, TensorProduct.map_tmul, LinearMap.toSpanSingleton_apply,
    one_smul]
  exact sub_self _

end CommRing

section Field

variable {k : Type u} [Field k] {H : Grp (CommComon (ModuleCat.{u} k))} (S : SubGrpObj H)

/-- **A generalized element with trivial class lies in the image of the subgroup object.**
Over a field, if `x ≫ q = 1 ≫ q` for the coset quotient `q : H ⟶ H/S`, then `x` takes values in
the image `K` of `S`: they lie in `μ (ker q) ≤ μ (H K⁺)`, and `μ (H K⁺) = K` by Newman's
closure identity for sub-Hopf algebras (`HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq`). -/
theorem range_le_of_comp_quotπ {T : CommComon (ModuleCat.{u} k)} (x : T ⟶ H.X)
    (hx : x ≫ S.quotπ = (1 : T ⟶ H.X) ≫ S.quotπ) :
    LinearMap.range (elemLinearMap x) ≤ LinearMap.range S.inclLinearMap := by
  rintro _ ⟨t, rfl⟩
  have h := HopfAlgebra.Cocommutative.coinv_mono S.ker_quotπLinearMap_le_tau
    (S.mem_coinv_ker_of_comp_quotπ x hx t)
  rw [← S.toSubmodule_rangeSubalgebra,
    HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq S.isSubHopf_rangeSubalgebra] at h
  rwa [← S.toSubmodule_rangeSubalgebra]

/-! ## Subgroup inclusions are injective -/

/-- **The kernel of the inclusion of a subgroup object is a left bi-ideal** of the underlying
Hopf algebra of `S`: the inclusion is a morphism of Hopf algebras, and over a field the kernel of
`n ⊗ n` is `ker n ⊗ S + S ⊗ ker n`. -/
theorem isLeftBiIdeal_ker_linearMap_incl :
    HopfAlgebra.Cocommutative.IsLeftBiIdeal (LinearMap.ker (linearMap S.incl)) where
  mul_mem h x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [HopfAlgebra.Cocommutative.GrpDict.map_mul, hx, mul_zero]
  counit_eq_zero x hx := by
    have h : Coalgebra.counit (R := k) (linearMap S.incl x) = Coalgebra.counit (R := k) x :=
      congr(($(IsComonHom.hom_counit (f := S.n.hom.hom))).hom x)
    rw [LinearMap.mem_ker.mp hx, map_zero] at h
    exact h.symm
  comul_mem x hx := by
    have hcomul : Coalgebra.comul (R := k) (linearMap S.incl x) =
        TensorProduct.map (linearMap S.incl) (linearMap S.incl) (Coalgebra.comul (R := k) x) :=
      congr(($(IsComonHom.hom_comul (f := S.n.hom.hom))).hom x)
    rw [LinearMap.mem_ker.mp hx, map_zero] at hcomul
    set n := linearMap S.incl
    have hinj : Function.Injective (TensorProduct.map (LinearMap.range n).subtype
        (LinearMap.range n).subtype) :=
      TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
        (Submodule.injective_subtype _)
    have hcomp : TensorProduct.map n n = TensorProduct.map (LinearMap.range n).subtype
        (LinearMap.range n).subtype ∘ₗ TensorProduct.map n.rangeRestrict n.rangeRestrict := by
      rw [← TensorProduct.map_comp]
      rfl
    have hmem : Coalgebra.comul (R := k) x ∈ LinearMap.ker (TensorProduct.map n n) :=
      LinearMap.mem_ker.mpr hcomul.symm
    rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj),
      HopfAlgebra.Cocommutative.ker_map_of_surjective _ n.surjective_rangeRestrict,
      LinearMap.ker_rangeRestrict] at hmem
    exact hmem

/-- **A point on which a coreflexive pair agrees is a value of its equalizer.** For a coreflexive
pair `u, v : M ⟶ N` of cocommutative comonoids over `k`, whose equalizer is computed on
underlying modules (`UlmerBialgebras.ComonCoreflexiveEq.eqCommComon`), every `b` with
`u b = v b` is `ι t` for some `t`. -/
theorem exists_eqCommComonι_apply {M N : CommComon (ModuleCat.{u} k)} {u v : M ⟶ N}
    (hr : IsCoreflexivePair u.hom.hom v.hom.hom) {b : (M.X : ModuleCat.{u} k)}
    (hb : u.hom.hom.hom b = v.hom.hom.hom b) :
    ∃ t, (ComonCoreflexiveEq.eqCommComonι hr
      (equalizerIsEqualizer u.hom.hom v.hom.hom)).hom.hom.hom t = b := by
  let f : ModuleCat.of k k ⟶ M.X := ModuleCat.ofHom (LinearMap.toSpanSingleton k _ b)
  have hf : f ≫ u.hom.hom = f ≫ v.hom.hom := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    exact (u.hom.hom.hom.map_smul (c : k) b).trans
      (congr((c : k) • $hb).trans (v.hom.hom.hom.map_smul (c : k) b).symm)
  refine ⟨(equalizer.lift f hf).hom (1 : k), ?_⟩
  have h : (equalizer.ι u.hom.hom v.hom.hom).hom _ = (1 : k) • b :=
    congr(($(equalizer.lift_ι f hf)).hom (1 : k))
  rwa [one_smul] at h

/-- **The coinvariants of the kernel of `n : S ⟶ H` are scalars.** They are the values of the
equalizer `ι : E ⟶ S` of the coreflexive pair `(id, n), (id, 1) : S ⟶ S ⊗ H`, which is computed
on underlying vector spaces (`UlmerBialgebras.ComonCoreflexiveEq.eqCommComon`). Then
`ι ≫ n = 1 ≫ n`, so `ι = 1` because `n` is a monomorphism, and the values of `1` are scalars. -/
theorem exists_eq_smul_one_of_mem_coinv_ker {b : (S.toGrp.X.X : ModuleCat.{u} k)}
    (hb : b ∈ HopfAlgebra.Cocommutative.coinv (LinearMap.ker (linearMap S.incl))) :
    ∃ c : k, b = c • (1 : (S.toGrp.X.X : ModuleCat.{u} k)) := by
  let u : S.N ⟶ S.N ⊗ H.X := lift (𝟙 S.N) S.n
  let v : S.N ⟶ S.N ⊗ H.X := lift (𝟙 S.N) (1 : S.N ⟶ H.X)
  have hr : IsCoreflexivePair u.hom.hom v.hom.hom :=
    IsCoreflexivePair.mk' (fst S.N H.X).hom.hom
      (congr(($(lift_fst (𝟙 S.N) S.n)).hom.hom))
      (congr(($(lift_fst (𝟙 S.N) (1 : S.N ⟶ H.X))).hom.hom))
  let he := equalizerIsEqualizer u.hom.hom v.hom.hom
  let j := ComonCoreflexiveEq.eqCommComonι hr he
  have hj : j ≫ S.n = (1 : ComonCoreflexiveEq.eqCommComon hr he ⟶ S.toGrp.X) ≫ S.n := by
    have hc := ((ComonCoreflexiveEq.eqCommComon_condition hr he) =≫ snd S.N H.X)
    simp only [Category.assoc, u, v, lift_snd, MonObj.comp_one] at hc
    exact hc.trans (MonObj.one_comp S.incl.hom.hom).symm
  have hj1 : j = (1 : ComonCoreflexiveEq.eqCommComon hr he ⟶ S.toGrp.X) :=
    (cancel_mono S.n).mp hj
  -- `b` equalizes the underlying linear maps of the pair
  have hu : u.hom.hom.hom b = b ⊗ₜ[k] (1 : (H.X.X : ModuleCat.{u} k)) := by
    have h1 : Coalgebra.comul (R := k) b - b ⊗ₜ[k] (1 : (S.toGrp.X.X : ModuleCat.{u} k)) ∈
        LinearMap.ker (LinearMap.lTensor _ (linearMap S.incl)) := by
      rw [HopfAlgebra.Cocommutative.ker_lTensor_eq_rightTensor]
      exact hb
    rw [LinearMap.mem_ker, map_sub, LinearMap.lTensor_tmul,
      HopfAlgebra.Cocommutative.GrpDict.map_one, sub_eq_zero] at h1
    exact h1
  have hv : v.hom.hom.hom b = b ⊗ₜ[k] (1 : (H.X.X : ModuleCat.{u} k)) := by
    change (Δ[S.N.X] ≫ (𝟙 S.N.X ⊗ₘ (1 : S.N ⟶ H.X).hom.hom)).hom b = _
    rw [one_hom_eq]
    change TensorProduct.map LinearMap.id ((unitHom H).hom ∘ₗ
        Coalgebra.counit (R := k) (A := (S.N.X : ModuleCat.{u} k)))
        (Coalgebra.comul (R := k) (A := (S.N.X : ModuleCat.{u} k)) b) = _
    rw [← LinearMap.map_lTensor]
    exact congr(TensorProduct.map LinearMap.id (unitHom H).hom
      $(Coalgebra.lTensor_counit_comul (R := k) (A := (S.N.X : ModuleCat.{u} k)) b))
  -- so `b` is a value of the equalizer
  obtain ⟨t, ht⟩ := exists_eqCommComonι_apply hr (hu.trans hv.symm)
  let E := ComonCoreflexiveEq.eqCommComon hr he
  let z : (E.X : ModuleCat.{u} k) := t
  refine ⟨Coalgebra.counit (R := k) z, ?_⟩
  have h := congr(elemLinearMap (H := S.toGrp) ($hj1) z)
  exact ht.symm.trans (h.trans (elemLinearMap_one_apply (H := S.toGrp) (T := E) z))

/-- **The inclusion of a subgroup object of a cocommutative Hopf algebra over a field is
injective.** Its kernel `J` is a left bi-ideal whose coinvariants are scalars
(`exists_eq_smul_one_of_mem_coinv_ker`), so `J = τ (μ J) = 0` by Newman's second closure
identity (`HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq`). -/
theorem injective_inclLinearMap : Function.Injective S.inclLinearMap := by
  have haug : HopfAlgebra.Cocommutative.augPart
      (HopfAlgebra.Cocommutative.coinv (LinearMap.ker (linearMap S.incl))) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbL, hbε⟩ := HopfAlgebra.Cocommutative.mem_augPart.mp hb
    obtain ⟨c, rfl⟩ := S.exists_eq_smul_one_of_mem_coinv_ker hbL
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hbε
    rw [hbε, zero_smul]
    exact Submodule.zero_mem _
  have hker : LinearMap.ker (linearMap S.incl) = ⊥ := by
    rw [← HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq S.isLeftBiIdeal_ker_linearMap_incl,
      HopfAlgebra.Cocommutative.tau, haug, Submodule.map₂_bot_right]
  exact LinearMap.ker_eq_bot.mp hker

/-! ## Generalized elements with values in the image factor through `S` -/

/-- **A generalized element with values in the image of a subgroup object belongs to it.** The
inclusion `n` is injective, so `n⁻¹ ∘ x` is a well-defined linear map; it is a morphism of
coalgebras because `n ⊗ n` is injective. -/
theorem mem_of_range_le {T : CommComon (ModuleCat.{u} k)} (x : T ⟶ H.X)
    (hx : LinearMap.range (elemLinearMap x) ≤ LinearMap.range S.inclLinearMap) : S.Mem x := by
  -- `x` factors linearly through the injective `S.inclLinearMap` as `z₀`; `z₀` is a comonoid
  -- morphism because `S.n` and `x` are and the tensor square of the inclusion is injective
  have hinj := S.injective_inclLinearMap
  have hxt : ∀ t, elemLinearMap x t ∈ LinearMap.range S.inclLinearMap := fun t => hx ⟨t, rfl⟩
  let z₀ : (T.X : ModuleCat.{u} k) →ₗ[k] (S.N.X : ModuleCat.{u} k) :=
    (LinearEquiv.ofInjective S.inclLinearMap hinj).symm.toLinearMap ∘ₗ
      (elemLinearMap x).codRestrict _ hxt
  have hz₀ : ∀ t, S.inclLinearMap (z₀ t) = elemLinearMap x t := fun t =>
    LinearEquiv.ofInjective_symm_apply (f := S.inclLinearMap) (h := hinj) ⟨elemLinearMap x t, hxt t⟩
  have hz₀' : S.inclLinearMap ∘ₗ z₀ = elemLinearMap x := LinearMap.ext hz₀
  have hnn : Function.Injective (TensorProduct.map S.inclLinearMap S.inclLinearMap) :=
    TensorProduct.map_injective_of_flat_flat _ _ hinj hinj
  let z : T.X ⟶ S.N.X := ModuleCat.ofHom z₀
  -- `z₀` preserves the counit and the comultiplication
  have hcounit : z ≫ ε[S.N.X] = ε[T.X] := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    have h1 : ε[H.X.X].hom (S.inclLinearMap (z₀ t)) = ε[S.N.X].hom (z₀ t) :=
      congr(($(IsComonHom.hom_counit (f := S.n.hom.hom))).hom (z₀ t))
    have h2 : ε[H.X.X].hom (elemLinearMap x t) = ε[T.X].hom t :=
      congr(($(IsComonHom.hom_counit (f := x.hom.hom))).hom t)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ← h1, hz₀, h2]
  have hcomul : z ≫ Δ[S.N.X] = Δ[T.X] ≫ (z ⊗ₘ z) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, ModuleCat.hom_tensorHom, ModuleCat.hom_ofHom]
    apply hnn
    have h1 : Δ[H.X.X].hom (S.inclLinearMap (z₀ t)) =
        TensorProduct.map S.inclLinearMap S.inclLinearMap (Δ[S.N.X].hom (z₀ t)) :=
      congr(($(IsComonHom.hom_comul (f := S.n.hom.hom))).hom (z₀ t))
    have h2 : Δ[H.X.X].hom (elemLinearMap x t) =
        TensorProduct.map (elemLinearMap x) (elemLinearMap x) (Δ[T.X].hom t) :=
      congr(($(IsComonHom.hom_comul (f := x.hom.hom))).hom t)
    rw [← h1, hz₀, h2, ← LinearMap.comp_apply (TensorProduct.map S.inclLinearMap S.inclLinearMap)
      (TensorProduct.map z₀ z₀), ← TensorProduct.map_comp, hz₀']
  have : IsComonHom z := { hom_counit := hcounit, hom_comul := hcomul }
  refine ⟨UlmerBialgebras.CommComon.homMk z, ?_⟩
  exact CategoryTheory.CommComon.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext hz₀))

/-! ## Effectiveness of the coset relations -/

/-- **The kernel of the coset quotient `H ⟶ H/S` is contained in `S`.** A generalized element
with trivial class takes values in the image of `S` (`range_le_of_comp_quotπ`), hence belongs
to `S` (`mem_of_range_le`). -/
theorem kernelSub_quot_le : ((S.quot).kernelSub).Le S := by
  rw [SubGrpObj.le_iff_mem]
  intro T x hx
  rw [QuotObj.mem_kernelSub, quot_q] at hx
  exact S.mem_of_range_le x (S.range_le_of_comp_quotπ x hx)

/-- **The kernel of the coset quotient `H ⟶ H/S` is `S`.** -/
theorem kernelSub_quot_equiv : ((S.quot).kernelSub).Equiv S :=
  ⟨S.kernelSub_quot_le, S.le_kernelSub_quot⟩

/-- **Every coset relation of a cocommutative Hopf algebra over a field is effective**: the coset
pair `H ⊗ S ⇉ H` of a subgroup object `S` is the kernel pair of `H ⟶ H/S`. The proof uses only
Newman's two closure identities, not Takeuchi's faithful flatness theorem. -/
theorem isEffectiveCoset_of_field : S.IsEffectiveCoset :=
  isEffectiveCoset_of_kernelSub_quot_equiv S.kernelSub_quot_equiv

end Field

end InternalGroups.SubGrpObj

namespace UlmerBialgebras.CocommComon

end UlmerBialgebras.CocommComon
