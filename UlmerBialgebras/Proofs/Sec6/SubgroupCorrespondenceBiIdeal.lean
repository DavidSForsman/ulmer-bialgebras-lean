module

public import UlmerBialgebras.Proofs.Sec6.SubgroupCorrespondenceCategorical
public import Hopf.Cocommutative.BiIdealDictionary
public import InternalGroups.GrpObjSubgroupCorrespondenceBiIdeal

/-!
# Newman's bi-ideal correspondence for `Comon_k^coc`

Let `k` be a field and `H` a group object of `Comon_k^coc = CommComon (ModuleCat k)`, a
cocommutative Hopf algebra.  This file compares Newman's categorical bi-ideal map
(`InternalGroups.biIdealMap`, `InternalGroups/GrpObjSubgroupCorrespondenceBiIdeal.lean`) with
Newman's algebraic correspondence `τ : K ↦ H K⁺`
(`HopfAlgebra.Cocommutative.Correspondence.tauEquiv`).

* A subgroup object `s` of `H` is a `SubGrpObj` of `H` (`InternalGroups.SubGrp.toSubGrpObj`), so
  the lemmas of `UlmerBialgebras/Proofs/Sec6/SubgroupCorrespondenceCategorical.lean` apply to it.
  Subgroup objects are
  ordered by their images in `H` (`InternalGroups.SubGrp.le_iff_range_le`).
* The kernel of the coset quotient `H ⟶ H/s` is `H K⁺`, where `K` is the image of `s`
  (`InternalGroups.SubGrp.ker_quotLinearMap`).

* The bi-ideal of `s` is `H K⁺` (`InternalGroups.SubGrp.biIdeal_toLeftBiIdeal`), so the
  bi-ideal map is conjugate to `τ`, and bijective once every sub-Hopf algebra is the image of a
  subgroup object (`InternalGroups.biIdealMap_bijective_of_surjective`).

* Every sub-Hopf algebra is the image of a subgroup object
  (`InternalGroups.SubGrp.toSubHopfAlg_surjective`): its subcoalgebra is an object of
  `Comon_k^coc`, closed under the operations of `H` on generalized elements.  Hence the bi-ideal
  map is bijective (`InternalGroups.biIdealMap_bijective_of_field`).

## Main results

* `InternalGroups.SubGrp.le_iff_range_le`: `s ≤ t` iff the image of `s` lies in that of `t`;
* `InternalGroups.SubGrp.ker_quotLinearMap`: the kernel of the coset quotient is `H K⁺`;
* `InternalGroups.biIdealMap_bijective_of_surjective`: the bi-ideal map is bijective if every
  sub-Hopf algebra is the image of a subgroup object;
* `InternalGroups.biIdealMap_bijective_of_field`: the bi-ideal map is bijective.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped MonObj ComonObj

namespace InternalGroups

open HopfAlgebra.Cocommutative.GrpDict UlmerBialgebras
open _root_.HopfAlgebra.Cocommutative (tau tau_le mem_augPart SubHopfAlg tauMap tauMap_carrier
  LeftBiIdeal Correspondence.tauEquiv)

variable {k : Type u} [Field k] {H : Grp (CategoryTheory.CommComon (ModuleCat.{u} k))}

/-- A subgroup object `s` of `H`, as a `SubGrpObj` of `H`. -/
noncomputable def SubGrp.toSubGrpObj (s : SubGrp H.X) : SubGrpObj H :=
  SubGrpObj.ofGrpHom (Grp.homMk (A := Grp.mk s.N) (B := H) s.i) (inferInstanceAs (Mono s.i))

/-- **Subgroup objects are ordered by their images.** -/
theorem SubGrp.le_iff_range_le (s t : SubGrp H.X) :
    s ≤ t ↔ LinearMap.range s.toSubGrpObj.inclLinearMap ≤
      LinearMap.range t.toSubGrpObj.inclLinearMap := by
  constructor
  · rintro ⟨f, hf⟩ _ ⟨x, rfl⟩
    exact ⟨f.hom.hom.hom x, congr(($hf).hom.hom.hom x)⟩
  · intro h
    obtain ⟨f, hf⟩ := t.toSubGrpObj.mem_of_range_le s.i h
    exact ⟨f, hf⟩

/-- The coset multiplication of `s` is that of the associated `SubGrpObj`. -/
lemma SubGrp.cosetMul_eq (s : SubGrp H.X) : cosetMul s = s.toSubGrpObj.cosetMul := by
  rw [cosetMul, CategoryTheory.Hom.mul_def, SubGrpObj.cosetMul]
  congr 1

/-- The underlying linear map of the coset quotient `H ⟶ H/s`. -/
noncomputable abbrev SubGrp.quotLinearMap (s : SubGrp H.X) :
    (H.X.X : ModuleCat.{u} k) →ₗ[k] (s.quot.V.X.X : ModuleCat.{u} k) :=
  modLinearMap s.quot.p

/-- `s.quotLinearMap` is the underlying linear map of the coset quotient's map of modules. -/
lemma SubGrp.modHomA_quot_p_hom (s : SubGrp H.X) :
    (modHomA s.quot.p).hom = s.quotLinearMap := rfl

/-- The coset quotient coequalizes the coset pair of the associated `SubGrpObj`. -/
lemma SubGrp.cosetMul_comp_quot_p' (s : SubGrp H.X) :
    s.toSubGrpObj.cosetMul ≫ s.quot.p.hom =
      CartesianMonoidalCategory.fst H.X s.toSubGrpObj.N ≫ s.quot.p.hom := by
  rw [← SubGrp.cosetMul_eq]; exact cosetMul_comp_quot_p s

/-- **The kernel of the coset quotient `H ⟶ H/s` lies in `H K⁺`**, where `K` is the image of
`s`: the coset quotient is a coequalizer of the coset pair in `Comon_k^coc`, since the forgetful
functor from `s`-modules preserves reflexive coequalizers
(`InternalGroups.SubGrpObj.ker_le_tau_of_isColimit`). -/
theorem SubGrp.ker_quotLinearMap_le_tau (s : SubGrp H.X) :
    LinearMap.ker s.quotLinearMap ≤
      tau (LinearMap.range s.toSubGrpObj.inclLinearMap) :=
  s.toSubGrpObj.ker_le_tau_of_isColimit s.quot.p.hom s.cosetMul_comp_quot_p'
    (isColimitCoforkQuot s (CategoryTheory.Mod_.preservesReflexiveCoequalizers_forget (A := H.X)
      fun _ => inferInstance))

/-- **`H K⁺` is killed by the coset quotient `H ⟶ H/s`**, where `K` is the image of `s`. -/
theorem SubGrp.tau_le_ker_quotLinearMap (s : SubGrp H.X) :
    tau (LinearMap.range s.toSubGrpObj.inclLinearMap) ≤
      LinearMap.ker s.quotLinearMap := by
  set S := s.toSubGrpObj
  refine tau_le fun a x hx => ?_
  obtain ⟨⟨n, rfl⟩, hε⟩ := mem_augPart.mp hx
  have hcounit : Coalgebra.counit (R := k) (S.inclLinearMap n) = Coalgebra.counit (R := k) n :=
    congr(($(IsComonHom.hom_counit (f := S.n.hom.hom))).hom n)
  have h : s.quotLinearMap (S.cosetMul.hom.hom.hom (a ⊗ₜ[k] n)) =
      s.quotLinearMap ((CartesianMonoidalCategory.fst H.X S.N).hom.hom.hom (a ⊗ₜ[k] n)) :=
    congr(($(s.cosetMul_comp_quot_p')).hom.hom.hom (a ⊗ₜ[k] n))
  rw [S.cosetMul_tmul, S.fst_tmul] at h
  rw [LinearMap.mem_ker, h, map_smul, ← hcounit, hε, zero_smul]

/-- **The kernel of the coset quotient `H ⟶ H/s` is `H K⁺`**, where `K` is the image of `s`. -/
theorem SubGrp.ker_quotLinearMap (s : SubGrp H.X) :
    LinearMap.ker s.quotLinearMap =
      tau (LinearMap.range s.toSubGrpObj.inclLinearMap) :=
  le_antisymm s.ker_quotLinearMap_le_tau s.tau_le_ker_quotLinearMap

/-! ## The bi-ideal map is conjugate to `τ` -/

/-- The image of a subgroup object, a sub-Hopf algebra of `H`. -/
noncomputable def SubGrp.toSubHopfAlg (s : SubGrp H.X) :
    SubHopfAlg k (H.X.X : ModuleCat.{u} k) :=
  ⟨s.toSubGrpObj.rangeSubalgebra, s.toSubGrpObj.isSubHopf_rangeSubalgebra⟩

/-- The underlying subspace of the image of `s` is the range of its inclusion. -/
lemma SubGrp.toSubmodule_toSubHopfAlg (s : SubGrp H.X) :
    Subalgebra.toSubmodule s.toSubHopfAlg.carrier =
      LinearMap.range s.toSubGrpObj.inclLinearMap :=
  s.toSubGrpObj.toSubmodule_rangeSubalgebra

/-- Subgroup objects are ordered by their images, as sub-Hopf algebras. -/
lemma SubGrp.toSubHopfAlg_le_iff (s t : SubGrp H.X) :
    s ≤ t ↔ s.toSubHopfAlg.carrier ≤ t.toSubHopfAlg.carrier := by
  rw [SubGrp.le_iff_range_le, ← s.toSubmodule_toSubHopfAlg, ← t.toSubmodule_toSubHopfAlg]
  exact Subalgebra.toSubmodule.le_iff_le

/-- **The bi-ideal of a subgroup object is `H K⁺`**, where `K` is its image. -/
theorem SubGrp.biIdeal_toLeftBiIdeal (s : SubGrp H.X) :
    s.biIdeal.toLeftBiIdeal = tauMap s.toSubHopfAlg := by
  apply LeftBiIdeal.ext
  change ModuleCat.subobjectModule _ (kernelSubobject (modHomA s.quot.p)) = _
  rw [subobjectModule_kernelSubobject, s.modHomA_quot_p_hom, s.ker_quotLinearMap, tauMap_carrier,
    s.toSubmodule_toSubHopfAlg]

/-- **Newman's bi-ideal map is bijective as soon as every sub-Hopf algebra is the image of a
subgroup object.**  It is conjugate to Newman's algebraic correspondence `τ`
(`InternalGroups.SubGrp.biIdeal_toLeftBiIdeal`), which is bijective
(`HopfAlgebra.Cocommutative.Correspondence.tauEquiv`); bi-ideals embed into left bi-ideals, and
subgroup objects into sub-Hopf algebras. -/
theorem biIdealMap_bijective_of_surjective
    (hC : Function.Surjective (SubGrp.toSubHopfAlg (H := H))) :
    Function.Bijective (biIdealMap H.X) := by
  have key : ∀ s : SubGrp H.X, (biIdealMap H.X (toAntisymmetrization (· ≤ ·) s)).toLeftBiIdeal =
      Correspondence.tauEquiv s.toSubHopfAlg :=
    fun s => s.biIdeal_toLeftBiIdeal
  constructor
  · intro a b hab
    induction a using Antisymmetrization.ind with | _ s => ?_
    induction b using Antisymmetrization.ind with | _ t => ?_
    have h := congr(($hab).toLeftBiIdeal)
    rw [key, key] at h
    have h' := congr(($(Correspondence.tauEquiv.injective h)).carrier)
    exact (toAntisymmetrization_eq _ _ _).2
      ⟨(s.toSubHopfAlg_le_iff t).2 h'.le, (t.toSubHopfAlg_le_iff s).2 h'.ge⟩
  · intro I
    obtain ⟨s, hs⟩ :=
      hC (Correspondence.tauEquiv.symm I.toLeftBiIdeal)
    refine ⟨toAntisymmetrization (· ≤ ·) s, BiIdeal.toLeftBiIdeal_injective ?_⟩
    rw [key, hs, Equiv.apply_symm_apply]

/-! ## Every sub-Hopf algebra is the image of a subgroup object -/

/-- **Every sub-Hopf algebra of `H` is the image of a subgroup object.** -/
theorem exists_subGrpObj_range_eq
    (K : SubHopfAlg k (H.X.X : ModuleCat.{u} k)) :
    ∃ S : SubGrpObj H, LinearMap.range S.inclLinearMap = Subalgebra.toSubmodule K.carrier := by
  -- `K` is the image of a subcoalgebra `n : N ⟶ H`; it is closed under the unit, the
  -- multiplication and the antipode, so `n` is a subgroup object (`hmem` factors through `n`)
  set E := Subalgebra.toSubmodule K.carrier
  obtain ⟨N, n, hn, hrange⟩ := exists_subcoalgebra_hom H.X E K.isSubHopf.comul_mem
  have hmem : ∀ {T : CategoryTheory.CommComon (ModuleCat.{u} k)} (x : T ⟶ H.X),
      (∀ t, x.hom.hom.hom t ∈ K.carrier) → ∃ z : T ⟶ N, z ≫ n = x := fun x hx =>
    exists_comp_eq_of_range_le n hn x (by rintro _ ⟨t, rfl⟩; rw [hrange]; exact hx t)
  have hval : ∀ {T : CategoryTheory.CommComon (ModuleCat.{u} k)} (x : T ⟶ N) (t : T.X),
      (x ≫ n).hom.hom.hom t ∈ K.carrier := fun x t => by
    have : (x ≫ n).hom.hom.hom t ∈ LinearMap.range n.hom.hom.hom := ⟨x.hom.hom.hom t, rfl⟩
    rwa [hrange] at this
  have hv : ∀ a, n.hom.hom.hom a ∈ K.carrier := fun a => by
    have : n.hom.hom.hom a ∈ LinearMap.range n.hom.hom.hom := ⟨a, rfl⟩
    rwa [hrange] at this
  let nl : (N.X : ModuleCat.{u} k) →ₗ[k] (H.X.X : ModuleCat.{u} k) := n.hom.hom.hom
  have hw : ∀ w : TensorProduct k (N.X : ModuleCat.{u} k) (N.X : ModuleCat.{u} k),
      LinearMap.mul' k (H.X.X : ModuleCat.{u} k) (TensorProduct.map nl nl w) ∈ K.carrier :=
    fun w => by
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
        rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
        exact K.carrier.mul_mem (hv a) (hv b)
      | add v w hv' hw' => rw [map_add, map_add]; exact add_mem hv' hw'
  have hmono : Mono n := by
    have : Mono ((CommComon.forgetV (ModuleCat.{u} k)).map n) :=
      (ModuleCat.mono_iff_injective _).2 hn
    exact (CommComon.forgetV (ModuleCat.{u} k)).mono_of_mono_map this
  refine ⟨⟨N, n, hmono, fun T => ?_, fun {T} x y => ?_, fun {T} x => ?_⟩, hrange⟩
  · -- the unit
    refine hmem _ fun t => ?_
    rw [show (1 : T ⟶ H.X).hom.hom.hom t = (unitHom H).hom (ε[T.X].hom t) from
      congr(($(one_hom_eq H)).hom t), ← algebraMap_eq]
    exact K.carrier.algebraMap_mem _
  · -- products
    refine hmem _ fun t => ?_
    have h := congr(($(mul_hom_eq H (x ≫ n) (y ≫ n))).hom t)
    have h' : ((x ≫ n) * (y ≫ n)).hom.hom.hom t = LinearMap.mul' k (H.X.X : ModuleCat.{u} k)
        (TensorProduct.map nl nl
          (TensorProduct.map x.hom.hom.hom y.hom.hom.hom (Δ[T.X].hom t))) := by
      rw [mul'_eq]
      exact h.trans (congr((mulHom H).hom $(LinearMap.congr_fun
        (TensorProduct.map_comp nl nl x.hom.hom.hom y.hom.hom.hom) (Δ[T.X].hom t))))
    rw [h']
    exact hw _
  · -- the antipode
    refine hmem _ fun t => ?_
    exact K.isSubHopf.antipode_mem _ (hv (x.hom.hom.hom t))

/-- A `SubGrpObj` of `H`, as a subgroup object of `H.X`. -/
noncomputable def SubGrpObj.toSubGrp (S : SubGrpObj H) : SubGrp H.X :=
  letI := S.grpObj
  haveI := S.mono
  haveI := S.isMonHom_n
  ⟨S.N, S.n⟩

/-- **Every sub-Hopf algebra of `H` is the image of a subgroup object.** -/
theorem SubGrp.toSubHopfAlg_surjective :
    Function.Surjective (SubGrp.toSubHopfAlg (H := H)) := fun K => by
  obtain ⟨S, hS⟩ := exists_subGrpObj_range_eq K
  refine ⟨S.toSubGrp,
    SubHopfAlg.ext (Subalgebra.toSubmodule_injective ?_)⟩
  rw [SubGrp.toSubmodule_toSubHopfAlg]
  exact hS

/-- **Newman's bi-ideal correspondence holds for cocommutative Hopf algebras over a field**: the
bi-ideal map of every group object of `Comon_k^coc` is bijective. -/
theorem biIdealMap_bijective_of_field (h : CategoryTheory.CommComon (ModuleCat.{u} k))
    [GrpObj h] : Function.Bijective (biIdealMap h) :=
  biIdealMap_bijective_of_surjective (H := Grp.mk h) SubGrp.toSubHopfAlg_surjective

end InternalGroups
