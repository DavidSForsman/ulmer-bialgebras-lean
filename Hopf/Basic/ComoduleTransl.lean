module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Hopf.Basic.Comodule

/-!
# Translation of a comodule by a functional

Let `C` be a coalgebra over `R` and `M` a right `C`-comodule with coaction `ρ m = ∑ m₍₀₎ ⊗ m₍₁₎`.
Every functional `u : C →ₗ[R] R` acts on `M` by

`u ⇀ m = ∑ u (m₍₁₎) • m₍₀₎`.

This is the action of `C*` on comodules used throughout §3 of M. Takeuchi, *A correspondence
between Hopf ideals and sub-Hopf algebras* (manuscripta math. **7** (1972), 251–270).

## Main definitions

* `Coalgebra.Comodule.transl u`: the operator `u ⇀ -`;
* `Coalgebra.Comodule.convFun v u`: the convolution product of two functionals;
* `Coalgebra.Comodule.translSpan m`: the span of all translates of `m`;
* `Coalgebra.translLeft w`: the left translation `w ⇁ c = ∑ w (c₍₁₎) c₍₂₎` of a coalgebra
  by a functional, with `translLeft_translLeft` (`v ⇁ (v' ⇁ c) = (v' ⋆ v) ⇁ c`) and
  `translLeft_counit`.

## Main results

* `Coalgebra.Comodule.transl_transl`: `v ⇀ (u ⇀ m) = (v ⋆ u) ⇀ m`, and `transl_counit`: `ε ⇀ m = m`;
* `Coalgebra.Comodule.transl_bijective`: `u ⇀ -` is bijective when `u` is convolution invertible;
* `Coalgebra.Comodule.isSubcomodule_translSpan` and `Coalgebra.Comodule.translSpan_fg`: over a
  field, the span of the translates of `m` is a finitely generated subcomodule containing `m` — the
  smallest subcomodule containing `m`. This is the fundamental theorem of comodules in a precise
  form.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Section
  3
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter II
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

section
open TensorProduct Coalgebra Coalgebra.Comodule

namespace Coalgebra.Comodule

section Transl

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [AddCommMonoid M] [Module R M] [RightComodule R C M]

/-- The translation operator `u ⇀ m = ∑ u (m₍₁₎) • m₍₀₎` of a functional `u` on a comodule. -/
noncomputable def transl (u : C →ₗ[R] R) : M →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ (LinearMap.lTensor M u) ∘ₗ coact (R := R) (C := C)

/-- On a Sweedler representation of `m`: `u ⇀ m = ∑ u (m₍₁₎) • m₍₀₎`. -/
lemma transl_apply (u : C →ₗ[R] R) {m : M} (r : Repr R C m) :
    transl u m = ∑ i ∈ r.index, u (r.right i) • r.left i := by
  simp [transl, ← r.eq, map_sum]

/-- The convolution product `(v ⋆ u) (c) = ∑ v (c₍₁₎) * u (c₍₂₎)` of two functionals. -/
noncomputable def convFun (v u : C →ₗ[R] R) : C →ₗ[R] R :=
  (LinearMap.mul' R R) ∘ₗ (TensorProduct.map v u) ∘ₗ comul (R := R) (A := C)

/-- On a Sweedler representation of `c`: `(v ⋆ u) c = ∑ v (c₍₁₎) * u (c₍₂₎)`. -/
lemma convFun_apply (v u : C →ₗ[R] R) {c : C} {ι : Type*} (r : Coalgebra.Repr R c ι) :
    convFun v u c = ∑ i ∈ r.index, v (r.left i) * u (r.right i) := by
  simp [convFun, ← r.eq, map_sum]

/-- The counit acts as the identity. -/
lemma transl_counit : (transl (counit : C →ₗ[R] R) : M →ₗ[R] M) = LinearMap.id :=
  Coalgebra.RightComodule.counit_coact (R := R) (C := C) (M := M)

/-- Translating an element of a comodule by the counit fixes the element. -/
@[simp] lemma transl_counit_apply (m : M) :
    transl (counit : C →ₗ[R] R) m = m := by
  rw [transl_counit, LinearMap.id_apply]

/-- Translation turns the convolution product into composition. -/
lemma transl_transl (v u : C →ₗ[R] R) (m : M) :
    transl v (transl u m) = transl (convFun v u) m := by
  classical
  set r := Repr.arbitrary R C m with hr
  set a : (i : r.ι) → Repr R C (r.left i) := fun i => Repr.arbitrary R C (r.left i) with ha
  set b : (i : r.ι) → Coalgebra.Repr R (r.right i) (C × C) := fun i => Coalgebra.Repr.arbitrary R _
      with hb
  -- the linear functional `x ⊗ (h ⊗ h') ↦ (v h * u h') • x`
  set f : M ⊗[R] (C ⊗[R] C) →ₗ[R] M :=
    (TensorProduct.rid R M).toLinearMap ∘ₗ
      LinearMap.lTensor M ((LinearMap.mul' R R) ∘ₗ (TensorProduct.map v u)) with hf
  have hfapply : ∀ (x : M) (h h' : C), f (x ⊗ₜ[R] (h ⊗ₜ[R] h')) = (v h * u h') • x := by
    intro x h h'
    simp [hf]
  have hkey := sum_tmul_tmul_eq r a b
  apply_fun f at hkey
  rw [map_sum] at hkey
  simp only [map_sum, hfapply] at hkey
  -- the left-hand side is `v ⇀ (u ⇀ m)`
  have hleft : transl v (transl u m) = ∑ i ∈ r.index, ∑ j ∈ (a i).index,
      (v ((a i).right j) * u (r.right i)) • (a i).left j := by
    rw [transl_apply u r, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, transl_apply v (a i), Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  -- the right-hand side is `(v ⋆ u) ⇀ m`
  have hright : transl (convFun v u) m = ∑ i ∈ r.index, ∑ j ∈ (b i).index,
      (v ((b i).left j) * u ((b i).right j)) • r.left i := by
    rw [transl_apply (convFun v u) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [convFun_apply v u (b i), Finset.sum_smul]
  rw [hleft, hright, hkey]

/-- Translation by a convolution-invertible functional is bijective. -/
lemma transl_bijective {v u : C →ₗ[R] R} (h1 : convFun v u = (counit : C →ₗ[R] R))
    (h2 : convFun u v = (counit : C →ₗ[R] R)) :
    Function.Bijective (transl u : M →ₗ[R] M) := by
  have leftInverse : Function.LeftInverse (transl v) (transl u : M →ₗ[R] M) :=
    fun x => by rw [transl_transl, h1, transl_counit_apply]
  have rightInverse : Function.RightInverse (transl v) (transl u : M →ₗ[R] M) :=
    fun x => by rw [transl_transl, h2, transl_counit_apply]
  exact ⟨leftInverse.injective, rightInverse.surjective⟩

/-- `u ⇀ -` as an additive equivalence, when `v` is a two-sided convolution inverse of `u`. -/
noncomputable def translAddEquiv {v u : C →ₗ[R] R} (h1 : convFun v u = (counit : C →ₗ[R] R))
    (h2 : convFun u v = (counit : C →ₗ[R] R)) : M ≃+ M :=
  AddEquiv.ofBijective (transl u : M →ₗ[R] M).toAddMonoidHom (transl_bijective h1 h2)
/-- `translAddEquiv h1 h2` acts as the translation `u ⇀ -`. -/
@[simp] lemma translAddEquiv_apply {v u : C →ₗ[R] R} (h1 : convFun v u = (counit : C →ₗ[R] R))
    (h2 : convFun u v = (counit : C →ₗ[R] R)) (m : M) :
    translAddEquiv (M := M) h1 h2 m = transl u m := rfl


end Transl

section TranslSpan

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [RightComodule k C M]

/-- The span of all translates `u ⇀ m` of an element of a comodule. -/
noncomputable def translSpan (m : M) : Submodule k M :=
  Submodule.span k (Set.range fun w : C →ₗ[k] k => transl (R := k) (C := C) w m)

/-- Every translate `w ⇀ m` lies in `translSpan m`. -/
lemma transl_mem_translSpan (w : C →ₗ[k] k) (m : M) : transl (R := k) (C := C) w m ∈ translSpan
    (k := k) (C := C) m :=
  Submodule.subset_span ⟨w, rfl⟩

/-- `m ∈ translSpan m`, since `ε ⇀ m = m`. -/
lemma self_mem_translSpan (m : M) : m ∈ translSpan (k := k) (C := C) m := by
  simpa only [transl_counit_apply] using
    transl_mem_translSpan (counit : C →ₗ[k] k) m

/-- Coordinates of an element of `M ⊗ C` with respect to a `k`-basis `b` of `C`. -/
private noncomputable def basisTensorEquiv {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k C) :
    M ⊗[k] C ≃ₗ[k] (ι →₀ M) :=
  (TensorProduct.congr (LinearEquiv.refl k M) b.repr).trans
    (TensorProduct.finsuppScalarRight k k M ι)

omit [Coalgebra k C] [RightComodule k C M] in
/-- Reconstructing an element of `M ⊗ C` from its `b`-coordinates. -/
private lemma basisTensorEquiv_decomp {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k C)
    (t : M ⊗[k] C) :
    t = ∑ i ∈ (basisTensorEquiv b t).support, (basisTensorEquiv b t i) ⊗ₜ[k] b i := by
  have hφ_tmul : ∀ (y : M) (c : C) (i : ι),
      basisTensorEquiv b (y ⊗ₜ[k] c) i = (b.repr c i) • y := fun y c i => by
    simp [basisTensorEquiv, TensorProduct.finsuppScalarRight_apply_tmul_apply]
  have hφ_symm : ∀ (i : ι) (y : M),
      (basisTensorEquiv b).symm (Finsupp.single i y) = y ⊗ₜ[k] b i := fun i y => by
    apply (basisTensorEquiv b).injective
    rw [LinearEquiv.apply_symm_apply]
    ext j
    rw [hφ_tmul]
    by_cases h : i = j <;> simp [h, eq_comm]
  have h1 : (basisTensorEquiv b).symm
      (∑ i ∈ (basisTensorEquiv b t).support, Finsupp.single i (basisTensorEquiv b t i)) =
      ∑ i ∈ (basisTensorEquiv b t).support, (basisTensorEquiv b t i) ⊗ₜ[k] b i := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hφ_symm i _
  have h2 : ∑ i ∈ (basisTensorEquiv b t).support, Finsupp.single i (basisTensorEquiv b t i) =
      basisTensorEquiv b t := by
    simpa [Finsupp.sum] using Finsupp.sum_single (basisTensorEquiv b t)
  rw [← h1, h2, (basisTensorEquiv b).symm_apply_apply]

/-- The `i₀`-th coordinate of `coact m` with respect to `b` is the translate `b.coord i₀ ⇀ m`. -/
private lemma basisCoord_eq_transl {ι : Type*} (b : Module.Basis ι k C) (m : M)
    (x : ι →₀ M) (hcoact : ∑ i ∈ x.support, (x i) ⊗ₜ[k] b i = coact (R := k) (C := C) m)
    (i₀ : ι) :
    x i₀ = transl (R := k) (C := C) (b.coord i₀) m := by
  classical
  let r : Coalgebra.Comodule.Repr k C m :=
    { ι := ι, index := x.support, left := fun i => x i, right := fun i => b i, eq := hcoact }
  rw [transl_apply _ r]
  change x i₀ = ∑ i ∈ x.support, (b.coord i₀) (b i) • x i
  rw [Finset.sum_congr rfl (g := fun i => if i = i₀ then x i else 0) ?_]
  · rw [Finset.sum_ite_eq' x.support i₀]
    by_cases hi₀ : i₀ ∈ x.support
    · simp [hi₀]
    · simp [hi₀, Finsupp.notMem_support_iff.1 hi₀]
  · intro i _
    by_cases h : i = i₀
    · subst h; simp
    · have hzero : (b.coord i₀) (b i) = 0 := by simp [Module.Basis.coord_apply, h]
      change (b.coord i₀) (b i) • x i = if i = i₀ then x i else 0
      rw [hzero, zero_smul, ite_eq_right h]

/-- Each basis coordinate `x i` of `coact m` has `coact (x i)` in the range of `N ⊗ C → M ⊗ C`,
where `N` is the span of `{x i | i ∈ x.support}`. -/
private lemma coact_basisCoord_mem_range {ι : Type*} (b : Module.Basis ι k C)
    (m : M) (x : ι →₀ M) (hcoact : ∑ i ∈ x.support, (x i) ⊗ₜ[k] b i = coact (R := k) (C := C) m)
    (N : Submodule k M) (hxN : ∀ i : ι, x i ∈ N) (i₀ : ι) :
    coact (R := k) (C := C) (x i₀) ∈ LinearMap.range (LinearMap.rTensor C N.subtype) := by
  classical
  by_cases hi₀ : i₀ ∈ x.support
  · let r : Coalgebra.Comodule.Repr k C m :=
      { ι := ι, index := x.support, left := fun i => x i, right := fun i => b i, eq := hcoact }
    let a : (i : r.ι) → Coalgebra.Comodule.Repr k C (r.left i) :=
      fun i => Coalgebra.Comodule.Repr.arbitrary k C (x i)
    let bb : (i : r.ι) → Coalgebra.Repr k (r.right i) (C × C) := fun i => ℛ k (b i)
    have key := Coalgebra.Comodule.sum_tmul_tmul_eq r a bb
    let Φ : M ⊗[k] (C ⊗[k] C) →ₗ[k] M ⊗[k] C :=
      LinearMap.lTensor M ((TensorProduct.rid k C).toLinearMap ∘ₗ
        LinearMap.lTensor C (b.coord i₀))
    have hΦ : ∀ (u : M) (v w : C), Φ (u ⊗ₜ[k] (v ⊗ₜ[k] w)) = (b.coord i₀ w) • (u ⊗ₜ[k] v) :=
      fun u v w => by simp [Φ, TensorProduct.smul_tmul']
    apply_fun Φ at key
    simp only [map_sum, hΦ] at key
    have hleft : ∑ i ∈ x.support, ∑ j ∈ (a i).index,
        (b.coord i₀ (b i)) • ((a i).left j ⊗ₜ[k] (a i).right j) =
        coact (R := k) (C := C) (x i₀) := by
      rw [Finset.sum_congr rfl (g := fun i => if i = i₀ then
        coact (R := k) (C := C) (x i) else 0) ?_]
      · rw [Finset.sum_ite_eq' x.support i₀]; simp [hi₀]
      · intro i _
        by_cases h : i = i₀
        · subst h; simp only [show b.coord i (b i) = 1 by simp, one_smul]; exact (a i).eq
        · simp only [ite_eq_right h, show b.coord i₀ (b i) = 0 by
            simp [Module.Basis.coord_apply, Ne.symm h], zero_smul, Finset.sum_const_zero]
    rw [hleft] at key
    rw [key]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ ⟨(⟨x i, hxN i⟩ : N) ⊗ₜ[k] (bb i).left j, by simp [r]⟩
  · rw [Finsupp.notMem_support_iff.1 hi₀]; simp

/-- Over a field, the span of the translates of `m` is a finitely generated subcomodule. -/
theorem translSpan_spec (m : M) :
    (translSpan (k := k) (C := C) m).FG ∧
      IsSubcomodule (C := C) (translSpan (k := k) (C := C) m) := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := k) (M := C)
  set x : ι →₀ M := basisTensorEquiv b (coact (R := k) (C := C) m)
  have hcoact : ∑ i ∈ x.support, (x i) ⊗ₜ[k] b i = coact (R := k) (C := C) m :=
    (basisTensorEquiv_decomp b (coact (R := k) (C := C) m)).symm
  let r : Coalgebra.Comodule.Repr k C m :=
    { ι := ι, index := x.support, left := fun i => x i, right := fun i => b i, eq := hcoact }
  have hcoord : ∀ i : ι, x i = transl (R := k) (C := C) (b.coord i) m :=
    basisCoord_eq_transl b m x hcoact
  set N : Submodule k M := Submodule.span k ((x.support.image fun i => x i : Finset M) : Set M)
  have hxN : ∀ i : ι, x i ∈ N := fun i => by
    by_cases hi : i ∈ x.support
    · exact Submodule.subset_span (by simpa using ⟨i, Finsupp.mem_support_iff.1 hi, rfl⟩)
    · rw [Finsupp.notMem_support_iff.1 hi]; exact N.zero_mem
  have hNeq : translSpan (k := k) (C := C) m = N := by
    refine le_antisymm ?_ ?_
    · rw [translSpan, Submodule.span_le]
      rintro - ⟨w, rfl⟩
      rw [show (fun w : C →ₗ[k] k => transl (R := k) (C := C) w m) w =
        ∑ i ∈ x.support, w (b i) • x i from transl_apply w r]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxN i)
    · rw [Submodule.span_le]
      intro y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
      obtain ⟨i, _, rfl⟩ := hy
      rw [hcoord i]
      exact transl_mem_translSpan _ m
  refine ⟨hNeq ▸ ⟨_, rfl⟩, ?_⟩
  rw [hNeq]
  intro y hy
  refine Submodule.span_induction (p := fun z _ =>
    coact (R := k) (C := C) z ∈ LinearMap.range (LinearMap.rTensor C N.subtype)) ?_ ?_ ?_ ?_ hy
  · rintro z hz
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact coact_basisCoord_mem_range b m x hcoact N hxN i
  · simp
  · intro u v _ _ hu hv; rw [map_add]; exact Submodule.add_mem _ hu hv
  · intro c u _ hu; rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- Over a field, `translSpan m` is finitely generated. -/
lemma translSpan_fg (m : M) : (translSpan (k := k) (C := C) m).FG := (translSpan_spec m).1

/-- Over a field, `translSpan m` is a subcomodule. -/
lemma isSubcomodule_translSpan (m : M) : IsSubcomodule (C := C) (translSpan (k := k) (C := C) m) :=
  (translSpan_spec m).2

end TranslSpan

end Coalgebra.Comodule

/-! ## Left translation of a coalgebra by a functional -/

namespace Coalgebra

section TranslLeft

variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The *left* translation operator `v ⇁ c = ∑ v (c₍₁₎) c₍₂₎` of a functional on a coalgebra.
(The operator `Coalgebra.Comodule.transl` is its right-handed counterpart.) -/
noncomputable def translLeft (w : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap ∘ₗ (LinearMap.rTensor C w) ∘ₗ comul (R := R) (A := C)

/-- On a Sweedler representation of `c`: `translLeft w c = ∑ w (c₍₁₎) • c₍₂₎`. -/
lemma translLeft_apply (w : C →ₗ[R] R) {c : C} {ι : Type*} (r : Coalgebra.Repr R c ι) :
    translLeft w c = ∑ i ∈ r.index, w (r.left i) • r.right i := by
  simp [translLeft, ← r.eq, map_sum]

/-- Left translation turns the convolution product into composition. -/
lemma translLeft_translLeft (v v' : C →ₗ[R] R) (c : C) :
    translLeft v (translLeft v' c) = translLeft (Coalgebra.Comodule.convFun v' v) c := by
  classical
  set r := Coalgebra.Repr.arbitrary R c with hr
  set a : (i : C × C) → Coalgebra.Repr R (r.left i) (C × C) := fun i => Coalgebra.Repr.arbitrary R _
      with ha
  set b : (i : C × C) → Coalgebra.Repr R (r.right i) (C × C) := fun i => Coalgebra.Repr.arbitrary R
      _ with hb
  -- Apply coassociativity to the contraction of the first two tensor factors.
  set g : C ⊗[R] C →ₗ[R] C :=
    (TensorProduct.lid R C).toLinearMap ∘ₗ (LinearMap.rTensor C v) with hg
  set f : C ⊗[R] (C ⊗[R] C) →ₗ[R] C :=
    (TensorProduct.lid R C).toLinearMap ∘ₗ (TensorProduct.map v' g) with hf
  have hfapply : ∀ x y z : C, f (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (v' x * v y) • z := by
    intro x y z
    simp only [hf, hg, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, mul_smul]
  have hkey := Coalgebra.sum_tmul_tmul_eq r a b
  apply_fun f at hkey
  rw [map_sum] at hkey
  simp only [map_sum, hfapply] at hkey
  have hleft : translLeft v (translLeft v' c)
      = ∑ i ∈ r.index, ∑ j ∈ (b i).index, (v' (r.left i) * v ((b i).left j)) • (b i).right j := by
    rw [translLeft_apply v' r, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, translLeft_apply v (b i), Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  have hright : translLeft (Coalgebra.Comodule.convFun v' v) c
      = ∑ i ∈ r.index, ∑ j ∈ (a i).index,
          (v' ((a i).left j) * v ((a i).right j)) • r.right i := by
    rw [translLeft_apply (Coalgebra.Comodule.convFun v' v) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Coalgebra.Comodule.convFun_apply v' v (a i), Finset.sum_smul]
  rw [hleft, hright, ← hkey]

/-- The counit acts as the identity. -/
lemma translLeft_counit : (translLeft (counit : C →ₗ[R] R) : C →ₗ[R] C) = LinearMap.id := by
  classical
  ext c
  rw [translLeft_apply _ (Coalgebra.Repr.arbitrary R c)]
  simpa using Coalgebra.sum_counit_smul (R := R) (Coalgebra.Repr.arbitrary R c)

end TranslLeft

end Coalgebra

end
