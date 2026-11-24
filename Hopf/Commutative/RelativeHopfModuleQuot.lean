module

public import Hopf.Basic.SubComodule
public import Hopf.Basic.RelativeHopfFlat
public import Hopf.Basic.ComoduleTensor
public import Foundations.RingTheory.FlatDirectedUnion
public import Foundations.RingTheory.FlatQuotientPurity

/-!
# Takeuchi's Proposition 2.4

Let `k` be a field, `H` a `k`-bialgebra and `K` a `k`-bialgebra with a morphism of bialgebras
`φ : K →ₐc[k] H` which makes `H` a `K`-algebra (in Takeuchi's situation `K` is a sub-Hopf algebra
of `H` and `φ` is the inclusion).

**Proposition 2.4** of M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*
(manuscripta math. **7** (1972), 251–270): if every relative `(H,K)`-Hopf module which is finitely
generated as a `K`-module is a flat `K`-module, then `H` is a faithfully flat `K`-module.

Takeuchi's proof is formalised here. By Corollary 2.3 (in the form of
`Coalgebra.Comodule.exists_fg_subcomodule_finite` together with
`HopfAlgebra.IsRelativeHopfModule.isSubcomodule_span`) every relative Hopf module is the filtered
union of its finitely generated sub-Hopf-modules, hence is flat; this applies both to `H` itself and
to the quotient `H ⧸ K`, which is again a relative Hopf module because the image of `K` is a
subcomodule of `H`. Flatness of `H ⧸ K` makes the inclusion `K → H` pure
(`Module.FaithfullyFlat.mem_ideal_smul_of_mem_of_flat_quotient`), which upgrades flatness to
faithful flatness (`Module.FaithfullyFlat.faithfullyFlat_of_flat_quotient`).

## Main definitions

* `HopfAlgebra.Commutative.RelativeHopfModulesFlat`: the hypothesis of Proposition 2.4;
* `Coalgebra.Comodule.quotComodule`: the comodule structure of a quotient by a subcomodule.

## Main results

* `HopfAlgebra.Commutative.isRelativeHopfModule_quot`: a quotient of a relative Hopf module by a
  sub-Hopf-module is a relative Hopf module;
* `HopfAlgebra.Commutative.isRelativeHopfModule_self`: `H` is a relative `(H,K)`-Hopf module;
* `HopfAlgebra.Commutative.isSubcomodule_rangeAlgebraMap`: the image of `K` in `H` is a subcomodule;
* `HopfAlgebra.IsRelativeHopfModule.flat_of_relativeHopfModulesFlat`: every relative
  Hopf module is flat as soon as the finitely generated ones are;
* `HopfAlgebra.Commutative.faithfullyFlat_of_relativeHopfModulesFlat`: **Takeuchi's Proposition
  2.4**.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Corollary 2.3, Propositions 2.4 and 2.5
-/

@[expose] public section

section
open Coalgebra Coalgebra.Comodule HopfAlgebra

open TensorProduct _root_.Coalgebra

namespace Coalgebra.Comodule

section Sup

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [AddCommGroup M] [Module k M]

/-- Membership in `N ⊗ C` is monotone in the submodule `N`. -/
lemma mem_range_rTensor_mono {N P : Submodule k M} (h : N ≤ P) {t : M ⊗[k] C}
    (ht : t ∈ LinearMap.range (LinearMap.rTensor C N.subtype)) :
    t ∈ LinearMap.range (LinearMap.rTensor C P.subtype) := by
  obtain ⟨s, rfl⟩ := ht
  refine ⟨LinearMap.rTensor C (Submodule.inclusion h) s, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

variable [Coalgebra k C] [RightComodule k C M]

/-- The zero submodule is a subcomodule. -/
lemma isSubcomodule_bot : IsSubcomodule (C := C) (⊥ : Submodule k M) := by
  intro x hx
  rw [Submodule.mem_bot] at hx
  subst hx
  exact ⟨0, by simp⟩

/-- The sum of two subcomodules is a subcomodule. -/
lemma IsSubcomodule.sup {N P : Submodule k M} (hN : IsSubcomodule (C := C) N)
    (hP : IsSubcomodule (C := C) P) : IsSubcomodule (C := C) (N ⊔ P) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem _ (mem_range_rTensor_mono le_sup_left (hN a ha))
    (mem_range_rTensor_mono le_sup_right (hP b hb))

/-- A finite family of elements of a comodule over a field is contained in a finitely generated
subcomodule. -/
theorem exists_fg_subcomodule_finite (l : ℕ) (x : Fin l → M) :
    ∃ N : Submodule k M, (∀ i, x i ∈ N) ∧ N.FG ∧ IsSubcomodule (C := C) N := by
  induction l with
  | zero => exact ⟨⊥, fun i => i.elim0, Submodule.fg_bot, isSubcomodule_bot⟩
  | succ n ih =>
    obtain ⟨N, hN, hNfg, hNsub⟩ := ih (fun i => x i.succ)
    obtain ⟨P, hP, hPfg, hPsub⟩ := exists_fg_subcomodule (k := k) (C := C) (M := M) (x 0)
    refine ⟨N ⊔ P, fun i => ?_, hNfg.sup hPfg, hNsub.sup hPsub⟩
    refine Fin.cases ?_ ?_ i
    · exact Submodule.mem_sup_right hP
    · exact fun j => Submodule.mem_sup_left (hN j)

end Sup

section Quot

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [RightComodule k C M]

variable {R : Type*} [CommRing R] [Algebra k R] [Module R M] [IsScalarTower k R M]
  {W : Submodule R M} (hW : IsSubcomodule (C := C) (W.restrictScalars k))

include hW

/-- The coaction of the quotient of a comodule by a subcomodule. -/
noncomputable def quotCoact : (M ⧸ W) →ₗ[k] (M ⧸ W) ⊗[k] C :=
  (W.restrictScalars k).liftQ
    ((LinearMap.rTensor C (W.mkQ.restrictScalars k))
        ∘ₗ (Coalgebra.RightComodule.coact (R := k) (C := C)))
    (by
      intro w hw
      obtain ⟨s, hs⟩ := hW w hw
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, ← hs]
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      have : (W.mkQ.restrictScalars k) ∘ₗ (W.restrictScalars k).subtype = 0 := by
        ext y
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
          LinearMap.coe_restrictScalars, Submodule.mkQ_apply, LinearMap.zero_apply,
          Submodule.Quotient.mk_eq_zero]
        exact y.2
      rw [this]
      simp)

/-- `quotCoact [m] = (π ⊗ id) (coact m)`, for the quotient map `π : M → M ⧸ W`. -/
@[simp] lemma quotCoact_mk (m : M) :
    quotCoact hW (W.mkQ m) = LinearMap.rTensor C (W.mkQ.restrictScalars k)
      (Coalgebra.RightComodule.coact (R := k) (C := C) m) := rfl

/-- The quotient of a comodule by a subcomodule is a comodule. -/
@[instance_reducible]
noncomputable def quotComodule : RightComodule k C (M ⧸ W) :=
  Coalgebra.RightComodule.ofSurjective (W.mkQ.restrictScalars k)
    (Submodule.mkQ_surjective W) (quotCoact hW) (fun m => quotCoact_mk hW m)

end Quot

end Coalgebra.Comodule

namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

section Naturality

variable {k K H M Q : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [AddCommGroup M] [Module k M] [Module K M]
  [IsScalarTower k K M] [AddCommGroup Q] [Module k Q] [Module K Q] [IsScalarTower k K Q]
  {φ : K →ₐc[k] H}

/-- The map used to state the axiom of a relative Hopf module is natural in the module: it
commutes with `π ⊗ id` for a `K`-linear map `π`. -/
lemma rTensor_relCompat (π : M →ₗ[k] Q) (hπ : ∀ (x : K) (m : M), π (x • m) = x • π m)
    (u : K ⊗[k] K) (t : M ⊗[k] H) :
    LinearMap.rTensor H π (relCompat k K H M φ (u ⊗ₜ[k] t))
      = relCompat k K H Q φ (u ⊗ₜ[k] LinearMap.rTensor H π t) := by
  induction u with
  | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  | tmul a b =>
    induction t with
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
    | tmul m h =>
      simp only [relCompat_tmul, LinearMap.rTensor_tmul]
      rw [hπ]

end Naturality

section Quot

variable {k K H M : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [AddCommGroup M] [Module k M] [Module K M]
  [IsScalarTower k K M] [RightComodule k H M] {φ : K →ₐc[k] H}

/-- A quotient of a relative `(H,K)`-Hopf module by a `K`-submodule which is a subcomodule is
again a relative `(H,K)`-Hopf module. -/
theorem isRelativeHopfModule_quot (hM : IsRelativeHopfModule k K H M φ) (W : Submodule K M)
    (hW : IsSubcomodule (C := H) (W.restrictScalars k)) :
    letI : RightComodule k H (M ⧸ W) := Coalgebra.Comodule.quotComodule hW
    IsRelativeHopfModule k K H (M ⧸ W) φ := by
  let : RightComodule k H (M ⧸ W) := Coalgebra.Comodule.quotComodule hW
  intro x q
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective W q
  have hcoact : ∀ m : M, coact (R := k) (C := H) (W.mkQ m)
      = LinearMap.rTensor H (W.mkQ.restrictScalars k) (coact (R := k) (C := H) m) :=
    fun m => Coalgebra.Comodule.quotCoact_mk hW m
  have hsmul : x • W.mkQ m = W.mkQ (x • m) := rfl
  rw [hsmul, hcoact, hcoact, hM x m]
  exact rTensor_relCompat (φ := φ) (W.mkQ.restrictScalars k) (fun y n => rfl) _ _

end Quot

section Self

variable {k K H : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [Algebra K H] [IsScalarTower k K H]
  (φ : K →ₐc[k] H)

/-- The compatibility map of a relative Hopf module, computed on `H` itself: it is the product
in `H ⊗ H` of the image of the first argument and the second argument. -/
lemma relCompat_self (hφ : ∀ x : K, φ x = algebraMap K H x) (u : K ⊗[k] K) (t : H ⊗[k] H) :
    relCompat k K H H φ (u ⊗ₜ[k] t)
      = (map (φ : K →ₗ[k] H) (φ : K →ₗ[k] H) u) * t := by
  induction u with
  | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv, add_mul]
  | tmul a b =>
    induction t with
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs, mul_add]
    | tmul c d =>
      have hac : a • c = φ a * c := by rw [Algebra.smul_def, hφ]
      simp only [relCompat_tmul, TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, hac]
      rfl

/-- **`H` is a relative `(H,K)`-Hopf module** over itself, the coaction being the
comultiplication. -/
theorem isRelativeHopfModule_self (hφ : ∀ x : K, φ x = algebraMap K H x) :
    IsRelativeHopfModule k K H H φ := by
  intro x m
  have hsmul : x • m = φ x * m := by rw [hφ, Algebra.smul_def]
  have hcoact : ∀ h : H, coact (R := k) (C := H) h = comul (R := k) h := fun _ => rfl
  rw [hcoact, hcoact, hsmul, Bialgebra.comul_mul, relCompat_self φ hφ]
  congr 1
  exact (CoalgHomClass.map_comp_comul_apply φ x).symm

end Self

section RangeSubcomodule

variable {k K H : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [Algebra K H] [IsScalarTower k K H]
  (φ : K →ₐc[k] H)

/-- The image of `K` in `H` is a subcomodule of `H`. -/
theorem isSubcomodule_rangeAlgebraMap (hφ : ∀ x : K, φ x = algebraMap K H x) :
    IsSubcomodule (C := H)
      ((LinearMap.range (Algebra.linearMap K H)).restrictScalars k) := by
  set N : Submodule k H := (LinearMap.range (Algebra.linearMap K H)).restrictScalars k with hN
  have hmem : ∀ x : K, φ x ∈ N := fun x => ⟨x, (hφ x).symm⟩
  -- the corestriction of `φ` to `N`
  set ψ : K →ₗ[k] ↥N := LinearMap.codRestrict N (φ : K →ₗ[k] H) hmem with hψ
  rintro y hy
  obtain ⟨x, rfl⟩ : ∃ x : K, algebraMap K H x = y := hy
  have hy' : (algebraMap K H x) = φ x := (hφ x).symm
  refine ⟨(map ψ (φ : K →ₗ[k] H)) (comul (R := k) x), ?_⟩
  have hcomp : (LinearMap.rTensor H N.subtype) ∘ₗ (map ψ (φ : K →ₗ[k] H))
      = map (φ : K →ₗ[k] H) (φ : K →ₗ[k] H) := by
    ext a b
    simp [hψ]
    rfl
  rw [← LinearMap.comp_apply, hcomp, hy']
  exact CoalgHomClass.map_comp_comul_apply φ x

end RangeSubcomodule

section Prop24

universe u

variable (k K H : Type u) [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] (φ : K →ₐc[k] H)

/-- The hypothesis of Takeuchi's Proposition 2.4: every relative `(H,K)`-Hopf module which is
finitely generated as a `K`-module is a flat `K`-module. -/
def RelativeHopfModulesFlat : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module k M] [Module K M] [IsScalarTower k K M]
    [RightComodule k H M], IsRelativeHopfModule k K H M φ → Module.Finite K M → Module.Flat K M

variable {k K H φ}

/-- Under the hypothesis of Proposition 2.4, *every* relative Hopf module is flat: by Takeuchi's
Corollary 2.3 it is the filtered union of finitely generated ones. -/
theorem _root_.HopfAlgebra.IsRelativeHopfModule.flat_of_relativeHopfModulesFlat
    (hyp : RelativeHopfModulesFlat k K H φ) {M : Type u} [AddCommGroup M] [Module k M]
    [Module K M] [IsScalarTower k K M] [RightComodule k H M]
    (hM : IsRelativeHopfModule k K H M φ) : Module.Flat K M := by
  refine Module.Flat.flat_of_forall_finite_flat_submodule (fun l x => ?_)
  obtain ⟨V, hV, hVfg, hVsub⟩ :=
    Coalgebra.Comodule.exists_fg_subcomodule_finite (k := k) (C := H) (M := M) l x
  refine ⟨Submodule.span K (V : Set M), fun i => Submodule.subset_span (hV i), ?_⟩
  set W : Submodule K M := Submodule.span K (V : Set M) with hW
  have hWfg : W.FG := by
    obtain ⟨s, hs⟩ := hVfg
    exact ⟨s, by rw [hW, ← hs, Submodule.span_span_of_tower k]⟩
  have hWsub : IsSubcomodule (C := H) (W.restrictScalars k) := hM.isSubcomodule_span V hVsub
  let : RightComodule k H ↥W := Coalgebra.Comodule.subComodule hWsub
  have : Module.Finite K ↥W := Module.Finite.iff_fg.2 hWfg
  exact hyp ↥W (isRelativeHopfModule_sub hM W hWsub) inferInstance

variable [Algebra K H] [IsScalarTower k K H]

/-- **Takeuchi's Proposition 2.4** [Takeuchi1972]: if every relative `(H,K)`-Hopf module which is
finitely generated over `K` is flat, then `H` is a faithfully flat `K`-module. -/
theorem faithfullyFlat_of_relativeHopfModulesFlat (hyp : RelativeHopfModulesFlat k K H φ)
    (hφ : ∀ x : K, φ x = algebraMap K H x)
    (hinj : Function.Injective (algebraMap K H)) :
    Module.FaithfullyFlat K H := by
  have hself : IsRelativeHopfModule k K H H φ := isRelativeHopfModule_self φ hφ
  have hflat : Module.Flat K H := hself.flat_of_relativeHopfModulesFlat hyp
  -- the quotient `H ⧸ K` is again a relative Hopf module, hence flat
  set N : Submodule K H := LinearMap.range (Algebra.linearMap K H) with hN
  have hNsub : IsSubcomodule (C := H) (N.restrictScalars k) :=
    isSubcomodule_rangeAlgebraMap φ hφ
  let : RightComodule k H (H ⧸ N) := Coalgebra.Comodule.quotComodule hNsub
  have hquot : IsRelativeHopfModule k K H (H ⧸ N) φ :=
    isRelativeHopfModule_quot hself N hNsub
  have : Module.Flat K (H ⧸ N) := hquot.flat_of_relativeHopfModulesFlat hyp
  exact Module.FaithfullyFlat.faithfullyFlat_of_flat_quotient K H hinj

end Prop24

section Equivalence

universe u

variable {k K H : Type u} [Field k] [CommRing K] [CommRing H] [Bialgebra k K] [HopfAlgebra k H]
  [Algebra K H] [IsScalarTower k K H] (φ : K →ₐc[k] H)

end Equivalence

end HopfAlgebra.Commutative

end
