module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Two general descent lemmas for faithful flatness

This file contains the two pieces of commutative algebra needed in Takeuchi's proof of his
Theorem 3.1 (the characteristic-`p` reduction), both independent of Hopf algebra theory, and
the descent step that combines them.

## Main results

* `Module.FaithfullyFlat.faithfullyFlat_tensorRight_ringHom`: if `M` is faithfully flat over `L`,
  then `M ⊗[k] H` is faithfully flat over `L ⊗[k] H` for every `k`-algebra `H` — the base change of
  `L → M` along `L → L ⊗[k] H`.
* `Module.FaithfullyFlat.faithfullyFlat_of_faithfullyFlat_tensorSelf`: for `A → K → H` with
  `H ⊗[A] H` faithfully flat over `K`, the algebra `H` itself is faithfully flat over `K`. Indeed
  `H` is a `K`-module retract of `H ⊗[A] H` (via `h ↦ h ⊗ 1` and the multiplication map), so it is
  flat, and the surjectivity of `Spec (H ⊗[A] H) → Spec K` forces `Spec H → Spec K` to be
  surjective.
* `Module.FaithfullyFlat.faithfullyFlat_of_mixed_square`: the descent step in Takeuchi's proof of
  his Theorem 3.1: for `A → K → H` with `H` faithfully flat over `A`, a commuting square of ring
  isomorphisms `K ⊗[A] H ≅ L ⊗[k] H`, `H ⊗[A] H ≅ M ⊗[k] H` with `M` faithfully flat over `L` makes
  `H` faithfully flat over `K`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  3.1
-/

@[expose] public section

namespace Module.FaithfullyFlat

open TensorProduct

/-- The composite of two faithfully flat ring maps is faithfully flat. This is Mathlib's
`RingHom.FaithfullyFlat.stableUnderComposition`, stated with the maps' rings as explicit
`CommRing`s: Mathlib's form does not elaborate at the uses below, where the property in
`RingHom.StableUnderComposition` stays an unreduced lambda. -/
theorem ringHom_faithfullyFlat_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : RingHom.FaithfullyFlat f)
    (hg : RingHom.FaithfullyFlat g) : RingHom.FaithfullyFlat (g.comp f) := by
  algebraize [f, g, g.comp f]
  rw [← RingHom.algebraMap_toAlgebra (g.comp f), RingHom.faithfullyFlat_algebraMap_iff]
  have h1 : Module.FaithfullyFlat R S := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]; rwa [RingHom.algebraMap_toAlgebra]
  have h2 : Module.FaithfullyFlat S T := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]; rwa [RingHom.algebraMap_toAlgebra]
  exact Module.FaithfullyFlat.trans R S T

section TensorRight

variable (k L M H : Type*) [CommRing k] [CommRing L] [CommRing M] [CommRing H]
  [Algebra k L] [Algebra k M] [Algebra k H] [Algebra L M] [IsScalarTower k L M]

/-- The `k`-algebra map `L ⊗[k] H → M ⊗[k] H` induced by `L → M`. -/
noncomputable abbrev tensorRightMap : L ⊗[k] H →ₐ[k] M ⊗[k] H :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L M) (AlgHom.id k H)

/-- **Faithful flatness is stable under tensoring on the right**: if `M` is faithfully flat over
`L`, then `M ⊗[k] H` is faithfully flat over `L ⊗[k] H`. -/
theorem faithfullyFlat_tensorRight_ringHom [Module.FaithfullyFlat L M] :
    RingHom.FaithfullyFlat (tensorRightMap k L M H).toRingHom := by
  -- Base change of `L → M` along `L → L ⊗[k] H` is faithfully flat, and it is identified
  -- with `M ⊗[k] H` by `e`, which sends `z ⊗ 1` to `tensorRightMap z`.
  have : Module.FaithfullyFlat (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M) :=
    Module.FaithfullyFlat.instTensorProduct L M (L ⊗[k] H)
  set e : ((L ⊗[k] H) ⊗[L] M) ≃ₐ[L] (M ⊗[k] H) :=
    (Algebra.TensorProduct.comm L (L ⊗[k] H) M).trans
      (Algebra.TensorProduct.cancelBaseChange k L L M H) with he
  have hgen : ∀ z : L ⊗[k] H, e (z ⊗ₜ[L] (1 : M)) = tensorRightMap k L M H z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [he]
      simp [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
    | add u v hu hv =>
      rw [TensorProduct.add_tmul, map_add, map_add, hu, hv]
  have hsq : ∀ z : L ⊗[k] H,
      e (algebraMap (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M) z) = tensorRightMap k L M H z := by
    intro z
    have hz : algebraMap (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M) z = z ⊗ₜ[L] (1 : M) := by
      simp [Algebra.TensorProduct.algebraMap_apply (S := L ⊗[k] H) (R := L) (B := M)]
    rw [hz]
    exact hgen z
  -- The composite of the base change with the isomorphism is `tensorRightMap`.
  have h1 := (RingHom.faithfullyFlat_algebraMap_iff (R := L ⊗[k] H)
      (S := (L ⊗[k] H) ⊗[L] M)).2
      (inferInstance : Module.FaithfullyFlat (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M))
  let g : @RingHom ((L ⊗[k] H) ⊗[L] M) (M ⊗[k] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    e.toRingEquiv.toRingHom
  have hgz : ∀ z, g z = e z := fun _ => rfl
  have h2 : RingHom.FaithfullyFlat g := RingHom.FaithfullyFlat.of_bijective e.bijective
  let f1 : @RingHom (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    algebraMap (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M)
  have hf1z : ∀ z, f1 z = algebraMap (L ⊗[k] H) ((L ⊗[k] H) ⊗[L] M) z := fun _ => rfl
  have h1' : RingHom.FaithfullyFlat f1 := h1
  have h3 := ringHom_faithfullyFlat_comp f1 g h1' h2
  have heq : g.comp f1 = (tensorRightMap k L M H).toRingHom :=
    RingHom.ext fun z => (hgz _).trans ((congr(e $(hf1z z))).trans (hsq z))
  rwa [heq] at h3

end TensorRight

section Retract

variable {A K H : Type*} [CommRing A] [CommRing K] [CommRing H] [Algebra A K] [Algebra A H]
  [Algebra K H] [IsScalarTower A K H]

/-- The multiplication map `H ⊗[A] H → H` as a `K`-algebra map. -/
noncomputable def tensorSelfMul : H ⊗[A] H →ₐ[K] H :=
  Algebra.TensorProduct.lift (AlgHom.id K H) (AlgHom.id A H) fun x y => mul_comm x y
/-- The multiplication map `tensorSelfMul` sends `x ⊗ₜ[A] y` to `x * y`. -/
@[simp] lemma tensorSelfMul_tmul (x y : H) :
    (tensorSelfMul (A := A) (K := K)) (x ⊗ₜ[A] y) = x * y := rfl

/-- `H` is a retract of `H ⊗[A] H` as a `K`-module, hence flat over `K` as soon as `H ⊗[A] H`
is. -/
theorem flat_of_flat_tensorSelf [Module.Flat K (H ⊗[A] H)] : Module.Flat K H :=
  Module.Flat.of_retract
    (Algebra.TensorProduct.includeLeft (S := K) (R := A) (A := H) (B := H)).toLinearMap
    (tensorSelfMul (A := A) (K := K)).toLinearMap
    (by ext x; simp)

/-- **Descent of faithful flatness through the cokernel pair**: if `H ⊗[A] H` is faithfully flat
over `K`, then so is `H`. -/
theorem faithfullyFlat_of_faithfullyFlat_tensorSelf
    [Module.FaithfullyFlat K (H ⊗[A] H)] : Module.FaithfullyFlat K H := by
  have : Module.Flat K H := flat_of_flat_tensorSelf (A := A)
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  have hcomp : (algebraMap K (H ⊗[A] H))
      = (algebraMap H (H ⊗[A] H)).comp (algebraMap K H) := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one, IsScalarTower.algebraMap_apply K H (H ⊗[A] H)]
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap K (H ⊗[A] H))) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  rw [hcomp, PrimeSpectrum.comap_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

end Retract

section MixedSquare

variable {k A K H L M : Type*} [CommRing k] [CommRing A] [CommRing K] [CommRing H]
  [CommRing L] [CommRing M]
  [Algebra A K] [Algebra A H] [Algebra K H] [IsScalarTower A K H]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M] [Algebra k H]

/-- The map `K ⊗[A] H → H ⊗[A] H` induced by the structure map `K → H`. -/
noncomputable abbrev tensorLeftMap : K ⊗[A] H →ₐ[A] H ⊗[A] H :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A K H) (AlgHom.id A H)

/-- **The descent step in Takeuchi's proof of Theorem 3.1** [Takeuchi1972].  Suppose `A → K → H` are
commutative rings with `H` faithfully flat over `A`, and that the square
```
K ⊗[A] H → H ⊗[A] H
   ≅           ≅
L ⊗[k] H → M ⊗[k] H
```
commutes, where `M` is faithfully flat over `L`.  Then `H` is faithfully flat over `K`. -/
theorem faithfullyFlat_of_mixed_square [Module.FaithfullyFlat A H] [Module.FaithfullyFlat L M]
    (α : (K ⊗[A] H) ≃+* (L ⊗[k] H)) (β : (H ⊗[A] H) ≃+* (M ⊗[k] H))
    (hsq : ∀ z : K ⊗[A] H, β (tensorLeftMap z) = tensorRightMap k L M H (α z)) :
    Module.FaithfullyFlat K H := by
  -- The composite `b ∘ s ∘ a` around the square is faithfully flat and equals `K ⊗ H → H ⊗ H`.
  have hs0 := faithfullyFlat_tensorRight_ringHom k L M H
  let a : @RingHom (K ⊗[A] H) (L ⊗[k] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    α.toRingHom
  have haz : ∀ z, a z = α z := fun _ => rfl
  let b : @RingHom (M ⊗[k] H) (H ⊗[A] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    β.symm.toRingHom
  have hbz : ∀ z, b z = β.symm z := fun _ => rfl
  let s : @RingHom (L ⊗[k] H) (M ⊗[k] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    (tensorRightMap k L M H).toRingHom
  have hsz : ∀ z, s z = tensorRightMap k L M H z := fun _ => rfl
  have hs : RingHom.FaithfullyFlat s := hs0
  have ha : RingHom.FaithfullyFlat a := RingHom.FaithfullyFlat.of_bijective (f := a) α.bijective
  have hb : RingHom.FaithfullyFlat b :=
    RingHom.FaithfullyFlat.of_bijective (f := b) β.symm.bijective
  have hcomp : RingHom.FaithfullyFlat (b.comp (s.comp a)) :=
    ringHom_faithfullyFlat_comp _ _ (ringHom_faithfullyFlat_comp _ _ ha hs) hb
  let i : @RingHom (K ⊗[A] H) (H ⊗[A] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    (tensorLeftMap (A := A) (K := K) (H := H)).toRingHom
  have hiz : ∀ z, i z = tensorLeftMap (A := A) (K := K) (H := H) z := fun _ => rfl
  have hieq : b.comp (s.comp a) = i := by
    refine RingHom.ext fun z => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, haz, hsz, hbz, hiz, ← hsq z]
    exact β.symm_apply_apply _
  rw [hieq] at hcomp
  -- Precomposed with the faithfully flat `K → K ⊗[A] H`, it is the structure map `K → H ⊗[A] H`.
  let f0 : @RingHom K (K ⊗[A] H)
      CommRing.toCommSemiring.toNonAssocSemiring CommRing.toCommSemiring.toNonAssocSemiring :=
    algebraMap K (K ⊗[A] H)
  have hf0z : ∀ x, f0 x = algebraMap K (K ⊗[A] H) x := fun _ => rfl
  have hf0 : RingHom.FaithfullyFlat f0 :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := K) (S := K ⊗[A] H)).2
      (Module.FaithfullyFlat.instTensorProduct A H K)
  have hfin : RingHom.FaithfullyFlat (i.comp f0) :=
    ringHom_faithfullyFlat_comp _ _ hf0 hcomp
  have hfineq : i.comp f0 = algebraMap K (H ⊗[A] H) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hf0z, hiz]
    rw [Algebra.TensorProduct.algebraMap_apply (R := A) (S := K) (A := K) (B := H) x,
      Algebra.TensorProduct.algebraMap_apply (R := A) (S := K) (A := H) (B := H) x]
    simp
  rw [hfineq] at hfin
  have : Module.FaithfullyFlat K (H ⊗[A] H) :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := K) (S := H ⊗[A] H)).1 hfin
  exact faithfullyFlat_of_faithfullyFlat_tensorSelf (A := A)

end MixedSquare

end Module.FaithfullyFlat
