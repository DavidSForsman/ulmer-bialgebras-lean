module

public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Cocommutative.Descent
public import Hopf.Cocommutative.AntipodeAntiMul
public import Hopf.Cocommutative.CoinvAntipode
public import Hopf.Basic.HopfGaloisMap

/-!
# The Galois map of a cocommutative Hopf algebra is surjective

Let `H` be a Hopf algebra over a field `k`.  `Hopf/Cocommutative/Descent.lean` attaches to a
quotient `π : H ↠ H ⧸ I` the Galois map

```
β : H ⊗ H → H ⊗ (H ⧸ I),   x ⊗ y ↦ ∑ x₁ y ⊗ π x₂
```

and shows that Newman's closure identity `μ (τ K) = K` follows from injectivity of the induced
map `H ⊗_K H → H ⊗ (H ⧸ τ K)` together with descent along `K ⊆ H`.  This file analyses `β`
itself.  It factors as

```
β = (1 ⊗ π) ∘ α,     α : H ⊗ H → H ⊗ H,  x ⊗ y ↦ ∑ x₁ y ⊗ x₂
```

and the **un-quotiented Galois map `α` is bijective as soon as `H` is cocommutative**: it is
conjugate, by the antipode and the flip, to the classical Galois map
`β₀ : b ⊗ c ↦ ∑ b c₁ ⊗ c₂` of `Hopf/Basic/HopfGaloisMap.lean`, which is bijective for
an arbitrary Hopf algebra.  (The conjugation uses that the antipode of a cocommutative Hopf
algebra is an involutive morphism of coalgebras and an anti-morphism of algebras — the results of
`Hopf/Cocommutative/AntipodeAntiMul.lean` and `Hopf/Cocommutative/CoinvAntipode.lean`.)

Consequences:

* `HopfAlgebra.Cocommutative.galFull_bijective` — `α` is bijective, so `β` is surjective for every
  `I`, i.e. `H` is "Hopf–Galois up to injectivity" over any sub-Hopf algebra;
* `HopfAlgebra.Cocommutative.ker_gal_eq_comap` — `ker β = α⁻¹ (H ⊗ I)`;
* `HopfAlgebra.Cocommutative.ker_gal_le_balRel_iff` — the injectivity hypothesis of the descent
  theorem is *equivalent* to the concrete statement `H ⊗ H K⁺ ⊆ α (balanced relations)`;
* `HopfAlgebra.Cocommutative.coinv_tau_eq_of_rightTensor_le_of_descent` — Newman's closure identity
  `μ (τ K) = K` from that statement together with descent.

## Main results

* `HopfAlgebra.Cocommutative.galFull_bijective`: for a cocommutative `H`, the un-quotiented Galois
  map `α` is bijective.
* `HopfAlgebra.Cocommutative.ker_gal_eq_comap`: `ker β = α⁻¹ (H ⊗ I)`.
* `HopfAlgebra.Cocommutative.ker_gal_le_balRel_iff`: for a subalgebra `K` of a cocommutative `H`,
  the kernel of the Galois map of `τ K` lies in the `K`-balanced relations if and only if `H ⊗ τ K`
  lies in the image under `α` of the `K`-balanced relations.
* `HopfAlgebra.Cocommutative.coinv_tau_eq_of_rightTensor_le_of_descent`: Newman's closure identity
  `μ (τ K) = K` for a sub-bialgebra `K` of a cocommutative `H`, from that inclusion together with
  descent along `K ⊆ H`.

## References

* [S. U. Chase, M. E. Sweedler, *Hopf algebras and Galois theory*][chaseHopfAlgebrasGalois1969]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

/-! ### The un-quotiented Galois map -/

variable (k H) in
/-- The rearrangement `(x ⊗ v) ⊗ y ↦ x y ⊗ v` on `H ⊗ H ⊗ H`. -/
noncomputable def galFullCore : (H ⊗[k] H) ⊗[k] H →ₗ[k] H ⊗[k] H :=
  TensorProduct.map (LinearMap.mul' k H) LinearMap.id
    ∘ₗ (TensorProduct.assoc k H H H).symm.toLinearMap
    ∘ₗ TensorProduct.map LinearMap.id (TensorProduct.comm k H H).toLinearMap
    ∘ₗ (TensorProduct.assoc k H H H).toLinearMap

/-- `galFullCore (t ⊗ y)` is `t` with its first tensor factor multiplied on the right by `y`. -/
lemma galFullCore_tmul (t : H ⊗[k] H) (y : H) :
    galFullCore k H (t ⊗ₜ[k] y) = LinearMap.rTensor H ((LinearMap.mul k H).flip y) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a v => simp [galFullCore]
  | add u v hu hv => rw [add_tmul, map_add, map_add, hu, hv]

variable (k H) in
/-- The **un-quotiented Galois map** `α : H ⊗ H → H ⊗ H`, `x ⊗ y ↦ ∑ x₁ y ⊗ x₂`. -/
noncomputable def galFull : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  galFullCore k H ∘ₗ TensorProduct.map (comul (R := k) (A := H)) LinearMap.id

/-- `galFull (x ⊗ y)` is `Δ x` with its first tensor factor multiplied on the right by `y`. -/
lemma galFull_tmul (x y : H) :
    galFull k H (x ⊗ₜ[k] y)
      = LinearMap.rTensor H ((LinearMap.mul k H).flip y) (comul (R := k) x) := by
  simp [galFull, galFullCore_tmul]

/-- `galFull (x ⊗ y) = ∑ᵢ x₁ⁱ y ⊗ x₂ⁱ` for any representation `Δ x = ∑ᵢ x₁ⁱ ⊗ x₂ⁱ`. -/
lemma galFull_tmul_repr (x y : H) {J : Type*} (r : Coalgebra.Repr k x J) :
    galFull k H (x ⊗ₜ[k] y) = ∑ i ∈ r.index, (r.left i * y) ⊗ₜ[k] r.right i := by
  rw [galFull_tmul, ← r.eq, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The Galois map of a quotient is the un-quotiented one followed by `1 ⊗ π`. -/
lemma gal_eq_lTensor_galFull (I : Submodule k H) :
    gal I = LinearMap.lTensor H I.mkQ ∘ₗ galFull k H := by
  ext x y
  change gal I (x ⊗ₜ[k] y) = LinearMap.lTensor H I.mkQ (galFull k H (x ⊗ₜ[k] y))
  rw [gal_tmul_eq_map, galFull_tmul]
  exact (LinearMap.congr_fun
    (LinearMap.lTensor_comp_rTensor H ((LinearMap.mul k H).flip y) I.mkQ)
    (comul (R := k) x)).symm

/-! ### Bijectivity for a cocommutative `H` -/

section Cocomm

variable [Coalgebra.IsCocomm k H]

/-- The representation of `S x` obtained by applying the antipode to a representation of `x`;
available because `S` is a morphism of coalgebras for a cocommutative `H`. -/
noncomputable def Repr.antipode {x : H} {J : Type*} (r : Coalgebra.Repr k x J) :
    Coalgebra.Repr k (HopfAlgebra.antipode k x) J where
  index := r.index
  left i := HopfAlgebra.antipode k (r.left i)
  right i := HopfAlgebra.antipode k (r.right i)
  eq := by
    have h := congr($(comul_comp_antipode_of_isCocomm (k := k) (H := H)) x)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [h, ← r.eq, map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl

/-- `α` is conjugate to the classical Galois map `β₀ : b ⊗ c ↦ ∑ b c₁ ⊗ c₂` by the antipode and
the flip: `α (x ⊗ y) = (S ⊗ S) (β₀ (S y ⊗ S x))`. -/
theorem galFull_tmul_eq_conj (x y : H) :
    galFull k H (x ⊗ₜ[k] y)
      = TensorProduct.map (HopfAlgebra.antipode k) (HopfAlgebra.antipode k)
          (HopfAlgebra.galoisMap k H
            (HopfAlgebra.antipode k y ⊗ₜ[k] HopfAlgebra.antipode k x)) := by
  classical
  set r := ℛ k x with hr
  rw [HopfAlgebra.galoisMap_tmul _ _ (Repr.antipode r), map_sum,
    galFull_tmul_repr x y r]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Repr.antipode, TensorProduct.map_tmul]
  rw [antipode_mul, antipode_antipode, antipode_antipode, antipode_antipode]

variable (k H) in
/-- The antipode of a cocommutative Hopf algebra as a linear involution. -/
noncomputable def antipodeEquiv : H ≃ₗ[k] H where
  __ := (HopfAlgebra.antipode k : H →ₗ[k] H)
  invFun := HopfAlgebra.antipode k
  left_inv := antipode_antipode
  right_inv := antipode_antipode

variable (k H) in
/-- **The un-quotiented Galois map of a cocommutative Hopf algebra is bijective.** -/
noncomputable def galFullEquiv : H ⊗[k] H ≃ₗ[k] H ⊗[k] H :=
  ((TensorProduct.comm k H H).trans
      (TensorProduct.congr (antipodeEquiv k H) (antipodeEquiv k H))).trans
    ((HopfAlgebra.galoisEquiv k H).trans
      (TensorProduct.congr (antipodeEquiv k H) (antipodeEquiv k H)))

/-- For a cocommutative `H`, the linear equivalence `galFullEquiv` agrees with `galFull`. -/
@[simp] lemma galFullEquiv_apply (t : H ⊗[k] H) : galFullEquiv k H t = galFull k H t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [galFull_tmul_eq_conj]
    rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- For a cocommutative `H`, the un-quotiented Galois map `galFull` is bijective. -/
theorem galFull_bijective : Function.Bijective (galFull k H) := by
  have : (galFull k H) = (galFullEquiv k H : H ⊗[k] H →ₗ[k] H ⊗[k] H) := by
    ext x y; exact (galFullEquiv_apply _).symm
  rw [this]
  exact (galFullEquiv k H).bijective

end Cocomm

/-! ### The kernel of the Galois map -/

variable [IsAbsFlat k]

/-- `ker β = α⁻¹ (H ⊗ I)`. -/
theorem ker_gal_eq_comap (I : Submodule k H) :
    LinearMap.ker (gal I) = Submodule.comap (galFull k H) (rightTensor I) := by
  rw [gal_eq_lTensor_galFull, LinearMap.ker_comp, ker_lTensor_eq_rightTensor, Submodule.ker_mkQ]

section Cocomm

variable [Coalgebra.IsCocomm k H]

/-- **The injectivity input of the descent theorem, made concrete.**  For a sub-bialgebra `K` of a
cocommutative Hopf algebra, the descended Galois map `H ⊗_K H → H ⊗ (H ⧸ τ K)` is injective if and
only if the image under `α` of the `K`-balanced relations is all of `H ⊗ H K⁺`. -/
theorem ker_gal_le_balRel_iff (K : Subalgebra k H) :
    LinearMap.ker (gal (tau K.toSubmodule)) ≤ balRel K.toSubmodule ↔
      rightTensor (tau K.toSubmodule) ≤ Submodule.map (galFull k H) (balRel K.toSubmodule) := by
  constructor
  · intro h
    calc rightTensor (tau K.toSubmodule)
        = Submodule.map (galFull k H)
            (Submodule.comap (galFull k H) (rightTensor (tau K.toSubmodule))) :=
          (Submodule.map_comap_eq_of_surjective galFull_bijective.2 _).symm
      _ ≤ Submodule.map (galFull k H) (balRel K.toSubmodule) :=
          Submodule.map_mono (by rw [← ker_gal_eq_comap]; exact h)
  · intro h t ht
    rw [ker_gal_eq_comap, Submodule.mem_comap] at ht
    obtain ⟨s, hs, hst⟩ := h ht
    rwa [← galFull_bijective.1 hst]

/-- **Newman's closure identity `μ (τ K) = K`** for a sub-bialgebra `K` of a cocommutative Hopf
algebra, from the two concrete inputs: the `K`-balanced relations generate `H ⊗ H K⁺` through the
Galois map, and descent along `K ⊆ H`. -/
theorem coinv_tau_eq_of_rightTensor_le_of_descent {K : Subalgebra k H} (hK : IsSubBialg K)
    (hgen : rightTensor (tau K.toSubmodule) ≤ Submodule.map (galFull k H) (balRel K.toSubmodule))
    (hdesc : ∀ h : H, h ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] h ∈ balRel K.toSubmodule → h ∈ K) :
    coinv (tau K.toSubmodule) = K.toSubmodule :=
  coinv_tau_eq_of_ker_gal_le_of_descent hK ((ker_gal_le_balRel_iff K).2 hgen) hdesc

end Cocomm

end HopfAlgebra.Cocommutative
