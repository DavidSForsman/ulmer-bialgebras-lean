module

public import Hopf.Cocommutative.GaloisIso

/-!
# The Amitsur complex of a split extension, and Masuoka's lifting of primitives

Let `K` be a sub-Hopf algebra of a Hopf algebra `H` over a field `k`, `N = τ K = H K⁺` and
`C = H ⧸ N`.  Masuoka's proof of the surjectivity of Newman's correspondence rests on the
description of the primitive elements of the `H`-coring `H ⊗_K H`: they are all of the shape
`1 ⊗ x - x ⊗ 1`.  Over a *split* extension — one admitting a right `K`-linear retraction
`E : H ↠ K`, which is what Sweedler's freeness theorem provides — this is elementary: the
Amitsur complex

```
H --d⁰--> H ⊗_K H --d¹--> H ⊗_K H ⊗_K H
```

has the contracting homotopy `s¹ (x ⊗ y) = E x · y`, `s² (x ⊗ ξ) = E x · ξ`, so that
`s² ∘ d¹ + d⁰ ∘ s¹ = id`.

The primitive attached to an element `y` of `H` is `Ξ y = ∑ y₁ ⊗ S y₂`; it is a cocycle,
`d¹ (Ξ y) = 0`, as soon as the class of `y` in `C` is primitive, and then the homotopy exhibits
it as `d⁰ x` for `x = ∑ E(y₁) S(y₂)`.  Reading this off through Takeuchi's isomorphism
`H ⊗_K H ≅ C ⊗ H` gives the main result of the file, the Hopf-algebraic core of Masuoka's
Lemma 2.6.

## Main results

* `HopfAlgebra.Cocommutative.homotopy`: the contracting homotopy identity
  `s² (d¹ t) + d⁰ (s¹ t) = t` on `H ⊗_K H`.
* `HopfAlgebra.Cocommutative.exists_comul_sub_mem`: for a sub-Hopf algebra `K` with a right
  `K`-linear retraction `E : H → K`, if `Δ y - y ⊗ 1 - 1 ⊗ y ∈ N ⊗ H + H ⊗ N` then there is `x` with
  `Δ x - 1 ⊗ x + y ⊗ 1 ∈ N ⊗ H`.

## References

* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991], Lemma 2.6
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [S. U. Chase, M. E. Sweedler, *Hopf Algebras and Galois Theory*][chaseHopfAlgebrasGalois1969]
* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

universe u

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

section Complex

variable (K : Subalgebra k H)

/-- `d⁰ : H → H ⊗_K H`, `a ↦ 1 ⊗ a - a ⊗ 1`. -/
noncomputable def d0 : H →ₗ[k] Q₂ K.toSubmodule :=
  (balAct K.toSubmodule actH).mkQ ∘ₗ
    ((TensorProduct.mk k H H 1) - (TensorProduct.mk k H H).flip 1)

/-- `d0 K a = 1 ⊗ a - a ⊗ 1` in `H ⊗_K H`. -/
lemma d0_apply (a : H) :
    d0 K a = rmk K.toSubmodule actH 1 a - rmk K.toSubmodule actH a 1 := by
  simp [d0, rmk_def, Submodule.mkQ_apply, Submodule.Quotient.mk_sub]

/-- The three terms of `d¹ : H ⊗_K H → H ⊗_K H ⊗_K H`,
`x ⊗ y ↦ 1 ⊗ x ⊗ y - x ⊗ 1 ⊗ y + x ⊗ y ⊗ 1`, before passing to the quotient. -/
noncomputable def d1Raw : H ⊗[k] H →ₗ[k] Q₃ K.toSubmodule :=
  ((balAct K.toSubmodule (act₂ K.toSubmodule)).mkQ ∘ₗ
      (TensorProduct.mk k H (Q₂ K.toSubmodule) 1) ∘ₗ (balAct K.toSubmodule actH).mkQ)
  - ((balAct K.toSubmodule (act₂ K.toSubmodule)).mkQ ∘ₗ
      TensorProduct.map LinearMap.id
        ((balAct K.toSubmodule actH).mkQ ∘ₗ (TensorProduct.mk k H H 1)))
  + ((balAct K.toSubmodule (act₂ K.toSubmodule)).mkQ ∘ₗ
      TensorProduct.map LinearMap.id
        ((balAct K.toSubmodule actH).mkQ ∘ₗ (TensorProduct.mk k H H).flip 1))

/-- `d1Raw K (x ⊗ y) = 1 ⊗ x ⊗ y - x ⊗ 1 ⊗ y + x ⊗ y ⊗ 1`. -/
lemma d1Raw_tmul (x y : H) :
    d1Raw K (x ⊗ₜ[k] y)
      = rmk K.toSubmodule (act₂ K.toSubmodule) 1 (rmk K.toSubmodule actH x y)
        - rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH 1 y)
        + rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH y 1) := rfl

/-- `d¹ : H ⊗_K H → H ⊗_K H ⊗_K H`. -/
noncomputable def d1 : Q₂ K.toSubmodule →ₗ[k] Q₃ K.toSubmodule :=
  liftT K.toSubmodule actH (d1Raw K) (by
    intro x y a ha
    rw [d1Raw_tmul, d1Raw_tmul]
    have hay : (actH (k := k) a) y = a * y := rfl
    have hbal : rmk K.toSubmodule actH (x * a) y = rmk K.toSubmodule actH x (a * y) :=
      rmk_balanced K.toSubmodule actH x y ha
    have hbal1 : rmk K.toSubmodule actH a y = rmk K.toSubmodule actH 1 (a * y) := by
      have h := rmk_balanced K.toSubmodule actH (1 : H) y ha
      rwa [one_mul] at h
    have e1 : rmk K.toSubmodule (act₂ K.toSubmodule) 1 (rmk K.toSubmodule actH (x * a) y)
        = rmk K.toSubmodule (act₂ K.toSubmodule) 1 (rmk K.toSubmodule actH x (a * y)) := by
      rw [hbal]
    have e2 : rmk K.toSubmodule (act₂ K.toSubmodule) (x * a) (rmk K.toSubmodule actH 1 y)
        = rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH 1 (a * y)) := by
      rw [rmk_balanced K.toSubmodule (act₂ K.toSubmodule) x _ ha, act₂_apply_rmk, mul_one, hbal1]
    have e3 : rmk K.toSubmodule (act₂ K.toSubmodule) (x * a) (rmk K.toSubmodule actH y 1)
        = rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH (a * y) 1) := by
      rw [rmk_balanced K.toSubmodule (act₂ K.toSubmodule) x _ ha, act₂_apply_rmk]
    rw [hay, e1, e2, e3])

/-- `d¹ (x ⊗ y) = 1 ⊗ x ⊗ y - x ⊗ 1 ⊗ y + x ⊗ y ⊗ 1`. -/
@[simp] lemma d1_rmk (x y : H) :
    d1 K (rmk K.toSubmodule actH x y)
      = rmk K.toSubmodule (act₂ K.toSubmodule) 1 (rmk K.toSubmodule actH x y)
        - rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH 1 y)
        + rmk K.toSubmodule (act₂ K.toSubmodule) x (rmk K.toSubmodule actH y 1) := rfl

variable (E : H →ₗ[k] H) (hEmem : ∀ x : H, E x ∈ K) (hEid : ∀ a ∈ K, E a = a)
  (hEmul : ∀ (x : H), ∀ a ∈ K, E (x * a) = E x * a)

include hEmul

/-- `s¹ : H ⊗_K H → H`, `x ⊗ y ↦ E x · y`. -/
noncomputable def s1 : Q₂ K.toSubmodule →ₗ[k] H :=
  liftT K.toSubmodule actH (TensorProduct.lift ((LinearMap.mul k H) ∘ₗ E)) (by
    intro x y a ha
    simp [hEmul x a ha, mul_assoc])

/-- `s¹ (x ⊗ y) = E x * y`. -/
@[simp] lemma s1_rmk (x y : H) : s1 K E hEmul (rmk K.toSubmodule actH x y) = E x * y := rfl

/-- `s² : H ⊗_K H ⊗_K H → H ⊗_K H`, `x ⊗ ξ ↦ E x · ξ`. -/
noncomputable def s2 : Q₃ K.toSubmodule →ₗ[k] Q₂ K.toSubmodule :=
  liftT K.toSubmodule (act₂ K.toSubmodule)
    (actLin (act₂ K.toSubmodule) ∘ₗ LinearMap.rTensor (Q₂ K.toSubmodule) E) (by
      intro x m a ha
      simp [hEmul x a ha, map_mul])

/-- `s² (x ⊗ m) = E x • m`, acting through `act₂`. -/
@[simp] lemma s2_rmk (x : H) (m : Q₂ K.toSubmodule) :
    s2 K E hEmul (rmk K.toSubmodule (act₂ K.toSubmodule) x m)
      = act₂ K.toSubmodule (E x) m := rfl

include hEmem hEid

/-- **The contracting homotopy of the Amitsur complex** of a split extension. -/
theorem homotopy (t : Q₂ K.toSubmodule) :
    s2 K E hEmul (d1 K t) + d0 K (s1 K E hEmul t) = t := by
  induction t using RelT.induction_on with
  | rmk x y =>
      rw [d1_rmk, s1_rmk]
      simp only [map_add, map_sub, s2_rmk, act₂_apply_rmk, d0_apply]
      rw [hEid 1 K.one_mem]
      have hmove : rmk K.toSubmodule actH (E x) y
          = rmk K.toSubmodule actH 1 (E x * y) := by
        have h := rmk_balanced K.toSubmodule actH (1 : H) y (hEmem x)
        rw [one_mul] at h
        exact h
      simp only [one_mul, mul_one]
      rw [hmove]
      abel
  | add u v hu hv =>
      rw [map_add, map_add, map_add, map_add]
      rw [show s2 K E hEmul (d1 K u) + s2 K E hEmul (d1 K v) +
          (d0 K (s1 K E hEmul u) + d0 K (s1 K E hEmul v))
          = (s2 K E hEmul (d1 K u) + d0 K (s1 K E hEmul u)) +
            (s2 K E hEmul (d1 K v) + d0 K (s1 K E hEmul v)) by abel, hu, hv]

end Complex

/-! ### The cocycle attached to an element -/

section Cocycle

variable (K : Subalgebra k H)

/-- `Ξ : H → H ⊗_K H`, `y ↦ ∑ y₁ ⊗ S y₂`: the candidate primitive attached to `y`. -/
noncomputable def xiMap : H →ₗ[k] Q₂ K.toSubmodule :=
  gamRaw K actH ∘ₗ (TensorProduct.mk k H H).flip 1

/-- `xiMap K y = gamRaw K actH (y ⊗ 1)`. -/
lemma xiMap_apply (y : H) : xiMap K y = gamRaw K actH (y ⊗ₜ[k] (1 : H)) := rfl

variable {K}

/-- `Ξ y` is the class of `∑ y₁ ⊗ S y₂` in `H ⊗_K H`. -/
lemma xiMap_eq_mkQ (y : H) :
    xiMap K y = (balAct K.toSubmodule actH).mkQ (sAnti k H y) := by
  have hact : actOn (actH (k := k) (H := H)) (1 : H) = LinearMap.id :=
    LinearMap.ext fun z => by simp
  rw [xiMap_apply, gamRaw_tmul, rmkOn, LinearMap.comp_apply, hact, TensorProduct.map_id]
  rfl

variable (K) in
/-- `t ↦ t ⊗ 1` into `H ⊗_K H`. -/
noncomputable def rmkOne : H →ₗ[k] Q₂ K.toSubmodule :=
  (balAct K.toSubmodule actH).mkQ ∘ₗ (TensorProduct.mk k H H).flip 1

/-- `rmkOne K t = t ⊗ 1` in `H ⊗_K H`. -/
@[simp] lemma rmkOne_apply (t : H) : rmkOne K t = rmk K.toSubmodule actH t 1 := rfl

variable (hK : HopfAlgebra.IsSubHopfAlgebra k K)

include hK

/-- For a sub-Hopf algebra `K`, `bet` sends `Ξ y` to `[y] ⊗ 1`, with `[y]` the class of `y`
modulo `τ K`. -/
lemma bet_xiMap (y : H) :
    bet hK actH (xiMap K y) = (tau K.toSubmodule).mkQ y ⊗ₜ[k] (1 : H) := by
  rw [xiMap_apply, ← gam_tmul hK actH y (1 : H), bet_gam]

/-- For a sub-Hopf algebra `K`, `Ξ n = 0` for every `n ∈ τ K`. -/
lemma xiMap_eq_zero_of_mem_tau {n : H} (hn : n ∈ HopfAlgebra.Cocommutative.tau K.toSubmodule) :
    xiMap K n = 0 := by
  rw [xiMap_apply]
  exact gamRaw_eq_zero_of_mem_tau hK actH hn 1

/-- The image of `d¹` under Takeuchi's isomorphism, on `H ⊗ H`. -/
lemma bet_d1Raw (w : H ⊗[k] H) :
    bet hK (act₂ K.toSubmodule) (d1Raw K w)
      = (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ 1 ⊗ₜ[k] (balAct K.toSubmodule actH).mkQ w
        - TensorProduct.map (tau K.toSubmodule).mkQ (balAct K.toSubmodule actH).mkQ
            ((TensorProduct.assoc k H H H)
              (LinearMap.rTensor H (comul (R := k) (A := H)) w))
        + TensorProduct.map (tau K.toSubmodule).mkQ (rmkOne K) (mulR k H w) := by
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      rw [d1Raw_tmul, map_add, map_sub, bet_rmk, bet_rmk, bet_rmk, betRaw_tmul, betRaw_tmul,
        betRaw_tmul, Bialgebra.comul_one, LinearMap.rTensor_tmul, mulR_tmul]
      have h1 : TensorProduct.map (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ
          (actOn (act₂ K.toSubmodule) (rmk K.toSubmodule actH u v))
          (1 ⊗ₜ[k] (1 : H) : H ⊗[k] H)
          = (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ 1 ⊗ₜ[k]
            (balAct K.toSubmodule actH).mkQ (u ⊗ₜ[k] v) := by
        simp [rmk_def]
      rw [show (1 : H ⊗[k] H) = 1 ⊗ₜ[k] (1 : H) from Algebra.TensorProduct.one_def, h1]
      congr 1
      · congr 1
        induction (comul (R := k) u) using TensorProduct.inductionOn with
        | tmul a b =>
            simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, actOn_apply,
              Submodule.mkQ_apply]
            rw [act₂_apply_rmk, mul_one]
            rfl
        | add s t hs ht =>
            rw [map_add, TensorProduct.add_tmul, map_add, map_add, hs, ht]
      · induction (comul (R := k) u) using TensorProduct.inductionOn with
        | tmul a b =>
            simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, actOn_apply,
              LinearMap.flip_apply, LinearMap.mul_apply', rmkOne_apply]
            rw [act₂_apply_rmk]
        | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  | add s t hs ht =>
      rw [map_add, map_add, hs, ht]
      simp only [map_add, TensorProduct.tmul_add]
      abel

/-- **The cocycle identity.**  `β (d¹ (Ξ y)) = 1 ⊗ Ξ y - (p ⊗ Ξ) (Δ y) + p y ⊗ Ξ 1`. -/
theorem bet_d1_xiMap (y : H) :
    bet hK (act₂ K.toSubmodule) (d1 K (xiMap K y))
      = (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ 1 ⊗ₜ[k] xiMap K y
        - TensorProduct.map (tau K.toSubmodule).mkQ (xiMap K) (comul (R := k) y)
        + (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ y ⊗ₜ[k] xiMap K (1 : H) := by
  have hd1 : d1 K (xiMap K y) = d1Raw K (sAnti k H y) := by
    rw [xiMap_eq_mkQ]
    rfl
  rw [hd1, bet_d1Raw hK, ← xiMap_eq_mkQ]
  congr 1
  · congr 1
    rw [assoc_rTensor_comul_sAnti]
    induction (comul (R := k) y) using TensorProduct.inductionOn with
    | tmul a b => simp [xiMap_eq_mkQ]
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  · rw [show mulR k H (sAnti k H y) = y ⊗ₜ[k] (1 : H) from congr($mulR_comp_sAnti y)]
    simp only [TensorProduct.map_tmul, rmkOne_apply, xiMap_eq_mkQ, sAnti_apply,
      Bialgebra.comul_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
      HopfAlgebra.antipode_one]
    rfl

/-- If the class of `y` modulo `N = τ K` is primitive, then `Ξ y` is a cocycle. -/
theorem d1_xiMap_eq_zero {y : H}
    (hy : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y ∈
      HopfAlgebra.Cocommutative.leftTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule) ⊔
        HopfAlgebra.Cocommutative.rightTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule)) :
    d1 K (xiMap K y) = 0 := by
  have hzero : TensorProduct.map (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ (xiMap K)
      (comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y) = 0 := by
    have hle : HopfAlgebra.Cocommutative.leftTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule) ⊔
        HopfAlgebra.Cocommutative.rightTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule) ≤
        LinearMap.ker (TensorProduct.map (tau K.toSubmodule).mkQ (xiMap K)) := by
      refine sup_le (leftTensor_le fun z hz a => ?_) (rightTensor_le fun a z hz => ?_)
      · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 hz]
      · simp [LinearMap.mem_ker, xiMap_eq_zero_of_mem_tau hK hz]
    exact hle hy
  have hexp : TensorProduct.map (tau K.toSubmodule).mkQ (xiMap K) (comul (R := k) y)
      = (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ y ⊗ₜ[k] xiMap K (1 : H)
        + (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ 1 ⊗ₜ[k] xiMap K y := by
    have h := hzero
    rw [map_sub, map_sub, sub_eq_zero] at h
    rw [sub_eq_iff_eq_add] at h
    simpa [TensorProduct.map_tmul, add_comm] using h
  have hbet := bet_d1_xiMap hK y
  rw [hexp] at hbet
  have : bet hK (act₂ K.toSubmodule) (d1 K (xiMap K y)) = 0 := by
    rw [hbet]; abel
  exact (bet_injective hK (act₂ K.toSubmodule)) (by simpa using this)

end Cocycle

/-! ### The main lifting statement -/

section Main

variable {K : Subalgebra k H} (hK : HopfAlgebra.IsSubHopfAlgebra k K)
variable (E : H →ₗ[k] H) (hEmem : ∀ x : H, E x ∈ K) (hEid : ∀ a ∈ K, E a = a)
  (hEmul : ∀ (x : H), ∀ a ∈ K, E (x * a) = E x * a)

include hK hEmem hEid hEmul

/-- **Masuoka's lifting.**  Let `K` be a sub-Hopf algebra of `H` admitting a right `K`-linear
retraction `E : H ↠ K`, and let `N = τ K = H K⁺`.  If the class of `y` modulo `N` is primitive,
then there is `x ∈ H` with `Δ x - 1 ⊗ x + y ⊗ 1 ∈ N ⊗ H`; explicitly `x = ∑ E(y₁) S(y₂)`. -/
theorem exists_comul_sub_mem {y : H}
    (hy : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y ∈
      HopfAlgebra.Cocommutative.leftTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule) ⊔
        HopfAlgebra.Cocommutative.rightTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule)) :
    ∃ x : H, comul (R := k) x - (1 : H) ⊗ₜ[k] x + y ⊗ₜ[k] (1 : H)
      ∈ HopfAlgebra.Cocommutative.leftTensor (HopfAlgebra.Cocommutative.tau K.toSubmodule) := by
  classical
  set N : Submodule k H := HopfAlgebra.Cocommutative.tau K.toSubmodule with hN
  refine ⟨s1 K E hEmul (xiMap K y), ?_⟩
  -- the cocycle `Ξ y` is a coboundary
  have hxi : d0 K (s1 K E hEmul (xiMap K y)) = xiMap K y := by
    have h := homotopy K E hEmem hEid hEmul (xiMap K y)
    rw [d1_xiMap_eq_zero hK hy, map_zero, zero_add] at h
    exact h
  set x : H := s1 K E hEmul (xiMap K y) with hx
  -- apply Takeuchi's isomorphism
  have hbet := congrArg (bet hK actH) hxi
  rw [bet_xiMap hK y] at hbet
  -- compute the left-hand side
  have hd0 : bet hK actH (d0 K x)
      = N.mkQ 1 ⊗ₜ[k] x - TensorProduct.map N.mkQ LinearMap.id (comul (R := k) x) := by
    rw [d0_apply, map_sub, bet_rmk, bet_rmk, betRaw_tmul, betRaw_tmul]
    congr 1
    · rw [Bialgebra.comul_one]
      simp [Algebra.TensorProduct.one_def]
    · rw [show actOn (actH (k := k) (H := H)) (1 : H) = LinearMap.id from
        LinearMap.ext fun z => by simp]
  rw [hd0] at hbet
  have hker : TensorProduct.map N.mkQ (LinearMap.id (R := k) (M := H))
      (comul (R := k) x - (1 : H) ⊗ₜ[k] x + y ⊗ₜ[k] (1 : H)) = 0 := by
    rw [map_add, map_sub]
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [← hbet]
    abel
  have hmapeq : TensorProduct.map N.mkQ (LinearMap.id (R := k) (M := H))
      = LinearMap.rTensor H N.mkQ := rfl
  rw [hmapeq] at hker
  have hmem : comul (R := k) x - (1 : H) ⊗ₜ[k] x + y ⊗ₜ[k] (1 : H)
      ∈ LinearMap.ker (LinearMap.rTensor H N.mkQ) := hker
  rw [Coalgebra.Coradical.ker_rTensor, Submodule.ker_mkQ] at hmem
  exact hmem

end Main

end HopfAlgebra.Cocommutative
