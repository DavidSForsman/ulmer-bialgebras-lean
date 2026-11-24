module

public import Hopf.Graded.AssocGradedCoalg

/-!
# The associated graded Hopf algebra

Let `S : HopfAlgebra.Graded.HopfSplit k H` be a split, multiplicative, comultiplicative,
antipode-stable and almost commutative filtration of a Hopf algebra `H` over a field `k`, as in
`Hopf/Graded/AssocGraded.lean`. The associated graded object `S.Gr` is a commutative `k`-algebra
(loc. cit.) and a `k`-coalgebra (`Hopf/Graded/AssocGradedCoalg.lean`). This file shows that the two
structures are compatible and that the antipode of `H` descends, so that

```
S.Gr  is a commutative Hopf `k`-algebra,
```

connected in the sense that its degree-zero part is the line spanned by the unit.

The multiplicativity of the comultiplication rests on the compatibility of the degree-`n`
component map `S.phi n` on `H ⊗ H` with the product, `phi (m+n) (z w) = phi m z · phi n w` for
`z` of filtration degree `m` and `w` of filtration degree `n`
(`HopfAlgebra.Graded.HopfSplit.phi_mul`), which in turn is the statement that the product of `H` is
filtered.

## Main results

* `HopfAlgebra.Graded.HopfSplit.phi_mul`: for `z ∈ fil2 m` and `w ∈ fil2 n`,
  `phi (m + n) (z * w) = phi m z * phi n w`.
* `HopfAlgebra.Graded.HopfSplit.gcomul_mul`: `gcomul (x * y) = gcomul x * gcomul y`.
* `HopfAlgebra.Graded.HopfSplit.instBialgebra`: the `Bialgebra k S.Gr` instance.
* `HopfAlgebra.Graded.HopfSplit.gantipode`: the antipode of `S.Gr`, given on `Cₙ` by
  `cmp n ∘ antipode`.
* `HopfAlgebra.Graded.HopfSplit.instHopfAlgebra`: the `HopfAlgebra k S.Gr` instance.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [J. W. Milnor, J. C. Moore, *On the structure of Hopf algebras*][Milnor-Moore]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)

/-! ### Multiplicativity of `phi` -/

/-- For `z ∈ fil2 m` and `w ∈ fil2 n`, `phi (m + n) (z * w) = phi m z * phi n w`. -/
theorem phi_mul {m n : ℕ} {z w : H ⊗[k] H} (hz : z ∈ S.fil2 m) (hw : w ∈ S.fil2 n) :
    S.phi (m + n) (z * w) = S.phi m z * S.phi n w := by
  -- first fix `z` to be a tensor of homogeneous elements, and vary `w`
  have key : ∀ i ≤ m, ∀ u ∈ S.F i, ∀ v ∈ S.F (m - i), ∀ w ∈ S.fil2 n,
      S.phi (m + n) ((u ⊗ₜ[k] v) * w) = S.phi m (u ⊗ₜ[k] v) * S.phi n w := by
    intro i hi u hu v hv w hw
    refine S.fil2_ext
      (f := S.phi (m + n) ∘ₗ LinearMap.mulLeft k (u ⊗ₜ[k] v))
      (g := LinearMap.mulLeft k (S.phi m (u ⊗ₜ[k] v)) ∘ₗ S.phi n)
      (fun j hj u' hu' v' hv' => ?_) hw
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [Algebra.TensorProduct.tmul_mul_tmul,
      S.phi_tmul_of_mem (p := i + j) (q := (m - i) + (n - j)) (by omega)
        (S.mul_mem i j (Submodule.mul_mem_mul hu hu'))
        (S.mul_mem (m - i) (n - j) (Submodule.mul_mem_mul hv hv')),
      S.phi_tmul_of_mem (p := i) (q := m - i) (by omega) hu hv,
      S.phi_tmul_of_mem (p := j) (q := n - j) (by omega) hu' hv',
      Algebra.TensorProduct.tmul_mul_tmul,
      S.cmp_mul_cmp hu hu', S.cmp_mul_cmp hv hv']
  refine S.fil2_ext
    (f := S.phi (m + n) ∘ₗ LinearMap.mulRight k w)
    (g := LinearMap.mulRight k (S.phi n w) ∘ₗ S.phi m)
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
  exact key i hi u hu v hv w hw

/-! ### The bialgebra structure -/

/-- `gcounit 1 = 1`. -/
theorem gcounit_one : S.gcounit 1 = 1 := by
  rw [one_def, S.gcounit_cmp_zero S.one_mem, Bialgebra.counit_one]

/-- `gcounit (x * y) = gcounit x * gcounit y`. -/
theorem gcounit_mul (x y : S.Gr) : S.gcounit (x * y) = S.gcounit x * S.gcounit y := by
  refine S.induction_on (motive := fun x => S.gcounit (x * y) = S.gcounit x * S.gcounit y) x
    (by simp [S.zero_mul']) (fun m a => ?_) (fun x₁ x₂ h₁ h₂ => by
      rw [S.add_mul', map_add, map_add, h₁, h₂, add_mul])
  refine S.induction_on (motive := fun y => S.gcounit (S.ofC m a * y)
      = S.gcounit (S.ofC m a) * S.gcounit y) y (by simp [S.mul_zero']) (fun n b => ?_)
    (fun y₁ y₂ h₁ h₂ => by
      rw [S.mul_add', map_add, map_add, h₁, h₂, mul_add])
  have ha : (a : H) ∈ S.F m := S.c_le_f m a.2
  have hb : (b : H) ∈ S.F n := S.c_le_f n b.2
  rw [S.ofC_eq_cmp, S.ofC_eq_cmp, S.cmp_mul_cmp ha hb]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hm; subst hn
      rw [S.gcounit_cmp_zero (S.mul_mem 0 0 (Submodule.mul_mem_mul ha hb)),
        S.gcounit_cmp_zero ha, S.gcounit_cmp_zero hb, Bialgebra.counit_mul]
    · rw [S.gcounit_cmp_of_pos (by omega), S.gcounit_cmp_of_pos hn, mul_zero]
  · rw [S.gcounit_cmp_of_pos (by omega), S.gcounit_cmp_of_pos hm, zero_mul]

/-- `gcomul 1 = 1`. -/
theorem gcomul_one : S.gcomul 1 = 1 := by
  rw [one_def, S.gcomul_cmp S.one_mem, S.dAux_apply, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def, S.phi_tmul_of_mem (p := 0) (q := 0) rfl S.one_mem S.one_mem]
  rfl

/-- `gcomul (x * y) = gcomul x * gcomul y`. -/
theorem gcomul_mul (x y : S.Gr) : S.gcomul (x * y) = S.gcomul x * S.gcomul y := by
  refine S.induction_on (motive := fun x => S.gcomul (x * y) = S.gcomul x * S.gcomul y) x
    (by simp [S.zero_mul']) (fun m a => ?_) (fun x₁ x₂ h₁ h₂ => by
      rw [S.add_mul', map_add, map_add, h₁, h₂, add_mul])
  refine S.induction_on (motive := fun y => S.gcomul (S.ofC m a * y)
      = S.gcomul (S.ofC m a) * S.gcomul y) y (by simp [S.mul_zero']) (fun n b => ?_)
    (fun y₁ y₂ h₁ h₂ => by
      rw [S.mul_add', map_add, map_add, h₁, h₂, mul_add])
  have ha : (a : H) ∈ S.F m := S.c_le_f m a.2
  have hb : (b : H) ∈ S.F n := S.c_le_f n b.2
  rw [S.ofC_eq_cmp, S.ofC_eq_cmp, S.cmp_mul_cmp ha hb,
    S.gcomul_cmp (S.mul_mem m n (Submodule.mul_mem_mul ha hb)), S.gcomul_cmp ha, S.gcomul_cmp hb,
    S.dAux_apply, S.dAux_apply, S.dAux_apply, Bialgebra.comul_mul,
    S.phi_mul (S.comul_mem_fil2 ha) (S.comul_mem_fil2 hb)]

/-- **The associated graded object is a bialgebra.** -/
noncomputable instance instBialgebra : Bialgebra k S.Gr :=
  Bialgebra.mk' k S.Gr S.gcounit_one (fun {a b} => S.gcounit_mul a b) S.gcomul_one
    (fun {a b} => S.gcomul_mul a b)

/-! ### The antipode -/

/-- The antipode of the associated graded object, on the homogeneous piece of degree `n`. -/
noncomputable def gantipodeAux (n : ℕ) : H →ₗ[k] S.Gr :=
  S.cmp n ∘ₗ (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)

/-- The antipode of the associated graded object. -/
noncomputable def gantipode : S.Gr →ₗ[k] S.Gr :=
  DirectSum.toModule k ℕ S.Gr (fun n => (S.gantipodeAux n) ∘ₗ (S.C n).subtype)

/-- `gantipode (ofC n a)` is `cmp n` of the antipode of `a`. -/
theorem gantipode_ofC (n : ℕ) (a : ↥(S.C n)) :
    S.gantipode (S.ofC n a) = S.cmp n (HopfAlgebra.antipode (R := k) (a : H)) :=
  DirectSum.toModule_lof k (φ := fun i => S.gantipodeAux i ∘ₗ (S.C i).subtype) n a

/-- For `x ∈ Fₙ`, the graded antipode of `cmp n x` is `cmp n (S x)`. -/
theorem gantipode_cmp {n : ℕ} {x : H} (hx : x ∈ S.F n) :
    S.gantipode (S.cmp n x) = S.cmp n (HopfAlgebra.antipode (R := k) x) := by
  have h1 : S.cmp n x = S.ofC n ⟨S.pr n x, S.pr_mem_C n x⟩ := rfl
  rw [h1, S.gantipode_ofC, Subtype.coe_mk]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [S.toSplit.pr_zero_of_mem_F_zero hx]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsub : x - S.pr (m + 1) x ∈ S.F m := S.toSplit.sub_pr_mem hx
    have hanti : HopfAlgebra.antipode (R := k) (x - S.pr (m + 1) x) ∈ S.F m :=
      S.antipode_mem m _ hsub
    have : S.cmp (m + 1) (HopfAlgebra.antipode (R := k) (x - S.pr (m + 1) x)) = 0 :=
      S.cmp_eq_zero_of_mem_lt (by omega) hanti
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this.symm

/-- For `z ∈ fil2 n`, `mul' ((gantipode ⊗ id) (phi n z))` is `cmp n` of
`mul' ((antipode ⊗ id) z)`. -/
theorem antipode_aux_rTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    LinearMap.mul' k S.Gr (LinearMap.rTensor S.Gr S.gantipode (S.phi n z))
      = S.cmp n (LinearMap.mul' k H
          (LinearMap.rTensor H (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) z)) := by
  refine S.fil2_ext
    (f := LinearMap.mul' k S.Gr ∘ₗ (LinearMap.rTensor S.Gr S.gantipode) ∘ₗ S.phi n)
    (g := S.cmp n ∘ₗ LinearMap.mul' k H
      ∘ₗ (LinearMap.rTensor H (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply,
    S.gantipode_cmp hu, S.cmp_mul_cmp (S.antipode_mem i _ hu) hv]
  rw [show i + (n - i) = n by omega]

/-- For `z ∈ fil2 n`, `mul' ((id ⊗ gantipode) (phi n z))` is `cmp n` of
`mul' ((id ⊗ antipode) z)`. -/
theorem antipode_aux_lTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    LinearMap.mul' k S.Gr (LinearMap.lTensor S.Gr S.gantipode (S.phi n z))
      = S.cmp n (LinearMap.mul' k H
          (LinearMap.lTensor H (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) z)) := by
  refine S.fil2_ext
    (f := LinearMap.mul' k S.Gr ∘ₗ (LinearMap.lTensor S.Gr S.gantipode) ∘ₗ S.phi n)
    (g := S.cmp n ∘ₗ LinearMap.mul' k H
      ∘ₗ (LinearMap.lTensor H (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply,
    S.gantipode_cmp hv, S.cmp_mul_cmp hu (S.antipode_mem (n - i) _ hv)]
  rw [show i + (n - i) = n by omega]

/-- For `a ∈ Cₙ`, `cmp n (algebraMap (ε a)) = algebraMap (gcounit (cmp n a))`. -/
theorem cmp_algebraMap_counit {n : ℕ} {a : H} (ha : a ∈ S.C n) :
    S.cmp n (algebraMap k H (counit (R := k) a)) = algebraMap k S.Gr (S.gcounit (S.cmp n a)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have ha0 : a ∈ S.F 0 := S.c_le_f 0 ha
    rw [S.gcounit_cmp_zero ha0, S.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
      map_smul]
  · have h0 : counit (R := k) a = 0 := by
      obtain ⟨y, rfl⟩ := ha
      exact S.counit_pr n hn y
    rw [h0, map_zero, map_zero, S.gcounit_cmp_of_pos hn, map_zero]

/-- Antipode axiom for `Gr`: `mul' ∘ (gantipode ⊗ id) ∘ gcomul = algebraMap ∘ gcounit`. -/
theorem gmul_antipode_rTensor_comul :
    LinearMap.mul' k S.Gr ∘ₗ LinearMap.rTensor S.Gr S.gantipode ∘ₗ S.gcomul
      = (Algebra.linearMap k S.Gr) ∘ₗ S.gcounit := by
  refine LinearMap.ext fun g => ?_
  refine S.induction_on (motive := fun g =>
    (LinearMap.mul' k S.Gr ∘ₗ LinearMap.rTensor S.Gr S.gantipode ∘ₗ S.gcomul) g
      = ((Algebra.linearMap k S.Gr) ∘ₗ S.gcounit) g) g (by simp)
    (fun n a => ?_) (fun x y hx hy => by simp only [map_add, hx, hy])
  have ha : (a : H) ∈ S.F n := S.c_le_f n a.2
  simp only [LinearMap.comp_apply]
  rw [S.gcomul_ofC, S.dAux_apply, S.antipode_aux_rTensor (S.comul_mem_fil2 ha)]
  have hH : LinearMap.mul' k H (LinearMap.rTensor H
      (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) (comul (R := k) (a : H)))
      = algebraMap k H (counit (R := k) (a : H)) :=
    HopfAlgebra.mul_antipode_rTensor_comul_apply (a : H)
  rw [hH, S.cmp_algebraMap_counit a.2, S.ofC_eq_cmp]
  rfl

/-- Antipode axiom for `Gr`: `mul' ∘ (id ⊗ gantipode) ∘ gcomul = algebraMap ∘ gcounit`. -/
theorem gmul_antipode_lTensor_comul :
    LinearMap.mul' k S.Gr ∘ₗ LinearMap.lTensor S.Gr S.gantipode ∘ₗ S.gcomul
      = (Algebra.linearMap k S.Gr) ∘ₗ S.gcounit := by
  refine LinearMap.ext fun g => ?_
  refine S.induction_on (motive := fun g =>
    (LinearMap.mul' k S.Gr ∘ₗ LinearMap.lTensor S.Gr S.gantipode ∘ₗ S.gcomul) g
      = ((Algebra.linearMap k S.Gr) ∘ₗ S.gcounit) g) g (by simp)
    (fun n a => ?_) (fun x y hx hy => by simp only [map_add, hx, hy])
  have ha : (a : H) ∈ S.F n := S.c_le_f n a.2
  simp only [LinearMap.comp_apply]
  rw [S.gcomul_ofC, S.dAux_apply, S.antipode_aux_lTensor (S.comul_mem_fil2 ha)]
  have hH : LinearMap.mul' k H (LinearMap.lTensor H
      (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) (comul (R := k) (a : H)))
      = algebraMap k H (counit (R := k) (a : H)) :=
    HopfAlgebra.mul_antipode_lTensor_comul_apply (a : H)
  rw [hH, S.cmp_algebraMap_counit a.2, S.ofC_eq_cmp]
  rfl

/-- **The associated graded object of a filtered Hopf algebra is a Hopf algebra**, commutative
because the filtration is almost commutative. -/
noncomputable instance instHopfAlgebra : HopfAlgebra k S.Gr where
  antipode := S.gantipode
  mul_antipode_rTensor_comul := S.gmul_antipode_rTensor_comul
  mul_antipode_lTensor_comul := S.gmul_antipode_lTensor_comul

end HopfSplit

end HopfAlgebra.Graded
