module

public import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Hopf.Cocommutative.CocommProj

/-!
# Group objects of `Comon_k^coc` are cocommutative Hopf algebras

Let `k` be a commutative ring and `C = CommComon (ModuleCat k)` the category of cocommutative
`k`-coalgebras.  A group object `H : Grp C` is, classically, a cocommutative Hopf `k`-algebra.
This file makes the translation explicit: for `H : Grp C` the underlying `k`-module `H.X.X`
carries a `Coalgebra`, `Ring`, `Algebra`, `Bialgebra` and `HopfAlgebra` structure, and the
generalized elements of `H` — the morphisms `T ⟶ H.X` of `C` — multiply by the *convolution*
product of the underlying linear maps.

The main tool is `HopfAlgebra.Cocommutative.GrpDict.mul_hom_eq`: for `x y : T ⟶ H.X`,

`(x * y).hom.hom = Δ[T.X] ≫ (x.hom.hom ⊗ₘ y.hom.hom) ≫ mulHom H`.

Everything else — associativity, unitality, the bialgebra compatibilities and the antipode
identities — is deduced from the group axioms of `Hom (T, H.X)` applied to well-chosen
generalized elements, together with the universal property of the tensor product of
cocommutative comonoids.

## Main results

* `HopfAlgebra.Cocommutative.GrpDict.mul_hom_eq`: the product of two generalized elements
  `x y : T ⟶ H.X` has underlying linear map `CocommComon.lift x y ≫ mulHom H`, their convolution
  product.
* `HopfAlgebra.Cocommutative.GrpDict.instBialgebra`: for `H : Grp (CommComon (ModuleCat k))`, the
  underlying module `H.X.X` is a `k`-bialgebra.
* `HopfAlgebra.Cocommutative.GrpDict.instHopfAlgebra`: `H.X.X` is a Hopf `k`-algebra, with antipode
  the inverse morphism of `H`.
* `HopfAlgebra.Cocommutative.GrpDict.instIsCocomm`: the underlying coalgebra of `H.X.X` is
  cocommutative.

## References

* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6, before Corollary 6.11
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory TensorProduct
open UlmerBialgebras

attribute [local instance] ComonObj.instTensorUnit

namespace HopfAlgebra.Cocommutative.GrpDict

open scoped MonObj Obj ComonObj

-- `A.toComon.X` is `A.X` by definition; instance arguments are compared at instance
-- transparency, so the coercion to `Comon C` (and the trivial comonoid) has to unfold there.
attribute [local instance_reducible] CommComon.toComon CommComon.trivial

variable {k : Type u} [CommRing k]

/-! ## The coalgebra structure -/

/-- A comonoid object of `ModuleCat k` is a `k`-coalgebra. -/
noncomputable scoped instance instCoalgebra (X : ModuleCat.{u} k) [ComonObj X] :
    Coalgebra k X :=
  { CoalgCat.ofComonObjCoalgebraStruct X with
    coassoc := ModuleCat.hom_ext_iff.mp (ComonObj.comul_assoc X).symm
    rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (ComonObj.counit_comul X)
    lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (ComonObj.comul_counit X) }
/-- The comultiplication of `instCoalgebra X` is the comonoid comultiplication of `X`. -/
@[simp] lemma comul_eq (X : ModuleCat.{u} k) [ComonObj X] :
    (Coalgebra.comul (R := k) (A := X)) = (ComonObj.comul (X := X)).hom := rfl

/-- The counit of `instCoalgebra X` is the comonoid counit of `X`. -/
@[simp] lemma counit_eq (X : ModuleCat.{u} k) [ComonObj X] :
    (Coalgebra.counit (R := k) (A := X)) = (ComonObj.counit (X := X)).hom := rfl

variable (H : Grp (CommComon (ModuleCat.{u} k)))

/-! ## The multiplication and the unit -/

/-- The comparison morphism from the tensor product of two cocommutative comonoids to their
categorical product. -/
noncomputable def eHom (X Y : CommComon (ModuleCat.{u} k)) :
    UlmerBialgebras.CommComon.tensorObj X Y ⟶ X ⊗ Y :=
  lift (UlmerBialgebras.CommComon.homMk (UlmerBialgebras.CocommComon.fst X.X Y.X))
       (UlmerBialgebras.CommComon.homMk (UlmerBialgebras.CocommComon.snd X.X Y.X))

/-- The multiplication of the group object, as a map `A ⊗ A ⟶ A` of `k`-modules. -/
noncomputable def mulHom : (H.X.X ⊗ H.X.X : ModuleCat.{u} k) ⟶ H.X.X :=
  (eHom H.X H.X ≫ μ[H.X]).hom.hom

/-- The unit of the group object, as a morphism out of the trivial comonoid. -/
noncomputable def oneMor : (CommComon.trivial (ModuleCat.{u} k)) ⟶ H.X := 1

/-- The unit of the group object, as a map `k ⟶ A` of `k`-modules. -/
noncomputable def unitHom : (𝟙_ (ModuleCat.{u} k)) ⟶ H.X.X := (oneMor H).hom.hom

/-- The multiplication `A ⊗ A → A` of a group object is a morphism of comonoids. -/
instance : IsComonHom (mulHom H) := (eHom H.X H.X ≫ μ[H.X]).hom.isComonHom_hom

/-- The unit `k → A` of a group object is a morphism of comonoids. -/
instance : IsComonHom (unitHom H) := (oneMor H).hom.isComonHom_hom

/-! ## Multiplication of generalized elements is convolution -/

/-- The pairing `lift x y` into `H.X ⊗ H.X` is the tensor-product pairing of `x` and `y`
followed by the comparison morphism `eHom H.X H.X`. -/
lemma lift_eq {T : CommComon (ModuleCat.{u} k)} (x y : T ⟶ H.X) :
    lift x y = UlmerBialgebras.CommComon.homMk
      (UlmerBialgebras.CocommComon.lift x.hom.hom y.hom.hom) ≫ eHom H.X H.X := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, eHom, lift_fst]
    ext : 2
    exact congrArg ModuleCat.Hom.hom (UlmerBialgebras.CocommComon.lift_fst x.hom.hom y.hom.hom).symm
  · rw [lift_snd, Category.assoc, eHom, lift_snd]
    ext : 2
    exact congrArg ModuleCat.Hom.hom (UlmerBialgebras.CocommComon.lift_snd x.hom.hom y.hom.hom).symm

/-- **The product of two generalized elements is their convolution product.** -/
lemma mul_hom_eq {T : CommComon (ModuleCat.{u} k)} (x y : T ⟶ H.X) :
    (x * y).hom.hom = UlmerBialgebras.CocommComon.lift x.hom.hom y.hom.hom ≫ mulHom H := by
  rw [CategoryTheory.Hom.mul_def, lift_eq H x y]
  rfl

/-! ## The unit and the antipode -/

/-- The counit `ε : X → k` of a comonoid object of `ModuleCat k` is a morphism of comonoids. -/
instance isComonHom_counit (X : ModuleCat.{u} k) [ComonObj X] :
    IsComonHom (ε[X] : X ⟶ 𝟙_ (ModuleCat.{u} k)) where
  hom_counit := by simp
  hom_comul := by simp [unitors_inv_equal]

/-- The unique morphism to the trivial cocommutative comonoid. -/
noncomputable def toTrivial (T : CommComon (ModuleCat.{u} k)) :
    T ⟶ CommComon.trivial (ModuleCat.{u} k) :=
  UlmerBialgebras.CommComon.homMk (A := T) (B := CommComon.trivial (ModuleCat.{u} k)) ε[T.X]
/-- The underlying linear map of the identity of a cocommutative comonoid is the identity. -/
lemma id_hom_hom (A : CommComon (ModuleCat.{u} k)) : (𝟙 A : A ⟶ A).hom.hom = 𝟙 A.X := rfl

/-- **The unit generalized element is the counit followed by the unit.** -/
lemma one_hom_eq {T : CommComon (ModuleCat.{u} k)} :
    (1 : T ⟶ H.X).hom.hom = ε[T.X] ≫ unitHom H := by
  have h : (1 : T ⟶ H.X) = toTrivial T ≫ oneMor H := by
    rw [oneMor, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc]
    congr 1
  rw [h]
  rfl

/-- The antipode of the group object, as a map of `k`-modules. -/
noncomputable def invHom : H.X.X ⟶ H.X.X := ((𝟙 H.X)⁻¹ : H.X ⟶ H.X).hom.hom

/-! ## The monoid and antipode identities -/

/-- Associativity of the multiplication of a group object. -/
theorem mulHom_assoc :
    (mulHom H ⊗ₘ 𝟙 H.X.X) ≫ mulHom H
      = (α_ H.X.X H.X.X H.X.X).hom ≫ (𝟙 H.X.X ⊗ₘ mulHom H) ≫ mulHom H := by
  let T : CommComon (ModuleCat.{u} k) := CommComon.mk ((H.X.X ⊗ H.X.X) ⊗ H.X.X)
  let p1 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk
    (CocommComon.fst (H.X.X ⊗ H.X.X) H.X.X ≫ CocommComon.fst H.X.X H.X.X)
  let p2 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk
    (CocommComon.fst (H.X.X ⊗ H.X.X) H.X.X ≫ CocommComon.snd H.X.X H.X.X)
  let p3 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk (CocommComon.snd (H.X.X ⊗ H.X.X) H.X.X)
  have key := congrArg (fun f : T ⟶ H.X => f.hom.hom) (mul_assoc p1 p2 p3)
  simp only [mul_hom_eq, UlmerBialgebras.CommComon.homMk_hom, p1, p2, p3] at key
  rw [CocommComon.lift_comp_left, CocommComon.lift_fst_fst_snd H.X.X H.X.X H.X.X,
    CocommComon.lift_fst_snd_self (H.X.X ⊗ H.X.X) H.X.X] at key
  rw [CocommComon.lift_comp_right, CocommComon.lift_eq_associator H.X.X H.X.X H.X.X] at key
  exact (Category.id_comp _).symm.trans (key.trans (Category.assoc _ _ _))

/-- The left unit law. -/
theorem unitHom_mulHom_left :
    (λ_ H.X.X).inv ≫ (unitHom H ▷ H.X.X) ≫ mulHom H = 𝟙 H.X.X := by
  have h := congrArg (fun f : H.X ⟶ H.X => f.hom.hom) (one_mul (𝟙 H.X))
  simp only [mul_hom_eq, one_hom_eq, id_hom_hom] at h
  have h1 : CocommComon.lift ε[H.X.X] (𝟙 H.X.X) = (λ_ H.X.X).inv := by
    rw [CocommComon.lift, ComonObj.counit_comul_hom, Category.id_comp]
  rw [CocommComon.lift_comp_left, h1, MonoidalCategory.tensorHom_id, Category.assoc] at h
  exact h

/-- The right unit law. -/
theorem unitHom_mulHom_right :
    (ρ_ H.X.X).inv ≫ (H.X.X ◁ unitHom H) ≫ mulHom H = 𝟙 H.X.X := by
  have h := congrArg (fun f : H.X ⟶ H.X => f.hom.hom) (mul_one (𝟙 H.X))
  simp only [mul_hom_eq, one_hom_eq, id_hom_hom] at h
  have h1 : CocommComon.lift (𝟙 H.X.X) ε[H.X.X] = (ρ_ H.X.X).inv := by
    rw [CocommComon.lift, ComonObj.comul_counit_hom, Category.id_comp]
  rw [CocommComon.lift_comp_right, h1, MonoidalCategory.id_tensorHom, Category.assoc] at h
  exact h

/-- The first antipode identity. -/
theorem invHom_mulHom :
    CocommComon.lift (invHom H) (𝟙 H.X.X) ≫ mulHom H = ε[H.X.X] ≫ unitHom H := by
  have h := congrArg (fun f : H.X ⟶ H.X => f.hom.hom) (inv_mul_cancel (𝟙 H.X))
  simp only [mul_hom_eq, one_hom_eq] at h
  exact h

/-- The second antipode identity. -/
theorem mulHom_invHom :
    CocommComon.lift (𝟙 H.X.X) (invHom H) ≫ mulHom H = ε[H.X.X] ≫ unitHom H := by
  have h := congrArg (fun f : H.X ⟶ H.X => f.hom.hom) (mul_inv_cancel (𝟙 H.X))
  simp only [mul_hom_eq, one_hom_eq] at h
  exact h

/-! ## The Hopf algebra structure on the underlying `k`-module -/

/-- The multiplication of the Hopf algebra underlying a group object. -/
noncomputable instance instMul : Mul (H.X.X : ModuleCat.{u} k) :=
  ⟨fun a b => (mulHom H).hom (a ⊗ₜ[k] b)⟩

/-- `a * b` is the multiplication morphism applied to `a ⊗ b`. -/
lemma mul_def (a b : (H.X.X : ModuleCat.{u} k)) : a * b = (mulHom H).hom (a ⊗ₜ[k] b) := rfl

/-- The unit of the Hopf algebra underlying a group object. -/
noncomputable instance instOne : One (H.X.X : ModuleCat.{u} k) := ⟨(unitHom H).hom (1 : k)⟩

/-- `1` is the unit morphism applied to `1 : k`. -/
lemma one_def : (1 : (H.X.X : ModuleCat.{u} k)) = (unitHom H).hom (1 : k) := rfl

/-- **The underlying module of a group object of `Comon_k^coc` is a ring.** -/
noncomputable instance instRing : Ring (H.X.X : ModuleCat.{u} k) :=
  { (inferInstance : AddCommGroup (H.X.X : ModuleCat.{u} k)), instMul H, instOne H with
    mul_assoc := by
      intro a b c
      have h := congrArg (fun f : (H.X.X ⊗ H.X.X) ⊗ H.X.X ⟶ H.X.X =>
        f.hom ((a ⊗ₜ[k] b) ⊗ₜ[k] c)) (mulHom_assoc H)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.tensorHom_tmul,
        ModuleCat.MonoidalCategory.associator_hom_apply] at h
      exact h
    one_mul := by
      intro a
      have h := congrArg (fun f : H.X.X ⟶ H.X.X => f.hom a) (unitHom_mulHom_left H)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
        ModuleCat.MonoidalCategory.whiskerRight_apply] at h
      simpa [mul_def, one_def] using h
    mul_one := by
      intro a
      have h := congrArg (fun f : H.X.X ⟶ H.X.X => f.hom a) (unitHom_mulHom_right H)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
        ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
      simpa [mul_def, one_def] using h
    left_distrib := by intro a b c; simp [mul_def, TensorProduct.tmul_add]
    right_distrib := by intro a b c; simp [mul_def, TensorProduct.add_tmul]
    zero_mul := by intro a; simp [mul_def]
    mul_zero := by intro a; simp [mul_def] }

/-- **The underlying module of a group object of `Comon_k^coc` is a `k`-algebra.** -/
noncomputable instance instAlgebra : Algebra k (H.X.X : ModuleCat.{u} k) :=
  Algebra.ofModule
    (fun r x y => by rw [mul_def, mul_def, ← TensorProduct.smul_tmul', map_smul])
    (fun r x y => by rw [mul_def, mul_def, TensorProduct.tmul_smul, map_smul])

/-- `algebraMap k A r` is the unit morphism applied to `r`. -/
lemma algebraMap_eq (r : k) :
    algebraMap k (H.X.X : ModuleCat.{u} k) r = (unitHom H).hom r := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, ← map_smul]
  simp

/-- Multiplication on the underlying module is the multiplication morphism. -/
lemma mul'_eq (t : (H.X.X : ModuleCat.{u} k) ⊗[k] (H.X.X : ModuleCat.{u} k)) :
    LinearMap.mul' k (H.X.X : ModuleCat.{u} k) t = (mulHom H).hom t := by
  induction t with
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The shuffle map computes the product of the tensor square. -/
lemma tensorMu_mul (x y : (H.X.X : ModuleCat.{u} k) ⊗[k] (H.X.X : ModuleCat.{u} k)) :
    ((tensorμ H.X.X H.X.X H.X.X H.X.X ≫ (mulHom H ⊗ₘ mulHom H)).hom (x ⊗ₜ[k] y)) = x * y := by
  induction x with
  | add x₁ x₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, h₁, h₂, add_mul]
  | tmul a b =>
    induction y with
    | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, h₁, h₂, mul_add]
    | tmul c d =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_def]
        rfl

/-- **The underlying module of a group object of `Comon_k^coc` is a `k`-bialgebra.** -/
noncomputable instance instBialgebra : Bialgebra k (H.X.X : ModuleCat.{u} k) :=
  Bialgebra.mk' k _
    (counit_one := by
      have h := congrArg (fun f : (𝟙_ (ModuleCat.{u} k)) ⟶ 𝟙_ (ModuleCat.{u} k) => f.hom (1 : k))
        (IsComonHom.hom_counit (f := unitHom H))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h)
    (counit_mul := by
      intro a b
      have h := congrArg (fun f : (H.X.X ⊗ H.X.X : ModuleCat.{u} k) ⟶ 𝟙_ (ModuleCat.{u} k) =>
        f.hom (a ⊗ₜ[k] b)) (IsComonHom.hom_counit (f := mulHom H))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Comon.tensorObj_counit,
        ModuleCat.MonoidalCategory.tensorHom_tmul,
        ModuleCat.MonoidalCategory.leftUnitor_hom_apply] at h
      simpa [mul_def, smul_eq_mul] using h)
    (comul_one := by
      have h := congrArg
        (fun f : (𝟙_ (ModuleCat.{u} k)) ⟶ (H.X.X ⊗ H.X.X : ModuleCat.{u} k) => f.hom (1 : k))
        (IsComonHom.hom_comul (f := unitHom H))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      simpa [one_def, Algebra.TensorProduct.one_def] using h)
    (comul_mul := by
      intro a b
      have h := congrArg
        (fun f : (H.X.X ⊗ H.X.X : ModuleCat.{u} k) ⟶ (H.X.X ⊗ H.X.X : ModuleCat.{u} k) =>
          f.hom (a ⊗ₜ[k] b)) (IsComonHom.hom_comul (f := mulHom H))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Comon.tensorObj_comul] at h
      rw [mul_def]
      simp only [comul_eq] at h ⊢
      exact h.trans (tensorMu_mul H _ _))

/-- **The underlying module of a group object of `Comon_k^coc` is a Hopf `k`-algebra**, with
antipode the inverse morphism of the group object. -/
noncomputable instance instHopfAlgebra : HopfAlgebra k (H.X.X : ModuleCat.{u} k) where
  antipode := (invHom H).hom
  mul_antipode_rTensor_comul := by
    ext a
    have h := congrArg (fun f : H.X.X ⟶ H.X.X => f.hom a) (invHom_mulHom H)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CocommComon.lift] at h
    rw [ModuleCat.hom_tensorHom, ModuleCat.hom_id] at h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      mul'_eq, Algebra.linearMap_apply, algebraMap_eq]
    exact h
  mul_antipode_lTensor_comul := by
    ext a
    have h := congrArg (fun f : H.X.X ⟶ H.X.X => f.hom a) (mulHom_invHom H)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CocommComon.lift] at h
    rw [ModuleCat.hom_tensorHom, ModuleCat.hom_id] at h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      mul'_eq, Algebra.linearMap_apply, algebraMap_eq]
    exact h

/-- **The underlying coalgebra of a group object of `Comon_k^coc` is cocommutative.** -/
instance instIsCocomm : Coalgebra.IsCocomm k (H.X.X : ModuleCat.{u} k) where
  comm_comp_comul := by
    ext a
    have h := congrArg (fun f : H.X.X ⟶ (H.X.X ⊗ H.X.X : ModuleCat.{u} k) => f.hom a)
      (IsCommComonObj.comul_comm (X := H.X.X))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end HopfAlgebra.Cocommutative.GrpDict
