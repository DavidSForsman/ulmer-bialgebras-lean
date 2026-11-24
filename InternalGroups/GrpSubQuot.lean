module

public import Foundations.CategoryTheory.Grp.GrpRegular
public import Foundations.CategoryTheory.Factorization.RegularTools

/-!
# Subgroup objects and equivariant quotients of an internal group

Let `C` be a cartesian monoidal category and `H : Grp C` a group object.  This file sets up
the two posets which are related by Newman's correspondence:

* `InternalGroups.SubGrpObj H` — a **subgroup object** of `H`: a monomorphism `n : N ⟶ H.X` of `C`
  whose generalized elements are closed under the unit, the multiplication and the inverse
  of `H`.  (Equivalently, by `UlmerBialgebras.subGrpObj`, an object of `Grp C` together with a
  monomorphism into `H`; the elementwise description is the one we use.)
* `InternalGroups.QuotObj H` — an **equivariant quotient** of `H`: an object `Q` of `C` equipped
  with a left action of `H` (that is, an object of `C^H`) together with an equivariant
  epimorphism `q : H.X ⟶ Q`.  Here `H` acts on itself by left translation, so equivariance
  reads `h · q g = q (h g)`.

Both are preordered by factorization (`InternalGroups.SubGrpObj.Le`, `InternalGroups.QuotObj.Le`),
and the right adjoint of Newman's Galois connection, the **kernel** of an equivariant quotient, is
constructed here (`InternalGroups.QuotObj.kernelSub`).  Everything is phrased with generalized
elements: `Hom (T, H.X)` is a group, functorially in `T`, and a subgroup object of `H` is
exactly a subgroup of that group, functorially in `T`.

## Main results

* `InternalGroups.SubGrpObj`: a subgroup object of `H`, a subobject of `H.X` whose generalized
  elements form a subgroup of `Hom (T, H.X)` for every `T`.
* `InternalGroups.QuotObj`: an equivariant quotient of `H`, an `H`-object `Q` with an equivariant
  epimorphism `q : H.X ⟶ Q`.
* `InternalGroups.QuotObj.kernelSub`: the kernel of an equivariant quotient, as a subgroup object.
* `InternalGroups.QuotObj.mem_kernelSub`: `x` lies in the kernel of `P` if and only if
  `x ≫ P.q = 1 ≫ P.q`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6.3
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
-/

@[expose] public section

universe v u

namespace InternalGroups

open UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## Subgroup objects -/

/-- A **subgroup object** of the group object `H`: a subobject of `H.X` whose generalized
elements form a subgroup of the group `Hom (T, H.X)` for every `T`. -/
structure SubGrpObj (H : Grp C) where
  /-- The underlying object. -/
  N : C
  /-- The inclusion. -/
  n : N ⟶ H.X
  /-- The inclusion is a monomorphism. -/
  mono : Mono n
  /-- The unit belongs to the subgroup object. -/
  one_mem : ∀ T : C, ∃ z : T ⟶ N, z ≫ n = 1
  /-- The subgroup object is closed under multiplication. -/
  mul_mem : ∀ {T : C} (x y : T ⟶ N), ∃ z : T ⟶ N, z ≫ n = (x ≫ n) * (y ≫ n)
  /-- The subgroup object is closed under inverses. -/
  inv_mem : ∀ {T : C} (x : T ⟶ N), ∃ z : T ⟶ N, z ≫ n = (x ≫ n)⁻¹

namespace SubGrpObj

variable {H : Grp C}

attribute [instance] SubGrpObj.mono

/-- A generalized element of `H` **belongs** to the subgroup object `S`. -/
def Mem (S : SubGrpObj H) {T : C} (x : T ⟶ H.X) : Prop := Factors S.n x

/-- The inclusion `S.n` is itself a member of `S`. -/
lemma mem_self (S : SubGrpObj H) : S.Mem S.n := ⟨𝟙 S.N, Category.id_comp _⟩

/-- The order on subgroup objects: `S ≤ S'` when the inclusion of `S` factors through the
inclusion of `S'`. -/
def Le (S S' : SubGrpObj H) : Prop := ∃ f : S.N ⟶ S'.N, f ≫ S'.n = S.n

/-- `S ≤ S'` iff every generalized element of `S` belongs to `S'`. -/
lemma le_iff_mem (S S' : SubGrpObj H) :
    S.Le S' ↔ ∀ {T : C} (x : T ⟶ H.X), S.Mem x → S'.Mem x := by
  constructor
  · rintro ⟨f, hf⟩ T x ⟨z, rfl⟩
    exact ⟨z ≫ f, by rw [Category.assoc, hf]⟩
  · intro h
    exact h S.n S.mem_self

/-- Two subgroup objects are **equivalent** when they define the same subobject. -/
def Equiv (S S' : SubGrpObj H) : Prop := S.Le S' ∧ S'.Le S

end SubGrpObj

/-! ## Equivariant quotients -/

/-- An **equivariant quotient** of the group object `H`: an object `Q` of `C` equipped with
a left action of `H` — that is, an object of `C^H` — together with an equivariant
epimorphism `q : H.X ⟶ Q`, where `H` acts on itself by left translation. -/
structure QuotObj (H : Grp C) where
  /-- The underlying object. -/
  Q : C
  /-- The action of `H`. -/
  act : H.X ⊗ Q ⟶ Q
  /-- The quotient morphism. -/
  q : H.X ⟶ Q
  /-- The quotient morphism is an epimorphism. -/
  epi : Epi q
  /-- The unit acts trivially. -/
  act_one : ∀ {T : C} (y : T ⟶ Q), lift (1 : T ⟶ H.X) y ≫ act = y
  /-- The action is associative. -/
  act_mul : ∀ {T : C} (h k : T ⟶ H.X) (y : T ⟶ Q),
    lift h (lift k y ≫ act) ≫ act = lift (h * k) y ≫ act
  /-- The quotient morphism is equivariant. -/
  equivariant : ∀ {T : C} (h g : T ⟶ H.X), lift h (g ≫ q) ≫ act = (h * g) ≫ q

namespace QuotObj

variable {H : Grp C}

attribute [instance] QuotObj.epi

/-- The action of a generalized element of `H` on a generalized element of `P`. -/
def smul (P : QuotObj H) {T : C} (h : T ⟶ H.X) (y : T ⟶ P.Q) : T ⟶ P.Q := lift h y ≫ P.act

/-- The order on quotients: `P ≤ P'` when `P'` factors through `P`, i.e. `P'` is a further
quotient of `P`. -/
def Le (P P' : QuotObj H) : Prop := ∃ h : P.Q ⟶ P'.Q, P.q ≫ h = P'.q

/-- The order on equivariant quotients is reflexive. -/
lemma le_refl (P : QuotObj H) : P.Le P := ⟨𝟙 P.Q, Category.comp_id _⟩

/-! ### The kernel of an equivariant quotient -/

section Kernel

/-- The generalized elements killed by an equivariant quotient are closed under
multiplication. -/
lemma kernel_mul (P : QuotObj H) {T : C} {a b : T ⟶ H.X} (ha : a ≫ P.q = (1 : T ⟶ H.X) ≫ P.q)
    (hb : b ≫ P.q = (1 : T ⟶ H.X) ≫ P.q) : (a * b) ≫ P.q = (1 : T ⟶ H.X) ≫ P.q :=
  calc (a * b) ≫ P.q = P.smul a (b ≫ P.q) := (P.equivariant a b).symm
    _ = P.smul a ((1 : T ⟶ H.X) ≫ P.q) := by rw [hb]
    _ = (a * 1) ≫ P.q := P.equivariant a 1
    _ = (1 : T ⟶ H.X) ≫ P.q := by rw [mul_one, ha]

/-- The generalized elements killed by an equivariant quotient are closed under inverses. -/
lemma kernel_inv (P : QuotObj H) {T : C} {a : T ⟶ H.X} (ha : a ≫ P.q = (1 : T ⟶ H.X) ≫ P.q) :
    a⁻¹ ≫ P.q = (1 : T ⟶ H.X) ≫ P.q :=
  calc a⁻¹ ≫ P.q = (a⁻¹ * 1) ≫ P.q := by rw [mul_one]
    _ = P.smul a⁻¹ ((1 : T ⟶ H.X) ≫ P.q) := (P.equivariant _ _).symm
    _ = P.smul a⁻¹ (a ≫ P.q) := by rw [ha]
    _ = (a⁻¹ * a) ≫ P.q := P.equivariant _ _
    _ = (1 : T ⟶ H.X) ≫ P.q := by rw [inv_mul_cancel]

variable [HasEqualizers C]

/-- The generalized elements of the kernel of an equivariant quotient are exactly those
killed by the quotient morphism. -/
lemma factors_kernel_iff (P : QuotObj H) {T : C} (x : T ⟶ H.X) :
    Factors (equalizer.ι P.q ((1 : H.X ⟶ H.X) ≫ P.q)) x ↔ x ≫ P.q = (1 : T ⟶ H.X) ≫ P.q := by
  constructor
  · rintro ⟨y, rfl⟩
    have := equalizer.condition P.q ((1 : H.X ⟶ H.X) ≫ P.q)
    rw [Category.assoc, this, ← Category.assoc, ← Category.assoc, MonObj.comp_one]
  · intro hx
    refine ⟨equalizer.lift x ?_, equalizer.lift_ι _ _⟩
    rw [hx, ← Category.assoc, MonObj.comp_one]

/-- **The kernel of an equivariant quotient**, the right adjoint of Newman's Galois
connection. -/
noncomputable def kernelSub (P : QuotObj H) : SubGrpObj H where
  N := equalizer P.q ((1 : H.X ⟶ H.X) ≫ P.q)
  n := equalizer.ι _ _
  mono := inferInstance
  one_mem T := (P.factors_kernel_iff (1 : T ⟶ H.X)).2 rfl
  mul_mem x y :=
    (P.factors_kernel_iff _).2
      (P.kernel_mul ((P.factors_kernel_iff _).1 ⟨x, rfl⟩) ((P.factors_kernel_iff _).1 ⟨y, rfl⟩))
  inv_mem x :=
    (P.factors_kernel_iff _).2 (P.kernel_inv ((P.factors_kernel_iff _).1 ⟨x, rfl⟩))

/-- `x` belongs to the kernel of `P` iff `x ≫ P.q = 1 ≫ P.q`. -/
@[simp]
lemma mem_kernelSub (P : QuotObj H) {T : C} (x : T ⟶ H.X) :
    (P.kernelSub).Mem x ↔ x ≫ P.q = (1 : T ⟶ H.X) ≫ P.q :=
  P.factors_kernel_iff x

end Kernel

end QuotObj

end InternalGroups
