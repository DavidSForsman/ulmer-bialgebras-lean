module

public import InternalGroups.HomomorphismDetection

/-!
# The internal wreath product, and regular monomorphisms from coset separators

Let `C` be a cartesian monoidal category, `G` an internal group of `C` such that `G ⊗ -` has a
right adjoint (for instance `C` cartesian closed), and `A` an internal group of `C`.

* The exponential `A^G := (ihom G).obj A` carries the pointwise group structure: its generalized
  elements at stage `T` are the morphisms `G ⊗ T ⟶ A` (`InternalGroups.Internal.cofreeGrpObj`).
* `G` acts on `A^G` by translation of the argument, `(g · f) (x) = f (x * g)`
  (`InternalGroups.Internal.transl`), by group automorphisms, and the semidirect product
  `A^G ⋊ G`, the **wreath product** of the classical proof that monomorphisms of groups are
  equalizers, is an internal group (`InternalGroups.Internal.wreathGrpObj`).  It is built through
  the Yoneda description of internal groups: `A^G ⊗ G` represents the presheaf of groups
  `T ↦ (T ⟶ A^G) ⋊ (T ⟶ G)`.
* A morphism `u : G ⟶ A` **separates the cosets** of `i : H ⟶ G`
  (`InternalGroups.Internal.IsCosetSeparator`) if right translation by a generalized element `g`
  fixes `u` exactly when `g` factors through `i`.  In `Set` one takes for `A` the free abelian group
  on `G / H` and for `u` the quotient map.
* `InternalGroups.Internal.regularMonoOfCosetSeparator`: **a monomorphism of internal groups with a
  coset separator into an internal group is a regular monomorphism**: the equalizer of the two
  homomorphisms `g ↦ (u⁻¹ (g · u), g)` and `g ↦ (1, g)` into the wreath product `A^G ⋊ G`.

Conversely, the equalizer of `f, g : G ⟶ K` is separated by `x ↦ f x · (g x)⁻¹`, so in a
cartesian closed category the regular subgroups are exactly the subgroups with a coset separator
into an internal group, while the stabilizers are those with a coset separator into an arbitrary
object.

## References

* D. Forsman, exactness criterion for internal groups (unpublished, announced)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory MonObj

namespace InternalGroups

namespace Internal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## The pointwise group structure on an exponential -/

section Cofree

variable (H G : C) [Closed H] [GrpObj G]

/-- The presheaf of groups `T ↦ (H ⊗ T ⟶ G)`, whose value at `T` is the group of "functions from
`H` to `G` defined over `T`". -/
@[simps]
def cofreePresheaf : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (H ⊗ T.unop ⟶ G)
  map {_ _} φ := GrpCat.ofHom
    { toFun := fun x => (H ◁ φ.unop) ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun a b => MonObj.comp_mul _ a b }
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- The exponential `H ⟹ G` represents the presheaf `InternalGroups.Internal.cofreePresheaf`. -/
def cofreeRepresentableBy :
    (cofreePresheaf H G ⋙ forget _).RepresentableBy ((ihom H).obj G) where
  homEquiv :=
    { toFun := uncurry
      invFun := curry
      left_inv := fun f => curry_uncurry f
      right_inv := fun f => uncurry_curry f }
  homEquiv_comp f g := uncurry_natural_left f g

/-- **The exponential `H ⟹ G` is an internal group**, with the pointwise group structure. -/
@[instance_reducible]
noncomputable def cofreeGrpObj : GrpObj ((ihom H).obj G) :=
  GrpObj.ofRepresentableBy _ (cofreePresheaf H G) (cofreeRepresentableBy H G)

attribute [local instance] cofreeGrpObj

variable {H G}

/-- The group structure of `H ⟹ G` is the pointwise one. -/
lemma uncurry_mul {T : C} (u v : T ⟶ (ihom H).obj G) :
    uncurry (u * v) = uncurry u * uncurry v :=
  homEquiv_mul _ (cofreePresheaf H G ⋙ forget₂ GrpCat MonCat) (cofreeRepresentableBy H G) u v

omit [GrpObj G] in
/-- Transposition is injective. -/
lemma uncurry_injective {T : C} {u v : T ⟶ (ihom H).obj G} (h : uncurry u = uncurry v) :
    u = v := by
  rw [← curry_uncurry u, ← curry_uncurry v, h]

end Cofree

attribute [local instance] cofreeGrpObj

/-! ## Right translation and the translation action -/

section Transl

variable {G A : C} [GrpObj G]

/-- Right translation of the argument, `(x, t) ↦ (x * g t, t)`. -/
noncomputable def shear {T : C} (g : T ⟶ G) : G ⊗ T ⟶ G ⊗ T :=
  lift (fst G T * (snd G T ≫ g)) (snd G T)

/-- The first component of `shear g` is `(x, t) ↦ x * g t`. -/
@[reassoc (attr := simp)]
lemma shear_fst {T : C} (g : T ⟶ G) : shear g ≫ fst G T = fst G T * (snd G T ≫ g) := by
  simp [shear]

/-- Right translation by the identity element is the identity. -/
@[simp]
lemma shear_one {T : C} : shear (1 : T ⟶ G) = 𝟙 (G ⊗ T) := by
  rw [shear, MonObj.comp_one, _root_.mul_one, lift_fst_snd]

/-- Right translation by a product `g₁ * g₂` is translation by `g₁` followed by translation by `g₂`.
-/
lemma shear_mul {T : C} (g₁ g₂ : T ⟶ G) : shear (g₁ * g₂) = shear g₁ ≫ shear g₂ := by
  apply hom_ext <;> simp [shear, MonObj.comp_mul, _root_.mul_assoc]

/-- Right translation is natural in the stage: reindexing along `φ : T' ⟶ T` commutes with `shear`.
-/
lemma whiskerLeft_shear {T T' : C} (φ : T' ⟶ T) (g : T ⟶ G) :
    (G ◁ φ) ≫ shear g = shear (φ ≫ g) ≫ (G ◁ φ) := by
  apply hom_ext <;> simp [shear, MonObj.comp_mul]

variable [Closed G]

/-- The translation action of a generalized element `g : T ⟶ G` on a generalized element of
`A^G`: `(g · f) (x) = f (x * g)`. -/
noncomputable def transl {T : C} (g : T ⟶ G) (f : T ⟶ (ihom G).obj A) :
    T ⟶ (ihom G).obj A :=
  curry (shear g ≫ uncurry f)

/-- The transpose of `transl g f` is `shear g` followed by the transpose of `f`. -/
@[simp]
lemma uncurry_transl {T : C} (g : T ⟶ G) (f : T ⟶ (ihom G).obj A) :
    uncurry (transl g f) = shear g ≫ uncurry f :=
  uncurry_curry _

/-- Translation by the identity element is the identity. -/
@[simp]
lemma transl_one {T : C} (f : T ⟶ (ihom G).obj A) : transl (1 : T ⟶ G) f = f := by
  refine uncurry_injective ?_
  simp

/-- Translation is an action: translating by `g₁ * g₂` is translating by `g₂` and then by `g₁`. -/
lemma transl_transl {T : C} (g₁ g₂ : T ⟶ G) (f : T ⟶ (ihom G).obj A) :
    transl (g₁ * g₂) f = transl g₁ (transl g₂ f) := by
  refine uncurry_injective ?_
  simp [shear_mul]

/-- Translation is natural in the stage: `φ ≫ transl g f = transl (φ ≫ g) (φ ≫ f)`. -/
lemma comp_transl {T T' : C} (φ : T' ⟶ T) (g : T ⟶ G) (f : T ⟶ (ihom G).obj A) :
    φ ≫ transl g f = transl (φ ≫ g) (φ ≫ f) := by
  refine uncurry_injective ?_
  rw [uncurry_transl, uncurry_natural_left, uncurry_transl, uncurry_natural_left,
    ← Category.assoc, whiskerLeft_shear, Category.assoc]

variable [GrpObj A]

/-- Translation by `g` is multiplicative for the pointwise group structure on `A^G`. -/
lemma transl_mul {T : C} (g : T ⟶ G) (f₁ f₂ : T ⟶ (ihom G).obj A) :
    transl g (f₁ * f₂) = transl g f₁ * transl g f₂ := by
  refine uncurry_injective ?_
  rw [uncurry_mul, uncurry_transl, uncurry_transl, uncurry_transl, uncurry_mul,
    MonObj.comp_mul]

/-- Translation by `g`, as a group automorphism of the group of generalized elements of `A^G`. -/
@[simps]
noncomputable def translAut {T : C} (g : T ⟶ G) : MulAut (T ⟶ (ihom G).obj A) where
  toFun f := transl g f
  invFun f := transl g⁻¹ f
  left_inv f := by
    change transl g⁻¹ (transl g f) = f
    rw [← transl_transl, inv_mul_cancel, transl_one]
  right_inv f := by
    change transl g (transl g⁻¹ f) = f
    rw [← transl_transl, mul_inv_cancel, transl_one]
  map_mul' f₁ f₂ := transl_mul g f₁ f₂

/-- Translation, as a homomorphism from `T ⟶ G` to the automorphisms of `T ⟶ A^G`. -/
@[simps]
noncomputable def translHom (T : C) : (T ⟶ G) →* MulAut (T ⟶ (ihom G).obj A) where
  toFun g := translAut g
  map_one' := by ext f; simp [translAut]
  map_mul' g₁ g₂ := by ext f; simp [translAut, transl_transl]

end Transl

/-! ## The wreath product `A^G ⋊ G` -/

section Wreath

variable (G A : C) [GrpObj G] [Closed G] [GrpObj A]

/-- The presheaf of groups `T ↦ (T ⟶ A^G) ⋊ (T ⟶ G)` represented by the wreath product. -/
@[simps]
noncomputable def wreathPresheaf : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (SemidirectProduct (T.unop ⟶ (ihom G).obj A) (T.unop ⟶ G)
    (translHom T.unop))
  map {T T'} φ := GrpCat.ofHom
    { toFun := fun p => ⟨φ.unop ≫ p.left, φ.unop ≫ p.right⟩
      map_one' := by
        refine SemidirectProduct.ext ?_ ?_
        · simp
        · simp
      map_mul' := fun a b => by
        refine SemidirectProduct.ext ?_ ?_
        · simp only [SemidirectProduct.mul_left, MonObj.comp_mul, translHom_apply,
            translAut_apply]
          rw [comp_transl]
        · simpa using MonObj.comp_mul _ _ _ }
  map_id T := by
    ext p
    · simp
    · simp
  map_comp φ ψ := by
    ext p
    · simp
    · simp

/-- The wreath product `A^G ⋊ G`, as an object of `C`. -/
noncomputable def wreath : C := (ihom G).obj A ⊗ G

/-- The first projection of the wreath product. -/
noncomputable def wfst : wreath G A ⟶ (ihom G).obj A := fst _ _

/-- The second projection of the wreath product. -/
noncomputable def wsnd : wreath G A ⟶ G := snd _ _

variable {G A}

/-- A generalized element of the wreath product from its two components. -/
noncomputable def wlift {T : C} (f : T ⟶ (ihom G).obj A) (g : T ⟶ G) : T ⟶ wreath G A :=
  lift f g

omit [GrpObj G] [GrpObj A] in
/-- The first projection of `wlift f g` is `f`. -/
@[reassoc (attr := simp)]
lemma wlift_wfst {T : C} (f : T ⟶ (ihom G).obj A) (g : T ⟶ G) : wlift f g ≫ wfst G A = f :=
  lift_fst _ _

omit [GrpObj G] [GrpObj A] in
/-- The second projection of `wlift f g` is `g`. -/
@[reassoc (attr := simp)]
lemma wlift_wsnd {T : C} (f : T ⟶ (ihom G).obj A) (g : T ⟶ G) : wlift f g ≫ wsnd G A = g :=
  lift_snd _ _

omit [GrpObj G] [GrpObj A] in
/-- Two generalized elements of the wreath product with equal projections are equal. -/
@[ext]
lemma wreath_hom_ext {T : C} {a b : T ⟶ wreath G A} (h₁ : a ≫ wfst G A = b ≫ wfst G A)
    (h₂ : a ≫ wsnd G A = b ≫ wsnd G A) : a = b :=
  hom_ext _ _ h₁ h₂

variable (G A)

/-- The wreath product represents the presheaf of groups `wreathPresheaf`. -/
noncomputable def wreathRepresentableBy :
    (wreathPresheaf G A ⋙ forget _).RepresentableBy (wreath G A) where
  homEquiv {T} :=
    { toFun := fun a => ⟨a ≫ wfst G A, a ≫ wsnd G A⟩
      invFun := fun p => wlift p.left p.right
      left_inv := fun a => by ext <;> simp
      right_inv := fun p => SemidirectProduct.ext (by simp) (by simp) }
  homEquiv_comp := by
    intro T T' φ a
    exact SemidirectProduct.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- **The wreath product is an internal group.** -/
@[instance_reducible]
noncomputable def wreathGrpObj : GrpObj (wreath G A) :=
  GrpObj.ofRepresentableBy _ (wreathPresheaf G A) (wreathRepresentableBy G A)

attribute [local instance] wreathGrpObj

variable {G A}

/-- The bijection `wreathRepresentableBy` between generalized elements of the wreath product and the
semidirect product `(T ⟶ A^G) ⋊ (T ⟶ G)` is multiplicative. -/
lemma wreath_homEquiv_mul {T : C} (a b : T ⟶ wreath G A) :
    (wreathRepresentableBy G A).homEquiv (a * b) =
      (wreathRepresentableBy G A).homEquiv a * (wreathRepresentableBy G A).homEquiv b :=
  homEquiv_mul (wreath G A) (wreathPresheaf G A ⋙ forget₂ GrpCat MonCat)
    (wreathRepresentableBy G A) a b

/-- The second projection of a product in the wreath product is the product of the second
projections. -/
@[reassoc]
lemma wreathMul_wsnd {T : C} (a b : T ⟶ wreath G A) :
    (a * b) ≫ wsnd G A = (a ≫ wsnd G A) * (b ≫ wsnd G A) :=
  congrArg SemidirectProduct.right (wreath_homEquiv_mul a b)

/-- The first projection of a product `a * b` in the wreath product is the semidirect product
formula: the first component of `a` times the translate of the first component of `b` by the second
component of `a`. -/
@[reassoc]
lemma wreathMul_wfst {T : C} (a b : T ⟶ wreath G A) :
    (a * b) ≫ wfst G A = (a ≫ wfst G A) * transl (a ≫ wsnd G A) (b ≫ wfst G A) :=
  congrArg SemidirectProduct.left (wreath_homEquiv_mul a b)

end Wreath

attribute [local instance] wreathGrpObj

/-! ## Coset separators -/

section Separator

variable {G H A : C} [GrpObj G]

/-- A morphism `u : G ⟶ A` **separates the cosets** of `i : H ⟶ G` if right translation by a
generalized element `g : T ⟶ G` leaves `u` unchanged — `u (x * g) = u x` for the generic `x` —
exactly when `g` factors through `i`.

In `Set`, with `A` the free abelian group on `G/H` and `u` the composite `G → G/H → A`, this is
the computation `(∀ x, x g H = x H) ↔ g ∈ H` of the classical proof. -/
def IsCosetSeparator (i : H ⟶ G) (u : G ⟶ A) : Prop :=
  ∀ ⦃T : C⦄ (g : T ⟶ G),
    (shear g ≫ (fst G T ≫ u) = fst G T ≫ u) ↔ ∃ h : T ⟶ H, h ≫ i = g

/-- A coset separator stays one after composition with a monomorphism. -/
lemma IsCosetSeparator.comp_mono {i : H ⟶ G} {u : G ⟶ A} (hu : IsCosetSeparator i u)
    {B : C} (m : A ⟶ B) [Mono m] : IsCosetSeparator i (u ≫ m) := by
  intro T g
  rw [← hu g]
  constructor
  · intro h
    rw [← cancel_mono m]
    simpa only [Category.assoc] using h
  · intro h
    simp only [← Category.assoc] at h ⊢
    rw [h]

variable [Closed G] [GrpObj A]

/-- The generalized element of `A^G` at stage `T` given by a morphism `u : G ⟶ A`, i.e. the
constant family with value `u`. -/
noncomputable def uconst (u : G ⟶ A) (T : C) : T ⟶ (ihom G).obj A := curry (fst G T ≫ u)

omit [GrpObj G] [GrpObj A] in
/-- The transpose of `uconst u T` is the first projection followed by `u`. -/
@[simp]
lemma uncurry_uconst (u : G ⟶ A) (T : C) : uncurry (uconst u T) = fst G T ≫ u :=
  uncurry_curry _

omit [GrpObj G] [GrpObj A] in
/-- The constant family `uconst u` is stable under reindexing along `φ : T' ⟶ T`. -/
lemma comp_uconst (u : G ⟶ A) {T T' : C} (φ : T' ⟶ T) : φ ≫ uconst u T = uconst u T' := by
  refine uncurry_injective ?_
  rw [uncurry_natural_left, uncurry_uconst, uncurry_uconst, ← Category.assoc, whiskerLeft_fst]

omit [GrpObj A] in
/-- Translation by `g` fixes `uconst u T` if and only if right translation by `g` leaves `u`
unchanged. -/
lemma transl_uconst_eq_iff (u : G ⟶ A) {T : C} (g : T ⟶ G) :
    transl g (uconst u T) = uconst u T ↔ shear g ≫ (fst G T ≫ u) = fst G T ≫ u := by
  constructor
  · intro h
    have := congrArg uncurry h
    rwa [uncurry_transl, uncurry_uconst] at this
  · intro h
    refine uncurry_injective ?_
    rw [uncurry_transl, uncurry_uconst, h]

/-- The **principal cocycle** attached to `u`, `c (g) = u⁻¹ · (g · u)`. -/
noncomputable def cocycle (u : G ⟶ A) {T : C} (g : T ⟶ G) : T ⟶ (ihom G).obj A :=
  (uconst u T)⁻¹ * transl g (uconst u T)

/-- The principal cocycle is natural in the stage: `φ ≫ cocycle u g = cocycle u (φ ≫ g)`. -/
lemma comp_cocycle (u : G ⟶ A) {T T' : C} (φ : T' ⟶ T) (g : T ⟶ G) :
    φ ≫ cocycle u g = cocycle u (φ ≫ g) := by
  rw [cocycle, cocycle, MonObj.comp_mul, GrpObj.comp_inv, comp_uconst, comp_transl, comp_uconst]

/-- The cocycle identity `c (g₁ * g₂) = c (g₁) * (g₁ · c (g₂))` for the principal cocycle. -/
lemma cocycle_mul (u : G ⟶ A) {T : C} (g₁ g₂ : T ⟶ G) :
    cocycle u (g₁ * g₂) = cocycle u g₁ * transl g₁ (cocycle u g₂) := by
  have h1 : transl g₁ ((uconst u T)⁻¹) = (transl g₁ (uconst u T))⁻¹ :=
    map_inv (translAut (A := A) g₁).toMonoidHom _
  rw [cocycle, cocycle, cocycle, transl_mul, h1, ← transl_transl]
  group

/-- The principal cocycle vanishes at `g` if and only if translation by `g` fixes `uconst u T`. -/
lemma cocycle_eq_one_iff (u : G ⟶ A) {T : C} (g : T ⟶ G) :
    cocycle u g = 1 ↔ transl g (uconst u T) = uconst u T := by
  rw [cocycle, inv_mul_eq_one, eq_comm]

/-- The homomorphism `φ : G ⟶ A^G ⋊ G`, `g ↦ (c (g), g)`. -/
noncomputable def phi (u : G ⟶ A) : G ⟶ wreath G A := wlift (cocycle u (𝟙 G)) (𝟙 G)

/-- The homomorphism `ψ : G ⟶ A^G ⋊ G`, `g ↦ (1, g)`. -/
noncomputable def psi (_u : G ⟶ A) : G ⟶ wreath G A := wlift 1 (𝟙 G)

/-- A generalized element `a` of `G` composed with `phi u` is `(c (a), a)`. -/
@[simp]
lemma comp_phi (u : G ⟶ A) {T : C} (a : T ⟶ G) : a ≫ phi u = wlift (cocycle u a) a := by
  refine wreath_hom_ext ?_ ?_
  · rw [Category.assoc, wlift_wfst, phi, wlift_wfst, comp_cocycle, Category.comp_id]
  · rw [Category.assoc, wlift_wsnd, phi, wlift_wsnd, Category.comp_id]

omit [GrpObj G] in
/-- A generalized element `a` of `G` composed with `psi u` is `(1, a)`. -/
@[simp]
lemma comp_psi (u : G ⟶ A) {T : C} (a : T ⟶ G) : a ≫ psi u = wlift 1 a := by
  refine wreath_hom_ext ?_ ?_
  · rw [Category.assoc, wlift_wfst, psi, wlift_wfst, MonObj.comp_one]
  · rw [Category.assoc, wlift_wsnd, psi, wlift_wsnd, Category.comp_id]

instance isMonHom_phi (u : G ⟶ A) : IsMonHom (phi u) := by
  refine isMonHom_of_mul' _ fun T a b => ?_
  refine wreath_hom_ext ?_ ?_
  · rw [comp_phi, wlift_wfst, wreathMul_wfst, comp_phi, comp_phi, wlift_wfst, wlift_wsnd,
      wlift_wfst, cocycle_mul]
  · rw [comp_phi, wlift_wsnd, wreathMul_wsnd, comp_phi, comp_phi, wlift_wsnd, wlift_wsnd]

instance isMonHom_psi (u : G ⟶ A) : IsMonHom (psi u) := by
  refine isMonHom_of_mul' _ fun T a b => ?_
  refine wreath_hom_ext ?_ ?_
  · have h1 : transl a (1 : T ⟶ (ihom G).obj A) = 1 :=
      map_one (translAut (A := A) a).toMonoidHom
    rw [comp_psi, wlift_wfst, wreathMul_wfst, comp_psi, comp_psi, wlift_wfst, wlift_wsnd,
      wlift_wfst, h1, _root_.one_mul]
  · rw [comp_psi, wlift_wsnd, wreathMul_wsnd, comp_psi, comp_psi, wlift_wsnd, wlift_wsnd]

/-- A generalized element `a` of `G` is equalized by `phi u` and `psi u` if and only if translation
by `a` fixes `uconst u T`. -/
lemma comp_phi_eq_comp_psi_iff (u : G ⟶ A) {T : C} (a : T ⟶ G) :
    a ≫ phi u = a ≫ psi u ↔ transl a (uconst u T) = uconst u T := by
  rw [comp_phi, comp_psi, ← cocycle_eq_one_iff]
  constructor
  · intro h
    simpa using congrArg (fun x => x ≫ wfst G A) h
  · intro h
    rw [h]

/-- Given a coset separator, a generalized element of `G` is equalized by `phi u` and `psi u`
exactly when it factors through `i`. -/
lemma comp_phi_eq_comp_psi_iff_exists {i : H ⟶ G} {u : G ⟶ A} (hu : IsCosetSeparator i u)
    {T : C} (a : T ⟶ G) : a ≫ phi u = a ≫ psi u ↔ ∃ h : T ⟶ H, h ≫ i = a := by
  rw [comp_phi_eq_comp_psi_iff, transl_uconst_eq_iff]
  exact hu a

end Separator

/-! ## Coset separators give regular monomorphisms -/

section Main

variable {X Y : Grp C} [Closed Y.X] {i : X ⟶ Y} {A : C} [GrpObj A] {u : Y.X ⟶ A}

variable (hu : IsCosetSeparator i.hom.hom u)
include hu

/-- The monomorphism `i` is equalized by `phi u` and `psi u`, when `u` separates its cosets. -/
lemma comp_phi_eq_comp_psi_of_hom : i.hom.hom ≫ phi u = i.hom.hom ≫ psi u :=
  (comp_phi_eq_comp_psi_iff_exists hu _).2 ⟨𝟙 X.X, Category.id_comp _⟩

/-- The morphism of internal groups `i` is equalized by `phi u` and `psi u`, as morphisms of
internal groups, when `u` separates its cosets. -/
lemma grp_comp_phi_eq_comp_psi :
    i ≫ (Grp.homMk (phi u) : Y ⟶ Grp.mk (wreath Y.X A)) =
      i ≫ (Grp.homMk (psi u) : Y ⟶ Grp.mk (wreath Y.X A)) :=
  Grp.hom_ext _ _ (by simpa using comp_phi_eq_comp_psi_of_hom hu)

/-- The factorization of a generalized element equalized by `phi u` and `psi u` through `i`. -/
noncomputable def separatorLift {T : C} {g : T ⟶ Y.X} (hg : g ≫ phi u = g ≫ psi u) :
    T ⟶ X.X :=
  ((comp_phi_eq_comp_psi_iff_exists hu g).1 hg).choose

/-- The factorization `separatorLift` followed by `i` is the original generalized element. -/
@[reassoc (attr := simp)]
lemma separatorLift_comp {T : C} {g : T ⟶ Y.X} (hg : g ≫ phi u = g ≫ psi u) :
    separatorLift hu hg ≫ i.hom.hom = g :=
  ((comp_phi_eq_comp_psi_iff_exists hu g).1 hg).choose_spec

/-- **A monomorphism of internal groups admitting a coset separator into an internal group is
regular**: it is the equalizer of the two homomorphisms `phi u` and `psi u` into the wreath
product `A^Y ⋊ Y`. -/
noncomputable def regularMonoOfCosetSeparator [Mono i.hom.hom] : RegularMono i where
  Z := Grp.mk (wreath Y.X A)
  left := Grp.homMk (phi u)
  right := Grp.homMk (psi u)
  w := grp_comp_phi_eq_comp_psi hu
  isLimit := by
    refine Fork.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s m hm => ?_)
    · have hg : (show s.pt ⟶ Y from s.ι).hom.hom ≫ phi u
          = (show s.pt ⟶ Y from s.ι).hom.hom ≫ psi u := by
        have := congrArg (fun t => t.hom.hom) s.condition
        simpa using this
      have : IsMonHom (separatorLift hu hg ≫ i.hom.hom) := by
        rw [separatorLift_comp]; infer_instance
      have := isMonHom_of_comp_mono (separatorLift hu hg) i.hom.hom
      exact Grp.homMk (separatorLift hu hg)
    · exact Grp.hom_ext _ _ (by simp)
    · refine Grp.hom_ext _ _ ?_
      rw [← cancel_mono i.hom.hom]
      have := congrArg (fun t => t.hom.hom) hm
      simpa using this

/-- **A monomorphism of internal groups admitting a coset separator into an internal group is a
regular monomorphism.** -/
theorem isRegularMono_of_isCosetSeparator [Mono i.hom.hom] : IsRegularMono i :=
  ⟨⟨regularMonoOfCosetSeparator hu⟩⟩

end Main

end Internal

end InternalGroups
