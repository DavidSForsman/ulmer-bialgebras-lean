module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import InternalGroups.GrpSubQuot
public import Foundations.CategoryTheory.Monoidal.ReflexivePairWhisker
public import Foundations.CategoryTheory.Monoidal.CartesianHomExt

/-!
# Newman's correspondence for internal groups

Let `C` be a cartesian monoidal category with finite limits and reflexive coequalizers, in
which the tensor product preserves reflexive coequalizers in each variable.  For a group
object `H : Grp C` this file constructs the **Galois connection**

* `InternalGroups.SubGrpObj.quot` (left adjoint) — the quotient of `H` by a subgroup object `S`,
  namely the coequalizer of the reflexive pair `(g, z) ↦ g z`, `(g, z) ↦ g` on `H ⊗ S`,
  together with the residual left translation action of `H` on it; this is an object of
  `C^H`, the category of `H`-objects;
* `InternalGroups.QuotObj.kernelSub` (right adjoint, in `GrpSubQuot.lean`) — the kernel of an
  equivariant quotient,

and proves the adjunction

* `InternalGroups.SubGrpObj.quot_le_iff` : `S.quot ≤ P ↔ S ≤ P.kernelSub`,

as well as the unit inequality (`InternalGroups.SubGrpObj.le_kernelSub_quot`).  **Newman's
correspondence** is the assertion that this Galois connection restricts to an isomorphism
between the `M`-subobjects and the `E`-quotients of `H`, for every `H`; it is not formalized
in this file.

Since the notion of exactness used in this development fixes the right class `M` of the
factorization system to be the class of all monomorphisms (and the left class `E` is then
the class `UlmerBialgebras.extremalEpi` of regular epimorphisms), a `M`-subobject of `H` is here an
arbitrary subgroup object, and an `E`-quotient is an equivariant quotient whose structural
morphism is a regular epimorphism.

## Main results

* `InternalGroups.SubGrpObj.quot`: the quotient of `H` by a subgroup object `S`, as an equivariant
  quotient of `H`.
* `InternalGroups.SubGrpObj.quot_le_iff`: `S.quot ≤ P ↔ S ≤ P.kernelSub`.
* `InternalGroups.SubGrpObj.le_kernelSub_quot`: `S ≤ S.quot.kernelSub`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 6
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

namespace InternalGroups

open UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace SubGrpObj

variable {H : Grp C} (S : SubGrpObj H)

/-! ## The quotient of a group object by a subgroup object -/

/-- The left leg of the coset pair of a subgroup object: `(g, z) ↦ g z`. -/
noncomputable def cosetMul : H.X ⊗ S.N ⟶ H.X := (H.X ◁ S.n) ≫ μ[H.X]

/-- On generalized elements, the coset multiplication is `(g, z) ↦ g · S.n z`. -/
@[simp]
lemma lift_cosetMul {T : C} (g : T ⟶ H.X) (z : T ⟶ S.N) :
    lift g z ≫ S.cosetMul = g * (z ≫ S.n) := by
  rw [cosetMul, ← Category.assoc, lift_whiskerLeft, Hom.mul_def]

/-- The coset pair of a subgroup object is a reflexive pair. -/
instance isReflexivePair_coset : IsReflexivePair S.cosetMul (fst H.X S.N) := by
  obtain ⟨z₀, hz₀⟩ := S.one_mem H.X
  refine ⟨⟨lift (𝟙 H.X) z₀, ?_, ?_⟩⟩
  · rw [lift_cosetMul, hz₀, mul_one]
  · exact lift_fst _ _

variable [HasReflexiveCoequalizers C]

/-- The underlying object of the quotient of `H` by the subgroup object `S`. -/
noncomputable def quotObj : C := coequalizer S.cosetMul (fst H.X S.N)

/-- The quotient morphism `H ⟶ H/S`. -/
noncomputable def quotπ : H.X ⟶ S.quotObj := coequalizer.π _ _

/-- The quotient morphism `H → H/S` is an epimorphism. -/
instance : Epi S.quotπ := coequalizer.π_epi

/-- The quotient morphism is the coequalizer of the coset pair. -/
noncomputable def quotIsColimit :
    IsColimit (Cofork.ofπ S.quotπ (coequalizer.condition S.cosetMul (fst H.X S.N))) :=
  coequalizerIsCoequalizer _ _

/-- The quotient morphism coequalizes the coset pair: `(g, z) ↦ g · z` and `(g, z) ↦ g`. -/
lemma quotπ_condition : S.cosetMul ≫ S.quotπ = (fst H.X S.N) ≫ S.quotπ :=
  coequalizer.condition _ _

/-- Multiplying by an element of `S` does not change the class in the quotient. -/
lemma quotπ_mul_mem {T : C} (g : T ⟶ H.X) {x : T ⟶ H.X} (hx : S.Mem x) :
    (g * x) ≫ S.quotπ = g ≫ S.quotπ := by
  obtain ⟨z, rfl⟩ := hx
  have h := lift g z ≫= S.quotπ_condition
  simp only [← Category.assoc, lift_cosetMul, lift_fst] at h
  exact h

/-- An element of `S` is killed by the quotient morphism. -/
lemma quotπ_mem {T : C} {x : T ⟶ H.X} (hx : S.Mem x) :
    x ≫ S.quotπ = (1 : T ⟶ H.X) ≫ S.quotπ := by
  have := S.quotπ_mul_mem (1 : T ⟶ H.X) hx
  rwa [one_mul] at this

/-- The universal property of the quotient, elementwise. -/
lemma quotπ_desc {D : C} (f : H.X ⟶ D)
    (hf : ∀ {T : C} (g : T ⟶ H.X) {x : T ⟶ H.X}, S.Mem x → (g * x) ≫ f = g ≫ f) :
    ∃! v : S.quotObj ⟶ D, S.quotπ ≫ v = f := by
  have hcond : S.cosetMul ≫ f = (fst H.X S.N) ≫ f := by
    refine hom_ext_lift ?_
    intro T g z
    rw [← Category.assoc, ← Category.assoc, lift_cosetMul, lift_fst]
    exact hf g ⟨z, rfl⟩
  refine ⟨coequalizer.desc f hcond, coequalizer.π_desc _ _, fun v hv => ?_⟩
  exact (cancel_epi S.quotπ).1 (hv.trans (coequalizer.π_desc f hcond).symm)

section Action

variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)] in
/-- `H ◁ cosetMul` and `H ◁ fst` have equal composites with `μ[H.X] ≫ quotπ`. -/
lemma quotAct_cond :
    (H.X ◁ S.cosetMul) ≫ (μ[H.X] ≫ S.quotπ) = (H.X ◁ (fst H.X S.N)) ≫ (μ[H.X] ≫ S.quotπ) := by
  refine hom_ext_lift₃ ?_
  intro T a b c
  simp only [← Category.assoc, lift_whiskerLeft, lift_cosetMul, lift_fst, ← Hom.mul_def]
  rw [← mul_assoc]
  exact S.quotπ_mul_mem (a * b) ⟨c, rfl⟩

/-- The residual left translation action of `H` on the quotient `H/S`. -/
noncomputable def quotAct : H.X ⊗ S.quotObj ⟶ S.quotObj :=
  Cofork.IsColimit.desc (isColimitCoforkWhiskerLeft S.quotIsColimit H.X) (μ[H.X] ≫ S.quotπ)
    S.quotAct_cond

/-- `(H ◁ quotπ) ≫ quotAct = μ[H.X] ≫ quotπ`. -/
lemma whiskerLeft_quotπ_quotAct : (H.X ◁ S.quotπ) ≫ S.quotAct = μ[H.X] ≫ S.quotπ := by
  exact Cofork.IsColimit.π_desc' (isColimitCoforkWhiskerLeft S.quotIsColimit H.X)
    (μ[H.X] ≫ S.quotπ) S.quotAct_cond

/-- The quotient morphism is equivariant. -/
lemma lift_quotAct {T : C} (h g : T ⟶ H.X) :
    lift h (g ≫ S.quotπ) ≫ S.quotAct = (h * g) ≫ S.quotπ := by
  rw [← lift_whiskerLeft, Category.assoc, whiskerLeft_quotπ_quotAct, ← Category.assoc,
    ← Hom.mul_def]

/-- Unit law of `quotAct`: the unit of `H` acts as the identity on `H/S`. -/
lemma quotAct_one : lift (1 : S.quotObj ⟶ H.X) (𝟙 S.quotObj) ≫ S.quotAct = 𝟙 S.quotObj := by
  rw [← cancel_epi S.quotπ, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id]
  have := S.lift_quotAct (1 : H.X ⟶ H.X) (𝟙 H.X)
  rwa [Category.id_comp, one_mul, Category.id_comp] at this

/-- Associativity of `quotAct`: `a · (b · x) = (a b) · x`. -/
lemma quotAct_assoc :
    (H.X ◁ S.quotAct) ≫ S.quotAct =
      lift ((fst H.X (H.X ⊗ S.quotObj)) * (snd H.X (H.X ⊗ S.quotObj) ≫ fst H.X S.quotObj))
        (snd H.X (H.X ⊗ S.quotObj) ≫ snd H.X S.quotObj) ≫ S.quotAct := by
  have : Epi (H.X ◁ S.quotπ) :=
    epi_of_isColimit_cofork (isColimitCoforkWhiskerLeft S.quotIsColimit H.X)
  have : IsReflexivePair (H.X ◁ S.cosetMul) (H.X ◁ (fst H.X S.N)) :=
    CategoryTheory.isReflexivePair_map (tensorLeft H.X) inferInstance
  have : Epi (H.X ◁ (H.X ◁ S.quotπ)) :=
    epi_of_isColimit_cofork
      (isColimitCoforkWhiskerLeft (isColimitCoforkWhiskerLeft S.quotIsColimit H.X) H.X)
  rw [← cancel_epi (H.X ◁ (H.X ◁ S.quotπ))]
  refine hom_ext_lift₃ ?_
  intro T a b c
  simp only [← Category.assoc, lift_whiskerLeft, comp_lift, MonObj.comp_mul, lift_fst, lift_snd,
    S.lift_quotAct, mul_assoc]

/-- **The quotient of `H` by a subgroup object**, an object of `C^H` together with an
equivariant quotient morphism: the left adjoint of Newman's Galois connection. -/
noncomputable def quot : QuotObj H where
  Q := S.quotObj
  act := S.quotAct
  q := S.quotπ
  epi := inferInstance
  act_one {T} y := by
    have h : lift (1 : T ⟶ H.X) y = y ≫ lift (1 : S.quotObj ⟶ H.X) (𝟙 S.quotObj) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [h, Category.assoc, S.quotAct_one, Category.comp_id]
  act_mul {T} h k y := by
    have hL : lift h (lift k y ≫ S.quotAct) = lift h (lift k y) ≫ (H.X ◁ S.quotAct) := by
      rw [lift_whiskerLeft]
    have hR : lift (h * k) y = lift h (lift k y) ≫
        lift ((fst H.X (H.X ⊗ S.quotObj)) * (snd H.X (H.X ⊗ S.quotObj) ≫ fst H.X S.quotObj))
          (snd H.X (H.X ⊗ S.quotObj) ≫ snd H.X S.quotObj) := by
      rw [comp_lift, MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd, lift_fst,
        ← Category.assoc, lift_snd, lift_snd]
    rw [hL, hR, Category.assoc, Category.assoc, S.quotAct_assoc]
  equivariant := S.lift_quotAct

/-- The quotient map of the equivariant quotient `S.quot` is `S.quotπ`. -/
@[simp] lemma quot_q : (S.quot).q = S.quotπ := rfl

end Action

end SubGrpObj

/-! ## The Galois connection -/

section Galois

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]
variable {H : Grp C}

/-- **The Galois connection of Newman's correspondence.**  The quotient of `H` by a
subgroup object `S` is smaller than the equivariant quotient `P` exactly when `S` is
contained in the kernel of `P`. -/
theorem SubGrpObj.quot_le_iff (S : SubGrpObj H) (P : QuotObj H) :
    (S.quot).Le P ↔ S.Le (P.kernelSub) := by
  constructor
  · rintro ⟨h, hh⟩
    rw [SubGrpObj.le_iff_mem]
    intro T x hx
    rw [QuotObj.mem_kernelSub, ← hh]
    change x ≫ S.quotπ ≫ h = (1 : T ⟶ H.X) ≫ S.quotπ ≫ h
    exact (Category.assoc _ _ _).symm.trans
      ((S.quotπ_mem hx =≫ h).trans (Category.assoc _ _ _))
  · intro hS
    rw [SubGrpObj.le_iff_mem] at hS
    have hcond : ∀ {T : C} (g : T ⟶ H.X) {x : T ⟶ H.X}, S.Mem x → (g * x) ≫ P.q = g ≫ P.q := by
      intro T g x hx
      have hx' : x ≫ P.q = (1 : T ⟶ H.X) ≫ P.q := (P.mem_kernelSub x).1 (hS x hx)
      calc (g * x) ≫ P.q = P.smul g (x ≫ P.q) := (P.equivariant g x).symm
        _ = P.smul g ((1 : T ⟶ H.X) ≫ P.q) := by rw [hx']
        _ = (g * 1) ≫ P.q := P.equivariant g 1
        _ = g ≫ P.q := by rw [mul_one]
    obtain ⟨v, hv, -⟩ := S.quotπ_desc P.q hcond
    exact ⟨v, hv⟩

/-- The unit of the Galois connection: a subgroup object is contained in the kernel of the
quotient by it. -/
theorem SubGrpObj.le_kernelSub_quot (S : SubGrpObj H) : S.Le ((S.quot).kernelSub) :=
  (S.quot_le_iff (S.quot)).1 (QuotObj.le_refl _)

end Galois

end InternalGroups
