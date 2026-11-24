module

public import Foundations.CategoryTheory.Monoidal.ModObjFree
public import Foundations.CategoryTheory.Monoidal.ModObjColimits

/-!
# The Galois connection between submonoids and quotient modules of a monoid object

Let `C` be a monoidal category whose monoidal unit `𝟙_ C` is a terminal object, which has finite
limits and reflexive coequalizers, and in which tensoring preserves reflexive coequalizers in
each variable.  Fix a monoid object `m` of `C`.

* `InternalGroups.SubMon m` is the (pre)ordered collection of *submonoids* of `m`: monoid objects
  `n` together with a monomorphism `n ⟶ m` of monoid objects.
* `InternalGroups.QuotMod m` is the (pre)ordered collection of *quotient modules* of `m`:
  epimorphisms `m ⟶ v` in the category `Mod_ C m` of `m`-modules (the Eilenberg–Moore category of
  the monad `m ⊗ -`), where `m` is regarded as a module over itself.

The two constructions are:

* `InternalGroups.SubMon.quot`: a submonoid `n ↪ m` is sent to the reflexive coequalizer, in
  `Mod_ C m`, of the two adjoint transposes `m ⊗ n ⇉ m` of the inclusion `n ⟶ m` and of the trivial
  map `n ⟶ 𝟙_ C ⟶ m`.
* `InternalGroups.QuotMod.sub`: a quotient module `p : m ⟶ v` is sent to the pullback of the base
  point `𝟙_ C ⟶ m ⟶ v` along `p`, i.e. to the "stabiliser" `m ×_v 𝟙_ C`.

The main result is `InternalGroups.galoisConnection_quot_sub`: these two maps form a Galois
connection.

## Main results

* `InternalGroups.SubMon`: a submonoid of `m`, a monoid object with a monomorphism into `m` that is
  a morphism of monoid objects.
* `InternalGroups.QuotMod`: a quotient module of `m`, an epimorphism `m ⟶ V` of `m`-modules.
* `InternalGroups.SubMon.quot`: the quotient module attached to a submonoid.
* `InternalGroups.QuotMod.sub`: the submonoid attached to a quotient module.
* `InternalGroups.galoisConnection_quot_sub`: `SubMon.quot` and `QuotMod.sub` form a Galois
  connection.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VII.3
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section MonObjOfMono

/-- A subobject of a monoid object which is closed under the unit and the multiplication is
itself a monoid object. -/
@[instance_reducible, simps one mul]
def monObjOfMono {n m : C} [MonObj m] (i : n ⟶ m) [Mono i]
    (one : 𝟙_ C ⟶ n) (mul : n ⊗ n ⟶ n)
    (hone : one ≫ i = η[m]) (hmul : mul ≫ i = (i ⊗ₘ i) ≫ μ[m]) : MonObj n where
  one := one
  mul := mul
  one_mul := by
    rw [← cancel_mono i, Category.assoc, hmul, MonoidalCategory.tensorHom_def]
    simp only [← Category.assoc]
    rw [← comp_whiskerRight, hone, ← whisker_exchange]
    simp only [Category.assoc]
    rw [MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    rw [← cancel_mono i, Category.assoc, hmul, MonoidalCategory.tensorHom_def']
    simp only [← Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, hone, whisker_exchange]
    simp only [Category.assoc]
    rw [MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    rw [← cancel_mono i, Category.assoc, hmul, Category.assoc, Category.assoc, hmul]
    have hl : (mul ▷ n) ≫ (i ⊗ₘ i) = ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[m] ▷ m) := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hmul, Category.comp_id, Category.id_comp]
    have hr : (n ◁ mul) ≫ (i ⊗ₘ i) = (i ⊗ₘ i ⊗ₘ i) ≫ (m ◁ μ[m]) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hmul, Category.comp_id, Category.id_comp]
    rw [reassoc_of% hl, reassoc_of% hr, MonObj.mul_assoc, ← Category.assoc,
      associator_naturality, Category.assoc]

/-- The inclusion of a subobject with the induced monoid structure is a monoid morphism. -/
lemma isMonHom_monObjOfMono {n m : C} [MonObj m] (i : n ⟶ m) [Mono i]
    (one : 𝟙_ C ⟶ n) (mul : n ⊗ n ⟶ n)
    (hone : one ≫ i = η[m]) (hmul : mul ≫ i = (i ⊗ₘ i) ≫ μ[m]) :
    letI := monObjOfMono i one mul hone hmul
    IsMonHom i :=
  letI := monObjOfMono i one mul hone hmul
  { one_hom := hone, mul_hom := hmul }

end MonObjOfMono

/-- A monoid object, viewed as a module over itself. -/
@[implicit_reducible]
noncomputable def selfMod (m : C) [MonObj m] : CategoryTheory.Mod C m :=
  letI := ModObj.regular m; ⟨m⟩

/-- The underlying object of `selfMod m` is `m`. -/
@[simp]
lemma selfMod_X (m : C) [MonObj m] : (selfMod m).X = m := rfl

/-- `selfMod m` is Mathlib's `CategoryTheory.Mod.regular m`. It is kept as its own definition
because the proofs here need `(selfMod m).X` to reduce to `m` at instance transparency, which
Mathlib's `Mod.regular` (a plain `def`) does not. -/
lemma selfMod_eq_regular (m : C) [MonObj m] : selfMod m = CategoryTheory.Mod.regular m := rfl

/-- The action of `m` on `selfMod m` is the multiplication `μ[m]`. -/
@[simp]
lemma selfMod_smul (m : C) [MonObj m] : γ[m, (selfMod m).X] = μ[m] := rfl

/-- A **submonoid** of a monoid object `m`: a monoid object `N` together with a monomorphism
`N.X ⟶ m` which is a morphism of monoid objects. -/
structure SubMon (m : C) [MonObj m] where
  /-- the underlying monoid object -/
  N : Mon C
  /-- the inclusion -/
  i : N.X ⟶ m
  [mono_i : Mono i]
  [isMonHom_i : IsMonHom i]

attribute [instance] SubMon.mono_i SubMon.isMonHom_i

/-- A **quotient module** of a monoid object `m`: an epimorphism `m ⟶ V` in the category of
`m`-modules, where `m` is regarded as a module over itself. -/
structure QuotMod (m : C) [MonObj m] where
  /-- the underlying `m`-module -/
  V : CategoryTheory.Mod C m
  /-- the quotient map -/
  p : selfMod m ⟶ V
  [epi_p : Epi p]

attribute [instance] QuotMod.epi_p

variable {m : C} [MonObj m]

/-- Submonoids are preordered by factorisation of the inclusions. -/
instance : Preorder (SubMon m) where
  le a b := ∃ f : a.N.X ⟶ b.N.X, f ≫ b.i = a.i
  le_refl a := ⟨𝟙 _, by simp⟩
  le_trans a b c := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩

/-- Quotient modules are preordered by factorisation of the quotient maps: `a ≤ b` means that
`b` is a further quotient of `a`. -/
instance : Preorder (QuotMod m) where
  le a b := ∃ h : a.V ⟶ b.V, a.p ≫ h = b.p
  le_refl a := ⟨𝟙 _, by simp⟩
  le_trans a b c := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f ≫ g, by rw [← Category.assoc, hf, hg]⟩

/-! ## From submonoids to quotient modules -/

namespace SubMon

variable (hunit : IsTerminal (𝟙_ C)) (s : SubMon m)

/-- The adjoint transpose `m ⊗ n ⟶ m` of the inclusion `n ⟶ m`. -/
noncomputable def mulTranspose : (freeMod m).obj s.N.X ⟶ selfMod m :=
  ((freeModAdj m).homEquiv s.N.X (selfMod m)).symm s.i

/-- The adjoint transpose `m ⊗ n ⟶ m` of the trivial map `n ⟶ 𝟙_ C ⟶ m`. -/
noncomputable def oneTranspose : (freeMod m).obj s.N.X ⟶ selfMod m :=
  ((freeModAdj m).homEquiv s.N.X (selfMod m)).symm (hunit.from s.N.X ≫ η[m])

/-- The underlying morphism of `mulTranspose s` is `m ⊗ n ⟶ m`, `(x, a) ↦ x · i a`. -/
@[simp]
lemma mulTranspose_hom : (mulTranspose s).hom = m ◁ s.i ≫ μ[m] := by
  rw [mulTranspose, freeModAdj_homEquiv_symm_hom]; rfl

/-- The underlying morphism of `oneTranspose hunit s` is `m ⊗ n ⟶ m`, `(x, a) ↦ x`
(written as `x · 1`). -/
@[simp]
lemma oneTranspose_hom :
    (oneTranspose hunit s).hom = m ◁ (hunit.from s.N.X ≫ η[m]) ≫ μ[m] :=
  freeModAdj_homEquiv_symm_hom _ _

/-- The common section of the two transposes, given by the unit of `n`. -/
noncomputable def commonSection : selfMod m ⟶ (freeMod m).obj s.N.X where
  hom := (ρ_ m).inv ≫ m ◁ η[s.N.X]
  isModHom := ⟨by
    change μ[m] ≫ (ρ_ m).inv ≫ m ◁ η[s.N.X] =
      m ◁ ((ρ_ m).inv ≫ m ◁ η[s.N.X]) ≫ (α_ m m s.N.X).inv ≫ μ[m] ▷ s.N.X
    have h : m ◁ (ρ_ m).inv ≫ (α_ m m (𝟙_ C)).inv = (ρ_ (m ⊗ m)).inv := by monoidal
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange, ← Category.assoc,
      ← Category.assoc, h, Category.assoc, ← rightUnitor_inv_naturality_assoc]⟩

/-- The underlying morphism of `commonSection s` is `(ρ_ m).inv ≫ m ◁ η[s.N.X]`. -/
@[simp]
lemma commonSection_hom : (commonSection s).hom = (ρ_ m).inv ≫ m ◁ η[s.N.X] := rfl

/-- `commonSection s` is a section of `mulTranspose s`. -/
lemma commonSection_mulTranspose : commonSection s ≫ mulTranspose s = 𝟙 _ := by
  apply CategoryTheory.Mod.Hom.ext
  rw [CategoryTheory.Mod.comp_hom', commonSection_hom, mulTranspose_hom,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, IsMonHom.one_hom]
  simp

include hunit in
/-- `commonSection s` is a section of `oneTranspose hunit s`. -/
lemma commonSection_oneTranspose :
    commonSection s ≫ oneTranspose hunit s = 𝟙 _ := by
  apply CategoryTheory.Mod.Hom.ext
  have ht : η[s.N.X] ≫ hunit.from s.N.X ≫ η[m] = η[m] := by
    rw [← Category.assoc, hunit.hom_ext (η[s.N.X] ≫ hunit.from s.N.X) (𝟙 _), Category.id_comp]
  rw [CategoryTheory.Mod.comp_hom', commonSection_hom, oneTranspose_hom,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ht]
  simp

/-- The "unit" section `n ⟶ m ⊗ n`, used to restrict a morphism out of the free module. -/
noncomputable def unitLeft : s.N.X ⟶ m ⊗ s.N.X := (λ_ s.N.X).inv ≫ η[m] ▷ s.N.X

/-- For `g : n ⟶ m`, the unit section followed by `(x, a) ↦ x · g a` is `g`. -/
lemma unitLeft_comp' {n : C} (g : n ⟶ m) :
    ((λ_ n).inv ≫ η[m] ▷ n) ≫ (m ◁ g ≫ μ[m]) = g := by
  rw [Category.assoc, ← whisker_exchange_assoc, MonObj.one_mul, leftUnitor_naturality]
  simp

/-- `unitLeft s` followed by the underlying morphism of `mulTranspose s` is `s.i`. -/
lemma unitLeft_mulTranspose : unitLeft s ≫ (mulTranspose s).hom = s.i := by
  rw [mulTranspose_hom, unitLeft]
  exact unitLeft_comp' (m := m) s.i

/-- `unitLeft s` followed by the underlying morphism of `oneTranspose hunit s` is
`hunit.from s.N.X ≫ η[m]`. -/
lemma unitLeft_oneTranspose :
    unitLeft s ≫ (oneTranspose hunit s).hom = hunit.from s.N.X ≫ η[m] := by
  rw [oneTranspose_hom, unitLeft]
  exact unitLeft_comp' (m := m) (hunit.from s.N.X ≫ η[m])

/-- The two transposes form a reflexive pair, with common section `commonSection s`. -/
lemma isReflexivePair : IsReflexivePair (mulTranspose s) (oneTranspose hunit s) :=
  ⟨commonSection s, commonSection_mulTranspose s, commonSection_oneTranspose hunit s⟩

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C m)]

/-- The two transposes have a coequalizer in the category of `m`-modules. -/
instance hasCoequalizer_transposes :
    HasCoequalizer (mulTranspose s) (oneTranspose hunit s) := by
  have := isReflexivePair hunit s
  exact HasReflexiveCoequalizers.has_coeq _ _

/-- **The quotient module attached to a submonoid**: the coequalizer, in `Mod_ C m`, of the two
adjoint transposes. -/
noncomputable def quot : QuotMod m where
  V := coequalizer (mulTranspose s) (oneTranspose hunit s)
  p := coequalizer.π _ _
/-- The quotient map of `quot hunit s` is the coequalizer projection. -/
@[simp] lemma quot_p : (quot hunit s).p = coequalizer.π _ _ := rfl

end SubMon

/-! ## From quotient modules to submonoids -/

namespace QuotMod

variable (hunit : IsTerminal (𝟙_ C)) (q : QuotMod m)

/-- The base point of a quotient module: the image of the unit of `m`. -/
noncomputable def basePoint : 𝟙_ C ⟶ q.V.X := η[m] ≫ q.p.hom

include hunit in
/-- Since `𝟙_ C` is terminal (`hunit`), the base point `basePoint q` is a monomorphism. -/
lemma mono_basePoint : Mono (basePoint q) :=
  ⟨fun _ _ _ => hunit.hom_ext _ _⟩

/-- Equivariance of the quotient map, in the form used below. -/
lemma mul_comp_p : μ[m] ≫ q.p.hom = m ◁ q.p.hom ≫ γ[m, q.V.X] := by
  have := IsModHom.smul_hom (A := m) (f := q.p.hom)
  simpa using this

/-- `m ◁ basePoint q ≫ γ[m, q.V.X] = (ρ_ m).hom ≫ q.p.hom`. -/
lemma unit_whisker_comp_p :
    m ◁ basePoint q ≫ γ[m, q.V.X] = (ρ_ m).hom ≫ q.p.hom := by
  rw [basePoint, MonoidalCategory.whiskerLeft_comp, Category.assoc, ← mul_comp_p q,
    ← Category.assoc, MonObj.mul_one]

variable [HasPullbacks C]

/-- The underlying object of the submonoid attached to a quotient module: the pullback of the
base point along the quotient map. -/
noncomputable abbrev subObj : C := pullback q.p.hom (basePoint q)

/-- The inclusion of the submonoid attached to a quotient module. -/
noncomputable abbrev subIncl : subObj q ⟶ m := pullback.fst _ _

include hunit in
/-- The inclusion `subIncl q` of the pullback of the base point is a monomorphism. -/
lemma mono_subIncl : Mono (subIncl q) := by
  have := mono_basePoint hunit q
  infer_instance

include hunit in
/-- The inclusion followed by the quotient map is constant at the base point. -/
lemma subIncl_comp_p :
    subIncl q ≫ q.p.hom = hunit.from (subObj q) ≫ basePoint q := by
  rw [pullback.condition]
  congr 1
  exact hunit.hom_ext _ _

/-- The unit of the submonoid attached to a quotient module. -/
noncomputable def subOne : 𝟙_ C ⟶ subObj q :=
  pullback.lift η[m] (𝟙 _) (by simp [basePoint])

/-- The unit of the submonoid `subObj q`, followed by the inclusion, is the unit of `m`. -/
@[reassoc (attr := simp)]
lemma subOne_comp : subOne q ≫ subIncl q = η[m] := by simp [subOne]

/-- The multiplication of the submonoid attached to a quotient module. -/
noncomputable def subMul : subObj q ⊗ subObj q ⟶ subObj q :=
  pullback.lift ((subIncl q ⊗ₘ subIncl q) ≫ μ[m]) (hunit.from _) (by
    have e1 : (subIncl q ⊗ₘ subIncl q) ≫ m ◁ q.p.hom
        = (subObj q ◁ (subIncl q ≫ q.p.hom)) ≫ (subIncl q ▷ q.V.X) := by
      rw [tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        whisker_exchange]
    calc ((subIncl q ⊗ₘ subIncl q) ≫ μ[m]) ≫ q.p.hom
        = (subIncl q ⊗ₘ subIncl q) ≫ m ◁ q.p.hom ≫ γ[m, q.V.X] := by
          rw [Category.assoc, mul_comp_p q]
      _ = (subObj q ◁ (subIncl q ≫ q.p.hom)) ≫ (subIncl q ▷ q.V.X) ≫ γ[m, q.V.X] := by
          rw [← Category.assoc, e1, Category.assoc]
      _ = (subObj q ◁ hunit.from (subObj q)) ≫ (subObj q ◁ basePoint q) ≫
            (subIncl q ▷ q.V.X) ≫ γ[m, q.V.X] := by
          rw [subIncl_comp_p hunit q, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = (subObj q ◁ hunit.from (subObj q)) ≫ (subIncl q ▷ 𝟙_ C) ≫
            (m ◁ basePoint q) ≫ γ[m, q.V.X] := by
          rw [whisker_exchange_assoc]
      _ = (subObj q ◁ hunit.from (subObj q)) ≫ (subIncl q ▷ 𝟙_ C) ≫ (ρ_ m).hom ≫ q.p.hom := by
          rw [unit_whisker_comp_p q]
      _ = (subObj q ◁ hunit.from (subObj q)) ≫ (ρ_ (subObj q)).hom ≫ subIncl q ≫ q.p.hom := by
          rw [rightUnitor_naturality_assoc]
      _ = hunit.from (subObj q ⊗ subObj q) ≫ basePoint q := by
          rw [subIncl_comp_p hunit q, ← Category.assoc, ← Category.assoc]
          congr 1
          exact hunit.hom_ext _ _)

/-- The multiplication of `subObj q` is compatible with that of `m` along the inclusion. -/
@[reassoc (attr := simp)]
lemma subMul_comp :
    subMul hunit q ≫ subIncl q = (subIncl q ⊗ₘ subIncl q) ≫ μ[m] := by simp [subMul]

/-- **The submonoid attached to a quotient module**: the pullback of the base point along the
quotient map. -/
@[implicit_reducible]
noncomputable def sub : SubMon m :=
  letI := mono_subIncl hunit q
  letI : MonObj (subObj q) :=
    monObjOfMono (subIncl q) (subOne q) (subMul hunit q) (subOne_comp q) (subMul_comp hunit q)
  { N := ⟨subObj q⟩
    i := subIncl q
    isMonHom_i := isMonHom_monObjOfMono (subIncl q) (subOne q) (subMul hunit q)
      (subOne_comp q) (subMul_comp hunit q) }

end QuotMod

/-! ## The Galois connection -/

section Galois

variable (hunit : IsTerminal (𝟙_ C)) [HasPullbacks C]

/-- A submonoid `n ⟶ m` is contained in the submonoid attached to a quotient module `p : m ⟶ v`
if and only if `p` kills `n`, i.e. `n ⟶ m ⟶ v` factors through the base point. -/
lemma SubMon.le_sub_iff (s : SubMon m) (q : QuotMod m) :
    s ≤ QuotMod.sub hunit q ↔
      s.i ≫ q.p.hom = hunit.from s.N.X ≫ QuotMod.basePoint q := by
  constructor
  · rintro ⟨f, hf⟩
    rw [← hf, Category.assoc]
    rw [show (QuotMod.sub hunit q).i = QuotMod.subIncl q from rfl,
      QuotMod.subIncl_comp_p hunit q, ← Category.assoc]
    congr 1
    exact hunit.hom_ext _ _
  · intro h
    exact ⟨pullback.lift s.i (hunit.from _) h, by simp [QuotMod.sub]⟩

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C m)]

/-- **The Galois connection between submonoids and quotient modules of a monoid object.** -/
theorem galoisConnection_quot_sub :
    GaloisConnection (fun s : SubMon m => SubMon.quot hunit s)
      (fun q : QuotMod m => QuotMod.sub hunit q) := by
  intro s q
  rw [SubMon.le_sub_iff]
  constructor
  · rintro ⟨h, hh⟩
    have hcond := coequalizer.condition (SubMon.mulTranspose s) (SubMon.oneTranspose hunit s)
    have hcond' : (SubMon.mulTranspose s).hom ≫ (SubMon.quot hunit s).p.hom
        = (SubMon.oneTranspose hunit s).hom ≫ (SubMon.quot hunit s).p.hom :=
      congr(($hcond).hom)
    have hp : (SubMon.quot hunit s).p.hom ≫ h.hom = q.p.hom := by
      rw [← CategoryTheory.Mod.comp_hom', hh]
    calc s.i ≫ q.p.hom
        = (SubMon.unitLeft s ≫ (SubMon.mulTranspose s).hom) ≫
            (SubMon.quot hunit s).p.hom ≫ h.hom := by
          rw [SubMon.unitLeft_mulTranspose, hp]
      _ = (SubMon.unitLeft s ≫ (SubMon.oneTranspose hunit s).hom) ≫
            (SubMon.quot hunit s).p.hom ≫ h.hom := by
          rw [Category.assoc, Category.assoc, ← Category.assoc (SubMon.mulTranspose s).hom,
            hcond', Category.assoc]
      _ = hunit.from s.N.X ≫ QuotMod.basePoint q := by
          rw [SubMon.unitLeft_oneTranspose hunit s, hp, Category.assoc]
          rfl
  · intro h
    have hco : SubMon.mulTranspose s ≫ q.p = SubMon.oneTranspose hunit s ≫ q.p := by
      apply CategoryTheory.Mod.Hom.ext
      rw [CategoryTheory.Mod.comp_hom', CategoryTheory.Mod.comp_hom',
        SubMon.mulTranspose_hom, SubMon.oneTranspose_hom, Category.assoc, Category.assoc,
        QuotMod.mul_comp_p q, ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, h]
      simp [QuotMod.basePoint]
    exact ⟨coequalizer.desc q.p hco, coequalizer.π_desc _ _⟩

end Galois

end InternalGroups
