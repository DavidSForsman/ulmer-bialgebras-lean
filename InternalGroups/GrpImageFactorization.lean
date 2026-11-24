module

public import InternalGroups.GrpStablyEpi

/-!
# Images and factorizations in `Grp C` from effective coset relations

Standing hypotheses: `C` is cartesian monoidal with finite limits and reflexive coequalizers which
the binary product preserves, so that `Grp C` is pointed, protomodular, finitely complete and has
reflexive coequalizers computed in `C`.

This file shows that the **effectivity of the coset relations of `C`** (`CosetInjective C`) already
produces the image factorization of `Grp C`:

> Every morphism of `Grp C` factors as an extremal epimorphism followed by a monomorphism
> (`InternalGroups.isExtremalEpi_grpImageFactor`, `InternalGroups.mono_grpImageι`,
> `InternalGroups.grpImageFactor_comp_ι`).

No hypothesis on the epimorphisms of `C` is needed.  In particular the extremal epi–mono
factorizations that the earlier development *assumed* are automatic.

## The construction

For a morphism of monoid objects `u : A ⟶ m` — not assumed monic — the pair of adjoint transposes

```
(freeMod m).obj A  ⇉  selfMod m ,      (x, a) ↦ x · u a  and  (x, a) ↦ x
```

is reflexive, so it has a coequalizer `homQuot u : QuotMod m`, the quotient of `m` by the image of
`u`; for a subgroup object this is the coset quotient of
`InternalGroups/SubMonQuotGalois.lean` (and the two constructions agree definitionally).
The **image** of a morphism `f : X ⟶ Y` of `Grp C` is then the subgroup object

```
InternalGroups.grpImage f := stab (homQuot f)   ≤   Y ,
```

the stabiliser of the base point of `Y / f(X)`.  Two facts make this work:

* `f` kills its own quotient (`InternalGroups.kills_grpImage`), so it factors through the image —
  this is unconditional;
* if `f` factors through *any* subgroup object `s ≤ Y`, then `grpImage f ≤ s`
  (`InternalGroups.grpImage_le`) — here the injectivity of Newman's correspondence is used, in the
  form `stab s.quot ≤ s`.

Minimality immediately gives that the first factor `X ⟶ grpImage f` is an extremal epimorphism.

## Consequences for balancedness

The image factorization reduces the balancedness of `Grp C` to a single statement about
epimorphisms: `Grp C` is balanced **iff** every epimorphism of `Grp C` is an extremal
epimorphism.  A sufficient condition is that epimorphisms of `Grp C` be epimorphic in `C` (for
`C = Set` this is the classical theorem that epimorphisms of groups are surjective, which is *not*
a formal consequence of the hypotheses used here).  These remarks are not formalized here.

Independently of that, `Grp C` is always **balanced over `C`**: a monomorphism whose underlying
morphism is epimorphic in `C` is an isomorphism (`InternalGroups.isIso_of_mono_of_epi_hom`, in
`InternalGroups/GrpStablyEpi.lean`).

## Main results

* `InternalGroups.homQuot`, `InternalGroups.homQuot_le`;
* `InternalGroups.grpImage`, `InternalGroups.grpImage_le`;
* `InternalGroups.grpImageFactor`, `InternalGroups.isExtremalEpi_grpImageFactor`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Barr, *Exact categories*][Ba]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory CategoryTheory.LiftedOFS

open CategoryTheory.LiftedOFS


/-! ## The quotient of a monoid object by the image of a morphism -/

section General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {m : C} [MonObj m]
variable {A B : C}

/-- The adjoint transpose `m ⊗ A ⟶ m`, `(x, a) ↦ x · u a`, of a morphism `u : A ⟶ m`.  For a
subgroup object this is the coset relation, `InternalGroups.SubMon.mulTranspose`. -/
noncomputable def homMulTranspose (u : A ⟶ m) : (freeMod m).obj A ⟶ selfMod m :=
  ((freeModAdj m).homEquiv A (selfMod m)).symm u

/-- The adjoint transpose `m ⊗ A ⟶ m`, `(x, a) ↦ x`, of the trivial morphism `A ⟶ 𝟙_ C ⟶ m`. -/
noncomputable def homOneTranspose (hunit : IsTerminal (𝟙_ C)) (A : C) :
    (freeMod m).obj A ⟶ selfMod m :=
  ((freeModAdj m).homEquiv A (selfMod m)).symm (hunit.from A ≫ η[m])

/-- The underlying morphism of `homMulTranspose u` is `m ◁ u ≫ μ[m]`. -/
@[simp] lemma homMulTranspose_hom (u : A ⟶ m) : (homMulTranspose u).hom = m ◁ u ≫ μ[m] := by
  exact freeModAdj_homEquiv_symm_hom m (M := selfMod m) u

/-- The underlying morphism of `homOneTranspose hunit A` is `m ◁ (hunit.from A ≫ η[m]) ≫ μ[m]`. -/
@[simp] lemma homOneTranspose_hom (hunit : IsTerminal (𝟙_ C)) :
    (homOneTranspose (m := m) hunit A).hom = m ◁ (hunit.from A ≫ η[m]) ≫ μ[m] := by
  exact freeModAdj_homEquiv_symm_hom m (M := selfMod m) (hunit.from A ≫ η[m])

/-- Naturality: `homMulTranspose (g ≫ v) = (freeMod m).map g ≫ homMulTranspose v`. -/
lemma homMulTranspose_comp (g : A ⟶ B) (v : B ⟶ m) :
    homMulTranspose (g ≫ v) = (freeMod m).map g ≫ homMulTranspose v :=
  (freeModAdj m).homEquiv_naturality_left_symm (Y := selfMod m) g v

/-- Naturality: `homOneTranspose hunit A = (freeMod m).map g ≫ homOneTranspose hunit B`. -/
lemma homOneTranspose_comp (hunit : IsTerminal (𝟙_ C)) (g : A ⟶ B) :
    homOneTranspose (m := m) hunit A = (freeMod m).map g ≫ homOneTranspose hunit B := by
  rw [homOneTranspose, homOneTranspose,
    ← (freeModAdj m).homEquiv_naturality_left_symm (Y := selfMod m) g]
  congr 1
  rw [hunit.hom_ext (hunit.from A) (g ≫ hunit.from B)]
  exact Category.assoc _ _ _

variable [MonObj A] [MonObj B]

/-- The common section of the two transposes, given by the unit of `A`. -/
noncomputable def homCommonSection (A : C) [MonObj A] : selfMod m ⟶ (freeMod m).obj A where
  hom := (ρ_ m).inv ≫ m ◁ η[A]
  isModHom := ⟨by
    change μ[m] ≫ (ρ_ m).inv ≫ m ◁ η[A] =
      m ◁ ((ρ_ m).inv ≫ m ◁ η[A]) ≫ (α_ m m A).inv ≫ μ[m] ▷ A
    have h : m ◁ (ρ_ m).inv ≫ (α_ m m (𝟙_ C)).inv = (ρ_ (m ⊗ m)).inv := by monoidal
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange, ← Category.assoc,
      ← Category.assoc, h, Category.assoc, ← rightUnitor_inv_naturality_assoc]⟩

/-- The underlying morphism of `homCommonSection A` is `(ρ_ m).inv ≫ m ◁ η[A]`. -/
@[simp] lemma homCommonSection_hom : (homCommonSection (m := m) A).hom = (ρ_ m).inv ≫ m ◁ η[A] :=
  rfl

/-- For a morphism of monoid objects `u`, `homCommonSection A` is a section of
`homMulTranspose u`. -/
lemma homCommonSection_homMulTranspose (u : A ⟶ m) [IsMonHom u] :
    homCommonSection A ≫ homMulTranspose u = 𝟙 _ := by
  apply CategoryTheory.Mod.Hom.ext
  rw [CategoryTheory.Mod.comp_hom', homMulTranspose_hom, homCommonSection_hom]
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, IsMonHom.one_hom]
  simp

/-- `homCommonSection A` is a section of `homOneTranspose hunit A`. -/
lemma homCommonSection_homOneTranspose (hunit : IsTerminal (𝟙_ C)) :
    homCommonSection (m := m) A ≫ homOneTranspose hunit A = 𝟙 _ := by
  apply CategoryTheory.Mod.Hom.ext
  have ht : η[A] ≫ hunit.from A ≫ η[m] = η[m] := by
    rw [← Category.assoc, hunit.hom_ext (η[A] ≫ hunit.from A) (𝟙 _), Category.id_comp]
  rw [CategoryTheory.Mod.comp_hom', homOneTranspose_hom, homCommonSection_hom]
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ht]
  simp

/-- For a morphism of monoid objects `u`, `homMulTranspose u` and `homOneTranspose hunit A`
form a reflexive pair. -/
lemma homTranspose_isReflexivePair (hunit : IsTerminal (𝟙_ C)) (u : A ⟶ m) [IsMonHom u] :
    IsReflexivePair (homMulTranspose u) (homOneTranspose hunit A) :=
  ⟨homCommonSection A, homCommonSection_homMulTranspose u, homCommonSection_homOneTranspose hunit⟩

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C m)]

/-- The two transposes `homMulTranspose u` and `homOneTranspose` have a coequalizer of
`m`-modules (they form a reflexive pair). -/
instance hasCoequalizer_homTransposes (hunit : IsTerminal (𝟙_ C)) (u : A ⟶ m) [IsMonHom u] :
    HasCoequalizer (homMulTranspose u) (homOneTranspose hunit A) := by
  have := homTranspose_isReflexivePair hunit u
  exact HasReflexiveCoequalizers.has_coeq _ _

/-- **The quotient module of `m` by the image of a morphism of monoid objects** `u : A ⟶ m`: the
coequalizer, in the category of `m`-modules, of `(x, a) ↦ x · u a` and `(x, a) ↦ x`.  When `u` is
a subgroup object this is its coset quotient. -/
noncomputable def homQuot (hunit : IsTerminal (𝟙_ C)) (u : A ⟶ m) [IsMonHom u] : QuotMod m where
  V := coequalizer (homMulTranspose u) (homOneTranspose hunit A)
  p := coequalizer.π _ _

/-- **A morphism of monoid objects is annihilated by the quotient by its own image.** -/
lemma comp_homQuot_p (hunit : IsTerminal (𝟙_ C)) (u : A ⟶ m) [IsMonHom u] :
    u ≫ (homQuot hunit u).p.hom = (hunit.from A ≫ η[m]) ≫ (homQuot hunit u).p.hom := by
  have hc := coequalizer.condition (homMulTranspose u) (homOneTranspose hunit A)
  have hc' : (homMulTranspose u).hom ≫ (homQuot hunit u).p.hom
      = (homOneTranspose hunit A).hom ≫ (homQuot hunit u).p.hom := congr(($hc).hom)
  have h1 : ((λ_ A).inv ≫ η[m] ▷ A) ≫ (homMulTranspose u).hom = u := by
    rw [homMulTranspose_hom]; exact SubMon.unitLeft_comp' (m := m) u
  have h2 : ((λ_ A).inv ≫ η[m] ▷ A) ≫ (homOneTranspose hunit A).hom = hunit.from A ≫ η[m] := by
    rw [homOneTranspose_hom]; exact SubMon.unitLeft_comp' (m := m) (hunit.from A ≫ η[m])
  calc u ≫ (homQuot hunit u).p.hom
      = ((λ_ A).inv ≫ η[m] ▷ A) ≫ (homMulTranspose u).hom ≫ (homQuot hunit u).p.hom := by
        rw [← Category.assoc, h1]
    _ = ((λ_ A).inv ≫ η[m] ▷ A) ≫ (homOneTranspose hunit A).hom ≫ (homQuot hunit u).p.hom := by
        rw [hc']
    _ = (hunit.from A ≫ η[m]) ≫ (homQuot hunit u).p.hom := by rw [← Category.assoc, h2]

/-- **The quotient by the image is the largest one annihilating the morphism**: if `u` factors
through `v`, then the quotient by the image of `v` is a further quotient of the quotient by the
image of `u`. -/
lemma homQuot_le (hunit : IsTerminal (𝟙_ C)) {u : A ⟶ m} [IsMonHom u] {v : B ⟶ m} [IsMonHom v]
    (g : A ⟶ B) (hg : g ≫ v = u) : homQuot hunit u ≤ homQuot hunit v := by
  refine ⟨coequalizer.desc (homQuot hunit v).p ?_, coequalizer.π_desc _ _⟩
  rw [← hg, homMulTranspose_comp, homOneTranspose_comp hunit g, Category.assoc, Category.assoc]
  congr 1
  exact coequalizer.condition _ _

end General

/-! ## The image of a morphism of group objects -/

section GrpImage

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

variable {X Y : Grp C}

/-- **The image of a morphism of group objects**: the stabiliser of the base point of the quotient
of `Y` by the image of `f`. -/
noncomputable def grpImage (f : X ⟶ Y) : SubGrp Y.X :=
  stab (homQuot isTerminalTensorUnit f.hom.hom)

omit [HasFiniteLimits C] in
/-- A morphism of group objects is annihilated by the quotient by its image. -/
lemma kills_grpImage (f : X ⟶ Y) :
    Kills (homQuot isTerminalTensorUnit f.hom.hom) f.hom.hom := by
  have h := comp_homQuot_p (isTerminalTensorUnit (C := C)) f.hom.hom
  rw [Kills, h, isTerminalTensorUnit_from, pt, QuotMod.basePoint]
  exact Category.assoc _ _ _

/-- **A morphism of group objects factors through its image.** -/
lemma exists_grpImage_factor (f : X ⟶ Y) :
    ∃ e : X.X ⟶ (grpImage f).N, e ≫ (grpImage f).i = f.hom.hom :=
  (kills_iff_factors _ _).1 (kills_grpImage f)

/-- **The image is the smallest subgroup object through which the morphism factors.**  This is
where the injectivity of Newman's correspondence is used. -/
theorem grpImage_le (hinj : CosetInjective C) (f : X ⟶ Y) (s : SubGrp Y.X)
    (g : X.X ⟶ s.N) (hg : g ≫ s.i = f.hom.hom) : grpImage f ≤ s :=
  le_trans (galoisConnection_quot_stab.monotone_u
    (homQuot_le (isTerminalTensorUnit (C := C)) g hg)) (hinj Y.X s)

/-- The image of a morphism of group objects, as an object of `Grp C`. -/
noncomputable abbrev grpImageObj (f : X ⟶ Y) : Grp C := Grp.mk (grpImage f).N

/-- The inclusion of the image into the target. -/
noncomputable def grpImageι (f : X ⟶ Y) : grpImageObj f ⟶ Y := Grp.homMk (grpImage f).i

/-- The inclusion of the image of a morphism of group objects is a monomorphism of `Grp C`. -/
instance mono_grpImageι (f : X ⟶ Y) : Mono (grpImageι f) :=
  (Grp.forget C).mono_of_mono_map (f := grpImageι f)
    (by
      rw [show (Grp.forget C).map (grpImageι f) = (grpImage f).i from rfl]
      exact (grpImage f).mono_i)

/-- The underlying morphism of the corestriction of `f` to its image. -/
noncomputable def grpImageHom (f : X ⟶ Y) : X.X ⟶ (grpImage f).N :=
    (exists_grpImage_factor f).choose

/-- The corestriction followed by the inclusion of the image is `f`. -/
lemma grpImageHom_comp (f : X ⟶ Y) : grpImageHom f ≫ (grpImage f).i = f.hom.hom :=
  (exists_grpImage_factor f).choose_spec

/-- The corestriction of `f` to its image is a morphism of monoid objects. -/
instance isMonHom_grpImageHom (f : X ⟶ Y) : IsMonHom (grpImageHom f) := by
  have : IsMonHom (grpImageHom f ≫ (grpImage f).i) := by
    rw [grpImageHom_comp]; infer_instance
  exact Internal.isMonHom_of_comp_mono (grpImageHom f) (grpImage f).i

/-- **The corestriction of a morphism of group objects to its image.** -/
noncomputable def grpImageFactor (f : X ⟶ Y) : X ⟶ grpImageObj f := Grp.homMk (grpImageHom f)

/-- The corestriction followed by the inclusion of the image is `f`, in `Grp C`. -/
@[reassoc (attr := simp)]
lemma grpImageFactor_comp_ι (f : X ⟶ Y) : grpImageFactor f ≫ grpImageι f = f := by
  ext
  exact grpImageHom_comp f

/-- **The corestriction of a morphism to its image is an extremal epimorphism.**  Indeed a
monomorphic factorization of it produces a smaller subgroup object of the target through which the
morphism factors, and the image is the smallest one. -/
theorem isExtremalEpi_grpImageFactor (hinj : CosetInjective C) (f : X ⟶ Y) :
    IsExtremalEpi (grpImageFactor f) := by
  refine ExtremalEpi.mk_of_hasEqualizers _ fun {J} e' n hfac hn => ?_
  have := hn
  have : Mono (n ≫ grpImageι f) := mono_comp _ _
  have : Mono (n ≫ grpImageι f).hom.hom := mono_hom_of_mono _
  have : Mono n.hom.hom := mono_hom_of_mono _
  let s : SubGrp Y.X := { N := J.X, i := (n ≫ grpImageι f).hom.hom }
  have hfac' : e'.hom.hom ≫ s.i = f.hom.hom := by
    have : e' ≫ n ≫ grpImageι f = f := by
      rw [← Category.assoc, hfac, grpImageFactor_comp_ι]
    exact congr(($this).hom.hom)
  obtain ⟨k₀, hk⟩ := grpImage_le hinj f s e'.hom.hom hfac'
  let k : (grpImageObj f).X ⟶ J.X := k₀
  have : Mono (grpImageι f).hom.hom := inferInstanceAs (Mono (grpImage f).i)
  have h1 : k ≫ n.hom.hom = 𝟙 _ := by
    refine (cancel_mono (grpImageι f).hom.hom).1 ?_
    rw [Category.assoc, Category.id_comp]
    exact hk
  have h2 : n.hom.hom ≫ k = 𝟙 _ := by
    refine (cancel_mono n.hom.hom).1 ?_
    rw [Category.assoc, h1, Category.id_comp]
    exact Category.comp_id n.hom.hom
  exact isIso_of_isIso_hom n ⟨k, h2, h1⟩

variable [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

end GrpImage

/-! ## Balancedness -/

section Balanced

/-- An extremal epimorphism followed by an isomorphism is an extremal epimorphism. -/
lemma isExtremalEpi_comp_isIso {D : Type u} [Category.{v} D] {X I Y : D} {e : X ⟶ I} {m : I ⟶ Y}
    (he : IsExtremalEpi e) [IsIso m] : IsExtremalEpi (e ≫ m) := by
  have := he.epi
  refine IsExtremalEpi.mk inferInstance (fun {Z} a n hn hfac => ?_)
  have := hn
  have : Mono (n ≫ inv m) := mono_comp _ _
  have hfac' : a ≫ (n ≫ inv m) = e := by
    rw [← Category.assoc, hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have := he.isIso_of_mono a (n ≫ inv m) inferInstance hfac'
  have hn' : n = (n ≫ inv m) ≫ m := by simp
  rw [hn']
  infer_instance

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

end Balanced


end InternalGroups
